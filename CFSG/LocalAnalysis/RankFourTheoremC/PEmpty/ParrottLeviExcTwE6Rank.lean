module

public import CFSG.ClassicalInvolution.WeakCT.TwistedE6Model
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models.TwistedPairs Subgroup

namespace PB1

theorem three_dvd_mul_sq_sub_one (n : ℕ) : 3 ∣ n * (n ^ 2 - 1) := by
  rcases n with _ | m
  · simp
  · have h : (m + 1) ^ 2 - 1 = m * (m + 2) :=
      Nat.sub_eq_of_eq_add (by ring)
    rw [h]
    have h3 : 3 ∣ m ∨ 3 ∣ m + 1 ∨ 3 ∣ m + 2 := by omega
    rcases h3 with h3 | h3 | h3
    · exact ((h3.mul_right _).mul_left _)
    · exact h3.mul_right _
    · exact ((h3.mul_left _).mul_left _)

theorem three_dvd_card_sl2 (F : Type*) [Field F] [Finite F] :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact three_dvd_mul_sq_sub_one _

theorem center_sl2_eq_bot {F : Type*} [Field F] (h2 : (2 : F) = 0) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem center_range_eq_bot {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) (hG : Subgroup.center G = ⊥) :
    Subgroup.center ↥f.range = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨_, A, rfl⟩ hz
  have hA : A ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply hf
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨f B, B, rfl⟩)
  rw [hG, Subgroup.mem_bot] at hA
  subst hA
  rw [Subgroup.mem_bot]
  exact Subtype.ext (map_one f)

theorem card_range_of_injective {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) : Nat.card ↥f.range = Nat.card G :=
  (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

variable {k : Type} [Field k] (θ : k →+* k)

theorem two_eq_zero_fixedField [CharP k 2] : (2 : ↥(fixedField θ)) = 0 :=
  Subtype.ext (CharTwo.two_eq_zero (R := k))

theorem two_le_of_card [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2) : 2 ≤ q := by
  have h1 : 1 < Nat.card k := Finite.one_lt_card
  rw [hk] at h1
  rcases q with _ | _ | q
  · simp at h1
  · simp at h1
  · omega

theorem involutive_of_card [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) (c : k) : θ (θ c) = c := by
  have := Fintype.ofFinite k
  rw [hθq, hθq, ← pow_mul, ← sq, ← hk, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card c

theorem exists_ne_of_card [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) : ∃ c : k, θ c ≠ c := by
  have hq : 2 ≤ q := two_le_of_card hk
  by_contra! h
  classical
  haveI := Fintype.ofFinite k
  have hdeg : (Polynomial.X ^ q - Polynomial.X : Polynomial k).natDegree = q := by
    have h1 : (Polynomial.X : Polynomial k).natDegree <
        (Polynomial.X ^ q : Polynomial k).natDegree := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      omega
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt h1, Polynomial.natDegree_X_pow]
  have hp0 : (Polynomial.X ^ q - Polynomial.X : Polynomial k) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ : Finset k).val ⊆
      (Polynomial.X ^ q - Polynomial.X : Polynomial k).roots := by
    intro c _
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero, ← hθq c, h c]
  have hle := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_univ, hdeg, ← Nat.card_eq_fintype_card, hk] at hle
  nlinarith

theorem card_eq_card_fixedField_sq [Finite k] (hθ : ∀ c, θ (θ c) = c) {ω : k}
    (hω : θ ω ≠ ω) : Nat.card k = Nat.card ↥(fixedField θ) ^ 2 := by
  have hω' : ω - θ ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hω)
  let Φ : ↥(fixedField θ) × ↥(fixedField θ) → k := fun p => p.1 + p.2 * ω
  have hinj : Function.Injective Φ := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have ha : θ a = a := ha
    have hb : θ b = b := hb
    have ha' : θ a' = a' := ha'
    have hb' : θ b' = b' := hb'
    simp only [Φ] at h
    have h2 := congrArg θ h
    simp only [map_add, map_mul, ha, hb, ha', hb'] at h2
    have h3 : (b - b') * (ω - θ ω) = 0 := by linear_combination h - h2
    have hbb : b = b' := by
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact sub_eq_zero.mp h4
      · exact absurd h4 hω'
    subst hbb
    have : a = a' := by linear_combination h
    subst this
    rfl
  have hsurj : Function.Surjective Φ := by
    intro x
    have hb : θ ((x - θ x) / (ω - θ ω)) = (x - θ x) / (ω - θ ω) := by
      rw [map_div₀, map_sub, map_sub, hθ, hθ, ← neg_sub x, ← neg_sub ω, neg_div_neg_eq]
    refine ⟨(⟨x - (x - θ x) / (ω - θ ω) * ω, ?_⟩, ⟨(x - θ x) / (ω - θ ω), hb⟩), ?_⟩
    · change θ (x - (x - θ x) / (ω - θ ω) * ω) = x - (x - θ x) / (ω - θ ω) * ω
      rw [map_sub, map_mul, hb]
      have : (x - θ x) / (ω - θ ω) * (ω - θ ω) = x - θ x := div_mul_cancel₀ _ hω'
      linear_combination this
    · simp only [Φ]
      ring
  rw [sq, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective Φ ⟨hinj, hsurj⟩)).symm

theorem lt_or_lt_of_cartan_eq_zero (i j : Fin 4) (hij : i ≠ j)
    (hc : CFSG.Blueprint.Chevalley.Tag.cartan .F4 i j = 0) :
    i.val + 1 < j.val ∨ j.val + 1 < i.val := by
  revert hij hc
  fin_cases i <;> fin_cases j <;> decide

theorem fin_four_cases
    (i : Fin (twistedDatum k θ).rank) : i = nf 0 ∨ i = nf 1 ∨ i = nf 2 ∨ i = nf 3 := by
  obtain ⟨n, hn⟩ := i
  have hn4 : n < 4 := hn
  interval_cases n
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

end PB1


variable {k : Type} [Field k] (θ : k →+* k)

theorem commute_rankOne_of_cartan_eq_zero (hθ : ∀ c, θ (θ c) = c) :
    ∀ i j : Fin (twistedDatum k θ).rank, i ≠ j → (twistedDatum k θ).cartan i j = 0 →
      ∀ u ∈ rankOne (twistedDatum k θ).rootGroup i,
        ∀ v ∈ rankOne (twistedDatum k θ).rootGroup j, u * v = v * u := by
  intro i j hij hc
  rcases PB1.lt_or_lt_of_cartan_eq_zero i j hij hc with h | h
  · exact commute_rankOne_twistedE6 θ hθ i j h
  · intro u hu v hv
    exact (commute_rankOne_twistedE6 θ hθ j i h v hv u hu).symm

theorem three_dvd_card_rankOne [Finite k] [CharP k 2] (hθ : ∀ c, θ (θ c) = c)
    (i : Fin (twistedDatum k θ).rank) :
    3 ∣ Nat.card (rankOne (twistedDatum k θ).rootGroup i) := by
  rcases PB1.fin_four_cases θ i with rfl | rfl | rfl | rfl
  · rw [rankOne_twistedE6_zero,
      PB1.card_range_of_injective (f := nodeHom0 θ) (rFixed_injective θ _ _)]
    exact PB1.three_dvd_card_sl2 _
  · rw [rankOne_twistedE6_one,
      PB1.card_range_of_injective (f := nodeHom1 θ) (rFixed_injective θ _ _)]
    exact PB1.three_dvd_card_sl2 _
  · rw [rankOne_twistedE6_two θ hθ,
      PB1.card_range_of_injective (f := nodeHom2 θ hθ) (slOrbitHom_injective θ hθ _)]
    exact PB1.three_dvd_card_sl2 _
  · rw [rankOne_twistedE6_three θ hθ,
      PB1.card_range_of_injective (f := nodeHom3 θ hθ) (slOrbitHom_injective θ hθ _)]
    exact PB1.three_dvd_card_sl2 _

theorem center_rankOne_eq_bot [Finite k] [CharP k 2] (hθ : ∀ c, θ (θ c) = c)
    (i : Fin (twistedDatum k θ).rank) :
    center ↥(rankOne (twistedDatum k θ).rootGroup i) = ⊥ := by
  have hk : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k) = ⊥ :=
    PB1.center_sl2_eq_bot CharTwo.two_eq_zero
  have hF : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ↥(fixedField θ)) = ⊥ :=
    PB1.center_sl2_eq_bot (PB1.two_eq_zero_fixedField θ)
  rcases PB1.fin_four_cases θ i with rfl | rfl | rfl | rfl
  · rw [rankOne_twistedE6_zero]
    exact PB1.center_range_eq_bot (f := nodeHom0 θ) (rFixed_injective θ _ _) hF
  · rw [rankOne_twistedE6_one]
    exact PB1.center_range_eq_bot (f := nodeHom1 θ) (rFixed_injective θ _ _) hF
  · rw [rankOne_twistedE6_two θ hθ]
    exact PB1.center_range_eq_bot (f := nodeHom2 θ hθ) (slOrbitHom_injective θ hθ _) hk
  · rw [rankOne_twistedE6_three θ hθ]
    exact PB1.center_range_eq_bot (f := nodeHom3 θ hθ) (slOrbitHom_injective θ hθ _) hk

theorem card_rankOne_fixed [Finite k] (hk2 : Nat.card (fixedField θ) = 2)
    {j : Fin (twistedDatum k θ).rank} (hj : j = nf 0 ∨ j = nf 1) :
    Nat.card (rankOne (twistedDatum k θ).rootGroup j) = 6 := by
  rcases hj with rfl | rfl
  · rw [rankOne_twistedE6_zero,
      PB1.card_range_of_injective (f := nodeHom0 θ) (rFixed_injective θ _ _),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk2]
    norm_num
  · rw [rankOne_twistedE6_one,
      PB1.card_range_of_injective (f := nodeHom1 θ) (rFixed_injective θ _ _),
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk2]
    norm_num

theorem card_fixedField [Finite k] {q : ℕ} (hk : Nat.card k = q ^ 2) (hθq : ∀ c, θ c = c ^ q) :
    Nat.card (fixedField θ) = q := by
  obtain ⟨ω, hω⟩ := PB1.exists_ne_of_card θ hk hθq
  have h := PB1.card_eq_card_fixedField_sq θ (PB1.involutive_of_card θ hk hθq) hω
  rw [hk] at h
  exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h).symm

theorem exists_eq_add_of_fixed [Finite k] [CharP k 2] {q : ℕ} (hk : Nat.card k = q ^ 2)
    (hθq : ∀ c, θ c = c ^ q) {c : k} (hc : θ c = c) : ∃ u : k, c = u + θ u := by
  have hθ := PB1.involutive_of_card θ hk hθq
  let T : k →+ k :=
    { toFun := fun u => u + θ u
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add]; abel }
  have hT : ∀ u, T u = u + θ u := fun u => rfl
  let F : AddSubgroup k := (fixedField θ).toAddSubgroup
  have hmemF : ∀ u, u ∈ F ↔ θ u = u := fun u => Iff.rfl
  have hker : T.ker = F := by
    ext u
    rw [AddMonoidHom.mem_ker, hT, hmemF, CharTwo.add_eq_zero, eq_comm]
  have hle : T.range ≤ F := by
    rintro _ ⟨u, rfl⟩
    rw [hmemF, hT, map_add, hθ, add_comm]
  have hF : Nat.card ↥F = q := card_fixedField θ hk hθq
  have hcard := AddSubgroup.card_ker_mul_card_range T
  rw [hker, hF, hk] at hcard
  have hq : 0 < q := by have := PB1.two_le_of_card hk; omega
  have hR : Nat.card ↥T.range = q :=
    Nat.eq_of_mul_eq_mul_left hq (by rw [hcard, sq])
  have heq : T.range = F := AddSubgroup.eq_of_le_of_card_ge hle (le_of_eq (hF.trans hR.symm))
  have hcF : c ∈ F := hc
  rw [← heq] at hcF
  obtain ⟨u, hu⟩ := hcF
  exact ⟨u, hu.symm⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6
