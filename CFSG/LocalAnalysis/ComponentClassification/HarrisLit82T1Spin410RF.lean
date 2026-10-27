module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RT
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1Spin410RS

public section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution
open CFSG.GH74.GLS.Bg.Thompson (IsSylowIn)
open scoped MatrixGroups

theorem not_dvd_relIndex_inf_of_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    {P N : Subgroup G} [N.Normal] (hP : ¬ p ∣ P.index) : ¬ p ∣ (P ⊓ N).relIndex N := by
  have h1 : (P ⊓ N).relIndex N * N.index = (P ⊓ N).index := relIndex_mul_index inf_le_right
  have h2 : (P ⊓ N).relIndex P * P.index = (P ⊓ N).index := relIndex_mul_index inf_le_left
  have h3 : (P ⊓ N).relIndex P = N.relIndex (P ⊔ N) := by
    rw [inf_relIndex_left, relIndex_sup_right]
  have h4 : N.relIndex (P ⊔ N) * (P ⊔ N).index = N.index := relIndex_mul_index le_sup_right
  have ha : N.relIndex (P ⊔ N) ≠ 0 := by
    intro h
    have := relIndex_mul_card (le_sup_right : N ≤ P ⊔ N)
    rw [h, zero_mul] at this
    exact (Nat.card_pos (α := ↥(P ⊔ N))).ne' this.symm
  have hx : (P ⊓ N).relIndex N * (P ⊔ N).index = P.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha)
    calc N.relIndex (P ⊔ N) * ((P ⊓ N).relIndex N * (P ⊔ N).index) =
        (P ⊓ N).relIndex N * (N.relIndex (P ⊔ N) * (P ⊔ N).index) := by ring
      _ = N.relIndex (P ⊔ N) * P.index := by rw [h4, h1, ← h2, h3]
  intro hd
  exact hP (hx ▸ dvd_mul_of_dvd_left hd _)

theorem isSylowIn_inf_of_normal {G : Type*} [Group G] [Finite G] {C T J : Subgroup G}
    (hT : IsSylowIn 2 T C) (hJC : J ≤ C) (hJn : (J.subgroupOf C).Normal) :
    IsSylowIn 2 (T ⊓ J) J := by
  refine ⟨inf_le_right, hT.2.1.to_inf_left, ?_⟩
  have h := not_dvd_relIndex_inf_of_normal (G := ↥C) (P := T.subgroupOf C)
    (N := J.subgroupOf C) hT.2.2
  have e : (T ⊓ J).subgroupOf C = T.subgroupOf C ⊓ J.subgroupOf C := comap_inf _ _ _
  rwa [← e, relIndex_subgroupOf hJC] at h

theorem mul_mul_mul_mul_mul_of_commute {G : Type*} [Group G] {a a' b b' c c' : G}
    (h1 : a' * b = b * a') (h2 : a' * c = c * a') (h3 : b' * c = c * b') :
    a * b * c * (a' * b' * c') = a * a' * (b * b') * (c * c') := by
  have e : b * c * a' = a' * (b * c) := by
    calc b * c * a' = b * (c * a') := mul_assoc _ _ _
      _ = b * (a' * c) := by rw [← h2]
      _ = b * a' * c := (mul_assoc _ _ _).symm
      _ = a' * b * c := by rw [← h1]
      _ = a' * (b * c) := mul_assoc _ _ _
  have e' : c * b' = b' * c := h3.symm
  calc a * b * c * (a' * b' * c') = a * (b * c * a') * (b' * c') := by simp only [mul_assoc]
    _ = a * (a' * (b * c)) * (b' * c') := by rw [e]
    _ = a * a' * (b * (c * b')) * c' := by simp only [mul_assoc]
    _ = a * a' * (b * b') * (c * c') := by rw [e']; simp only [mul_assoc]

variable {K : Type} [Field K]

theorem sylow_range_sl2_facts [Finite K] (hodd : Odd (Nat.card K)) {G : Type*} [Group G]
    (ρ : SL(2, K) →* G) (hρ : Function.Injective ρ) {Q : Subgroup G}
    (hQ : IsSylowIn 2 Q ρ.range) :
    (∀ g ∈ Q, ∃ x ∈ Q, ∃ y ∈ Q, x * x = ρ (-1) ∧ y * y = ρ (-1) ∧ g = x * y) ∧
      ∀ g ∈ ρ.range, (∀ x ∈ Q, g * x = x * g) → g = 1 ∨ g = ρ (-1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Q.comap ρ) := hQ.2.1.comap_of_injective ρ hρ
  have hi : ¬ 2 ∣ (Q.comap ρ).index := by rw [index_comap]; exact hQ.2.2
  set P : Sylow 2 SL(2, K) := hp.toSylow hi with hP
  have hPQ : ∀ x, x ∈ (P : Subgroup SL(2, K)) ↔ ρ x ∈ Q := fun x => Iff.rfl
  obtain ⟨hprod, -⟩ := sylow_sl2_facts hodd P
  refine ⟨fun g hg => ?_, fun g hg hc => ?_⟩
  · obtain ⟨g', rfl⟩ := hQ.1 hg
    obtain ⟨x, hx, y, hy, hxx, hyy, hxy⟩ := hprod g' ((hPQ g').mpr hg)
    exact ⟨ρ x, (hPQ x).mp hx, ρ y, (hPQ y).mp hy, by rw [← map_mul, hxx],
      by rw [← map_mul, hyy], by rw [hxy, map_mul]⟩
  · obtain ⟨g', rfl⟩ := hg
    have hM : ∀ x ∈ (P : Subgroup SL(2, K)),
        (g' : Matrix (Fin 2) (Fin 2) K) * x = x * g' := by
      intro x hx
      have h := hc (ρ x) ((hPQ x).mp hx)
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hρ h)
    obtain ⟨c, hc'⟩ := eq_smul_one_of_commute_sylow_sl2 hodd P hM
    have hdet : c ^ 2 = 1 := by
      have h := g'.2
      rw [hc', Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
      exact h
    have hc1 : c = 1 ∨ c = -1 := by
      have h : (c - 1) * (c + 1) = 0 := by linear_combination hdet
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hc1 with rfl | rfl
    · left
      have : g' = 1 := Subtype.ext (by rw [hc', one_smul]; rfl)
      rw [this, map_one]
    · right
      have : g' = -1 := Subtype.ext (by
        rw [hc', neg_smul, one_smul, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one])
      rw [this]

section Model

variable [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
  (h5 : 5 ≤ p ^ f)
include hp hp2 hK h5

theorem two_mul_card_sup_sup {A B D : Subgroup (spinGroup (quadOdd 3 K))}
    (hA : A ≤ spinJ₁ K) (hB : B ≤ spinJ₂ K) (hD : D ≤ spinJ₃ K)
    (hz : spinZ K ∈ A) (ht : tSeven K ∈ B) (hzt : spinZ K * tSeven K ∈ D) :
    2 * Nat.card ↥(A ⊔ B ⊔ D) = Nat.card A * Nat.card B * Nat.card D := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have h4 := four_le_card_spin hK h5
  obtain ⟨hzz, hz1, hzc, htt, -, -, -, -, -, -⟩ := spinZ_facts hp hp2 hK
  set ι : (A × B) × D →* (spinJ₁ K × spinJ₂ K) × spinJ₃ K :=
    ((inclusion hA).prodMap (inclusion hB)).prodMap (inclusion hD) with hιdef
  have hι : Function.Injective ι := by
    rw [hιdef, MonoidHom.coe_prodMap, MonoidHom.coe_prodMap]
    exact ((inclusion_injective hA).prodMap (inclusion_injective hB)).prodMap
      (inclusion_injective hD)
  set φ := (spinMul h4).comp ι with hφ
  have happly : ∀ x : (A × B) × D, φ x = (x.1.1 : spinGroup (quadOdd 3 K)) * x.1.2 * x.2 :=
    fun x => rfl
  have hrange : φ.range = A ⊔ B ⊔ D := by
    refine le_antisymm ?_ (sup_le (sup_le ?_ ?_) ?_)
    · rintro _ ⟨x, rfl⟩
      rw [happly]
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left x.1.1.2))
        (mem_sup_left (mem_sup_right x.1.2.2))) (mem_sup_right x.2.2)
    · intro a ha
      exact ⟨((⟨a, ha⟩, 1), 1), by rw [happly]; simp⟩
    · intro b hb
      exact ⟨((1, ⟨b, hb⟩), 1), by rw [happly]; simp⟩
    · intro d hd
      exact ⟨((1, 1), ⟨d, hd⟩), by rw [happly]; simp⟩
  set w : (A × B) × D := ((⟨spinZ K, hz⟩, ⟨tSeven K, ht⟩), ⟨spinZ K * tSeven K, hzt⟩) with hw
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  have hww : w * w = 1 :=
    Prod.ext (Prod.ext (Subtype.ext hzz) (Subtype.ext htt)) (Subtype.ext hztzt)
  have hw1 : w ≠ 1 := fun h => hz1 (congrArg (fun v => (v.1.1 : spinGroup (quadOdd 3 K))) h)
  have hker : φ.ker = zpowers w := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      mem_ker_spinMul_iff hp hp2 hK h5 h4]
    constructor
    · rintro (h | h)
      · rw [show x = 1 from hι (h.trans (map_one ι).symm)]
        exact one_mem _
      · rw [show x = w from hι h]
        exact mem_zpowers _
    · intro hx
      rcases eq_one_or_eq_of_mem_zpowers_of_mul_self hww hx with rfl | rfl
      · exact Or.inl (map_one ι)
      · exact Or.inr rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card φ.ker = 2 := by
    rw [hker, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  have h := card_ker_mul_card_range φ
  rw [hcard, hrange, Nat.card_prod, Nat.card_prod] at h
  exact h

theorem not_dvd_relIndex_sup_sup {Q₁ Q₂ Q₃ : Subgroup (spinGroup (quadOdd 3 K))}
    (h1 : IsSylowIn 2 Q₁ (spinJ₁ K)) (h2 : IsSylowIn 2 Q₂ (spinJ₂ K))
    (h3 : IsSylowIn 2 Q₃ (spinJ₃ K)) (hz : spinZ K ∈ Q₁) (ht : tSeven K ∈ Q₂)
    (hzt : spinZ K * tSeven K ∈ Q₃) : ¬ 2 ∣ (Q₁ ⊔ Q₂ ⊔ Q₃).relIndex (spinE K) := by
  have := finite_spinSeven (two_ne_zero_spin hp hp2 hK)
  have hP := two_mul_card_sup_sup hp hp2 hK h5 h1.1 h2.1 h3.1 hz ht hzt
  have hE := card_spinE hp hp2 hK h5
  have hJ₁ := card_range_sl2 (shortSeven K) injective_shortSeven
  have hJ₂ := card_range_sl2 ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true true)
    (longSL2_injective _ fin3_zero_ne_one true true)
  have hJ₃ := card_range_sl2 ((oddFrame 3 K).toHypFrame.longSL2 fin3_zero_ne_one true false)
    (longSL2_injective _ fin3_zero_ne_one true false)
  have e1 := relIndex_mul_card h1.1
  have e2 := relIndex_mul_card h2.1
  have e3 := relIndex_mul_card h3.1
  have e := relIndex_mul_card (sup_le (sup_le (h1.1.trans le_sup_left |>.trans le_sup_left)
    (h2.1.trans le_sup_right |>.trans le_sup_left)) (h3.1.trans le_sup_right) :
      Q₁ ⊔ Q₂ ⊔ Q₃ ≤ spinE K)
  have hEJ : 2 * Nat.card (spinE K) = Nat.card (spinJ₁ K) * Nat.card (spinJ₂ K) *
      Nat.card (spinJ₃ K) := by
    rw [hE, hJ₁, hJ₂, hJ₃]
    ring
  have hpos : 0 < Nat.card ↥(Q₁ ⊔ Q₂ ⊔ Q₃) := Nat.card_pos
  have key : (Q₁ ⊔ Q₂ ⊔ Q₃).relIndex (spinE K) =
      Q₁.relIndex (spinJ₁ K) * Q₂.relIndex (spinJ₂ K) * Q₃.relIndex (spinJ₃ K) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by norm_num : 0 < 2) hpos)
    calc (Q₁ ⊔ Q₂ ⊔ Q₃).relIndex (spinE K) * (2 * Nat.card ↥(Q₁ ⊔ Q₂ ⊔ Q₃)) =
        2 * Nat.card (spinE K) := by rw [← e]; ring
      _ = Nat.card (spinJ₁ K) * Nat.card (spinJ₂ K) * Nat.card (spinJ₃ K) := hEJ
      _ = _ := by rw [← e1, ← e2, ← e3, hP]; ring
  rw [key]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
  · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
    · exact h1.2.2 hd
    · exact h2.2.2 hd
  · exact h3.2.2 hd

theorem exists_involution_not_mem_spinE {T₀ : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T₀ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))) :
    ∃ τ' ∈ T₀, τ' * τ' = 1 ∧ τ' ∉ spinE K := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have := finite_spinSeven h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (spinGroup (quadOdd 3 K)) :=
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  obtain ⟨ν, hν0, hνs⟩ := exists_nonsquare_spin hp hp2 hK
  have hτC := spinTau_mem_centralizer ν hν0
  have hττ := spinTau_mul_self ν hν0
  set τC : C := ⟨spinTau ν hν0, hτC⟩ with hτCdef
  have hτN : τC ∉ (spinE K).subgroupOf C := by
    rw [← ker_spinNormC hp hp2 hK h5, MonoidHom.mem_ker]
    exact spinNormC_spinTau_ne_one ν hν0 hνs hτC
  have hτ1 : τC ≠ 1 := fun h => hτN (h ▸ one_mem _)
  have hτ2 : IsPGroup 2 (zpowers τC) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext hττ) hτ1
  obtain ⟨T₁, hT₁⟩ := hτ2.exists_le_sylow
  have hT₀p : IsPGroup 2 (T₀.subgroupOf C) := hT.2.1.comap_of_injective _ C.subtype_injective
  set S₀ : Sylow 2 C := hT₀p.toSylow hT.2.2 with hS₀
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C T₁ S₀
  have hmem : c * τC * c⁻¹ ∈ (S₀ : Subgroup C) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hT₁ (mem_zpowers τC))
  refine ⟨((c * τC * c⁻¹ : C) : spinGroup (quadOdd 3 K)), hmem, ?_, ?_⟩
  · rw [← Subgroup.coe_mul]
    have : c * τC * c⁻¹ * (c * τC * c⁻¹) = 1 := by
      rw [show c * τC * c⁻¹ * (c * τC * c⁻¹) = c * (τC * τC) * c⁻¹ by group,
        show τC * τC = 1 from Subtype.ext hττ, mul_one, mul_inv_cancel]
    rw [this]
    rfl
  · intro h
    apply hτN
    have hN := (normal_spinE (K := K) hp hp2 hK h5)
    have h' : c * τC * c⁻¹ ∈ (spinE K).subgroupOf C := h
    have := hN.conj_mem _ h' c⁻¹
    rwa [show c⁻¹ * (c * τC * c⁻¹) * c⁻¹⁻¹ = τC by group] at this

theorem closure_involutions_eq_of_isSylowIn {T₀ : Subgroup (spinGroup (quadOdd 3 K))}
    (hT : IsSylowIn 2 T₀ (centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))))) :
    closure {x | x ∈ T₀ ∧ x * x = 1} = T₀ := by
  have h2 := two_ne_zero_spin hp hp2 hK
  have := finite_spinSeven h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h4 := four_le_card_spin hK h5
  obtain ⟨hzz, -, hzc, htt, -, -, -, -, -, h3eq⟩ := spinZ_facts hp hp2 hK
  have hQ : quadOdd 3 K ≠ 0 := (nondegenerate_quadOdd 3 K).ne_zero
  obtain ⟨l1, l2, l3⟩ := spinJ_le_centralizer (K := K) hp hp2 hK
  obtain ⟨n1, n2, n3⟩ := normal_spinJ (K := K) hp hp2 hK h5
  set C : Subgroup (spinGroup (quadOdd 3 K)) :=
    centralizer ({tSeven K} : Set (spinGroup (quadOdd 3 K))) with hC
  set S := closure {x | x ∈ T₀ ∧ x * x = 1} with hSdef
  refine le_antisymm ((closure_le _).mpr fun x hx => hx.1) ?_
  have hS : ∀ x, x ∈ T₀ → x * x = 1 → x ∈ S := fun x hx hxx => subset_closure ⟨hx, hxx⟩
  have hzcomm : ∀ g : spinGroup (quadOdd 3 K), spinZ K * g = g * spinZ K := fun g =>
    (mem_center_iff.mp hzc g).symm
  have htcomm : ∀ g ∈ C, tSeven K * g = g * tSeven K := fun g hg =>
    (mem_centralizer_singleton_iff.mp hg).symm
  have hztzt : spinZ K * tSeven K * (spinZ K * tSeven K) = 1 := by
    rw [mul_assoc, ← mul_assoc (tSeven K), ← hzcomm, mul_assoc, htt, mul_one, hzz]
  have htzt : tSeven K * (spinZ K * tSeven K) * spinZ K = 1 := by
    rw [hzcomm (tSeven K), ← mul_assoc, htt, one_mul, hzz]
  have c12 : ∀ a ∈ spinJ₁ K, ∀ b ∈ spinJ₂ K, a * b = b * a := fun a ha b hb =>
    commute_spinJ₁_spinJ₂ ha hb
  have c13 : ∀ a ∈ spinJ₁ K, ∀ c ∈ spinJ₃ K, a * c = c * a := fun a ha c hc =>
    commute_spinJ₁_spinJ₃ ha hc
  have c23 : ∀ b ∈ spinJ₂ K, ∀ c ∈ spinJ₃ K, b * c = c * b := fun b hb c hc =>
    commute_spinJ₂_spinJ₃ h4 hb hc
  have hQ1 := isSylowIn_inf_of_normal hT l1 n1
  have hQ2 := isSylowIn_inf_of_normal hT l2 n2
  have hQ3 := isSylowIn_inf_of_normal hT l3 n3
  obtain ⟨f1, -⟩ := sylow_range_sl2_facts hodd (shortSeven K) injective_shortSeven hQ1
  obtain ⟨f2, -⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true true) hQ2
  obtain ⟨f3, -⟩ := sylow_range_sl2_facts hodd _
    (longSL2_injective _ fin3_zero_ne_one true false) hQ3
  rw [shortSeven_neg_one hQ] at f1
  rw [h3eq] at f3
  obtain ⟨x₁, hx₁, -, -, hx₁x₁, -, -⟩ := f1 1 (one_mem _)
  obtain ⟨x₂, hx₂, -, -, hx₂x₂, -, -⟩ := f2 1 (one_mem _)
  obtain ⟨x₃, hx₃, -, -, hx₃x₃, -, -⟩ := f3 1 (one_mem _)
  have hzT : spinZ K ∈ T₀ := by
    have h := mul_mem hx₁.1 hx₁.1
    rw [hx₁x₁] at h
    exact h
  have htT : tSeven K ∈ T₀ := by
    have h := mul_mem hx₂.1 hx₂.1
    rw [hx₂x₂] at h
    exact h
  have hztT : spinZ K * tSeven K ∈ T₀ := mul_mem hzT htT
  have hinv : ∀ a ∈ T₀ ⊓ spinJ₁ K, ∀ b ∈ T₀ ⊓ spinJ₂ K, ∀ c ∈ T₀ ⊓ spinJ₃ K,
      a * a = spinZ K → b * b = tSeven K → c * c = spinZ K * tSeven K → a * b * c ∈ S := by
    intro a ha b hb c hc haa hbb hcc
    refine hS _ (mul_mem (mul_mem ha.1 hb.1) hc.1) ?_
    rw [mul_mul_mul_mul_mul_of_commute (c12 a ha.2 b hb.2) (c13 a ha.2 c hc.2)
      (c23 b hb.2 c hc.2), haa, hbb, hcc, hztzt]
  have hQ1S : T₀ ⊓ spinJ₁ K ≤ S := by
    intro g hg
    obtain ⟨x, hx, y, hy, hxx, hyy, rfl⟩ := f1 g hg
    have e : x * x₂ * x₃ * (y * x₂ * x₃) * spinZ K = x * y := by
      rw [mul_mul_mul_mul_mul_of_commute (c12 y hy.2 x₂ hx₂.2) (c13 y hy.2 x₃ hx₃.2)
        (c23 x₂ hx₂.2 x₃ hx₃.2), hx₂x₂, hx₃x₃]
      calc x * y * tSeven K * (spinZ K * tSeven K) * spinZ K =
          x * y * (tSeven K * (spinZ K * tSeven K) * spinZ K) := by simp only [mul_assoc]
        _ = x * y := by rw [htzt, mul_one]
    rw [← e]
    exact mul_mem (mul_mem (hinv x hx x₂ hx₂ x₃ hx₃ hxx hx₂x₂ hx₃x₃)
      (hinv y hy x₂ hx₂ x₃ hx₃ hyy hx₂x₂ hx₃x₃)) (hS _ hzT hzz)
  have hQ2S : T₀ ⊓ spinJ₂ K ≤ S := by
    intro g hg
    obtain ⟨x, hx, y, hy, hxx, hyy, rfl⟩ := f2 g hg
    have e : x₁ * x * x₃ * (x₁ * y * x₃) * tSeven K = x * y := by
      rw [mul_mul_mul_mul_mul_of_commute (c12 x₁ hx₁.2 x hx.2) (c13 x₁ hx₁.2 x₃ hx₃.2)
        (c23 y hy.2 x₃ hx₃.2), hx₁x₁, hx₃x₃]
      calc spinZ K * (x * y) * (spinZ K * tSeven K) * tSeven K =
          spinZ K * (x * y) * spinZ K * (tSeven K * tSeven K) := by simp only [mul_assoc]
        _ = x * y * (spinZ K * spinZ K) := by rw [htt, mul_one, hzcomm (x * y), mul_assoc]
        _ = x * y := by rw [hzz, mul_one]
    rw [← e]
    exact mul_mem (mul_mem (hinv x₁ hx₁ x hx x₃ hx₃ hx₁x₁ hxx hx₃x₃)
      (hinv x₁ hx₁ y hy x₃ hx₃ hx₁x₁ hyy hx₃x₃)) (hS _ htT htt)
  have hQ3S : T₀ ⊓ spinJ₃ K ≤ S := by
    intro g hg
    obtain ⟨x, hx, y, hy, hxx, hyy, rfl⟩ := f3 g hg
    have hxyC : x * y ∈ C := mul_mem (l3 hx.2) (l3 hy.2)
    have e : x₁ * x₂ * x * (x₁ * x₂ * y) * (spinZ K * tSeven K) = x * y := by
      rw [mul_mul_mul_mul_mul_of_commute (c12 x₁ hx₁.2 x₂ hx₂.2) (c13 x₁ hx₁.2 x hx.2)
        (c23 x₂ hx₂.2 x hx.2), hx₁x₁, hx₂x₂]
      calc spinZ K * tSeven K * (x * y) * (spinZ K * tSeven K) =
          spinZ K * (tSeven K * (x * y)) * (spinZ K * tSeven K) := by rw [mul_assoc (spinZ K)]
        _ = spinZ K * (x * y * tSeven K) * (spinZ K * tSeven K) := by rw [htcomm _ hxyC]
        _ = x * y * spinZ K * tSeven K * (spinZ K * tSeven K) := by
          rw [← mul_assoc (spinZ K) (x * y) (tSeven K), hzcomm (x * y)]
        _ = x * y * (spinZ K * tSeven K * (spinZ K * tSeven K)) := by simp only [mul_assoc]
        _ = x * y := by rw [hztzt, mul_one]
    rw [← e]
    exact mul_mem (mul_mem (hinv x₁ hx₁ x₂ hx₂ x hx hx₁x₁ hx₂x₂ hxx)
      (hinv x₁ hx₁ x₂ hx₂ y hy hx₁x₁ hx₂x₂ hyy)) (hS _ hztT hztzt)
  have hP'S : (T₀ ⊓ spinJ₁ K) ⊔ (T₀ ⊓ spinJ₂ K) ⊔ (T₀ ⊓ spinJ₃ K) ≤ S :=
    sup_le (sup_le hQ1S hQ2S) hQ3S
  have hP'E : (T₀ ⊓ spinJ₁ K) ⊔ (T₀ ⊓ spinJ₂ K) ⊔ (T₀ ⊓ spinJ₃ K) ≤ T₀ ⊓ spinE K :=
    sup_le (sup_le (inf_le_inf_left _ (le_sup_left.trans le_sup_left))
      (inf_le_inf_left _ (le_sup_right.trans le_sup_left))) (inf_le_inf_left _ le_sup_right)
  have hzJ : spinZ K ∈ spinJ₁ K := by
    have h := mul_mem hx₁.2 hx₁.2
    rw [hx₁x₁] at h
    exact h
  have htJ : tSeven K ∈ spinJ₂ K := by
    have h := mul_mem hx₂.2 hx₂.2
    rw [hx₂x₂] at h
    exact h
  have hztJ : spinZ K * tSeven K ∈ spinJ₃ K := by
    have h := mul_mem hx₃.2 hx₃.2
    rw [hx₃x₃] at h
    exact h
  have hodd' := not_dvd_relIndex_sup_sup hp hp2 hK h5 hQ1 hQ2 hQ3 ⟨hzT, hzJ⟩ ⟨htT, htJ⟩
    ⟨hztT, hztJ⟩
  have hTE : T₀ ⊓ spinE K ≤ (T₀ ⊓ spinJ₁ K) ⊔ (T₀ ⊓ spinJ₂ K) ⊔ (T₀ ⊓ spinJ₃ K) := by
    rw [← relIndex_eq_one]
    obtain ⟨k, hk⟩ := (hT.2.1.to_inf_left (K := spinE K)).exists_card_eq
    have hd1 : ((T₀ ⊓ spinJ₁ K) ⊔ (T₀ ⊓ spinJ₂ K) ⊔ (T₀ ⊓ spinJ₃ K)).relIndex
        (T₀ ⊓ spinE K) ∣ 2 ^ k := by
      rw [← hk]
      exact Dvd.intro _ (relIndex_mul_card hP'E)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    have hd2 := relIndex_mul_relIndex _ _ _ hP'E (inf_le_right : T₀ ⊓ spinE K ≤ spinE K)
    rw [hj] at hd2 ⊢
    rcases j with _ | j
    · rfl
    · exfalso
      apply hodd'
      rw [← hd2, pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  obtain ⟨τ', hτ'T, hτ'τ', hτ'E⟩ := exists_involution_not_mem_spinE hp hp2 hK h5 hT
  have hidx := index_spinE_eq_two (K := K) hp hp2 hK h5
  intro g hg
  by_cases hgE : g ∈ spinE K
  · exact hP'S (hTE ⟨hg, hgE⟩)
  · have hgτ : g * τ'⁻¹ ∈ spinE K := by
      have h := (mul_mem_iff_of_index_two hidx (a := (⟨g, hT.1 hg⟩ : C))
        (b := (⟨τ'⁻¹, C.inv_mem (hT.1 hτ'T)⟩ : C))).mpr
      have h' : (⟨τ'⁻¹, C.inv_mem (hT.1 hτ'T)⟩ : C) ∉ (spinE K).subgroupOf C := fun h'' =>
        hτ'E (by simpa using inv_mem (show τ'⁻¹ ∈ spinE K from h''))
      exact h ⟨fun h'' => absurd h'' hgE, fun h'' => absurd h'' h'⟩
    have hmem : g * τ'⁻¹ ∈ S :=
      hP'S (hTE (Subgroup.mem_inf.mpr ⟨mul_mem hg (inv_mem hτ'T), hgτ⟩))
    have hτS : τ' ∈ S := hS _ hτ'T hτ'τ'
    have : g = g * τ'⁻¹ * τ' := by group
    rw [this]
    exact mul_mem hmem hτS

end Model

end CFSG.ComponentClassification.HarrisLit.T1
