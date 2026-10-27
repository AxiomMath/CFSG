module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.SubfieldMaximalSL2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.NormalizerSubfieldSL2
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Proving.GoursatCentral
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFour

set_option linter.unusedSectionVars false

public section

open Subgroup CFSG.HardMathSupport.Seitz.TrialityOdd.Proving
open scoped MatrixGroups

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.GoursatJ

section Basic

variable {G : Type*} [Group G]

theorem inf_eq_bot_or_le {P Q D : Subgroup G} (hc : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p)
    (hD : D ≤ P ⊔ Q) (hs : IsSimpleGroup D) : D ⊓ P = ⊥ ∨ D ≤ P := by
  have hnorm : ((D ⊓ P).subgroupOf D).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ D ⊓ P := hn
    obtain ⟨p, hp, q, hq, hpq⟩ := mem_sup_eq_mul_of_comm P Q hc (g : G) (hD g.2)
    have hnq : (n : G) * q = q * n := (hc _ hn'.2 q hq)
    have e : ((g * n * g⁻¹ : D) : G) = p * n * p⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hpq]
      calc p * q * n * (p * q)⁻¹ = p * (q * n) * q⁻¹ * p⁻¹ := by group
        _ = p * (n * q) * q⁻¹ * p⁻¹ := by rw [hnq]
        _ = p * n * p⁻¹ := by group
    show ((g * n * g⁻¹ : D) : G) ∈ D ⊓ P
    refine ⟨(g * n * g⁻¹ : D).2, ?_⟩
    rw [e]
    exact P.mul_mem (P.mul_mem hp hn'.2) (P.inv_mem hp)
  rcases (haveI := hnorm; hs.eq_bot_or_eq_top_of_normal ((D ⊓ P).subgroupOf D)) with h | h
  · left
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx.1⟩ : D) ∈ (D ⊓ P).subgroupOf D := hx
    rw [h] at hmem
    have := (Subgroup.mem_bot.1 hmem)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · right
    intro x hx
    have hmem : (⟨x, hx⟩ : D) ∈ (D ⊓ P).subgroupOf D := by rw [h]; trivial
    exact hmem.2

theorem false_of_index_two_perfect {H : Type*} [Group H] [Finite H] (hperf : Group.IsPerfect H)
    (N : Subgroup H) (hN : 2 * Nat.card N = Nat.card H) : False := by
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hidx : N.index = 2 := by
    have h := Subgroup.card_mul_index N
    have : Nat.card N * N.index = Nat.card N * 2 := by rw [h, ← hN]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have : N.Normal := Subgroup.normal_of_index_eq_two hidx
  have hq : Nat.card (H ⧸ N) = 2 := by rw [← Subgroup.index_eq_card, hidx]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (H ⧸ N) := isCyclic_of_prime_card hq
  have hcomm : ∀ x y : H ⧸ N, x * y = y * x := fun x y => (IsCyclic.isMulCommutative (α := H ⧸ N)).is_comm.comm x y
  have hle : (⊤ : Subgroup H) ≤ N := by
    rw [← hperf.commutator_eq_top]
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    simp only [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (x : H ⧸ N) y]
    group
  have h1 : N = ⊤ := top_le_iff.1 hle
  rw [h1, Subgroup.index_top] at hidx
  omega

end Basic

section SL2

variable {G : Type*} [Group G] {F : Type} [Field F] [Finite F]

theorem sl2_perfect (h4 : 4 ≤ Nat.card F) : Group.IsPerfect SL(2, F) :=
  CFSG.RankThree.PartOne.KCOrthogonal.sl2_isPerfect h4

theorem range_perfect (h4 : 4 ≤ Nat.card F) (ι : SL(2, F) →* G) :
    ⁅ι.range, ι.range⁆ = ι.range := by
  have h := (sl2_perfect h4).commutator_eq_top
  have h' : ⁅(⊤ : Subgroup SL(2, F)), ⊤⁆ = ⊤ := h
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h']

theorem range_simple_quot (h4 : 4 ≤ Nat.card F) {ι : SL(2, F) →* G}
    (hι : Function.Injective ι) :
    IsSimpleGroup (↥ι.range ⧸ Subgroup.center ↥ι.range) := by
  let e : SL(2, F) ≃* ι.range := MonoidHom.ofInjective hι
  have he : (Subgroup.center SL(2, F)).map e.toMonoidHom = Subgroup.center ι.range :=
    Subgroup.map_center_eq e
  let e' : SL(2, F) ⧸ Subgroup.center SL(2, F) ≃* ↥ι.range ⧸ Subgroup.center ↥ι.range :=
    QuotientGroup.congr _ _ e he
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact MulEquiv.isSimpleGroup e'.symm

theorem false_of_le_range (h4 : 4 ≤ Nat.card F) {ι : SL(2, F) →* G}
    (hι : Function.Injective ι) {D : Subgroup G} (hD : D ≤ ι.range)
    (hcard : 2 * Nat.card D = Nat.card SL(2, F)) : False := by
  have hmap : (D.comap ι).map ι = D := Subgroup.map_comap_eq_self hD
  have hc : Nat.card (D.comap ι) = Nat.card D := by
    conv_rhs => rw [← hmap]
    exact (Subgroup.card_map_of_injective hι).symm
  exact false_of_index_two_perfect (sl2_perfect h4) (D.comap ι) (by rw [hc]; exact hcard)

theorem isOddPrimePower_of_ringChar {L : Type} [Field L] [Finite L] (h : ringChar L ≠ 2) :
    CFSG.GorensteinWalter.IsOddPrimePower (Nat.card L) := by
  have hp : (ringChar L).Prime := CharP.char_is_prime L (ringChar L)
  have : Fact (ringChar L).Prime := ⟨hp⟩
  have : CharP L (ringChar L) := ringChar.charP L
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨n, -, hn⟩ := FiniteField.card L (ringChar L)
  exact ⟨ringChar L, (n : ℕ), hp, hp.odd_of_ne_two h, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

theorem card_cube {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]
    (h3 : Module.finrank F K = 3) : Nat.card K = Nat.card F ^ 3 := by
  rw [Module.natCard_eq_pow_finrank (K := F) (V := K), h3]

theorem ringChar_ne_two_of_algebra {F K : Type} [Field F] [Field K] [Algebra F K]
    (hK : ringChar K ≠ 2) : ringChar F ≠ 2 := by
  have hres : ringChar F = ringChar K := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [← ringChar.spec F (ringChar K)]
      apply (algebraMap F K).injective
      rw [map_natCast, map_zero]
      exact (ringChar.spec K (ringChar K)).2 dvd_rfl
    · rw [← ringChar.spec K (ringChar F)]
      have : ((ringChar F : ℕ) : F) = 0 := (ringChar.spec F (ringChar F)).2 dvd_rfl
      rw [← map_natCast (algebraMap F K), this, map_zero]
  rwa [hres]

theorem not_iso_quot {K : Type} [Field K] [Algebra F K] [Finite K] (h3 : Module.finrank F K = 3)
    (hK : ringChar K ≠ 2) (h4 : 4 ≤ Nat.card F)
    {ιA : SL(2, F) →* G} {ιB : SL(2, K) →* G} (hA : Function.Injective ιA)
    (hB : Function.Injective ιB) :
    ¬ Nonempty (↥ιA.range ⧸ Subgroup.center ↥ιA.range ≃* ↥ιB.range ⧸ Subgroup.center ↥ιB.range) := by
  rintro ⟨e⟩
  have hF : ringChar F ≠ 2 := ringChar_ne_two_of_algebra hK
  let eA : SL(2, F) ⧸ Subgroup.center SL(2, F) ≃* ↥ιA.range ⧸ Subgroup.center ↥ιA.range :=
    QuotientGroup.congr _ _ (MonoidHom.ofInjective hA) (Subgroup.map_center_eq _)
  let eB : SL(2, K) ⧸ Subgroup.center SL(2, K) ≃* ↥ιB.range ⧸ Subgroup.center ↥ιB.range :=
    QuotientGroup.congr _ _ (MonoidHom.ofInjective hB) (Subgroup.map_center_eq _)
  have hcard : Nat.card (CFSG.GorensteinWalter.PSL2 F) = Nat.card (CFSG.GorensteinWalter.PSL2 K) :=
    Nat.card_congr (eA.trans (e.trans eB.symm)).toEquiv
  rw [CFSG.GorensteinWalter.psl2_card_formula F (isOddPrimePower_of_ringChar hF),
    CFSG.GorensteinWalter.psl2_card_formula K (isOddPrimePower_of_ringChar hK),
    card_cube h3] at hcard
  have hq : 4 ≤ Nat.card F := h4
  set q := Nat.card F
  have hx : 15 ≤ q ^ 2 - 1 := by
    have : 16 ≤ q ^ 2 := by nlinarith
    omega
  have hxy : q ^ 2 - 1 ≤ (q ^ 3) ^ 2 - 1 := by
    have : q ^ 2 ≤ (q ^ 3) ^ 2 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have h3q : 4 * q ≤ q ^ 3 := by nlinarith [pow_pos (show 0 < q by omega) 2]
  have hBA : 4 * (q * (q ^ 2 - 1)) ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := by
    calc 4 * (q * (q ^ 2 - 1)) = (4 * q) * (q ^ 2 - 1) := by ring
      _ ≤ q ^ 3 * ((q ^ 3) ^ 2 - 1) := Nat.mul_le_mul h3q hxy
  have hApos : 0 < q * (q ^ 2 - 1) := Nat.mul_pos (by omega) (by omega)
  generalize q * (q ^ 2 - 1) = A at *
  generalize q ^ 3 * ((q ^ 3) ^ 2 - 1) = B at *
  omega

theorem sl2Range_card {K : Type} [Field K] [Algebra F K] :
    Nat.card (sl2Range F K) = Nat.card SL(2, F) := by
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K)) := by
    intro x y h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simp only [Matrix.SpecialLinearGroup.map_apply_coe] at this
    exact Matrix.map_injective (algebraMap F K).injective this
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem sl2_map_injective {K : Type} [Field K] [Algebra F K] :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K)) := by
  intro x y h
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe] at this
  exact Matrix.map_injective (algebraMap F K).injective this

end SL2

section Main

variable {G : Type*} [Group G] {F K : Type} [Field F] [Field K] [Algebra F K] [Finite F] [Finite K]

theorem neg_eq_neg_one_mul {R : Type} [Field R] (a : SL(2, R)) : -a = (-1 : SL(2, R)) * a := by
  ext1
  simp [Matrix.SpecialLinearGroup.coe_neg]

theorem neg_one_mul_neg_one' {R : Type} [Field R] : (-1 : SL(2, R)) * -1 = 1 := by
  ext1
  simp

theorem neg_one_ne_one' {R : Type} [Field R] [Finite R] (h : ringChar R ≠ 2) : (-1 : SL(2, R)) ≠ 1 := by
  intro hh
  have := congrArg (fun A : SL(2, R) => (A : Matrix (Fin 2) (Fin 2) R) 0 0) hh
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at this
  have h2 : (2 : R) = 0 := by linear_combination -this
  have : ringChar R ∣ 2 := (ringChar.spec R 2).1 (by exact_mod_cast h2)
  have := (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime R (ringChar R)) Nat.prime_two).1 this
  exact h this

theorem goursatJ
    (h3 : Module.finrank F K = 3) (hK : ringChar K ≠ 2) (hF : 5 ≤ Nat.card F)
    (ιA : SL(2, F) →* G) (ιB : SL(2, K) →* G)
    (hA : Function.Injective ιA) (hB : Function.Injective ιB)
    (hc : ∀ a b, ιA a * ιB b = ιB b * ιA a) (hz : ιA (-1) = ιB (-1))
    (J : Subgroup G) (hJA : ∀ a, ιA a ∈ J) (hJB : ∀ b, ιB b ∈ J ↔ b ∈ sl2Range F K)
    (D : Subgroup G) (hDs : IsSimpleGroup D)
    (hDc : 2 * Nat.card D = Nat.card SL(2, F))
    (hDM : D ≤ ιA.range ⊔ ιB.range) (hDJ : D ≤ J)
    (ν : G) (hν : ν ∈ ιA.range ⊔ ιB.range) :
    ν ∈ J ∨ ιA.range ⊔ ιB.range ≤ D ⊔ D.map (MulAut.conj ν).toMonoidHom := by
  classical
  have h4 : 4 ≤ Nat.card F := by omega
  have hcomm : ∀ a ∈ ιA.range, ∀ b ∈ ιB.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact hc a b
  let Φ : SL(2, F) × SL(2, K) →* G := ιA.noncommCoprod ιB (fun a b => hc a b)
  have hΦ : ∀ a b, Φ (a, b) = ιA a * ιB b := fun a b => rfl
  have hzz : ιA (-1) * ιA (-1) = 1 := by rw [← map_mul, neg_one_mul_neg_one', map_one]
  set Dt : Subgroup (SL(2, F) × SL(2, K)) := D.comap Φ with hDt
  have hDtJ : ∀ p ∈ Dt, p.2 ∈ sl2Range F K := by
    rintro ⟨a, b⟩ hp
    have h1 : ιA a * ιB b ∈ J := hDJ hp
    have h2 : ιB b ∈ J := by
      have := J.mul_mem (J.inv_mem (hJA a)) h1
      simpa [mul_assoc] using this
    exact (hJB b).1 h2
  have hDB : D ⊓ ιB.range = ⊥ := by
    rcases inf_eq_bot_or_le (P := ιB.range) (Q := ιA.range) (fun p hp q hq => (hcomm q hq p hp).symm)
      (by rwa [sup_comm]) hDs with h | h
    · exact h
    · exfalso
      have hle : D ≤ (ιB.comp (Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K))).range := by
        intro d hd
        obtain ⟨b, rfl⟩ := h hd
        obtain ⟨s, hs⟩ := (hJB b).1 (hDJ hd)
        exact ⟨s, by simp [hs]⟩
      exact false_of_le_range h4 (hB.comp sl2_map_injective) hle hDc
  have hDA : D ⊓ ιA.range = ⊥ := by
    rcases inf_eq_bot_or_le (P := ιA.range) (Q := ιB.range) hcomm hDM hDs with h | h
    · exact h
    · exact (false_of_le_range h4 hA h hDc).elim
  have hε : ((-1 : SL(2, F)), (-1 : SL(2, K))) ∈ Dt := by
    show Φ _ ∈ D
    rw [hΦ, ← hz, hzz]
    exact D.one_mem
  have hdec := mem_sup_eq_mul_of_comm ιA.range ιB.range hcomm
  let f : Dt →* G := Φ.comp Dt.subtype
  have hfr : f.range = D := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact x.2
    · intro d hd
      obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := hdec d (hDM hd)
      exact ⟨⟨(a, b), hd⟩, rfl⟩
  have hker : 1 < Nat.card f.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro hbot
    have hmem : (⟨_, hε⟩ : Dt) ∈ f.ker := by
      show Φ ((-1 : SL(2, F)), (-1 : SL(2, K))) = 1
      rw [hΦ, ← hz, hzz]
    rw [hbot, Subgroup.mem_bot] at hmem
    have := congrArg (fun x : Dt => (x : SL(2, F) × SL(2, K)).1) hmem
    exact neg_one_ne_one' (R := F) (ringChar_ne_two_of_algebra hK) this
  have hDtcard : Nat.card SL(2, F) ≤ Nat.card Dt := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfr] at h
    have : 2 * Nat.card D ≤ Nat.card f.ker * Nat.card D :=
      Nat.mul_le_mul_right _ hker
    omega
  let pr1 : Dt →* SL(2, F) := (MonoidHom.fst _ _).comp Dt.subtype
  let pr2 : Dt →* SL(2, K) := (MonoidHom.snd _ _).comp Dt.subtype
  have hpr1 : Function.Injective pr1 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, hx⟩ h
    have ha : a = 1 := h
    subst ha
    have hbD : ιB b ∈ D := by
      have : Φ (1, b) ∈ D := hx
      simpa [hΦ] using this
    have hmem : ιB b ∈ D ⊓ ιB.range := ⟨hbD, b, rfl⟩
    rw [hDB, Subgroup.mem_bot] at hmem
    have hb : b = 1 := hB (by rw [hmem, map_one])
    subst hb
    rfl
  have hpr2 : Function.Injective pr2 := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, hx⟩ h
    have hb : b = 1 := h
    subst hb
    have haD : ιA a ∈ D := by
      have : Φ (a, 1) ∈ D := hx
      simpa [hΦ] using this
    have hmem : ιA a ∈ D ⊓ ιA.range := ⟨haD, a, rfl⟩
    rw [hDA, Subgroup.mem_bot] at hmem
    have ha : a = 1 := hA (by rw [hmem, map_one])
    subst ha
    rfl
  have hcardr1 : Nat.card pr1.range = Nat.card Dt :=
    (Nat.card_congr (MonoidHom.ofInjective hpr1).toEquiv).symm
  have hcardr2 : Nat.card pr2.range = Nat.card Dt :=
    (Nat.card_congr (MonoidHom.ofInjective hpr2).toEquiv).symm
  have hr1 : pr1.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : Nat.card pr1.range ≤ Nat.card SL(2, F) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
    omega
  have hr2 : pr2.range = sl2Range F K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact hDtJ x.1 x.2
    · rw [sl2Range_card]
      omega
  have hsurjA : ∀ a : SL(2, F), ∃ b, ιA a * ιB b ∈ D := by
    intro a
    have : a ∈ pr1.range := by rw [hr1]; trivial
    obtain ⟨⟨⟨a', b⟩, hx⟩, h⟩ := this
    have ha : a' = a := h
    subst ha
    exact ⟨b, hx⟩
  have hsurjB : ∀ s ∈ sl2Range F K, ∃ a, ιA a * ιB s ∈ D := by
    intro s hs
    have : s ∈ pr2.range := by rw [hr2]; exact hs
    obtain ⟨⟨⟨a, b⟩, hx⟩, h⟩ := this
    have hb : b = s := h
    subst hb
    exact ⟨a, hx⟩
  obtain ⟨_, ⟨a₀, rfl⟩, _, ⟨b₀, rfl⟩, hνab⟩ := hdec ν hν
  by_cases hnorm : ∀ s ∈ sl2Range F K, b₀ * s * b₀⁻¹ ∈ sl2Range F K
  · left
    have hb₀ : b₀ ∈ sl2Range F K := by
      obtain ⟨y, hy, hyb⟩ := mem_SL2_of_normalizes_SL2 h3 (b₀ : Matrix (Fin 2) (Fin 2) K) b₀.2 (by
        intro x hx
        have hmem : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K)
            (⟨x, hx⟩ : SL(2, F)) ∈ sl2Range F K := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ := hnorm _ hmem
        refine ⟨(y : Matrix (Fin 2) (Fin 2) F), y.2, ?_⟩
        have h1 : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) y =
            b₀ * Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) ⟨x, hx⟩ * b₀⁻¹ := hy
        have h2 : Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) y * b₀ =
            b₀ * Matrix.SpecialLinearGroup.map (n := Fin 2) (algebraMap F K) ⟨x, hx⟩ := by
          rw [h1]; group
        have h3' := congrArg (fun z : SL(2, K) => (z : Matrix (Fin 2) (Fin 2) K)) h2
        simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.map_apply_coe]
          at h3'
        exact h3'.symm)
      refine ⟨(⟨y, hy⟩ : SL(2, F)), Subtype.ext ?_⟩
      exact hyb.symm
    rw [hνab]
    exact J.mul_mem (hJA a₀) ((hJB b₀).2 hb₀)
  · right
    push Not at hnorm
    obtain ⟨s, hs, hsn⟩ := hnorm
    set X : Subgroup G := D ⊔ D.map (MulAut.conj ν).toMonoidHom with hX
    have hνM : ν ∈ ιA.range ⊔ ιB.range := hν
    have hD''M : D.map (MulAut.conj ν).toMonoidHom ≤ ιA.range ⊔ ιB.range := by
      rintro _ ⟨d, hd, rfl⟩
      have := (ιA.range ⊔ ιB.range).mul_mem ((ιA.range ⊔ ιB.range).mul_mem hνM (hDM hd))
        ((ιA.range ⊔ ιB.range).inv_mem hνM)
      simpa [MulAut.conj_apply] using this
    have hXM : X ≤ ιA.range ⊔ ιB.range := sup_le hDM hD''M
    set Y : Subgroup SL(2, K) := (X.comap Φ).map (MonoidHom.snd _ _) with hY
    have hYmem : ∀ b : SL(2, K), b ∈ Y ↔ ∃ a, ιA a * ιB b ∈ X := by
      intro b
      constructor
      · rintro ⟨⟨a, b'⟩, hp, rfl⟩
        exact ⟨a, hp⟩
      · rintro ⟨a, ha⟩
        exact ⟨(a, b), ha, rfl⟩
    have hY0 : sl2Range F K ≤ Y := by
      intro b hb
      obtain ⟨a, ha⟩ := hsurjB b hb
      exact (hYmem b).2 ⟨a, (le_sup_left : D ≤ X) ha⟩
    have hj : b₀ * s * b₀⁻¹ ∈ Y := by
      obtain ⟨a, ha⟩ := hsurjB s hs
      refine (hYmem _).2 ⟨a₀ * a * a₀⁻¹, ?_⟩
      have hmem : ν * (ιA a * ιB s) * ν⁻¹ ∈ X :=
        (le_sup_right : D.map (MulAut.conj ν).toMonoidHom ≤ X) ⟨_, ha, by simp [MulAut.conj_apply]⟩
      have e : ν * (ιA a * ιB s) * ν⁻¹ = ιA (a₀ * a * a₀⁻¹) * ιB (b₀ * s * b₀⁻¹) := by
        have h1 : ν = Φ (a₀, b₀) := by rw [hνab]; rfl
        have h2 : ιA a * ιB s = Φ (a, s) := rfl
        rw [h1, h2, ← map_inv, ← map_mul, ← map_mul]
        show Φ _ = Φ (a₀ * a * a₀⁻¹, b₀ * s * b₀⁻¹)
        congr 1
      rwa [e] at hmem
    have hYtop : Y = ⊤ := sl2_range_maximal h3 hK hF Y hY0 hj hsn
    have hXA : X ⊔ ιA.range = ιA.range ⊔ ιB.range := by
      refine le_antisymm (sup_le hXM le_sup_left) (sup_le ?_ ?_)
      · exact le_sup_right
      · rintro _ ⟨b, rfl⟩
        have hb : b ∈ Y := by rw [hYtop]; trivial
        obtain ⟨a, ha⟩ := (hYmem b).1 hb
        have : ιB b = (ιA a)⁻¹ * (ιA a * ιB b) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨a⁻¹, by simp⟩)
          (Subgroup.mem_sup_left ha)
    have hXB : X ⊔ ιB.range = ιA.range ⊔ ιB.range := by
      refine le_antisymm (sup_le hXM le_sup_right) (sup_le ?_ ?_)
      · rintro _ ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := hsurjA a
        have : ιA a = (ιA a * ιB b) * (ιB b)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((le_sup_left : D ≤ X) hb))
          (Subgroup.mem_sup_right ⟨b⁻¹, by simp⟩)
      · exact le_sup_right
    have h4K : 4 ≤ Nat.card K := by
      rw [card_cube h3]
      calc 4 ≤ Nat.card F := h4
        _ ≤ Nat.card F ^ 3 := Nat.le_self_pow (by norm_num) _
    have hXeq := goursat_eq_sup_of_perfect ιA.range ιB.range X hcomm (range_simple_quot h4 hA)
      (range_simple_quot h4K hB) (not_iso_quot h3 hK h4 hA hB) hXA hXB hXM
      (range_perfect h4 ιA) (range_perfect h4K ιB)
    exact hXeq.ge


end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.GoursatJ
