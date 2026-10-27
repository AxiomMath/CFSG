module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagLin
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4 CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)

theorem od_three_ne_zero_of_charP {K : Type} [Field K] {r : ℕ} [CharP K r] (hr : r.Prime)
    (hr3 : r ≠ 3) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
  have := (CharP.cast_eq_zero_iff K r 3).1 h'
  exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)

theorem od_cube_mul_eq {G : Type*} [Group G] (a φ a₁ a₂ : G) (h1 : φ * a = a₁ * φ)
    (h2 : φ * a₁ = a₂ * φ) : (a * φ) ^ 3 = a * a₁ * a₂ * φ ^ 3 := by
  calc (a * φ) ^ 3 = a * (φ * a) * (φ * a) * φ := by rw [pow_three']; group
    _ = a * (a₁ * φ) * (a₁ * φ) * φ := by rw [h1]
    _ = a * a₁ * (φ * a₁) * φ * φ := by group
    _ = a * a₁ * (a₂ * φ) * φ * φ := by rw [h2]
    _ = a * a₁ * a₂ * φ ^ 3 := by rw [pow_three']; group

theorem uniThree_card_mul_gcd {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) := by
  rw [← CFSG.SectionRank.OddCover.card_statedSU_three hK,
    ← CFSG.GH74.GLS.LU.Local.card_scalars_statedSU_three (Fact.out : p.Prime) hf hK]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))).symm

theorem uniThree_eightyOne_dvd {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) (h3 : 3 ∣ p ^ f + 1)
    (h9 : 9 ∣ p ^ f + 1) : 81 ∣ Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) := by
  have hc := uniThree_card_mul_gcd hK hf
  rw [Nat.gcd_eq_left h3] at hc
  set q := p ^ f with hqdef
  have hq1 : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ := h9
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · omega
    · exact h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hq : q = 9 * m' + 8 := by omega
  have e2 : q ^ 2 - 1 = 9 * ((m' + 1) * (9 * m' + 7)) := by
    rw [hq]; apply Nat.sub_eq_of_eq_add; ring
  have e3 : q ^ 3 + 1 = 27 * (27 * m' ^ 3 + 72 * m' ^ 2 + 64 * m' + 19) := by
    rw [hq]; ring
  rw [e2, e3] at hc
  have : 3 * 81 ∣ 3 * Nat.card (StatedProj (StatedSU 3 q K)) := by
    rw [mul_comm 3 (Nat.card _), hc]
    exact ⟨q ^ 3 * ((m' + 1) * (9 * m' + 7)) * (27 * m' ^ 3 + 72 * m' ^ 2 + 64 * m' + 19),
      by ring⟩
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

theorem uniThree_card_two {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) (h2 : p ^ f = 2) :
    Nat.card (StatedProj (StatedSU 3 (p ^ f) K)) = 72 := by
  have hc := uniThree_card_mul_gcd hK hf
  rw [h2] at hc ⊢
  norm_num at hc ⊢
  omega

theorem uniThree_two_false {p f : ℕ} {K : Type} [Field K] [Finite K] [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hf : 1 ≤ f) (h2 : p ^ f = 2)
    {L : Type} [Group L] [IsSimpleGroup L] (hnab : ∃ a b : L, a * b ≠ b * a)
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K)) : False := by
  have hc := uniThree_card_two hK hf h2
  haveI : Finite (StatedProj (StatedSU 3 (p ^ f) K)) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hc]; norm_num
  haveI : Finite L := Finite.of_equiv _ e.symm.toEquiv
  have hsolv : Group.IsSolvable L := by
    have h72 : Nat.card L ∣ 72 := by
      rw [Nat.card_congr e.toEquiv, hc]
    exact CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg.isSolvable_of_card_dvd_seventy_two
      h72
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := L)).2 hsolv a b)

theorem uniThree_nine_dvd {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) (h3 : 3 ∣ p ^ f + 1) (B : Subgroup (MulAut (unitaryPSU h 3)))
    (hB : IsElemAbelian 3 B) (hc : 27 ≤ Nat.card B) : 9 ∣ p ^ f + 1 := by
  haveI := h.finite
  have hp := h.prime
  have hp3 : p ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by have := h.one_le; omega)
    have := (Nat.dvd_add_right h1).1 h3
    omega
  haveI := h.charP
  have h30 : (3 : K) ≠ 0 := od_three_ne_zero_of_charP hp hp3
  by_contra h9
  set N := (psuConj h).range with hN
  have hBN : B ≤ N := by
    intro b hb
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    by_cases hσ : σ = 1
    · rw [hAσ, hσ, map_one, mul_one]
      exact ⟨A, rfl⟩
    · exfalso
      have hb3 : b ^ 3 = 1 := hB.2 b hb
      set A₁ : unitaryIsom3 h := ⟨glAut σ A, glAut_mem_unitaryIsom3 σ A.2⟩ with hA₁
      set A₂ : unitaryIsom3 h := ⟨glAut σ A₁, glAut_mem_unitaryIsom3 σ A₁.2⟩ with hA₂
      have h1 : psuField h σ * psuConj h A = psuConj h A₁ * psuField h σ := by
        have := psuField_mul_psuConj_mul_inv σ A
        rw [← this]
        group
      have h2 : psuField h σ * psuConj h A₁ = psuConj h A₂ * psuField h σ := by
        have := psuField_mul_psuConj_mul_inv σ A₁
        rw [← this]
        group
      have h3' := od_cube_mul_eq (psuConj h A) (psuField h σ) (psuConj h A₁) (psuConj h A₂) h1 h2
      rw [← hAσ, hb3, ← map_pow, ← map_mul, ← map_mul] at h3'
      have h4 : psuConj h (A * A₁ * A₂) * psuField h (σ ^ 3) = 1 := h3'.symm
      have hσ3 : σ ^ 3 = 1 := (eq_one_of_psuConj_mul_psuField_eq_one _ _ h4).1
      have hord : orderOf σ = 3 := by
        haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact orderOf_eq_prime hσ3 hσ
      have hcard := (card_ringAut_and_isCyclic hp K h.card).1
      have h3f : 3 ∣ 2 * f := by
        rw [← hcard, ← hord]
        exact orderOf_dvd_natCard σ
      have h3f' : 3 ∣ f := by
        rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3f with h | h
        · omega
        · exact h
      obtain ⟨m, rfl⟩ := h3f'
      have hq3 : p ^ (3 * m) = (p ^ m) ^ 3 := by rw [mul_comm, pow_mul]
      rw [hq3] at h3 h9
      exact h9 (od_nine_dvd_cube_add_one h3)
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := ((B ⊓ N).subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h99 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE]
    refine card_le_nine_of_pgl3 h30 E ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hBc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
      rw [this, map_one]
  rw [inf_eq_left.2 hBN] at h99
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
