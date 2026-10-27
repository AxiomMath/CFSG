module

public import CFSG.CGT.PushingUpLit.A78One.OneStmts
import CFSG.CGT.PushingUpLit.A78One.CjLemmas
import CFSG.CGT.PushingUpLit.A78One.DictStar
import CFSG.CGT.PushingUpLit.A78One.Star
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.Quasithin
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G] [Finite G]

namespace CexCtx

variable {L M : Subgroup G} {n : ℕ} {T T' : Subgroup G} {x : G}

theorem card_Q_le (c : CexCtx L M n T T' x) :
    Nat.card ↥(T' ⊓ (L ⊔ cexP L T)) ≤ 2 ^ n * Nat.card ↥(cexP L T) := by
  classical
  obtain ⟨φ, -, hφk⟩ := c.exists_phi
  have hPN : cexP L T ≤ L ⊔ cexP L T := le_sup_right
  have hQN : T' ⊓ (L ⊔ cexP L T) ≤ L ⊔ cexP L T := inf_le_right
  have hPQ : cexP L T ≤ T' ⊓ (L ⊔ cexP L T) := le_inf c.v0_P_le hPN
  let ψ : ↥(T' ⊓ (L ⊔ cexP L T)) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    φ.comp (Subgroup.inclusion hQN)
  have h1 : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = Nat.card ↥(T' ⊓ (L ⊔ cexP L T)) := by
    rw [← ψ.ker.card_mul_index, Subgroup.index_ker]
  have hker : ψ.ker = (cexP L T).subgroupOf (T' ⊓ (L ⊔ cexP L T)) := by
    ext q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show φ (Subgroup.inclusion hQN q) = 1 ↔ (q : G) ∈ cexP L T
    rw [← MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf]
    rfl
  have hkercard : Nat.card ↥ψ.ker = Nat.card ↥(cexP L T) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPQ).toEquiv
  have hQ2 : IsPGroup 2 ↥(T' ⊓ (L ⊔ cexP L T)) :=
    c.sylow.isPGroup.to_le (inf_le_left.trans c.le)
  have hR2 : IsPGroup 2 ↥ψ.range := hQ2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n :=
    GaloisField.card 2 n (by have := c.hyp.two_le; omega)
  have hrange : Nat.card ↥ψ.range ≤ 2 ^ n := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hR2
    have hdvd : Nat.card ↥ψ.range ∣
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Subgroup.card_subgroup_dvd_card ψ.range
    rw [card_sl2_field, hFcard, hk] at hdvd
    have hodd : Odd ((2 ^ n) ^ 2 - 1) := odd_sq_two_pow_sub_one (by have := c.hyp.two_le; omega)
    have hcop : Nat.Coprime (2 ^ k) ((2 ^ n) ^ 2 - 1) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
    have h2 : 2 ^ k ∣ 2 ^ n := hcop.dvd_of_dvd_mul_right hdvd
    rw [hk]
    exact Nat.le_of_dvd (by positivity) h2
  calc Nat.card ↥(T' ⊓ (L ⊔ cexP L T)) = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := h1.symm
    _ = Nat.card ↥(cexP L T) * Nat.card ↥ψ.range := by rw [hkercard]
    _ ≤ Nat.card ↥(cexP L T) * 2 ^ n := Nat.mul_le_mul_left _ hrange
    _ = 2 ^ n * Nat.card ↥(cexP L T) := mul_comm _ _

theorem offender_sylow (c : CexCtx L M n T T' x) {A : Subgroup G} (hA : IsMaxElemAbelian T' A)
    (hnt : ¬ A ≤ cexP L T) :
    A ≤ L ⊔ cexP L T ∧ A ⊔ cexP L T = T' ⊓ (L ⊔ cexP L T) := by
  have H45 := c.hyp45 hA (c.v0_not_le_centralizer hA hnt)
  have hAL : A ≤ L ⊔ cexP L T := by
    intro a ha
    obtain ⟨l, hl, hact⟩ := H45.acts_as a ha
    have h1 := H45.inv_mul_mem_centralizer ha hl hact
    rw [c.centralizer_U] at h1
    have e : a = l * (l⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right h1)
  refine ⟨hAL, ?_⟩
  have hle : A ⊔ cexP L T ≤ T' ⊓ (L ⊔ cexP L T) :=
    sup_le (le_inf hA.1 hAL) (le_inf c.v0_P_le le_sup_right)
  have hAN : A ≤ Subgroup.normalizer (cexP L T : Set G) := fun a ha =>
    c.v0_le_normalizer_P' (c.le (hA.1 ha))
  have hAinf : A ⊓ cexP L T = A ⊓ Subgroup.centralizer (blockU L : Set G) := by
    rw [← c.v0_inf_eq]
    ext y
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hy, -, hyc⟩
      exact ⟨hy, hyc⟩
    · rintro ⟨hy, hyc⟩
      exact ⟨hy, hA.1 hy, hyc⟩
  have hprod := K1214.card_sup_mul_card_inf_of_le_normalizer hAN
  rw [sup_comm (cexP L T) A, inf_comm (cexP L T) A, hAinf] at hprod
  have hdiv := H45.card_inf_centralizer
  have hpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (blockU L : Set G)) := Nat.card_pos
  have hAP : Nat.card ↥(A ⊔ cexP L T) = 2 ^ n * Nat.card ↥(cexP L T) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hprod, ← hdiv]
    ring
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAP]; exact c.card_Q_le)

theorem sylow_eq_U1 (c : CexCtx L M n T T' x) :
    T' ⊓ (L ⊔ cexP L T) = cj x⁻¹ (blockU L) ⊔ cexP L T := by
  obtain ⟨A₁, hA₁, hA₁P⟩ := c.exists_not_le
  have H₁ := c.hyp45 hA₁ (c.v0_not_le_centralizer hA₁ hA₁P)
  obtain ⟨A₀, hA₀P⟩ : ∃ A₀, IsMaxElemAbelian (cexP L T) A₀ := by
    refine ⟨Hyp45.bGrp L A₁, ?_⟩
    have := H₁.isMaxElemAbelian_B_P
    rwa [c.v0_inf_eq] at this
  have hA₀T' : IsMaxElemAbelian T' A₀ := c.isMax_of_isMax_P hA₀P
  have hA'T' : IsMaxElemAbelian T' (cj x A₀) := cjx_isMax_of_normalizer hA₀T' c.hx
  have hA'nt : ¬ cj x A₀ ≤ cexP L T := by
    intro hle
    have hA'P := c.v0_isMax_P_of_le hA'T' hle
    have h2 : IsMaxElemAbelian (cj x⁻¹ (cexP L T)) A₀ := by
      have := cjx_isMax x⁻¹ hA'P
      rwa [cjx_inv_cj] at this
    exact c.star hA₀P h2
  have H' := c.hyp45 hA'T' (c.v0_not_le_centralizer hA'T' hA'nt)
  have hBT' : IsMaxElemAbelian T' (Hyp45.bGrp L (cj x A₀)) := H'.isMaxElemAbelian_B
  have hBP : IsMaxElemAbelian (cexP L T) (Hyp45.bGrp L (cj x A₀)) := by
    have := H'.isMaxElemAbelian_B_P
    rwa [c.v0_inf_eq] at this
  have hB₁T' : IsMaxElemAbelian T' (cj x⁻¹ (Hyp45.bGrp L (cj x A₀))) :=
    cjx_isMax_of_normalizer hBT' ((Subgroup.normalizer (T' : Set G)).inv_mem c.hx)
  have hB₁Px : IsMaxElemAbelian (cj x⁻¹ (cexP L T)) (cj x⁻¹ (Hyp45.bGrp L (cj x A₀))) :=
    cjx_isMax x⁻¹ hBP
  have hB₁nt : ¬ cj x⁻¹ (Hyp45.bGrp L (cj x A₀)) ≤ cexP L T := fun hle =>
    c.star (c.v0_isMax_P_of_le hB₁T' hle) hB₁Px
  obtain ⟨-, hF1⟩ := c.offender_sylow hB₁T' hB₁nt
  rw [← hF1]
  have hB1 : cj x⁻¹ (Hyp45.bGrp L (cj x A₀)) = (A₀ ⊓ Subgroup.centralizer
      ((cj x⁻¹ (blockU L) : Subgroup G) : Set G)) ⊔ cj x⁻¹ (blockU L) := by
    rw [cjx_bGrp, cjx_inv_cj]
  rw [hB1]
  apply le_antisymm
  · exact sup_le (sup_le ((inf_le_left.trans hA₀P.1).trans le_sup_right) le_sup_left) le_sup_right
  · exact sup_le_sup_right le_sup_right _

end CexCtx

end CFSG.CGT.PushingUpLit.A78One
