module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypDefs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.HypModule
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModuleActions
public import Mathlib.FieldTheory.Finiteness

public section

open scoped IsMulCommutative commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {J : Type} [Group J] [Finite J]

theorem exists_abelian_of_hyperplane_action {D : Type} [Group D] [Finite D] {p q n : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) (hn : 2 ≤ n)
    (hcl : ∀ a b : D, ⁅a, b⁆ ∈ Subgroup.center D)
    [IsElementaryAbelian q (D ⧸ Subgroup.center D)] [IsElementaryAbelian q (Subgroup.center D)]
    [MulDistribMulAction J D] [MulDistribMulAction J (D ⧸ Subgroup.center D)]
    (hcompat : ∀ (g : J) (x : D),
      g • (x : D ⧸ Subgroup.center D) = ((g • x : D) : D ⧸ Subgroup.center D))
    {U : Subgroup J} (hU : Nat.card U = p ^ n) (hUexp : ∀ u ∈ U, u ^ p = 1)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u) {σ : J} (hσ : MovesHyperplanes p U σ)
    (hUZ : ∀ u ∈ U, ∀ z ∈ Subgroup.center D, u • z = z)
    (hnt : ∃ u ∈ U, ∃ x : D,
      u • (x : D ⧸ Subgroup.center D) ≠ (x : D ⧸ Subgroup.center D)) :
    ∃ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ Subgroup.center D ≤ E ∧
      q ^ 3 * Nat.card (Subgroup.center D) ≤ Nat.card E := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  have hpF : ((p : ℕ) : ZMod q) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hpq ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h).symm
  let ρ : J →* Module.End (ZMod q) (Additive (D ⧸ Subgroup.center D)) :=
    Theory.Representation.ofElementaryAbelianAction (p := q) (A := J)
      (G := D ⧸ Subgroup.center D)
  obtain ⟨β, hβ⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_comm_pairing q hcl
  have hρ : ∀ (g : J) (x : D), ρ g (Additive.ofMul (x : D ⧸ Subgroup.center D)) =
      Additive.ofMul ((g • x : D) : D ⧸ Subgroup.center D) := fun g x => by
    rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul, hcompat]
  have hsurj : ∀ v : Additive (D ⧸ Subgroup.center D),
      ∃ x : D, Additive.ofMul (x : D ⧸ Subgroup.center D) = v := fun v => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨x, by rw [hx]; rfl⟩
  have hinv : ∀ u ∈ U, ∀ v w, β (ρ u v) (ρ u w) = β v w := by
    intro u hu v w
    obtain ⟨x, rfl⟩ := hsurj v
    obtain ⟨y, rfl⟩ := hsurj w
    rw [hρ, hρ, hβ, hβ]
    congr 2
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.smul_commutator, hUZ u hu _ (hcl x y)]
  have halt : ∀ v, β v v = 0 := by
    intro v
    obtain ⟨x, rfl⟩ := hsurj v
    rw [hβ]
    have : (⟨⁅x, x⁆, hcl x x⟩ : Subgroup.center D) = 1 := Subtype.ext (by simp)
    rw [this]
    rfl
  obtain ⟨H, hHU, hHc, a, haH, u, hu, hua⟩ := HypModule.exists_hyperplane_fixed_not_fixed
    (HypModule.not_dvd_card_of_isElementaryAbelian hpq) hUexp hcomm (by
      obtain ⟨u, hu, x, hx⟩ := hnt
      exact ⟨u, hu, (x : D ⧸ Subgroup.center D), hx⟩)
  have hρ' : ∀ (g : J) (b : D ⧸ Subgroup.center D), ρ g (Additive.ofMul b) =
      Additive.ofMul (g • b) := fun g b =>
    Theory.Representation.ofElementaryAbelianAction_apply_ofMul g b
  have hHyp : HypModule.IsHyp p U H := ⟨hHU, hHc⟩
  have hne : CFSG.LocalAnalysis.RankThreeTheoremC.PlaneModule.proj ρ U H ≠ 0 :=
    HypModule.hproj_ne_zero_of_fixed hpF ρ hU hHyp (v := Additive.ofMul a)
      (fun h hh => by rw [hρ', haH h hh])
      ⟨u, hu, fun h => hua (by rw [hρ'] at h; exact Additive.ofMul.injective h)⟩
  obtain ⟨S, hS3, hSiso⟩ := HypModule.exists_isotropic_three_hyp hpF ρ β hinv halt hU hcomm hσ
    hHyp hne
  let Ssub : Subgroup (D ⧸ Subgroup.center D) :=
    { carrier := {x | Additive.ofMul x ∈ S}
      mul_mem' := fun {a b} ha hb => S.add_mem ha hb
      one_mem' := S.zero_mem
      inv_mem' := fun {a} ha => S.neg_mem ha }
  refine ⟨Ssub.comap (QuotientGroup.mk' (Subgroup.center D)), ?_, ?_, ?_⟩
  · intro x hx y hy
    have h1 : β (Additive.ofMul (x : D ⧸ Subgroup.center D))
        (Additive.ofMul (y : D ⧸ Subgroup.center D)) = 0 := hSiso _ hx _ hy
    rw [hβ] at h1
    have h2 : ⁅x, y⁆ = 1 := congrArg (fun z : Additive (Subgroup.center D) => (z.toMul : D)) h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h2)
  · intro z hz
    show Additive.ofMul (QuotientGroup.mk' (Subgroup.center D) z) ∈ S
    have h : (QuotientGroup.mk' (Subgroup.center D)) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h]
    exact S.zero_mem
  · have h1 := QuotientGroup.card_preimage_mk (Subgroup.center D)
      (Ssub : Set (D ⧸ Subgroup.center D))
    have h2 : Nat.card (Ssub : Set (D ⧸ Subgroup.center D)) = q ^ 3 := by
      have h3 := Module.natCard_eq_pow_finrank (K := ZMod q) (V := S)
      rw [Nat.card_zmod, hS3] at h3
      rw [← h3]
      exact Nat.card_congr
        { toFun := fun x => ⟨Additive.ofMul x.1, x.2⟩
          invFun := fun s => ⟨Additive.toMul s.1, s.2⟩
          left_inv := fun x => rfl
          right_inv := fun s => rfl }
    have h4 : Nat.card (Ssub.comap (QuotientGroup.mk' (Subgroup.center D))) =
        Nat.card (QuotientGroup.mk ⁻¹' (Ssub : Set (D ⧸ Subgroup.center D))) := rfl
    rw [h4, h1, h2, mul_comm]

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
