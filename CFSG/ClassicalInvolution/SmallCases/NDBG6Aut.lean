module

public import CFSG.LieType.Chevalley.OddF4G2AutomorphismNormalForm
public import CFSG.ClassicalInvolution.Generic.Induction
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section Model

variable {K : Type} [Field K]

theorem card_conjSub {X : Type} [Group X] (g : X) (H : Subgroup X) :
    Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem map_rootSubgroup_eq_conjSub [Finite K] (α : MulAut ↥(adjointGroup .G2 K))
    (g : ↥(adjointGroup .G2 K)) (σ : K ≃+* K)
    (hα : ∀ h : ↥(adjointGroup .G2 K), (α h : ModGL .G2 K) =
      (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹)
    (a : Root .G2) :
    ((rootOperatorFamily .G2).rootSubgroup K a).map α.toMonoidHom =
      conjSub g ((rootOperatorFamily .G2).rootSubgroup K a) := by
  set X := (rootOperatorFamily .G2).rootSubgroup K a with hX
  have hle : X.map α.toMonoidHom ≤ conjSub g X := by
    rintro _ ⟨h, hh, rfl⟩
    replace hh : h ∈ X := hh
    rw [mem_conjSub_iff]
    rw [hX, ← (rootOperatorFamily .G2).subgroupOf_rootSubgroup_eq K a, Subgroup.mem_subgroupOf]
      at hh ⊢
    obtain ⟨c, hc⟩ := CFSG.Blueprint.Chevalley.mem_rootSubgroup.mp hh
    refine CFSG.Blueprint.Chevalley.mem_rootSubgroup.mpr ⟨σ c, ?_⟩
    have h1 : Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) =
        pinnedX .G2 K a.1 (σ c) := by
      refine Units.ext ?_
      rw [Units.coe_map, ← hc]
      exact entrywise_pinnedX σ.toRingHom a.1 c
    have h2 : ((g⁻¹ * α.toMonoidHom h * g : ↥(adjointGroup .G2 K)) : ModGL .G2 K) =
        (g : ModGL .G2 K)⁻¹ * (α h : ModGL .G2 K) * (g : ModGL .G2 K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom]
    rw [h2, hα h, h1]
    group
  have hcard : Nat.card ↥(conjSub g X) ≤ Nat.card ↥(X.map α.toMonoidHom) := by
    rw [card_conjSub, Subgroup.card_map_of_injective α.injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem map_rootGroup_eq_conjSub [Finite K] (α : MulAut ↥(adjointGroup .G2 K))
    (g : ↥(adjointGroup .G2 K)) (σ : K ≃+* K)
    (hα : ∀ h : ↥(adjointGroup .G2 K), (α h : ModGL .G2 K) =
      (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹)
    (γ : Fin (Tag.rank .G2) → ℤ) :
    (rootGroup (rootOperatorFamily .G2) K γ).map α.toMonoidHom =
      conjSub g (rootGroup (rootOperatorFamily .G2) K γ) := by
  unfold rootGroup
  split_ifs with h
  · exact map_rootSubgroup_eq_conjSub α g σ hα ⟨γ, h⟩
  · unfold conjSub
    rw [Subgroup.map_bot, Subgroup.map_bot]

theorem map_fund_eq_conjSub [Finite K] (α : MulAut ↥(adjointGroup .G2 K))
    (g : ↥(adjointGroup .G2 K)) (σ : K ≃+* K)
    (hα : ∀ h : ↥(adjointGroup .G2 K), (α h : ModGL .G2 K) =
      (g : ModGL .G2 K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL .G2 K) *
        (g : ModGL .G2 K)⁻¹)
    {R : Subgroup ↥(adjointGroup .G2 K)} (hR : R ∈ fundamentalSubgroups .G2 (g2Datum K)) :
    ∃ k : ↥(adjointGroup .G2 K), R.map α.toMonoidHom = conjSub k R := by
  obtain ⟨g₀, γ, -, rfl⟩ := hR
  set Q : Subgroup ↥(adjointGroup .G2 K) :=
    rootGroup (rootOperatorFamily .G2) K γ ⊔ rootGroup (rootOperatorFamily .G2) K (-γ) with hQ
  have hQα : Q.map α.toMonoidHom = conjSub g Q := by
    rw [hQ, Subgroup.map_sup, map_rootGroup_eq_conjSub α g σ hα,
      map_rootGroup_eq_conjSub α g σ hα]
    unfold conjSub
    rw [Subgroup.map_sup]
  have hcomp : α.toMonoidHom.comp (MulAut.conj g₀).toMonoidHom =
      (MulAut.conj (α g₀)).toMonoidHom.comp α.toMonoidHom := by
    ext x
    simp [map_mul, map_inv]
  refine ⟨α g₀ * g * g₀⁻¹, ?_⟩
  change (Q.map (MulAut.conj g₀).toMonoidHom).map α.toMonoidHom =
    conjSub (α g₀ * g * g₀⁻¹) (conjSub g₀ Q)
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hQα]
  change conjSub (α g₀) (conjSub g Q) = conjSub (α g₀ * g * g₀⁻¹) (conjSub g₀ Q)
  rw [← conjSub_mul, ← conjSub_mul]
  congr 1
  group

theorem exists_conjSub_of_mulAut_g2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (he : 1 ≤ e) (α : MulAut ↥(adjointGroup .G2 (GaloisField p e)))
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) :
    ∃ k, R.map α.toMonoidHom = conjSub k R := by
  obtain ⟨hnf, -⟩ := odd_F4_and_nonexceptional_G2_automorphism_normal_form Fact.out hp2 he
    (GaloisField p e) (GaloisField.card p e (by omega)) .G2 (Or.inr ⟨rfl, hp3⟩)
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
  exact map_fund_eq_conjSub α g σ hgσ hR

end Model

theorem exists_conjSub_of_mulAut_tag {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {t : StatedLieTag} {n e : ℕ} (ht : t = .G2) (hadm : StatedLieAdmissible t n p e)
    (α : MulAut (modelUniv t n p e Fact.out).K) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    ∃ k, R.map α.toMonoidHom = conjSub k R := by
  subst ht
  have hn : n = 0 := hadm.2.2.1
  subst hn
  exact exists_conjSub_of_mulAut_g2 hp2 hp3 hadm.2.1 α hR

end CFSG.ClassicalInvolution.NDB.NDBG
