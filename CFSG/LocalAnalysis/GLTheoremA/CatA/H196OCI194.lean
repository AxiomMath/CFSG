module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Reduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I194Main

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H196OC

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.Balance (elemAbelian_subgroupOf)

theorem i194_of_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {X B A : Subgroup G}
    (hBX : B ≤ X) (hB : CFSG.Open.IsElemAbelian p B) (hAB : A ≤ B)
    (hcf : ∀ J : Subgroup G, GLAPComponent p X J → IsCompCoreFreeLocalType p B J) :
    GLAPPrimeCoreOf p (X ⊓ Subgroup.centralizer (A : Set G)) ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π : ↥X →* ↥X ⧸ GLAPPrimeCore p ↥X := QuotientGroup.mk' (GLAPPrimeCore p ↥X) with hπ
  have hY : ∀ L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X), IsComponent L →
      IsCompCoreFreeLocalType p (barX p X B) L := by
    intro L hL
    obtain ⟨J, hJ, rfl⟩ := exists_glaPComponent_barX_eq X ((isComponent_iff_open L).1 hL)
    exact isCompCoreFree_barX hp hJ (hcf J hJ)
  have hBbar : CFSG.Open.IsElemAbelian p (barX p X B) :=
    CFSG.Open.IsElemAbelian.map (elemAbelian_subgroupOf hBX hB) _
  have hAle : barX p X A ≤ barX p X B :=
    Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.2 (hAB (Subgroup.mem_subgroupOf.1 hx)))
  have hO : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hW := i194_reduced hp hO hBbar hAle hY
  set C' : Subgroup ↥X := Subgroup.centralizer ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) with hC'
  have hQp : IsPGroup p ↥(A.subgroupOf X) :=
    isPGroup_subgroupOf_of_pow (fun x hx => hB.2 x (hAB hx)) X
  have h1 := CFSG.HardMathSupport.Solomon.Coordinator.h1Stmt_holds π
    (QuotientGroup.mk'_surjective _) hp hQp
  have hker : GLAPPrimeCoreOf p C' ≤ GLAPPrimeCore p ↥X := by
    intro x hx
    have hmap : π x ∈ GLAPPrimeCoreOf p (Subgroup.centralizer
        ((barX p X A : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) : Set (↥X ⧸ GLAPPrimeCore p ↥X))) :=
      h1 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hW, Subgroup.mem_bot] at hmap
    exact (QuotientGroup.eq_one_iff x).1 hmap
  have hmapC : C'.map X.subtype = X ⊓ Subgroup.centralizer (A : Set G) := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haX : a ∈ X := hBX (hAB ha)
      have hq : (⟨a, haX⟩ : ↥X) ∈ A.subgroupOf X := Subgroup.mem_subgroupOf.2 ha
      have := Subgroup.mem_centralizer_iff.1 hx ⟨a, haX⟩ hq
      exact congrArg Subtype.val this
    · intro hg
      obtain ⟨hgX, hgC⟩ := Subgroup.mem_inf.1 hg
      refine ⟨⟨g, hgX⟩, ?_, rfl⟩
      rw [hC', SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro q hq
      have hqA : (q : G) ∈ A := Subgroup.mem_subgroupOf.1 hq
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hgC) (q : G) hqA
  let e : ↥C' ≃* ↥(X ⊓ Subgroup.centralizer (A : Set G)) :=
    (C'.equivMapOfInjective X.subtype X.subtype_injective).trans (MulEquiv.subgroupCongr hmapC)
  have he : ∀ x : ↥C', ((e x : ↥(X ⊓ Subgroup.centralizer (A : Set G))) : G) =
      (X.subtype.comp C'.subtype) x := fun x => rfl
  have hformula := CFSG.HardMathSupport.Timmesfeld.Balance.gLAPPrimeCoreOf_eq_map_of_mulEquiv p
    (X.subtype.comp C'.subtype) e he
  intro g hg
  rw [hformula] at hg
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  have hyX : C'.subtype y ∈ GLAPPrimeCoreOf p C' := Subgroup.mem_map.2 ⟨y, hy, rfl⟩
  have hyO := hker hyX
  unfold GLAPPrimeCoreOf
  exact Subgroup.mem_map.2 ⟨C'.subtype y, hyO, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.H196OC

end
