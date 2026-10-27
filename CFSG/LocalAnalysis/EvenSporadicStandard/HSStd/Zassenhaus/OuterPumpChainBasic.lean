module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterPumpType
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerCore
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobBalance

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Induction
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.HSStd

theorem PumpType.congr {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q') (h : PumpType Q) :
    PumpType Q' := by
  rcases h with ⟨k, hk, ⟨f⟩⟩ | h | h | h | ⟨i, hi, h⟩
  · exact Or.inl ⟨k, hk, ⟨e.symm.trans f⟩⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.symm.trans f⟩)
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩)))

structure PumpCtx (G : Type) [Group G] : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G
  balanced : ∀ x : G, orderOf x = 2 → CFSG.oddCore ↥(centralizer ({x} : Set G)) = ⊥

variable {G : Type} [Group G]

theorem PumpCtx.centralizer_ne_top (h : PumpCtx G) {v : G} (hv : v ≠ 1) :
    centralizer ({v} : Set G) ≠ ⊤ := by
  intro htop
  have := h.simple
  have hc : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h' | h'
    · exact h'
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      exact absurd (mem_center_iff.mp (h' ▸ mem_top b) a) hab
  apply hv
  have hv' : v ∈ center G := by
    rw [mem_center_iff]
    intro g
    have hg : g ∈ centralizer ({v} : Set G) := htop ▸ mem_top g
    exact mem_centralizer_singleton_iff.1 hg
  rw [hc, mem_bot] at hv'
  exact hv'

theorem PumpCtx.ne_top_of_isCompIn (h : PumpCtx G) {K : Subgroup G} {x : G} (hx : orderOf x = 2)
    (hK : IsCompIn K (centralizer ({x} : Set G))) : K ≠ ⊤ := by
  intro htop
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  apply h.centralizer_ne_top hx1
  exact top_le_iff.1 (htop ▸ hK.le)

theorem PumpCtx.isPGroup_center [Finite G] (h : PumpCtx G) {K : Subgroup G} {x : G}
    (hx : orderOf x = 2) (hK : IsCompIn K (centralizer ({x} : Set G))) :
    IsPGroup 2 ↥(center ↥K) := by
  have hO : CFSG.pPrimeCore 2 ↥(centralizer ({x} : Set G)) = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two']
    exact h.balanced x hx
  have hOK : CFSG.pPrimeCore 2 ↥K = ⊥ :=
    Induction.Balance.pPrimeCore_eq_bot_of_isSubnormal hK.le hK.2.2 hO
  exact Induction.Balance.isPGroup_center_of_pPrimeCore_eq_bot hOK

theorem PumpCtx.catalog_center_quotient [Finite G] (h : PumpCtx G) {K : Subgroup G} {x : G}
    (hx : orderOf x = 2) (hK : IsCompIn K (centralizer ({x} : Set G))) :
    Catalog (↥K ⧸ center ↥K) :=
  Induction.Balance.catalog_center_quotient_of_kProper h.kProper (h.ne_top_of_isCompIn hx hK)
    hK.isQuasisimple

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
