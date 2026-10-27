module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Diagonal
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance

universe u

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}

theorem commute_of_mem_gLAPPrimeCoreOf_of_isComponent (hp : p.Prime) {C K : Subgroup Y}
    (hKC : K ≤ C) (hK : IsComponent (K.subgroupOf C)) (hKp : ¬ Nat.Coprime p (Nat.card K))
    {d : Y} (hd : d ∈ GLAPPrimeCoreOf p C) : ∀ x ∈ K, d * x = x * d := by
  have hKo : GorensteinWalter.IsComponentOf (K.subgroupOf C) (⊤ : Subgroup ↥C) := by
    obtain ⟨⟨hperf, hsimple, a, b, hab⟩, hsn⟩ := hK
    refine ⟨le_top, hsn.subgroupOf, ?_, hperf.commutator_eq_top, hsimple⟩
    by_contra hns
    rw [not_nontrivial_iff_subsingleton] at hns
    exact hab (Subsingleton.elim _ _)
  have hN : (GLAPPrimeCore p ↥C).Normal := inferInstance
  have hcard : Nat.card (K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  rcases GorensteinWalter.component_le_or_commutator_eq_bot_of_normal hKo hN with hle | hcomm
  · exfalso
    apply hKp
    rw [← hcard]
    exact (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp ↥C).coprime_dvd_right (Subgroup.card_dvd_of_le hle)
  · obtain ⟨n, hn, rfl⟩ := hd
    intro x hx
    have hmem : (⟨x, hKC hx⟩ : C) ∈ K.subgroupOf C := hx
    have := Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hmem) n hn
    exact congrArg Subtype.val this

end CFSG.HardMathSupport.Timmesfeld.Balance
