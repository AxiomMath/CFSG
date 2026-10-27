module

public import CFSG.GH74.GLS.Stage1.Thm4.P92Basic
public import CFSG.GH74.GLS.Bg.Iii2.CMAux

public section

namespace CFSG.GH74.GLS.Stage1.Thm4.P92

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.TwoThin CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Lh : Type} [Group Lh] {n : ℕ}

theorem exists_stepData' {x u : G} {K J : Subgroup G} (hK : IsPRigid 2 x K)
    (hlt : PumpUpLT 2 x K u J) (hxY : x ∈ centralizer ({u} : Set G)) :
    ∃ Λ : Subgroup G, Bg.Iii2.CMEngine.StepData x u hxY K J Λ := by
  obtain ⟨e⟩ := hK.2 u J (LongPumpUp.single' hlt)
  have hle : hatCard J ≤ hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, -, -, -, -, hcases⟩ := rigid_step hlt hxY hle
  refine ⟨Λ, hΛ, ?_⟩
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, hAB, -, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, hAB, h2⟩

theorem mem_pumpUp {x u : G} {K J : Subgroup G} (hK : IsPRigid 2 x K) (hlt : PumpUpLT 2 x K u J)
    (hxY : x ∈ centralizer ({u} : Set G)) (hvert : x ∈ normalizer (J : Set G)) {p : G} (hpK : p ∈ K)
    (hpY : p ∈ centralizer ({u} : Set G)) (h2el : ∃ m : ℕ, p ^ (2 ^ m) = 1) : p ∈ J := by
  obtain ⟨Λ, hΛ⟩ := exists_stepData' hK hlt hxY
  have hbar : bar u Λ = bar u J := (hΛ.cases.resolve_right (fun h => h.1 hvert)).2
  have hΛJ : Λ ≤ J := Bg.Iii2.CMEngine.lam_le_of_bar_le hΛ.lam hlt.2.1.2.2 hbar.le
  exact hΛJ (hΛ.lam.twoElt p (Subgroup.mem_inf.mpr ⟨hpK, hpY⟩) h2el)

theorem exists_rigid_pumpUp (E : Env G Lh n) {x u : G} {K : Subgroup G} (hK : IsRigidOfType Lh x K)
    (hux : u ∈ centralizer ({x} : Set G)) (huo : orderOf u = 2) (huz : u ∈ zStar K) :
    ∃ J : Subgroup G, IsRigidOfType Lh u J ∧ u ∈ J := by
  have hwC : u ∈ CxK x K := Subgroup.mem_inf.mpr ⟨hux, (Subgroup.mem_inf.mp huz).2⟩
  obtain ⟨J, hJ⟩ := exists_pumpUpLT (rig_ilo hK) huo hwC (E.hR u huo)
  have hJr : IsRigidOfType Lh u J := isRigidOfType_of_pumpUpLT hK hJ
  have hxY : x ∈ centralizer ({u} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp hux).symm
  refine ⟨J, hJr, mem_pumpUp hK.1 hJ hxY (E.norm hJr hxY) (Subgroup.mem_inf.mp huz).1
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) ⟨1, ?_⟩⟩
  have : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [huo, sq] at this
  simpa [sq] using this

end CFSG.GH74.GLS.Stage1.Thm4.P92
