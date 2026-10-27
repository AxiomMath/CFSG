module

public import CFSG.ClassicalInvolution.Q3.TL4Res2FCore

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem not_mem_center (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) : z ∉ Subgroup.center G := by
  obtain ⟨-, -, -, -, hno, -, -, -, -, hZ, -, -⟩ := hc
  intro hzc
  exact hno K hK z hz ⟨pCore 2 G, CFSG.pCore_normal, CFSG.pCore_isPGroup, by rw [hZ]; exact hzc⟩

theorem le_of_subnormal (hc : F2CoreConfig J L L₀) {K : Subgroup G}
    (hK : K ∈ CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L) {z : G}
    (hz : IsUniqueInvolution K z) {W : Subgroup G} (hKW : K ≤ W) (hWs : IsSubnormal W ⊤) :
    L₀ ≤ W := by
  have hzZ := not_mem_center hc hK hz
  obtain ⟨-, -, -, -, -, hL₀, -, -, -, -, hC, -⟩ := hc
  have hmove : ∃ y ∈ L₀, y * z ≠ z * y := by
    by_contra hcon
    push Not at hcon
    exact hzZ (hC ▸ Subgroup.mem_centralizer_iff.mpr hcon)
  exact component_le_of_not_commute hWs (hKW hz.mem) ((CFSG.isComponent_iff_open L₀).mp hL₀)
    hmove

omit [Finite G] in
theorem isQuasisimple_subgroupOf (hL₀ : CFSG.IsComponent L₀) {W : Subgroup G} (hLW : L₀ ≤ W) :
    CFSG.IsQuasisimple ↥(L₀.subgroupOf W) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLW).symm hL₀.1

omit [Finite G] in
theorem centralizer_subgroupOf (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G)
    {W : Subgroup G} (hLW : L₀ ≤ W) :
    Subgroup.centralizer ((L₀.subgroupOf W : Subgroup ↥W) : Set ↥W) = Subgroup.center ↥W := by
  ext w
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · intro hw v
    have hwG : (w : G) ∈ Subgroup.centralizer (L₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hw ⟨y, hLW hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
    rw [hC] at hwG
    exact Subtype.ext (Subgroup.mem_center_iff.mp hwG v)
  · intro hw y _
    exact hw y

omit [Finite G] in
theorem mem_center_of_mem_center (hC : Subgroup.centralizer (L₀ : Set G) = Subgroup.center G)
    {W : Subgroup G} (hLW : L₀ ≤ W) {w : ↥W} (hw : w ∈ Subgroup.center ↥W) :
    (w : G) ∈ Subgroup.center G := by
  rw [← centralizer_subgroupOf hC hLW] at hw
  rw [← hC, Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp hw ⟨y, hLW hy⟩ (Subgroup.mem_subgroupOf.mpr hy))

theorem mem_center_of_tightInO2_G (hc : F2CoreConfig J L L₀) {g : G} (h : TightInO2 g) :
    g ∈ Subgroup.center G := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hZ, -, -⟩ := hc
  obtain ⟨P, hPn, hP2, hgP⟩ := h
  rw [← hZ]
  exact (le_sSup (s := {K : Subgroup G | K.Normal ∧ IsPGroup 2 ↥K}) ⟨hPn, hP2⟩ :
    P ≤ CFSG.pCore 2 G) hgP

theorem mem_center_of_tightInO2 (hc : F2CoreConfig J L L₀) {W : Subgroup G}
    (hWs : IsSubnormal W ⊤) {w : ↥W} (h : TightInO2 w) : (w : G) ∈ Subgroup.center G :=
  mem_center_of_tightInO2_G hc
    (PhilipHall.Frame.Thm4Twin.F2.tightInO2_of_subnormal hWs w.2 h)

theorem isPGroup_center (hc : F2CoreConfig J L L₀) {W : Subgroup G} (hLW : L₀ ≤ W) :
    IsPGroup 2 ↥(Subgroup.center ↥W) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hZ, hC, -⟩ := hc
  intro w
  have hwG : ((w : ↥W) : G) ∈ CFSG.pCore 2 G := by
    rw [hZ]
    exact mem_center_of_mem_center hC hLW w.2
  obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup ⟨_, hwG⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg Subtype.val hk
  simpa using this

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo
