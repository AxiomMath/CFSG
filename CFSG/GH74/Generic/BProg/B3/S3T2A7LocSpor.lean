module

public import CFSG.GH74.Generic.BProg.B3.S3T2A7LocGen
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.SmallOddCore.HSMcL
public import CFSG.Sporadic.Schreier.SteinbergBSLyOuterTrivial
public import CFSG.Sporadic.Schreier.LyOddCoreInner
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.GH74.Generic.BProg.B3.S3T2A7Loc

open CFSG CFSG.Blueprint Subgroup

theorem locBal1Two_mathieu
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .M11 ∨ NativeSporadic.IsSporadic T .M12 ∨
      NativeSporadic.IsSporadic T .M22 ∨ NativeSporadic.IsSporadic T .M23) :
    S3T2A7.LocBal1Two T := by
  rcases hT with h | h | h | h
  · obtain ⟨ψ⟩ := h
    exact locBal1Two_of_normal_equiv ψ Sporadic.Schreier.m11_center_eq_bot'
      fun X _ _ S _ hS hC t ht =>
        Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
          S (Or.inl hS) hC t ht
  · obtain ⟨ψ⟩ := h
    exact locBal1Two_of_normal_equiv ψ Sporadic.Schreier.m12_center_eq_bot'
      fun X _ _ S _ hS hC t ht =>
        Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
          S (Or.inr (Or.inl hS)) hC t ht
  · obtain ⟨ψ⟩ := h
    exact locBal1Two_of_normal_equiv ψ Sporadic.Schreier.m22_center_eq_bot'
      fun X _ _ S _ hS hC t ht =>
        Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
          S (Or.inr (Or.inr (Or.inl hS))) hC t ht
  · obtain ⟨ψ⟩ := h
    exact locBal1Two_of_normal_equiv ψ Sporadic.Schreier.m23_center_eq_bot'
      fun X _ _ S _ hS hC t ht =>
        Sporadic.Schreier.ctuc_mathieu_almost_simple_involution_centralizer_odd_core_trivial
          S (Or.inr (Or.inr (Or.inr (Or.inl hS)))) hC t ht

theorem locBal1Two_J2
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .J2) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := hT
  exact locBal1Two_of_normal_equiv ψ (center_eq_bot_of_equiv Sporadic.Schreier.j2PermEquiv
      (center_eq_bot_of_centralizer Sporadic.SmallOddCore.j2_centralizer_eq_bot))
    fun X _ _ S _ hS hC t ht =>
      Sporadic.SmallOddCore.ctuc_j2_almost_simple_involution_centralizer_odd_core_trivial
        S hS hC t ht

theorem locBal1Two_J3
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .J3) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := hT
  exact locBal1Two_of_normal_equiv ψ (center_eq_bot_of_equiv Sporadic.Schreier.j3PermEquiv
      (center_eq_bot_of_centralizer Sporadic.SmallOddCore.j3_centralizer_eq_bot))
    fun X _ _ S _ hS hC t ht =>
      Sporadic.SmallOddCore.ctuc_j3_almost_simple_involution_centralizer_odd_core_trivial
        S hS hC t ht

theorem locBal1Two_McL
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .McL) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := hT
  exact locBal1Two_of_normal_equiv ψ (center_eq_bot_of_equiv Sporadic.Schreier.mclPermEquiv
      (center_eq_bot_of_centralizer Sporadic.SmallOddCore.mcl_centralizer_eq_bot))
    fun X _ _ S _ hS hC t ht =>
      Sporadic.SmallOddCore.ctuc_hs_mcl_almost_simple_involution_centralizer_odd_core_trivial
        S (Or.inr hS) hC t ht

theorem locBal1Two_J1
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .J1) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := hT
  obtain ⟨hfin, -, hs⟩ := Sporadic.J1.fam_j1_simplicity
  have hZ : center NativeSporadic.J1 = ⊥ := center_eq_bot_of_simple hs
    (exists_noncomm_of_not_prime hs (by rw [Sporadic.J1.card_J1]; norm_num))
  exact locBal1Two_of_inner (center_eq_bot_of_equiv ψ hZ)
    (forall_inner_of_equiv ψ Sporadic.Schreier.at_j1_schreier.2.1)
    fun t ht => (Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨ψ⟩ t ht).2.2.2

theorem locBal1Two_Ly
    {T : Type} [Group T] [Finite T]
    (hT : NativeSporadic.IsSporadic T .Ly) : S3T2A7.LocBal1Two T := by
  obtain ⟨ψ⟩ := hT
  have hs := Sporadic.Ly.isSimpleGroup_Ly
  have hfin : Finite NativeSporadic.Ly :=
    Nat.finite_of_card_ne_zero (by rw [Sporadic.Ly.card_Ly']; norm_num)
  have hZ : center NativeSporadic.Ly = ⊥ := center_eq_bot_of_simple hs
    (exists_noncomm_of_not_prime hs (by rw [Sporadic.Ly.card_Ly']; norm_num))
  have hInn : ∀ φ : MulAut NativeSporadic.Ly, ∃ g : NativeSporadic.Ly, φ = MulAut.conj g := by
    intro φ
    have hφ : φ ∈ ComponentClassification.OuterAutomorphisms.inner NativeSporadic.Ly := by
      rw [ComponentClassification.RestrictedStd.Spor.lyOuterTrivialInput]
      exact mem_top φ
    obtain ⟨g, hg⟩ := hφ
    exact ⟨g, hg.symm⟩
  refine locBal1Two_of_inner (center_eq_bot_of_equiv ψ hZ) (forall_inner_of_equiv ψ hInn) ?_
  intro t ht
  obtain ⟨hq, hZc, -⟩ := Sporadic.LySchreier.involution_centralizers_quasisimple ⟨ψ⟩ t ht
  have heven : 2 ∣ Nat.card ↥(centralizer ({t} : Set T)) := by
    have hmem : t ∈ centralizer ({t} : Set T) := mem_centralizer_singleton_iff.2 rfl
    rw [← ht, ← Subgroup.orderOf_mk t hmem]
    exact orderOf_dvd_natCard _
  exact Sporadic.LySchreier.oddCore_eq_bot_of_quasisimple_center_two hq hZc heven

theorem locBal1For_sporGH :
    S3T2A7.LocBal1For S3T2A7.SporGH := by
  intro T _ _ hT
  rcases hT with h | h | h | h | h | h | h | h | h
  · exact locBal1Two_mathieu (Or.inl h)
  · exact locBal1Two_mathieu (Or.inr (Or.inl h))
  · exact locBal1Two_mathieu (Or.inr (Or.inr (Or.inl h)))
  · exact locBal1Two_mathieu (Or.inr (Or.inr (Or.inr h)))
  · exact locBal1Two_J1 h
  · exact locBal1Two_J2 h
  · exact locBal1Two_J3 h
  · exact locBal1Two_McL h
  · exact locBal1Two_Ly h

end CFSG.GH74.Generic.BProg.B3.S3T2A7Loc
