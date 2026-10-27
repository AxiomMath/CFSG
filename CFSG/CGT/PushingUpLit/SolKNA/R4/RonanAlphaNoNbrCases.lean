module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrExit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanAlphaNoNbrExitL2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26L3Edge
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Layer
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26Prelim
public import CFSG.CGT.PushingUpLit.SolKNA.R4.RonanResS26U3Edge
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4L3Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4Main
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4U3Main

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSocF4
open CFSG.ClassicalInvolution.Q3.TA3 (SmallL2 SmallL3Ne3 SmallU3Ne3)
open CFSG.GorensteinWalter (PSL2 IsOddPrimePower)
open scoped commutatorElement Pointwise

section Cert



variable {r n : ℕ}

theorem member_inv_mem_of_normal {X : Type} [Group X] {A : Subgroup X} {Φ : Set (Subgroup X)}
    (hfam : CoreAssembly.conjClass (tightCore A) = Φ) (hcore : tightCore A = A) {z : X}
    (hz : IsUniqueInvolution A z) {L : Subgroup X} [L.Normal] (hzL : z ∈ L) :
    ∀ M ∈ Φ, ∀ m : X, IsUniqueInvolution M m → m ∈ L := by
  intro M hM m hm
  have hM' : M ∈ CoreAssembly.conjClass (tightCore A) := hfam ▸ hM
  obtain ⟨g, hg⟩ := hM'
  have hg' : conjSub g A = M := by
    rw [← hcore]
    exact hg
  have h1 := hz.conj g
  rw [hg'] at h1
  rw [hm.eq h1]
  exact Subgroup.Normal.conj_mem ‹L.Normal› z hzL g

theorem exit_cases (hr : 4 ≤ r) (hA : CIT3Below n) (hB : TightBelowR r n)
    (hG : GH74SectionalModels) (h6 : ∀ m, TightLargeEdgeSR r m) {X : Type} [Group X] [Finite X]
    (hn : Nat.card X < n) {Φ : Set (Subgroup X)} (hΦ : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) {A : Subgroup X} (hAΦ : A ∈ Φ) {S : Sylow 2 ↥A}
    {z : X} (hd : TightDatum A S z) (hz : IsUniqueInvolution A z) (hc : TightClsR r X A S z)
    (hfam : CoreAssembly.conjClass (tightCore A) = Φ) (hnO : ¬ TightInO2 z)
    (hE : TightEdgeless A) :
    ((∃ M ∈ Φ, (omegaStarNbr Φ M).Nonempty) ∧ ExitLU A S z) ∨ ExitL2Facts Φ := by
  classical
  have hcore : tightCore A = A := hΦ.closure_twoElts hAΦ
  have hgenA : (⨆ g : X, conjSub g A) = ⊤ := by
    have h := hc.2.1
    unfold TightSelfGen at h
    rwa [hcore] at h
  obtain ⟨x, b, hxS, hbS, hxo, hbx, hbb⟩ := exists_quat_full_of_datum (by omega : 3 ≤ r) hc
  have hxA : x ∈ A := mem_sylowSet_le S hxS
  have hzx : x ^ 2 ^ (r - 2) = z := by
    apply hd.eq_of_orderOf_eq_two (Subgroup.pow_mem _ hxA _)
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
      (by rw [hxo]; exact pow_dvd_pow 2 (by omega)), hxo,
      show 2 ^ (r - 1) = 2 * 2 ^ (r - 2) by rw [← pow_succ']; congr 1; omega]
    exact Nat.mul_div_cancel 2 (by positivity)
  obtain ⟨L, hLn, hLq, hLC, hzn, hnt, hd', hc', hnO', hE', hTs, hab, hTC, hfamL⟩ :=
    layerIdent hr hA hB (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6 hn hd hc hnO hE
  haveI := hLn
  have hdich := (Perp22Rest.layerAut hr hA hB (smallListR_of_gh74 hG) (noDatumOtherR_holds r) h6
    (TwinSocF4.model163R_of_socF4 (TwinSocF4.socF4L3_holds r) (TwinSocF4.socF4U3_holds r)) hn hd hc
    hnO hE).1
  rcases hfamL with hL2 | hL3 | hU3
  ·
    right
    have hZ : Subgroup.center X = ⊥ :=
      s26_l2_center_bot hr hO hΦ hAΦ hd hz hLq hLC hzn hnt hL2 hTC hgenA hxS hbS hxo hbx hbb hzx
    obtain ⟨hbT, hxL, -⟩ :=
      s26_l2_x_mem hr hO hΦ hAΦ hd hz hzn hnt hL2 hTC hxS hbS hxo hbx hbb hzx
    have hzL : z ∈ L := hzx ▸ L.pow_mem hxL _
    have hbL : b ∉ L := fun h => hbT ⟨b, h, rfl⟩
    have hcomm : ∀ x y : X, ⁅x, y⁆ ∈ L := by
      intro x y
      obtain ⟨l, hl, hl'⟩ :=
        l2_comm_all (socleOf L) hL2 hTC (QuotientGroup.mk x) (QuotientGroup.mk y)
      have h1 : (QuotientGroup.mk l : X ⧸ Subgroup.center X) = QuotientGroup.mk ⁅x, y⁆ := by
        have h := map_commutatorElement (QuotientGroup.mk' (Subgroup.center X)) x y
        exact hl'.trans h.symm
      have h2 : l⁻¹ * ⁅x, y⁆ ∈ Subgroup.center X := QuotientGroup.eq.mp h1
      rw [hZ, Subgroup.mem_bot] at h2
      have h3 : ⁅x, y⁆ = l := by
        calc ⁅x, y⁆ = l * (l⁻¹ * ⁅x, y⁆) := by group
          _ = l := by rw [h2, mul_one]
      rw [h3]
      exact hl
    have hidx : L.index ≤ 2 := exitL2_index hr hΦ hAΦ hcomm hgenA hxS hbS hxL hbL hxo hbb
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exitL2_psl hr hLq hLC hZ hzn hL2 hTC hxo hbx hbb hzx
    obtain ⟨hF1, hF2, hF3⟩ := exitL2_fstar hr hLq hLC hZ hzn hL2 hTC hxo hbx hbb hzx
    have hLX : ∀ y : X, y * y ∈ L := by
      intro y
      have hne : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : L.index = 1 ∨ L.index = 2 := by omega
      rcases h2 with h | h
      · rw [Subgroup.index_eq_one] at h
        rw [h]
        exact Subgroup.mem_top _
      · exact Subgroup.mul_self_mem_of_index_two h y
    have hinv := member_inv_mem_of_normal hfam hcore hz hzL
    refine ⟨hZ, ?_, ?_, hF3, exitL2_dstar hr hΦ hK e hLX hinv⟩
    · rw [hF1]
      exact hF2
    · rw [hF1]
      exact hidx
  ·
    left
    refine ⟨?_, exitLU_of_ident hr hd hc hLq hLC hnt hd' hc' rfl hTC (Or.inl hL3)
      fun φ h1 h2 => hdich φ h1 h2⟩
    obtain ⟨hxo', -, -, -⟩ := quatPair_mk hr hzn hxo hbx hbb hzx
    obtain ⟨g, hgz, hgc⟩ := l3_exists_comm_conj hr (socleOf L) hTs hab hTC hL3 hd' hc'
      (x := (QuotientGroup.mk x : X ⧸ Subgroup.center X)) (Subgroup.mem_map_of_mem _ hxA) hxo'
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨hy, hcomm⟩ := lift_comm_conj hnt hgz hgc
    exact dstar_edge_of_comm hr hΦ hAΦ hz S hxS hxo hy hcomm
  ·
    left
    refine ⟨?_, exitLU_of_ident hr hd hc hLq hLC hnt hd' hc' rfl hTC (Or.inr hU3)
      fun φ h1 h2 => hdich φ h1 h2⟩
    obtain ⟨hxo', hbx', hbb', hxz'⟩ := quatPair_mk hr hzn hxo hbx hbb hzx
    have hxS' : (QuotientGroup.mk x : X ⧸ Subgroup.center X) ∈
        ((TwistQ.sylowMap (Subgroup.center X) S : Sylow 2 _) : Subgroup _).map
          (A.map (QuotientGroup.mk' (Subgroup.center X))).subtype := by
      rw [TwistQ.sylowMap_map_subtype]
      exact Subgroup.mem_map_of_mem _ hxS
    have hbS' : (QuotientGroup.mk b : X ⧸ Subgroup.center X) ∈
        ((TwistQ.sylowMap (Subgroup.center X) S : Sylow 2 _) : Subgroup _).map
          (A.map (QuotientGroup.mk' (Subgroup.center X))).subtype := by
      rw [TwistQ.sylowMap_map_subtype]
      exact Subgroup.mem_map_of_mem _ hbS
    obtain ⟨g, hgz, hgc⟩ := u3_exists_comm_conj hr (socleOf L) hTs hab hTC hU3 hd' hc' hxS' hbS'
      hxo' hbx' hbb' hxz'
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨hy, hcomm⟩ := lift_comm_conj hnt hgz hgc
    exact dstar_edge_of_comm hr hΦ hAΦ hz S hxS hxo hy hcomm

end Cert

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
