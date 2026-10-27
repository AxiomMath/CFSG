module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

section Prelim

variable {r : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstar_edgeless_of_muZ2 (hΦ : TypeRFam r Φ) (hAE : ∀ L ∈ Φ, AEmpty Φ L)
    (hEdgeless : DEdgeless Φ) {W' : Subgroup X} (hW' : W' ∈ WSet Φ) (hμ : MuIsoZ2 Φ W') :
    ∀ M ∈ Φ, omegaStarNbr Φ M = ∅ := by
  intro M hM
  by_contra hne
  have hS3 : MuIsoS3 Φ W' :=
    Q3T6.Mu.muIsoS3_of_shape ⟨hΦ.hyp, hΦ.cls, hAE⟩ hW' hEdgeless
      ⟨M, hM, Set.nonempty_iff_ne_empty.mpr hne⟩
  obtain ⟨e₂⟩ := hμ
  obtain ⟨e₃⟩ := hS3
  have h := Nat.card_congr (e₂.symm.toEquiv.trans e₃.toEquiv)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  simp [Fintype.card_perm, Nat.factorial] at h

theorem false_of_inO2_s26 (hr : 4 ≤ r) (hΦ : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hgen : omegaGen Φ = ⊤) (hAE : ∀ L ∈ Φ, AEmpty Φ L) (hTop : ⊤ ∉ Φ)
    (hstar : ∀ M ∈ Φ, omegaStarNbr Φ M = ∅) {K : Subgroup X} (hK : K ∈ Φ)
    (htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L) {z : X} (hz : IsUniqueInvolution K z)
    (hzO2 : TightInO2 z) : False := by
  have hin : ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u →
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q := by
    intro L hL u hu
    obtain ⟨P, hPn, hP2, hzP⟩ := hzO2
    obtain ⟨g, -, rfl⟩ := htr L hL
    refine ⟨P, hPn, hP2, ?_⟩
    rw [← (hz.conj g).eq hu]
    exact hPn.conj_mem z hzP g
  have h2 : ∀ L ∈ Φ, IsPGroup 2 L := fun L hL => by
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΦ.hyp hL
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hin L hL u hu
    exact LinkE2.isPGroup_of_inO2_typeR hΦ hO hL hu hQn hQ2 huQ
  have h8 : ∀ L ∈ Φ, Nat.card L = 2 ^ r := fun L hL => by
    obtain ⟨e⟩ := hΦ.quat L hL L (AlphaFr.E2A.isSylow2In_self (h2 L hL))
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  obtain ⟨J, hJ, hJK⟩ : ∃ J ∈ Φ, J ≠ K := by
    by_contra hno
    push Not at hno
    apply hTop
    have : omegaGen Φ = K := by
      apply le_antisymm
      · exact iSup₂_le fun L hL => (hno L hL).le
      · exact le_omegaGen hK
    rw [← hgen, this]
    exact hK
  have hmem := mem_omegaStarNbr_of_normalizes hΦ.hyp h2 h8 hAE hO hin hK hJ hJK hz
    (mem_normalizer_of_four_le hr hΦ.hyp h2 h8 hin hJ hK hz)
  have := hstar K hK
  rw [this] at hmem
  exact hmem

theorem dstar_edge_of_comm (hr : 4 ≤ r) (hΦ : TypeRFam r Φ) {A : Subgroup X} (hA : A ∈ Φ) {z : X}
    (hz : IsUniqueInvolution A z) (S : Sylow 2 ↥A) {u : X}
    (huS : u ∈ (S : Subgroup A).map A.subtype) (hou : orderOf u = 2 ^ (r - 1)) {g : X}
    (hy : g * z * g⁻¹ ≠ z) (hcomm : u * (g * z * g⁻¹) = (g * z * g⁻¹) * u) :
    ∃ M ∈ Φ, (omegaStarNbr Φ M).Nonempty := by
  have hKy : conjSub g A ∈ Φ := hΦ.hyp.conjInvariant g A hA
  have hzy : IsUniqueInvolution (conjSub g A) (g * z * g⁻¹) := hz.conj g
  have hne : A ≠ conjSub g A := by
    intro h
    apply hy
    rw [← h] at hzy
    exact (hz.eq hzy).symm
  have huA : u ∈ A := Subgroup.map_subtype_le _ huS
  have hR' : (S : Subgroup A).map A.subtype ∈ RSet Φ :=
    mem_RSet_of_isSylow2In hA (isSylow2In_map_subtype A S)
  have hUR : Subgroup.zpowers u ≤ (S : Subgroup A).map A.subtype := Subgroup.zpowers_le.mpr huS
  have hcard : Nat.card ↥((S : Subgroup A).map A.subtype) = 2 ^ r := by
    obtain ⟨e⟩ := hΦ.quat A hA _ (isSylow2In_map_subtype A S)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  have hrel : (Subgroup.zpowers u).relIndex ((S : Subgroup A).map A.subtype) = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.zpowers u)
      (K := (S : Subgroup A).map A.subtype)
    rw [inf_eq_left.mpr hUR, Nat.card_zpowers, hou, hcard] at h1
    have h2 : 2 ^ r = 2 * 2 ^ (r - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h1
  have hU : Subgroup.zpowers u ∈ USet Φ :=
    ⟨_, hR', hUR, inferInstance, hrel⟩
  have hUN : Subgroup.zpowers u ≤ Subgroup.normalizer ((conjSub g A : Subgroup X) : Set X) := by
    refine le_trans (Subgroup.zpowers_le.mpr ?_) (hΦ.tight _ hKy _ hzy)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  exact ⟨conjSub g A, hKy, A, hA, hne, Subgroup.zpowers u, hU, Subgroup.zpowers_le.mpr huA, hUN⟩

end Prelim

end CFSG.CGT.PushingUpLit.SolKNA.R4.RonanRes
