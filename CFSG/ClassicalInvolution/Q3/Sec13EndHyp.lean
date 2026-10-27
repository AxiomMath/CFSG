module

public import CFSG.ClassicalInvolution.Q3.Sec13StarMu
import CFSG.ClassicalInvolution.Q3.TL3T28

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

@[expose] def zGroup (Ω : Set (Subgroup G)) : Subgroup G :=
  Subgroup.closure {u | ∃ L ∈ Ω, IsUniqueInvolution L u}

@[expose] def eGroup (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  Subgroup.closure {u | ∃ J ∈ insert K (omegaStarNbr Ω K), IsUniqueInvolution J u}

structure EndHyp (Ω : Set (Subgroup G)) : Prop extends StarHyp Ω where
  cls : Q3CL.ClassicalClause Ω
  disc : ¬ Disconnected.DConnected Ω
  star : DStarConn Ω
  mu : ∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W
  not : ¬ ThmDConcl Ω

theorem EndHyp.ofDCex {IH : ℕ → Prop} {Ω : Set (Subgroup G)} (hc : DCex 3 IH Ω)
    (hZ : Subgroup.center G = ⊥) (hd : ¬ Disconnected.DConnected Ω) (hs : DStarConn Ω)
    (hm : ∀ W ∈ WSet Ω, MuIsoS3 Ω W ∨ MuIsoS4 Ω W ∨ MuIsoWylD4 Ω W) : EndHyp Ω :=
  ⟨StarHyp.ofDCex hc hZ, dLeafCls_holds 3 G Ω hc.toThmDHyp, hd, hs, hm, hc.not⟩

namespace EndHyp

variable {Ω : Set (Subgroup G)} (h : EndHyp Ω)
include h

theorem card_eq_eight {L : Subgroup G} (hL : L ∈ Ω) : Nat.card L = 8 :=
  h.thmD.card L hL

theorem exists_ne : ∃ L ∈ Ω, ∃ L' ∈ Ω, L ≠ L' := by
  by_contra hcon
  push Not at hcon
  exact h.not (Or.inl hcon)

theorem wSet_ne (W : Subgroup G) : WSet Ω ≠ {W} := fun hW =>
  h.not (Or.inr (Or.inl ⟨W, hW⟩))

theorem no_e8 (E : Subgroup G) : ¬ E8Struct ⊤ E := fun hE =>
  h.not (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))

theorem no_e64 : IsEmpty (AEIdentOn Ω 7 AE.e64Sets AE.e64Sub) :=
  ⟨fun hA => h.not (Or.inr (Or.inr (Or.inr (Or.inl ⟨hA⟩))))⟩

theorem no_aeIdent {n : ℕ} (hn : 5 ≤ n) : IsEmpty (AEIdent Ω n) :=
  ⟨fun hA => h.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨hA⟩⟩)))))⟩

theorem no_e29 : IsEmpty (AEIdentOn Ω 8 AE.e29Sets AE.e29Sub) :=
  ⟨fun hA => h.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hA⟩)))))⟩

theorem mem_pCore {L : Subgroup G} (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z) :
    z ∈ pCore 2 G := by
  obtain ⟨Q, hQn, hQ2, hzQ⟩ := h.thmD.inO2 L hL z hz
  exact (le_sSup ⟨hQn, hQ2⟩ : Q ≤ pCore 2 G) hzQ

theorem zGroup_le_pCore : zGroup Ω ≤ pCore 2 G :=
  (Subgroup.closure_le _).mpr fun _ ⟨_, hL, hu⟩ => h.mem_pCore hL hu

theorem not_dbarConnected {W : Subgroup G} (hW : W ∈ WSet Ω) : ¬ DbarConnected Ω W := by
  obtain ⟨K, hK, J, hJ, hKJ⟩ : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dComp Ω K := by
    by_contra hcon
    push Not at hcon
    exact h.disc fun K hK J hJ => hcon K hK J hJ
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hKJ (heq ▸ h.star K hK J hJ)
  exact Q3T8.Asc77.thompsonGraphAll G Ω h.partIHyp hK hne hW

theorem mem_dSet_of_mem {W : Subgroup G} (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ Ω)
    {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W) : K ∈ DSet Ω W := by
  obtain ⟨η, hη, rfl⟩ := hW
  have hΩ := h.thmD.hyp
  have hWz : TC.etaSpan η ≤ Subgroup.centralizer ({z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (TC.etaSpan_comm hΩ hη w hw z hzW)
  obtain ⟨U, hU, hUK, P, hP, hUP⟩ := uAt_self_of hΩ h.thmD.two K hK z hz
  have hact := (TC.normalizes_w_of_le_twoNormal hΩ h.thmD.two hη hWz hK hU hUK hP hUP).1
  refine h.mem_dSet_iff.mpr ⟨hK, fun k hk => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  exact TC.conjSub_etaSpan_eq (hact k hk) (hact k⁻¹ (K.inv_mem hk))

theorem exists_wSet_of_le {K : Subgroup G} (hK : K ∈ Ω) (S : Sylow 2 G)
    (hKS : K ≤ (S : Subgroup G)) :
    ∃ η ∈ etaG Ω, (∀ V ∈ η, V ≤ (S : Subgroup G)) ∧
      (∀ s ∈ (S : Subgroup G), ∀ V ∈ η, conjSub s V ∈ η) ∧ K ⊓ (⨆ V ∈ η, V) ∈ η := by
  obtain ⟨η, hηS, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet h.thmD.hyp S
  have hη : η ∈ etaG Ω := ⟨S, hηS, hinv⟩
  have hηle : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηS.1 hV).2
  refine ⟨η, hη, hηle, hinv, Sec6Gen.l6_11Gen G Ω h.thmD.hyp S η hη hηle K hK ?_⟩
  rw [inf_eq_left.mpr hKS, h.card_eq_eight hK]
  norm_num

end EndHyp

end CFSG.ClassicalInvolution.Q3.Sec13
