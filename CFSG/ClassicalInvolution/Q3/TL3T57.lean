module

public import CFSG.ClassicalInvolution.Q3.TL3T40
public import CFSG.ClassicalInvolution.Q3.TL4AECover

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {G : Type} [Group G] [Finite G] {IH : ℕ → Prop} {Ω : Set (Subgroup G)}

namespace CHyp

variable {K J : Subgroup G} (hS : CHyp 3 IH Ω K J)
include hS

theorem aeCoverHyp_orb {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) : TL4.AECoverHyp I where
  ker_two := I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot
  card := fun L hL => by rw [hS.card L (hS.orb_subset_omega hL)]; norm_num
  conj_mem := fun L hL x hx => CSetting.conjSub_mem_orb hS.adj.1 (hS.pSpan_orb_le hx) hL
  label_inj := fun L hL L' hL' h => aeIdent_eq_of_map_eq hS.hyp hS.two hS.orb_subset_omega hn I
    (I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot) hL hL' h
  twin_comm := by
    intro α h L hL L' hL' hlab hlab'
    refine aeIdent_comm_of_map_comm hS.hyp hS.two hS.orb_subset_omega I
      (I.toLabel.isPGroup_ker hS.oddCore_orb_eq_bot) hL hL' ?_ ?_
    · intro e
      subst e
      rw [hlab] at hlab'
      exact AE.memBar_true_ne_false hn α h hlab'
    · rw [hlab, hlab']
      exact memBar_twin_comm α h true
  twin_z := by
    intro α h L hL L' hL' hlab hlab' u u' hu hu'
    exact (hS.z_eq_of_label hn hn8 I hL hL' hlab hlab' u u' hu hu').symm

theorem exists_swap : ∃ t : G, conjSub t K = J ∧ conjSub t J = K := by
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  obtain ⟨g, hg⟩ := hS.trans K hS.adj.1 J (hS.orb_subset_omega hJπ)
  have horb := hS.orb_swap_eq hg
  have hgJ : conjSub g J ∈ orbOf (TC.nbrAdj Ω) J K := horb ▸ ⟨J, hJπ, rfl⟩
  obtain ⟨a, ha, haK⟩ := orbOf_subset_gen hS.graphFam'.graph hS.swap.adj hgJ
  have hle : (⨆ I ∈ orbOf (TC.nbrAdj Ω) J K, I) ≤ nbrGen (TC.nbrAdj Ω) J :=
    iSup₂_le fun I hI => le_nbrGen (adj_of_mem_orbOf hS.graphFam'.graph hS.swap.adj hI)
  have haJ : conjSub a J = J := conjSub_self_of_mem_nbrGen hS.graphFam'.graph (hle ha)
  have haJ' : conjSub a⁻¹ J = J := by
    calc conjSub a⁻¹ J = conjSub a⁻¹ (conjSub a J) := by rw [haJ]
      _ = J := conjSub_inv_conjSub a J
  refine ⟨a⁻¹ * g, ?_, ?_⟩
  · rw [conjSub_mul, hg, haJ']
  · rw [conjSub_mul, ← haK, conjSub_inv_conjSub]

omit [Finite G] hS in
theorem swap_inv {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K) :
    conjSub s⁻¹ K = J ∧ conjSub s⁻¹ J = K := by
  constructor
  · rw [← hs', conjSub_inv_conjSub]
  · rw [← hs, conjSub_inv_conjSub]

theorem conjSub_orb_swap {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K) :
    conjSub s '' orbOf (TC.nbrAdj Ω) J K = orbOf (TC.nbrAdj Ω) K J := by
  rw [← orbOf_conj hS.graphFam'.graph J K s, hs', hs]

theorem twin_label_of_z {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {δ : Finset (Fin n)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ b)
    {M : Subgroup G} (hM : M ∈ orbOf (TC.nbrAdj Ω) K J) (hMJ : M ≠ J)
    (hz : ∀ z z' : G, IsUniqueInvolution J z → IsUniqueInvolution M z' → z' = z) :
    (M.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ (!b) := by
  have hH := hS.aeCoverHyp_orb hn hn8 I
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hPΩ := hS.orb_subset_omega
  obtain ⟨γ, hγ, c, hlabM⟩ := I.label M hM
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hS.hyp.omega1 J (hPΩ hJπ)
  obtain ⟨⟨zM, hzM⟩, -⟩ := hS.hyp.omega1 M (hPΩ hM)
  have hzz : zM = zJ := hz zJ zM hzJ hzM
  have e1 := I.map_eq_zBar hn hJπ (hH.card J hJπ) hlabJ hzJ
  have e2 := I.map_eq_zBar hn hM (hH.card M hM) hlabM hzM
  have hγδ : γ = δ := by
    apply AE.eq_of_zBar_eq hn8
    rw [← e1, ← e2]
    congr 1
    exact Subtype.ext hzz
  subst hγδ
  have hc : c = !b := by
    by_contra hne
    have : c = b := by cases c <;> cases b <;> simp_all
    subst this
    exact hMJ (hH.label_inj M hM J hJπ (hlabM.trans hlabJ.symm))
  rw [hlabM, hc]

theorem conjSub_twin_mem {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K)
    {Ks : Subgroup G} (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) :
    conjSub s Ks ∈ orbOf (TC.nbrAdj Ω) K J := by
  rw [← hS.conjSub_orb_swap hs hs']
  exact ⟨Ks, hKs, rfl⟩

theorem conjSub_twin_label {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≠ 8)
    (I : AEIdent (orbOf (TC.nbrAdj Ω) K J) n) {δ : Finset (Fin n)} {hδ : δ.card = 4} {b : Bool}
    (hlabJ : (J.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ = memBar δ hδ b)
    {s : G} (hs : conjSub s K = J) (hs' : conjSub s J = K) {Ks : Subgroup G}
    (hKs : Ks ∈ orbOf (TC.nbrAdj Ω) J K) (hKsK : Ks ≠ K)
    (hz : ∀ z zs : G, IsUniqueInvolution K z → IsUniqueInvolution Ks zs → zs = z) :
    ((conjSub s Ks).subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) K J))).map I.φ =
      memBar δ hδ (!b) := by
  refine hS.twin_label_of_z hn hn8 I hlabJ (hS.conjSub_twin_mem hs hs' hKs) ?_ ?_
  · intro e
    apply hKsK
    apply conjSub_injective s
    rw [e, hs]
  · intro z z' hzJ hz'
    obtain ⟨⟨zK, hzK⟩, -⟩ := hS.hyp.omega1 K hS.adj.1
    obtain ⟨⟨zKs, hzKs⟩, -⟩ := hS.hyp.omega1 Ks (hS.swap.orb_subset_omega hKs)
    have h1 : zKs = zK := hz zK zKs hzK hzKs
    have h2 : IsUniqueInvolution J (s * zK * s⁻¹) := hs ▸ hzK.conj s
    have h3 : IsUniqueInvolution (conjSub s Ks) (s * zK * s⁻¹) := by
      have := hzKs.conj s
      rwa [h1] at this
    rw [hz'.eq h3, hzJ.eq h2]

end CHyp

end CFSG.ClassicalInvolution.Q3.TC.Thin
