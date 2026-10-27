module

public import CFSG.ClassicalInvolution.Q3.TL4OddConv
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinGraph
public import CFSG.ClassicalInvolution.Q3.TL4E3Z2

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem orbitGraph_of_sepAlpha (hL : TightLargeHypR 3 n Y R S t) (hα : TightSepAlpha R t)
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    OrbitGraph (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  refine ⟨fun {K J} h => ⟨h.2.1, Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ h.1 h.2.1 h.2⟩,
    fun K h => h.2.2.1 rfl,
    fun {K J} g h => ⟨hΩ.conjInvariant g K h.1, Asc77.omegaNbr_conj hΩ.conjInvariant h.2 g⟩,
    fun {K J} h j hj => ?_, fun hKJ hKJ' h => hsp hKJ hKJ' h⟩
  obtain ⟨g, hgK'⟩ := h.1
  have hgK : conjSub g (tightCore R) = K := hgK'
  obtain ⟨a, haJ'⟩ := h.2.1
  have haJ : conjSub a (tightCore R) = J := haJ'
  obtain ⟨SJ, hLg⟩ := tightLargeHypR_conj hL g
  have hcore : tightCore (conjSub g R) = K := by rw [← conjSub_tightCore, hgK]
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hcore]
    exact h.2
  have huJ : IsUniqueInvolution J (a * t * a⁻¹) := haJ ▸ hL.datum.isUniqueInvolution_core.conj a
  have hαJ := (hα.conj g) J hJ' (a * t * a⁻¹) huJ
  have hJN := edge_le_normalizer_of_alpha hLg.datum hJ' huJ hαJ
  rw [hcore] at hJN
  exact conjSub_eq_of_mem_normalizer (hJN hj)

theorem graphFam_of_sepAlpha (hL : TightLargeHypR 3 n Y R S t) (hα : TightSepAlpha R t)
    (hc : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R)))
    (hsp : TC.SepHyp (CoreAssembly.conjClass (tightCore R))) :
    GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) := by
  have hΩ := hL.datum.hypOmegaGen
  have hgen : (⨆ J ∈ CoreAssembly.conjClass (tightCore R), J) = ⊤ := by
    rw [iSup_conjClass_eq]
    exact hL.cls.2.1
  refine ⟨orbitGraph_of_sepAlpha hL hα hsp, fun h => h.1,
    fun K hK g => hΩ.conjInvariant g K hK, ?_, ?_⟩
  · intro L hL' M hM
    obtain ⟨a, rfl⟩ := hL'
    obtain ⟨b, rfl⟩ := hM
    refine ⟨b * a⁻¹, by rw [hgen]; exact Subgroup.mem_top _, ?_⟩
    rw [conjSub_mul, conjSub_inv_conjSub]
  · intro L hL' M hM
    have key : ∀ b, Relation.ReflTransGen (fun M N : Subgroup Y =>
        N ∈ CoreAssembly.conjClass (tightCore R) ∧
          Disconnected.dAdj (CoreAssembly.conjClass (tightCore R)) M N) L b →
        b ∈ CoreAssembly.conjClass (tightCore R) ∧
          Relation.ReflTransGen (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L b := by
      intro b hb
      induction hb with
      | refl => exact ⟨hL', Relation.ReflTransGen.refl⟩
      | tail _ hbc ih =>
        rename_i b c
        obtain ⟨hbΩ, hpath⟩ := ih
        obtain ⟨hcΩ, hadj⟩ := hbc
        refine ⟨hcΩ, hpath.tail ⟨hbΩ, ?_⟩⟩
        rcases hadj with h | h
        · exact h
        · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hcΩ hbΩ h
    exact (key M (hc L hL' M hM)).2

variable {J : Subgroup Y} {u : Y}

theorem E3Frame.graphFam (hF : E3Frame n R S t J u) :
    GraphFam (CoreAssembly.conjClass (tightCore R))
      (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) :=
  graphFam_of_sepAlpha hF.large hF.alpha hF.conn hF.sep

theorem E3Frame.lemma1710 (hF : E3Frame n R S t J u) :
    PhilipHall.Frame.Lemma1710 (TC.nbrAdj (CoreAssembly.conjClass (tightCore R)))
      (CoreAssembly.conjClass (tightCore R)) (tightCore R)
      (orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) J) :=
  PhilipHall.Frame.graph_17_10 hF.graphFam (CoreAssembly.mem_conjClass_self _) hF.maxAdj.2

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
