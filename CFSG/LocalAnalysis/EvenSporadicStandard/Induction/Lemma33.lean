module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ChainLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp31
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitComp
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Sol78Thm22Guarded
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Input
public import CFSG.LocalAnalysis.OddStandard.SmallF3Interfaces
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import Certificates.Certificate3085Base

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {n : ℕ} {L T : ℕ → Subgroup H}
  {s : ℕ → H}

omit [Finite H] in
theorem FStarSimple.centerIn_eq_bot (hN : FStarSimple N) : centerIn N = ⊥ := by
  have := hN.isSimpleGroup
  have hc : center ↥N = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥N) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hN.nonabelian
      exact hab (mem_center_iff.1 (h1 ▸ mem_top b) a)
  unfold centerIn
  rw [hc]
  exact Subgroup.map_bot _

theorem FStarSimple.centralizer_eq_bot (hN : FStarSimple N) : centralizer (N : Set H) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxN : x ∈ N := hN.centralizer_le hx
  have hz : (⟨x, hxN⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hx g g.2)
  have hc : center ↥N = ⊥ := by
    have h1 : centerIn N = ⊥ := hN.centerIn_eq_bot
    unfold centerIn at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 h1
  rw [hc, Subgroup.mem_bot] at hz
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hz)

theorem Sol78Chain23.inL (hN : FStarSimple N) (h : Sol78Chain23 H N n L T s) {i : ℕ}
    (hi : i < n) : InL (L i) :=
  ⟨T i, h.T_ne_bot hN hi, (h.comp i hi.le).1, (h.comp i hi.le).2⟩

omit [Finite H] in
theorem Sol78Chain23.last_link (hN : FStarSimple N) (h : Sol78Chain23 H N n L T s)
    (hn : 1 ≤ n) :
    L n = (L n).map (MulAut.conj (s n)).toMonoidHom ∧
      StdModulo (L n ⊔ zpowers (s n)) (centralizer (L n : Set H)) (L (n - 1)) := by
  rcases h.link n hn le_rfl with h5a | h5b
  · exfalso
    apply h5a.1
    have hs : s n ∈ normalizer (N : Set H) := by
      rw [Subgroup.normalizer_eq_top_iff.2 hN.normal]
      exact mem_top _
    rw [h.last]
    exact (CFSG.EvenSporadicStandard.Solomon78.mem_normalizer_iff_map_conj_eq.1 hs).symm
  · exact h5b

theorem Sol78Chain23.last_std (hN : FStarSimple N) (h : Sol78Chain23 H N n L T s) (hn : 1 ≤ n) :
    L (n - 1) ≤ N ⊔ zpowers (s n) ∧ InL ((L (n - 1)).subgroupOf (N ⊔ zpowers (s n))) ∧
      StdBare ((L (n - 1)).subgroupOf (N ⊔ zpowers (s n))) := by
  obtain ⟨hfix, hstd⟩ := h.last_link hN hn
  obtain ⟨hincl, -⟩ := h.incl n hn le_rfl
  obtain ⟨hTp, hLc⟩ := h.comp n le_rfl
  obtain ⟨hsp, hsN, hs2, hLp⟩ := h.elem n hn le_rfl
  rw [h.last] at hfix hstd hincl hLc
  have hle : L (n - 1) ≤ N := by
    rw [← hfix, sup_idem] at hincl
    exact hincl
  have hY : L (n - 1) ≤ N ⊔ zpowers (s n) := hle.trans le_sup_left
  refine ⟨hY, ?_, stdBare_subgroupOf_of_stdModulo hN.centralizer_eq_bot hstd⟩
  have hTN : T n ≤ N := fun x hx =>
    hN.centralizer_le (mem_centralizer_iff.2 fun m hm =>
      (mem_centralizer_iff.1 (hLc.1 hm) x hx).symm)
  have hPY : T n ⊔ zpowers (s n) ≤ N ⊔ zpowers (s n) := sup_le_sup_right hTN _
  have hP : T n ⊔ zpowers (s n) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hLp
    have := hN.eq_of_isCompIn_bot hLp
    exact absurd (h.inj (n - 1) (by omega) n le_rfl (by rw [h.last]; exact this))
      (by omega)
  exact inL_subgroupOf hLp hY hPY hP (isPGroup_sup_zpowers hTp hsN hs2)

theorem not_klike_last {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL)
    (h : Sol78Chain23 H N n L T s) (hn : 1 ≤ n) (hK : KLike IsK (L (n - 1))) : False := by
  obtain ⟨hle, hinL, hstd⟩ := h.last_std hyp.fstar hn
  exact hyp.not_max (L (n - 1)) (h.inL hyp.fstar (by omega)) hK (N ⊔ zpowers (s n)) le_sup_left
    ⟨hle, maximal_of_stdBare hinL hstd⟩

theorem stdBare_of_inL {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {M : Subgroup H} (hinL : InL M) (_hMN : M ≠ N) (hLj : IsL ↥M) : StdBare M :=
  thm22 hkp N hyp.fstar hyp.index_le_two M (hyp.type_max M hinL hLj).1
    (hyp.quasi_L _ hLj).2.2

theorem stdBare_of_typeL {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) {j : ℕ} (hj : j < n) (hLj : IsL ↥(L j)) : StdBare (L j) :=
  stdBare_of_inL hyp thm22 hkp (h.inL hyp.fstar hj)
    (fun heq => absurd (h.inj j hj.le n le_rfl (by rw [h.last]; exact heq)) (by omega)) hLj

theorem exclusion_of_typeL {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) {j : ℕ} (hj : j + 1 < n) (hLj : IsL ↥(L j)) : False := by
  have hN := hyp.fstar
  have hinL : InL (L j) := h.inL hN (by omega)
  have hmax : Maximal (L j) := (hyp.type_max (L j) hinL hLj).1
  have hT1 : T (j + 1) ≠ ⊥ := h.T_ne_bot hN hj
  have hlt : Lt (L j) (L (j + 1)) := by
    have := h.lt (i := j + 1) (by omega) hj.le hT1
    simpa using this
  have hiso := hmax.2 (L (j + 1)) (TransGen.single hlt)
  have hne : L j ≠ L (j + 1) := fun heq =>
    absurd (h.inj j (by omega) (j + 1) hj.le heq) (by omega)
  have hLjq : CFSG.IsQuasisimple ↥(L j) := hinL.isQuasisimple
  have hLj1q : CFSG.IsQuasisimple ↥(L (j + 1)) := (h.comp (j + 1) hj.le).2.isQuasisimple
  obtain ⟨hincl, heq⟩ := h.incl (j + 1) (by omega) hj.le
  simp only [Nat.add_sub_cancel] at hincl heq
  rcases h.link (j + 1) (by omega) hj.le with h5a | h5b
  · exact link5a_false_of_stdBare (h.comp (j + 1) hj.le).2
      (h.elem (j + 1) (by omega) hj.le).2.1 hT1 (h.comp (j + 1) hj.le).1 hincl heq hne
      hLjq (stdBare_of_typeL hyp thm22 hkp h (by omega) hLj) h5a.1
  ·
    have hle : L j ≤ L (j + 1) := by
      have h1 := h5b.1
      rw [← h1, sup_idem] at hincl
      exact hincl
    exact hne (eq_of_le_of_iso hle hLjq hLj1q hiso)

theorem lemma33_one_klike {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) (h0 : IsK ↥(L 0)) (hn : 2 ≤ n) :
    IsL ↥(L (n - 1)) ∧ KLike IsK (L (n - 2)) ∧
      IsK (↥(L (n - 2)) ⧸ CFSG.oddCore ↥(L (n - 2))) := by
  classical
  have hN := hyp.fstar
  have hK0 : KLike IsK (L 0) :=
    ⟨↥(L 0), inferInstance, MonoidHom.id _, Function.surjective_id, by simp, h0⟩
  have hex : ∃ j, j ≤ n - 1 ∧ ¬ KLike IsK (L j) := by
    by_contra hcon
    push Not at hcon
    exact not_klike_last hyp h (by omega) (hcon (n - 1) le_rfl)
  let j := Nat.find hex
  have hj : j ≤ n - 1 ∧ ¬ KLike IsK (L j) := Nat.find_spec hex
  have hmin : ∀ i < j, KLike IsK (L i) := fun i hi => by
    by_contra hK
    exact Nat.find_min hex hi ⟨by omega, hK⟩
  have hj0 : j ≠ 0 := fun h0' => hj.2 (h0' ▸ hK0)
  have hKj : KLike IsK (L (j - 1)) := hmin (j - 1) (by omega)
  have hlt : Lt (L (j - 1)) (L j) := h.lt (by omega) (by omega) (h.T_ne_bot hN (by omega))
  have hdesc := hyp.desc (L (j - 1)) (L j) (h.inL hN (by omega)) hKj (h.inL hN (by omega))
    (ReflTransGen.single hlt)
  have hLj : IsL ↥(L j) ∧ IsK (↥(L (j - 1)) ⧸ CFSG.oddCore ↥(L (j - 1))) := by
    rcases hdesc with ⟨π, hπ, hker⟩ | hd
    · exfalso
      exact hj.2 (KLike.of_central_cover hKj (h.comp j (by omega)).2.isQuasisimple.1 π hπ hker)
    · exact hd
  have hjn : j = n - 1 := by
    by_contra hne
    exact exclusion_of_typeL hyp thm22 hkp h (j := j) (by omega) hLj.1
  have h1 : n - 2 = j - 1 := by omega
  rw [h1]
  exact ⟨by rw [← hjn]; exact hLj.1, hKj, hLj.2⟩

theorem lemma33_one {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) (h0 : IsK ↥(L 0)) (hn : 2 ≤ n) :
    IsL ↥(L (n - 1)) ∧ IsK (↥(L (n - 2)) ⧸ CFSG.oddCore ↥(L (n - 2))) :=
  let h1 := lemma33_one_klike hyp thm22 hkp h h0 hn
  ⟨h1.1, h1.2.2⟩

theorem lemma33_pair {IsK IsL : GroupClass} (hyp : Hyp31 H N IsK IsL) (thm22 : Sol78Thm22At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) (h0 : IsK ↥(L 0)) (hn : 2 ≤ n) :
    IsL ↥(L (n - 1)) ∧ IsK (↥(L (n - 2)) ⧸ CFSG.oddCore ↥(L (n - 2))) ∧
      L (n - 2) ≤ L (n - 1) ∧ Lt (L (n - 2)) (L (n - 1)) ∧ Maximal (L (n - 1)) ∧
      StdBare (L (n - 1)) ∧ SolStd ((L (n - 2)).subgroupOf (L (n - 1))) ∧
      twoAdic (autCentralizer (L (n - 1)) (L (n - 2))) ≤ 2 ∧
      ∃ S : Sylow 2 (centralizer (L (n - 1) : Set H)), IsCyclic ↥S := by
  obtain ⟨hL, hK⟩ := lemma33_one hyp thm22 hkp h h0 hn
  have hN := hyp.fstar
  have hinL : InL (L (n - 1)) := h.inL hN (by omega)
  obtain ⟨hmax, hcyc⟩ := hyp.type_max (L (n - 1)) hinL hL
  have hlt : Lt (L (n - 2)) (L (n - 1)) := by
    have := h.lt (i := n - 1) (by omega) (by omega) (h.T_ne_bot hN (by omega))
    have h1 : n - 1 - 1 = n - 2 := by omega
    rwa [h1] at this
  have h1 : n - 1 - 1 = n - 2 := by omega
  have h5b : Sol78Link5b (L (n - 1)) (L (n - 2)) (s (n - 1)) := by
    rcases h.link (n - 1) (by omega) (by omega) with h5a | h5b
    · exfalso
      rw [h1] at h5a
      obtain ⟨e⟩ := h5a.2
      exact hyp.K_ne_L _ _ hL hK ⟨e⟩
    · rw [h1] at h5b
      exact h5b
  have hle : L (n - 2) ≤ L (n - 1) := by
    obtain ⟨hincl, -⟩ := h.incl (n - 1) (by omega) (by omega)
    rw [← h5b.1, sup_idem, h1] at hincl
    exact hincl
  have hlink : Sol78Link5bData (L (n - 2)) (L (n - 1)) (T (n - 1)) (s (n - 1)) := by
    obtain ⟨hTp, hLc⟩ := h.comp (n - 1) (by omega)
    obtain ⟨hsp, hsN, hs2, hKc⟩ := h.elem (n - 1) (by omega) (by omega)
    obtain ⟨hincl, hincl2⟩ := h.incl (n - 1) (by omega) (by omega)
    rw [h1] at hKc hincl hincl2
    exact ⟨hTp, hLc, hsp, hsN, hs2, hKc, ⟨hincl, hincl2⟩, h5b⟩
  obtain ⟨hstd1, hA⟩ := hyp.std_in (L (n - 2)) (L (n - 1)) (T (n - 1)) (s (n - 1))
    (h.T_ne_bot hN (by omega)) hmax hlink hK
  exact ⟨hL, hK, hle, hlt, hmax, stdBare_of_typeL hyp thm22 hkp h (by omega) hL, hstd1, hA, hcyc⟩

end CFSG.EvenSporadicStandard.Induction
