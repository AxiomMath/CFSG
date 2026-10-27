module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Variant3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma33
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Links
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.FiStep
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Glob
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting

public section

namespace CFSG.EvenSporadicStandard.Induction.Fi.V3

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

section Prelim

variable {H : Type} [Group H]

theorem stdBare_of_subgroupOf_top {K : Subgroup H} (h : StdBare (K.subgroupOf (⊤ : Subgroup H))) :
    StdBare K := by
  have h1 := stdBare_map_mulEquiv (Subgroup.topEquiv (G := H)) h
  have hmap : (K.subgroupOf (⊤ : Subgroup H)).map
      (Subgroup.topEquiv (G := H)).toMonoidHom = K := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, Subgroup.mem_top x⟩, hx, rfl⟩
  rwa [hmap] at h1

end Prelim

variable {H : Type} [Group H] [Finite H] {N : Subgroup H} {n : ℕ} {L T : ℕ → Subgroup H}
  {s : ℕ → H}

omit [Finite H] in
theorem cqOrd_eq_of_klike {IsK : GroupClass} (hcq : CqEq IsK) {X X' : Subgroup H}
    (hXq : CFSG.IsQuasisimple ↥X) (hX'q : CFSG.IsQuasisimple ↥X') (hX : KLike IsK X)
    (hX' : KLike IsK X') : cqOrd X = cqOrd X' := by
  obtain ⟨Y, _, π, hπ, hker, hY⟩ := hX
  obtain ⟨Y', _, π', hπ', hker', hY'⟩ := hX'
  have : Group.IsPerfect ↥X := hXq.1
  have : Group.IsPerfect ↥X' := hX'q.1
  obtain ⟨e₁⟩ := cqEquiv_of_central_cover π hπ hker
  obtain ⟨e₂⟩ := cqEquiv_of_central_cover π' hπ' hker'
  obtain ⟨e₃⟩ := hcq Y Y' hY hY'
  exact Nat.card_congr (e₁.trans (e₃.trans e₂.symm)).toEquiv

theorem false_of_link_eq_cqOrd {N' : Subgroup H} {m : ℕ}
    (h : Sol78Chain23 H N' m L T s) {i : ℕ} (hi : 1 ≤ i) (him : i ≤ m)
    (hq : cqOrd (L (i - 1)) = cqOrd (L i)) (hne : L (i - 1) ≠ L i) (hstd : StdBare (L i)) :
    False := by
  have h5a := h.toLinks.link5a_of_cqOrd_eq hi him hq hne
  obtain ⟨hTp, hLc⟩ := h.comp i him
  obtain ⟨-, hsN, -, -⟩ := h.elem i hi him
  have hK'c : IsCompIn ((L i).map (MulAut.conj (s i)).toMonoidHom) (centralizer (T i : Set H)) :=
    isCompIn_map_conj_of_mem_normalizer hLc (mem_normalizer_centralizer_of_mem_normalizer hsN)
  have hcomm : ∀ a ∈ L i, ∀ b ∈ (L i).map (MulAut.conj (s i)).toMonoidHom, a * b = b * a :=
    hLc.commute_of_ne hK'c h5a.1
  apply hstd.1 (s i)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hcomm a ha b hb).symm

theorem not_klike_last_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (h : Sol78Chain23 H N n L T s) (hn : 1 ≤ n) (hK : KLike IsK (L (n - 1)))
    (hsub : N ⊔ zpowers (s n) = ⊤ → StdBare (L (n - 1)) → False) : False := by
  obtain ⟨hle, hinL, hstd⟩ := h.last_std hyp.fstar hn
  by_cases hY : N ⊔ zpowers (s n) = ⊤
  · rw [hY] at hstd
    exact hsub hY (stdBare_of_subgroupOf_top hstd)
  · exact hyp.not_max (L (n - 1)) (h.inL hyp.fstar (by omega)) hK (N ⊔ zpowers (s n))
      le_sup_left hY ⟨hle, maximal_of_stdBare hinL hstd⟩

theorem stdBare_of_inL_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (thm22 : Sol78Thm22At H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    {M : Subgroup H} (hinL : InL M) (_hMN : M ≠ N) (hLj : IsL ↥M) : StdBare M :=
  thm22 hkp N hyp.fstar hyp.index_le_two M (hyp.type_max M hinL hLj).1
    (hyp.quasi_L _ hLj).2.2

theorem stdBare_of_typeL_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (thm22 : Sol78Thm22At H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) {j : ℕ} (hj : j < n) (hLj : IsL ↥(L j)) : StdBare (L j) :=
  stdBare_of_inL_ns hyp thm22 hkp (h.inL hyp.fstar hj)
    (fun heq => absurd (h.inj j hj.le n le_rfl (by rw [h.last]; exact heq)) (by omega)) hLj

theorem exclusion_of_typeL_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (thm22 : Sol78Thm22At H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
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
      hLjq (stdBare_of_typeL_ns hyp thm22 hkp h (by omega) hLj) h5a.1
  · have hle : L j ≤ L (j + 1) := by
      have h1 := h5b.1
      rw [← h1, sup_idem] at hincl
      exact hincl
    exact hne (eq_of_le_of_iso hle hLjq hLj1q hiso)

theorem lemma33_one_klike_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (hcq : CqEq IsK) (thm22 : Sol78Thm22At H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
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
    refine not_klike_last_ns hyp h (by omega) (hcon (n - 1) le_rfl) fun hY hstd => ?_
    have h1 : n - 1 - 1 = n - 2 := by omega
    refine false_of_link_eq_cqOrd h (i := n - 1) (by omega) (by omega) ?_ ?_ hstd
    · exact cqOrd_eq_of_klike hcq (h.inL hN (by omega)).isQuasisimple
        (h.inL hN (by omega)).isQuasisimple (hcon _ (by omega)) (hcon _ (by omega))
    · exact fun heq => absurd (h.inj (n - 1 - 1) (by omega) (n - 1) (by omega) heq) (by omega)
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
    exact exclusion_of_typeL_ns hyp thm22 hkp h (j := j) (by omega) hLj.1
  have h1 : n - 2 = j - 1 := by omega
  rw [h1]
  exact ⟨by rw [← hjn]; exact hLj.1, hKj, hLj.2⟩

theorem lemma33_pair_ns {IsK IsL : GroupClass} (hyp : Hyp31NS H N IsK IsL)
    (hcq : CqEq IsK) (thm22 : Sol78Thm22At H) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H)
    (h : Sol78Chain23 H N n L T s) (h0 : IsK ↥(L 0)) (hn : 2 ≤ n) :
    IsL ↥(L (n - 1)) ∧ IsK (↥(L (n - 2)) ⧸ CFSG.oddCore ↥(L (n - 2))) ∧
      L (n - 2) ≤ L (n - 1) ∧ Lt (L (n - 2)) (L (n - 1)) ∧ Maximal (L (n - 1)) ∧
      StdBare (L (n - 1)) ∧
      Sol78Link5bData (L (n - 2)) (L (n - 1)) (T (n - 1)) (s (n - 1)) ∧ T (n - 1) ≠ ⊥ ∧
      ∃ S : Sylow 2 (centralizer (L (n - 1) : Set H)), IsCyclic ↥S := by
  obtain ⟨hL, -, hK⟩ := lemma33_one_klike_ns hyp hcq thm22 hkp h h0 hn
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
  exact ⟨hL, hK, hle, hlt, hmax, stdBare_of_typeL_ns hyp thm22 hkp h (by omega) hL, hlink,
    h.T_ne_bot hN (by omega), hcyc⟩

end CFSG.EvenSporadicStandard.Induction.Fi.V3
