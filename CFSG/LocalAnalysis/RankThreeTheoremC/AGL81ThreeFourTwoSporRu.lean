module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
public import Certificates.Certificate31063
public import CFSG.LocalAnalysis.RankThreeTheoremC.CoreGenerationOne
public import Certificates.Data.CoreD2LinesOne
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoreD2Ru
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporCore
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
import CFSG.Quasithin.Background.A318POutMore
import CFSG.RankThree.PartTwo.Sec4.Item47Native
import CFSG.Sporadic.Bridge.RuSurj
public import CFSG.Sporadic.Schreier.RuCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 Certificates.CoreD2Perm
open Certificates.FusD2Perm (powT wordT)

section Abstract

theorem CoreGenerationOneOf.of_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (e : G ≃* H) (h : CoreGenerationOneOf G p) :
    CoreGenerationOneOf H p := by
  obtain ⟨E, hEc, hEexp, hEnab, hall⟩ := h
  refine ⟨E.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, hEc]
  · rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg e (hEexp x hx)
  · obtain ⟨x, hx, y, hy, hxy⟩ := hEnab
    exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, fun h => hxy (e.injective (by simpa using h))⟩
  · intro A' hA'E hA'e hA'c
    set A : Subgroup G := A'.map e.symm.toMonoidHom with hAdef
    have hAE : A ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (hA'E hy)
      have : e.symm.toMonoidHom y = x := by
        rw [← hxy]
        exact e.symm_apply_apply x
      rwa [this]
    have hAe : IsElemAbelian p A := CFSG.SectionRank.isElemAbelian_map hA'e _
    have hAc : Nat.card A = p ^ 2 := by
      rw [hAdef, Subgroup.card_map_of_injective e.symm.injective, hA'c]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall A hAE hAe hAc
    refine ⟨e.toMonoidHom '' Γ, ?_, ?_⟩
    · rw [← MonoidHom.map_closure, hΓ, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨Q, hQA, hrank, hgQ⟩ := hnorm g hg
      refine ⟨Q.map e.toMonoidHom, ?_, ?_, ?_⟩
      · rintro _ ⟨q, hq, rfl⟩
        obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.1 (hQA hq)
        have : e.toMonoidHom q = x := by
          rw [← hxq]
          exact e.apply_symm_apply x
        rwa [this]
      · exact hrank.trans (CFSG.SectionRank.pRank_le_map hp.one_lt e.toMonoidHom e.injective Q)
      · rw [← Subgroup.map_equiv_normalizer_eq]
        exact Subgroup.mem_map_of_mem _ hgQ

theorem sylow_facts_of_coreGenerationOneOf {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (h : CoreGenerationOneOf G p) (hS : ∀ T : Sylow p G, Nat.card T = p ^ 3)
    (S : Sylow p G) :
    Nat.card (S : Subgroup G) = p ^ 3 ∧ (∀ x ∈ (S : Subgroup G), x ^ p = 1) ∧
      (∃ x ∈ (S : Subgroup G), ∃ y ∈ (S : Subgroup G), x * y ≠ y * x) ∧
      ∀ A : Subgroup G, A ≤ S → IsElemAbelian p A → Nat.card A = p ^ 2 →
        GLBCore p 1 A = ⊤ := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, hEc, hEexp, hEnab, hall⟩ := h
  have hEp : IsPGroup p E := IsPGroup.of_card hEc
  obtain ⟨T₀, hET⟩ := hEp.exists_le_sylow
  have hET0 : (T₀ : Subgroup G) = E :=
    (Subgroup.eq_of_le_of_card_ge hET (by rw [hEc, hS T₀])).symm
  obtain ⟨l, -, hl⟩ := CFSG.AGLEmbedding.exists_mem_map_conj_eq_of_card_eq
    (L := ⊤) (le_top : (S : Subgroup G) ≤ ⊤) le_top S.isPGroup' T₀.isPGroup'
    (by
      change ¬ p ∣ (S : Subgroup G).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact S.not_dvd_index)
    (by rw [Sylow.card_eq_multiplicity T₀, Sylow.card_eq_multiplicity S])
  rw [hET0] at hl
  refine ⟨hS S, fun x hx => ?_, ?_, fun A hAS hAe hA => ?_⟩
  · have hx' : l * x * l⁻¹ ∈ E := by
      rw [← hl]
      exact ⟨x, hx, rfl⟩
    have h1 := hEexp _ hx'
    rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  · obtain ⟨x, hx, y, hy, hxy⟩ := hEnab
    rw [← hl] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨x', hx', y', hy', fun h => hxy ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show l * x' * l⁻¹ * (l * y' * l⁻¹) = l * (x' * y') * l⁻¹ by group, h]
    group
  · have hA' : A.map (MulAut.conj l).toMonoidHom ≤ E := by
      rw [← hl]
      exact Subgroup.map_mono hAS
    have hAe' : IsElemAbelian p (A.map (MulAut.conj l).toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map hAe _
    have hAc' : Nat.card (A.map (MulAut.conj l).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj l).injective, hA]
    obtain ⟨Γ, hΓ, hnorm⟩ := hall _ hA' hAe' hAc'
    have hle : (⊤ : Subgroup G) ≤ GLBCore p 1 (A.map (MulAut.conj l).toMonoidHom) := by
      rw [← hΓ, Subgroup.closure_le]
      intro g hg
      obtain ⟨Q, hQA, hrank, hgQ⟩ := hnorm g hg
      exact CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 hQA hrank hgQ
    have hAA : (A.map (MulAut.conj l).toMonoidHom).map (MulAut.conj l⁻¹).toMonoidHom = A :=
      map_conj_inv_map_conj A l
    have h1 := glbCore_le_comap_conj p 1 hp l⁻¹ hAA
    rw [eq_top_iff]
    intro x _
    have hx := h1 (hle (Subgroup.mem_top (l * x * l⁻¹)))
    rw [Subgroup.mem_comap] at hx
    simpa [MulAut.conj_apply, mul_assoc] using hx

end Abstract

section Perm

theorem coreGenerationOneOf_of_check {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {a, b}) {V : VData} (hn : V.base.n = n)
    (hp : V.base.p.Prime) (ha : TabRep V.base.aT a) (hb : TabRep V.base.bT b)
    (h : checkVOne V = true) : CoreGenerationOneOf ↥G V.base.p := by
  rcases V with ⟨D, ys, gk, wAs, wBs⟩
  dsimp only at hn hp ha hb ⊢
  subst hn
  simp only [checkVOne, Bool.and_eq_true] at h
  obtain ⟨⟨h, hexpOK⟩, hstrict⟩ := h
  rw [allBelow_eq_true] at hstrict
  simp only [checkV, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, anyBelow_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨heK, hncT⟩, hinv⟩, hinvg⟩, henum⟩, hsz⟩, hz⟩, hys⟩, hcov⟩, hgklen⟩, hkind⟩,
    hwAlen⟩, hwBlen⟩, hwords⟩ := h
  set S : List (Equiv.Perm (Fin D.n)) := [a, b] with hSdef
  obtain ⟨hgs, hgi⟩ := gs_rep ha hb hinv
  have haS : a ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hbS : b ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [haS, hbS]
  set S' : List (Equiv.Perm (Fin D.n)) := D.gWs.map (wordVal S) with hS'def
  have hgT : ∀ j, TabRep ((gT D).getD j (idTab D.n)) (S'.getD j 1) :=
    rep_map_words S _ _ hgs hgi D.gWs
  have hsize : (gT D).size = D.gWs.length := by simp [gT]
  have hgTi : ∀ j, TabRep ((gTi D).getD j (idTab D.n)) (S'.getD j 1)⁻¹ := by
    intro j
    by_cases hj : j < D.gWs.length
    · obtain ⟨h1, h2⟩ := hinvg j (by rw [hsize]; exact hj)
      rw [show (gTi D).getD j (idTab D.n) = (gTi D)[j]! by simp [gTi, gT, hj]]
      have := hgT j
      rw [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hj]] at this
      exact this.inv h1 h2
    · have hn : D.gWs[j]? = none := List.getElem?_eq_none (by omega)
      rw [show (gTi D).getD j (idTab D.n) = idTab D.n by simp [gTi, gT, hn],
        show S'.getD j 1 = 1 by simp [hS'def, hn]]
      simpa using TabRep.idTab (n := D.n)
  have hS'len : S'.length = D.gWs.length := by simp [hS'def]
  have hS'G : ∀ g ∈ S', g ∈ G := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG w
  set L : List (Equiv.Perm (Fin D.n)) := D.eW.map (wordVal S) with hLdef
  have heG : ∀ j, TabRep ((eGens D).getD j (idTab D.n)) (L.getD j 1) :=
    rep_map_words S _ _ hgs hgi D.eW
  have hEsz : (eGens D).size = D.eW.length := by simp [eGens]
  have hLlen : L.length = D.eW.length := by simp [hLdef]
  have heG' : ∀ j (hj : j < D.eW.length), TabRep (eGens D)[j]! (L.getD j 1) := by
    intro j hj
    have := heG j
    rwa [show (eGens D).getD j (idTab D.n) = (eGens D)[j]! by simp [eGens, hj]] at this
  have hLmem : ∀ j, j < D.eW.length → L.getD j 1 ∈ L := by
    intro j hj
    rw [show L.getD j 1 = L[j]'(by omega) by simp [List.getD_eq_getElem?_getD, hLlen, hj]]
    exact List.getElem_mem _
  have hA : ∀ g ∈ {g | g ∈ L}, ∃ j < (eGens D).size, TabRep (eGens D)[j]! g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < D.eW.length := by omega
    refine ⟨j, by rw [hEsz]; exact hj', ?_⟩
    have := heG' j hj'
    rwa [show L.getD j 1 = L[j] by simp [hj]] at this
  have hgensE : ∀ j < (eGens D).size, ∃ g ∈ {g | g ∈ L}, TabRep (eGens D)[j]! g := by
    intro j hj
    have hj' : j < D.eW.length := by rwa [hEsz] at hj
    exact ⟨L.getD j 1, hLmem j hj', heG' j hj'⟩
  have hE := enumerates_closure (A := {g | g ∈ L}) hA hgensE henum
  have hEcard : Nat.card (Subgroup.closure {g | g ∈ L}) = D.p ^ 3 := by
    rw [hE.card, Array.length_toList, hsz, heK]
  have hEexp : ∀ x ∈ Subgroup.closure {g | g ∈ L}, x ^ D.p = 1 := by
    intro x hx
    obtain ⟨tab, htab, hrep⟩ := hE.complete x hx
    have h1 := (Array.all_eq_true'.1 (by simpa only [expOK] using hexpOK)) tab
      (Array.mem_toList_iff.1 htab)
    simp only [beq_iff_eq] at h1
    exact ((powT_rep hrep D.p).eq_iff TabRep.idTab).1 h1
  have hEG : Subgroup.closure {g | g ∈ L} ≤ G := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG w
  have hnc : ∃ x ∈ Subgroup.closure {g | g ∈ L}, ∃ y ∈ Subgroup.closure {g | g ∈ L},
      x * y ≠ y * x := by
    obtain ⟨i, hi, j, hj, hij⟩ := hncT
    have hx : TabRep (eT D i) (L.getD i 1) := heG i
    have hy : TabRep (eT D j) (L.getD j 1) := heG j
    exact ⟨L.getD i 1, Subgroup.subset_closure (hLmem _ hi), L.getD j 1,
      Subgroup.subset_closure (hLmem _ hj),
      fun h1 => hij (((hx.comp hy).eq_iff (hy.comp hx)).2 h1)⟩
  simp only [zOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, allBelow_eq_true] at hz
  obtain ⟨⟨⟨hz0, hzp⟩, hz1⟩, hzc⟩ := hz
  set z : Equiv.Perm (Fin D.n) := L.getD 0 1 with hzdef
  have hzt : TabRep (eT D 0) z := heG 0
  have hzE : z ∈ Subgroup.closure {g | g ∈ L} := Subgroup.subset_closure (hLmem 0 hz0)
  have hzp' : z ^ D.p = 1 := ((powT_rep hzt D.p).eq_iff TabRep.idTab).1 hzp
  have hz1' : z ≠ 1 := fun h1 => hz1 ((hzt.eq_iff TabRep.idTab).2 h1)
  have hzcent : ∀ x ∈ Subgroup.closure {g | g ∈ L}, x * z = z * x := by
    have hcl : Subgroup.closure {g | g ∈ L} ≤
        Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin D.n))) := by
      rw [Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hk' : k < D.eW.length := by omega
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hc := hzc k hk'
      have hgk : TabRep (eT D k) L[k] := by
        have := heG k
        rwa [show L.getD k 1 = L[k] by simp [hk]] at this
      exact (((hzt.comp hgk).eq_iff (hgk.comp hzt)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  have hys' : ∀ i < ys.length, vOK D (ys.getD i 0) = true := by
    intro i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact List.all_eq_true.1 hys _ (List.getElem_mem hi)
  set vv : ℕ → Equiv.Perm (Fin D.n) := fun i => L.getD (ys.getD i 0) 1 with hvvdef
  have hvt : ∀ i, TabRep (eT D (ys.getD i 0)) (vv i) := fun i => heG _
  have hvfacts : ∀ i < ys.length, vv i ∈ Subgroup.closure {g | g ∈ L} ∧ (vv i) ^ D.p = 1 ∧
      (∀ k < D.p, vv i ≠ z ^ k) ∧ z * vv i = vv i * z := by
    intro i hi
    have h1 := hys' i hi
    simp only [vOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, allBelow_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h1
    obtain ⟨⟨hj, hvp⟩, hvz⟩ := h1
    have hvE : vv i ∈ Subgroup.closure {g | g ∈ L} :=
      Subgroup.subset_closure (hLmem _ hj)
    exact ⟨hvE, ((powT_rep (hvt i) D.p).eq_iff TabRep.idTab).1 hvp,
      fun k hk h1 => hvz k hk (((hvt i).eq_iff (powT_rep hzt k)).2 h1), (hzcent _ hvE).symm⟩
  have hcover : ∀ t ∈ Subgroup.closure {g | g ∈ L}, ∃ i < ys.length, ∃ a' b' : ℕ,
      t = z ^ a' * (vv i) ^ b' := by
    intro t ht
    obtain ⟨tab, htab, hrep⟩ := hE.complete t ht
    have hc := (Array.all_eq_true'.1 (by simpa only [coverYOK] using hcov)) tab
      (Array.mem_toList_iff.1 htab)
    simp only [anyBelow_eq_true, beq_iff_eq] at hc
    obtain ⟨i, hi, a', -, b', -, he⟩ := hc
    exact ⟨i, hi, a', b', ((hrep.eq_iff ((powT_rep hzt a').comp (powT_rep (hvt i) b'))).1 he)⟩
  have hoz : orderOf z = D.p := by
    have : Fact D.p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hzp' hz1'
  refine coreGenerationOneOf_of_gens hp hG (S := {a, b}) hEcard hEexp hnc hEG ?_
  intro A hAE hAe hAc
  have hzA : z ∈ A := mem_of_central hp hEcard hnc hAE hAe hAc hzE hzcent
  obtain ⟨t, htA, htz⟩ : ∃ t ∈ A, t ∉ Subgroup.zpowers z := by
    by_contra hcon
    have hle : A ≤ Subgroup.zpowers z := fun t ht => by
      by_contra h1
      exact hcon ⟨t, ht, h1⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [hAc, Nat.card_zpowers, hoz] at h1
    have h2 := hp.two_le
    have : D.p ^ 2 ≤ D.p := h1
    nlinarith
  have htE : t ∈ Subgroup.closure {g | g ∈ L} := hAE htA
  obtain ⟨i, hi, a', b', hteq⟩ := hcover t htE
  obtain ⟨hvE, hvp, hvz, hzv⟩ := hvfacts i hi
  have hYcard : Nat.card (Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n)))) =
      D.p ^ 2 := card_closure_pair_of_pow hp hzp' hvp hzv hz1' hvz
  have htp : t ^ D.p = 1 := hAe.2 t htA
  have hzt' : z * t = t * z := (hzcent t htE).symm
  have htzk : ∀ k < D.p, t ≠ z ^ k := fun k hk h1 =>
    htz (h1 ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers z) k)
  have hZTcard : Nat.card (Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n)))) =
      D.p ^ 2 := card_closure_pair_of_pow hp hzp' htp hzt' hz1' htzk
  have hZTA : Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n))) ≤ A := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hzA, htA⟩
  have hZTY : Subgroup.closure ({z, t} : Set (Equiv.Perm (Fin D.n))) ≤
      Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n))) := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    refine ⟨Subgroup.subset_closure (by simp), ?_⟩
    rw [hteq]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hAY : Subgroup.closure ({z, vv i} : Set (Equiv.Perm (Fin D.n))) = A :=
    (Subgroup.eq_of_le_of_card_ge hZTY (by rw [hYcard, hZTcard])).symm.trans
      (Subgroup.eq_of_le_of_card_ge hZTA (by rw [hAc, hZTcard]))
  set Γ : Set (Equiv.Perm (Fin D.n)) := {g | ∃ j < D.gWs.length,
    allowedOne ⟨D, ys, gk, wAs, wBs⟩ i j = true ∧ g = S'.getD j 1} with hΓdef
  have hall : ∀ w : List ℤ,
      (∀ l ∈ w, allowedOne ⟨D, ys, gk, wAs, wBs⟩ i (l.natAbs - 1) = true) →
      wordVal S' w ∈ Subgroup.closure Γ := by
    intro w hw
    refine wordVal_mem_of S' _ w fun l hl => ?_
    by_cases hlt : l.natAbs - 1 < D.gWs.length
    · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
    · rw [List.getD_eq_default _ _ (by rw [hS'len]; omega)]
      exact Subgroup.one_mem _
  obtain ⟨⟨⟨hwA, hwB⟩, -⟩, -⟩ := hwords i hi
  have hstr := hstrict i hi
  simp only [wordOKOne, Bool.and_eq_true, List.all_eq_true] at hstr
  obtain ⟨hoA, hoB⟩ := hstr
  have hA' : wordVal S' (wAs.getD i []) = a := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi (wAs.getD i [])
    rw [hwA] at h1
    exact h1.perm_eq ha
  have hB' : wordVal S' (wBs.getD i []) = b := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi (wBs.getD i [])
    rw [hwB] at h1
    exact h1.perm_eq hb
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rintro g ⟨j, hj, -, rfl⟩
    refine hS'G _ ?_
    rw [List.getD_eq_getElem _ _ (by rw [hS'len]; exact hj)]
    exact List.getElem_mem _
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact hall _ hoA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact hall _ hoB
  · rintro g ⟨j, hj, hok, rfl⟩
    have hj' : j < (gT D).size := by rw [hsize]; exact hj
    have hgj : TabRep (gT D)[j]! (S'.getD j 1) := by
      have := hgT j
      rwa [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hj]] at this
    have hk := hkind j hj'
    simp only [kindOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
    simp only [allowedOne, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at hok
    generalize gk.getD j default = f at hk hok
    obtain ⟨hidx, hk⟩ := hk
    by_cases hk0 : f.kind = 0
    · simp only [hk0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hk
      obtain ⟨e1, e2⟩ := hk
      obtain ⟨hvE', hvp', hvz', hzv'⟩ := hvfacts f.idx hidx
      have hfi : f.idx = i := hok.resolve_right fun h => h.1 hk0
      have hvA : vv f.idx ∈ A := by
        rw [hfi, ← hAY]
        exact Subgroup.subset_closure (by simp)
      left
      exact ⟨z, vv f.idx, hzA, hvA, hzp', hvp', hzv', hz1', hvz', f.f1, f.f2, f.f3, f.f4,
        ((hgj.comp hzt).eq_iff
          (((powT_rep hzt f.f1).comp (powT_rep (hvt f.idx) f.f2)).comp hgj)).1 e1,
        ((hgj.comp (hvt f.idx)).eq_iff
          (((powT_rep hzt f.f3).comp (powT_rep (hvt f.idx) f.f4)).comp hgj)).1 e2⟩
    · simp only [hk0, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
        beq_eq_false_iff_ne, ne_eq] at hk
      obtain ⟨⟨e0, e1⟩, e2⟩ := hk
      right
      have hyt : TabRep (comp D.n (powT D.n (eT D 0) f.f1)
          (powT D.n (eT D (ys.getD f.idx 0)) f.f2)) (z ^ f.f1 * vv f.idx ^ f.f2) :=
        (powT_rep hzt f.f1).comp (powT_rep (hvt f.idx) f.f2)
      refine ⟨z ^ f.f1 * vv f.idx ^ f.f2, ?_, fun h1 => e0 ((hyt.eq_iff TabRep.idTab).2 h1),
        ((powT_rep hyt D.p).eq_iff TabRep.idTab).1 e1, f.f3,
        ((hgj.comp hyt).eq_iff ((powT_rep hyt f.f3).comp hgj)).1 e2⟩
      rcases hok with hidx' | ⟨-, hf2⟩
      · rw [hidx', ← hAY]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      · rw [hf2, pow_zero, mul_one]
        exact Subgroup.pow_mem _ hzA _

end Perm

section Ru

open CFSG.Sporadic.RuSchreier

theorem coreGenerationOneOf_ruP :
    CoreGenerationOneOf ↥ruP 5 :=
  Certificates.certificate31063

private theorem card_sylow_five_of_card {K : Type*} [Group K] [Finite K]
    (hK : Nat.card K = 145926144000) (T : Sylow 5 K) : Nat.card T = 5 ^ 3 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h0 : (145926144000 : ℕ) ≠ 0 := by norm_num
  have h1 := (Nat.prime_five.pow_dvd_iff_le_factorization h0).1
    (by norm_num : 5 ^ 3 ∣ 145926144000)
  have h2 : ¬ 4 ≤ (145926144000 : ℕ).factorization 5 := fun h => by
    have := (Nat.prime_five.pow_dvd_iff_le_factorization h0).2 h
    norm_num at this
  rw [Sylow.card_eq_multiplicity T, hK, show (145926144000 : ℕ).factorization 5 = 3 by omega]

theorem threeFourTwoNoneAt_ru :
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.sporadic .Ru).Group := by
  have hcard : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 :=
    CFSG.Sporadic.Ru.card_Ru
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .Ru) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hO : Nat.card (Outer (CFSG.Blueprint.NativeSporadic.Carrier .Ru)) ≤ 2 :=
    CFSG.RankThree.PartTwo.Sec4.card_outer_Ru
  obtain ⟨hX, hnab, hout⟩ := sporadicIndex_facts_of_bridge (s := .Ru)
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv CFSG.Sporadic.Ru.isSimpleGroup_Ru hO
    Nat.prime_five (by rw [hcard]; norm_num)
  refine threeFourTwoNoneAt_of_glbCore_eq_top hX hnab hout fun K _ _ hK => ?_
  obtain ⟨e⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .Ru)
    CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv hK
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hKc : Nat.card K = 145926144000 := by rw [Nat.card_congr e.toEquiv, hcard]
  have hcg : CoreGenerationOneOf K 5 :=
    coreGenerationOneOf_ruP.of_mulEquiv Nat.prime_five (e.trans ruEquivP).symm
  refine ⟨CFSG.Quasithin.A318P.not_dvd_outer_Ru e Nat.prime_five (by norm_num), fun T => ?_⟩
  obtain ⟨hTc, hTexp, hTnab, hTA⟩ :=
    sylow_facts_of_coreGenerationOneOf hcg (card_sylow_five_of_card hKc) T
  refine ⟨hTc, hTexp, hTnab, ?_, hTA⟩
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  set S : Sylow 5 (CFSG.Blueprint.NativeSporadic.Carrier .Ru) := T.mapSurjective hsurj with hS
  have hST : (S : Subgroup _).map e.symm.toMonoidHom = T := by
    rw [hS, Sylow.coe_mapSurjective, Subgroup.map_map]
    convert Subgroup.map_id (T : Subgroup K)
    ext x
    simp
  rw [← hST]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn
    Nat.prime_five e.symm.toMonoidHom e.symm.surjective
    (fun x _ hx => e.symm.injective (by simpa using hx)) (CFSG.AGLEmbedding.glbCore_Ru_five S)

end Ru

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
