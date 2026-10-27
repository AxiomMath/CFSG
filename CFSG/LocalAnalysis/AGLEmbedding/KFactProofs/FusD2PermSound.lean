module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.FusD2Perm
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Certificates.Data.FusD2Perm

public section

namespace CFSG.AGLEmbedding.FusD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Certificates.FusD2Perm
open CFSG.RankThree.PartOne.CTP.Fus (FusionGenerationOf)

@[expose] def wordVal {G : Type*} [Group G] (S : List G) : List ℤ → G
  | [] => 1
  | z :: w =>
    (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * wordVal S w

theorem wordVal_mem {G : Type*} [Group G] (S : List G) (H : Subgroup G) (hS : ∀ g ∈ S, g ∈ H) :
    ∀ w : List ℤ, wordVal S w ∈ H
  | [] => H.one_mem
  | z :: w => by
    have hget : ∀ k, S.getD k 1 ∈ H := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases h : S[k]? with
      | none => exact H.one_mem
      | some g => exact hS g (List.mem_of_getElem? h)
    rw [wordVal]
    refine H.mul_mem ?_ (wordVal_mem S H hS w)
    split_ifs
    · exact hget _
    · exact H.inv_mem (hget _)

theorem powT_rep {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) (k : ℕ) :
    TabRep (powT n t k) (g ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact TabRep.idTab
  | succ k ih =>
    rw [pow_succ']
    exact ht.comp ih

theorem wordT_rep {n : ℕ} (S : List (Equiv.Perm (Fin n))) (gs gi : Array Tab)
    (hgs : ∀ j, TabRep (gs.getD j (idTab n)) (S.getD j 1))
    (hgi : ∀ j, TabRep (gi.getD j (idTab n)) (S.getD j 1)⁻¹) (w : List ℤ) :
    TabRep (wordT n gs gi w) (wordVal S w) := by
  induction w with
  | nil => exact TabRep.idTab
  | cons z w ih =>
    rw [wordT, wordVal]
    refine TabRep.comp ?_ ih
    split_ifs
    · exact hgs _
    · exact hgi _

theorem fusionGenerationOf_of_check {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    {a b : Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {a, b}) {D : Data} (hn : D.n = n)
    (hp : D.p.Prime) (ha : TabRep D.aT a) (hb : TabRep D.bT b) (h : check D = true) :
    FusionGenerationOf ↥G D.p := by
  subst hn
  simp only [check, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hinv, hinvg⟩, hxp⟩, hyp⟩, hcomm⟩, hx1⟩, hlen⟩, hfus⟩, hwA⟩, hwB⟩ := h
  set S : List (Equiv.Perm (Fin D.n)) := [a, b] with hSdef
  have hgs : ∀ j, TabRep ((gsT D).getD j (idTab D.n)) (S.getD j 1) := by
    intro j
    match j with
    | 0 =>
      rw [show (gsT D).getD 0 (idTab D.n) = D.aT by simp [gsT]]
      exact ha
    | 1 =>
      rw [show (gsT D).getD 1 (idTab D.n) = D.bT by simp [gsT]]
      exact hb
    | j + 2 =>
      rw [show (gsT D).getD (j + 2) (idTab D.n) = idTab D.n by simp [gsT]]
      simpa [hSdef] using TabRep.idTab (n := D.n)
  have hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹ := by
    intro j
    match j with
    | 0 =>
      obtain ⟨h1, h2⟩ := hinv 0 (by norm_num)
      rw [show (giT D).getD 0 (idTab D.n) = (giT D)[0]! by simp [giT, gsT]]
      exact ha.inv h1 (by simpa [gsT] using h2)
    | 1 =>
      obtain ⟨h1, h2⟩ := hinv 1 (by norm_num)
      rw [show (giT D).getD 1 (idTab D.n) = (giT D)[1]! by simp [giT, gsT]]
      exact hb.inv h1 (by simpa [gsT] using h2)
    | j + 2 =>
      rw [show (giT D).getD (j + 2) (idTab D.n) = idTab D.n by simp [giT, gsT]]
      simpa [hSdef] using TabRep.idTab (n := D.n)
  have hxrep : TabRep (xT D) (wordVal S D.xW) := wordT_rep S _ _ hgs hgi D.xW
  have hyrep : TabRep (yT D) (wordVal S D.yW) := wordT_rep S _ _ hgs hgi D.yW
  set S' : List (Equiv.Perm (Fin D.n)) := D.gWs.map (wordVal S) with hS'def
  have hgT : ∀ j, TabRep ((gT D).getD j (idTab D.n)) (S'.getD j 1) := by
    intro j
    by_cases hj : j < D.gWs.length
    · rw [show (gT D).getD j (idTab D.n) = wordT D.n (gsT D) (giT D) D.gWs[j] by simp [gT, hj],
        show S'.getD j 1 = wordVal S D.gWs[j] by simp [hS'def, hj]]
      exact wordT_rep S _ _ hgs hgi _
    · have hn : D.gWs[j]? = none := List.getElem?_eq_none (by omega)
      rw [show (gT D).getD j (idTab D.n) = idTab D.n by simp [gT, hn],
        show S'.getD j 1 = 1 by simp [hS'def, hn]]
      exact TabRep.idTab
  have hsize : (gT D).size = D.gWs.length := by simp [gT]
  have hgTi : ∀ j, TabRep ((gTi D).getD j (idTab D.n)) (S'.getD j 1)⁻¹ := by
    intro j
    by_cases hj : j < D.gWs.length
    · obtain ⟨h1, h2⟩ := hinvg j (by rw [hsize]; exact hj)
      rw [show (gTi D).getD j (idTab D.n) = (gTi D)[j]! by
        simp [gTi, gT, hj]]
      have := hgT j
      rw [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hj]] at this
      exact this.inv h1 h2
    · have hn : D.gWs[j]? = none := List.getElem?_eq_none (by omega)
      rw [show (gTi D).getD j (idTab D.n) = idTab D.n by simp [gTi, gT, hn],
        show S'.getD j 1 = 1 by simp [hS'def, hn]]
      simpa using TabRep.idTab (n := D.n)
  have hx : wordVal S D.xW ^ D.p = 1 :=
    ((powT_rep hxrep D.p).eq_iff TabRep.idTab).1 hxp
  have hy : wordVal S D.yW ^ D.p = 1 :=
    ((powT_rep hyrep D.p).eq_iff TabRep.idTab).1 hyp
  have hxy : wordVal S D.xW * wordVal S D.yW = wordVal S D.yW * wordVal S D.xW :=
    ((hxrep.comp hyrep).eq_iff (hyrep.comp hxrep)).1 hcomm
  have hx1' : wordVal S D.xW ≠ 1 := fun h1 => hx1 ((hxrep.eq_iff TabRep.idTab).2 h1)
  have haS : a ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hbS : b ∈ G := by rw [hG]; exact Subgroup.subset_closure (by simp)
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    exacts [haS, hbS]
  have hS'G : ∀ g ∈ S', g ∈ G := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG w
  have hfus' : ∀ g ∈ S', ∃ i j k l : ℕ, wordVal S D.xW ^ i * wordVal S D.yW ^ j ≠ 1 ∧
      g * (wordVal S D.xW ^ i * wordVal S D.yW ^ j) =
        (wordVal S D.xW ^ k * wordVal S D.yW ^ l) * g := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj' : j < (gT D).size := by rw [hsize]; simpa [hS'def] using hj
    have hf := hfus
    unfold fusOK at hf
    simp only [allBelow_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      beq_iff_eq] at hf
    obtain ⟨hne, heq⟩ := hf j hj'
    generalize hd : D.fd.getD j (0, 0, 0, 0) = d at hne heq
    obtain ⟨i, l, k, m⟩ := d
    simp only [fusPair] at hne heq
    have hu : TabRep (comp D.n (powT D.n (xT D) i) (powT D.n (yT D) l))
        (wordVal S D.xW ^ i * wordVal S D.yW ^ l) :=
      (powT_rep hxrep i).comp (powT_rep hyrep l)
    have hw : TabRep (comp D.n (powT D.n (xT D) k) (powT D.n (yT D) m))
        (wordVal S D.xW ^ k * wordVal S D.yW ^ m) :=
      (powT_rep hxrep k).comp (powT_rep hyrep m)
    have hgj : TabRep (gT D)[j]! S'[j] := by
      have hjl : j < D.gWs.length := by rw [← hsize]; exact hj'
      have := hgT j
      rwa [show (gT D).getD j (idTab D.n) = (gT D)[j]! by simp [gT, hjl],
        show S'.getD j 1 = S'[j] by simp [hj]] at this
    refine ⟨i, l, k, m, fun h1 => hne ((hu.eq_iff TabRep.idTab).2 h1), ?_⟩
    exact ((hgj.comp hu).eq_iff (hw.comp hgj)).1 heq
  have hA : wordVal S' D.wA = a := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi D.wA
    rw [hwA] at h1
    exact h1.perm_eq ha
  have hB : wordVal S' D.wB = b := by
    have h1 := wordT_rep S' (gT D) (gTi D) hgT hgTi D.wB
    rw [hwB] at h1
    exact h1.perm_eq hb
  refine fusionGenerationOf_of_gens hp hG (x := wordVal S D.xW) (y := wordVal S D.yW) hx hy hxy hx1'
    (wordVal_mem S G hSG _) (wordVal_mem S G hSG _) (Γ := {g | g ∈ S'}) (fun g hg => hS'G g hg)
    hfus' ?_
  intro z hz
  rcases hz with rfl | rfl
  · rw [← hA]
    exact wordVal_mem S' (Subgroup.closure {g | g ∈ S'}) (fun g hg => Subgroup.subset_closure hg) _
  · rw [← hB]
    exact wordVal_mem S' (Subgroup.closure {g | g ∈ S'}) (fun g hg => Subgroup.subset_closure hg) _

end CFSG.AGLEmbedding.FusD2
