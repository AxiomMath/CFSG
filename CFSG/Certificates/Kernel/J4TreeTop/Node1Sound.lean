module

public import CFSG.Certificates.Kernel.J4TreeTop.CoverKSound

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem eclassOK_spec {T : Tabs} {z e Ki m : ℕ} {l : List ℕ}
    (h : eclassOK T z e (Ki :: m :: l) = true) :
    invK (T.kel e) Ki = true ∧ e < 1024 ∧ (l.take m).length = m ∧ (∀ c ∈ l.take m, c < 2048) ∧
      spanAll (translK (T.eta z) :: commE T (T.kel e) Ki ++
        (l.take m).map fun c => translK (T.eta c)) = true ∧
      ∀ I < 2 ^ m, ecLeaf e ((l.drop m).headD 0)
        (prodFrom (T.kel e) ((l.take m).map fun c => M (M Ki (T.eta c)) (T.kel e)) I) I = true := by
  simp only [eclassOK, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hinv, he⟩, hlen⟩, hcs⟩, hspan⟩, henum⟩ := h
  refine ⟨hinv, he, hlen, hcs, hspan, fun I hI => ?_⟩
  have := enumOK_spec henum I (by rw [List.length_map, hlen]; exact hI)
  simpa using this

theorem ecLeaf_spec {e L X I : ℕ} (h : ecLeaf e L X I = true) (hsq : sqOneK X = true)
    (h1 : e ≠ 0 ∨ I ≠ 0) : L.testBit I = true := by
  unfold ecLeaf at h
  have h0 : (e == 0 && I == 0) = false := by
    rcases h1 with h1 | h1 <;> simp [h1]
  rw [hsq, h0] at h
  simpa using h

theorem eclass_leaf_sound {e L X I : ℕ} (h : ecLeaf e L X I = true) {x : J} (hx : PK x X)
    (hsq : x * x = 1) (h1 : e ≠ 0 ∨ I ≠ 0) : L.testBit I = true :=
  ecLeaf_spec h ((pk_sq hx).mp hsq) h1

theorem c1Walk_spec {T : Tabs} {G GI Y : List ℕ} {Z e : ℕ} {cs : List ℕ} {L : ℕ} :
    ∀ (f acc : ℕ) (R : List ℕ), c1Walk T G GI Y Z e cs L f acc R = true →
    ∀ I, L.testBit I = true → acc.testBit I = false →
      (∃ v₁ v₂ : ℕ, non2AK T.sx (ccT T (xorSel cs I, e)) v₁ = true ∧
        non2AK T.sx (M (ccT T (xorSel cs I, e)) Z) v₂ = true) ∨
      ∃ j : ℕ, ∃ ch : List ℕ, j < Y.length ∧ (∀ i ∈ ch, i < G.length) ∧
        (conjCh G GI (ccT T (xorSel cs I, e)) ch = Y.getD j 0 ∨
          conjCh G GI (ccT T (xorSel cs I, e)) ch = M (Y.getD j 0) Z)
  | _, acc, [], h, I, hL, hacc => by
    simp only [c1Walk, beq_iff_eq] at h
    rw [h, hL] at hacc
    exact absurd hacc (by simp)
  | 0, _, _ :: _, h, _, _, _ => by simp [c1Walk] at h
  | _ + 1, _, [_], h, _, _, _ => by simp [c1Walk] at h
  | f + 1, acc, I' :: j :: l, h, I, hL, hacc => by
    have hacc' : I' ≠ I → (acc ||| 2 ^ I').testBit I = false := by
      intro hII
      rw [Nat.testBit_or, Nat.testBit_two_pow, decide_eq_false hII, Bool.or_false, hacc]
    simp only [c1Walk] at h
    split_ifs at h with hj0
    · rcases l with _ | ⟨v₁, _ | ⟨v₂, l⟩⟩
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, hrest⟩ := h
        by_cases hII : I' = I
        · subst hII
          exact Or.inl ⟨v₁, v₂, h1, h2⟩
        · exact c1Walk_spec f _ _ hrest I hL (hacc' hII)
    · rcases l with _ | ⟨d, l⟩
      · simp at h
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, beq_iff_eq,
          List.all_eq_true] at h
        obtain ⟨⟨⟨⟨hjY, -⟩, hch⟩, hW⟩, hrest⟩ := h
        by_cases hII : I' = I
        · subst hII
          refine Or.inr ⟨j - 1, l.take d, hjY, fun i hi => hch i hi, ?_⟩
          rcases hW with hW | hW
          · exact Or.inl (Nat.eq_of_beq_eq_true hW)
          · exact Or.inr (Nat.eq_of_beq_eq_true hW)
        · exact c1Walk_spec f _ _ hrest I hL (hacc' hII)

theorem c1Glob_sound {T : Tabs} (hT : tabsOK T = true) {z : ℕ} (hz : coordOK (z, 0) = true)
    {g : C1Glob} (hg : c1GlobOK T z g = true) :
    let Gs := g.wn.map (fun w => wordProd xJ (wordC 64 w)) ++ g.cc.map burnsideJ4NP_treeElt
    List.Forall₂ PK Gs g.G ∧ List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI ∧
      Subgroup.closure {s | s ∈ Gs} ≤
        Hj ⊓ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)} ∧
      List.Forall₂ PK (g.ys.map burnsideJ4NP_treeElt) (g.ys.map (ccT T)) ∧
      g.ys = topNode1.children.map TopChild.y := by
  intro Gs
  unfold c1GlobOK at hg
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hg
  have hY2 := List.rel_append (forall₂_word hT g.wn) (forall₂_cc hT _ (List.all_eq_true.mp h3))
  have hG2 : List.Forall₂ PK Gs g.G := forall₂_of_beq hY2 (by rw [h1]; simp) h5
  have hGI2 := forall₂_inv hG2 h6 h2
  have hZ : PK (burnsideJ4NP_treeElt (z, 0)) (ccT T (z, 0)) := pk_cc hT hz
  refine ⟨hG2, hGI2, (Subgroup.closure_le _).mpr fun s hs => ?_,
    forall₂_cc hT _ (List.all_eq_true.mp h4), h8⟩
  obtain ⟨X, hX, hsX⟩ := forall₂_exists hG2 s hs
  refine Subgroup.mem_inf.mpr ⟨hsX.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  exact (pk_comm hsX hZ).mpr (List.all_eq_true.mp h7 X hX)

theorem cover1_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {z : ℕ}
    (hz : coordOK (z, 0) = true) {g : C1Glob} (hg : c1GlobOK T z g = true) {e Ki m : ℕ}
    {l R : List ℕ} (h : cover1OK T z e g (Ki :: m :: l) R = true) {I : ℕ}
    (hI : ((l.drop m).headD 0).testBit I = true) {x : J}
    (hx : PK x (ccT T (xorSel (l.take m) I, e))) :
    (burnsideJ4NP_treeTest (burnsideJ4NP_encJ x) = false ∧
        burnsideJ4NP_treeTest (burnsideJ4NP_encJ (x * burnsideJ4NP_treeElt (z, 0))) = false) ∨
      ∃ j < topNode1.children.length,
        ∃ n ∈ Hj ⊓ Subgroup.centralizer {burnsideJ4NP_treeElt (z, 0)},
        n * x * n⁻¹ = burnsideJ4NP_treeElt (topNode1.children.getD j default).y ∨
          n * x * n⁻¹ = burnsideJ4NP_treeElt (topNode1.children.getD j default).y *
            burnsideJ4NP_treeElt (z, 0) := by
  obtain ⟨hG2, hGI2, hcl, hY2, hys⟩ := c1Glob_sound hT hz hg
  have hZ : PK (burnsideJ4NP_treeElt (z, 0)) (ccT T (z, 0)) := pk_cc hT hz
  simp only [cover1OK] at h
  rcases c1Walk_spec _ _ _ h I hI (Nat.zero_testBit I) with ⟨v₁, v₂, h1, h2⟩ |
    ⟨j, ch, hj, hch, hW⟩
  · exact Or.inl ⟨non2AK_spec h1 hx.2 hsx, non2AK_spec h2 (pk_mul hx hZ).2 hsx⟩
  · right
    obtain ⟨n, hn, hpk⟩ := pk_conjCh hG2 hGI2 ch hch hx
    have hjys : j < g.ys.length := by
      rw [List.length_map] at hj
      exact hj
    have hjc : j < topNode1.children.length := by
      have e : g.ys.length = topNode1.children.length := by rw [hys, List.length_map]
      rw [← e]
      exact hjys
    have hjy : j < (g.ys.map burnsideJ4NP_treeElt).length := by
      rw [List.length_map]
      exact hjys
    have hyj := forall₂_getD (a := 1) (b := 0) hY2 j hjy
    have hyeq : (g.ys.map burnsideJ4NP_treeElt).getD j 1 =
        burnsideJ4NP_treeElt (topNode1.children.getD j default).y := by
      simp only [List.getD_eq_getElem?_getD, hys, List.map_map, List.getElem?_map,
        List.getElem?_eq_getElem hjc, Option.map_some, Option.getD_some, Function.comp_apply]
    refine ⟨j, hjc, n, hcl hn, ?_⟩
    rcases hW with hW | hW
    · left
      rw [pk_eq hpk (by rw [hW]; exact hyj), hyeq]
    · right
      rw [pk_eq hpk (by rw [hW]; exact pk_mul hyj hZ), hyeq]

end CFSG.KC.J4TreeT
