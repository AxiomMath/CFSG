module

public import CFSG.Certificates.Kernel.J4TreeTop.SylowSound
public import Certificates.Data.Kernel.J4TreeTopCoverK

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT


theorem ckWalk_spec {sx : ℕ} {G GI Y AL : List ℕ} {X₀ : ℕ} {S : List ℕ} {L : ℕ} :
    ∀ (f acc : ℕ) (R : List ℕ), ckWalk sx G GI Y AL X₀ S L f acc R = true →
    ∀ I, L.testBit I = true → acc.testBit I = false →
      (∀ t < AL.length, ∃ z, non2AK sx (M (prodFrom X₀ S I) (AL.getD t 0)) z = true) ∨
      ∃ j m : ℕ, ∃ ch : List ℕ, j < Y.length ∧ m < AL.length ∧ (∀ i ∈ ch, i < G.length) ∧
        conjCh G GI (prodFrom X₀ S I) ch = M (Y.getD j 0) (AL.getD m 0)
  | _, acc, [], h, I, hL, hacc => by
    simp only [ckWalk, beq_iff_eq] at h
    rw [h, hL] at hacc
    exact absurd hacc (by simp)
  | 0, _, _ :: _, h, _, _, _ => by simp [ckWalk] at h
  | _ + 1, _, [_], h, _, _, _ => by simp [ckWalk] at h
  | f + 1, acc, I' :: j :: l, h, I, hL, hacc => by
    have hbit : ∀ a : ℕ, (acc ||| 2 ^ I').testBit I = false → I' ≠ I := by
      intro _ h0 hII
      rw [Nat.testBit_or, Nat.testBit_two_pow, decide_eq_true hII, Bool.or_true] at h0
      exact Bool.noConfusion h0
    have hacc' : I' ≠ I → (acc ||| 2 ^ I').testBit I = false := by
      intro hII
      rw [Nat.testBit_or, Nat.testBit_two_pow, decide_eq_false hII, Bool.or_false, hacc]
    simp only [ckWalk] at h
    split_ifs at h with hj0
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hlen, hall⟩, hrest⟩ := h
      by_cases hII : I' = I
      · subst hII
        left
        intro t ht
        exact ⟨_, zip_all_getD (a := 0) (b := 0) hall hlen.symm t ht⟩
      · exact ckWalk_spec f _ _ hrest I hL (hacc' hII)
    · rcases l with _ | ⟨m, _ | ⟨d, l⟩⟩
      · simp at h
      · simp at h
      · simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq, List.all_eq_true] at h
        obtain ⟨⟨⟨⟨⟨hjY, hm⟩, hd⟩, hch⟩, hW⟩, hrest⟩ := h
        by_cases hII : I' = I
        · subst hII
          right
          exact ⟨j - 1, m, l.take d, hjY, hm, fun i hi => hch i hi,
            Nat.eq_of_beq_eq_true hW⟩
        · exact ckWalk_spec f _ _ hrest I hL (hacc' hII)

theorem pk_conjCh {Gs : List J} {G GI : List ℕ} (hG : List.Forall₂ PK Gs G)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) Gs GI) :
    ∀ (ch : List ℕ), (∀ i ∈ ch, i < G.length) → ∀ {x : J} {X : ℕ}, PK x X →
      ∃ n ∈ Subgroup.closure {s | s ∈ Gs}, PK (n * x * n⁻¹) (conjCh G GI X ch)
  | [], _, x, X, hx => ⟨1, Subgroup.one_mem _, by simpa [conjCh] using hx⟩
  | i :: ch, hch, x, X, hx => by
    have hi : i < Gs.length := by rw [forall₂_length hG]; exact hch i List.mem_cons_self
    have hs := forall₂_getD (a := 1) (b := 0) hG i hi
    have hsi := forall₂_getD (a := 1) (b := 0) hGI i hi
    obtain ⟨n, hn, hpk⟩ := pk_conjCh hG hGI ch (fun i' hi' => hch i' (List.mem_cons_of_mem _ hi'))
      (pk_mul (pk_mul hs hx) hsi)
    refine ⟨n * Gs.getD i 1, Subgroup.mul_mem _ hn (Subgroup.subset_closure (getD_mem hi)), ?_⟩
    have e : n * Gs.getD i 1 * x * (n * Gs.getD i 1)⁻¹ =
        n * (Gs.getD i 1 * x * (Gs.getD i 1)⁻¹) * n⁻¹ := by group
    rw [e]
    exact hpk

theorem zip3_all {f : (ℕ × ℕ) × List ℕ → Bool} {G GI : List ℕ} {ms : List (List ℕ)}
    (h : ((G.zip GI).zip ms).all f = true) (h1 : GI.length = G.length) (h2 : ms.length = G.length) :
    ∀ j < G.length, f ((G.getD j 0, GI.getD j 0), ms.getD j []) = true := by
  intro j hj
  refine List.all_eq_true.mp h _ ?_
  have hj1 : j < GI.length := by omega
  have hj2 : j < ms.length := by omega
  have hz : j < ((G.zip GI).zip ms).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2]
  have e : ((G.zip GI).zip ms)[j] = ((G[j], GI[j]), ms[j]) := by simp
  rw [← e]
  exact List.getElem_mem _

theorem cover_normalizes {T : Tabs} (hT : tabsOK T = true) {B : List ℕ} {bJ : List J}
    (hB2 : List.Forall₂ PK bJ B) {H : WHd} {d : TopNode} {g : CKGlob}
    (h : ckGlobOK T B H d g = true) :
    let Gs := g.wn.map (fun w => wordProd xJ (wordC 64 w)) ++ g.cc.map burnsideJ4NP_treeElt
    List.Forall₂ PK Gs g.G ∧ List.Forall₂ (fun s X => PK s⁻¹ X) Gs g.GI ∧
      Subgroup.closure {s | s ∈ Gs} ≤ Hj ∧
      Subgroup.closure {s | s ∈ Gs} ≤
        Subgroup.normalizer ((Subgroup.closure {b | b ∈ bJ} : Subgroup J) : Set J) ∧
      List.Forall₂ PK (g.ys.map burnsideJ4NP_treeElt) (g.ys.map (ccT T)) ∧
      g.ys = d.children.map TopChild.y := by
  intro Gs
  unfold ckGlobOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, -⟩ := h
  have hY2 := List.rel_append (forall₂_word hT g.wn) (forall₂_cc hT _ (List.all_eq_true.mp h4))
  have hG2 : List.Forall₂ PK Gs g.G := forall₂_of_beq hY2 (by rw [h1]; simp) h6
  have hGI2 := forall₂_inv hG2 h7 h2
  refine ⟨hG2, hGI2, (Subgroup.closure_le Hj).mpr (mem_Hj_of hG2), ?_,
    forall₂_cc hT _ (List.all_eq_true.mp h5), h9⟩
  rw [Subgroup.closure_le]
  intro s hs
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
  have hiG : i < g.G.length := by rw [← forall₂_length hG2]; exact hi
  have hn := zip3_all h8 h2 h3 i hiG
  unfold normMsK at hn
  simp only [Bool.and_eq_true, List.all_eq_true] at hn
  have hs1 := forall₂_getD (a := 1) (b := 0) hG2 i hi
  have hsi := forall₂_getD (a := 1) (b := 0) hGI2 i hi
  rw [← List.getD_eq_getElem _ 1 hi]
  refine mem_normalizer_of fun b hb => ?_
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
  have htB : t < B.length := by rw [← forall₂_length hB2]; exact ht
  have hbX := forall₂_getD (a := 1) (b := 0) hB2 t ht
  have hmem : (B.getD t 0, t) ∈ B.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem htB]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htB]
  have hc := (hn.2 _ hmem).1
  rw [← List.getD_eq_getElem _ 1 ht,
    pk_beq (pk_mul (pk_mul hs1 hbX) hsi) (pk_prodMask hB2 _) hc]
  exact nwFrom_mem (fun b hb => Subgroup.subset_closure hb) (Subgroup.one_mem _) _

theorem coverK_sound {T : Tabs} (hT : tabsOK T = true)
    (hsx : ∀ t < 2048, T.sx.testBit t = (burnsideJ4NP_sextArr ())[t]?.getD false) {B : List ℕ}
    {bJ : List J} (hB2 : List.Forall₂ PK bJ B) {H : WHd} {d : TopNode} {g : CKGlob}
    (hg : ckGlobOK T B H d g = true) {e Ki ce m : ℕ} {l R : List ℕ}
    (h : coverKOK T B H g e (2 :: Ki :: ce :: m :: l) R = true) {I : ℕ}
    (hI : ((l.drop m).headD 0).testBit I = true) {x : J}
    (hx : PK x (prodFrom (M (T.eta ce) (T.kel e))
      (((l.take m).map fun i => H.vs.getD i 0).map fun c => M (M Ki (T.eta c)) (T.kel e)) I)) :
    (∀ v < 2 ^ B.length, burnsideJ4NP_treeTest (burnsideJ4NP_encJ (x * nwFrom 1 bJ v)) = false) ∨
      ∃ j < d.children.length, ∃ n ∈ Hj,
        n ∈ Subgroup.normalizer ((Subgroup.closure {b | b ∈ bJ} : Subgroup J) : Set J) ∧
        ∃ v < 2 ^ B.length,
          n * x * n⁻¹ = burnsideJ4NP_treeElt (d.children.getD j default).y * nwFrom 1 bJ v := by
  obtain ⟨hG2, hGI2, hH, hN, hY2, hys⟩ := cover_normalizes hT hB2 hg
  unfold coverKOK at h
  have hAL : ∀ t < ((List.range (2 ^ B.length)).map (prodMask B)).length,
      ((List.range (2 ^ B.length)).map (prodMask B)).getD t 0 = prodMask B t := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    simp
  have hALl : ((List.range (2 ^ B.length)).map (prodMask B)).length = 2 ^ B.length := by simp
  rcases ckWalk_spec _ _ _ h I hI (Nat.zero_testBit I) with hnon | ⟨j, v, ch, hj, hv, hch, hW⟩
  · left
    intro v hv
    obtain ⟨z, hz⟩ := hnon v (by rw [hALl]; exact hv)
    rw [hAL v (by rw [hALl]; exact hv)] at hz
    exact non2AK_spec hz (pk_mul hx (pk_prodMask hB2 v)).2 hsx
  · right
    obtain ⟨n, hn, hpk⟩ := pk_conjCh hG2 hGI2 ch hch hx
    have hjys : j < g.ys.length := by
      rw [List.length_map] at hj
      exact hj
    have hjc : j < d.children.length := by
      have e : g.ys.length = d.children.length := by rw [hys, List.length_map]
      rw [← e]
      exact hjys
    have hjy : j < (g.ys.map burnsideJ4NP_treeElt).length := by
      rw [List.length_map]
      exact hjys
    have hyj := forall₂_getD (a := 1) (b := 0) hY2 j hjy
    have hyeq : (g.ys.map burnsideJ4NP_treeElt).getD j 1 =
        burnsideJ4NP_treeElt (d.children.getD j default).y := by
      simp only [List.getD_eq_getElem?_getD, hys, List.map_map, List.getElem?_map,
        List.getElem?_eq_getElem hjc, Option.map_some, Option.getD_some, Function.comp_apply]
    rw [hAL v hv] at hW
    rw [hALl] at hv
    refine ⟨j, hjc, n, hH hn, hN hn, v, hv, ?_⟩
    rw [pk_beq hpk (pk_mul hyj (pk_prodMask hB2 v)) (by rw [hW]; exact Nat.beq_refl _), hyeq]

theorem coverK_sup {A : Subgroup J} {n x y a : J} (hn : n ∈ Subgroup.normalizer (A : Set J))
    (ha : a ∈ A) (he : n * x * n⁻¹ = y * a) :
    A ⊔ Subgroup.zpowers x = (A ⊔ Subgroup.zpowers y).map (MulAut.conj n⁻¹).toMonoidHom := by
  refine burnsideJ4NP_sup_zpowers_eq_map_conj (Subgroup.inv_mem _ hn) ?_
  have e : x = n⁻¹ * (y * a) * n := by rw [← he]; group
  have e2 : (n⁻¹ * y * n⁻¹⁻¹)⁻¹ * x = n⁻¹ * a * n := by rw [e]; group
  rw [e2]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) a).mp ha
  simpa using this

end CFSG.KC.J4TreeT
