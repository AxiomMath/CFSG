module

public import CFSG.Certificates.Kernel.CoreD2K.Sound
public import Certificates.Data.CoreD2LinesOne

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm

theorem lines_facts_one {n w : Nat} {V : VData}
    {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat} {cnt cap len : Nat}
    (H : KHyps n w V GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hst : allN V.ys.length (fun i => bAnd(wordOKOne V i (V.wAs.getD i []),
      wordOKOne V i (V.wBs.getD i []))) = true)
    (hp : V.base.p.Prime) {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), Nat.card E = V.base.p ^ 3 ∧
      (∀ x ∈ E, x ^ V.base.p = 1) ∧ (∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x) ∧
      E ≤ Subgroup.closure {a, b} ∧
      ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E → IsElemAbelian V.base.p A →
        Nat.card A = V.base.p ^ 2 →
        ∃ Γ : Set (Equiv.Perm (Fin n)), Γ ⊆ Subgroup.closure {a, b} ∧
          ({a, b} : Set (Equiv.Perm (Fin n))) ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
            (∃ u v : Equiv.Perm (Fin n), u ∈ A ∧ v ∈ A ∧ u ^ V.base.p = 1 ∧ v ^ V.base.p = 1 ∧
              u * v = v * u ∧ u ≠ 1 ∧ (∀ j < V.base.p, v ≠ u ^ j) ∧ ∃ α β γ δ : ℕ,
                g * u = (u ^ α * v ^ β) * g ∧ g * v = (u ^ γ * v ^ δ) * g) ∨
            (∃ y ∈ A, y ≠ 1 ∧ y ^ V.base.p = 1 ∧ ∃ α : ℕ, g * y = y ^ α * g) := by
  have hn := H.hn
  set p := V.base.p with hpdef
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  have hgens := H.hgens
  unfold gensK at hgens
  obtain ⟨hG2, hrest⟩ := band_e hgens
  obtain ⟨hE1, hG1⟩ := band_e hrest
  have hG2' : allN 2 (fun j => permOK n w (mask w) (n * w) (GP j) (GPI j)) = true := hG2
  have hSr : ∀ j < 2, TabRep (unpack n w (GP j)) (S.getD j 1) := by
    intro j hj
    rcases j with _ | _ | j
    · exact ha
    · exact hb
    · omega
  have hword : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GP GPI 2 wd r = true → TabRep (unpack n w r) (wordVal S wd) :=
    fun h => pr_word (k := 2) rfl hG2' hSr h
  have hSG : ∀ g ∈ S, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  set ne := V.base.eW.length with hne
  set Le : List (Equiv.Perm (Fin n)) := V.base.eW.map (wordVal S) with hLe
  have hLeget : ∀ k < ne, Le.getD k 1 = wordVal S (V.base.eW.getD k []) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLe] using hk), List.getD_eq_getElem _ _ hk,
      List.getElem_map]
  have hEk : ∀ k < ne, wordEqK n w (mask w) (pidn n w) GP GPI 2 (V.base.eW.getD k []) (EG k) =
      true ∧ canonK n w (mask w) (n * w) (EG k) = true := fun k hk =>
    band_e (PK.allN_iff.1 hE1 k hk)
  have hEP : ∀ k < ne, PR n w (EG k) (Le.getD k 1) := fun k hk =>
    ⟨(hEk k hk).2, by rw [hLeget k hk]; exact hword (hEk k hk).1⟩
  have hLmem : ∀ k < ne, Le.getD k 1 ∈ Le := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLe] using hk)]
    exact List.getElem_mem _
  have hLeG : ∀ g ∈ Le, g ∈ G := by
    intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  set ng := V.base.gWs.length with hng
  set Lg : List (Equiv.Perm (Fin n)) := V.base.gWs.map (wordVal S) with hLg
  have hLgget : ∀ j < ng, Lg.getD j 1 = wordVal S (V.base.gWs.getD j []) := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj), List.getD_eq_getElem _ _ hj,
      List.getElem_map]
  have hGk : ∀ j < ng, wordEqK n w (mask w) (pidn n w) GP GPI 2 (V.base.gWs.getD j []) (GT j) =
      true ∧ permOK n w (mask w) (n * w) (GT j) (GTI j) = true := fun j hj =>
    band_e (PK.allN_iff.1 hG1 j hj)
  have hgP : ∀ j < ng, PR n w (GT j) (Lg.getD j 1) := fun j hj =>
    ⟨(perm_canon (hGk j hj).2 hn).1, by rw [hLgget j hj]; exact hword (hGk j hj).1⟩
  have hGTp : allN ng (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) = true :=
    PK.allN_iff.2 fun j hj => (hGk j hj).2
  have hwordG : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GT GTI ng wd r = true → TabRep (unpack n w r) (wordVal Lg wd) :=
    fun h => pr_word (by simp [hLg, hng]) hGTp (fun j hj => (hgP j hj).2) h
  have hLgmem : ∀ j < ng, Lg.getD j 1 ∈ Lg := fun j hj => by
    rw [List.getD_eq_getElem _ _ (by simpa [hLg] using hj)]
    exact List.getElem_mem _
  have hLgG : ∀ g ∈ Lg, g ∈ G := by
    intro g hg
    obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hg
    exact wordVal_mem S G hSG wd
  set gens : Array Tab := Array.ofFn (n := ne) fun k => unpack n w (EG k.val) with hgens'
  have hgget : ∀ k < ne, gens[k]! = unpack n w (EG k) := fun k hk => by
    rw [hgens', getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  have hgsz : gens.size = ne := Array.size_ofFn
  have hgOK : GensOK n w ne EG gens := ⟨hgsz, fun j hj => ⟨hgget j hj, (hEk j hj).2⟩⟩
  obtain ⟨-, henum⟩ := penumK_left_sound hn hgOK H.hh
    (fun i hi => CFSG.KS.BaseMask.penumSl_spec H.hsl (Nat.zero_le i) (by have := H.hlen; omega) hi)
  set E := Subgroup.closure {g | g ∈ Le} with hEdef
  have hA : ∀ g ∈ {g | g ∈ Le}, ∃ j < gens.size, TabRep gens[j]! g := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have hk' : k < ne := by simpa [hLe] using hk
    refine ⟨k, by rw [hgsz]; exact hk', ?_⟩
    rw [hgget k hk', ← List.getD_eq_getElem _ 1 hk]
    exact (hEP k hk').2
  have hgensE : ∀ j < gens.size, ∃ g ∈ {g | g ∈ Le}, TabRep gens[j]! g := by
    intro j hj
    rw [hgsz] at hj
    exact ⟨Le.getD j 1, hLmem j hj, by rw [hgget j hj]; exact (hEP j hj).2⟩
  have hE := enumerates_closure hA hgensE henum
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE.card, Array.length_toList, rec_size, H.hcnt]
  have hEG : E ≤ G := by
    rw [hEdef, Subgroup.closure_le]
    exact fun g hg => hLeG g hg
  have hmemE : ∀ k < ne, Le.getD k 1 ∈ E := fun k hk => Subgroup.subset_closure (hLmem k hk)
  have hnab := H.hnab
  unfold nabK at hnab
  have hnab' := bnot_e hnab
  have hnc : ∃ x ∈ E, ∃ y ∈ E, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hall : allN ne (fun i => strictB (EG i) (fun x => allN ne (fun j => strictB (EG j)
        (fun y => Nat.beq (pcomp n w (mask w) x y) (pcomp n w (mask w) y x))))) = true := by
      refine PK.allN_iff.2 fun i hi => ?_
      rw [PK.strictB_eq]
      refine PK.allN_iff.2 fun j hj => ?_
      rw [PK.strictB_eq]
      exact (pr_beq (pr_mul (hEP i hi) (hEP j hj)) (pr_mul (hEP j hj) (hEP i hi))).2
        (hcon _ (hmemE i hi) _ (hmemE j hj))
    rw [hall] at hnab'
    exact absurd hnab' (by decide)
  have hcen := H.hcen
  unfold cenK at hcen
  rw [PK.strictB_eq] at hcen
  obtain ⟨h0, hcen⟩ := band_e hcen
  obtain ⟨hzp, hcen⟩ := band_e hcen
  obtain ⟨hz1, hzc⟩ := band_e hcen
  have h0' : 0 < ne := Nat.blt_eq.mp h0
  set z := Le.getD 0 1 with hzdef
  have hzP : PR n w (EG 0) z := hEP 0 h0'
  have hzE : z ∈ E := hmemE 0 h0'
  have hzp' : z ^ p = 1 := (pr_beq (pr_pow hn hzP p) (pr_one hn)).1 hzp
  have hz1' : z ≠ 1 := pr_ne hzP (pr_one hn) hz1
  have hzcent : ∀ x ∈ E, x * z = z * x := by
    have hcl : E ≤ Subgroup.centralizer ({z} : Set (Equiv.Perm (Fin n))) := by
      rw [hEdef, Subgroup.closure_le]
      intro g hg
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
      have hk' : k < ne := by simpa [hLe] using hk
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← List.getD_eq_getElem _ 1 hk]
      have hc := PK.allN_iff.1 hzc k hk'
      rw [PK.strictB_eq] at hc
      exact ((pr_beq (pr_mul hzP (hEP k hk')) (pr_mul (hEP k hk') hzP)).1 hc).symm
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcl hx)
  have hlines := H.hlines
  unfold linesK at hlines
  rw [PK.strictB_eq] at hlines
  obtain ⟨hys, hlines⟩ := band_e hlines
  obtain ⟨hvs, hds⟩ := band_e hlines
  have hys' : V.ys.length = p + 1 := Nat.eq_of_beq_eq_true hys
  set v : ℕ → Equiv.Perm (Fin n) := fun i => Le.getD (V.ys.getD i 0) 1 with hvdef
  have hvK : ∀ i < V.ys.length, V.ys.getD i 0 < ne ∧
      vK n w p (EG 0) (EG (V.ys.getD i 0)) = true := fun i hi => by
    obtain ⟨h1, h2⟩ := band_e (PK.allN_iff.1 hvs i hi)
    exact ⟨Nat.blt_eq.mp h1, h2⟩
  have hvP : ∀ i < V.ys.length, PR n w (EG (V.ys.getD i 0)) (v i) := fun i hi =>
    hEP _ (hvK i hi).1
  have hvfacts : ∀ i < V.ys.length, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧
      ∀ k < p, v i ≠ z ^ k := by
    intro i hi
    obtain ⟨hlt, hk⟩ := hvK i hi
    unfold vK at hk
    obtain ⟨hk1, hk2⟩ := band_e hk
    have hvE : v i ∈ E := hmemE _ hlt
    exact ⟨hvE, (pr_beq (pr_pow hn (hvP i hi) p) (pr_one hn)).1 hk1, (hzcent _ hvE).symm,
      fun k hk' => pr_ne (hvP i hi) (pr_pow hn hzP k) (PK.allN_iff.1 hk2 k hk')⟩
  have hv' : ∀ i ≤ p, v i ∈ E ∧ v i ^ p = 1 ∧ z * v i = v i * z ∧ ∀ k < p, v i ≠ z ^ k :=
    fun i hi => hvfacts i (by omega)
  have hd : ∀ j ≤ p, ∀ i < j, v j ∉ Subgroup.closure ({z, v i} : Set (Equiv.Perm (Fin n))) := by
    intro j hj i hij hmem
    have hj' : j < V.ys.length := by omega
    have hi' : i < V.ys.length := by omega
    have hdj := PK.allN_iff.1 hds j hj'
    rw [PK.strictB_eq] at hdj
    have hout := PK.allN_iff.1 hdj i hij
    obtain ⟨hvi, hvp, hzv, -⟩ := hvfacts i hi'
    obtain ⟨c, hc, d, hd, e⟩ := exists_pow_mul_pow_of_mem hp.pos hzv hzp' hvp hmem
    exact outK_sound hn hzP (hvP i hi') (hvP j hj') hout c hc d hd e
  have hEexp : ∀ x ∈ E, x ^ p = 1 := by
    intro x hx
    obtain ⟨i, hi, hxY⟩ := mem_lines_of_distinct hp hEc hzE hzp' hz1' hv' hd x hx
    obtain ⟨-, hvp, hzv, -⟩ := hv' i hi
    obtain ⟨c, -, d, -, rfl⟩ := exists_pow_mul_pow_of_mem hp.pos hzv hzp' hvp hxY
    have hc : Commute (z ^ c) (v i ^ d) := (Commute.pow_pow hzv c d)
    rw [hc.mul_pow, ← pow_mul, mul_comm c, pow_mul, hzp', one_pow, ← pow_mul, mul_comm d, pow_mul,
      hvp, one_pow, one_mul]
  have hkinds := H.hkinds
  unfold kindsK at hkinds
  obtain ⟨hgkl, hkall⟩ := band_e hkinds
  have hwords := H.hwords
  unfold wordsK at hwords
  obtain ⟨-, hwords⟩ := band_e hwords
  obtain ⟨-, hwall⟩ := band_e hwords
  refine ⟨E, hEc, hEexp, hnc, hEG, ?_⟩
  intro A hAE hAe hAc
  obtain ⟨i, hi, hYA⟩ := eq_line_of_elemAbelian hp hEc hnc hzE hzp' hz1' hzcent hv' hd hAE hAe hAc
  have hi' : i < V.ys.length := by omega
  have hzA : z ∈ A := by
    rw [← hYA]
    exact Subgroup.subset_closure (by simp)
  set Γ : Set (Equiv.Perm (Fin n)) := {g | ∃ j < ng, allowedOne V i j = true ∧ g = Lg.getD j 1}
    with hΓdef
  have hall : ∀ wd : List Int, (∀ l ∈ wd, allowedOne V i (l.natAbs - 1) = true) →
      wordVal Lg wd ∈ Subgroup.closure Γ := by
    intro wd hw
    refine wordVal_mem_of Lg _ wd fun l hl => ?_
    by_cases hlt : l.natAbs - 1 < ng
    · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
    · rw [List.getD_eq_default _ _ (by simp [hLg]; omega)]
      exact Subgroup.one_mem _
  obtain ⟨hwA, hwrest⟩ := band_e (PK.allN_iff.1 hwall i hi')
  obtain ⟨hwB, -⟩ := band_e hwrest
  obtain ⟨hoA, hoB⟩ := band_e (PK.allN_iff.1 hst i hi')
  unfold wordOKOne at hoA hoB
  have hA' : wordVal Lg (V.wAs.getD i []) = a := (hwordG hwA).perm_eq ha
  have hB' : wordVal Lg (V.wBs.getD i []) = b := (hwordG hwB).perm_eq hb
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rintro g ⟨j, hj, -, rfl⟩
    exact hLgG _ (hLgmem j hj)
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact hall _ (List.all_eq_true.1 hoA)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact hall _ (List.all_eq_true.1 hoB)
  · rintro g ⟨j, hj, hok, rfl⟩
    obtain ⟨hidx, hk⟩ := band_e (PK.allN_iff.1 hkall j hj)
    have hidx' : (V.gk.getD j default).idx < V.ys.length := Nat.blt_eq.mp hidx
    simp only [allowedOne, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq] at hok
    generalize hf : V.gk.getD j default = f at hk hok hidx'
    unfold kindK at hk
    rw [PK.strictB_eq] at hk
    have huP := hzP
    have hvfP := hvP f.idx hidx'
    obtain ⟨hvE', hvp', hzv', hvz'⟩ := hvfacts f.idx hidx'
    have hyP := pr_mul (pr_pow hn huP f.f1) (pr_pow hn hvfP f.f2)
    by_cases hk0 : f.kind = 0
    · have hk' := bif_t (by rw [hk0]; rfl) hk
      obtain ⟨e1, e2⟩ := band_e hk'
      have hfi : f.idx = i := hok.resolve_right fun h => h.1 hk0
      have hvA : v f.idx ∈ A := by
        rw [hfi, ← hYA]
        exact Subgroup.subset_closure (by simp)
      left
      refine ⟨z, v f.idx, hzA, hvA, hzp', hvp', hzv', hz1', hvz', f.f1, f.f2, f.f3, f.f4, ?_, ?_⟩
      · exact (pr_beq (pr_mul (hgP j hj) huP) (pr_mul hyP (hgP j hj))).1 e1
      · exact (pr_beq (pr_mul (hgP j hj) hvfP)
          (pr_mul (pr_mul (pr_pow hn huP f.f3) (pr_pow hn hvfP f.f4)) (hgP j hj))).1 e2
    · have hk' := bif_f (Bool.eq_false_iff.2 fun e => hk0 (Nat.eq_of_beq_eq_true e)) hk
      obtain ⟨e0, hk'⟩ := band_e hk'
      obtain ⟨e1, e2⟩ := band_e hk'
      right
      refine ⟨z ^ f.f1 * v f.idx ^ f.f2, ?_, pr_ne hyP (pr_one hn) e0,
        (pr_beq (pr_pow hn hyP p) (pr_one hn)).1 e1, f.f3,
        (pr_beq (pr_mul (hgP j hj) hyP) (pr_mul (pr_pow hn hyP f.f3) (hgP j hj))).1 e2⟩
      rcases hok with hidx'' | ⟨-, hf2⟩
      · rw [hidx'', ← hYA]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      · rw [hf2, pow_zero, mul_one]
        exact Subgroup.pow_mem _ hzA _

end CFSG.KD.CoreD2K

end
