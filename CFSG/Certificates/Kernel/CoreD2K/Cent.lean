module

public import Certificates.Data.Kernel.CoreD2K.Steps
public import CFSG.Certificates.Kernel.CoreD2K.Sound

public section

namespace CFSG.KD.CoreD2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MaxD2 CFSG.KS.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  CFSG.AGLEmbedding.CoreD2 CFSG.Open Certificates.CoreD2Perm

theorem gensK_eW {n w : Nat} {V : VData} {GP GPI EG GT GTI : Nat → Nat}
    (h : gensK n w V GP GPI EG GT GTI = true) :
    ∀ k < V.base.eW.length, bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2)
      (V.base.eW.getD k []) (EG k), canonK n w (mask w) (Nat.mul n w) (EG k)) = true := by
  unfold gensK at h
  exact PK.allN_iff.1 (band_e (band_e h).2).1

theorem linesK_congr {n w p : Nat} {V V' : VData} {EG : Nat → Nat} (hy : V.ys = V'.ys)
    (he : V.base.eW.length = V'.base.eW.length) : linesK n w p V EG = linesK n w p V' EG := by
  simp only [linesK, hy, he]

theorem conj_mem_of_closure {X : Type*} [Group X] {g : X} {S : Set X} {H : Subgroup X}
    (h : ∀ s ∈ S, g * s * g⁻¹ ∈ H) {y : X} (hy : y ∈ Subgroup.closure S) : g * y * g⁻¹ ∈ H := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact H.mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact H.inv_mem hx

structure KHypsC (n w : Nat) (V : VData) (reps : List Nat) (steps : List CStep)
    (GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat) (cnt cap len : Nat) : Prop where
  hn : szOK n w = true
  hgp : allN (nat_lit 2) (fun j => permOK n w (mask w) (Nat.mul n w) (GP j) (GPI j)) = true
  hE : ∀ k < V.base.eW.length, bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2)
    (V.base.eW.getD k []) (EG k), canonK n w (mask w) (Nat.mul n w) (EG k)) = true
  hG : ∀ j < V.base.gWs.length, bAnd(wordEqK n w (mask w) (pidn n w) GP GPI (nat_lit 2)
    (V.base.gWs.getD j []) (GT j), permOK n w (mask w) (Nat.mul n w) (GT j) (GTI j)) = true
  hh : penumHdK (pidn n w) cnt cap T PL = true
  hsl : penumSlK n w (mask w) (n * w) false EG EGI V.base.eW.length cnt T PL POS SRT SRI 0 len =
    true
  hlen : cnt ≤ len
  hcnt : cnt = V.base.p ^ 3
  hnab : nabK n w V.base.eW.length EG = true
  hcen : cenK n w V.base.p V.base.eW.length EG = true
  hlines : linesK n w V.base.p V EG = true
  hkinds : kindsK n w V EG GT = true
  hreps : ∀ i ∈ reps, repCK n w V GP GT GTI i = true
  hsteps : ∀ s ∈ steps, stepCK n w V EG GT s = true
  hchain : chainOK V.ys.length reps steps = true

theorem cent_facts {n w : Nat} {V : VData} {reps : List Nat} {steps : List CStep}
    {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat} {cnt cap len : Nat}
    (H : KHypsC n w V reps steps GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hp : V.base.p.Prime) (hkd : ∀ f ∈ V.gk, f.kind ≠ 0) (hf3 : ∀ f ∈ V.gk, f.f3 = 1)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup (Equiv.Perm (Fin n)), Nat.card E = V.base.p ^ 3 ∧
      E ≤ Subgroup.closure {a, b} ∧
      ∀ A : Subgroup (Equiv.Perm (Fin n)), A ≤ E → IsElemAbelian V.base.p A →
        Nat.card A = V.base.p ^ 2 →
        ∃ Γ : Set (Equiv.Perm (Fin n)), Γ ⊆ Subgroup.closure {a, b} ∧
          Subgroup.closure {a, b} ≤ Subgroup.closure Γ ∧
          ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g := by
  have hn := H.hn
  set p := V.base.p with hpdef
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set S : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  have hG2' : allN 2 (fun j => permOK n w (mask w) (n * w) (GP j) (GPI j)) = true := H.hgp
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
      true ∧ canonK n w (mask w) (n * w) (EG k) = true := fun k hk => band_e (H.hE k hk)
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
      true ∧ permOK n w (mask w) (n * w) (GT j) (GTI j) = true := fun j hj => band_e (H.hG j hj)
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
  have hkinds := H.hkinds
  unfold kindsK at hkinds
  obtain ⟨hgkl, hkall⟩ := band_e hkinds
  have hgkl' : V.gk.length = ng := Nat.eq_of_beq_eq_true hgkl
  set P : ℕ → Prop := fun i => ∃ Γ : Set (Equiv.Perm (Fin n)), Γ ⊆ G ∧ G ≤ Subgroup.closure Γ ∧
    ∀ g ∈ Γ, ∃ y ∈ Subgroup.closure ({z, v i} : Set (Equiv.Perm (Fin n))), y ≠ 1 ∧
      g * y = y * g with hPdef
  have hrep : ∀ i ∈ reps, i < V.ys.length ∧ P i := by
    intro i hi
    have h := H.hreps i hi
    unfold repCK at h
    obtain ⟨hlt, h⟩ := band_e h
    obtain ⟨hwA, h⟩ := band_e h
    obtain ⟨hwB, h⟩ := band_e h
    obtain ⟨hoA, hoB⟩ := band_e h
    have hi' : i < V.ys.length := Nat.blt_eq.mp hlt
    refine ⟨hi', ?_⟩
    set Γ : Set (Equiv.Perm (Fin n)) := {g | ∃ j < ng,
      (((V.gk.getD j default).kind = 0 ∨ (V.gk.getD j default).idx = i) ∨
        (V.gk.getD j default).f2 = 0) ∧ g = Lg.getD j 1} with hΓdef
    have hall : ∀ wd : List Int, (∀ l ∈ wd, (((V.gk.getD (l.natAbs - 1) default).kind = 0 ∨
        (V.gk.getD (l.natAbs - 1) default).idx = i) ∨
          (V.gk.getD (l.natAbs - 1) default).f2 = 0)) →
        wordVal Lg wd ∈ Subgroup.closure Γ := by
      intro wd hw
      refine wordVal_mem_of Lg _ wd fun l hl => ?_
      by_cases hlt : l.natAbs - 1 < ng
      · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
      · rw [List.getD_eq_default _ _ (by simp [hLg]; omega)]
        exact Subgroup.one_mem _
    simp only [wordOK, allowed, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hoA hoB
    have hA' : wordVal Lg (V.wAs.getD i []) = a := (hwordG hwA).perm_eq ha
    have hB' : wordVal Lg (V.wBs.getD i []) = b := (hwordG hwB).perm_eq hb
    refine ⟨Γ, ?_, ?_, ?_⟩
    · rintro g ⟨j, hj, -, rfl⟩
      exact hLgG _ (hLgmem j hj)
    · rw [hGdef, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | hx
      · rw [← hA']
        exact hall _ hoA
      · rw [Set.mem_singleton_iff] at hx
        rw [hx, ← hB']
        exact hall _ hoB
    · rintro g ⟨j, hj, hok, rfl⟩
      obtain ⟨hidx, hk⟩ := band_e (PK.allN_iff.1 hkall j hj)
      have hidx' : (V.gk.getD j default).idx < V.ys.length := Nat.blt_eq.mp hidx
      have hmemf : V.gk.getD j default ∈ V.gk := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      have hk0 := hkd _ hmemf
      have hf31 := hf3 _ hmemf
      generalize hf : V.gk.getD j default = f at hk hok hidx' hk0 hf31
      unfold kindK at hk
      rw [PK.strictB_eq] at hk
      have hvfP := hvP f.idx hidx'
      have hyP := pr_mul (pr_pow hn hzP f.f1) (pr_pow hn hvfP f.f2)
      have hk' := bif_f (Bool.eq_false_iff.2 fun e => hk0 (Nat.eq_of_beq_eq_true e)) hk
      obtain ⟨e0, hk'⟩ := band_e hk'
      obtain ⟨-, e2⟩ := band_e hk'
      have hc := (pr_beq (pr_mul (hgP j hj) hyP) (pr_mul (pr_pow hn hyP f.f3) (hgP j hj))).1 e2
      rw [hf31, pow_one] at hc
      refine ⟨z ^ f.f1 * v f.idx ^ f.f2, ?_, pr_ne hyP (pr_one hn) e0, hc⟩
      rcases hok with (hk0' | hidx'') | hf2
      · exact absurd hk0' hk0
      · rw [hidx'']
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      · rw [hf2, pow_zero, mul_one]
        exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
  have hstep : ∀ s ∈ steps, P s.src → P s.tgt := by
    intro s hs hP
    have h := H.hsteps s hs
    unfold stepCK at h
    rw [PK.strictB_eq] at h
    obtain ⟨hj, h⟩ := band_e h
    obtain ⟨hsrc, h⟩ := band_e h
    obtain ⟨htgt, h⟩ := band_e h
    obtain ⟨hcz, hcv⟩ := band_e h
    have hj' : s.j < ng := Nat.blt_eq.mp hj
    have hsrc' : s.src < V.ys.length := Nat.blt_eq.mp hsrc
    have htgt' : s.tgt < V.ys.length := Nat.blt_eq.mp htgt
    set g := Lg.getD s.j 1 with hgdef
    have hgG : g ∈ G := hLgG _ (hLgmem _ hj')
    have hgz : g * z = z * g := (pr_beq (pr_mul (hgP _ hj') hzP) (pr_mul hzP (hgP _ hj'))).1 hcz
    have hgv : g * v s.src = (z ^ s.a * v s.tgt ^ s.b) * g :=
      (pr_beq (pr_mul (hgP _ hj') (hvP _ hsrc'))
        (pr_mul (pr_mul (pr_pow hn hzP s.a) (pr_pow hn (hvP _ htgt') s.b)) (hgP _ hj'))).1 hcv
    have hY : ∀ y ∈ Subgroup.closure ({z, v s.src} : Set (Equiv.Perm (Fin n))),
        g * y * g⁻¹ ∈ Subgroup.closure ({z, v s.tgt} : Set (Equiv.Perm (Fin n))) := by
      intro y hy
      refine conj_mem_of_closure (fun t ht => ?_) hy
      rcases ht with rfl | ht
      · rw [hgz, mul_inv_cancel_right]
        exact Subgroup.subset_closure (by simp)
      · rw [Set.mem_singleton_iff] at ht
        rw [ht, hgv, mul_inv_cancel_right]
        exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
          (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    obtain ⟨Γ, hΓG, hGΓ, hΓc⟩ := hP
    refine ⟨(fun x => g * x * g⁻¹) '' Γ, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact G.mul_mem (G.mul_mem hgG (hΓG hx)) (G.inv_mem hgG)
    · intro x hx
      have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ Subgroup.closure Γ :=
        hGΓ (G.mul_mem (G.mul_mem (G.inv_mem hgG) hx) (G.inv_mem (G.inv_mem hgG)))
      have e : x = g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ := by group
      rw [e]
      exact conj_mem_of_closure (fun t ht => Subgroup.subset_closure (Set.mem_image_of_mem _ ht)) hx'
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hyY, hy1, hxy⟩ := hΓc x hx
      refine ⟨g * y * g⁻¹, hY y hyY, fun h1 => hy1 ?_, ?_⟩
      · have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
        rw [e, h1]
        group
      · calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
          _ = g * (y * x) * g⁻¹ := by rw [hxy]
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group
  have hchain : ∀ (l : List CStep) (cov : List Nat), (∀ s ∈ l, s ∈ steps) →
      (∀ i ∈ cov, P i) → chainOK V.ys.length cov l = true → ∀ i < V.ys.length, P i := by
    intro l
    induction l with
    | nil =>
      intro cov _ hcov h i hi
      simp only [chainOK, List.all_eq_true, List.mem_range] at h
      exact hcov i (by simpa using h i hi)
    | cons s r ih =>
      intro cov hl hcov h
      simp only [chainOK, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hsrc : s.src ∈ cov := by simpa using h1
      refine ih (s.tgt :: cov) (fun t ht => hl t (List.mem_cons_of_mem _ ht)) ?_ h2
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact hstep s (hl s List.mem_cons_self) (hcov _ hsrc)
      · exact hcov i hi
  have hallP : ∀ i < V.ys.length, P i :=
    hchain steps reps (fun _ h => h) (fun i hi => (hrep i hi).2) H.hchain
  refine ⟨E, hEc, hEG, ?_⟩
  intro A hAE hAe hAc
  obtain ⟨i, hi, hYA⟩ := eq_line_of_elemAbelian hp hEc hnc hzE hzp' hz1' hzcent hv' hd hAE hAe hAc
  obtain ⟨Γ, hΓG, hGΓ, hΓc⟩ := hallP i (by omega)
  refine ⟨Γ, hΓG, hGΓ, fun g hg => ?_⟩
  obtain ⟨y, hy, hy1, hgy⟩ := hΓc g hg
  exact ⟨y, hYA ▸ hy, hy1, hgy⟩

theorem exists_cent_gens_of_kchecks {n w : Nat} {V : VData} {reps : List Nat}
    {steps : List CStep} {GP GPI GT GTI EG EGI T PL POS SRT SRI : Nat → Nat} {cnt cap len : Nat}
    (H : KHypsC n w V reps steps GP GPI GT GTI EG EGI T PL POS SRT SRI cnt cap len)
    (hp : V.base.p.Prime) (hkd : ∀ f ∈ V.gk, f.kind ≠ 0) (hf3 : ∀ f ∈ V.gk, f.f3 = 1)
    {a b : Equiv.Perm (Fin n)} (ha : TabRep (unpack n w (GP 0)) a)
    (hb : TabRep (unpack n w (GP 1)) b) :
    ∃ E : Subgroup ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))),
      Nat.card E = V.base.p ^ 3 ∧
      ∀ A : Subgroup ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))), A ≤ E →
        IsElemAbelian V.base.p A → Nat.card A = V.base.p ^ 2 →
        ∃ Γ : Set ↥(Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n)))),
          Subgroup.closure Γ = ⊤ ∧ ∀ g ∈ Γ, ∃ y ∈ A, y ≠ 1 ∧ g * y = y * g := by
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  obtain ⟨E, hEc, hEG, hΓ⟩ := cent_facts H hp hkd hf3 ha hb
  refine ⟨E.subgroupOf G, ?_, ?_⟩
  · rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  intro A' hA'E hA'e hA'c
  set A : Subgroup (Equiv.Perm (Fin n)) := A'.map G.subtype with hAdef
  have hAE : A ≤ E := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hA'E hx)
  have hAe : IsElemAbelian V.base.p A := CFSG.SectionRank.isElemAbelian_map hA'e _
  have hAc : Nat.card A = V.base.p ^ 2 := by
    rw [hAdef, Subgroup.card_map_of_injective G.subtype_injective, hA'c]
  obtain ⟨Γ, hΓG, hgen, hcent⟩ := hΓ A hAE hAe hAc
  refine ⟨{g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}, ?_, ?_⟩
  · rw [eq_top_iff]
    intro h _
    have hmap : (Subgroup.closure {g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}).map G.subtype =
        Subgroup.closure Γ := by
      rw [MonoidHom.map_closure]
      congr 1
      ext z
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact hg
      · intro hz
        exact ⟨⟨z, hΓG hz⟩, hz, rfl⟩
    have hle : G ≤ (Subgroup.closure {g : ↥G | (g : Equiv.Perm (Fin n)) ∈ Γ}).map G.subtype := by
      rw [hmap]
      exact hgen
    obtain ⟨k, hk, hkh⟩ := hle h.2
    have : k = h := Subtype.ext hkh
    rwa [← this]
  · intro g hg
    obtain ⟨y, hyA, hy1, h1⟩ := hcent _ hg
    obtain ⟨y', hy'A, rfl⟩ := Subgroup.mem_map.1 hyA
    refine ⟨y', hy'A, fun h0 => hy1 (by rw [h0]; rfl), Subtype.ext (by simpa using h1)⟩

end CFSG.KD.CoreD2K

end
