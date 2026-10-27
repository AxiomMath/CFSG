module

public import Certificates.Data.Kernel.K36K.Check
public import CFSG.Certificates.Kernel.CoreD2K.Sound

public section

namespace CFSG.KD.K36K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.K36K CFSG.KD.CoreD2K
open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
  Certificates.K36Spor

theorem mem_plane {X : Type*} [Group X] (S : SData) (e : ℕ → X) {i : ℕ} {c : Cent}
    (hc : c.idx = i ∨ c.f2 = 0) :
    e 0 ^ c.f1 * e (S.ys.getD c.idx 0) ^ c.f2 ∈
      Subgroup.closure ({e 0, e (S.ys.getD i 0)} : Set X) := by
  rcases hc with rfl | h0
  · exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · rw [h0, pow_zero, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _

theorem allowedS_iff {S : SData} {i j : ℕ} :
    allowedS S i j = true ↔ (S.gc.getD j default).idx = i ∨ (S.gc.getD j default).f2 = 0 := by
  unfold allowedS
  simp only [Bool.or_eq_true, beq_iff_eq]

section Packed

variable {n w : Nat}

theorem pr_pg {p : Nat} {g : Equiv.Perm (Fin n)} (hp : PR n w p g) (x : Fin n) :
    pg w (mask w) p x = (g x : ℕ) := by
  rw [← get_u x.2]
  exact hp.2.apply x

theorem centEK_sound (hn : szOK n w = true) {z v g f1 f2 : Nat} {zz vv gg : Equiv.Perm (Fin n)}
    (hz : PR n w z zz) (hv : PR n w v vv) (hg : PR n w g gg) (h : centEK n w z v g f1 f2 = true) :
    zz ^ f1 * vv ^ f2 ≠ 1 ∧ (zz ^ f1 * vv ^ f2) * gg = gg * (zz ^ f1 * vv ^ f2) := by
  unfold centEK at h
  rw [PK.strictB_eq] at h
  obtain ⟨h1, h2⟩ := band_e h
  have hy := pr_mul (pr_pow hn hz f1) (pr_pow hn hv f2)
  exact ⟨pr_ne hy (pr_one hn) h1, ((pr_beq (pr_mul hg hy) (pr_mul hy hg)).1 h2).symm⟩

theorem centCK_sound (hn : szOK n w = true) {S : SData} {EG : ℕ → ℕ} {e : ℕ → Equiv.Perm (Fin n)}
    (he : ∀ k < S.base.eW.length, PR n w (EG k) (e k)) {c : Cent} {g : Nat}
    {gg : Equiv.Perm (Fin n)} (hg : PR n w g gg) (h : centCK n w S EG c g = true) :
    c.idx < S.ys.length ∧ e 0 ^ c.f1 * e (S.ys.getD c.idx 0) ^ c.f2 ≠ 1 ∧
      (e 0 ^ c.f1 * e (S.ys.getD c.idx 0) ^ c.f2) * gg =
        gg * (e 0 ^ c.f1 * e (S.ys.getD c.idx 0) ^ c.f2) := by
  unfold centCK at h
  obtain ⟨h1, h⟩ := band_e h
  obtain ⟨h2, h3⟩ := band_e h
  have h2' : S.ys.getD c.idx 0 < S.base.eW.length := Nat.blt_eq.mp h2
  exact ⟨Nat.blt_eq.mp h1, centEK_sound hn (he 0 (by omega)) (he _ h2') hg h3⟩

theorem gen_sound (hn : szOK n w = true) {S : SData} {GP GT GTI EG : ℕ → ℕ}
    {e : ℕ → Equiv.Perm (Fin n)} {L : List (Equiv.Perm (Fin n))} {a b : Equiv.Perm (Fin n)}
    (he : ∀ k < S.base.eW.length, PR n w (EG k) (e k)) (hL : L.length = S.base.gWs.length)
    (hGT : allN S.base.gWs.length (fun j => permOK n w (mask w) (n * w) (GT j) (GTI j)) = true)
    (hgP : ∀ j < S.base.gWs.length, PR n w (GT j) (L.getD j 1))
    (ha : TabRep (unpack n w (GP 0)) a) (hb : TabRep (unpack n w (GP 1)) b)
    (hcent : centSK n w S EG GT = true) (hwords : wordsSK n w S GP GT GTI = true) :
    ∀ k < S.gen.length, ∃ Γ : Set (Equiv.Perm (Fin n)), Γ ⊆ {g | g ∈ L} ∧
      ({a, b} : Set (Equiv.Perm (Fin n))) ⊆ Subgroup.closure Γ ∧ ∀ g ∈ Γ,
        ∃ u ∈ Subgroup.closure ({e 0, e (S.ys.getD (S.gen.getD k 0) 0)} :
          Set (Equiv.Perm (Fin n))), u ≠ 1 ∧ u * g = g * u := by
  intro k hk
  set i := S.gen.getD k 0 with hi
  set ng := S.base.gWs.length with hng
  have hwordG : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GT GTI ng wd r = true → TabRep (unpack n w r) (wordVal L wd) :=
    fun h => pr_word hL hGT (fun j hj => (hgP j hj).2) h
  unfold centSK at hcent
  obtain ⟨-, hcall⟩ := band_e hcent
  unfold wordsSK at hwords
  obtain ⟨hwA, hw⟩ := band_e (PK.allN_iff.1 hwords k hk)
  obtain ⟨hwB, hw⟩ := band_e hw
  obtain ⟨hoA, hoB⟩ := band_e hw
  set Γ : Set (Equiv.Perm (Fin n)) := {g | ∃ j < ng, allowedS S i j = true ∧ g = L.getD j 1}
    with hΓdef
  have hall : ∀ wd : List Int, wd.all (fun l => allowedS S i (l.natAbs - 1)) = true →
      wordVal L wd ∈ Subgroup.closure Γ := by
    intro wd hw
    rw [List.all_eq_true] at hw
    refine CFSG.AGLEmbedding.CoreD2.wordVal_mem_of L _ wd fun l hl => ?_
    by_cases hlt : l.natAbs - 1 < ng
    · exact Subgroup.subset_closure ⟨_, hlt, hw l hl, rfl⟩
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Subgroup.one_mem _
  have hA' : wordVal L (S.wAs.getD k []) = a := (hwordG hwA).perm_eq ha
  have hB' : wordVal L (S.wBs.getD k []) = b := (hwordG hwB).perm_eq hb
  refine ⟨Γ, ?_, ?_, ?_⟩
  · rintro g ⟨j, hj, -, rfl⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro x hx
    rcases hx with rfl | hx
    · rw [← hA']
      exact hall _ hoA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, ← hB']
      exact hall _ hoB
  · rintro g ⟨j, hj, hok, rfl⟩
    obtain ⟨-, hne, hcomm⟩ := centCK_sound hn he (hgP j hj) (PK.allN_iff.1 hcall j hj)
    exact ⟨_, mem_plane S e (allowedS_iff.1 hok), hne, hcomm⟩

theorem cyT_lt {m : Nat} {CT : Nat → Nat} {y j : Nat} (hj : j < m) : cyT m CT y j = CT j := by
  unfold cyT
  rw [Nat.blt_eq.mpr hj]

theorem cyT_self {m : Nat} {CT : Nat → Nat} {y : Nat} : cyT m CT y m = y := by
  have e : Nat.blt m m = false :=
    Bool.eq_false_iff.2 fun h => absurd (Nat.blt_eq.mp h) (Nat.lt_irrefl m)
  unfold cyT
  rw [e]

theorem exc_sound (hn : szOK n w = true) {S : SData} {X : Exc} {EG GP GPI CT CTI : ℕ → ℕ}
    {YT YTI : ℕ} {FT FYT : ℕ → ℕ} {e : ℕ → Equiv.Perm (Fin n)} {a b : Equiv.Perm (Fin n)}
    (he : ∀ k < S.base.eW.length, PR n w (EG k) (e k))
    (hGP : allN 2 (fun j => permOK n w (mask w) (n * w) (GP j) (GPI j)) = true)
    (ha : TabRep (unpack n w (GP 0)) a) (hb : TabRep (unpack n w (GP 1)) b)
    (h : excWK n w S X EG GP GPI CT CTI YT YTI FT FYT = true) :
    ∃ (cs : List (Equiv.Perm (Fin n))) (y : Equiv.Perm (Fin n)) (f f' : ℕ → Equiv.Perm (Fin n)),
      cs.length = X.cW.length ∧ (∀ l < X.cW.length, PR n w (CT l) (cs.getD l 1)) ∧
      (∀ c ∈ cs, c ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) ∧
        ∃ u ∈ Subgroup.closure ({e 0, e (S.ys.getD X.idx 0)} : Set (Equiv.Perm (Fin n))),
          u ≠ 1 ∧ u * c = c * u) ∧
      y ∈ Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) ∧
      (∀ k < 2, f k ∈ Subgroup.closure {c | c ∈ cs} ∧ f' k ∈ Subgroup.closure {c | c ∈ cs} ∧
        y * f k = f' k * y ∧ PR n w (FT k) (f k)) ∧
      a ∈ Subgroup.closure ({c | c ∈ cs} ∪ {y}) ∧ b ∈ Subgroup.closure ({c | c ∈ cs} ∪ {y}) := by
  set G := Subgroup.closure ({a, b} : Set (Equiv.Perm (Fin n))) with hGdef
  set Sab : List (Equiv.Perm (Fin n)) := [a, b] with hSdef
  have hSr : ∀ j < 2, TabRep (unpack n w (GP j)) (Sab.getD j 1) := by
    intro j hj
    rcases j with _ | _ | j
    · exact ha
    · exact hb
    · omega
  have hword : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) GP GPI 2 wd r = true →
        TabRep (unpack n w r) (wordVal Sab wd) :=
    fun h => pr_word (k := 2) rfl hGP hSr h
  have hSG : ∀ g ∈ Sab, g ∈ G := by
    intro g hg
    simp only [hSdef, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
  unfold excWK at h
  obtain ⟨-, h⟩ := band_e h
  obtain ⟨hcall, h⟩ := band_e h
  obtain ⟨hyW, h⟩ := band_e h
  obtain ⟨hyp, h⟩ := band_e h
  obtain ⟨hfall, h⟩ := band_e h
  obtain ⟨hwA, hwB⟩ := band_e h
  set m := X.cW.length with hm
  set cs : List (Equiv.Perm (Fin n)) := X.cW.map (wordVal Sab) with hcsdef
  have hcslen : cs.length = m := by simp [hcsdef, hm]
  have hcsget : ∀ l < m, cs.getD l 1 = wordVal Sab (X.cW.getD l []) := fun l hl => by
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hl, List.getElem_map]
  have hC : ∀ l < m, wordEqK n w (mask w) (pidn n w) GP GPI 2 (X.cW.getD l []) (CT l) = true ∧
      permOK n w (mask w) (n * w) (CT l) (CTI l) = true ∧ (X.cc.getD l default).idx = X.idx ∧
      centCK n w S EG (X.cc.getD l default) (CT l) = true := fun l hl => by
    obtain ⟨h1, h⟩ := band_e (PK.allN_iff.1 hcall l hl)
    obtain ⟨h2, h⟩ := band_e h
    obtain ⟨h3, h4⟩ := band_e h
    exact ⟨h1, h2, Nat.eq_of_beq_eq_true h3, h4⟩
  have hcP : ∀ l < m, PR n w (CT l) (cs.getD l 1) := fun l hl =>
    ⟨(perm_canon (hC l hl).2.1 hn).1, by rw [hcsget l hl]; exact hword (hC l hl).1⟩
  have hCTp : allN m (fun j => permOK n w (mask w) (n * w) (CT j) (CTI j)) = true :=
    PK.allN_iff.2 fun j hj => (hC j hj).2.1
  have hwordC : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) CT CTI m wd r = true → TabRep (unpack n w r) (wordVal cs wd) :=
    fun h => pr_word hcslen hCTp (fun j hj => (hcP j hj).2) h
  set y := wordVal Sab X.yW with hydef
  have hyP : PR n w YT y := ⟨(perm_canon hyp hn).1, hword hyW⟩
  set f : ℕ → Equiv.Perm (Fin n) := fun k => wordVal cs (X.fWc.getD k []) with hfdef
  set f' : ℕ → Equiv.Perm (Fin n) := fun k => wordVal cs (X.fyWc.getD k []) with hf'def
  set Lcy : List (Equiv.Perm (Fin n)) := cs ++ [y] with hLcy
  have hLcylen : Lcy.length = m + 1 := by simp [hLcy, hcslen]
  have hcyp : allN (m + 1) (fun j => permOK n w (mask w) (n * w) (cyT m CT YT j)
      (cyT m CTI YTI j)) = true := by
    refine PK.allN_iff.2 fun j hj => ?_
    by_cases hjm : j < m
    · rw [cyT_lt hjm, cyT_lt hjm]
      exact (hC j hjm).2.1
    · have e : j = m := by omega
      subst e
      rw [cyT_self, cyT_self]
      exact hyp
  have hcyr : ∀ j < m + 1, TabRep (unpack n w (cyT m CT YT j)) (Lcy.getD j 1) := by
    intro j hj
    by_cases hjm : j < m
    · rw [cyT_lt hjm, hLcy, List.getD_append _ _ _ _ (by omega)]
      exact (hcP j hjm).2
    · have e : j = m := by omega
      subst e
      rw [cyT_self, hLcy, List.getD_append_right _ _ _ _ (by omega), hcslen, Nat.sub_self]
      exact hyP.2
  have hwordY : ∀ {wd : List Int} {r : Nat},
      wordEqK n w (mask w) (pidn n w) (cyT m CT YT) (cyT m CTI YTI) (m + 1) wd r = true →
        TabRep (unpack n w r) (wordVal Lcy wd) :=
    fun h => pr_word hLcylen hcyp hcyr h
  have hLcyH : ∀ g ∈ Lcy, g ∈ Subgroup.closure ({c | c ∈ cs} ∪ {y}) := by
    intro g hg
    refine Subgroup.subset_closure ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact Or.inl hg
    · exact Or.inr (by simpa using hg)
  have hA' : wordVal Lcy X.wA = a := (hwordY hwA).perm_eq ha
  have hB' : wordVal Lcy X.wB = b := (hwordY hwB).perm_eq hb
  refine ⟨cs, y, f, f', hcslen, hcP, ?_, wordVal_mem Sab G hSG _, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨wd, hwd, rfl⟩ := List.mem_map.1 hc
    refine ⟨wordVal_mem Sab G hSG wd, ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hwd
    obtain ⟨-, -, hidx, hcent⟩ := hC l hl
    have hP := hcP l hl
    rw [hcsget l hl, List.getD_eq_getElem _ _ hl] at hP
    obtain ⟨-, hne, hcomm⟩ := centCK_sound hn he hP hcent
    exact ⟨_, mem_plane S e (Or.inl hidx), hne, hcomm⟩
  · intro k hk
    obtain ⟨hf, h⟩ := band_e (PK.allN_iff.1 hfall k hk)
    obtain ⟨hf', h⟩ := band_e h
    obtain ⟨hcf, h⟩ := band_e h
    obtain ⟨hcf', heq⟩ := band_e h
    have hfP : PR n w (FT k) (f k) := ⟨hcf, hwordC hf⟩
    have hf'P : PR n w (FYT k) (f' k) := ⟨hcf', hwordC hf'⟩
    exact ⟨wordVal_mem cs _ (fun g hg => Subgroup.subset_closure hg) _,
      wordVal_mem cs _ (fun g hg => Subgroup.subset_closure hg) _,
      (pr_beq (pr_mul hyP hfP) (pr_mul hf'P hyP)).1 heq, hfP⟩
  · rw [← hA']
    exact wordVal_mem Lcy _ hLcyH _
  · rw [← hB']
    exact wordVal_mem Lcy _ hLcyH _

theorem ltsK_cons {k j : Nat} {wd : List Nat} :
    ltsK k (j :: wd) = bAnd(Nat.blt j k, ltsK k wd) := rfl

theorem wptK_cons {F : Nat → Nat} {j x : Nat} {wd : List Nat} :
    wptK w F (j :: wd) x = pg w (mask w) (F j) (wptK w F wd x) := by
  change strictN (wptK w F wd x) (fun y => pg w (mask w) (F j) y) = _
  rw [PK.strictN_eq]

theorem wptK_eq {kF : Nat} {F : Nat → Nat} {f : ℕ → Equiv.Perm (Fin n)}
    (hF : ∀ k < kF, PR n w (F k) (f k)) :
    ∀ wd : List Nat, ltsK kF wd = true →
      (∀ j ∈ wd, j < kF) ∧ ∀ x : Fin n, wptK w F wd x = ((wd.map f).prod x : ℕ)
  | [], _ => ⟨by simp, fun x => rfl⟩
  | j :: wd, h => by
    rw [ltsK_cons] at h
    obtain ⟨hj, h⟩ := band_e h
    have hj' : j < kF := Nat.blt_eq.mp hj
    obtain ⟨hl, hx⟩ := wptK_eq hF wd h
    refine ⟨fun i hi => ?_, fun x => ?_⟩
    · rcases List.mem_cons.1 hi with rfl | hi
      · exact hj'
      · exact hl i hi
    · rw [wptK_cons, hx x, pr_pg (hF j hj') ((wd.map f).prod x)]
      simp [Equiv.Perm.mul_apply]

theorem fixWK_sound {kF k0 o0 : Nat} {F : Nat → Nat} {f : ℕ → Equiv.Perm (Fin n)}
    {HW : List (List Nat)} {OL : List Nat} {OW : List (List Nat)}
    (hF : ∀ k < kF, PR n w (F k) (f k)) (h : fixWK n w kF F k0 o0 HW OL OW = true)
    (t : Equiv.Perm (Fin n)) (ht : ∀ k < kF, t * f k = f k * t) :
    ∀ x : Fin n, (x : ℕ) ∈ OL → t x = x := by
  unfold fixWK at h
  obtain ⟨ho, h⟩ := band_e h
  obtain ⟨hk0, h⟩ := band_e h
  obtain ⟨hmv, h⟩ := band_e h
  obtain ⟨hpts, h⟩ := band_e h
  obtain ⟨-, hOL⟩ := band_e h
  have ho' : o0 < n := Nat.blt_eq.mp ho
  have hk0' : k0 < kF := Nat.blt_eq.mp hk0
  set o : Fin n := ⟨o0, ho'⟩ with hodef
  have hcomm : ∀ wd : List Nat, (∀ j ∈ wd, j < kF) → ∀ x : Fin n,
      t ((wd.map f).prod x) = (wd.map f).prod (t x) := by
    intro wd hwd x
    have hc : Commute t (wd.map f).prod := by
      refine Commute.list_prod_right _ _ fun g hg => ?_
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      exact ht j (hwd j hj)
    have := congrArg (fun g : Equiv.Perm (Fin n) => g x) hc.eq
    simpa [Equiv.Perm.mul_apply] using this
  have hmv' : f k0 o ≠ o := by
    intro e
    have e' := congrArg Fin.val e
    rw [← pr_pg (hF k0 hk0') o] at e'
    have e'' : pg w (mask w) (F k0) o0 = o0 := e'
    have hb := bnot_e hmv
    rw [e'', Nat.beq_refl] at hb
    exact absurd hb (by decide)
  have hto : t o = o := by
    by_contra hne
    set q := t o with hqdef
    have hq : (q : ℕ) ≠ o0 := fun e => hne (Fin.ext e)
    have hP := PK.allN_iff.1 hpts q q.2
    have hP' := bif_f (Bool.eq_false_iff.2 fun e => hq (Nat.eq_of_beq_eq_true e)) hP
    generalize hwd : HW.getD q [] = wd at hP'
    cases wd with
    | nil =>
      have hP'' : allN kF (fun k => Nat.beq (pg w (mask w) (F k) q) q) = true := hP'
      have h1 := Nat.eq_of_beq_eq_true (PK.allN_iff.1 hP'' k0 hk0')
      rw [pr_pg (hF k0 hk0') q] at h1
      have e1 : f k0 q = q := Fin.ext h1
      have e2 : f k0 q = t (f k0 o) := by
        have := congrArg (fun g : Equiv.Perm (Fin n) => g o) (ht k0 hk0')
        simpa [Equiv.Perm.mul_apply, hqdef] using this.symm
      exact hmv' (t.injective (by rw [← e2, e1]))
    | cons j rest =>
      have hP'' : bAnd(ltsK kF (j :: rest), bAnd(Nat.beq (wptK w F (j :: rest) o0) o0,
          bIf(Nat.beq (wptK w F (j :: rest) q) q, false, true))) = true := hP'
      obtain ⟨hl, hP''⟩ := band_e hP''
      obtain ⟨hfix, hmove⟩ := band_e hP''
      obtain ⟨hlt, hx⟩ := wptK_eq hF _ hl
      have hPo : ((j :: rest).map f).prod o = o := by
        apply Fin.ext
        rw [← hx o]
        exact Nat.eq_of_beq_eq_true hfix
      have hPq : ((j :: rest).map f).prod q ≠ q := by
        intro e
        have e' := congrArg Fin.val e
        rw [← hx q] at e'
        rw [e', Nat.beq_refl] at hmove
        exact absurd hmove (by decide)
      apply hPq
      rw [hqdef, ← hcomm _ hlt o, hPo]
  intro x hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨hl, heq⟩ := band_e (PK.allN_iff.1 hOL i hi)
  obtain ⟨hlt, hwx⟩ := wptK_eq hF _ hl
  have hPo : ((OW.getD i []).map f).prod o = x := by
    apply Fin.ext
    rw [← hwx o, Nat.eq_of_beq_eq_true heq, List.getD_eq_getElem _ _ hi, hix]
  rw [← hPo, hcomm _ hlt o, hto]

end Packed

end CFSG.KD.K36K

end
