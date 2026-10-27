module

public import Certificates.Data.Kernel.SlpClsPc
public import CFSG.Certificates.Kernel.SlpClsSound
public import CFSG.Certificates.Kernel.SporCov.PcCl

public section

namespace CFSG.KS.SlpPc

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.SlpPc CFSG.KS.SlpCls
open CFSG CFSG.StandardType CFSG.Assembly CFSG.StandardType.SporadicShape
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

@[expose] def hsR {M : Type} (R : ℕ → M) (sg : List ℕ) : Fin 6 → M := fun i => R (sg.getD i.val 0)

structure ClsPcFacts {q d : ℕ} (MA MB Xg : Mat q d) (rx : ℕ) (sg : List ℕ) (es : List (List ℕ))
    (R : ℕ → Mat q d) : Prop where
  reg : ∀ r, R r ∈ Submonoid.closure ({MA, MB} : Set (Mat q d))
  pow : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ hsR R sg i ^ 5 = nfP (hsR R sg) e
  conj : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
    hsR R sg j * hsR R sg i = hsR R sg i * nfP (hsR R sg) e
  ne : R rx ≠ 1
  pow5 : R rx ^ 5 = 1
  rep : R rx = Xg
  ent : ∀ e ∈ es, R rx * R (e.getD 6 0) = R (e.getD 6 0) * nfP (hsR R sg) (ex e) ∧
    ∀ z ∈ e.drop 7, R z * nfP (hsR R sg) (ex e) = nfP (hsR R sg) (ex e) * R z
  seeds : MA ∈ Submonoid.closure (Set.range (hsR R sg) ∪ {Y | ∃ z ∈ es.flatMap (·.drop 7), Y = R z}) ∧
    MB ∈ Submonoid.closure (Set.range (hsR R sg) ∪ {Y | ∃ z ∈ es.flatMap (·.drop 7), Y = R z})

theorem scp_beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

@[expose] noncomputable def scpPw (mul : ℕ → ℕ → ℕ) (ONE h : ℕ) : List ℕ :=
  [ONE, h, mul h h, mul (mul h h) h, mul (mul (mul h h) h) h, mul (mul (mul (mul h h) h) h) h]

theorem scp_pows (mul : ℕ → ℕ → ℕ) (ONE : ℕ) : ∀ (hs : List ℕ) (k : List (List ℕ) → Bool),
    pows mul ONE hs k = k (hs.map (scpPw mul ONE))
  | [], _ => rfl
  | h :: hs, k => by
    have e : pows mul ONE (h :: hs) k = sB (mul h h) fun h2 => sB (mul h2 h) fun h3 =>
        sB (mul h3 h) fun h4 => sB (mul h4 h) fun h5 =>
          pows mul ONE hs fun ps => k ([ONE, h, h2, h3, h4, h5] :: ps) := rfl
    rw [e]
    simp only [slc_sB, scp_pows mul ONE hs, List.map_cons]
    rfl

theorem scp_dropN : ∀ (n : ℕ) (l : List ℕ), dropN n l = l.drop n
  | 0, _ => rfl
  | n + 1, l => by
    have e : dropN (n + 1) l = tl (dropN n l) := rfl
    rw [e, scp_dropN n l, List.drop_add_one_eq_tail_drop]
    cases l.drop n <;> rfl

theorem scp_zsOf : ∀ es : List (List ℕ), zsOf es = es.flatMap (·.drop 7)
  | [] => rfl
  | e :: es => by
    have h : zsOf (e :: es) = revOnto (revOnto (dropN 7 e) []) (zsOf es) := rfl
    rw [h, slc_revOnto, slc_revOnto, scp_zsOf es, scp_dropN]
    simp

theorem scp_ltUpTo {a : List ℕ} {b : ℕ} : ∀ n, ltUpTo a b n = true → ∀ t < n, a.getD t 0 < b
  | 0, _, t, ht => absurd ht (by omega)
  | n + 1, h, t, ht => by
    have e : ltUpTo a b (n + 1) = andB (Nat.blt (nthD 0 a n) b) (ltUpTo a b n) := rfl
    rw [e, slc_and, slc_nthD, Nat.blt_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact scp_ltUpTo n h.2 t ht
    · exact h.1

theorem scp_zeroUpTo {a : List ℕ} : ∀ n, zeroUpTo a n = true → ∀ t < n, a.getD t 0 = 0
  | 0, _, t, ht => absurd ht (by omega)
  | n + 1, h, t, ht => by
    have e : zeroUpTo a (n + 1) = andB (Nat.beq (nthD 0 a n) 0) (zeroUpTo a n) := rfl
    rw [e, slc_and, slc_nthD] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact scp_zeroUpTo n h.2 t ht
    · exact Nat.eq_of_beq_eq_true h.1

theorem scp_pw {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    {h : ℕ} (hh : P h) : ∀ e ≤ 5, P ((scpPw mul ONE h).getD e 0) ∧
      OM ((scpPw mul ONE h).getD e 0) = OM h ^ e := by
  obtain ⟨c2, m2⟩ := hm _ _ hh hh
  obtain ⟨c3, m3⟩ := hm _ _ c2 hh
  obtain ⟨c4, m4⟩ := hm _ _ c3 hh
  obtain ⟨c5, m5⟩ := hm _ _ c4 hh
  intro e he
  interval_cases e
  · exact ⟨h1.1, by rw [pow_zero]; exact h1.2⟩
  · exact ⟨hh, (pow_one _).symm⟩
  · exact ⟨c2, m2.trans (pow_two _).symm⟩
  · exact ⟨c3, m3.trans (by rw [m2, pow_succ, pow_two])⟩
  · exact ⟨c4, m4.trans (by rw [m3, m2, pow_succ, pow_succ, pow_two])⟩
  · exact ⟨c5, m5.trans (by rw [m4, m3, m2, pow_succ, pow_succ, pow_succ, pow_two])⟩

@[expose] noncomputable def scpProd {M : Type} [Monoid M] (OM : ℕ → M) : List ℕ → List ℕ → M
  | [], _ => 1
  | h :: hl, a => OM h ^ a.getD 0 0 * scpProd OM hl (tl a)

theorem scp_prod_map {M : Type} [Monoid M] (OM : ℕ → M) (f : ℕ → ℕ) :
    ∀ (l a : List ℕ), scpProd OM (l.map f) a = scpProd (fun x => OM (f x)) l a
  | [], _ => rfl
  | h :: l, a => by
    simp only [List.map_cons, scpProd]
    rw [scp_prod_map OM f l]

theorem scp_prod_nfP {M : Type} [Monoid M] (R : ℕ → M) (sg : List ℕ) (hlen : sg.length = 6)
    (e : List ℕ) : scpProd (fun s => R s) sg e = nfP (hsR R sg) (ex e) := by
  match sg, hlen with
  | [s0, s1, s2, s3, s4, s5], _ =>
    simp only [scpProd, nfP, hsR, ex, slc_tl, mul_assoc, mul_one]
    rfl

@[expose] def scpInv {M : Type} [Monoid M] (OM : ℕ → M) (P : ℕ → Prop) (acc : ℕ) (X : M) : Prop :=
  (acc = 0 ∧ X = 1) ∨ (P acc ∧ OM acc = X)

theorem scp_nfGo {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    (hz : ∀ x, P x → x ≠ 0) : ∀ (hl : List ℕ) (a : List ℕ) (acc : ℕ) (X : M),
      (∀ h ∈ hl, P h) → (∀ t < hl.length, a.getD t 0 ≤ 5) → scpInv OM P acc X →
      scpInv OM P (nfGo mul (hl.map (scpPw mul ONE)) a acc) (X * scpProd OM hl a)
  | [], _, acc, X, _, _, hI => by
    rw [scpProd, mul_one]
    exact hI
  | h :: hl, a, acc, X, hP, ha, hI => by
    have e : nfGo mul ((h :: hl).map (scpPw mul ONE)) a acc =
        CFSG.KC.Loop.strictN (Bool.rec (motive := fun _ => ℕ)
          (Bool.rec (motive := fun _ => ℕ) (mul acc (nthD 0 (scpPw mul ONE h) (nthD 0 a 0)))
            (nthD 0 (scpPw mul ONE h) (nthD 0 a 0)) (Nat.beq acc 0))
          acc (Nat.beq (nthD 0 a 0) 0)) (nfGo mul (hl.map (scpPw mul ONE)) (tl a)) := rfl
    rw [e, slc_strictN, slc_nthD, slc_nthD]
    have hpw := scp_pw hm h1 (hP h List.mem_cons_self) (a.getD 0 0) (ha 0 (by simp))
    have ih := scp_nfGo hm h1 hz hl (tl a)
    have hP' : ∀ h ∈ hl, P h := fun h' hh' => hP h' (List.mem_cons_of_mem _ hh')
    have ha' : ∀ t < hl.length, (tl a).getD t 0 ≤ 5 := fun t ht => by
      rw [slc_tl]
      exact ha (t + 1) (by simp; omega)
    have hassoc : X * scpProd OM (h :: hl) a = X * OM h ^ a.getD 0 0 * scpProd OM hl (tl a) := by
      rw [scpProd, mul_assoc]
    rw [hassoc]
    refine ih _ _ hP' ha' ?_
    by_cases he : a.getD 0 0 = 0
    · have hb : Nat.beq (a.getD 0 0) 0 = true := by rw [he]; rfl
      rw [hb, he, pow_zero, mul_one]
      exact hI
    · rw [scp_beq_false he]
      rcases hI with ⟨rfl, rfl⟩ | ⟨hPa, hOa⟩
      · right
        exact ⟨hpw.1, hpw.2.trans (one_mul _).symm⟩
      · rw [scp_beq_false (hz acc hPa)]
        obtain ⟨c, m⟩ := hm _ _ hPa hpw.1
        right
        exact ⟨c, m.trans (by rw [hOa, hpw.2])⟩

theorem scp_nfM {M : Type} [Monoid M] {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {OM : ℕ → M} {P : ℕ → Prop}
    (hm : ∀ a b, P a → P b → P (mul a b) ∧ OM (mul a b) = OM a * OM b) (h1 : P ONE ∧ OM ONE = 1)
    (hz : ∀ x, P x → x ≠ 0) (hl a : List ℕ) (hP : ∀ h ∈ hl, P h)
    (ha : ∀ t < hl.length, a.getD t 0 ≤ 5) :
    P (nfM mul ONE (hl.map (scpPw mul ONE)) a) ∧
      OM (nfM mul ONE (hl.map (scpPw mul ONE)) a) = scpProd OM hl a := by
  have hI := scp_nfGo hm h1 hz hl a 0 1 hP ha (Or.inl ⟨rfl, rfl⟩)
  rw [one_mul] at hI
  have e : nfM mul ONE (hl.map (scpPw mul ONE)) a =
      Bool.rec (motive := fun _ => ℕ) (nfGo mul (hl.map (scpPw mul ONE)) a 0) ONE
        (Nat.beq (nfGo mul (hl.map (scpPw mul ONE)) a 0) 0) := rfl
  rw [e]
  rcases hI with ⟨h0, hX⟩ | ⟨hPr, hOr⟩
  · rw [h0]
    exact ⟨h1.1, h1.2.trans hX.symm⟩
  · rw [scp_beq_false (hz _ hPr)]
    exact ⟨hPr, hOr⟩

theorem scp_relOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {hs : List ℕ} {pw : List (List ℕ)} {i j : ℕ}
    {e : List ℕ} (h : CFSG.KC.SlpPc.relOK mul ONE hs pw i j e = true) :
    (∀ t < 6, e.getD t 0 < 5) ∧ (∀ t ≤ i, e.getD t 0 = 0) ∧
      (i = j → (pw.getD i []).getD 5 0 = nfM mul ONE pw e) ∧
      (i ≠ j → mul (hs.getD j 0) (hs.getD i 0) = mul (hs.getD i 0) (nfM mul ONE pw e)) := by
  unfold CFSG.KC.SlpPc.relOK at h
  rw [slc_and, slc_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨scp_ltUpTo 6 h1, fun t ht => scp_zeroUpTo (i + 1) h2 t (by omega), fun hij => ?_,
    fun hij => ?_⟩
  · subst hij
    rw [Nat.beq_refl] at h3
    have := Nat.eq_of_beq_eq_true h3
    rwa [slc_nthD, slc_nthD] at this
  · rw [scp_beq_false hij] at h3
    have := Nat.eq_of_beq_eq_true h3
    rwa [slc_nthD, slc_nthD] at this

theorem scp_relsOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {hs : List ℕ} {pw : List (List ℕ)} :
    ∀ (rel : List (List ℕ)) (i j : ℕ), relsOK mul ONE hs pw rel i j = true →
      ∀ i' j', i' ≤ j' → j' < 6 → (i < i' ∨ (i = i' ∧ j ≤ j')) →
        ∃ r ∈ rel, CFSG.KC.SlpPc.relOK mul ONE hs pw i' j' (tl (tl r)) = true
  | [], i, j, h, i', j', h1, h2, h3 => by
    have e : relsOK mul ONE hs pw [] i j = Nat.beq i 6 := rfl
    rw [e] at h
    have := Nat.eq_of_beq_eq_true h
    omega
  | r :: rel, i, j, h, i', j', h1, h2, h3 => by
    have e : relsOK mul ONE hs pw (r :: rel) i j = andB (Nat.beq (nthD 0 r 0) i)
        (andB (Nat.beq (nthD 0 r 1) j) (andB (CFSG.KC.SlpPc.relOK mul ONE hs pw i j (tl (tl r)))
          (Bool.rec (motive := fun _ => Bool) (relsOK mul ONE hs pw rel i (Nat.succ j))
            (relsOK mul ONE hs pw rel (Nat.succ i) (Nat.succ i)) (Nat.beq j 5)))) := rfl
    rw [e, slc_and, slc_and, slc_and] at h
    obtain ⟨-, -, hr, hn⟩ := h
    by_cases hij : i = i' ∧ j = j'
    · obtain ⟨rfl, rfl⟩ := hij
      exact ⟨r, List.mem_cons_self, hr⟩
    by_cases hj5 : j = 5
    · rw [hj5, Nat.beq_refl] at hn
      obtain ⟨r', hr', h'⟩ := scp_relsOK rel _ _ hn i' j' h1 h2 (by omega)
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩
    · rw [scp_beq_false hj5] at hn
      obtain ⟨r', hr', h'⟩ := scp_relsOK rel _ _ hn i' j' h1 h2 (by omega)
      exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem scp_entOK {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)} {X : ℕ}
    {e : List ℕ} (h : entOK mul ONE R pw X e = true) :
    (∀ t < 6, e.getD t 0 < 5) ∧ mul X (R (e.getD 6 0)) = mul (R (e.getD 6 0)) (nfM mul ONE pw e) ∧
      commOK mul R (nfM mul ONE pw e) (e.drop 7) = true := by
  unfold entOK at h
  simp only [slc_and, slc_sB, slc_nthD, scp_dropN] at h
  exact ⟨scp_ltUpTo 6 h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

theorem scp_ents {mul : ℕ → ℕ → ℕ} {ONE : ℕ} {R : ℕ → ℕ} {pw : List (List ℕ)} {X : ℕ} :
    ∀ es : List (List ℕ), List.rec (motive := fun _ => Bool) true
      (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es = true →
      ∀ e ∈ es, entOK mul ONE R pw X e = true
  | [], _, e, he => absurd he List.not_mem_nil
  | e :: es, h, e', he' => by
    have eq : List.rec (motive := fun _ => Bool) true
        (fun e _ ih => andB (entOK mul ONE R pw X e) ih) (e :: es) =
        andB (entOK mul ONE R pw X e) (List.rec (motive := fun _ => Bool) true
          (fun e _ ih => andB (entOK mul ONE R pw X e) ih) es) := rfl
    rw [eq, slc_and] at h
    rcases List.mem_cons.1 he' with rfl | he'
    · exact h.1
    · exact scp_ents es h.2 e' he'

theorem clsPc_sound {q w S d T L H CM RM ONE LV HV A B Xg : ℕ}
    (hc : constsOK q w S d T L H CM RM ONE LV HV = true) (hd : 0 < d) (hq : 1 < q)
    (hA : Canon q d w A) (hB : Canon q d w B) (hAu : IsUnit (ordMat q d w S A))
    (hBu : IsUnit (ordMat q d w S B)) {prg : List (ℕ × ℕ)} {rx : ℕ} {sg : List ℕ}
    {rel es : List (List ℕ)} {lp : List (ℕ × ℕ)} {ab : List ℕ}
    (h : clsPc (mulR q w S d T L H CM RM) ONE A B Xg prg rx sg rel es lp ab = true) :
    ∃ R, ClsPcFacts (ordMat q d w S A) (ordMat q d w S B) (ordMat q d w S Xg) rx sg es R := by
  have hS : S = d * w := by
    unfold constsOK at hc
    rw [slc_and, slc_and] at hc
    exact Nat.eq_of_beq_eq_true hc.2.1
  have hq1 : Fact (1 < q) := ⟨hq⟩
  have hone := one_sound hc
  have hmulC : ∀ a b, Canon q d w a → Canon q d w b →
      Canon q d w (mulR q w S d T L H CM RM a b) ∧ ordMat q d w S (mulR q w S d T L H CM RM a b) =
        ordMat q d w S a * ordMat q d w S b := fun a b ha hb => mulR_sound hc ha hb
  let P : ℕ → Prop := fun x => Canon q d w x ∧
    ordMat q d w S x ∈ Submonoid.closure ({ordMat q d w S A, ordMat q d w S B} : Set (Mat q d))
  have hP1 : P ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
  have hPm : ∀ a b, P a → P b → P (mulR q w S d T L H CM RM a b) := fun a b ha hb =>
    ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
  have hPmul : ∀ a b, P a → P b → P (mulR q w S d T L H CM RM a b) ∧
      ordMat q d w S (mulR q w S d T L H CM RM a b) = ordMat q d w S a * ordMat q d w S b :=
    fun a b ha hb => ⟨hPm a b ha hb, (hmulC a b ha.1 hb.1).2⟩
  have hz : ∀ x, P x → x ≠ 0 := by
    intro x hx h0
    have hle : Submonoid.closure ({ordMat q d w S A, ordMat q d w S B} : Set (Mat q d)) ≤
        IsUnit.submonoid (Mat q d) := by
      rw [Submonoid.closure_le]
      rintro _ (rfl | rfl)
      · exact hAu
      · exact hBu
    have hu : IsUnit (ordMat q d w S x) := (IsUnit.mem_submonoid_iff _).1 (hle hx.2)
    rw [h0] at hu
    have e0 : ordMat q d w S 0 = 0 := by
      funext i j
      simp [ordMat]
    rw [e0] at hu
    have h01 : (0 : Mat q d) ⟨0, hd⟩ ⟨0, hd⟩ = (1 : Mat q d) ⟨0, hd⟩ ⟨0, hd⟩ := by
      rw [isUnit_zero_iff.1 hu]
    simp at h01
  unfold clsPc at h
  obtain ⟨bl, cur, n, hall, hk⟩ :=
    slc_runP (Q := fun bl cur _ => slcAll P bl cur)
      (fun bl cur n r hQ _ => ⟨hQ.1, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hPm _ _ (slc_lk_P hP1 hQ _ _) (slc_lk_P hP1 hQ _ _)
        · exact hQ.2 x hx⟩)
      (fun bl cur n r hQ _ => ⟨fun b hb' x hx => by
        rcases List.mem_cons.1 hb' with rfl | hb'
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hPm _ _ (slc_lk_P hP1 hQ _ _) (slc_lk_P hP1 hQ _ _)
          · exact hQ.2 x hx
        · exact hQ.1 b hb' x hx, fun x hx => absurd hx List.not_mem_nil⟩)
      prg [] [B, A, ONE] 3 _ ⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨hB, Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
        · exact ⟨hA, Submonoid.subset_closure (Set.mem_insert _ _)⟩
        · exact hP1⟩ h
  simp only [slc_sB, slc_mapS, scp_pows, slc_and, slc_not, slc_lenN, clK, slc_revOnto, scp_zsOf,
    List.length_map] at hk
  obtain ⟨hlen, hne, hpw, hXg, hrel, hents, hlp⟩ := hk
  have hlen6 : sg.length = 6 := Nat.eq_of_beq_eq_true hlen
  have hPl : ∀ r, P (lk ONE bl cur n r) := fun r => slc_lk_P hP1 hall n r
  set hs := sg.map (lk ONE bl cur n) with hhs
  have hhsP : ∀ h ∈ hs, P h := by
    intro h hh
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 hh
    exact hPl s
  have hnf : ∀ e : List ℕ, (∀ t < 6, e.getD t 0 < 5) →
      P (nfM (mulR q w S d T L H CM RM) ONE (hs.map (scpPw (mulR q w S d T L H CM RM) ONE)) e) ∧
      ordMat q d w S (nfM (mulR q w S d T L H CM RM) ONE
        (hs.map (scpPw (mulR q w S d T L H CM RM) ONE)) e) =
        nfP (hsR (fun r => ordMat q d w S (lk ONE bl cur n r)) sg) (ex e) := by
    intro e he
    obtain ⟨h1, h2⟩ := scp_nfM hPmul ⟨hP1, hone.2⟩ hz hs e hhsP
      (fun t ht => by have := he t (by rw [hhs, List.length_map, hlen6] at ht; exact ht); omega)
    refine ⟨h1, ?_⟩
    rw [h2, hhs, scp_prod_map]
    exact scp_prod_nfP _ sg hlen6 e
  have hhsi : ∀ i : Fin 6, hs.getD i.val 0 = lk ONE bl cur n (sg.getD i.val 0) := fun i =>
    slc_getD_map (by rw [hlen6]; exact i.isLt) 0 0
  have hpwi : ∀ i : Fin 6, P (((hs.map (scpPw (mulR q w S d T L H CM RM) ONE)).getD i.val []).getD 5 0) ∧
      ordMat q d w S (((hs.map (scpPw (mulR q w S d T L H CM RM) ONE)).getD i.val []).getD 5 0) =
        hsR (fun r => ordMat q d w S (lk ONE bl cur n r)) sg i ^ 5 := by
    intro i
    have hi : i.val < hs.length := by rw [hhs, List.length_map, hlen6]; exact i.isLt
    rw [List.getD_eq_getElem (hs.map (scpPw (mulR q w S d T L H CM RM) ONE)) []
      (by simpa using hi), List.getElem_map,
      ← List.getD_eq_getElem _ 0 hi, hhsi i]
    exact scp_pw hPmul ⟨hP1, hone.2⟩ (hPl _) 5 (by norm_num)
  refine ⟨fun r => ordMat q d w S (lk ONE bl cur n r), fun r => (hPl r).2, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  ·
    intro i
    obtain ⟨r, -, hr⟩ := scp_relsOK _ 0 0 hrel i.val i.val le_rfl i.isLt (by omega)
    obtain ⟨he5, he0, hpow, -⟩ := scp_relOK hr
    refine ⟨ex (tl (tl r)), fun t ht => he0 t.val (by have := Fin.le_def.1 ht; omega), ?_⟩
    rw [← (hnf _ he5).2, ← hpow rfl, (hpwi i).2]
  ·
    intro i j hij
    have hij' : i.val < j.val := hij
    obtain ⟨r, -, hr⟩ := scp_relsOK _ 0 0 hrel i.val j.val hij'.le j.isLt (by omega)
    obtain ⟨he5, he0, -, hconj⟩ := scp_relOK hr
    refine ⟨ex (tl (tl r)), fun t ht => he0 t.val (by have := Fin.le_def.1 ht; omega), ?_⟩
    have e := hconj (by omega)
    rw [hhsi i, hhsi j] at e
    beta_reduce
    simp only [hsR]
    rw [← (hnf _ he5).2, ← (hmulC _ _ (hPl _).1 (hPl _).1).2, ← (hmulC _ _ (hPl _).1 (hnf _ he5).1.1).2, e]
  ·
    intro he
    exact Nat.ne_of_beq_eq_false hne (slc_inj hS (hPl rx).1 hone.1 (he.trans hone.2.symm))
  ·
    have hpe : pw1 (mulR q w S d T L H CM RM) (lk ONE bl cur n rx) 4 = ONE := Nat.eq_of_beq_eq_true hpw
    have h2 := (slc_pw1 hmulC (hPl rx).1 4).2
    rw [hpe, hone.2] at h2
    exact h2.symm
  ·
    beta_reduce
    rw [Nat.eq_of_beq_eq_true hXg]
  ·
    intro e he
    obtain ⟨he5, h1, h2⟩ := scp_entOK (scp_ents _ hents e he)
    have hy := hnf e he5
    rw [← hy.2]
    refine ⟨?_, fun z hz' => ?_⟩
    · beta_reduce
      rw [← (hmulC _ _ (hPl _).1 (hPl _).1).2, ← (hmulC _ _ (hPl _).1 hy.1.1).2, h1]
    · beta_reduce
      rw [← (hmulC _ _ (hPl _).1 hy.1.1).2, ← (hmulC _ _ hy.1.1 (hPl _).1).2,
        slc_commOK _ h2 z hz']
  ·
    let P2 : ℕ → Prop := fun x => Canon q d w x ∧ ordMat q d w S x ∈ Submonoid.closure
      (Set.range (hsR (fun r => ordMat q d w S (lk ONE bl cur n r)) sg) ∪
        {Y | ∃ z ∈ es.flatMap (·.drop 7), Y = ordMat q d w S (lk ONE bl cur n z)})
    have hP21 : P2 ONE := ⟨hone.1, by rw [hone.2]; exact Submonoid.one_mem _⟩
    have hP2m : ∀ a b, P2 a → P2 b → P2 (mulR q w S d T L H CM RM a b) := fun a b ha hb =>
      ⟨(hmulC a b ha.1 hb.1).1, by rw [(hmulC a b ha.1 hb.1).2]; exact Submonoid.mul_mem _ ha.2 hb.2⟩
    have hinit : slcAll P2 [] (((es.flatMap (·.drop 7)).map (lk ONE bl cur n)).reverse ++
        (hs.reverse ++ [ONE])) := by
      refine ⟨fun b hb => absurd hb List.not_mem_nil, fun x hx => ?_⟩
      simp only [hhs, List.mem_append, List.mem_reverse, List.mem_map, List.mem_singleton] at hx
      rcases hx with ⟨z, hz, rfl⟩ | ⟨s, hs', rfl⟩ | rfl
      · exact ⟨(hPl z).1, Submonoid.subset_closure (Or.inr ⟨z, hz, rfl⟩)⟩
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs'
        refine ⟨(hPl _).1, Submonoid.subset_closure (Or.inl ⟨⟨j, by omega⟩, ?_⟩)⟩
        simp only [hsR]
        rw [List.getD_eq_getElem _ _ hj]
      · exact hP21
    obtain ⟨bl', cur', n', hall', hk'⟩ := slc_runP (Q := fun bl cur _ => slcAll P2 bl cur)
      (fun bl cur n r hQ _ => ⟨hQ.1, fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hP2m _ _ (slc_lk_P hP21 hQ _ _) (slc_lk_P hP21 hQ _ _)
        · exact hQ.2 x hx⟩)
      (fun bl cur n r hQ _ => ⟨fun b hb x hx => by
        rcases List.mem_cons.1 hb with rfl | hb
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hP2m _ _ (slc_lk_P hP21 hQ _ _) (slc_lk_P hP21 hQ _ _)
          · exact hQ.2 x hx
        · exact hQ.1 b hb x hx, fun x hx => absurd hx List.not_mem_nil⟩)
      lp [] _ _ _ hinit hlp
    simp only [slc_and] at hk'
    obtain ⟨ha, hb⟩ := hk'
    have eA : lk ONE bl' cur' n' (nthD 0 ab 0) = A := Nat.eq_of_beq_eq_true ha
    have eB : lk ONE bl' cur' n' (nthD 0 ab 1) = B := Nat.eq_of_beq_eq_true hb
    have hA2 := (slc_lk_P hP21 hall' n' (nthD 0 ab 0)).2
    have hB2 := (slc_lk_P hP21 hall' n' (nthD 0 ab 1)).2
    rw [eA] at hA2
    rw [eB] at hB2
    exact ⟨hA2, hB2⟩

section Group

variable {G : Type} [Group G]

@[expose] def ext6 (g : Fin 6 → G) : ℕ → G := fun t => if h : t < 6 then g ⟨t, h⟩ else 1

@[expose] def exE (e : Fin 6 → ℕ) : ℕ → ℕ := fun t => if h : t < 6 then e ⟨t, h⟩ else 0

theorem nfP_eq_nfG (g : Fin 6 → G) (e : Fin 6 → ℕ) :
    nfP g e = CFSG.KD.SporCov.nfG (ext6 g) (exE e) 6 0 := by
  simp [nfP, CFSG.KD.SporCov.nfG, ext6, exE, mul_assoc]

theorem exE_zero {e : Fin 6 → ℕ} {i : ℕ} (hi : i < 6) (he : ∀ t, t ≤ (⟨i, hi⟩ : Fin 6) → e t = 0) :
    ∀ t ≤ i, exE e t = 0 := by
  intro t ht
  unfold exE
  split_ifs with h
  · exact he ⟨t, h⟩ (Fin.le_def.2 ht)
  · rfl

theorem isPGroup_ext6 [Finite G] (g : Fin 6 → G)
    (hpow : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ g i ^ 5 = nfP g e)
    (hconj : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
      g j * g i = g i * nfP g e) :
    IsPGroup 5 (pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0) := by
  have hg : ∀ i (hi : i < 6), ext6 g i = g ⟨i, hi⟩ := fun i hi => dif_pos hi
  refine CFSG.KD.SporCov.isPGroup_pcSub Nat.prime_five (ext6 g) ?_ ?_
  · intro i hi
    obtain ⟨e, he, h⟩ := hpow ⟨i, hi⟩
    exact ⟨exE e, exE_zero hi he, by rw [hg i hi, h, nfP_eq_nfG]⟩
  · intro i j hij hj
    obtain ⟨e, he, h⟩ := hconj ⟨i, by omega⟩ ⟨j, hj⟩ (Fin.lt_def.2 hij)
    exact ⟨exE e, exE_zero (by omega) he, by rw [hg i (by omega), hg j hj, h, nfP_eq_nfG]⟩

theorem ext6_mem (g : Fin 6 → G) (i : Fin 6) :
    g i ∈ pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0 := by
  have hm : (ext6 g i.val)⁻¹ ∈ pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0 :=
    Subgroup.subset_closure ⟨i, Nat.zero_le _, rfl⟩
  have e : ext6 g i.val = g i := dif_pos i.isLt
  rw [e] at hm
  simpa using Subgroup.inv_mem _ hm

theorem nfP_mem_ext6 (g : Fin 6 → G) (e : Fin 6 → ℕ) :
    nfP g e ∈ pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0 := by
  have hf : ∀ t : Fin 6, g t ^ e t ∈ pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0 :=
    fun t => Subgroup.pow_mem _ (ext6_mem g t) _
  unfold nfP
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (hf 0) (hf 1)) (hf 2)) (hf 3)) (hf 4)) (hf 5)

theorem generating_of_clsPcFacts [Finite G] {q d : ℕ} (ρ : G →* Mat q d)
    (hρ : Function.Injective ρ) (a b : G) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {Xg : Mat q d} {rx : ℕ} {sg : List ℕ} {es : List (List ℕ)} {R : ℕ → Mat q d}
    (hF : ClsPcFacts (ρ a) (ρ b) Xg rx sg es R) :
    ∃ x₀ : G, ρ x₀ = Xg ∧ orderOf x₀ = 5 ∧ ∀ x : G, IsConj x₀ x → SporKRestGenerating 5 x := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  choose rr hrr using fun r => exists_of_mclosure ρ a b (hF.reg r)
  set g : Fin 6 → G := fun i => rr (sg.getD i.val 0) with hgdef
  have hgs : (fun i => ρ (g i)) = hsR R sg := funext fun i => hrr _
  have nfρ : ∀ e, ρ (nfP g e) = nfP (hsR R sg) e := fun e => by rw [nfP_map, hgs]
  have hg : ∀ i, ρ (g i) = hsR R sg i := fun i => hrr _
  have hpowG : ∀ i : Fin 6, ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧ g i ^ 5 = nfP g e := by
    intro i
    obtain ⟨e, he, h⟩ := hF.pow i
    exact ⟨e, he, hρ (by rw [map_pow, hg, nfρ, h])⟩
  have hconjG : ∀ i j : Fin 6, i < j → ∃ e : Fin 6 → ℕ, (∀ t, t ≤ i → e t = 0) ∧
      g j * g i = g i * nfP g e := by
    intro i j hij
    obtain ⟨e, he, h⟩ := hF.conj i j hij
    exact ⟨e, he, hρ (by rw [map_mul, map_mul, hg, hg, nfρ, h])⟩
  set S₀ : Subgroup G := pcSub (fun t : Fin 6 => (ext6 g t)⁻¹) 0 with hS₀
  have hpg : IsPGroup 5 S₀ := isPGroup_ext6 g hpowG hconjG
  set Z : Set G := {u : G | ∃ z ∈ es.flatMap (·.drop 7), u = rr z} with hZdef
  have hZ : ∀ z ∈ Z, ∃ h y : G, y ∈ S₀ ∧ h⁻¹ * rr rx * h = y ∧ z * y = y * z := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨e, he, hze⟩ := List.mem_flatMap.mp hz
    obtain ⟨h1, h2⟩ := hF.ent e he
    refine ⟨rr (e.getD 6 0), nfP g (ex e), nfP_mem_ext6 g _, ?_, ?_⟩
    · have hm : rr rx * rr (e.getD 6 0) = rr (e.getD 6 0) * nfP g (ex e) :=
        hρ (by rw [map_mul, map_mul, nfρ, hrr, hrr, h1])
      rw [mul_assoc, hm, ← mul_assoc, inv_mul_cancel, one_mul]
    · exact hρ (by rw [map_mul, map_mul, nfρ, hrr, h2 z hze])
  have hS : ∀ Y ∈ Set.range (hsR R sg) ∪ {Y | ∃ z ∈ es.flatMap (·.drop 7), Y = R z},
      ∃ u ∈ Subgroup.closure ((S₀ : Set G) ∪ Z), ρ u = Y := by
    rintro Y (⟨i, rfl⟩ | ⟨z, hz, rfl⟩)
    · exact ⟨g i, Subgroup.subset_closure (Or.inl (ext6_mem g i)), hg i⟩
    · exact ⟨rr z, Subgroup.subset_closure (Or.inr ⟨z, hz, rfl⟩), hrr z⟩
  have ha := mem_of_mclosure ρ hρ _ hS hF.seeds.1
  have hb := mem_of_mclosure ρ hρ _ hS hF.seeds.2
  have hpow : rr rx ^ 5 = 1 := hρ (by rw [map_pow, hrr, hF.pow5, map_one])
  have hne : rr rx ≠ 1 := fun e => hF.ne (by rw [← hrr, e, map_one])
  exact ⟨rr rx, (hrr rx).trans hF.rep, orderOf_eq_prime hpow hne, fun x hx =>
    sporKRest_generating_of_pgroup_closure Nat.prime_five a b hab S₀ hpg (rr rx) Z hZ ha hb hx⟩

end Group

end CFSG.KS.SlpPc

end
