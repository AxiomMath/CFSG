
module

public import CFSG.Certificates.Kernel.ThCent.Bound
public import CFSG.Certificates.Kernel.Th.Spec.DceStrModel

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.DceS CFSG.KC.Th.Spec.Dce CFSG.Certificates.DceTw CFSG.KC.Th.Spec.DceStr
  CFSG.Certificates.LCE CFSG.KC.Loop CFSG.KC.Th.Gen

@[expose] noncomputable def wval {G : Type*} [Group G] (xg : ℕ → G) (w : List ℕ) : G :=
  (w.map (letV xg)).prod

theorem cLen_eq (N i : ℕ) : cLen N i = min (N - 2048 * i) 2048 := rfl

theorem of_chunks (P : ℕ → Bool) {N nc : ℕ} (hN : N ≤ 2048 * nc)
    (h : ∀ i < nc, allBelow (cLen N i) 32 (fun j => P (Nat.add (Nat.mul 2048 i) j)) = true) :
    ∀ k < N, P k = true := by
  intro k hk
  have hi : k / 2048 < nc := by omega
  have h1 : P (Nat.add (Nat.mul 2048 (k / 2048)) (k % 2048)) = true :=
    allBelow_spec (h _ hi) (by rw [cLen_eq]; omega) (k % 2048) (by rw [cLen_eq]; omega)
  have e : Nat.add (Nat.mul 2048 (k / 2048)) (k % 2048) = k := by
    change 2048 * (k / 2048) + k % 2048 = k
    omega
  rwa [e] at h1

theorem card_chunks (p : ℕ → Bool) {N nc : ℕ} (hN : N ≤ 2048 * nc) (cs : ℕ → ℕ)
    (h : ∀ i < nc,
      ((Finset.range (cLen N i)).filter fun j => p (2048 * i + j) = true).card = cs i) :
    ((Finset.range N).filter fun k => p k = true).card = ∑ i ∈ Finset.range nc, cs i := by
  have key : ∀ m ≤ nc, ((Finset.range (min N (2048 * m))).filter fun k => p k = true).card =
      ∑ i ∈ Finset.range m, cs i := by
    intro m
    induction m with
    | zero =>
      intro _
      simp
    | succ m ih =>
      intro hm
      rw [Finset.sum_range_succ, ← ih (by omega), ← h m (by omega)]
      simp only [Finset.card_filter]
      by_cases hNm : N ≤ 2048 * m
      · have e1 : min N (2048 * (m + 1)) = N := by omega
        have e2 : min N (2048 * m) = N := by omega
        have e3 : cLen N m = 0 := by
          rw [cLen_eq]
          omega
        rw [e1, e2, e3, Finset.range_zero, Finset.sum_empty, Nat.add_zero]
      · have e1 : min N (2048 * (m + 1)) = 2048 * m + cLen N m := by
          rw [cLen_eq]
          omega
        have e2 : min N (2048 * m) = 2048 * m := by omega
        rw [e1, e2, Finset.sum_range_add]
  have := key nc le_rfl
  rwa [show min N (2048 * nc) = N by omega] at this

theorem sumN_cons (a : ℕ) (l : List ℕ) : sumN (a :: l) = a + sumN l := rfl

theorem getN_cons_zero (a : ℕ) (l : List ℕ) : getN (a :: l) 0 = a := rfl

theorem getN_cons_succ (a : ℕ) (l : List ℕ) (i : ℕ) : getN (a :: l) (i + 1) = getN l i := rfl

theorem sum_getN_le : ∀ (l : List ℕ) (n : ℕ), ∑ i ∈ Finset.range n, getN l i ≤ sumN l
  | [], n => by
    have : ∀ i, getN [] i = 0 := fun _ => rfl
    simp [this]
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
    rw [Finset.sum_range_succ', getN_cons_zero, sumN_cons]
    simp only [getN_cons_succ]
    have := sum_getN_le l n
    omega

theorem allLt_spec {n : ℕ} : ∀ {l : List ℕ}, allLt l n = true → ∀ c ∈ l, c < n
  | [], _, c, hc => absurd hc List.not_mem_nil
  | a :: l, h, c, hc => by
    have h' : andB (Nat.blt a n) (allLt l n) = true := h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.blt_eq.mp (Gen.andB_left h')
    · exact allLt_spec (Gen.andB_right h') c hc

theorem nodupN_spec : ∀ {l : List ℕ}, nodupN l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    have h' : andB (DceS.notB (memN a l)) (nodupN l) = true := h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodupN_spec (Gen.andB_right h')⟩
    have h1 := Gen.andB_left h'
    rw [(memN_iff a l).2 ha] at h1
    exact absurd h1 (by decide)

theorem selAt_shift (R : ℕ → ℕ) (lo j : ℕ) : selAt R lo j = selAt R 0 (lo + j) := by
  unfold selAt
  rw [show Nat.add 0 (lo + j) = Nat.add lo j from Nat.zero_add _]

theorem commAt_shift (HB TB : ℕ → ℕ) (G lo j : ℕ) :
    commAt HB TB G lo j = commAt HB TB G 0 (lo + j) := by
  unfold commAt
  rw [show Nat.add 0 (lo + j) = Nat.add lo j from Nat.zero_add _]

theorem orAt_shift (EB : ℕ → ℕ) (o r lo j : ℕ) :
    orAt EB o r lo j = orAt EB o r 0 (lo + j) := by
  unfold orAt
  rw [show Nat.add 0 (lo + j) = Nat.add lo j from Nat.zero_add _]

theorem cLen_le (N i : ℕ) : cLen N i ≤ 64 * 32 := by
  rw [cLen_eq]
  omega

theorem sel_card_le {R : ℕ → ℕ} {N : ℕ} {CS : List ℕ} {nc : ℕ} (hN : N ≤ 2048 * nc)
    (h : ∀ i < nc, selChunk R N CS i = true) :
    ((Finset.range N).filter fun k => selAt R 0 k = true).card ≤ sumN CS := by
  rw [card_chunks (selAt R 0) hN (getN CS) fun i hi => ?_]
  · exact sum_getN_le CS nc
  · have e := Nat.eq_of_beq_eq_true (h i hi)
    rw [countSel_eq R (cLen_le N i)] at e
    rw [← e]
    simp only [selAt_shift R (Nat.mul 2048 i)]
    rfl

theorem comm_card_le {HB TB : ℕ → ℕ} {G n : ℕ} {CM : List ℕ} {nc : ℕ} (hn : n ≤ 2048 * nc)
    (h : ∀ i < nc, commChunk HB TB G n CM i = true) :
    ((Finset.range n).filter fun e => commAt HB TB G 0 e = true).card ≤ sumN CM := by
  rw [card_chunks (commAt HB TB G 0) hn (getN CM) fun i hi => ?_]
  · exact sum_getN_le CM nc
  · have e := Nat.eq_of_beq_eq_true (h i hi)
    rw [countComm_eq HB TB (cLen_le n i)] at e
    rw [← e]
    simp only [commAt_shift HB TB G (Nat.mul 2048 i)]
    rfl

theorem or_card_le {EB : ℕ → ℕ} {n o r : ℕ} {OR : List ℕ} {nc : ℕ} (hn : n ≤ 2048 * nc)
    (h : ∀ i < nc, orChunk EB n o r OR i = true) :
    ((Finset.range n).filter fun j => ordRank o r (DceS.mat EB j) = true).card ≤ sumN OR := by
  have e0 : ∀ j, ordRank o r (DceS.mat EB j) = orAt EB o r 0 j := fun j => by
    unfold orAt
    rw [show Nat.add 0 j = j from Nat.zero_add _]
  simp only [e0]
  rw [card_chunks (orAt EB o r 0) hn (getN OR) fun i hi => ?_]
  · exact sum_getN_le OR nc
  · have e := Nat.eq_of_beq_eq_true (h i hi)
    rw [countOR_eq EB (cLen_le n i)] at e
    rw [← e]
    simp only [orAt_shift EB o r (Nat.mul 2048 i)]
    rfl

theorem inv_comm_mat {Q P X : Mat24} (hQP : Q * P = 1) (hPQ : P * Q = 1) (h : Q * X = X * Q) :
    P * X = X * P := by
  calc P * X = P * X * (Q * P) := by rw [hQP, Matrix.mul_one]
    _ = P * (X * Q) * P := by simp only [Matrix.mul_assoc]
    _ = P * (Q * X) * P := by rw [h]
    _ = X * P := by rw [← Matrix.mul_assoc, hPQ, Matrix.one_mul]

theorem mat_comm_pow {A X : Mat24} (h : A * X = X * A) : ∀ k : ℕ, A * X ^ k = X ^ k * A
  | 0 => by rw [pow_zero, Matrix.mul_one, Matrix.one_mul]
  | k + 1 => by
    rw [pow_succ, ← Matrix.mul_assoc, mat_comm_pow h k, Matrix.mul_assoc, h, ← Matrix.mul_assoc]

theorem mat_comm_add_one {A X : Mat24} (h : A * X = X * A) : A * (X + 1) = (X + 1) * A := by
  rw [Matrix.mul_add, Matrix.add_mul, h, Matrix.mul_one, Matrix.one_mul]

theorem psOf_succ (T k : ℕ) : psOf T (Nat.succ k) = List.append (psOf T k)
    (List.cons (pw24 T (Nat.succ k)) (List.cons (Nat.xor (pw24 T (Nat.succ k)) ident24) List.nil)) :=
  rfl

theorem mem_psOf {T : ℕ} : ∀ {n : ℕ} {P : ℕ}, P ∈ psOf T n →
    ∃ k, toMat P = toMat T ^ k ∨ toMat P = toMat T ^ k + 1
  | 0, P, h => absurd h List.not_mem_nil
  | n + 1, P, h => by
    rw [psOf_succ] at h
    rcases List.mem_append.1 h with h1 | h1
    · exact mem_psOf h1
    · refine ⟨n + 1, ?_⟩
      rcases List.mem_cons.1 h1 with rfl | h1
      · exact Or.inl (toMat_pw24 T _)
      · rw [List.mem_singleton] at h1
        subst h1
        right
        change toMat (pw24 T (n + 1) ^^^ ident24) = _
        rw [toMat_xor', toMat_pw24, toMat_ident24]

theorem card_cent_map {M G : Type*} [Group M] [Group G] (φ : M →* G) (hinj : Function.Injective φ)
    (N : Subgroup G) (hφN : ∀ m, φ m ∈ N) (hNφ : ∀ n ∈ N, ∃ m, φ m = n) (x : M) :
    Nat.card (Subgroup.centralizer ({(⟨φ x, hφN x⟩ : N)} : Set N)) =
      Nat.card (Subgroup.centralizer ({x} : Set M)) := by
  let e : M ≃ N := Equiv.ofBijective (fun m => ⟨φ m, hφN m⟩) ⟨fun a b hab => hinj
    (congrArg Subtype.val hab), fun n => by
      obtain ⟨m, hm⟩ := hNφ n.1 n.2
      exact ⟨m, Subtype.ext hm⟩⟩
  refine (Nat.card_congr (Equiv.subtypeEquiv e fun c => ?_)).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hc
    apply Subtype.ext
    change φ c * φ x = φ x * φ c
    rw [← map_mul, ← map_mul, hc]
  · intro hc
    have hc' : φ c * φ x = φ x * φ c := congrArg Subtype.val hc
    rw [← map_mul, ← map_mul] at hc'
    exact hinj hc'

section Model

variable {G : Type*} [Group G] (xg : ℕ → G)
  (hrel : ∀ k < 39, bval xg (LceS.wWord (Hsw.sel k)) (LceS.wLen (Hsw.sel k)) = 1)
  (hgen : Subgroup.closure (xg '' {g | g < 8}) = ⊤)

theorem wval_cons (c : ℕ) (w : List ℕ) : wval xg (c :: w) = letV xg c * wval xg w := by
  simp [wval]

set_option exponentiation.threshold 700 in
include hrel hgen in
theorem class_bound (D : DceStructData) (h : dceStructChk D = true)
    (hG : Nat.card G = 90745943887872000)
    {SV PI QI CJ R H1 : ℕ → ℕ} {B : ℕ} {w FL CS CM : List ℕ} {o r i1 j1 Hi N1 m1 : ℕ}
    (hsh : sharedOK D.ThB_LT B D.ThA_CB CJ D.ThB_om = true) (hNB : D.ThB_NB = 1)
    (hNO : D.ThB_NO ≤ 2048 * 9) (hnT : D.ThB_nT ≤ 2048 * 18)
    (hsv : ∀ i < 9, svChunk SV PI D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NO i = true)
    (hpt : ∀ i < 9, ptChunk SV QI D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om D.ThB_NO i = true)
    (hmisc : classMisc D.ThB_LT D.ThA_CB D.ThB_HB D.ThB_GB D.ThB_OB SV D.ThB_osh D.ThB_owd
      D.ThB_om D.ThB_NO w FL CS CM o r i1 j1 Hi N1 m1 = true)
    (hdiff : ∀ i < 9, diffChunk SV R H1 D.ThB_NO B (psOf (wordM D.ThB_LT w) (o - 1))
      (FL.map (DceS.mat D.ThA_CB)) i1 i = true)
    (hsel : ∀ i < 9, selChunk R D.ThB_NO CS i = true)
    (hcomm : ∀ i < 18, commChunk D.ThB_HB D.ThB_TB
      (mul24 (mul24 (gmN D.ThB_HB D.ThB_GB j1) (wordM D.ThB_LT w)) Hi) D.ThB_nT CM i = true) :
    ∃ ht : wval xg w ∈ Subgroup.closure (xg '' {g | g < 7}),
      wval xg w ^ o = 1 ∧ (wval xg w = 1 → r = 0) ∧
      Nat.card (Subgroup.centralizer
        ({(⟨wval xg w, ht⟩ : Subgroup.closure (xg '' {g | g < 7}))} : Set _)) ≤ N1 * m1 ∧
      (∀ g ∈ Subgroup.closure (xg '' {g | g < 7}), ∀ w' : List ℕ, (∀ c ∈ w', c < 14) →
        g * wval xg w * g⁻¹ = wval xg w' → ordRank o r (wordM D.ThB_LT w') = true) ∧
      ∃ v : Fin 11 → G, v 0 = 1 ∧
        (∀ g : G, ∃ D', ∃ k ∈ Subgroup.closure (xg '' {g | g < 7}),
          ∃ k' ∈ Subgroup.closure (xg '' {g | g < 7}), g = k * v D' * k') ∧
        (∀ D' : Fin 11, D' ≠ 0 → Nat.card ↥(Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom) =
            CFSG.Sporadic.Th.Kernel.mD D') ∧
        ∀ D' : Fin 11, D' ≠ 0 → Nat.card {k : G // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
          (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom ∧
            ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = k} ≤
          ((Finset.range (CFSG.Sporadic.Th.Kernel.mD D')).filter fun j =>
            ordRank o r (DceS.mat (tabB D (cosetOrder D')) j) = true).card := by
  classical
  obtain ⟨φ, v, hφinj, hφN, hNφ, hlet, hLgen, hv0, hcov, hstab, hInT, hex, o', hCB, hinjC, hGM,
    hTS⟩ := struct_model xg hrel hgen D h hG
  rw [hNB] at o'
  have hom : D.ThB_om < 2 ^ 24 := Nat.blt_eq.mp (Gen.andB_left (Gen.andB_left hsh))
  have hinvL := letInvOK_spec (Gen.andB_right (Gen.andB_left hsh))
  have hform := formOK_spec (Gen.andB_left (Gen.andB_right hsh))
  have hcls := classOK_spec (Gen.andB_right (Gen.andB_right hsh)) (by norm_num)
  have m1' := Gen.andB_left hmisc
  have m2' := Gen.andB_right hmisc
  have hw14 := allLt_spec (Gen.andB_left (Gen.andB_left m1'))
  have hTr : ordRank o r (wordM D.ThB_LT w) = true := Gen.andB_right (Gen.andB_left m1')
  have hi1 : i1 < D.ThB_NO := Nat.blt_eq.mp (Gen.andB_left (Gen.andB_right m1'))
  have hj1 : j1 < D.ThB_NO := Nat.blt_eq.mp (Gen.andB_left (Gen.andB_right (Gen.andB_right m1')))
  have hv1 : SV i1 = pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j1 :=
    Nat.eq_of_beq_eq_true (Gen.andB_right (Gen.andB_right (Gen.andB_right m1')))
  have hHi : mul24 (gm D.ThB_HB D.ThB_GB j1) Hi = ident24 :=
    Nat.eq_of_beq_eq_true (Gen.andB_left (Gen.andB_left m2'))
  have hHi' : Hi < 2 ^ 576 := by
    have := Nat.blt_eq.mp (Gen.andB_right (Gen.andB_left m2'))
    change Hi < 1 <<< 576 at this
    rwa [Nat.one_shiftLeft] at this
  have m3' := Gen.andB_right m2'
  have hFL819 := allLt_spec (Gen.andB_left (Gen.andB_left m3'))
  have hFLnd := nodupN_spec (Gen.andB_right (Gen.andB_left m3'))
  have hfl := flOK_spec (Gen.andB_left (Gen.andB_right m3')) (by norm_num)
  have hCS : sumN CS = N1 :=
    Nat.eq_of_beq_eq_true (Gen.andB_left (Gen.andB_right (Gen.andB_right m3')))
  have hCM : sumN CM = m1 :=
    Nat.eq_of_beq_eq_true (Gen.andB_right (Gen.andB_right (Gen.andB_right m3')))
  have hword : ∀ u : List ℕ, (∀ c ∈ u, c < 14) →
      InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (wordM D.ThB_LT u) ∧
        rc φ (wordM D.ThB_LT u) = wval xg u := by
    intro u
    induction u with
    | nil =>
      intro _
      exact ⟨InM_one, by rw [show wordM D.ThB_LT [] = ident24 from rfl, rc_one]; rfl⟩
    | cons c u ih =>
      intro hu
      obtain ⟨h1, h2⟩ := ih fun c' hc' => hu c' (List.mem_cons_of_mem _ hc')
      have hc := hlet c (hu c List.mem_cons_self)
      have e : wordM D.ThB_LT (c :: u) = mul24 (let24 D.ThB_LT c) (wordM D.ThB_LT u) := rfl
      rw [e, wval_cons, ← h2, ← hc.2]
      exact ⟨InM_mul hc.1 h1, rc_mul φ hc.1 h1⟩
  obtain ⟨hT, hrcT⟩ := hword w hw14
  have ht : wval xg w ∈ Subgroup.closure (xg '' {g | g < 7}) := by
    rw [← hrcT]
    exact hφN _
  have hconj : ∀ {A : ℕ}, InM (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) A →
      ∀ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = rc φ A →
        ordRank o r A = true := by
    intro A hA g hg e
    obtain ⟨m, rfl⟩ := hNφ g hg
    rw [← hrcT] at e
    have e2 : mEl _ A = m * mEl _ (wordM D.ThB_LT w) * m⁻¹ := by
      apply hφinj
      rw [map_mul, map_mul, map_inv]
      exact e.symm
    have e3 := congrArg (fun y : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL =>
      ((y : Mat24ˣ) : Mat24)) e2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mEl_val hA, mEl_val hT] at e3
    refine ordRank_conj (Q := ((m : Mat24ˣ) : Mat24)) (P := (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24))
      ?_ ?_ e3 hTr
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨hpow, hrk⟩ := ordRank_spec hTr
  have hmpow : mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (wordM D.ThB_LT w) ^ o = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, mEl_val hT, hpow]
    rfl
  refine ⟨ht, ?_, ?_, ?_, ?_, v, hv0, hcov, hstab, ?_⟩
  · rw [← hrcT]
    change φ _ ^ o = 1
    rw [← map_pow, hmpow, map_one]
  · intro h1
    have e1 : mEl (Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) (wordM D.ThB_LT w) = 1 := by
      apply hφinj
      rw [map_one]
      exact hrcT.trans h1
    have e2 := mEl_val hT
    rw [e1] at e2
    have e3 : toMat (wordM D.ThB_LT w) + 1 = 0 := by
      rw [← e2]
      ext i j
      simp only [Subgroup.coe_one, Units.val_one, Matrix.add_apply, Matrix.zero_apply,
        Matrix.one_apply]
      split_ifs <;> decide
    rw [← hrk, e3, Matrix.rank_zero]
  rotate_left
  ·
    intro g hg w' hw' e
    obtain ⟨h1, h2⟩ := hword w' hw'
    exact hconj h1 g hg (e.trans h2.symm)
  ·
    intro D' hD0
    let F : {k : G // k ∈ Subgroup.closure (xg '' {g | g < 7}) ⊓
        (Subgroup.closure (xg '' {g | g < 7})).map (MulAut.conj (v D')).toMonoidHom ∧
          ∃ g ∈ Subgroup.closure (xg '' {g | g < 7}), g * wval xg w * g⁻¹ = k} →
        {j : ℕ // j ∈ (Finset.range (CFSG.Sporadic.Th.Kernel.mD D')).filter fun j =>
          ordRank o r (DceS.mat (tabB D (cosetOrder D')) j) = true} := fun k =>
      ⟨Classical.choose (hex D' hD0 k.1 k.2.1), by
        obtain ⟨hj, hjk⟩ := Classical.choose_spec (hex D' hD0 k.1 k.2.1)
        obtain ⟨g, hg, hgk⟩ := k.2.2
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ?_⟩
        exact hconj (hInT D' hD0 _ hj) g hg (hgk.trans hjk.symm)⟩
    have hF : Function.Injective F := by
      intro a b hab
      have e := congrArg Subtype.val hab
      have ha := (Classical.choose_spec (hex D' hD0 a.1 a.2.1)).2
      have hb := (Classical.choose_spec (hex D' hD0 b.1 b.2.1)).2
      apply Subtype.ext
      rw [← ha, ← hb]
      exact congrArg (fun j => rc φ (DceS.mat (tabB D (cosetOrder D')) j)) e
    refine (Nat.card_le_card_of_injective F hF).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have e1 : (⟨wval xg w, ht⟩ : Subgroup.closure (xg '' {g | g < 7})) =
      ⟨φ (mEl _ (wordM D.ThB_LT w)), hφN _⟩ := Subtype.ext hrcT.symm
  rw [e1, card_cent_map φ hφinj _ hφN hNφ]
  have hpt24 : ∀ j, pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j < 2 ^ 24 := fun j =>
    lt_of_le_of_lt (Nat.and_le_right) hom
  have hsvk := of_chunks (fun k => andB (orB (Nat.beq (Nat.succ k) D.ThB_NO)
      (Nat.blt (SV k) (SV (Nat.succ k))))
      (andB (Nat.blt (PI k) D.ThB_NO) (Nat.beq (SV k) (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om
        (PI k))))) hNO fun i hi => hsv i hi
  have hptk := of_chunks (fun j => memH SV D.ThB_NO (pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om j)
    (QI j)) hNO fun i hi => hpt i hi
  have hinc : ∀ k, k + 1 < D.ThB_NO → SV k < SV (k + 1) := by
    intro k hk
    have h1 := Gen.andB_left (hsvk k (by omega))
    rcases orB_iff.1 h1 with h2 | h2
    · exact absurd (Nat.eq_of_beq_eq_true h2) (by omega)
    · exact Nat.blt_eq.mp h2
  have hsvp : ∀ k < D.ThB_NO, PI k < D.ThB_NO ∧ SV k = pt D.ThB_OB D.ThB_osh D.ThB_owd D.ThB_om (PI k) := by
    intro k hk
    have h1 := Gen.andB_right (hsvk k hk)
    exact ⟨Nat.blt_eq.mp (Gen.andB_left h1), Nat.eq_of_beq_eq_true (Gen.andB_right h1)⟩
  have hSV24 : ∀ k < D.ThB_NO, SV k < 2 ^ 24 := fun k hk => by
    rw [(hsvp k hk).2]
    exact hpt24 _
  have hB : ∀ m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL,
      ((m : Mat24ˣ) : Mat24) * toMat B * ((m : Mat24ˣ) : Mat24).transpose = toMat B := by
    rintro ⟨m, hm⟩
    induction hm using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      change (Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g : Mat24) * _ * _ = _
      rw [hLgen g hg]
      exact hform g hg
    | one =>
      change ((1 : Mat24ˣ) : Mat24) * _ * _ = _
      rw [Units.val_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    | mul x y _ _ hx hy =>
      change ((x * y : Mat24ˣ) : Mat24) * _ * _ = _
      rw [Units.val_mul, Matrix.transpose_mul]
      calc (x : Mat24) * (y : Mat24) * toMat B * ((y : Mat24).transpose * (x : Mat24).transpose)
          = (x : Mat24) * ((y : Mat24) * toMat B * (y : Mat24).transpose) * (x : Mat24).transpose := by
            simp only [Matrix.mul_assoc]
        _ = toMat B := by rw [hy, hx]
    | inv x _ hx =>
      change ((x⁻¹ : Mat24ˣ) : Mat24) * _ * _ = _
      have h1 : ((x⁻¹ : Mat24ˣ) : Mat24) * (x : Mat24) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 : (x : Mat24).transpose * ((x⁻¹ : Mat24ˣ) : Mat24).transpose = 1 := by
        rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
      calc ((x⁻¹ : Mat24ˣ) : Mat24) * toMat B * ((x⁻¹ : Mat24ˣ) : Mat24).transpose
          = ((x⁻¹ : Mat24ˣ) : Mat24) * ((x : Mat24) * toMat B * (x : Mat24).transpose) *
              ((x⁻¹ : Mat24ˣ) : Mat24).transpose := by rw [hx]
        _ = (((x⁻¹ : Mat24ˣ) : Mat24) * (x : Mat24)) * toMat B *
              ((x : Mat24).transpose * ((x⁻¹ : Mat24ˣ) : Mat24).transpose) := by
            simp only [Matrix.mul_assoc]
        _ = toMat B := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hPs : ∀ m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL,
      ((m : Mat24ˣ) : Mat24) * toMat (wordM D.ThB_LT w) =
        toMat (wordM D.ThB_LT w) * ((m : Mat24ˣ) : Mat24) →
      ∀ P ∈ psOf (wordM D.ThB_LT w) (o - 1), ((m : Mat24ˣ) : Mat24) * toMat P =
        toMat P * ((m : Mat24ˣ) : Mat24) := by
    intro m hm P hP
    obtain ⟨k, hk | hk⟩ := mem_psOf hP
    · rw [hk]
      exact mat_comm_pow hm k
    · rw [hk]
      exact mat_comm_add_one (mat_comm_pow hm k)
  have hletInv : ∀ c < 14, toMat (let24 D.ThB_LT c) * toMat (let24 D.ThB_LT (c ^^^ 1)) = 1 := by
    intro c hc
    rw [← toMat_mul24, hinvL c hc, toMat_ident24]
  have hS : ∀ u ∈ Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL, ∀ k < 819, ∃ k' < 819,
      ((u⁻¹ : Mat24ˣ) : Mat24) * toMat (DceS.mat D.ThA_CB k) * (u : Mat24) =
        toMat (DceS.mat D.ThA_CB k') := by
    intro u hu
    have hgen1 : ∀ g < 7,
        (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24) =
          toMat (let24 D.ThB_LT (2 * g ^^^ 1)) := by
      intro g hg
      have h1 := hletInv (2 * g) (by omega)
      rw [← hLgen g hg] at h1
      have h2 := Units.inv_mul (Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)
      calc (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24)
          = (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g)⁻¹ : Mat24ˣ) : Mat24) *
            (((Lgen D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL g : Mat24ˣ) : Mat24) *
              toMat (let24 D.ThB_LT (2 * g ^^^ 1))) := by rw [h1, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    have hx1 : ∀ g < 7, (2 * g ^^^ 1) = 2 * g + 1 := by decide
    induction hu using Subgroup.closure_induction'' with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro k hk
      obtain ⟨h1, h2⟩ := hcls k hk (2 * g) (by simp only [Set.mem_setOf_eq] at hg; omega)
      refine ⟨_, h1, ?_⟩
      rw [h2, toMat_mul24, toMat_mul24, hgen1 g hg, hLgen g hg]
    | inv_mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro k hk
      have hg' : g < 7 := hg
      obtain ⟨h1, h2⟩ := hcls k hk (2 * g + 1) (by omega)
      refine ⟨_, h1, ?_⟩
      have e : (2 * g + 1) ^^^ 1 = 2 * g := by
        have : ∀ g < 7, (2 * g + 1) ^^^ 1 = 2 * g := by decide
        exact this g hg'
      rw [h2, toMat_mul24, toMat_mul24, e, inv_inv, hgen1 g hg', hx1 g hg', hLgen g hg']
    | one =>
      intro k hk
      exact ⟨k, hk, by rw [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]⟩
    | mul x y _ _ hx hy =>
      intro k hk
      obtain ⟨k1, hk1, e1⟩ := hx k hk
      obtain ⟨k2, hk2, e2⟩ := hy k1 hk1
      refine ⟨k2, hk2, ?_⟩
      rw [← e2, ← e1, mul_inv_rev, Units.val_mul, Units.val_mul]
      simp only [Matrix.mul_assoc]
  have hFLmem : ∀ k ∈ FL, k < 819 ∧
      mul24 (DceS.mat D.ThA_CB k) (wordM D.ThB_LT w) = mul24 (wordM D.ThB_LT w) (DceS.mat D.ThA_CB k) :=
    fun k hk => ⟨hFL819 k hk, (hfl k (hFL819 k hk)).2 hk⟩
  have hFLc : ∀ m : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL,
      ((m : Mat24ˣ) : Mat24) * toMat (wordM D.ThB_LT w) =
        toMat (wordM D.ThB_LT w) * ((m : Mat24ˣ) : Mat24) →
      ∀ Y ∈ (FL.map (DceS.mat D.ThA_CB)).map toMat,
        ((m : Mat24ˣ) : Mat24) * Y * (((m⁻¹ : Mgrp D.ThB_LT D.ThB_LI D.ThB_TL D.ThB_VL D.ThB_NL) :
          Mat24ˣ) : Mat24) ∈ (FL.map (DceS.mat D.ThA_CB)).map toMat := by
    intro m hm Y hY
    rw [List.map_map] at hY ⊢
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hY
    obtain ⟨hk819, hkT⟩ := hFLmem k hk
    obtain ⟨k', hk', e⟩ := hS _ (m⁻¹).2 k hk819
    rw [Subgroup.coe_inv, inv_inv] at e
    refine List.mem_map.2 ⟨k', ?_, ?_⟩
    · refine (hfl k' hk').1 (eq_of_toMat_eq (mul24_lt _ _) (mul24_lt _ _) ?_)
      rw [toMat_mul24, toMat_mul24, ← e]
      have hkT' : toMat (DceS.mat D.ThA_CB k) * toMat (wordM D.ThB_LT w) =
          toMat (wordM D.ThB_LT w) * toMat (DceS.mat D.ThA_CB k) := by
        rw [← toMat_mul24, ← toMat_mul24, hkT]
      have hmi : (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24) * toMat (wordM D.ThB_LT w) =
          toMat (wordM D.ThB_LT w) * (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24) :=
        inv_comm_mat (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
          (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hm
      set Mm := ((m : Mat24ˣ) : Mat24)
      set Mi := (((m : Mat24ˣ)⁻¹ : Mat24ˣ) : Mat24)
      set Y := toMat (DceS.mat D.ThA_CB k)
      set TT := toMat (wordM D.ThB_LT w)
      calc Mm * Y * Mi * TT = Mm * Y * (Mi * TT) := by simp only [Matrix.mul_assoc]
        _ = Mm * Y * (TT * Mi) := by rw [hmi]
        _ = Mm * (Y * TT) * Mi := by simp only [Matrix.mul_assoc]
        _ = Mm * (TT * Y) * Mi := by rw [hkT']
        _ = Mm * TT * Y * Mi := by simp only [Matrix.mul_assoc]
        _ = TT * Mm * Y * Mi := by rw [hm]
        _ = TT * (Mm * Y * Mi) := by simp only [Matrix.mul_assoc]
    · simp only [Function.comp]
      rw [← e, Subgroup.coe_inv]
  have hFLn : ((FL.map (DceS.mat D.ThA_CB)).map toMat).Nodup := by
    rw [List.map_map]
    refine hFLnd.map_on fun a ha b hb e => ?_
    have e' : DceS.mat D.ThA_CB a = DceS.mat D.ThA_CB b :=
      eq_of_toMat_eq (mat_lt _ _) (mat_lt _ _) e
    exact hinjC a (hFL819 a ha) b (hFL819 b hb) e'
  have hdiffk := of_chunks (fun k => diffOK SV R H1 D.ThB_NO B (psOf (wordM D.ThB_LT w) (o - 1))
    (FL.map (DceS.mat D.ThA_CB)) i1 k) hNO fun i hi => hdiff i hi
  have hN1 := (sel_card_le hNO hsel).trans hCS.le
  have hm1 := (comm_card_le hnT hcomm).trans hCM.le
  exact card_cent_le o' hpt24 hGM hTS hinc hSV24
    (fun k hk => ⟨PI k, (hsvp k hk).1, (hsvp k hk).2⟩)
    (fun j hj => ⟨QI j, Nat.blt_eq.mp (Gen.andB_left (hptk j hj)),
      Nat.eq_of_beq_eq_true (Gen.andB_right (hptk j hj))⟩)
    hT hB hPs hFLn hFLc hdiffk hN1 hi1 hj1 hv1 hHi hHi' hm1

end Model

end CFSG.KC.ThCent

end
