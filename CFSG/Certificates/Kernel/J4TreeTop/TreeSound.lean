module

public import CFSG.Certificates.Kernel.J4TreeNode.Node
public import Certificates.Data.Kernel.J4TreeTopSylow

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native CFSG.ASVolI CFSG.Sporadic.J4
open CFSG.Sporadic.J4.QT

theorem mem_mergeF : ∀ (f : ℕ) (a b : List ℕ) (x : ℕ), x ∈ mergeF f a b ↔ x ∈ a ∨ x ∈ b
  | 0, a, b, x => by simp [mergeF]
  | _ + 1, [], b, x => by simp [mergeF]
  | _ + 1, a :: as, [], x => by simp [mergeF]
  | f + 1, a :: as, b :: bs, x => by
    simp only [mergeF]
    split_ifs
    · simp only [List.mem_cons, mem_mergeF f (a :: as) bs x]
      tauto
    · simp only [List.mem_cons, mem_mergeF f as (b :: bs) x]
      tauto

theorem mem_halves : ∀ (l : List ℕ) (x : ℕ), x ∈ (halves l).1 ∨ x ∈ (halves l).2 ↔ x ∈ l
  | [], x => by
    change x ∈ [] ∨ x ∈ [] ↔ x ∈ []
    simp
  | [a], x => by
    change x ∈ [a] ∨ x ∈ [] ↔ x ∈ [a]
    simp
  | a :: b :: l, x => by
    change x ∈ a :: (halves l).1 ∨ x ∈ b :: (halves l).2 ↔ x ∈ a :: b :: l
    simp only [List.mem_cons]
    rw [← mem_halves l x]
    tauto

theorem mem_msort : ∀ (f : ℕ) (l : List ℕ) (x : ℕ), x ∈ msort f l ↔ x ∈ l
  | 0, _, _ => Iff.rfl
  | _ + 1, [], _ => Iff.rfl
  | _ + 1, [_], _ => Iff.rfl
  | f + 1, a :: b :: l', x => by
    change x ∈ mergeF (l'.length + 2) (msort f (halves (a :: b :: l')).1)
      (msort f (halves (a :: b :: l')).2) ↔ _
    rw [mem_mergeF, mem_msort f, mem_msort f, mem_halves]

theorem subS_spec : ∀ (f : ℕ) (ps ks : List ℕ), subS f ps ks = true → ∀ p ∈ ps, p ∈ ks
  | _, [], _, _, _, hp => by simp at hp
  | 0, _ :: _, _, h, _, _ => by simp [subS] at h
  | _ + 1, _ :: _, [], h, _, _ => by simp [subS] at h
  | f + 1, p :: ps, k :: ks, h, q, hq => by
    simp only [subS] at h
    split_ifs at h with hpk
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [Nat.eq_of_beq_eq_true hpk]
        exact List.mem_cons_self
      · exact subS_spec f ps (k :: ks) h q hq
    · rw [Bool.and_eq_true] at h
      exact List.mem_cons_of_mem _ (subS_spec f (p :: ps) ks h.2 q hq)

theorem incrFrom_sorted : ∀ (lo : ℕ) (l : List ℕ), incrFrom lo l = true →
    l.Pairwise (· < ·) ∧ ∀ x ∈ l, lo ≤ x
  | _, [], _ => ⟨List.Pairwise.nil, by simp⟩
  | lo, x :: l, h => by
    simp only [incrFrom, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := incrFrom_sorted (x + 1) l h2
    refine ⟨List.Pairwise.cons (fun y hy => by have := ih2 y hy; omega) ih1, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h1
    · have := ih2 y hy
      omega

theorem treeOK_spec {par : ℕ → ℕ → ℕ} {n Y : ℕ} {es : List (ℕ × ℕ × ℕ)}
    (h : treeOK par n Y es = true) :
    (es.map Prod.fst).Pairwise (· < ·) ∧ ∀ e ∈ es, e.1 < 2 ^ 144 ∧ (e.2.1 = 0 → e.1 = Y) ∧
      (e.2.1 ≠ 0 → e.2.2 < n ∧ ∃ e' ∈ es, e'.1 = par e.2.2 e.1 ∧ e'.2.1 + 1 = e.2.1) := by
  unfold treeOK at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨(incrFrom_sorted 0 _ h1).1, fun e he => ?_⟩
  have he2 := h2 e he
  simp only [Bool.and_eq_true, Nat.blt_eq] at he2
  obtain ⟨⟨hx, hd⟩, hc⟩ := he2
  refine ⟨hx, fun h0 => ?_, fun h0 => ?_⟩
  · rw [if_pos h0] at hc
    exact Nat.eq_of_beq_eq_true hc
  · rw [if_neg h0, Nat.blt_eq] at hc
    refine ⟨hc, ?_⟩
    have hk := subS_spec _ _ _ h3 (keyOf (par e.2.2 e.1) (e.2.1 - 1)) (by
      rw [mem_msort]
      have hb : Nat.beq e.2.1 0 = false := by
        cases hb : Nat.beq e.2.1 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hb) h0
      exact List.mem_map.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hb]⟩, rfl⟩)
    obtain ⟨e', he', hkey⟩ := List.mem_map.mp hk
    have hd' := h2 e' he'
    simp only [Bool.and_eq_true, Nat.blt_eq] at hd'
    unfold keyOf at hkey
    refine ⟨e', he', ?_, ?_⟩ <;> omega

theorem closedOK_spec {f : ℕ → ℕ → ℕ} {n : ℕ} {xs : List ℕ} (h : closedOK f n xs = true) :
    ∀ j < n, ∀ x ∈ xs, f j x ∈ xs := by
  intro j hj x hx
  unfold closedOK at h
  have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [beq_iff_eq] at h1
  rw [← h1, mem_msort]
  exact List.mem_map_of_mem hx

theorem codeWF_rc {a : Code} {X : ℕ} (ha : RC a X) : burnsideJ4NP_CodeWF a := by
  obtain ⟨rows⟩ := a
  change rows = CFSG.KC.Co1F2.unpackR 12 X at ha
  subst ha
  exact burnsideJ4NP_codeWF_of_wf (wf_unpack X)

section PK


theorem mat_mul_inv {s : J} (hs : s ∈ Hj) :
    burnsideJ4NP_codeMat (burnsideJ4NP_encJ s) * burnsideJ4NP_codeMat (burnsideJ4NP_encJ s⁻¹) =
      1 := by
  rw [← burnsideJ4NP_codeMat_mul, ← burnsideJ4NP_encJ_mul hs (Hj.inv_mem hs), mul_inv_cancel,
    burnsideJ4NP_encJ_one, burnsideJ4NP_codeMat_one]

theorem mat_inv_mul {s : J} (hs : s ∈ Hj) :
    burnsideJ4NP_codeMat (burnsideJ4NP_encJ s⁻¹) * burnsideJ4NP_codeMat (burnsideJ4NP_encJ s) =
      1 := by
  rw [← burnsideJ4NP_codeMat_mul, ← burnsideJ4NP_encJ_mul (Hj.inv_mem hs) hs, inv_mul_cancel,
    burnsideJ4NP_encJ_one, burnsideJ4NP_codeMat_one]

theorem pk_conj_of {s z : J} {S SI X : ℕ} (hs : PK s S) (hsi : PK s⁻¹ SI)
    (hz : PK z (M (M SI X) S)) : PK (s * z * s⁻¹) X := by
  have hx : RC (⟨CFSG.KC.Co1F2.unpackR 12 X⟩ : Code) X := rfl
  have hez : burnsideJ4NP_encJ z =
      burnsideJ4NP_encJ s⁻¹ * ⟨CFSG.KC.Co1F2.unpackR 12 X⟩ * burnsideJ4NP_encJ s :=
    rc_eq hz.2 (rc_mul (rc_mul hsi.2 hx) hs.2)
  have hw := pk_mul (pk_mul hs hz) hsi
  refine ⟨hw.1, ?_⟩
  have heq : burnsideJ4NP_encJ (s * z * s⁻¹) = ⟨CFSG.KC.Co1F2.unpackR 12 X⟩ := by
    refine burnsideJ4NP_codeMat_inj (codeWF_rc hw.2) (codeWF_rc hx) ?_
    rw [burnsideJ4NP_encJ_mul (Hj.mul_mem hs.1 hz.1) hsi.1, burnsideJ4NP_encJ_mul hs.1 hz.1, hez]
    simp only [burnsideJ4NP_codeMat_mul]
    have h1 := mat_mul_inv hs.1
    generalize burnsideJ4NP_codeMat (burnsideJ4NP_encJ s) = P at h1 ⊢
    generalize burnsideJ4NP_codeMat (burnsideJ4NP_encJ s⁻¹) = Q at h1 ⊢
    generalize burnsideJ4NP_codeMat (⟨CFSG.KC.Co1F2.unpackR 12 X⟩ : Code) = R
    calc P * (Q * R * P) * Q = (P * Q) * R * (P * Q) := by simp only [Matrix.mul_assoc]
      _ = R := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  rw [heq]
  exact hx

theorem pk_mul_of {s z : J} {S SI X : ℕ} (hs : PK s S) (hsi : PK s⁻¹ SI)
    (hz : PK z (M X SI)) : PK (z * s) X := by
  have hx : RC (⟨CFSG.KC.Co1F2.unpackR 12 X⟩ : Code) X := rfl
  have hez : burnsideJ4NP_encJ z = ⟨CFSG.KC.Co1F2.unpackR 12 X⟩ * burnsideJ4NP_encJ s⁻¹ :=
    rc_eq hz.2 (rc_mul hx hsi.2)
  have hw := pk_mul hz hs
  refine ⟨hw.1, ?_⟩
  have heq : burnsideJ4NP_encJ (z * s) = ⟨CFSG.KC.Co1F2.unpackR 12 X⟩ := by
    refine burnsideJ4NP_codeMat_inj (codeWF_rc hw.2) (codeWF_rc hx) ?_
    rw [burnsideJ4NP_encJ_mul hz.1 hs.1, hez]
    simp only [burnsideJ4NP_codeMat_mul]
    rw [Matrix.mul_assoc, mat_inv_mul hs.1, Matrix.mul_one]
  rw [heq]
  exact hx

theorem tree_conj {K : Subgroup J} {sl : List J} {S SI : List ℕ} (hS : List.Forall₂ PK sl S)
    (hSI : List.Forall₂ (fun s X => PK s⁻¹ X) sl SI) (hsK : ∀ s ∈ sl, s ∈ K) {y : J} {Y : ℕ}
    (hy : PK y Y) {n : ℕ} (hn : n = S.length) {es : List (ℕ × ℕ × ℕ)}
    (h : treeOK (fun j x => M (M (SI.getD j 0) x) (S.getD j 0)) n Y es = true) :
    ∀ e ∈ es, ∃ p ∈ K, PK (p * y * p⁻¹) e.1 := by
  obtain ⟨-, hent⟩ := treeOK_spec h
  have key : ∀ d, ∀ e ∈ es, e.2.1 = d → ∃ p ∈ K, PK (p * y * p⁻¹) e.1 := by
    intro d
    induction d with
    | zero =>
      intro e he hd
      refine ⟨1, K.one_mem, ?_⟩
      rw [(hent e he).2.1 hd]
      simpa using hy
    | succ d ih =>
      intro e he hd
      obtain ⟨hj, e', he', hpar, hd'⟩ := (hent e he).2.2 (by omega)
      obtain ⟨p, hpK, hpp⟩ := ih e' he' (by omega)
      have hj' : e.2.2 < sl.length := by rw [forall₂_length hS, ← hn]; exact hj
      have hs := forall₂_getD (a := 1) (b := 0) hS _ hj'
      have hsi := forall₂_getD (a := 1) (b := 0) hSI _ hj'
      rw [hpar] at hpp
      refine ⟨sl.getD e.2.2 1 * p, K.mul_mem (hsK _ (getD_mem hj')) hpK, ?_⟩
      have e1 : sl.getD e.2.2 1 * p * y * (sl.getD e.2.2 1 * p)⁻¹ =
          sl.getD e.2.2 1 * (p * y * p⁻¹) * (sl.getD e.2.2 1)⁻¹ := by group
      rw [e1]
      exact pk_conj_of hs hsi hpp
  exact fun e he => key _ e he rfl

theorem tree_orbit_bound {K : Subgroup J} {sl : List J} {S SI : List ℕ}
    (hS : List.Forall₂ PK sl S) (hSI : List.Forall₂ (fun s X => PK s⁻¹ X) sl SI)
    (hsK : ∀ s ∈ sl, s ∈ K) {y : J} {Y : ℕ} (hy : PK y Y) {n : ℕ} (hn : n = S.length)
    {es : List (ℕ × ℕ × ℕ)}
    (h : treeOK (fun j x => M (M (SI.getD j 0) x) (S.getD j 0)) n Y es = true) :
    es.length * Nat.card ↥(K ⊓ Subgroup.centralizer {y}) ≤ Nat.card K := by
  classical
  obtain ⟨hsort, hent⟩ := treeOK_spec h
  have hconj := tree_conj hS hSI hsK hy hn h
  choose! q hqK hq using fun i (hi : i < es.length) => hconj (es.getD i default) (getD_mem hi)
  let z : ℕ → J := fun i => q i * y * (q i)⁻¹
  have hinj : Set.InjOn z (Finset.range es.length) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hc := pk_canon (hq i hi) (hq j hj) (hent _ (getD_mem hi)).1 (hent _ (getD_mem hj)).1 hij
    rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have := List.pairwise_iff_getElem.mp hsort i j (by simpa using hi) (by simpa using hj) hlt
      simp only [List.getElem_map] at this
      omega
    · have := List.pairwise_iff_getElem.mp hsort j i (by simpa using hj) (by simpa using hi) hlt
      simp only [List.getElem_map] at this
      omega
  have hcard := Finset.card_image_of_injOn hinj
  have := card_conj_le K y ((Finset.range es.length).image z) (by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨q i, hqK i (Finset.mem_range.mp hi), rfl⟩)
  rwa [hcard, Finset.card_range] at this

theorem tree_right {gl : List J} {Go GIo : List ℕ} (hG : List.Forall₂ PK gl Go)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) gl GIo) {n : ℕ} (hn : n = Go.length)
    {es : List (ℕ × ℕ × ℕ)} (h : treeOK (fun j x => M x (GIo.getD j 0)) n oneK es = true) :
    ∀ e ∈ es, ∃ p ∈ Subgroup.closure {x | x ∈ gl}, PK p e.1 := by
  obtain ⟨-, hent⟩ := treeOK_spec h
  have key : ∀ d, ∀ e ∈ es, e.2.1 = d → ∃ p ∈ Subgroup.closure {x | x ∈ gl}, PK p e.1 := by
    intro d
    induction d with
    | zero =>
      intro e he hd
      refine ⟨1, Subgroup.one_mem _, ?_⟩
      rw [(hent e he).2.1 hd]
      exact pk_one
    | succ d ih =>
      intro e he hd
      obtain ⟨hj, e', he', hpar, hd'⟩ := (hent e he).2.2 (by omega)
      obtain ⟨p, hpK, hpp⟩ := ih e' he' (by omega)
      have hj' : e.2.2 < gl.length := by rw [forall₂_length hG, ← hn]; exact hj
      have hs := forall₂_getD (a := 1) (b := 0) hG _ hj'
      have hsi := forall₂_getD (a := 1) (b := 0) hGI _ hj'
      rw [hpar] at hpp
      exact ⟨p * gl.getD e.2.2 1, Subgroup.mul_mem _ hpK (Subgroup.subset_closure (getD_mem hj')),
        pk_mul_of hs hsi hpp⟩
  exact fun e he => key _ e he rfl

theorem tree_closure_card {gl : List J} {Go GIo : List ℕ} (hG : List.Forall₂ PK gl Go)
    (hGI : List.Forall₂ (fun s X => PK s⁻¹ X) gl GIo) {n : ℕ} (hn : n = Go.length)
    {es : List (ℕ × ℕ × ℕ)} (ht : treeOK (fun j x => M x (GIo.getD j 0)) n oneK es = true)
    (hc : closedOK (fun j x => M x (Go.getD j 0)) n (es.map Prod.fst) = true) (hne : es ≠ []) :
    Nat.card (Subgroup.closure {x | x ∈ gl}) = es.length := by
  classical
  set O := Subgroup.closure {x | x ∈ gl}
  obtain ⟨hsort, hent⟩ := treeOK_spec ht
  set codes := es.map Prod.fst with hcodes
  have hcode : ∀ x ∈ codes, ∃ p ∈ O, PK p x := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact tree_right hG hGI hn ht e he
  have hcan : ∀ x ∈ codes, x < 2 ^ 144 := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact (hent e he).1
  choose! q hqO hq using hcode
  set E : Set J := q '' {x | x ∈ codes} with hE
  have hEfin : E.Finite := (List.finite_toSet codes).image q
  have hEO : E ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact hqO x hx
  have hstep : ∀ s ∈ gl, ∀ w ∈ E, w * s ∈ E := by
    intro s hs w hw
    obtain ⟨x, hx, rfl⟩ := hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
    have hjn : j < n := by rw [hn, ← forall₂_length hG]; exact hj
    have hsj := forall₂_getD (a := 1) (b := 0) hG j hj
    rw [List.getD_eq_getElem _ _ hj] at hsj
    have hy := closedOK_spec hc j hjn x hx
    have he := pk_eq (pk_mul (hq x hx) hsj) (hq _ hy)
    rw [he]
    exact ⟨_, hy, rfl⟩
  have hinvE : ∀ a : J, (∀ v ∈ E, v * a ∈ E) → ∀ w ∈ E, w * a⁻¹ ∈ E := by
    intro a ha w hw
    have hbij := (hEfin.injOn_iff_bijOn_of_mapsTo (f := fun v => v * a)
      (by intro v hv; exact ha v hv)).mp (by intro x _ y _ hxy; exact mul_right_cancel hxy)
    obtain ⟨v, hv, rfl⟩ := hbij.surjOn hw
    simpa using hv
  have hclos : ∀ w ∈ O, ∀ v ∈ E, v * w ∈ E := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem s hs => exact fun v hv => hstep s hs v hv
    | one => exact fun v hv => by simpa using hv
    | mul a b _ _ ha hb => exact fun v hv => by rw [← mul_assoc]; exact hb _ (ha v hv)
    | inv a _ ha => exact hinvE a ha
  obtain ⟨e0, he0⟩ := List.exists_mem_of_ne_nil es hne
  have hx0 : e0.1 ∈ codes := List.mem_map_of_mem he0
  have hq0 : q e0.1 ∈ E := ⟨_, hx0, rfl⟩
  have hOE : (O : Set J) = E := by
    refine Set.Subset.antisymm (fun w hw => ?_) hEO
    have := hclos ((q e0.1)⁻¹ * w) (O.mul_mem (O.inv_mem (hEO hq0)) hw) _ hq0
    simpa using this
  have hnd : codes.Nodup := hsort.imp (fun h => ne_of_lt h)
  have hEF : E = ((codes.toFinset.image q : Finset J) : Set J) := by
    ext w
    simp [hE]
  have hcO : Nat.card ↥O = Nat.card ↥(O : Set J) := rfl
  rw [hcO, hOE, hEF, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn (fun x hx y hy hxy => pk_canon (hq x (by simpa using hx))
      (hq y (by simpa using hy)) (hcan x (by simpa using hx)) (hcan y (by simpa using hy)) hxy),
    List.toFinset_card_of_nodup hnd, hcodes, List.length_map]

end PK

end CFSG.KC.J4TreeS
