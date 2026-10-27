module

public import CFSG.LieType.Chevalley.RootOps.Check
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

@[expose] def imgTabs : Tag → List ℕ
  | .G2 => g2ImgTab
  | .F4 => f4ImgTab
  | .D4 => d4ImgTab
  | .E6 => e6ImgTab
  | .E7 => e7ImgTab
  | .E8 => e8ImgTab

@[expose] def imgPar (τ : Tag) (i : Fin τ.rank) (m : ℕ) : ℕ :=
  ((imgTabs τ).getD i 0 >>> (9 * m)) &&& 511

@[expose] def tabCheck (τ : Tag) : Bool :=
  (List.range τ.rootCertificate.roots.length).all fun m => (List.finRange τ.rank).all fun i =>
    imgPar τ i m == 2 * τ.rootCertificate.image m i + downAt τ m i % 2

@[expose] def sgnOf (b : ℕ) : ℤ := if b % 2 = 1 then -1 else 1

theorem neg_one_pow_eq_sgnOf {R : Type*} [CommRing R] (b : ℕ) :
    ((-1 : R) ^ b) = ((sgnOf b : ℤ) : R) := by
  unfold sgnOf
  split_ifs with h
  · rw [← Nat.div_add_mod b 2, h, pow_add, pow_mul]
    simp
  · rw [← Nat.div_add_mod b 2, Nat.mod_two_ne_one.1 h, pow_add, pow_mul]
    simp

theorem sgnOf_mul_self (b : ℕ) : sgnOf b * sgnOf b = 1 := by
  unfold sgnOf
  split_ifs <;> rfl

variable {τ : Tag}

theorem imgPar_eq (h : tabCheck τ = true) {m : ℕ} (hm : m < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : imgPar τ i m = 2 * τ.rootCertificate.image m i + downAt τ m i % 2 := by
  simp only [tabCheck, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    beq_iff_eq] at h
  exact h m hm i

theorem imgPar_div_two (h : tabCheck τ = true) {m : ℕ} (hm : m < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : imgPar τ i m / 2 = τ.rootCertificate.image m i := by
  rw [imgPar_eq h hm]
  omega

theorem sgnOf_imgPar (h : tabCheck τ = true) {m : ℕ} (hm : m < τ.rootCertificate.roots.length)
    (i : Fin τ.rank) : sgnOf (imgPar τ i m) = sgnOf (downAt τ m i) := by
  rw [imgPar_eq h hm]
  unfold sgnOf
  congr 1
  simp only [Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]

@[expose] def nRowF (τ : Tag) (i : Fin τ.rank) (p : ℕ) : List (ℕ × ℤ) :=
  if h : p < τ.rank then [(p, 1), (i, -((τ.cartan ⟨p, h⟩ i).natAbs : ℤ))]
  else [(τ.rank + imgPar τ i (p - τ.rank) / 2, sgnOf (imgPar τ i (p - τ.rank)))]

theorem nRowF_eq (h : tabCheck τ = true) (i : Fin τ.rank) {p : ℕ} (hp : p < dim τ) :
    nRowF τ i p = nPos τ i p := by
  unfold nRowF nPos
  split_ifs with hpr
  · rfl
  · have hm : p - τ.rank < τ.rootCertificate.roots.length := by simp only [dim] at hp; omega
    rw [imgPar_div_two h hm, sgnOf_imgPar h hm, neg_one_pow_eq_sgnOf (R := ℤ), Int.cast_id]

@[expose] def nColF (τ : Tag) (i : Fin τ.rank) (c : ℕ) : List (ℕ × ℤ) :=
  if c < τ.rank then
    (if c = i then (List.finRange τ.rank).map fun (m : Fin τ.rank) =>
        ((m : ℕ), (if m = i then 1 else 0) - ((τ.cartan m i).natAbs : ℤ))
      else [(c, 1)])
  else [(τ.rank + imgPar τ i (c - τ.rank) / 2, sgnOf (imgPar τ i (c - τ.rank)))]

@[expose] def conjEntries (τ : Tag) (i : Fin τ.rank) (L : List Entry) : List Entry :=
  L.flatMap fun e => (nColF τ i e.1).flatMap fun x =>
    (nRowF τ i e.2.1).map fun y => (x.1, y.1, x.2 * y.2 * e.2.2)

variable {R : Type*} [CommRing R]

theorem entriesOp_append (L L' : List Entry) :
    entriesOp τ R (L ++ L') = entriesOp τ R L + entriesOp τ R L' := by
  simp [entriesOp]

theorem entriesOp_flatMap {α : Type*} (l : List α) (f : α → List Entry) :
    entriesOp τ R (l.flatMap f) = (l.map fun a => entriesOp τ R (f a)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, entriesOp_append, ih, List.map_cons, List.sum_cons]

@[expose] noncomputable def coordOf (τ : Tag) (R : Type*) [CommRing R] (v : List (ℕ × ℤ)) :
    RootModule τ R →ₗ[R] R :=
  (v.map fun x => (x.2 : R) • posCoord τ R x.1).sum

theorem entriesOp_single_row (c : ℕ) (z : ℤ) (v : List (ℕ × ℤ)) :
    entriesOp τ R (v.map fun y => (c, y.1, y.2 * z)) =
      (z : R) • (posCoord τ R c).smulRight (vecOf τ R v) := by
  induction v with
  | nil =>
    refine LinearMap.ext fun u => ?_
    simp [entriesOp]
  | cons y v ih =>
    rw [List.map_cons, entriesOp_cons, ih]
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, vecOf_cons,
      Int.cast_mul]
    module

theorem entriesOp_conj_single (i : Fin τ.rank) (e : Entry) :
    entriesOp τ R ((nColF τ i e.1).flatMap fun x =>
        (nRowF τ i e.2.1).map fun y => (x.1, y.1, x.2 * y.2 * e.2.2)) =
      (e.2.2 : R) • (coordOf τ R (nColF τ i e.1)).smulRight (vecOf τ R (nRowF τ i e.2.1)) := by
  rw [entriesOp_flatMap]
  unfold coordOf
  induction nColF τ i e.1 with
  | nil =>
    refine LinearMap.ext fun u => ?_
    simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    have : ((nRowF τ i e.2.1).map fun y => (x.1, y.1, x.2 * y.2 * e.2.2)) =
        (nRowF τ i e.2.1).map fun y => (x.1, y.1, y.2 * (x.2 * e.2.2)) := by
      congr 1
      funext y
      congr 2
      ring
    rw [this, entriesOp_single_row]
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, Int.cast_mul]
    module


theorem coordOf_cons (x : ℕ × ℤ) (l : List (ℕ × ℤ)) :
    coordOf τ R (x :: l) = (x.2 : R) • posCoord τ R x.1 + coordOf τ R l :=
  rfl

theorem coordOf_apply (l : List (ℕ × ℤ)) (u : RootModule τ R) :
    coordOf τ R l u = (l.map fun x => (x.2 : R) * posCoord τ R x.1 u).sum := by
  induction l with
  | nil => simp [coordOf]
  | cons x l ih => simp [coordOf_cons, ih]

theorem nColF_self (i : Fin τ.rank) :
    nColF τ i i = (List.finRange τ.rank).map fun (m : Fin τ.rank) =>
      ((m : ℕ), (if m = i then 1 else 0) - ((τ.cartan m i).natAbs : ℤ)) := by
  simp [nColF, i.2]

theorem nColF_of_lt_of_ne (i : Fin τ.rank) {c : ℕ} (hc : c < τ.rank) (hci : c ≠ i) :
    nColF τ i c = [(c, 1)] := by
  simp [nColF, hc, hci]

theorem nColF_of_ge (i : Fin τ.rank) {c : ℕ} (hc : ¬c < τ.rank) :
    nColF τ i c = [(τ.rank + imgPar τ i (c - τ.rank) / 2, sgnOf (imgPar τ i (c - τ.rank)))] := by
  simp [nColF, hc]

theorem nRowF_of_lt (i : Fin τ.rank) {q : ℕ} (hq : q < τ.rank) :
    nRowF τ i q = [(q, 1), (i, -((τ.cartan ⟨q, hq⟩ i).natAbs : ℤ))] := by
  simp [nRowF, hq]

theorem nRowF_of_ge (i : Fin τ.rank) {q : ℕ} (hq : ¬q < τ.rank) :
    nRowF τ i q = [(τ.rank + imgPar τ i (q - τ.rank) / 2, sgnOf (imgPar τ i (q - τ.rank)))] := by
  simp [nRowF, hq]

theorem posCoord_posVec_fin {m : Fin τ.rank} {q : ℕ} (hq : q < dim τ) :
    posCoord τ R m (posVec τ R q) = if (m : ℕ) = q then 1 else 0 :=
  posCoord_posVec hq

theorem dim_eq : dim τ = τ.rank + τ.rootCertificate.roots.length :=
  rfl

theorem coordOf_nColF_weylElt_posVec (h : tabCheck τ = true) (i : Fin τ.rank) {c q : ℕ}
    (hc : c < dim τ) (hq : q < dim τ) :
    coordOf τ R (nColF τ i c) ((weylElt τ R i 1 : Module.End R (RootModule τ R)) (posVec τ R q)) =
      if c = q then 1 else 0 := by
  rw [weylElt_posVec i hq, ← nRowF_eq h i hq, coordOf_apply]
  have hi : (i : ℕ) < dim τ := by rw [dim_eq]; omega
  by_cases hcr : c < τ.rank <;> by_cases hqr : q < τ.rank
  · rw [nRowF_of_lt i hqr]
    simp only [vecOf_cons, vecOf_nil, add_zero, map_add, map_smul, smul_eq_mul, Int.cast_one,
      one_mul, Int.cast_neg, Int.cast_natCast]
    by_cases hci : c = i
    · subst hci
      rw [nColF_self, List.map_map, ← Fin.sum_univ_def]
      simp only [Function.comp, posCoord_posVec_fin hq, posCoord_posVec_fin hi, Int.cast_sub,
        Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_natCast]
      have hq' : ∀ m : Fin τ.rank, ((m : ℕ) = q) ↔ m = ⟨q, hqr⟩ := fun m => by
        rw [Fin.ext_iff]
      have hi' : ∀ m : Fin τ.rank, ((m : ℕ) = i) ↔ m = i := fun m => Fin.val_inj
      simp only [hq', hi', mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have h2 : ((τ.cartan i i).natAbs : R) = 2 := by
        rw [τ.cartan_self]
        norm_num
      rw [h2]
      by_cases hiq : (i : ℕ) = q
      · have : i = ⟨q, hqr⟩ := Fin.ext hiq
        subst this
        simp
        ring
      · have hne : (⟨q, hqr⟩ : Fin τ.rank) ≠ i := fun h => hiq (by rw [← h])
        simp [hne, Ne.symm hne]
        ring
    · rw [nColF_of_lt_of_ne i hcr hci]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Int.cast_one,
        one_mul, posCoord_posVec hq, posCoord_posVec hi, hci, ↓reduceIte, mul_zero, add_zero]
  · rw [nRowF_of_ge i hqr]
    have hq2 : τ.rank + imgPar τ i (q - τ.rank) / 2 < dim τ := by
      rw [imgPar_div_two h (by rw [dim_eq] at hq; omega), dim_eq]
      have := rootCertificate_image_lt (τ := τ) (k := q - τ.rank) (by rw [dim_eq] at hq; omega) i
      omega
    simp only [vecOf_cons, vecOf_nil, add_zero, map_smul, smul_eq_mul]
    have hne : c ≠ q := by omega
    simp only [hne, ↓reduceIte]
    by_cases hci : c = i
    · subst hci
      rw [nColF_self, List.map_map, ← Fin.sum_univ_def]
      refine Finset.sum_eq_zero fun m _ => ?_
      have hm2 : (m : ℕ) ≠ τ.rank + imgPar τ i (q - τ.rank) / 2 := by omega
      simp [posCoord_posVec_fin hq2, hm2]
    · rw [nColF_of_lt_of_ne i hcr hci]
      simp [posCoord_posVec hq2, show c ≠ τ.rank + imgPar τ i (q - τ.rank) / 2 by omega]
  · rw [nColF_of_ge i hcr, nRowF_of_lt i hqr]
    have hne : c ≠ q := by omega
    simp only [hne, ↓reduceIte]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, vecOf_cons,
      vecOf_nil, map_add, map_smul, posCoord_posVec hq, posCoord_posVec hi, smul_eq_mul]
    have h1 : τ.rank + imgPar τ i (c - τ.rank) / 2 ≠ q := by omega
    have h2 : τ.rank + imgPar τ i (c - τ.rank) / 2 ≠ (i : ℕ) := by omega
    simp [h1, h2]
  · rw [nColF_of_ge i hcr, nRowF_of_ge i hqr]
    have hm : c - τ.rank < τ.rootCertificate.roots.length := by rw [dim_eq] at hc; omega
    have hm' : q - τ.rank < τ.rootCertificate.roots.length := by rw [dim_eq] at hq; omega
    have hq3 : τ.rank + τ.rootCertificate.image (q - τ.rank) i < dim τ := by
      have := rootCertificate_image_lt (τ := τ) hm' i
      rw [dim_eq]
      omega
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, vecOf_cons,
      vecOf_nil, map_smul, smul_eq_mul, imgPar_div_two h hm, imgPar_div_two h hm',
      posCoord_posVec hq3]
    by_cases hcq : c = q
    · subst hcq
      simp only [↓reduceIte, mul_one]
      rw [← Int.cast_mul, sgnOf_mul_self, Int.cast_one]
    · have : τ.rootCertificate.image (c - τ.rank) i ≠ τ.rootCertificate.image (q - τ.rank) i := by
        intro he
        have := congrArg (fun m => τ.rootCertificate.image m i) he
        simp only [image_image hm, image_image hm'] at this
        omega
      simp [hcq, this]

theorem coordOf_nColF_comp (h : tabCheck τ = true) (i : Fin τ.rank) {c : ℕ} (hc : c < dim τ) :
    coordOf τ R (nColF τ i c) ∘ₗ (weylElt τ R i 1 : Module.End R (RootModule τ R)) =
      posCoord τ R c := by
  refine Finsupp.lhom_ext fun b z => ?_
  obtain ⟨q, hq, rfl⟩ := posLabel_surjective b
  have hs : Finsupp.single (posLabel q hq) z = z • posVec τ R q := by
    rw [posVec_eq_single hq, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hs, LinearMap.comp_apply, map_smul, map_smul, map_smul,
    coordOf_nColF_weylElt_posVec h i hc hq, posCoord_posVec hq]

theorem entriesOp_conjEntries_mul (h : tabCheck τ = true) (i : Fin τ.rank) {L : List Entry}
    (hL : ValidEntries τ L) :
    entriesOp τ R (conjEntries τ i L) * (weylElt τ R i 1 : Module.End R (RootModule τ R)) =
      (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R L := by
  induction L with
  | nil => simp [conjEntries]
  | cons e L ih =>
    have he := hL e (List.mem_cons_self ..)
    have hcons : conjEntries τ i (e :: L) = ((nColF τ i e.1).flatMap fun x =>
        (nRowF τ i e.2.1).map fun y => (x.1, y.1, x.2 * y.2 * e.2.2)) ++ conjEntries τ i L :=
      List.flatMap_cons ..
    rw [hcons, entriesOp_append, add_mul, ih fun f hf => hL f (List.mem_cons_of_mem _ hf),
      entriesOp_cons, mul_add, entriesOp_conj_single]
    congr 1
    refine LinearMap.ext fun u => ?_
    have hc := congrArg (fun φ => φ u) (coordOf_nColF_comp (R := R) h i he.1)
    simp only [LinearMap.comp_apply] at hc
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, hc,
      map_smul, weylElt_posVec i he.2, nRowF_eq h i he.2]

theorem entriesOp_map_smul (s : ℤ) (L : List Entry) :
    entriesOp τ R (L.map fun e => (e.1, e.2.1, s * e.2.2)) = (s : R) • entriesOp τ R L := by
  induction L with
  | nil => simp
  | cons e L ih =>
    rw [List.map_cons, entriesOp_cons, ih, entriesOp_cons, smul_add, Int.cast_mul, mul_smul]

@[expose] def keyLe (e f : Entry) : Bool :=
  Nat.blt e.1 f.1 || (Nat.beq e.1 f.1 && Nat.ble e.2.1 f.2.1)

@[expose] def mergeF : ℕ → List Entry → List Entry → List Entry
  | 0, l, l' => l ++ l'
  | _ + 1, [], l' => l'
  | _ + 1, e :: l, [] => e :: l
  | f + 1, e :: l, e' :: l' =>
    if keyLe e e' then e :: mergeF f l (e' :: l') else e' :: mergeF f (e :: l) l'

@[expose] def splitAlt : List Entry → List Entry × List Entry
  | [] => ([], [])
  | e :: l => ((splitAlt l).2.cons e, (splitAlt l).1)

@[expose] def msortF : ℕ → List Entry → List Entry
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [e] => [e]
  | f + 1, e :: e' :: l =>
    mergeF (l.length + 2) (msortF f (splitAlt (e :: e' :: l)).1)
      (msortF f (splitAlt (e :: e' :: l)).2)

@[expose] def combineE : List Entry → List Entry
  | [] => []
  | e :: l =>
    match combineE l with
    | [] => [e]
    | e' :: l' =>
      if Nat.beq e.1 e'.1 && Nat.beq e.2.1 e'.2.1 then (e.1, e.2.1, e.2.2 + e'.2.2) :: l'
      else e :: e' :: l'

@[expose] def canonE (L : List Entry) : List Entry :=
  (combineE (msortF 16 L)).filter fun e => e.2.2 != 0

theorem mergeF_perm : ∀ (f : ℕ) (l l' : List Entry), (mergeF f l l').Perm (l ++ l')
  | 0, l, l' => by simp [mergeF]
  | _ + 1, [], l' => by simp [mergeF]
  | _ + 1, e :: l, [] => by simp [mergeF]
  | f + 1, e :: l, e' :: l' => by
    unfold mergeF
    split_ifs
    · exact (mergeF_perm f l (e' :: l')).cons e
    · refine ((mergeF_perm f (e :: l) l').cons e').trans ?_
      simpa using (List.perm_middle (a := e') (l₁ := e :: l) (l₂ := l')).symm

theorem splitAlt_perm : ∀ l : List Entry, ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => by simp [splitAlt]
  | e :: l => by
    simp only [splitAlt, List.cons_append]
    refine List.Perm.cons e ?_
    exact List.perm_append_comm.trans (splitAlt_perm l)

theorem msortF_perm : ∀ (f : ℕ) (l : List Entry), (msortF f l).Perm l
  | 0, l => by simp [msortF]
  | _ + 1, [] => by simp [msortF]
  | _ + 1, [e] => by simp [msortF]
  | f + 1, e :: e' :: l => by
    unfold msortF
    refine (mergeF_perm _ _ _).trans ?_
    exact ((msortF_perm f _).append (msortF_perm f _)).trans (splitAlt_perm _)

theorem entriesOp_perm {L L' : List Entry} (h : L.Perm L') :
    entriesOp τ R L = entriesOp τ R L' :=
  (h.map _).sum_eq

theorem entriesOp_combineE (L : List Entry) : entriesOp τ R (combineE L) = entriesOp τ R L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [combineE]
    revert ih
    generalize combineE L = M
    intro ih
    rw [entriesOp_cons e L, ← ih]
    rcases M with _ | ⟨e', l'⟩
    · rfl
    · simp only
      split_ifs with hk
      · simp only [Bool.and_eq_true] at hk
        have h1 := Nat.eq_of_beq_eq_true hk.1
        have h2 := Nat.eq_of_beq_eq_true hk.2
        rw [entriesOp_cons, entriesOp_cons]
        simp only [← h1, ← h2, Int.cast_add, add_smul, add_assoc]
      · rfl

theorem entriesOp_filter_ne_zero (L : List Entry) :
    entriesOp τ R (L.filter fun e => e.2.2 != 0) = entriesOp τ R L := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [entriesOp_cons, ih, entriesOp_cons]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [ih, entriesOp_cons, h, Int.cast_zero, zero_smul, zero_add]

theorem entriesOp_canonE (L : List Entry) : entriesOp τ R (canonE L) = entriesOp τ R L := by
  rw [canonE, entriesOp_filter_ne_zero, entriesOp_combineE, entriesOp_perm (msortF_perm _ _)]

@[expose] def fastConjCheck (τ : Tag) (a : ℕ) (i : Fin τ.rank) (k : ℕ) : Bool :=
  validB τ (entries τ a k) &&
    canonE (conjEntries τ i (entries τ a k)) ==
      (entries τ (τ.rootCertificate.image a i) k).map fun e =>
        (e.1, e.2.1, signOf τ a i ^ k * e.2.2)

theorem conj_of_fastConjCheck (htab : tabCheck τ = true) {a : ℕ} {i : Fin τ.rank} {k : ℕ}
    (h : fastConjCheck τ a i k = true) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) * entriesOp τ R (entries τ a k) =
      ((signOf τ a i ^ k : ℤ) : R) • (entriesOp τ R (entries τ (τ.rootCertificate.image a i) k) *
        (weylElt τ R i 1 : Module.End R (RootModule τ R))) := by
  simp only [fastConjCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hv, heq⟩ := h
  have hc := congrArg (entriesOp τ R) heq
  rw [entriesOp_canonE, entriesOp_map_smul] at hc
  rw [← entriesOp_conjEntries_mul htab i (validEntries_of_validB hv), hc, smul_mul_assoc]

@[expose] def fastCheckAll (τ : Tag) : Bool :=
  tabCheck τ &&
    ((List.range τ.rootCertificate.roots.length).all fun a => (List.finRange τ.rank).all fun i =>
      [1, 2, 3].all fun k => fastConjCheck τ a i k) &&
    (List.finRange τ.rank).all fun j =>
      [1, 2, 3].all fun k => simpleCheck τ j k && negSimpleCheck τ j k

end CFSG.LieType.Chevalley.RootOps
