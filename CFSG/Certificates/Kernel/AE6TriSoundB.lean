module

public import Certificates.Data.Kernel.AE6Tri.DefsTA
public import CFSG.Certificates.Kernel.AE6TriSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

namespace CFSG.KC.AE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KS.Raw Pointwise

@[expose] def LRep (LB : List Nat) (ℓ : Nat → Equiv.Perm (Fin 360)) : Prop :=
  ∀ a < 168, Orb.PRep 360 9 (nthN LB a) (ℓ a)

@[expose] def prof (ℓ : Nat → Equiv.Perm (Fin 360)) (B : List Nat) (PW : List (List Nat))
    (PO PS PM : List Nat) (y : Nat → Nat) : Prop :=
  ∀ a < PW.length,
    orderOf ((PW.getD a []).map fun j => ℓ (y j)).prod = nthN PO a ∧
    (((PW.getD a []).map fun j => ℓ (y j)).prod ∈ setStab (finOfL B) ↔ nthN PS a = 1) ∧
    ((∃ b < 168, ℓ b = ((PW.getD a []).map fun j => ℓ (y j)).prod) ↔ nthN PM a = 1)

variable {G : List Nat} {g : Nat → Equiv.Perm (Fin 360)}

theorem nthD_getD {α : Type} (d : α) : ∀ (L : List α) (j : Nat), nthD L d j = L.getD j d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: L, j + 1 => nthD_getD d L j

theorem nthN_getD (L : List Nat) (j : Nat) : nthN L j = L.getD j 0 := nthD_getD 0 L j

theorem tlL_eq {α : Type} (L : List α) : tlL L = L.tail := by cases L <;> rfl

theorem isNilL_iff {α : Type} (L : List α) : isNilL L = true ↔ L = [] := by
  cases L with
  | nil => exact iff_of_true rfl rfl
  | cons a t => exact iff_of_false (fun h => Bool.false_ne_true h) (List.cons_ne_nil a t)

theorem inL_iff (L : List Nat) (x : Nat) : inL L x = true ↔ x ∈ L := by
  induction L with
  | nil => exact iff_of_false (fun h => Bool.false_ne_true h) (by simp)
  | cons a L ih =>
    change bIf(Nat.beq a x, true, inL L x) = true ↔ _
    rw [Orb.bIf_eq, List.mem_cons]
    by_cases h : a = x
    · rw [if_pos (by rw [Nat.beq_eq]; exact h)]
      exact iff_of_true rfl (Or.inl h.symm)
    · rw [if_neg (by rw [Nat.beq_eq]; exact h), ih]
      exact ⟨Or.inr, fun h' => h'.resolve_left fun e => h e.symm⟩

theorem endsAt_iff (u : List Nat) (i : Nat) : endsAt u i = true ↔ i ∈ u ∧ ∀ a ∈ u, a ≤ i := by
  unfold endsAt
  rw [Orb.bAnd_eq, Bool.and_eq_true, inL_iff]
  refine and_congr Iff.rfl ?_
  induction u with
  | nil => exact iff_of_true rfl (fun a ha => absurd ha (by simp))
  | cons a u ih =>
    change bAnd(Nat.ble a i, _) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons, Nat.ble_eq]

theorem eqPC_iff : ∀ (pre : List Nat) (r : Nat) (h : List Nat), eqPC pre r h = true ↔ h = pre ++ [r]
  | [], _, [] => iff_of_false (fun e => Bool.false_ne_true e) (by simp)
  | [], r, b :: t => by
    change bAnd(Nat.beq b r, isNilL t) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, isNilL_iff, List.nil_append, List.cons.injEq]
  | _ :: _, _, [] => iff_of_false (fun e => Bool.false_ne_true e) (by simp)
  | a :: pre, r, b :: t => by
    change bAnd(Nat.beq a b, eqPC pre r t) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq, eqPC_iff pre r t, List.cons_append,
      List.cons.injEq]
    exact and_congr eq_comm Iff.rfl

theorem getD_tail' (B : List Nat) (i : Nat) : B.tail.getD i 0 = B.getD (i + 1) 0 := by
  cases B <;> simp

theorem allZ_iff {α : Type} (f : Nat → α → Nat → Bool) : ∀ (A : List α) (B : List Nat) (i₀ : Nat),
    allZ A B f i₀ = true ↔ ∀ i (hi : i < A.length), f (i₀ + i) A[i] (B.getD i 0) = true
  | [], _, _ => iff_of_true rfl (fun i hi => absurd hi (Nat.not_lt_zero _))
  | a :: A, B, i₀ => by
    change bAnd(f i₀ a (nthN B 0), allZ A (tlL B) f (Nat.succ i₀)) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, allZ_iff f A (tlL B) (Nat.succ i₀), nthN_getD, tlL_eq]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i =>
        have e := h1 i (by simpa using hi)
        have e2 : Nat.succ i₀ + i = i₀ + (i + 1) := by omega
        rw [e2, getD_tail'] at e
        simpa using e
    · intro h
      have h0 := h 0 (by simp)
      refine ⟨by simpa using h0, fun i hi => ?_⟩
      have e := h (i + 1) (by simpa using hi)
      have e2 : i₀ + (i + 1) = Nat.succ i₀ + i := by omega
      rw [e2, ← getD_tail'] at e
      simpa using e

theorem allZ_get {α : Type} {f : Nat → α → Nat → Bool} {A : List α} {B : List Nat}
    (h : allZ A B f 0 = true) (i : Nat) (hi : i < A.length) : f i A[i] (B.getD i 0) = true := by
  have e := (allZ_iff f A B 0).1 h i hi
  rwa [Nat.zero_add] at e

theorem allRange_get {α : Type} {L : List α} {f : Nat → α → Bool} {lo hi : Nat}
    (h : allRange L f lo hi = true) {i : Nat} (hi' : i < L.length) (h1 : lo ≤ i) (h2 : i < hi) :
    f i L[i] = true := by
  have e := (allIx_iff L _ 0).1 h i hi'
  rw [Nat.zero_add, Orb.bIf_eq (Nat.blt i lo), if_neg (by rw [Nat.blt_eq]; omega),
    Orb.bIf_eq (Nat.blt i hi), if_pos (by rw [Nat.blt_eq]; exact h2)] at e
  exact e

theorem anyIx_ex {α : Type} {L : List α} {f : Nat → α → Bool} (h : anyIx L f 0 = true) :
    ∃ i, ∃ hi : i < L.length, f i L[i] = true := by
  unfold anyIx at h
  rw [notB_eq, Bool.not_eq_true'] at h
  by_contra hne
  push Not at hne
  have e : allIx L (fun i a => notB (f i a)) 0 = true := (allIx_iff _ _ 0).2 fun i hi => by
    rw [Nat.zero_add, notB_eq, Bool.not_eq_true']
    exact Bool.eq_false_iff.2 (hne i hi)
  rw [e] at h
  exact Bool.noConfusion h

theorem lettersIn_iff (L : Nat) (w : List Nat) :
    lettersIn L w = true ↔ ∀ c ∈ w, bit L c = true := by
  induction w with
  | nil => exact iff_of_true rfl (fun c hc => absurd hc (by simp))
  | cons c w ih =>
    change bAnd(bit L c, lettersIn L w) = true ↔ _
    rw [Orb.bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem lettersIn_append {L : Nat} {u v : List Nat} (hu : lettersIn L u = true)
    (hv : lettersIn L v = true) : lettersIn L (u ++ v) = true := by
  rw [lettersIn_iff] at hu hv ⊢
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · exact hu c hc
  · exact hv c hc

theorem nthN_map_lt (f : Nat → Nat) {L : List Nat} {j : Nat} (hj : j < L.length) :
    nthN (L.map f) j = f (nthN L j) := by
  rw [nthN_getD, nthN_getD, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
    List.getD_eq_getElem _ _ hj]

theorem nthN_map_ge (f : Nat → Nat) {L : List Nat} {j : Nat} (hj : L.length ≤ j) :
    nthN (L.map f) j = 0 := by
  rw [nthN_getD, List.getD_eq_default _ _ (by simpa using hj)]

theorem nthN_map_range (f : Nat → Nat) {n t : Nat} (ht : t < n) :
    nthN ((List.range n).map f) t = f t := by
  rw [nthN_map_lt f (by simpa using ht), nthN_getD, List.getD_eq_getElem _ _ (by simpa using ht),
    List.getElem_range]

theorem tw_append (TAU : Nat) (u v : List Nat) (a : Nat) :
    tw TAU (u ++ v) a = tw TAU u (tw TAU v a) := by
  induction u with
  | nil => rfl
  | cons d u ihu =>
    change tq TAU d (tw TAU (u ++ v) a) = tq TAU d (tw TAU u (tw TAU v a))
    rw [ihu]

theorem prep_inj {P : Nat} {x y : Equiv.Perm (Fin 360)} (hx : Orb.PRep 360 9 P x)
    (hy : Orb.PRep 360 9 P y) : x = y :=
  Equiv.ext fun i => Fin.ext ((hx i).symm.trans (hy i))

theorem prep_conj {X Y C : Nat} {x c : Equiv.Perm (Fin 360)} (hX : Orb.PRep 360 9 X x)
    (hC : Orb.PRep 360 9 C c)
    (h : allN 360 (fun i => Nat.beq (ap Y (ap C i)) (ap C (ap X i))) = true) :
    Orb.PRep 360 9 Y (c * x * c⁻¹) := fun z => by
  have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h _ (c⁻¹ z).2)
  unfold ap at e
  have hz : c (c⁻¹ z) = z := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [hC, hX, hC, hz] at e
  exact e

theorem ap_zero (x : Nat) : ap 0 x = 0 := by
  have e1 : ∀ n, Nat.shiftRight 0 n = 0 := Nat.zero_shiftRight
  have e2 : ∀ m, Nat.land 0 m = 0 := Nat.zero_and
  unfold ap pg
  rw [e1, e2]

theorem pP_eq {t : Nat → Nat} {σ : Nat → Equiv.Perm (Fin 360)} :
    ∀ u : List Nat, (∀ j ∈ u, Orb.PRep 360 9 (t j) (σ j)) → ∀ x : Fin 360,
      pP t u x = ((u.map σ).prod x : Nat)
  | [], _, _ => rfl
  | j :: u, h, x => by
    change ap (t j) (pP t u x) = _
    rw [pP_eq u (fun j' hj' => h j' (List.mem_cons_of_mem _ hj')) x, List.map_cons,
      List.prod_cons, Equiv.Perm.mul_apply]
    exact h j (by simp) _

theorem pK_eq {t : Nat → Nat} {σ : Nat → Equiv.Perm (Fin 360)} (u : List Nat)
    (h : ∀ j ∈ u, Orb.PRep 360 9 (t j) (σ j)) :
    ∀ (k : Nat) (x : Fin 360), pK t u k x = ((((u.map σ).prod) ^ k) x : Nat)
  | 0, x => by
    rw [pow_zero]
    rfl
  | k + 1, x => by
    change pP t u (pK t u k x) = _
    rw [pK_eq u h k x, pP_eq u h, pow_succ', Equiv.Perm.mul_apply]

theorem pP_const {t : Nat → Nat} : ∀ u : List Nat, (∃ j ∈ u, t j = 0) → ∃ K, ∀ x, pP t u x = K
  | [], ⟨_, hj, _⟩ => absurd hj (by simp)
  | j :: u, ⟨j', hj', ht⟩ => by
    by_cases hj : t j = 0
    · refine ⟨0, fun x => ?_⟩
      change ap (t j) (pP t u x) = 0
      rw [hj, ap_zero]
    · rcases List.mem_cons.1 hj' with rfl | hj'
      · exact absurd ht hj
      · obtain ⟨K, hK⟩ := pP_const u ⟨j', hj', ht⟩
        refine ⟨ap (t j) K, fun x => ?_⟩
        change ap (t j) (pP t u x) = _
        rw [hK]

theorem o248 {o : Nat} (h : bIf(Nat.beq o 2, true, bIf(Nat.beq o 4, true, Nat.beq o 8)) = true) :
    o = 2 ∨ o = 4 ∨ o = 8 := by
  rw [Orb.bIf_eq, Orb.bIf_eq] at h
  split_ifs at h with h2 h4
  · exact Or.inl (Nat.eq_of_beq_eq_true h2)
  · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h4))
  · exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true h))

theorem orderOf_of_pows {P : Equiv.Perm (Fin 360)} {o : Nat} (ho : o = 2 ∨ o = 4 ∨ o = 8)
    (h1 : P ^ o = 1) (h2 : P ^ (o / 2) ≠ 1) : orderOf P = o := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases ho with rfl | rfl | rfl
  · exact orderOf_eq_prime_pow (p := 2) (n := 0) h2 h1
  · exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h1
  · exact orderOf_eq_prime_pow (p := 2) (n := 2) h2 h1

theorem orderOf_conjB (V x : Equiv.Perm (Fin 360)) : orderOf (V * x * V⁻¹) = orderOf x := by
  have e := orderOf_injective (MulAut.conj V).toMonoidHom (MulAut.conj V).injective x
  simpa [MulAut.conj_apply] using e

theorem stab_of_maps {P : Equiv.Perm (Fin 360)} {B : List Nat}
    (h : ∀ x : Fin 360, x.val ∈ B → (P x).val ∈ B) : P ∈ setStab (finOfL B) := by
  classical
  have hO := inv_maps (O := Finset.univ.filter fun q : Fin 360 => q.val ∈ B) (x := P)
    (by simpa using h)
  rw [setStab, MulAction.mem_stabilizer_iff]
  ext y
  simp only [Set.mem_smul_set, finOfL, Set.mem_setOf_eq, Equiv.Perm.smul_def]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact h z hz
  · intro hy
    refine ⟨P⁻¹ y, ?_, by simp⟩
    simpa using hO y (by simpa using hy)

theorem maps_of_stab {P : Equiv.Perm (Fin 360)} {B : List Nat} (h : P ∈ setStab (finOfL B))
    (x : Fin 360) (hx : x.val ∈ B) : (P x).val ∈ B := by
  rw [setStab, MulAction.mem_stabilizer_iff] at h
  have e : P • x ∈ P • finOfL B := Set.smul_mem_smul_set hx
  rw [h] at e
  exact e

theorem stab_of_allN {B : List Nat} {f : Nat → Nat} {P : Equiv.Perm (Fin 360)}
    (hf : ∀ x : Fin 360, f x = (P x : Nat))
    (h : allN 360 (fun x => bIf(bit (maskL B) x, bit (maskL B) (f x), true)) = true) :
    P ∈ setStab (finOfL B) :=
  stab_of_maps fun x hx => by
    have e := Orb.allN_iff.1 h x x.2
    beta_reduce at e
    rw [Orb.bIf_eq, if_pos ((bit_maskL B x).2 hx), bit_maskL, hf x] at e
    exact e

theorem not_stab {B : List Nat} (hB : ∀ x ∈ B, x < 360) {f : Nat → Nat}
    {P : Equiv.Perm (Fin 360)} (hf : ∀ x : Fin 360, f x = (P x : Nat)) {x : Nat}
    (h1 : bit (maskL B) x = true) (h2 : notB (bit (maskL B) (f x)) = true) :
    P ∉ setStab (finOfL B) := by
  intro hP
  rw [bit_maskL] at h1
  have e := maps_of_stab hP ⟨x, hB x h1⟩ h1
  have e2 : f x = (P ⟨x, hB x h1⟩ : Nat) := hf ⟨x, hB x h1⟩
  rw [← bit_maskL B] at e
  rw [notB_eq, Bool.not_eq_true', e2, e] at h2
  exact Bool.noConfusion h2

theorem eq_of_allN {Y : Nat} {y P : Equiv.Perm (Fin 360)} (hY : Orb.PRep 360 9 Y y) {f : Nat → Nat}
    (hf : ∀ x : Fin 360, f x = (P x : Nat))
    (h : allN 360 (fun x => Nat.beq (f x) (ap Y x)) = true) : y = P :=
  Equiv.ext fun x => Fin.ext (by
    rw [← hY x, ← hf x]
    exact (Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h x x.2)).symm)

theorem sepAll_sound {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {t : Nat → Nat} {u r : List Nat} {P : Equiv.Perm (Fin 360)}
    (hP : ∀ x : Fin 360, pP t u x = (P x : Nat)) (h : sepAll LB t u r = true) :
    ∀ b < 168, ℓ b ≠ P := by
  unfold sepAll at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, lenL_eq] at h
  obtain ⟨hl, h⟩ := h
  have hl' := Nat.eq_of_beq_eq_true hl
  intro b hb hbP
  have e := allZ_get h b (by omega)
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq, notB_eq, Bool.not_eq_true'] at e
  obtain ⟨hy, hne⟩ := e
  have e1 : pP t u r[b] = (P ⟨r[b], hy⟩ : Nat) := hP ⟨r[b], hy⟩
  have e2 : ap (LB.getD b 0) r[b] = (ℓ b ⟨r[b], hy⟩ : Nat) := by
    rw [← nthN_getD]
    exact hℓ b hb ⟨r[b], hy⟩
  rw [e1, e2, hbP, Nat.beq_refl] at hne
  exact Bool.noConfusion hne

theorem wv_appendB (g : Nat → Equiv.Perm (Fin 360)) (u v : List Nat) :
    wv g (u ++ v) = wv g u * wv g v := by
  simp [wv, List.prod_append]

theorem wv_replicate (g : Nat → Equiv.Perm (Fin 360)) (n c : Nat) :
    wv g (List.replicate n c) = g c ^ n := by
  simp [wv, List.map_replicate, List.prod_replicate]

theorem wv_inv_word {MM : Nat} : ∀ w : List Nat, lettersIn MM w = true →
    ∃ w', lettersIn MM w' = true ∧ wv g w' = (wv g w)⁻¹
  | [], _ => ⟨[], rfl, by rw [wv_nil, inv_one]⟩
  | c :: w, h => by
    change bAnd(bit MM c, lettersIn MM w) = true at h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨w', h1, h2⟩ := wv_inv_word w h.2
    refine ⟨w' ++ List.replicate (orderOf (g c) - 1) c, lettersIn_append h1 ?_, ?_⟩
    · rw [lettersIn_iff]
      intro d hd
      rw [List.eq_of_mem_replicate hd]
      exact h.1
    · rw [wv_appendB, h2, wv_cons, mul_inv_rev, wv_replicate]
      congr 1
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos (g c)), pow_orderOf_eq_one]

theorem wv_stab {MM : Nat} (hMM : MM < 256) {B : List Nat}
    (hMB : ∀ c < 8, bit MM c = true → g c ∈ setStab (finOfL B)) :
    ∀ w : List Nat, lettersIn MM w = true → wv g w ∈ setStab (finOfL B)
  | [], _ => Subgroup.one_mem _
  | c :: w, h => by
    change bAnd(bit MM c, lettersIn MM w) = true at h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h
    rw [wv_cons]
    exact Subgroup.mul_mem _ (hMB c (bit_lt8 hMM h.1) h.1) (wv_stab hMM hMB w h.2)

theorem tw_sound {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} {TAU MM : Nat} (hMM : MM < 256)
    (hτ : ∀ c < 8, bit MM c = true → ∀ a < 168,
      tq TAU c a < 168 ∧ ℓ (tq TAU c a) = g c * ℓ a * (g c)⁻¹) :
    ∀ w : List Nat, lettersIn MM w = true → ∀ a < 168,
      tw TAU w a < 168 ∧ ℓ (tw TAU w a) = wv g w * ℓ a * (wv g w)⁻¹
  | [], _, a, ha => ⟨ha, by rw [wv_nil, one_mul, inv_one, mul_one]; rfl⟩
  | c :: w, h, a, ha => by
    change bAnd(bit MM c, lettersIn MM w) = true at h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := tw_sound (LB := LB) hMM hτ w h.2 a ha
    change tq TAU c (tw TAU w a) < 168 ∧ ℓ (tq TAU c (tw TAU w a)) = _
    obtain ⟨h3, h4⟩ := hτ c (bit_lt8 hMM h.1) h.1 _ h1
    refine ⟨h3, ?_⟩
    rw [h4, h2, wv_cons, mul_inv_rev]
    simp only [mul_assoc]

theorem prod_conj (V : Equiv.Perm (Fin 360)) {f f' : Nat → Equiv.Perm (Fin 360)} :
    ∀ u : List Nat, (∀ j ∈ u, f j = V * f' j * V⁻¹) →
      (u.map f).prod = V * (u.map f').prod * V⁻¹
  | [], _ => by simp
  | j :: u, h => by
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, h j (by simp),
      prod_conj V u (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem prof_conj {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} {TAU MM : Nat}
    (hMM : MM < 256)
    (hτ : ∀ c < 8, bit MM c = true → ∀ a < 168,
      tq TAU c a < 168 ∧ ℓ (tq TAU c a) = g c * ℓ a * (g c)⁻¹)
    {B : List Nat} (hMB : ∀ c < 8, bit MM c = true → g c ∈ setStab (finOfL B))
    {PW : List (List Nat)} {PO PS PM : List Nat} {y z : Nat → Nat}
    (hy : prof ℓ B PW PO PS PM y) {W : List Nat} (hW : lettersIn MM W = true) {a : Nat}
    (ha : a < PW.length)
    (hz : ∀ j ∈ PW.getD a [], ℓ (z j) = wv g W * ℓ (y j) * (wv g W)⁻¹) :
    orderOf ((PW.getD a []).map fun j => ℓ (z j)).prod = nthN PO a ∧
    (((PW.getD a []).map fun j => ℓ (z j)).prod ∈ setStab (finOfL B) ↔ nthN PS a = 1) ∧
    ((∃ b < 168, ℓ b = ((PW.getD a []).map fun j => ℓ (z j)).prod) ↔ nthN PM a = 1) := by
  obtain ⟨ho, hs, hm⟩ := hy a ha
  rw [prod_conj (wv g W) _ hz]
  generalize ((PW.getD a []).map fun j => ℓ (y j)).prod = P at ho hs hm
  have hV := wv_stab hMM hMB W hW
  refine ⟨by rw [orderOf_conjB]; exact ho, ?_, ?_⟩
  · rw [Subgroup.mul_mem_cancel_right _ (Subgroup.inv_mem _ hV),
      Subgroup.mul_mem_cancel_left _ hV]
    exact hs
  · rw [← hm]
    constructor
    · rintro ⟨b, hb, e⟩
      obtain ⟨W', hW', e'⟩ := wv_inv_word (g := g) W hW
      obtain ⟨h1, h2⟩ := tw_sound (LB := LB) hMM hτ W' hW' b hb
      refine ⟨tw TAU W' b, h1, ?_⟩
      rw [h2, e, e', inv_inv]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel, mul_one]
    · rintro ⟨b, hb, e⟩
      obtain ⟨h1, h2⟩ := tw_sound (LB := LB) hMM hτ W hW b hb
      exact ⟨tw TAU W b, h1, by rw [h2, e]⟩

theorem witOK_false {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {B : List Nat} (hB : ∀ x ∈ B, x < 360) {PW : List (List Nat)} {PO PS PM : List Nat}
    {t : Nat → Nat} {σ : Nat → Equiv.Perm (Fin 360)} {i : Nat}
    (ht : ∀ j ≤ i, Orb.PRep 360 9 (t j) (σ j))
    (hprof : ∀ a < PW.length, (∀ j ∈ PW.getD a [], j ≤ i) →
      orderOf ((PW.getD a []).map σ).prod = nthN PO a ∧
      (((PW.getD a []).map σ).prod ∈ setStab (finOfL B) ↔ nthN PS a = 1) ∧
      ((∃ b < 168, ℓ b = ((PW.getD a []).map σ).prod) ↔ nthN PM a = 1))
    {e : List Nat} (h : witOK LB (maskL B) PW PO PS PM t i e = true) : False := by
  unfold witOK at h
  beta_reduce at h
  generalize tlL (tlL e) = r at h
  generalize nthN e 0 = tag at h
  generalize nthN e 1 = a at h
  generalize nthN r 0 = x at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, endsAt_iff, nthD_getD] at h
  obtain ⟨⟨hiu, hle⟩, h⟩ := h
  have ha : a < PW.length := by
    by_contra hna
    rw [List.getD_eq_default _ _ (by omega)] at hiu
    exact absurd hiu (by simp)
  have ht' : ∀ j ∈ PW.getD a [], Orb.PRep 360 9 (t j) (σ j) := fun j hj => ht j (hle j hj)
  obtain ⟨ho, hs, hm⟩ := hprof a ha hle
  generalize hu : PW.getD a [] = u at ht' ho hs hm h
  have hP := pP_eq u ht'
  have hK := pK_eq u ht'
  generalize ((u.map σ).prod) = P at hP hK ho hs hm
  by_cases h1 : Nat.beq tag 1 = true
  · rw [Orb.bIf_eq (Nat.beq tag 1), if_pos h1, Orb.bAnd_eq, Bool.and_eq_true, notB_eq,
      Bool.not_eq_true'] at h
    have hx : x < 360 := by simpa [Nat.blt_eq] using h.1
    have hpo : P ^ nthN PO a = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one P
    have e1 : pK t u (nthN PO a) x = x := by
      have e2 := hK (nthN PO a) ⟨x, hx⟩
      rw [hpo] at e2
      exact e2
    rw [e1, Nat.beq_refl] at h
    exact Bool.noConfusion h.2
  rw [Orb.bIf_eq (Nat.beq tag 1), if_neg h1] at h
  by_cases h2 : Nat.beq tag 2 = true
  · rw [Orb.bIf_eq (Nat.beq tag 2), if_pos h2, Orb.bAnd_eq, Bool.and_eq_true] at h
    have h1o : 1 < nthN PO a := by simpa [Nat.blt_eq] using h.1
    have hpw : P ^ (Nat.shiftRight (nthN PO a) 1) = 1 := Equiv.ext fun z => Fin.ext (by
      rw [← hK]
      exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h.2 z z.2))
    have hd := orderOf_dvd_of_pow_eq_one hpw
    rw [ho, Orb.shr_eq, pow_one] at hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  rw [Orb.bIf_eq (Nat.beq tag 2), if_neg h2] at h
  by_cases h3 : Nat.beq tag 3 = true
  · rw [Orb.bIf_eq (Nat.beq tag 3), if_pos h3] at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    exact not_stab hB hP h.2.1 h.2.2 (hs.2 (Nat.eq_of_beq_eq_true h.1))
  rw [Orb.bIf_eq (Nat.beq tag 3), if_neg h3] at h
  by_cases h4 : Nat.beq tag 4 = true
  · rw [Orb.bIf_eq (Nat.beq tag 4), if_pos h4] at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true, notB_eq, Bool.not_eq_true'] at h
    have hps := hs.1 (stab_of_allN hP h.2)
    rw [hps, Nat.beq_refl] at h
    exact Bool.noConfusion h.1
  rw [Orb.bIf_eq (Nat.beq tag 4), if_neg h4] at h
  by_cases h5 : Nat.beq tag 5 = true
  · rw [Orb.bIf_eq (Nat.beq tag 5), if_pos h5] at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true, notB_eq, Bool.not_eq_true', Orb.strictB_eq,
      Nat.blt_eq] at h
    obtain ⟨hpm, hx, hY⟩ := h
    have hpm' := hm.1 ⟨x, hx, eq_of_allN (hℓ x hx) hP hY⟩
    rw [hpm', Nat.beq_refl] at hpm
    exact Bool.noConfusion hpm
  rw [Orb.bIf_eq (Nat.beq tag 5), if_neg h5] at h
  by_cases h6 : Nat.beq tag 6 = true
  · rw [Orb.bIf_eq (Nat.beq tag 6), if_pos h6, Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨b, hb, e⟩ := hm.2 (Nat.eq_of_beq_eq_true h.1)
    exact sepAll_sound hℓ hP h.2 b hb e
  rw [Orb.bIf_eq (Nat.beq tag 6), if_neg h6] at h
  exact Bool.noConfusion h

theorem lOK_sound (hG : GRep G g) {LB : List Nat} {TAU : Nat} {EL TP TC kw : List Nat}
    (h : lOK G LB TAU EL TP TC kw = true) :
    ∃ ℓ : Nat → Equiv.Perm (Fin 360), LRep LB ℓ ∧ ℓ 0 = wv g kw ∧
      (∀ c ∈ EL, ∀ a < 168, tq TAU c a < 168 ∧ ℓ (tq TAU c a) = g c * ℓ a * (g c)⁻¹) ∧
      ∀ a < 168, ∃ w : List Nat, (∀ c ∈ w, c ∈ EL) ∧ ℓ a = wv g w * ℓ 0 * (wv g w)⁻¹ := by
  unfold lOK at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Orb.strictB_eq] at h
  obtain ⟨hlen, h0, hTP, -, htree, hEL⟩ := h
  have hLB : LB.length = 168 := by
    rw [← lenL_eq]
    exact Nat.eq_of_beq_eq_true hlen
  have hP0 : Orb.PRep 360 9 (nthN LB 0) (wv g kw) := fun z => by
    have e := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 h0 z z.2)
    rw [ptW_eq hG] at e
    exact e
  have hconj : ∀ c ∈ EL, ∀ a < 168, ∀ x : Equiv.Perm (Fin 360), Orb.PRep 360 9 (nthN LB a) x →
      tq TAU c a < 168 ∧ Orb.PRep 360 9 (nthN LB (tq TAU c a)) (g c * x * (g c)⁻¹) := by
    intro c hc a ha x hx
    obtain ⟨_, e⟩ := allIx_mem hEL c hc
    have e2 := allIx_getD 0 e a (by rw [hLB]; exact ha)
    rw [← nthN_getD] at e2
    simp only [Bool.and_eq_true, Nat.blt_eq] at e2
    exact ⟨e2.1, prep_conj hx (hG c) e2.2⟩
  have htr : ∀ i < 168, ∃ w : List Nat, (∀ c ∈ w, c ∈ EL) ∧
      Orb.PRep 360 9 (nthN LB i) (wv g w * wv g kw * (wv g w)⁻¹) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      cases i with
      | zero =>
        refine ⟨[], fun c hc => absurd hc (by simp), ?_⟩
        rw [wv_nil, one_mul, inv_one, mul_one]
        exact hP0
      | succ k =>
        have hk : k < TP.length := by
          rw [← lenL_eq, Nat.eq_of_beq_eq_true hTP]
          omega
        have e := (allIx_iff TP _ 1).1 htree k hk
        simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, inL_iff, Nat.sub_eq,
          Nat.add_sub_cancel_left] at e
        obtain ⟨hp, hc, hq⟩ := e
        obtain ⟨w, hw, hpw⟩ := ih TP[k] (by omega) (by omega)
        have hq' : tq TAU (nthN TC k) TP[k] = k + 1 := by omega
        have e2 := (hconj _ hc _ (by omega) _ hpw).2
        rw [hq'] at e2
        refine ⟨nthN TC k :: w, fun c hc' => ?_, ?_⟩
        · rcases List.mem_cons.1 hc' with rfl | hc'
          · exact hc
          · exact hw c hc'
        · rw [wv_cons, mul_inv_rev]
          simpa only [mul_assoc] using e2
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Nat → Equiv.Perm (Fin 360), LRep LB ℓ :=
    ⟨fun a => if ha : a < 168 then wv g (htr a ha).choose * wv g kw * (wv g (htr a ha).choose)⁻¹
      else 1, fun a ha => by
        dsimp only
        rw [dif_pos ha]
        exact (htr a ha).choose_spec.2⟩
  have hl0 : ℓ 0 = wv g kw := prep_inj (hℓ 0 (by norm_num)) hP0
  refine ⟨ℓ, hℓ, hl0, fun c hc a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := hconj c hc a ha (ℓ a) (hℓ a ha)
    exact ⟨h1, prep_inj (hℓ _ h1) h2⟩
  · obtain ⟨w, hw, hpw⟩ := htr a ha
    exact ⟨w, hw, by rw [hl0]; exact prep_inj (hℓ a ha) hpw⟩

theorem vOK_sound {LB D : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {d : Nat → Equiv.Perm (Fin 360)} (hD : GRep D d) {ws : List (List Nat)} {ps : List Nat}
    (h : vOK LB D ws ps = true) :
    ∀ i < ws.length, nthN ps i < 168 ∧ ℓ (nthN ps i) = wv d (ws.getD i []) := by
  unfold vOK at h
  intro i hi
  have e := allIx_getD [] h i hi
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, (eqN_iff (hℓ _ e.1) (prep_wv hD _)).1 e.2⟩

theorem vOKd_sound {LB D : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {d : Nat → Equiv.Perm (Fin 360)} (hD : GRep D d) {DL ws : List (List Nat)} {ps : List Nat}
    (h : vOKd LB D DL ws ps = true) :
    ∀ i < ws.length, nthN ps i < 168 ∧
      ℓ (nthN ps i) = ((ws.getD i []).map fun c => wv d (DL.getD c [])).prod := by
  unfold vOKd at h
  rw [forceMap_eq] at h
  exact vOK_sound hℓ (prep_mapAw hD DL) h

theorem vOKdd_sound {LB D : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {d : Nat → Equiv.Perm (Fin 360)} (hD : GRep D d) {DLa DLb ws : List (List Nat)}
    {ps : List Nat} (h : vOKdd LB D DLa DLb ws ps = true) :
    ∀ i < ws.length, nthN ps i < 168 ∧
      ℓ (nthN ps i) = ((ws.getD i []).map fun c =>
        ((DLb.getD c []).map fun c' => wv d (DLa.getD c' [])).prod).prod := by
  unfold vOKdd at h
  rw [forceMap_eq] at h
  exact vOKd_sound hℓ (prep_mapAw hD DLa) h

theorem tOK_sound {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep LB ℓ)
    {B : List Nat} (hB : ∀ x ∈ B, x < 360) {PW : List (List Nat)} {PO PS PM tI : List Nat}
    {TW : List (List (List Nat))} (h : tOK LB (maskL B) PW PO PS PM tI TW = true) :
    (∀ j < tI.length, nthN tI j < 168) ∧ prof ℓ B PW PO PS PM (nthN tI) := by
  unfold tOK at h
  rw [Orb.bAnd_eq, Bool.and_eq_true, forceMap_eq] at h
  obtain ⟨hI, h⟩ := h
  beta_reduce at h
  have hlt : ∀ j < tI.length, nthN tI j < 168 := fun j hj => by
    have e := allIx_getD 0 hI j hj
    rw [← nthN_getD] at e
    simpa only [Nat.blt_eq] using e
  refine ⟨hlt, fun a ha => ?_⟩
  have e := allIx_getD [] h a ha
  beta_reduce at e
  simp only [Orb.bAnd_eq, Bool.and_eq_true] at e
  obtain ⟨ho, hpow, hwit, hS, hM⟩ := e
  have ht : ∀ j < tI.length, Orb.PRep 360 9 (nthN (tI.map (nthN LB)) j) (ℓ (nthN tI j)) :=
    fun j hj => by
      rw [nthN_map_lt _ hj]
      exact hℓ _ (hlt j hj)
  have ht0 : ∀ j, tI.length ≤ j → nthN (tI.map (nthN LB)) j = 0 := fun j hj => nthN_map_ge _ hj
  generalize nthN (tI.map (nthN LB)) = t at ht ht0 hpow hwit hS hM
  generalize PW.getD a [] = u at hpow hwit hS hM ⊢
  have ho' := o248 ho
  have hin : ∀ j ∈ u, j < tI.length := by
    by_contra hne
    push Not at hne
    obtain ⟨j, hj, hj'⟩ := hne
    obtain ⟨K, hK⟩ := pP_const u ⟨j, hj, ht0 j hj'⟩
    obtain ⟨o', hoo⟩ : ∃ o', nthN PO a = o' + 1 := ⟨nthN PO a - 1, by omega⟩
    have e0 := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hpow 0 (by norm_num))
    have e1 := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hpow 1 (by norm_num))
    rw [hoo] at e0 e1
    have k0 : pK t u (o' + 1) 0 = K := hK _
    have k1 : pK t u (o' + 1) 1 = K := hK _
    omega
  have ht' : ∀ j ∈ u, Orb.PRep 360 9 (t j) ((fun j => ℓ (nthN tI j)) j) :=
    fun j hj => ht j (hin j hj)
  have hP := pP_eq u ht'
  have hK := pK_eq u ht'
  generalize (u.map fun j => ℓ (nthN tI j)).prod = P at hP hK ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply orderOf_of_pows ho'
    · exact Equiv.ext fun z => Fin.ext (by
        rw [← hK]
        exact Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hpow z z.2))
    · intro h1
      simp only [Nat.blt_eq, notB_eq, Bool.not_eq_true'] at hwit
      obtain ⟨hx, hne⟩ := hwit
      have h1' : P ^ (Nat.shiftRight (nthN PO a) 1) = 1 := by
        rw [Orb.shr_eq, pow_one]
        exact h1
      have e2 := hK (Nat.shiftRight (nthN PO a) 1) ⟨_, hx⟩
      rw [h1'] at e2
      have e3 : pK t u (Nat.shiftRight (nthN PO a) 1) (nthN (nthD (nthD TW [] a) [] 0) 0) =
          nthN (nthD (nthD TW [] a) [] 0) 0 := e2
      rw [e3, Nat.beq_refl] at hne
      exact Bool.noConfusion hne
  · rw [Orb.bIf_eq (Nat.beq (nthN PS a) 1)] at hS
    split_ifs at hS with hps
    · exact iff_of_true (stab_of_allN hP hS) (Nat.eq_of_beq_eq_true hps)
    · simp only [Bool.and_eq_true] at hS
      exact iff_of_false (not_stab hB hP hS.1 hS.2) (fun e => hps (by rw [e]; rfl))
  · rw [Orb.bIf_eq (Nat.beq (nthN PM a) 1)] at hM
    split_ifs at hM with hpm
    · simp only [Bool.and_eq_true, Nat.blt_eq, Orb.strictB_eq] at hM
      exact iff_of_true ⟨_, hM.1, eq_of_allN (hℓ _ hM.1) hP hM.2⟩ (Nat.eq_of_beq_eq_true hpm)
    · exact iff_of_false (fun ⟨b, hb, e⟩ => sepAll_sound hℓ hP hM b hb e)
        (fun e => hpm (by rw [e]; rfl))

theorem sOK_sound (hG : GRep G g) {LB : List Nat} {ℓ : Nat → Equiv.Perm (Fin 360)}
    (hℓ : LRep LB ℓ) {TAU MM : Nat} (hMM : MM < 256)
    (hτ : ∀ c < 8, bit MM c = true → ∀ a < 168,
      tq TAU c a < 168 ∧ ℓ (tq TAU c a) = g c * ℓ a * (g c)⁻¹)
    {B : List Nat} (hMB : ∀ c < 8, bit MM c = true → g c ∈ setStab (finOfL B))
    {PW : List (List Nat)} {PO PS PM : List Nat} {sI : List (List Nat)}
    (hsI : ∀ j < 6, ∀ t < 6, nthN (nthD sI [] j) t < 168) {nodes : List (List (List Nat))}
    (hne : nodes ≠ []) (n : Nat) (hn : nodes.length ≤ 30 * n)
    (h : ∀ k < n, sOK LB TAU MM B PW PO PS PM sI nodes (30 * k) (30 * k + 30) = true) :
    ∀ y : Nat → Nat, (∀ t < 6, y t < 168) → prof ℓ B PW PO PS PM y →
      ∃ w : List Nat, lettersIn MM w = true ∧ ∃ j < 6, ∀ t < 6,
        wv g w * ℓ (nthN (nthD sI [] j) t) * (wv g w)⁻¹ = ℓ (y t) := by
  intro y hy hprof
  have hn0 : 0 < n := by
    have := List.length_pos_iff_ne_nil.2 hne
    omega
  have hb0 := h 0 hn0
  unfold sOK at hb0
  rw [Orb.strictB_eq] at hb0
  beta_reduce at hb0
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true] at hb0
  obtain ⟨hBc, hroot, -⟩ := hb0
  have hB : ∀ x ∈ B, x < 360 := fun x hx => by
    obtain ⟨_, e⟩ := allIx_mem hBc x hx
    simpa only [Nat.blt_eq] using e
  have hnode : ∀ nd ∈ nodes, nodeOK LB TAU MM (maskL B) PW PO PS PM sI nodes nd = true := by
    intro nd hnd
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hnd
    have e := h (m / 30) (by omega)
    unfold sOK at e
    rw [Orb.strictB_eq] at e
    beta_reduce at e
    rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.bAnd_eq, Bool.and_eq_true] at e
    exact allRange_get e.2.2 hm (by omega) (by omega)
  have htw := tw_sound (LB := LB) (g := g) hMM hτ
  have main : ∀ i ≤ 6, ∃ W : List Nat, lettersIn MM W = true ∧ ∃ nd ∈ nodes,
      nthD nd [] 0 = (List.range i).map fun t => tw TAU W (y t) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨nd0, rest, hnr⟩ := List.exists_cons_of_ne_nil hne
      subst hnr
      refine ⟨[], rfl, nd0, by simp, ?_⟩
      rw [List.range_zero, List.map_nil]
      exact (isNilL_iff _).1 hroot
    | succ i ih =>
      intro hi
      obtain ⟨W, hW, nd, hnd, hpre⟩ := ih (by omega)
      have e := hnode nd hnd
      unfold nodeOK at e
      beta_reduce at e
      rw [hpre] at e
      generalize hpr : (List.range i).map (fun t => tw TAU W (y t)) = pre at e
      have hpl : pre.length = i := by rw [← hpr, List.length_map, List.length_range]
      have hpt : ∀ t < i, nthN pre t = tw TAU W (y t) := fun t ht => by
        rw [← hpr]
        exact nthN_map_range _ ht
      rw [lenL_eq, hpl, Orb.bIf_eq (Nat.beq i 6), if_neg (by rw [Nat.beq_eq]; omega)] at e
      simp only [Orb.bAnd_eq, Bool.and_eq_true, lenL_eq, forceMap_eq, hpl] at e
      obtain ⟨-, -, hents, hz, hR⟩ := e
      generalize nthD nd [] 1 = R at hz hR
      generalize tlL (tlL nd) = ents at hents hz
      have hc := htw W hW (y i) (hy i (by omega))
      have e := allZ_get hz (tw TAU W (y i)) (by rw [Nat.eq_of_beq_eq_true hents]; exact hc.1)
      rw [← nthN_getD] at e
      beta_reduce at e
      rw [Orb.bIf_eq] at e
      split_ifs at e with htag
      · simp only [Bool.and_eq_true] at e
        obtain ⟨hw, hfix, hr⟩ := e
        rw [inL_iff] at hr
        obtain ⟨_, e2⟩ := allIx_mem hR _ hr
        obtain ⟨m, hm, e3⟩ := anyIx_ex e2
        rw [eqPC_iff] at e3
        refine ⟨_ ++ W, lettersIn_append hw hW, nodes[m], List.getElem_mem hm, ?_⟩
        rw [e3, List.range_succ, List.map_append]
        congr 1
        · rw [← hpr]
          apply List.map_congr_left
          intro t ht
          have hmem : tw TAU W (y t) ∈ pre := by
            rw [← hpr]
            exact List.mem_map.2 ⟨t, ht, rfl⟩
          obtain ⟨_, e4⟩ := allIx_mem hfix _ hmem
          rw [tw_append, Nat.eq_of_beq_eq_true e4]
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
          rw [tw_append]
      · exfalso
        refine witOK_false hℓ hB (σ := fun j => ℓ (tw TAU W (y j))) (i := i) ?_ ?_ e
        · intro j hj
          beta_reduce
          rw [Orb.nIf_eq]
          split_ifs with hji
          · rw [Nat.eq_of_beq_eq_true hji]
            exact hℓ _ hc.1
          · have hj' : j < i := by
              have : j ≠ i := fun e' => hji (by rw [e']; exact Nat.beq_refl i)
              omega
            rw [nthN_map_lt _ (by omega), hpt j hj']
            exact hℓ _ (htw W hW (y j) (hy j (by omega))).1
        · intro a ha hle
          exact prof_conj (LB := LB) hMM hτ hMB hprof hW ha fun j hj =>
            (htw W hW (y j) (hy j (by have := hle j hj; omega))).2
  obtain ⟨W, hW, nd, hnd, hpre⟩ := main 6 le_rfl
  have e := hnode nd hnd
  unfold nodeOK at e
  beta_reduce at e
  rw [hpre, lenL_eq, List.length_map, List.length_range, Orb.bIf_eq (Nat.beq 6 6),
    if_pos (Nat.beq_refl 6)] at e
  simp only [Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at e
  obtain ⟨hj, hw, hpt⟩ := e
  generalize nthN (nthD nd [] 1) 0 = j at hj hpt
  generalize nthD (tlL (tlL nd)) [] 0 = w at hw hpt
  obtain ⟨W', hW', hWi⟩ := wv_inv_word (g := g) W hW
  refine ⟨W' ++ w, lettersIn_append hW' hw, j, hj, fun t ht => ?_⟩
  have e1 := Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hpt t ht)
  rw [nthN_map_range _ ht] at e1
  obtain ⟨-, e2⟩ := htw w hw _ (hsI j hj t ht)
  obtain ⟨-, e3⟩ := htw W hW (y t) (hy t ht)
  rw [e1, e3] at e2
  rw [wv_appendB, hWi, mul_inv_rev, inv_inv]
  have e4 : ℓ (y t) = (wv g W)⁻¹ * (wv g w * ℓ (nthN (nthD sI [] j) t) * (wv g w)⁻¹) * wv g W := by
    rw [← e2]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [e4]
  simp only [mul_assoc]

end CFSG.KC.AE6Tri

end
