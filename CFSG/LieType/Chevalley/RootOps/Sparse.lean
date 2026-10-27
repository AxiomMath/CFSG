module

public import CFSG.LieType.Chevalley.BraidWalk
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley.RootOps

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag} {R : Type*} [CommRing R]

abbrev dim (τ : Tag) : ℕ := τ.rank + τ.rootCertificate.roots.length

abbrev Entry : Type := ℕ × ℕ × ℤ

variable (τ R) in
@[expose] noncomputable def posVec (p : ℕ) : RootModule τ R :=
  if h : p < τ.rank then hVec τ R ⟨p, h⟩ else rootVec τ R (τ.rootCertificate.root (p - τ.rank))

@[expose] def posLabel (p : ℕ) (hp : p < dim τ) : Label τ :=
  if h : p < τ.rank then .inl ⟨p, h⟩
  else .inr ⟨τ.rootCertificate.root (p - τ.rank),
    isRoot_rootCertificate_root (by simp only [dim] at hp; omega)⟩

theorem posVec_eq_single {p : ℕ} (hp : p < dim τ) :
    posVec τ R p = Finsupp.single (posLabel p hp) 1 := by
  unfold posVec posLabel
  split_ifs with h
  · rfl
  · exact dite_eq_left _

theorem posLabel_injective {p q : ℕ} (hp : p < dim τ) (hq : q < dim τ)
    (h : posLabel p hp = posLabel q hq) : p = q := by
  simp only [dim] at hp hq
  by_cases h₁ : p < τ.rank <;> by_cases h₂ : q < τ.rank <;>
    simp only [posLabel, h₁, h₂, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
      Fin.mk.injEq, Subtype.mk.injEq, reduceCtorEq] at h
  · exact h
  · have := rootCertificate_root_injOn (by omega) (by omega) h
    omega

theorem posLabel_surjective (b : Label τ) : ∃ p, ∃ hp : p < dim τ, posLabel p hp = b := by
  rcases b with j | ⟨α, hα⟩
  · exact ⟨j, by simp only [dim]; omega, by simp [posLabel]⟩
  · obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
    refine ⟨τ.rank + k, by simp only [dim]; omega, ?_⟩
    simp [posLabel]

theorem ext_posVec {f g : Module.End R (RootModule τ R)}
    (h : ∀ p, p < dim τ → f (posVec τ R p) = g (posVec τ R p)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
  simpa [posVec_eq_single hp] using h p hp

variable (τ R) in
@[expose] noncomputable def posCoord (p : ℕ) : RootModule τ R →ₗ[R] R :=
  if hp : p < dim τ then Finsupp.lapply (posLabel p hp) else 0

theorem posCoord_posVec {p q : ℕ} (hq : q < dim τ) :
    posCoord τ R p (posVec τ R q) = if p = q then 1 else 0 := by
  unfold posCoord
  split_ifs with hp hpq hpq
  · subst hpq
    rw [posVec_eq_single hq, Finsupp.lapply_apply, Finsupp.single_eq_same]
  · rw [posVec_eq_single hq, Finsupp.lapply_apply, Finsupp.single_eq_of_ne]
    exact fun h => hpq (posLabel_injective hp hq h)
  · exact absurd (hpq ▸ hq) hp
  · rfl

variable (τ R) in
@[expose] noncomputable def vecOf (v : List (ℕ × ℤ)) : RootModule τ R :=
  (v.map fun x => (x.2 : R) • posVec τ R x.1).sum

@[simp] theorem vecOf_nil : vecOf τ R [] = 0 :=
  rfl

@[simp] theorem vecOf_cons (x : ℕ × ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (x :: v) = (x.2 : R) • posVec τ R x.1 + vecOf τ R v :=
  rfl

theorem vecOf_append (v w : List (ℕ × ℤ)) : vecOf τ R (v ++ w) = vecOf τ R v + vecOf τ R w := by
  simp [vecOf]

theorem vecOf_flatMap (v : List (ℕ × ℤ)) (f : ℕ × ℤ → List (ℕ × ℤ)) :
    vecOf τ R (v.flatMap f) = (v.map fun x => vecOf τ R (f x)).sum := by
  induction v with
  | nil => rfl
  | cons x v ih => rw [List.flatMap_cons, vecOf_append, ih, List.map_cons, List.sum_cons]

theorem vecOf_map_mul (z : ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (v.map fun y => (y.1, z * y.2)) = (z : R) • vecOf τ R v := by
  induction v with
  | nil => simp
  | cons y v ih =>
    simp only [List.map_cons, vecOf_cons, ih, smul_add, Int.cast_mul, mul_smul]

@[expose] def colOf (L : List Entry) (c : ℕ) : List (ℕ × ℤ) :=
  (L.filter fun e => e.1 == c).map fun e => (e.2.1, e.2.2)

@[expose] def ValidVec (τ : Tag) (v : List (ℕ × ℤ)) : Prop :=
  ∀ x ∈ v, x.1 < dim τ

@[expose] def ValidEntries (τ : Tag) (L : List Entry) : Prop :=
  ∀ e ∈ L, e.1 < dim τ ∧ e.2.1 < dim τ

theorem ValidEntries.colOf {L : List Entry} (hL : ValidEntries τ L) (c : ℕ) :
    ValidVec τ (colOf L c) := by
  intro x hx
  simp only [RootOps.colOf, List.mem_map, List.mem_filter] at hx
  obtain ⟨e, ⟨he, -⟩, rfl⟩ := hx
  exact (hL e he).2

variable (τ R) in
@[expose] noncomputable def entriesOp (L : List Entry) : Module.End R (RootModule τ R) :=
  (L.map fun e => (e.2.2 : R) • (posCoord τ R e.1).smulRight (posVec τ R e.2.1)).sum

@[simp] theorem entriesOp_nil : entriesOp τ R [] = 0 :=
  rfl

theorem entriesOp_cons (e : Entry) (L : List Entry) :
    entriesOp τ R (e :: L) =
      (e.2.2 : R) • (posCoord τ R e.1).smulRight (posVec τ R e.2.1) + entriesOp τ R L :=
  rfl

theorem entriesOp_posVec (L : List Entry) {c : ℕ} (hc : c < dim τ) :
    entriesOp τ R L (posVec τ R c) = vecOf τ R (colOf L c) := by
  induction L with
  | nil => simp [colOf]
  | cons e L ih =>
    rw [entriesOp_cons, LinearMap.add_apply, ih, LinearMap.smul_apply, LinearMap.smulRight_apply,
      posCoord_posVec hc]
    simp only [colOf, List.filter_cons, beq_iff_eq]
    split_ifs with h
    · simp
    · simp

@[expose] def applyL (L : List Entry) (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (colOf L x.1).map fun y => (y.1, x.2 * y.2)

theorem entriesOp_vecOf (L : List Entry) {v : List (ℕ × ℤ)} (hv : ValidVec τ v) :
    entriesOp τ R L (vecOf τ R v) = vecOf τ R (applyL L v) := by
  induction v with
  | nil => simp [applyL]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, entriesOp_posVec L (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [applyL, List.flatMap_cons, vecOf_append, vecOf_map_mul]

@[expose] def nPos (τ : Tag) (i : Fin τ.rank) (p : ℕ) : List (ℕ × ℤ) :=
  if h : p < τ.rank then [(p, 1), (i, -((τ.cartan ⟨p, h⟩ i).natAbs : ℤ))]
  else [(τ.rank + τ.rootCertificate.image (p - τ.rank) i, (-1) ^ downAt τ (p - τ.rank) i)]

theorem weylElt_posVec (i : Fin τ.rank) {p : ℕ} (hp : p < dim τ) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (posVec τ R p) =
      vecOf τ R (nPos τ i p) := by
  unfold nPos
  split_ifs with h
  · have hi : posVec τ R (i : ℕ) = hVec τ R i := by simp [posVec, i.2]
    simp only [vecOf_cons, vecOf_nil, add_zero, Int.cast_one, one_smul, hi]
    rw [show posVec τ R p = hVec τ R ⟨p, h⟩ by simp [posVec, h], weylElt_hVec]
    rw [Int.cast_neg, Int.cast_natCast, neg_smul, sub_eq_add_neg]
  · have hm : p - τ.rank < τ.rootCertificate.roots.length := by simp only [dim] at hp; omega
    have hpv : posVec τ R p = rootVec τ R (τ.rootCertificate.root (p - τ.rank)) := by
      simp [posVec, h]
    have hq : posVec τ R (τ.rank + τ.rootCertificate.image (p - τ.rank) i) =
        rootVec τ R (τ.rootCertificate.root (τ.rootCertificate.image (p - τ.rank) i)) := by
      simp [posVec]
    rw [hpv, weylElt_rootVec i 1 (isRoot_rootCertificate_root hm), vecOf_cons, vecOf_nil,
      add_zero, hq, rootCertificate_root_image hm, stringDown_rootCertificate_root hm]
    simp

theorem validVec_nPos (i : Fin τ.rank) {p : ℕ} (hp : p < dim τ) : ValidVec τ (nPos τ i p) := by
  intro x hx
  unfold nPos at hx
  split_ifs at hx with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simpa using h.trans_le (Nat.le_add_right _ _)
    · simpa using i.2.trans_le (Nat.le_add_right _ _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    simp only [dim] at hp ⊢
    have := rootCertificate_image_lt (τ := τ) (k := p - τ.rank) (by omega) i
    omega

@[expose] def nVecL (τ : Tag) (i : Fin τ.rank) (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  v.flatMap fun x => (nPos τ i x.1).map fun y => (y.1, x.2 * y.2)

theorem weylElt_vecOf (i : Fin τ.rank) {v : List (ℕ × ℤ)} (hv : ValidVec τ v) :
    (weylElt τ R i 1 : Module.End R (RootModule τ R)) (vecOf τ R v) =
      vecOf τ R (nVecL τ i v) := by
  induction v with
  | nil => simp [nVecL]
  | cons x v ih =>
    rw [vecOf_cons, map_add, map_smul, weylElt_posVec i (hv x (List.mem_cons_self ..)),
      ih fun y hy => hv y (List.mem_cons_of_mem _ hy)]
    simp only [nVecL, List.flatMap_cons, vecOf_append, vecOf_map_mul]

@[expose] def insertCoeff (x : ℕ × ℤ) : List (ℕ × ℤ) → List (ℕ × ℤ)
  | [] => [x]
  | y :: ys =>
    if x.1 < y.1 then x :: y :: ys
    else if x.1 = y.1 then (x.1, x.2 + y.2) :: ys
    else y :: insertCoeff x ys

@[expose] def normalize (v : List (ℕ × ℤ)) : List (ℕ × ℤ) :=
  (v.foldr insertCoeff []).filter fun x => x.2 != 0

theorem vecOf_insertCoeff (x : ℕ × ℤ) (v : List (ℕ × ℤ)) :
    vecOf τ R (insertCoeff x v) = (x.2 : R) • posVec τ R x.1 + vecOf τ R v := by
  induction v with
  | nil => simp [insertCoeff]
  | cons y v ih =>
    unfold insertCoeff
    split_ifs with h₁ h₂
    · rfl
    · simp only [vecOf_cons, h₂, Int.cast_add, add_smul]
      abel
    · rw [vecOf_cons, ih, vecOf_cons]
      abel

theorem vecOf_filter_ne_zero (v : List (ℕ × ℤ)) :
    vecOf τ R (v.filter fun x => x.2 != 0) = vecOf τ R v := by
  induction v with
  | nil => rfl
  | cons y v ih =>
    rw [List.filter_cons]
    split_ifs with h
    · rw [vecOf_cons, ih, vecOf_cons]
    · simp only [bne_iff_ne, ne_eq, not_not] at h
      rw [ih, vecOf_cons, h, Int.cast_zero, zero_smul, zero_add]

theorem vecOf_normalize (v : List (ℕ × ℤ)) : vecOf τ R (normalize v) = vecOf τ R v := by
  rw [normalize, vecOf_filter_ne_zero]
  induction v with
  | nil => rfl
  | cons x v ih => rw [List.foldr_cons, vecOf_insertCoeff, ih, vecOf_cons]

theorem vecOf_eq_of_normalize_eq {v w : List (ℕ × ℤ)} (h : normalize v = normalize w) :
    vecOf τ R v = vecOf τ R w := by
  rw [← vecOf_normalize v, h, vecOf_normalize]

@[expose] def decodeEntries : ℕ → ℕ → List Entry
  | 0, _ => []
  | fuel + 1, code =>
    if code = 0 then []
    else
      (code % 2 ^ 20 / 4096, code % 2 ^ 20 / 16 % 256, ((code % 16 : ℕ) : ℤ) - 8) ::
        decodeEntries fuel (code / 2 ^ 20)

end CFSG.LieType.Chevalley.RootOps
