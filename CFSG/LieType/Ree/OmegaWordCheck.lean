module

public import CFSG.LieType.Ree.ConstWordCheck

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

@[expose] def redW (d : ℕ) (x : PEntry) : List Entry :=
  if x.1.1 % 3 = d then [x.2]
  else if x.1.1 % 3 = 2 then [(x.2.1, x.2.2.1, -x.2.2.2)] else []

@[expose] def normW (L : List PEntry) : List PEntry :=
  (modE 2 (canonE (L.flatMap (redW 0)))).map (fun e => ((0, 0), e)) ++
    (modE 2 (canonE (L.flatMap (redW 1)))).map (fun e => ((1, 0), e))

variable (τ) in
@[expose] def omegaProd : List PEntry → List (ℕ × ℤ × ℕ) → List PEntry
  | acc, [] => acc
  | acc, f :: fs =>
    omegaProd (normW (mul1 acc (nilpE τ f.1 (famSign τ f.1 * f.2.1) f.2.2 0))) fs

variable (τ) in
@[expose] def omegaCheck (L L' : List (ℕ × ℤ × ℕ)) : Bool :=
  (L ++ L').all (fun f => Nat.blt f.1 τ.rootCertificate.roots.length) &&
    (omegaProd τ [] L == omegaProd τ [] L')

variable (τ) in
@[expose] def omegaPinned
    (R : Type*) [CommRing R] (fs : List (ℕ × ℤ × ℕ)) (s : R) :
    (Module.End R (RootModule τ R))ˣ :=
  (fs.map fun f => pinnedX τ R (τ.rootCertificate.root f.1) ((f.2.1 : R) * s ^ f.2.2)).prod

theorem omegaPinned_nil
    (R : Type*) [CommRing R] (s : R) : omegaPinned τ R [] s = 1 :=
  rfl

theorem omegaPinned_cons
    (R : Type*) [CommRing R] (f : ℕ × ℤ × ℕ) (fs : List (ℕ × ℤ × ℕ)) (s : R) :
    omegaPinned τ R (f :: fs) s =
      pinnedX τ R (τ.rootCertificate.root f.1) ((f.2.1 : R) * s ^ f.2.2) *
        omegaPinned τ R fs s := by
  rw [omegaPinned, List.map_cons, List.prod_cons, ← omegaPinned]

theorem omegaPinned_append
    (R : Type*) [CommRing R] (fs fs' : List (ℕ × ℤ × ℕ)) (s : R) :
    omegaPinned τ R (fs ++ fs') s = omegaPinned τ R fs s * omegaPinned τ R fs' s := by
  rw [omegaPinned, List.map_append, List.prod_append, ← omegaPinned, ← omegaPinned]

section Sound

@[expose] def TFree (L : List PEntry) : Prop :=
  ∀ x ∈ L, x.1.2 = 0

theorem tFree_normW (L : List PEntry) : TFree (normW L) := by
  intro x hx
  simp only [normW, List.mem_append, List.mem_map] at hx
  obtain ⟨e, -, rfl⟩ | ⟨e, -, rfl⟩ := hx <;> rfl

theorem tFree_mul1 {A B : List PEntry} (hA : TFree A) (hB : TFree B) : TFree (mul1 A B) := by
  intro x hx
  simp only [mul1, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hA x hx
  · exact hB x hx
  · simp only [pmul, List.mem_flatMap, List.mem_map, List.mem_filter] at hx
    obtain ⟨y, hy, z, ⟨hz, -⟩, rfl⟩ := hx
    show z.1.2 + y.1.2 = 0
    rw [hA z hz, hB y hy]

theorem tFree_nilpE (g : ℕ) (C : ℤ) (ea : ℕ) : TFree (nilpE τ g C ea 0) := by
  intro x hx
  simp only [nilpE, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨k, -, e, -, rfl⟩ := hx
  simp

variable {R : Type*} [CommRing R]

theorem smul_entriesOp_redW
    {s : R} (hs : s ^ 2 + s + 1 = 0) (x : PEntry) (hx : x.1.2 = 0) (t : R) :
    (s ^ x.1.1 * t ^ x.1.2) • entriesOp τ R [x.2] =
      entriesOp τ R (redW 0 x) + s • entriesOp τ R (redW 1 x) := by
  have h3 : s ^ 3 = 1 := by linear_combination (s - 1) * hs
  have hpow : s ^ x.1.1 = s ^ (x.1.1 % 3) := by
    conv_lhs => rw [← Nat.div_add_mod x.1.1 3, pow_add, pow_mul, h3, one_pow, one_mul]
  have hneg : entriesOp τ R [(x.2.1, x.2.2.1, -x.2.2.2)] = -entriesOp τ R [x.2] := by
    rw [entriesOp_cons, entriesOp_cons, entriesOp_nil, add_zero, add_zero, Int.cast_neg,
      neg_smul]
  rw [hx, pow_zero, mul_one, hpow]
  rcases (by omega : x.1.1 % 3 = 0 ∨ x.1.1 % 3 = 1 ∨ x.1.1 % 3 = 2) with h | h | h
  · simp [redW, h]
  · simp [redW, h]
  · have hsq : s ^ 2 = -s - 1 := by linear_combination hs
    simp only [redW, h, hsq]
    simp [hneg]
    module

theorem pOp_eq_of_tFree
    {s : R} (hs : s ^ 2 + s + 1 = 0) :
    ∀ {L : List PEntry}, TFree L → ∀ t : R, pOp τ R L s t =
      entriesOp τ R (L.flatMap (redW 0)) + s • entriesOp τ R (L.flatMap (redW 1))
  | [], _, t => by simp
  | x :: L, hL, t => by
    rw [pOp_cons, pOp_eq_of_tFree hs (fun y hy => hL y (List.mem_cons_of_mem _ hy)) t,
      smul_entriesOp_redW hs x (hL x List.mem_cons_self) t, List.flatMap_cons, List.flatMap_cons,
      entriesOp_append, entriesOp_append, smul_add]
    abel

theorem pOp_normW
    {R : Type} [CommRing R] (h2 : (2 : R) = 0) {s : R}
    (hs : s ^ 2 + s + 1 = 0) {L : List PEntry} (hL : TFree L) (t : R) :
    pOp τ R (normW L) s t = pOp τ R L s t := by
  have h2' : ((2 : ℕ) : R) = 0 := by rw [Nat.cast_ofNat]; exact h2
  rw [normW, pOp_append, pOp_map_deg, pOp_map_deg, entriesOp_modE h2', entriesOp_modE h2',
    entriesOp_canonE, entriesOp_canonE, pOp_eq_of_tFree hs hL t]
  simp

theorem one_add_pOp_omegaProd
    {R : Type} [CommRing R] (h2 : (2 : R) = 0) {s : R}
    (hs : s ^ 2 + s + 1 = 0) (t : R) :
    ∀ (fs : List (ℕ × ℤ × ℕ)) (acc : List PEntry), TFree acc →
      (∀ f ∈ fs, f.1 < τ.rootCertificate.roots.length) →
      1 + pOp τ R (omegaProd τ acc fs) s t =
        (1 + pOp τ R acc s t) * (omegaPinned τ R fs s : Module.End R (RootModule τ R))
  | [], acc, _, _ => by simp [omegaProd, omegaPinned]
  | f :: fs, acc, hacc, hfs => by
    have hf := hfs f List.mem_cons_self
    have hv := (RootOps.dataChecks τ).valid
    rw [omegaProd, one_add_pOp_omegaProd h2 hs t fs _ (tFree_normW _)
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg)),
      pOp_normW h2 hs (tFree_mul1 hacc (tFree_nilpE _ _ _)) t,
      one_add_pOp_mul1 _ (validP_nilpE hv hf _ _ _), omegaPinned_cons, Units.val_mul, mul_assoc]
    congr 2
    have h := one_add_pOp_nilpE (R := R) (rootAt τ f.1 hf) (famSign τ f.1 * f.2.1) f.2.2 0 s t
    rw [rootPos_rootAt hf] at h
    rw [h, (rootOperatorFamily τ).pinnedX_eq_eltUnit R (RootWalk.isRoot_rootCertificate_root hf),
      RootOperatorFamily.coe_eltUnit, famSign_eq hf]
    simp only [pow_zero, mul_one, Int.cast_mul, mul_assoc]
    rfl

theorem omegaPinned_eq_of_omegaCheck
    {L L' : List (ℕ × ℤ × ℕ)}
    (h : omegaCheck τ L L' = true) (R : Type) [CommRing R] (h2 : (2 : R) = 0) (s : R)
    (hs : s ^ 2 + s + 1 = 0) : omegaPinned τ R L s = omegaPinned τ R L' s := by
  simp only [omegaCheck, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, beq_iff_eq] at h
  obtain ⟨hpos, hnorm⟩ := h
  have hnil : TFree ([] : List PEntry) := fun x hx => absurd hx List.not_mem_nil
  have h1 := one_add_pOp_omegaProd h2 hs 0 L [] hnil
    (fun f hf => hpos f (List.mem_append_left _ hf))
  have h1' := one_add_pOp_omegaProd h2 hs 0 L' [] hnil
    (fun f hf => hpos f (List.mem_append_right _ hf))
  rw [hnorm] at h1
  rw [pOp_nil, add_zero, one_mul] at h1 h1'
  exact Units.ext (h1.symm.trans h1')

end Sound

end CFSG.LieType.Ree
