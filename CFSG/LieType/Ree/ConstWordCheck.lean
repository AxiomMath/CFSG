module

public import CFSG.LieType.Ree.SmallReeCollectionCheck

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag}

variable (τ) in
@[expose] def famSign (g : ℕ) : ℤ :=
  pinnedSignW τ (certWitnessPos τ g)

theorem famSign_eq
    {g : ℕ} (hg : g < τ.rootCertificate.roots.length) :
    famSign τ g = (rootOperatorFamily τ).pinnedFamilySign (τ.rootCertificate.root g) := by
  rw [famSign, pinnedSignW_eq (certWitnessPos_lt hg), decodeVec_certWitnessPos hg]

@[expose] def modE (n : ℕ) (M : List Entry) : List Entry :=
  M.filterMap fun e => if e.2.2 % (n : ℤ) = 0 then none else some (e.1, e.2.1, e.2.2 % (n : ℤ))

@[expose] def normC (n : ℕ) (L : List PEntry) : List PEntry :=
  (modE n (canonE (L.map Prod.snd))).map fun e => ((0, 0), e)

variable (τ) in
@[expose] def constProd
    (n : ℕ) : List PEntry → List (ℕ × ℤ) → List PEntry
  | acc, [] => acc
  | acc, f :: fs => constProd n (normC n (mul1 acc (nilpE τ f.1 (famSign τ f.1 * f.2) 0 0))) fs

variable (τ) in
@[expose] def constCheck
    (n : ℕ) (L L' : List (ℕ × ℤ)) : Bool :=
  (L ++ L').all (fun f => Nat.blt f.1 τ.rootCertificate.roots.length) &&
    modEqCheck n (constProd τ n [] L) (constProd τ n [] L')

variable (τ) in
@[expose] def constPinned
    (R : Type*) [CommRing R] (fs : List (ℕ × ℤ)) :
    (Module.End R (RootModule τ R))ˣ :=
  (fs.map fun f => pinnedX τ R (τ.rootCertificate.root f.1) (f.2 : R)).prod

theorem constPinned_nil
    (R : Type*) [CommRing R] : constPinned τ R [] = 1 :=
  rfl

theorem constPinned_cons
    (R : Type*) [CommRing R] (f : ℕ × ℤ) (fs : List (ℕ × ℤ)) :
    constPinned τ R (f :: fs) =
      pinnedX τ R (τ.rootCertificate.root f.1) (f.2 : R) * constPinned τ R fs := by
  rw [constPinned, List.map_cons, List.prod_cons, ← constPinned]

theorem constPinned_append
    (R : Type*) [CommRing R] (fs fs' : List (ℕ × ℤ)) :
    constPinned τ R (fs ++ fs') = constPinned τ R fs * constPinned τ R fs' := by
  rw [constPinned, List.map_append, List.prod_append, ← constPinned, ← constPinned]

section Sound

variable {R : Type*} [CommRing R]

@[expose] def ConstP (L : List PEntry) : Prop :=
  ∀ x ∈ L, x.1 = (0, 0)

theorem pOp_eq_of_constP
    {L : List PEntry} (hL : ConstP L) (s t : R) :
    pOp τ R L s t = entriesOp τ R (L.map Prod.snd) := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [pOp_cons, ih fun y hy => hL y (List.mem_cons_of_mem _ hy), hL x List.mem_cons_self,
      List.map_cons, entriesOp_cons, entriesOp_cons, entriesOp_nil, add_zero]
    simp

theorem entriesOp_modE
    {n : ℕ} (hn : (n : R) = 0) (M : List Entry) :
    entriesOp τ R (modE n M) = entriesOp τ R M := by
  have hcast : ∀ z : ℤ, ((z % (n : ℤ) : ℤ) : R) = (z : R) := fun z => by
    conv_rhs => rw [← Int.emod_add_mul_ediv z n]
    rw [Int.cast_add, Int.cast_mul, Int.cast_natCast, hn, zero_mul, add_zero]
  induction M with
  | nil => rfl
  | cons e M ih =>
    rw [modE, List.filterMap_cons, entriesOp_cons, ← ih, ← modE]
    split_ifs with h
    · have h0 : (e.2.2 : R) = 0 := by rw [← hcast, h, Int.cast_zero]
      rw [h0, zero_smul, zero_add]
    · rw [entriesOp_cons, hcast]

theorem constP_normC (n : ℕ) (L : List PEntry) : ConstP (normC n L) := by
  intro x hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  rfl

theorem pOp_normC
    {n : ℕ} (hn : (n : R) = 0) {L : List PEntry} (hL : ConstP L) (s t : R) :
    pOp τ R (normC n L) s t = pOp τ R L s t := by
  rw [pOp_eq_of_constP (constP_normC n L), pOp_eq_of_constP hL, normC, List.map_map]
  simp only [Function.comp_def, List.map_id']
  rw [entriesOp_modE hn, entriesOp_canonE]

theorem constP_mul1 {A B : List PEntry} (hA : ConstP A) (hB : ConstP B) : ConstP (mul1 A B) := by
  intro x hx
  simp only [mul1, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · exact hA x hx
  · exact hB x hx
  · simp only [pmul, List.mem_flatMap, List.mem_map, List.mem_filter] at hx
    obtain ⟨y, hy, z, ⟨hz, -⟩, rfl⟩ := hx
    rw [hA z hz, hB y hy]
    rfl

theorem constP_nilpE (g : ℕ) (C : ℤ) : ConstP (nilpE τ g C 0 0) := by
  intro x hx
  simp only [nilpE, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨k, -, e, -, rfl⟩ := hx
  simp

theorem one_add_pOp_constProd
    {R : Type} [CommRing R] {n : ℕ} (hn : (n : R) = 0) :
    ∀ (fs : List (ℕ × ℤ)) (acc : List PEntry), ConstP acc →
      (∀ f ∈ fs, f.1 < τ.rootCertificate.roots.length) → ∀ s t : R,
      1 + pOp τ R (constProd τ n acc fs) s t =
        (1 + pOp τ R acc s t) * (constPinned τ R fs : Module.End R (RootModule τ R))
  | [], acc, _, _, s, t => by simp [constProd, constPinned]
  | f :: fs, acc, hacc, hfs, s, t => by
    have hf := hfs f List.mem_cons_self
    have hv := (RootOps.dataChecks τ).valid
    rw [constProd, one_add_pOp_constProd hn fs _ (constP_normC n _)
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) s t,
      pOp_normC hn (constP_mul1 hacc (constP_nilpE _ _)),
      one_add_pOp_mul1 _ (validP_nilpE hv hf _ _ _), constPinned_cons, Units.val_mul, mul_assoc]
    congr 2
    have h := one_add_pOp_nilpE (R := R) (rootAt τ f.1 hf) (famSign τ f.1 * f.2) 0 0 s t
    rw [rootPos_rootAt hf] at h
    rw [h, (rootOperatorFamily τ).pinnedX_eq_eltUnit R (RootWalk.isRoot_rootCertificate_root hf),
      RootOperatorFamily.coe_eltUnit, famSign_eq hf]
    simp only [pow_zero, mul_one, Int.cast_mul]
    rfl

theorem constPinned_eq_of_constCheck
    {n : ℕ} {L L' : List (ℕ × ℤ)}
    (h : constCheck τ n L L' = true) (R : Type) [CommRing R] (hn : (n : R) = 0) :
    constPinned τ R L = constPinned τ R L' := by
  simp only [constCheck, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨hpos, hmod⟩ := h
  have hnil : ConstP ([] : List PEntry) := fun x hx => absurd hx List.not_mem_nil
  have heq : 1 + pOp τ R (constProd τ n [] L) 0 0 = 1 + pOp τ R (constProd τ n [] L') 0 0 := by
    rw [pOp_eq_of_modEqCheck (τ := τ) hn hmod 0 0]
  rw [one_add_pOp_constProd hn L [] hnil (fun f hf => hpos f (List.mem_append_left _ hf)),
    one_add_pOp_constProd hn L' [] hnil (fun f hf => hpos f (List.mem_append_right _ hf)),
    pOp_nil, add_zero, one_mul, one_mul] at heq
  exact Units.ext heq

end Sound

end CFSG.LieType.Ree
