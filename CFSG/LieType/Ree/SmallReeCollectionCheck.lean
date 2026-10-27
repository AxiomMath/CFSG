module

public import CFSG.LieType.Chevalley.AllRootWeylSignsDefs
public import CFSG.LieType.Chevalley.D4TripleA2Lemmas

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

@[expose] def modEqCheck (n : ℤ) (L L' : List PEntry) : Bool :=
  (L ++ L').all fun x => (canonE (coeffAt L x.1 ++ (coeffAt L' x.1).map
    fun e => (e.1, e.2.1, -1 * e.2.2))).all fun e => e.2.2 % n == 0

section Ring

variable {R : Type*} [CommRing R]

theorem entriesOp_eq_zero_of_dvd
    {n : ℕ} (hn : (n : R) = 0) {L : List Entry}
    (h : ∀ e ∈ L, (n : ℤ) ∣ e.2.2) : entriesOp τ R L = 0 := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [entriesOp_cons, ih fun f hf => h f (List.mem_cons_of_mem _ hf)]
    obtain ⟨m, hm⟩ := h e List.mem_cons_self
    rw [hm, Int.cast_mul, Int.cast_natCast, hn, zero_mul, zero_smul, add_zero]

theorem pOp_eq_of_modEqCheck
    {n : ℕ} (hn : (n : R) = 0) {L L' : List PEntry}
    (h : modEqCheck n L L' = true) (s t : R) : pOp τ R L s t = pOp τ R L' s t := by
  classical
  set S : Finset (ℕ × ℕ) := ((L ++ L').map Prod.fst).toFinset
  have hS : ∀ x ∈ L ++ L', x.1 ∈ S := fun x hx =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [pOp_eq_sum L S (fun x hx => hS x (List.mem_append_left _ hx)),
    pOp_eq_sum L' S (fun x hx => hS x (List.mem_append_right _ hx))]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hδ)
  simp only [modEqCheck, List.all_eq_true, beq_iff_eq] at h
  have h0 := entriesOp_eq_zero_of_dvd (τ := τ) hn fun e he => Int.dvd_of_emod_eq_zero (h x hx e he)
  rw [entriesOp_canonE, entriesOp_append, entriesOp_map_smul, Int.cast_neg, Int.cast_one,
    neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  rw [h0]

end Ring

variable (τ) in
@[expose] def factorPinned
    (R : Type*) [CommRing R] (fs : List Factor) (s t : R) :
    (Module.End R (RootModule τ R))ˣ :=
  (fs.map fun f => pinnedX τ R (τ.rootCertificate.root f.2.2.1)
    ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1)).prod

variable (τ) in
@[expose] def signOneB (g : ℕ) : Bool :=
  Nat.blt g τ.rootCertificate.roots.length && pinnedSignW τ (certWitnessPos τ g) == 1

variable (τ) in
@[expose] def wordCheck
    (n : ℕ) (L L' : List Factor) : Bool :=
  (L ++ L').all (fun f => signOneB τ f.2.2.1) &&
    modEqCheck n (factorsN τ [] L) (factorsN τ [] L')

theorem pinnedFamilySign_of_signOneB
    {g : ℕ} (h : signOneB τ g = true) :
    g < τ.rootCertificate.roots.length ∧
      (rootOperatorFamily τ).pinnedFamilySign (τ.rootCertificate.root g) = 1 := by
  simp only [signOneB, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  refine ⟨h.1, ?_⟩
  rw [← decodeVec_certWitnessPos h.1, ← pinnedSignW_eq (certWitnessPos_lt h.1)]
  exact h.2

theorem factorPinned_nil
    (R : Type*) [CommRing R] (s t : R) : factorPinned τ R [] s t = 1 :=
  rfl

theorem factorPinned_cons
    (R : Type*) [CommRing R] (f : Factor) (fs : List Factor) (s t : R) :
    factorPinned τ R (f :: fs) s t = pinnedX τ R (τ.rootCertificate.root f.2.2.1)
      ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1) * factorPinned τ R fs s t := by
  rw [factorPinned, List.map_cons, List.prod_cons, ← factorPinned]

theorem factorsProd_eq_factorPinned
    {R : Type} [CommRing R] (fs : List Factor)
    (hfs : ∀ f ∈ fs, signOneB τ f.2.2.1 = true) (s t : R) :
    factorsProd τ R fs s t = (factorPinned τ R fs s t : Module.End R (RootModule τ R)) := by
  induction fs with
  | nil => simp [factorsProd, factorPinned]
  | cons f fs ih =>
    obtain ⟨hlt, hsign⟩ := pinnedFamilySign_of_signOneB (hfs f List.mem_cons_self)
    rw [factorsProd_cons, ih fun g hg => hfs g (List.mem_cons_of_mem _ hg), factorPinned_cons,
      Units.val_mul, dite_eq_left hlt,
      (rootOperatorFamily τ).pinnedX_eq_eltUnit R (RootWalk.isRoot_rootCertificate_root hlt), hsign,
      Int.cast_one, one_mul, RootOperatorFamily.coe_eltUnit]
    rfl

theorem factorPinned_eq_of_wordCheck_type
    {n : ℕ} {L L' : List Factor}
    (h : wordCheck τ n L L' = true) (R : Type) [CommRing R] (hn : (n : R) = 0) (s t : R) :
    factorPinned τ R L s t = factorPinned τ R L' s t := by
  simp only [wordCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hsign, hmod⟩ := h
  have hL : ∀ f ∈ L, signOneB τ f.2.2.1 = true := fun f hf =>
    hsign f (List.mem_append_left _ hf)
  have hL' : ∀ f ∈ L', signOneB τ f.2.2.1 = true := fun f hf =>
    hsign f (List.mem_append_right _ hf)
  have hv := (RootOps.dataChecks τ).valid
  have hnil : ValidP τ ([] : List PEntry) := fun x hx => absurd hx List.not_mem_nil
  have heq : 1 + pOp τ R (factorsN τ [] L) s t = 1 + pOp τ R (factorsN τ [] L') s t := by
    rw [pOp_eq_of_modEqCheck (τ := τ) hn hmod s t]
  rw [one_add_pOp_factorsN hv L (fun f hf => (pinnedFamilySign_of_signOneB (hL f hf)).1) [] hnil,
    one_add_pOp_factorsN hv L' (fun f hf => (pinnedFamilySign_of_signOneB (hL' f hf)).1) [] hnil,
    pOp_nil, add_zero, one_mul, one_mul, factorsProd_eq_factorPinned L hL,
    factorsProd_eq_factorPinned L' hL'] at heq
  exact Units.ext heq

theorem baseChange_factorPinned
    {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (fs : List Factor) (s t : R) :
    BaseChange g (factorPinned τ R fs s t : Module.End R (RootModule τ R))
      (factorPinned τ S fs (g s) (g t) : Module.End S (RootModule τ S)) := by
  induction fs with
  | nil => simpa [factorPinned] using BaseChange.one (τ := τ) (f := g)
  | cons f fs ih =>
    simp only [factorPinned, List.map_cons, List.prod_cons, Units.val_mul] at ih ⊢
    have h := baseChange_pinnedX (τ := τ) g (τ.rootCertificate.root f.2.2.1)
      ((f.2.2.2 : R) * s ^ f.1 * t ^ f.2.1)
    rw [map_mul, map_mul, map_intCast, map_pow, map_pow] at h
    exact h.mul ih

open MvPolynomial in
theorem factorPinned_eq_of_wordCheck
    {n : ℕ} {L L' : List Factor}
    (h : wordCheck τ n L L' = true) (R : Type*) [CommRing R] (hn : (n : R) = 0) (s t : R) :
    factorPinned τ R L s t = factorPinned τ R L' s t := by
  set A := MvPolynomial (Fin 2) (ZMod n)
  have hA : (n : A) = 0 := by
    rw [← map_natCast (MvPolynomial.C (σ := Fin 2)), ZMod.natCast_self, map_zero]
  have h0 := factorPinned_eq_of_wordCheck_type h A hA (X 0) (X 1)
  set φ : ZMod n →+* R := ZMod.castHom (ringChar.dvd hn) R
  set g : A →+* R := eval₂Hom φ ![s, t]
  have hg0 : g (X 0) = s := eval₂Hom_X' _ _ _
  have hg1 : g (X 1) = t := eval₂Hom_X' _ _ _
  have hb := baseChange_factorPinned (τ := τ) g L (X 0) (X 1)
  have hb' := baseChange_factorPinned (τ := τ) g L' (X 0) (X 1)
  rw [hg0, hg1] at hb hb'
  rw [h0] at hb
  exact Units.ext (hb.unique hb')

end CFSG.LieType.Ree
