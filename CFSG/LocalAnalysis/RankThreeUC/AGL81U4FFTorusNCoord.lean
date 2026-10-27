module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusDefs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Quasithin

section Coord

variable {F : Type} [Field F] {κ : ℕ}

theorem torusN_charP_two_of_card [Finite F] {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2) :
    CharP F 2 := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, hp⟩ := CharP.exists F
  obtain ⟨m, hpm, hm⟩ := FiniteField.card F p
  have h1 : p ^ (m : ℕ) = 2 ^ (n * 2) := by
    rw [← hm, ← Nat.card_eq_fintype_card, hF, pow_mul]
  have h2 : p ∣ 2 ^ (n * 2) := by
    rw [← h1]
    exact dvd_pow_self p (PNat.ne_zero m)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hpm Nat.prime_two).mp (hpm.dvd_of_dvd_pow h2)
  subst hp2
  exact hp

instance instIsF2SpaceFinPi [CharP F 2] : IsF2Space (Multiplicative (Fin κ → F)) :=
  ⟨fun v => by
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    funext i
    simp [nsmul_eq_mul, h2]⟩

@[expose] def coordSub (F : Type) [Field F] (i : Fin κ) : Subgroup (Multiplicative (Fin κ → F)) where
  carrier := {v | ∀ j, j ≠ i → Multiplicative.toAdd v j = 0}
  one_mem' := fun j _ => rfl
  mul_mem' := by
    intro a b ha hb j hj
    simp [ha j hj, hb j hj]
  inv_mem' := by
    intro a ha j hj
    simp [ha j hj]

theorem mem_coordSub {i : Fin κ} {v : Multiplicative (Fin κ → F)} :
    v ∈ coordSub F i ↔ ∀ j, j ≠ i → Multiplicative.toAdd v j = 0 := Iff.rfl

private def coordEval (F : Type) [Field F] (i : Fin κ) :
    Multiplicative (Fin κ → F) →* Multiplicative F where
  toFun v := Multiplicative.ofAdd (Multiplicative.toAdd v i)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem mem_ker_coordEval (F : Type) [Field F] (i : Fin κ)
    (v : Multiplicative (Fin κ → F)) :
    v ∈ (coordEval F i).ker ↔ Multiplicative.toAdd v i = 0 := by
  rw [MonoidHom.mem_ker]
  exact ofAdd_eq_one

theorem iSupIndep_coordSub : iSupIndep (fun i : Fin κ => coordSub F i) := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  have hle : (⨆ j : Fin κ, ⨆ (_ : j ≠ i), coordSub F j) ≤ (coordEval F i).ker := by
    refine iSup₂_le fun j hj => ?_
    intro v hv
    rw [mem_ker_coordEval]
    exact (mem_coordSub.mp hv) i (Ne.symm hj)
  have h0 : Multiplicative.toAdd x i = 0 := (mem_ker_coordEval F i x).mp (hle hx')
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  funext j
  by_cases hji : j = i
  · subst hji
    exact h0
  · exact (mem_coordSub.mp hx) j hji

theorem iSup_coordSub : ⨆ i : Fin κ, coordSub F i = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hmem : ∀ i : Fin κ,
      Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd v i) : Fin κ → F) ∈
        ⨆ j : Fin κ, coordSub F j := by
    intro i
    refine Subgroup.mem_iSup_of_mem i ?_
    rw [mem_coordSub]
    intro j hj
    rw [toAdd_ofAdd]
    exact Pi.single_eq_of_ne hj _
  have hprod := Subgroup.prod_mem (⨆ j : Fin κ, coordSub F j) (t := Finset.univ)
    (fun i _ => hmem i)
  have heq : (∏ i : Fin κ, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd v i) : Fin κ → F))
      = v := by
    rw [← ofAdd_sum, Finset.univ_sum_single, ofAdd_toAdd]
  rwa [heq] at hprod

theorem iSupIndep_comap_mulEquiv {S S' : Type} [Group S] [Group S'] (ψ : S ≃* S')
    {ι : Type} (W : ι → Subgroup S') (hind : iSupIndep W) :
    iSupIndep (fun i => (W i).comap ψ.toMonoidHom) :=
  iSupIndep.map_orderIso ψ.comapSubgroup hind

theorem iSup_comap_mulEquiv {S S' : Type} [Group S] [Group S'] (ψ : S ≃* S')
    {ι : Type} (W : ι → Subgroup S') (htop : ⨆ i, W i = ⊤) :
    ⨆ i, (W i).comap ψ.toMonoidHom = ⊤ := by
  have h1 : ψ.comapSubgroup (⨆ i, W i) = ⨆ i, (W i).comap ψ.toMonoidHom :=
    map_iSup ψ.comapSubgroup W
  rw [← h1, htop]
  exact map_top ψ.comapSubgroup

@[expose] def scaleAut (a : Fin κ → Fˣ) : MulAut (Multiplicative (Fin κ → F)) where
  toFun v := Multiplicative.ofAdd (fun i => (a i : F) * Multiplicative.toAdd v i)
  invFun v := Multiplicative.ofAdd (fun i => ((a i)⁻¹ : Fˣ) * Multiplicative.toAdd v i)
  left_inv v := by
    ext i
    simp
  right_inv v := by
    ext i
    simp
  map_mul' x y := by
    ext i
    simp [mul_add]

theorem scaleAut_apply (a : Fin κ → Fˣ) (v : Multiplicative (Fin κ → F)) (i : Fin κ) :
    Multiplicative.toAdd (scaleAut a v) i = (a i : F) * Multiplicative.toAdd v i := rfl

private theorem nsmul_val_coord [Algebra (ZMod 2) F] (c : ZMod 2)
    (x : Multiplicative (Fin κ → F)) (i : Fin κ) :
    Multiplicative.toAdd (Additive.toMul (c.val • Additive.ofMul x)) i =
      algebraMap (ZMod 2) F c * Multiplicative.toAdd x i := by
  have h2 : algebraMap (ZMod 2) F c = ((c.val : ℕ) : F) := by
    calc algebraMap (ZMod 2) F c = algebraMap (ZMod 2) F ((c.val : ℕ) : ZMod 2) := by
          rw [ZMod.natCast_zmod_val]
      _ = ((c.val : ℕ) : F) := map_natCast _ _
  rw [h2, toMul_nsmul, toAdd_pow, Pi.smul_apply, nsmul_eq_mul]
  rfl

private theorem aeval_scaleAut_coord [CharP F 2] [Algebra (ZMod 2) F] (a : Fin κ → Fˣ)
    (p : Polynomial (ZMod 2)) :
    ∀ (x : Multiplicative (Fin κ → F)) (i : Fin κ),
      Multiplicative.toAdd (Additive.toMul
          (Polynomial.aeval (linOf (scaleAut a)) p (Additive.ofMul x))) i =
        Polynomial.aeval (a i : F) p * Multiplicative.toAdd x i := by
  induction p using Polynomial.induction_on with
  | C c =>
    intro x i
    simp only [Polynomial.aeval_C]
    rw [Module.algebraMap_end_apply]
    show Multiplicative.toAdd (Additive.toMul (c.val • Additive.ofMul x)) i = _
    exact nsmul_val_coord c x i
  | add p q hp hq =>
    intro x i
    rw [map_add, map_add, LinearMap.add_apply, toMul_add, toAdd_mul, Pi.add_apply, hp x i,
      hq x i, add_mul]
  | monomial n c hc =>
    intro x i
    have e1 : ∀ r : Polynomial (ZMod 2),
        Polynomial.aeval (linOf (scaleAut a)) (r * Polynomial.X) =
          Polynomial.aeval (linOf (scaleAut a)) r * linOf (scaleAut a) := fun r => by
      rw [map_mul, Polynomial.aeval_X]
    have e2 : ∀ r : Polynomial (ZMod 2),
        Polynomial.aeval (a i : F) (r * Polynomial.X) =
          Polynomial.aeval (a i : F) r * (a i : F) := fun r => by
      rw [map_mul, Polynomial.aeval_X]
    rw [pow_succ, ← mul_assoc, e1, e2, Module.End.mul_apply, linOf_apply, hc (scaleAut a x) i,
      scaleAut_apply]
    ring

theorem polyAct_scaleAut [CharP F 2] [Algebra (ZMod 2) F] (a : Fin κ → Fˣ)
    (p : Polynomial (ZMod 2)) (v : Multiplicative (Fin κ → F)) (i : Fin κ) :
    Multiplicative.toAdd (polyAct (scaleAut a) p v) i =
      Polynomial.aeval (a i : F) p * Multiplicative.toAdd v i :=
  aeval_scaleAut_coord a p v i

end Coord

end CFSG.LocalAnalysis.RankThreeUC
