module

public import CFSG.Assembly.E6FourDiagonalData
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcD4
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.Assembly.E6FourCentOrbit
public import CFSG.Assembly.E6FourCentTwist
public import CFSG.Assembly.E6FourCentTyped

public noncomputable section

namespace CFSG.Assembly.E6FourDiagonal

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration CFSG.Assembly.E6FourCentChk
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.StandardType.N2E6Native
open scoped Matrix

private theorem mask_finite (c : ℕ) : (e6MaskRoots c).Finite :=
  (Set.finite_range (fun k : Fin 72 => e6RootVec k)).subset fun _ h => by
    obtain ⟨k, hk, -, rfl⟩ := h
    exact ⟨⟨k, hk⟩, rfl⟩

private theorem mask_orbit_one (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = wordMat Tag.E6 e6TwoWord *ᵥ γ)
    {c : ℕ} (hc : c < 2 ^ 72) (hmap : mapMaskP permLit 72 c 0 = c) :
    componentOrbitLength ρ (e6MaskRoots c) = 1 := by
  apply componentOrbitLength_eq_one (mask_finite c)
  have himage : ρ '' e6MaskRoots c = e6MaskRoots c := by
    rw [rho_image_e6MaskRoots ρ hρ hc, hmap]
  intro γ hγ
  rw [← himage]
  exact ⟨γ, hγ, rfl⟩

private theorem exists_table_pair_component
    {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = wordMat Tag.E6 e6TwoWord *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (i j : Fin 4) (hij : i ≠ j)
    (negative : Bool) :
    let v := tablePairWeight i j negative
    ∃ k : KernelComponent (rootCharHom (fun a => ζ ^ (v a).val)),
      componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k =
        kernelRoots (rootCharHom (fun a => ζ ^ (v a).val)) ∧
      compRank (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) = 4 ∧
      (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k).ncard = 24 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) = 1 ∧
      ¬ twistInner (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) ρ := by
  obtain ⟨_, _, hpop, htyped, hclosed, hconn, hne, hmap⟩ := pair_table_check i j hij negative
  let v := tablePairWeight i j negative
  obtain ⟨k, hk⟩ := e6Four_exists_component_eq_kernelRoots_of_connected ζ hζ v hne hclosed hconn
  have hmask : kernelRoots (rootCharHom (fun a => ζ ^ (v a).val)) = e6MaskRoots (e6SolMask v) := by
    rw [e6Four_kernelRoots ζ hζ v, e6MaskRoots_solMask v]
  have hcomp := hk.trans hmask
  obtain ⟨hr, hn⟩ := e6Four_d4_rank_card (e6SolMask_lt v) hpop htyped
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · rw [hcomp]; exact hr
  · rw [hcomp]; exact hn
  · rw [hcomp]; exact mask_orbit_one ρ hρ (e6SolMask_lt v) hmap
  · rw [hcomp]; exact e6Four_d4_twist hρ (e6SolMask_lt v) hpop htyped

private theorem exists_table_axis_component
    {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = wordMat Tag.E6 e6TwoWord *ᵥ γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (i : Fin 4) :
    let v := tableAxisWeight i
    ∃ k : KernelComponent (rootCharHom (fun a => ζ ^ (v a).val)),
      componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k =
        kernelRoots (rootCharHom (fun a => ζ ^ (v a).val)) ∧
      compRank (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) = 5 ∧
      (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k).ncard = 30 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) = 1 ∧
      twistInner (componentRoots (rootCharHom (fun a => ζ ^ (v a).val)) k) ρ := by
  obtain ⟨_, _, hpop, htyped, hclosed, hconn, hne, hmap⟩ := axis_table_check i
  let v := tableAxisWeight i
  obtain ⟨k, hk⟩ := e6Four_exists_component_eq_kernelRoots_of_connected ζ hζ v hne hclosed hconn
  have hmask : kernelRoots (rootCharHom (fun a => ζ ^ (v a).val)) = e6MaskRoots (e6SolMask v) := by
    rw [e6Four_kernelRoots ζ hζ v, e6MaskRoots_solMask v]
  have hcomp := hk.trans hmask
  obtain ⟨hr, hn⟩ := e6Four_a5_rank_card (e6SolMask_lt v) hpop htyped
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · rw [hcomp]; exact hr
  · rw [hcomp]; exact hn
  · rw [hcomp]; exact mask_orbit_one ρ hρ (e6SolMask_lt v) hmap
  · rw [hcomp]; exact e6Four_a5_twist hρ (e6SolMask_lt v) hpop htyped

private noncomputable def toGamma : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd toGammaWord

private noncomputable def tableRho : Equiv.Perm (Fin Tag.E6.rank → ℤ) :=
  MulAction.toPerm ((coxeterSystem Tag.E6).wordProd e6TwoWord)

private noncomputable def nativeRho : Equiv.Perm (Fin Tag.E6.rank → ℤ) :=
  tcrConjPerm toGamma tableRho

private theorem toGamma_apply
    (v : Fin Tag.E6.rank → ℤ) :
    toGamma • v = wordMat Tag.E6 toGammaWord *ᵥ v := by
  rw [toGamma, wordProd_smul_eq_foldr_reflect, wordMat_mulVec_eq_foldr]

private theorem tableRho_apply
    (v : Fin Tag.E6.rank → ℤ) :
    tableRho v = wordMat Tag.E6 e6TwoWord *ᵥ v := by
  change (coxeterSystem Tag.E6).wordProd e6TwoWord • v = _
  rw [wordProd_smul_eq_foldr_reflect, wordMat_mulVec_eq_foldr]

private theorem nativeW_eq_mulVec (v : Fin Tag.E6.rank → ℤ) :
    e6NativeW v = e6NativeWMat *ᵥ v := by
  let W : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
    { toFun := e6NativeW
      map_zero' := by simp [e6NativeW, e6NativePair]
      map_add' := by
        intro x y
        simp only [e6NativeW, e6NativePair, Pi.add_apply, add_mul,
          Finset.sum_add_distrib, add_smul]
        abel }
  have hv : v = ∑ i : Fin Tag.E6.rank, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  calc e6NativeW v = W v := rfl
    _ = W (∑ i : Fin Tag.E6.rank, v i • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) :=
      congrArg W hv
    _ = ∑ i : Fin Tag.E6.rank, v i • W (Pi.single i 1) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_zsmul W _ _
    _ = ∑ i : Fin Tag.E6.rank, v i • (fun k => e6NativeWMat k i) := by
      exact Finset.sum_congr rfl fun i _ => congrArg (fun x => v i • x) (e6NativeW_single i)
    _ = e6NativeWMat *ᵥ v := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem nativeRho_apply
    (v : Fin Tag.E6.rank → ℤ) :
    nativeRho v = e6NativeW v := by
  have hinv : toGamma⁻¹ • v = wordMat Tag.E6 toGammaWord.reverse *ᵥ v := by
    change ((coxeterSystem Tag.E6).wordProd toGammaWord)⁻¹ • v = _
    rw [← CoxeterSystem.wordProd_reverse, wordProd_smul_eq_foldr_reflect,
      wordMat_mulVec_eq_foldr]
  rw [nativeRho, tcrConjPerm_apply, hinv, tableRho_apply, toGamma_apply,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, toGamma_conj_matrix,
    nativeW_eq_mulVec]

private theorem zpow_modFive {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (n : ℤ) :
    ζ ^ n = ζ ^ (n : ZMod 5).val := by
  have hz : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.coe_units_iff.mp hζ
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, hz.eq_orderOf.symm]
  apply (ZMod.intCast_eq_intCast_iff _ _ 5).mp
  simp

private theorem nativeParam_eq {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (a : Fin 4 → ℤ) :
    (fun k => ζ ^ e6NativeChar a k) =
      fun k => ζ ^ (e6NativeChar a k : ZMod 5).val :=
  funext fun k => zpow_modFive ζ hζ (e6NativeChar a k)

private theorem pairing_transform
    (v vt : Fin Tag.E6.rank → ZMod 5)
    (ht : vt = fun k => ∑ j : Fin Tag.E6.rank,
      ((wordMat Tag.E6 toGammaWord j k : ℤ) : ZMod 5) * v j)
    (γ : Fin Tag.E6.rank → ℤ) : e6Pair vt γ = e6Pair v (toGamma • γ) := by
  rw [toGamma_apply]
  simp only [e6Pair, ht, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    Int.cast_sum, Int.cast_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem kernelRoots_transform
    {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (a : Fin 4 → ℤ) (vt : Fin Tag.E6.rank → ZMod 5)
    (ht : vt = fun k => ∑ j : Fin Tag.E6.rank,
      ((wordMat Tag.E6 toGammaWord j k : ℤ) : ZMod 5) * (e6NativeChar a j : ZMod 5)) :
    kernelRoots (rootCharHom (fun k => ζ ^ e6NativeChar a k)) =
      (fun γ => toGamma • γ) '' kernelRoots (rootCharHom (fun k => ζ ^ (vt k).val)) := by
  rw [nativeParam_eq ζ hζ a, e6Four_kernelRoots ζ hζ, e6Four_kernelRoots ζ hζ]
  ext γ
  constructor
  · rintro ⟨hroot, hzero⟩
    refine ⟨toGamma⁻¹ • γ, ⟨(isRoot_smul_iff toGamma⁻¹).mpr hroot, ?_⟩,
      smul_inv_smul toGamma γ⟩
    rw [pairing_transform _ vt ht, smul_inv_smul]
    exact hzero
  · rintro ⟨β, ⟨hroot, hzero⟩, rfl⟩
    refine ⟨(isRoot_smul_iff toGamma).mpr hroot, ?_⟩
    rw [← pairing_transform _ vt ht]
    exact hzero

private theorem tablePairWeight_eq_native (i j : Fin 4) (negative : Bool) :
    tablePairWeight i j negative = fun k => ∑ l : Fin Tag.E6.rank,
      ((wordMat Tag.E6 toGammaWord l k : ℤ) : ZMod 5) *
        (e6NativeChar (Pi.single i 1 + (if negative then (-1 : ℤ) else 1) • Pi.single j 1) l :
          ZMod 5) := by
  fin_cases i <;> fin_cases j <;> cases negative <;> decide +kernel

private theorem component_unique {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hi : componentRoots χ i = kernelRoots χ) : ∀ j : KernelComponent χ, j = i := by
  intro j
  obtain ⟨x, rfl⟩ := Quotient.exists_rep j
  apply eq_of_mem_componentRoots (α := (x : Fin Tag.E6.rank → ℤ))
  · exact ⟨x.2, rfl⟩
  · rw [hi]
    exact x.2

private theorem exists_native_pair_component_bool
    {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = e6NativeW γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (i j : Fin 4) (hij : i ≠ j)
    (negative : Bool) :
    let a := Pi.single i 1 + (if negative then (-1 : ℤ) else 1) • Pi.single j 1
    ∃ k : KernelComponent (rootCharHom (fun b => ζ ^ e6NativeChar a b)),
      (∀ k', k' = k) ∧
      componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k =
        kernelRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) ∧
      compRank (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 4 ∧
      (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k).ncard = 24 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 1 ∧
      ¬ twistInner (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) ρ := by
  let a : Fin 4 → ℤ := Pi.single i 1 + (if negative then (-1 : ℤ) else 1) • Pi.single j 1
  let vt := tablePairWeight i j negative
  let χ := rootCharHom (fun b => ζ ^ e6NativeChar a b)
  let χt := rootCharHom (fun b => ζ ^ (vt b).val)
  obtain ⟨kt, hkt, hr, hn, ho, hout⟩ :=
    exists_table_pair_component tableRho (fun γ _ => tableRho_apply γ) ζ hζ i j hij negative
  have hker : kernelRoots χ = (fun γ => toGamma • γ) '' kernelRoots χt :=
    kernelRoots_transform ζ hζ a vt (tablePairWeight_eq_native i j negative)
  obtain ⟨k, hk⟩ := exists_componentRoots_image toGamma hker kt
  have hkall : componentRoots χ k = kernelRoots χ := by
    rw [hk, hkt]
    exact hker.symm
  have hf : (componentRoots χ k).Finite := by
    rw [hk]
    apply Set.Finite.image
    rw [hkt, e6Four_kernelRoots ζ hζ vt, ← e6MaskRoots_solMask vt]
    exact mask_finite (e6SolMask vt)
  have hstable : ∀ γ ∈ componentRoots χ k, nativeRho γ ∈ componentRoots χ k := by
    rw [hk]
    have hmaskt : componentRoots χt kt = e6MaskRoots (e6SolMask vt) := by
      rw [hkt, e6Four_kernelRoots ζ hζ vt, e6MaskRoots_solMask vt]
    obtain ⟨_, _, _, _, _, _, _, hmap⟩ := pair_table_check i j hij negative
    have htstable : tableRho '' componentRoots χt kt = componentRoots χt kt := by
      rw [hmaskt, rho_image_e6MaskRoots tableRho (fun γ _ => tableRho_apply γ)
        (e6SolMask_lt vt), hmap]
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨tableRho γ, ?_, ?_⟩
    · rw [← htstable]
      exact ⟨γ, hγ, rfl⟩
    · rw [nativeRho, tcrConjPerm_apply, inv_smul_smul]
  refine ⟨k, component_unique χ k hkall, hkall, ?_, ?_, ?_, ?_⟩
  · rw [hk, compRank_image]
    exact hr
  · rw [hk, ncard_image_smul]
    exact hn
  · apply componentOrbitLength_eq_one hf
    intro γ hγ
    rw [hρ γ (by rw [hkall] at hγ; exact hγ.1), ← nativeRho_apply]
    exact hstable γ hγ
  · intro hin
    have hinn : twistInner (componentRoots χ k) nativeRho := by
      obtain ⟨w, hw, he⟩ := hin
      refine ⟨w, hw, fun γ hγ => ?_⟩
      rw [nativeRho_apply, ← hρ γ (by rw [hkall] at hγ; exact hγ.1)]
      exact he γ hγ
    rw [hk] at hinn
    have hfun : (nativeRho : (Fin Tag.E6.rank → ℤ) → _) =
        fun γ => toGamma • tableRho (toGamma⁻¹ • γ) :=
      funext fun γ => tcrConjPerm_apply toGamma tableRho γ
    rw [hfun] at hinn
    exact hout ((twistInner_conj toGamma (componentRoots χt kt) tableRho).mp hinn)

theorem exists_native_pair_component
    {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = e6NativeW γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (i j : Fin 4) (hij : i ≠ j)
    (e : ℤ) (he : e = 1 ∨ e = -1) :
    let a := Pi.single i 1 + e • Pi.single j 1
    ∃ k : KernelComponent (rootCharHom (fun b => ζ ^ e6NativeChar a b)),
      (∀ k', k' = k) ∧
      componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k =
        kernelRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) ∧
      compRank (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 4 ∧
      (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k).ncard = 24 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 1 ∧
      ¬ twistInner (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) ρ := by
  rcases he with rfl | rfl
  · simpa using exists_native_pair_component_bool ρ hρ ζ hζ i j hij false
  · simpa using exists_native_pair_component_bool ρ hρ ζ hζ i j hij true

theorem exists_native_axis_component
    {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hρ : ∀ γ, IsRoot Tag.E6 γ → ρ γ = e6NativeW γ)
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (i : Fin 4) :
    let a := Pi.single i 1
    ∃ k : KernelComponent (rootCharHom (fun b => ζ ^ e6NativeChar a b)),
      (∀ k', k' = k) ∧
      componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k =
        kernelRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) ∧
      compRank (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 5 ∧
      (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k).ncard = 30 ∧
      componentOrbitLength ρ (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) = 1 ∧
      twistInner (componentRoots (rootCharHom (fun b => ζ ^ e6NativeChar a b)) k) ρ := by
  let a : Fin 4 → ℤ := Pi.single i 1
  let vt := tableAxisWeight i
  let χ := rootCharHom (fun b => ζ ^ e6NativeChar a b)
  let χt := rootCharHom (fun b => ζ ^ (vt b).val)
  obtain ⟨kt, hkt, hr, hn, _ho, hin⟩ :=
    exists_table_axis_component tableRho (fun γ _ => tableRho_apply γ) ζ hζ i
  have hker : kernelRoots χ = (fun γ => toGamma • γ) '' kernelRoots χt :=
    kernelRoots_transform ζ hζ a vt (tableAxisWeight_eq i)
  obtain ⟨k, hk⟩ := exists_componentRoots_image toGamma hker kt
  have hkall : componentRoots χ k = kernelRoots χ := by
    rw [hk, hkt]
    exact hker.symm
  have hf : (componentRoots χ k).Finite := by
    rw [hk]
    apply Set.Finite.image
    rw [hkt, e6Four_kernelRoots ζ hζ vt, ← e6MaskRoots_solMask vt]
    exact mask_finite (e6SolMask vt)
  have hstable : ∀ γ ∈ componentRoots χ k, nativeRho γ ∈ componentRoots χ k := by
    rw [hk]
    have hmaskt : componentRoots χt kt = e6MaskRoots (e6SolMask vt) := by
      rw [hkt, e6Four_kernelRoots ζ hζ vt, e6MaskRoots_solMask vt]
    obtain ⟨_, _, _, _, _, _, _, hmap⟩ := axis_table_check i
    have htstable : tableRho '' componentRoots χt kt = componentRoots χt kt := by
      rw [hmaskt, rho_image_e6MaskRoots tableRho (fun γ _ => tableRho_apply γ)
        (e6SolMask_lt vt), hmap]
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨tableRho γ, ?_, ?_⟩
    · rw [← htstable]
      exact ⟨γ, hγ, rfl⟩
    · rw [nativeRho, tcrConjPerm_apply, inv_smul_smul]
  refine ⟨k, component_unique χ k hkall, hkall, ?_, ?_, ?_, ?_⟩
  · rw [hk, compRank_image]
    exact hr
  · rw [hk, ncard_image_smul]
    exact hn
  · apply componentOrbitLength_eq_one hf
    intro γ hγ
    rw [hρ γ (by rw [hkall] at hγ; exact hγ.1), ← nativeRho_apply]
    exact hstable γ hγ
  · have hinn : twistInner (componentRoots χ k) nativeRho := by
      rw [hk]
      have hfun : (nativeRho : (Fin Tag.E6.rank → ℤ) → _) =
          fun γ => toGamma • tableRho (toGamma⁻¹ • γ) :=
        funext fun γ => tcrConjPerm_apply toGamma tableRho γ
      rw [hfun]
      exact (twistInner_conj toGamma (componentRoots χt kt) tableRho).mpr hin
    obtain ⟨w, hw, he⟩ := hinn
    refine ⟨w, hw, fun γ hγ => ?_⟩
    rw [hρ γ (by rw [hkall] at hγ; exact hγ.1), ← nativeRho_apply]
    exact he γ hγ

end CFSG.Assembly.E6FourDiagonal

