module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAN24Blk
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Matrix CFSG.OddStandard.AltStdSmall4.GL62

private theorem n24_pi_single_castAdd (a : Fin 3) :
    (Pi.single (Fin.castAdd 3 a) (1 : ZMod 2)) = Fin.append (Pi.single a 1) 0 := by
  funext i
  refine Fin.addCases (fun b => ?_) (fun b => ?_) i
  · rw [Fin.append_left]
    by_cases h : b = a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_inj.mp h')), Pi.single_eq_of_ne h]
  · rw [Fin.append_right, Pi.single_eq_of_ne (i := Fin.castAdd 3 a) (i' := Fin.natAdd 3 b) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega)]
    rfl

private theorem n24_pi_single_natAdd (a : Fin 3) :
    (Pi.single (Fin.natAdd 3 a) (1 : ZMod 2)) = Fin.append 0 (Pi.single a 1) := by
  funext i
  refine Fin.addCases (fun b => ?_) (fun b => ?_) i
  · rw [Fin.append_left, Pi.single_eq_of_ne (i := Fin.natAdd 3 a) (i' := Fin.castAdd 3 b) (by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega)]
    rfl
  · rw [Fin.append_right]
    by_cases h : b = a
    · subst h; simp
    · rw [Pi.single_eq_of_ne
        (fun h' => h ((Fin.natAdd_inj 3).mp (by simpa [← Fin.natAdd_eq_addNat] using h'))),
        Pi.single_eq_of_ne h]

private theorem n24_zLin_single_castAdd (a : Fin 3) :
    zLin (Pi.single (Fin.castAdd 3 a) 1) = Pi.single (Fin.castAdd 3 a) 1 := by
  rw [n24_pi_single_castAdd, zLin_apply, fst_append, snd_append, add_zero]

private theorem n24_zLin_single_natAdd (a : Fin 3) :
    zLin (Pi.single (Fin.natAdd 3 a) 1) =
      Pi.single (Fin.castAdd 3 a) 1 + Pi.single (Fin.natAdd 3 a) 1 := by
  rw [n24_pi_single_natAdd, zLin_apply, fst_append, snd_append, zero_add,
    n24_pi_single_castAdd, ← append_add (Pi.single a 1) 0 0 (Pi.single a 1), add_zero, zero_add]

theorem n24_conj_z0 (τ : GL (Fin 6) (ZMod 2)) (hτ : τ * τ = 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (Matrix.toLin' ((τ : Matrix (Fin 6) (Fin 6) (ZMod 2)) + 1))) = 3) :
    ∃ g : GL (Fin 6) (ZMod 2), g * τ * g⁻¹ = z₀ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E := Fin 6 → ZMod 2
  let M : Matrix (Fin 6) (Fin 6) (ZMod 2) := (τ : Matrix (Fin 6) (Fin 6) (ZMod 2))
  have hM : M * M = 1 := by
    have := congrArg (fun u : GL (Fin 6) (ZMod 2) => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) hτ
    simpa [M] using this
  let τ' : E →ₗ[ZMod 2] E := Matrix.toLin' M
  let N : E →ₗ[ZMod 2] E := Matrix.toLin' (M + 1)
  have hr' : Module.finrank (ZMod 2) (LinearMap.range N) = 3 := hr
  have hτ' : τ' * τ' = 1 := by
    rw [show τ' = Matrix.toLin' M from rfl, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hM,
      Matrix.toLin'_one]
    rfl
  have hN' : N = τ' + 1 := by
    show Matrix.toLin' (M + 1) = Matrix.toLin' M + 1
    rw [map_add, Matrix.toLin'_one]
    rfl
  have hadd : ∀ x : E, x + x = 0 := by
    intro x
    ext i
    exact CharTwo.add_self_eq_zero (x i)
  have hτ'_apply : ∀ x : E, τ' (τ' x) = x := by
    intro x
    have h := congrArg (fun f : E →ₗ[ZMod 2] E => f x) hτ'
    simpa using h
  have hN2 : N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply]
    have hNx : N x = τ' x + x := by rw [hN']; rfl
    rw [hNx, hN', LinearMap.add_apply, Module.End.one_apply, map_add, hτ'_apply,
      add_comm (τ' x) x]
    exact hadd (x + τ' x)
  have hle : LinearMap.range N ≤ LinearMap.ker N := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have h := congrArg (fun f : E →ₗ[ZMod 2] E => f y) hN2
    simpa [Module.End.mul_apply] using h
  have hker : Module.finrank (ZMod 2) (LinearMap.ker N) = 3 := by
    have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker N)
    rw [LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange N), hr',
      Module.finrank_fin_fun] at h
    omega
  let W : Submodule (ZMod 2) E := LinearMap.range N
  have hrW : Module.finrank (ZMod 2) W = 3 := hr'
  have hWeq : W = LinearMap.ker N :=
    Submodule.eq_of_le_of_finrank_eq (K := ZMod 2) (S₁ := W) (S₂ := LinearMap.ker N)
      hle (by rw [hrW, hker])
  obtain ⟨V, hcompl⟩ := Submodule.exists_isCompl W
  let ψ : V →ₗ[ZMod 2] W :=
    (LinearMap.codRestrict W N (fun x => LinearMap.mem_range_self N x)).comp V.subtype
  have hψinj : Function.Injective ψ := by
    intro u v huv
    have hN : N ((u : E) - (v : E)) = 0 := by
      have h : N (u : E) = N (v : E) := by
        have := congrArg (fun w : W => (w : E)) huv
        change N (u : E) = N (v : E) at this
        exact this
      rw [map_sub, h, sub_self]
    have hdW : (u : E) - (v : E) ∈ W := by rw [hWeq]; exact hN
    have hdV : (u : E) - (v : E) ∈ V := V.sub_mem u.2 v.2
    have hbot : (u : E) - (v : E) ∈ (⊥ : Submodule (ZMod 2) E) := by
      rw [← hcompl.inf_eq_bot]; exact ⟨hdW, hdV⟩
    exact Subtype.ext (sub_eq_zero.mp ((Submodule.mem_bot (ZMod 2)).mp hbot))
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    rw [LinearMap.mem_range] at hw
    obtain ⟨x, rfl⟩ := hw
    have hx : x ∈ W ⊔ V := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    change N b = N x
    have ha0 : N a = 0 := LinearMap.mem_ker.mp (hWeq ▸ ha)
    rw [← hab, map_add, ha0, zero_add]
  have hψbij : Function.Bijective ψ := ⟨hψinj, hψsurj⟩
  let φ : V ≃ₗ[ZMod 2] W := LinearEquiv.ofBijective ψ hψbij
  have hVfin : Module.finrank (ZMod 2) V = 3 := by rw [LinearEquiv.finrank_eq φ, hrW]
  let bV : Module.Basis (Fin 3) (ZMod 2) V := Module.finBasisOfFinrankEq (ZMod 2) V hVfin
  let bW : Module.Basis (Fin 3) (ZMod 2) W := bV.map φ
  let bprod : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) (W × V) := bW.prod bV
  let bE : Module.Basis (Fin 3 ⊕ Fin 3) (ZMod 2) E :=
    bprod.map (Submodule.prodEquivOfIsCompl W V hcompl)
  let b : Module.Basis (Fin 6) (ZMod 2) E := bE.reindex n24Eq
  have hb_cast : ∀ a : Fin 3, b (Fin.castAdd 3 a) = N (bV a) := by
    intro a
    rw [show b = bE.reindex n24Eq from rfl, Module.Basis.reindex_apply, n24Eq_symm_castAdd,
      show bE = bprod.map (Submodule.prodEquivOfIsCompl W V hcompl) from rfl,
      Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    have h3 : bprod (Sum.inl a) = (bW a, 0) := by
      rw [show bprod = bW.prod bV from rfl, Module.Basis.prod_apply]
      rfl
    rw [h3]
    change (bW a : E) + 0 = N (bV a)
    rw [add_zero]
    rfl
  have hb_nat : ∀ a : Fin 3, b (Fin.natAdd 3 a) = (bV a : E) := by
    intro a
    rw [show b = bE.reindex n24Eq from rfl, Module.Basis.reindex_apply, n24Eq_symm_natAdd,
      show bE = bprod.map (Submodule.prodEquivOfIsCompl W V hcompl) from rfl,
      Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
    have h3 : bprod (Sum.inr a) = (0, bV a) := by
      rw [show bprod = bW.prod bV from rfl, Module.Basis.prod_apply]
      rfl
    rw [h3]
    change (0 : E) + (bV a : E) = (bV a : E)
    rw [zero_add]
  have hτ'_fix : ∀ x : E, τ' (N x) = N x := by
    intro x
    have hNx : N x = τ' x + x := by rw [hN']; rfl
    rw [hNx, map_add, hτ'_apply]
    exact add_comm x (τ' x)
  have hτ'_add : ∀ x : E, τ' x = x + N x := by
    intro x
    have hNx : N x = τ' x + x := by rw [hN']; rfl
    rw [hNx, add_comm (τ' x) x, ← add_assoc, hadd, zero_add]
  let e : E ≃ₗ[ZMod 2] E := b.equivFun.symm
  have he_std : ∀ i : Fin 6, (e : E →ₗ[ZMod 2] E) (Pi.single i 1) = b i := by
    intro i
    change e (Pi.single i 1) = b i
    rw [show e = b.equivFun.symm from rfl, Module.Basis.equivFun_symm_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hconj : τ' * e = e * zLin := by
    refine (Pi.basisFun (ZMod 2) (Fin 6)).ext fun i => ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, Pi.basisFun_apply, he_std]
    refine Fin.addCases (m := 3) (n := 3) (fun a => ?_) (fun a => ?_) i
    · rw [hb_cast, n24_zLin_single_castAdd, he_std, hb_cast]
      exact hτ'_fix (bV a)
    · rw [hb_nat, n24_zLin_single_natAdd, map_add, he_std, he_std, hb_cast, hb_nat,
        hτ'_add]
      exact add_comm (bV a : E) (N (bV a))
  have hconj' : (e.symm : E →ₗ[ZMod 2] E) * τ' * e = zLin := by
    refine LinearMap.ext fun x => ?_
    have h := congrArg (fun f : E →ₗ[ZMod 2] E => f x) hconj
    simp only [Module.End.mul_apply] at h
    rw [Module.End.mul_apply, Module.End.mul_apply, h]
    change e.symm (e (zLin x)) = zLin x
    exact e.symm_apply_apply (zLin x)
  let E' : LinearMap.GeneralLinearGroup (ZMod 2) E :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv e.symm
  have hEval : (E' : E →ₗ[ZMod 2] E) = e.symm := by
    refine LinearMap.ext fun x => ?_
    exact congrFun (LinearMap.GeneralLinearGroup.coe_ofLinearEquiv e.symm) x
  have hEinv : E'⁻¹ = LinearMap.GeneralLinearGroup.ofLinearEquiv e := by
    rw [show E' = LinearMap.GeneralLinearGroup.ofLinearEquiv e.symm from rfl,
      ← LinearMap.GeneralLinearGroup.ofLinearEquiv_inv]
    exact congrArg LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.symm_symm e)
  have hEinvval : (↑(E'⁻¹) : E →ₗ[ZMod 2] E) = e := by
    rw [hEinv]
    refine LinearMap.ext fun x => ?_
    exact congrFun (LinearMap.GeneralLinearGroup.coe_ofLinearEquiv e) x
  have hτlin : (Matrix.GeneralLinearGroup.toLin τ : E →ₗ[ZMod 2] E) = τ' := by
    rw [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
  have hzlin : (Matrix.GeneralLinearGroup.toLin z₀ : E →ₗ[ZMod 2] E) = zLin := by
    rw [Matrix.GeneralLinearGroup.coe_toLin, ← Matrix.toLin'_apply']
    change Matrix.toLin' (LinearMap.toMatrix' zLin) = zLin
    rw [Matrix.toLin'_toMatrix']
  have hgroup : E' * Matrix.GeneralLinearGroup.toLin τ * E'⁻¹ =
      Matrix.GeneralLinearGroup.toLin z₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hEval, hEinvval, hτlin, hzlin]
    exact hconj'
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm E', ?_⟩
  apply Matrix.GeneralLinearGroup.toLin.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hgroup

end CFSG.OddStandard.HigherRank.YamadaG23
