module

public import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.LinearAlgebra.RootGroupSL

open Module

variable {k E : Type} [Field k] [Field E] [Algebra k E]

theorem exists_norm_eq_one_adjoin_eq_top [Finite k] [Finite E] (hd : 2 ≤ Module.finrank k E) :
    ∃ ν : E, Algebra.norm k ν = 1 ∧ IntermediateField.adjoin k ({ν} : Set E) = ⊤ := by
  classical
  let Q := Nat.card k
  let d := Module.finrank k E
  let φ : Eˣ →* kˣ := Units.map (Algebra.norm k)
  let N₁ : Subgroup Eˣ := φ.ker
  haveI : Finite N₁ := inferInstance
  haveI : IsCyclic N₁ := isCyclic_subgroup_units (R := E) N₁
  obtain ⟨ν₀, hgen⟩ := IsCyclic.exists_generator (α := N₁)
  let ν : E := (ν₀ : Eˣ)
  have hQ2 : 2 ≤ Q := by
    have := Finite.one_lt_card (α := k)
    dsimp [Q]; omega
  have hd2 : 2 ≤ d := hd
  have hcardN : Nat.card N₁ * (Q - 1) = Q ^ d - 1 := by
    have h := Subgroup.card_ker_mul_card_of_surjective
      (f := φ) (FiniteField.unitsMap_norm_surjective k E)
    have hk : Nat.card kˣ = Q - 1 := Nat.card_units (α := k)
    have hE : Nat.card E = Q ^ d := by
      simpa [Q, d] using Module.natCard_eq_pow_finrank (K := k) (V := E)
    have hE' : Nat.card Eˣ = Q ^ d - 1 := by
      rw [Nat.card_units (α := E), hE]
    rw [show φ.ker = N₁ from rfl, hk, hE'] at h
    exact h
  have hN : Nat.card N₁ = (Q ^ d - 1) / (Q - 1) := by
    refine Nat.eq_div_of_mul_eq_right (by omega) ?_
    rw [Nat.mul_comm]
    exact hcardN
  have hNgt : Q ^ (d - 1) < Nat.card N₁ := by
    rw [hN, ← Nat.geomSum_eq hQ2 d]
    have hsplit : (∑ k ∈ Finset.range d, Q ^ k)
        = (∑ k ∈ Finset.range (d - 1), Q ^ k) + Q ^ (d - 1) := by
      conv_lhs => rw [show d = d - 1 + 1 by omega]
      rw [Finset.sum_range_succ]
    rw [hsplit]
    have hTpos : 0 < ∑ k ∈ Finset.range (d - 1), Q ^ k := by
      have hmem : 0 ∈ Finset.range (d - 1) := Finset.mem_range.mpr (by omega)
      have hle : (1 : ℕ) ≤ ∑ k ∈ Finset.range (d - 1), Q ^ k := by
        simpa using Finset.single_le_sum (s := Finset.range (d - 1))
          (f := fun k => Q ^ k) (fun k _ => Nat.zero_le _) hmem
      omega
    omega
  have hnorm : Algebra.norm k ν = 1 := by
    have hmem : φ (ν₀ : Eˣ) = 1 := MonoidHom.mem_ker.mp ν₀.2
    have h := congrArg (fun u : kˣ => (u : k)) hmem
    simpa [φ, ν] using h
  have horder : orderOf ν = Nat.card N₁ := by
    rw [show ν = ((ν₀ : Eˣ) : E) from rfl, orderOf_units, Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hgen
  refine ⟨ν, hnorm, ?_⟩
  by_contra hne
  let L : IntermediateField k E := IntermediateField.adjoin k ({ν} : Set E)
  have hLne : L ≠ ⊤ := hne
  have hνL : ν ∈ L := IntermediateField.subset_adjoin k _ (by simp)
  have hν0 : ν ≠ 0 := by
    intro h
    have : Algebra.norm k ν = 0 := by rw [h, Algebra.norm_zero]
    rw [hnorm] at this
    exact one_ne_zero this
  have hνLne : (⟨ν, hνL⟩ : L) ≠ 0 := by
    intro h
    exact hν0 (Subtype.ext_iff.mp h)
  let νL : Lˣ := Units.mk0 ⟨ν, hνL⟩ hνLne
  have horderL : orderOf νL = orderOf ν := by
    have h2 : orderOf νL = orderOf (νL : L) := (orderOf_units).symm
    have h3 : orderOf ν = orderOf (νL : L) := by
      have hinj : Function.Injective (IntermediateField.val L : L →* E) :=
        fun a b h => Subtype.ext h
      have h := orderOf_injective (IntermediateField.val L : L →* E) hinj (νL : L)
      have hval : ((IntermediateField.val L : L →* E)) (νL : L) = ν := rfl
      rw [hval] at h
      exact h
    exact h2.trans h3.symm
  have hdvd : orderOf ν ∣ Nat.card L - 1 := by
    have h := orderOf_dvd_natCard νL
    rw [Nat.card_units (α := L)] at h
    rwa [horderL] at h
  have hLcard : Nat.card L = Q ^ Module.finrank k L := by
    simpa [Q] using Module.natCard_eq_pow_finrank (K := k) (V := L)
  rw [hLcard] at hdvd
  have hf2 : 2 ≤ Module.finrank L E := by
    obtain ⟨x, hxL⟩ : ∃ x : E, x ∉ L := by
      by_contra h
      apply hLne
      ext y
      simp only [IntermediateField.mem_top, iff_true]
      by_contra hy
      exact h ⟨y, hy⟩
    have hlind : LinearIndependent L ![(1 : E), x] :=
      (LinearIndependent.pair_iff' (x := (1 : E)) (y := x) one_ne_zero).mpr (by
        intro a ha
        apply hxL
        have hsmul : a • (1 : E) = (a : E) := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rw [← ha, hsmul]
        exact a.2)
    simpa using hlind.fintype_card_le_finrank
  have he1 : 1 ≤ Module.finrank k L := by
    have : 0 < Module.finrank k L := finrank_pos_iff.mpr inferInstance
    omega
  have he_le : Module.finrank k L ≤ d - 1 := by
    have hd_eq : d = Module.finrank k L * Module.finrank L E :=
      (Module.finrank_mul_finrank k L E).symm
    have h2 : Module.finrank k L * 2 ≤ Module.finrank k L * Module.finrank L E :=
      Nat.mul_le_mul_left _ hf2
    have h3 : Module.finrank k L + 1 ≤ Module.finrank k L * 2 := by omega
    have h4 : Module.finrank k L + 1 ≤ d := by
      rw [hd_eq]; exact h3.trans h2
    omega
  have hQe2 : 2 ≤ Q ^ Module.finrank k L := by
    calc 2 ≤ Q := hQ2
      _ = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ Module.finrank k L := Nat.pow_le_pow_right (by omega) he1
  have hle : orderOf ν ≤ Q ^ Module.finrank k L - 1 :=
    Nat.le_of_dvd (by omega) hdvd
  have hQe_le : Q ^ Module.finrank k L ≤ Q ^ (d - 1) :=
    Nat.pow_le_pow_right (by omega) he_le
  have : Q ^ (d - 1) < orderOf ν := by rw [horder]; exact hNgt
  omega

theorem det_mulLeft_eq_norm (e : E ≃ₗ[k] E) (x : E)
    (he : (e : E →ₗ[k] E) = LinearMap.mulLeft k x) :
    ((LinearEquiv.det e : kˣ) : k) = Algebra.norm k x := by
  have h : Algebra.lmul k E x = LinearMap.mulLeft k x := LinearMap.ext fun _ => rfl
  rw [Algebra.norm_apply, LinearEquiv.coe_det, he, h]

variable {X : Type} [AddCommGroup X] [Module k X] [Module.Finite k X]

private lemma prod_fin_ite_lt {M : Type*} [CommMonoid M] (d m : ℕ) (hm : m ≤ d) (a : M) :
    (∏ i : Fin d, if (i : ℕ) < m then a else 1) = a ^ m := by
  induction d with
  | zero =>
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
      subst hm0
      simp
  | succ d ih =>
      rw [Fin.prod_univ_castSucc]
      rcases Nat.lt_or_ge m (d + 1) with hm' | hm'
      · have hmle : m ≤ d := Nat.lt_succ_iff.mp hm'
        have hlast : ¬ (d < m) := by omega
        rw [Fin.val_last, if_neg hlast, mul_one]
        have hcast : (∏ i : Fin d, if ((Fin.castSucc i : Fin (d + 1)) : ℕ) < m then a else 1)
            = (∏ i : Fin d, if (i : ℕ) < m then a else 1) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          simp
        rw [hcast, ih hmle]
      · have hmeq : m = d + 1 := le_antisymm hm hm'
        subst hmeq
        have hfirst : (∏ i : Fin d, if ((Fin.castSucc i : Fin (d + 1)) : ℕ) < d + 1 then a else 1)
            = a ^ d := by
          refine (Finset.prod_congr rfl fun i _ => ?_).trans (Fin.prod_const d a)
          simp [i.isLt]
        rw [hfirst, Fin.val_last, if_pos (Nat.lt_succ_self d), pow_succ]

theorem exists_linearEquiv_det_pow_no_eigenvalue (m : ℕ) (hm : m ≤ Module.finrank k X)
    (s : kˣ) (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1) :
    ∃ g : X ≃ₗ[k] X, LinearEquiv.det g = s⁻¹ ^ m ∧ g ^ orderOf s = 1 ∧
      (∀ x : X, g x = (s : k) • x → x = 0) ∧
      (m < Module.finrank k X → ∃ x : X, x ≠ 0 ∧ g x = x) ∧
      (m < Module.finrank k X →
        ∃ f : Module.Dual k X, f ≠ 0 ∧ f ∘ₗ g.symm.toLinearMap = f) := by
  classical
  let d := Module.finrank k X
  let b : Basis (Fin d) k X := Module.finBasis k X
  let D : Fin d → kˣ := fun i => if (i : ℕ) < m then s⁻¹ else 1
  let M : Matrix (Fin d) (Fin d) k := Matrix.diagonal fun i => (D i : k)
  have hDcoe : ∀ i : Fin d, (D i : k) = if (i : ℕ) < m then ((s⁻¹ : kˣ) : k) else 1 := by
    intro i
    simp only [D]
    split <;> rfl
  have hunit : IsUnit (LinearMap.toMatrix b b (Matrix.toLin b b M)).det := by
    rw [LinearMap.toMatrix_toLin, Matrix.det_diagonal]
    have hcoe : ((∏ i, D i : kˣ) : k) = ∏ i, ((D i : kˣ) : k) := by simp
    rw [← hcoe]
    exact (∏ i, D i).isUnit
  let g : X ≃ₗ[k] X :=
    LinearEquiv.ofIsUnitDet (v := b) (v' := b) (f := Matrix.toLin b b M) hunit
  have hg : (g : X →ₗ[k] X) = Matrix.toLin b b M := rfl
  have hsinv_ne : (s⁻¹ : kˣ) ≠ s := by
    intro h
    apply hs2
    rw [pow_two, ← inv_eq_iff_mul_eq_one]
    exact h
  have hD_ne : ∀ i : Fin d, (D i : k) ≠ (s : k) := by
    intro i h
    rw [hDcoe i] at h
    split_ifs at h with hi
    · exact hsinv_ne (Units.ext h)
    · exact hs1 (Units.ext h).symm
  have hDi : ∀ i : Fin d, (D i : k) ^ orderOf s = 1 := by
    intro i
    have hs_pow : ((s⁻¹ : kˣ) : k) ^ orderOf s = 1 := by
      have h1 : (s⁻¹ : kˣ) ^ orderOf s = 1 := by
        rw [← orderOf_inv (s : kˣ)]
        exact pow_orderOf_eq_one _
      calc ((s⁻¹ : kˣ) : k) ^ orderOf s
          = (((s⁻¹ : kˣ) ^ orderOf s : kˣ) : k) :=
            (map_pow (Units.coeHom k) (s⁻¹) (orderOf s)).symm
        _ = 1 := by rw [h1]; rfl
    rw [hDcoe i]
    split_ifs with hi
    · exact hs_pow
    · simp
  have hpowM : M ^ orderOf s = 1 := by
    have hfun : (fun i : Fin d => (D i : k)) ^ orderOf s = (1 : Fin d → k) := by
      funext i
      simpa using hDi i
    rw [show M = Matrix.diagonal (fun i => (D i : k)) from rfl, Matrix.diagonal_pow, hfun]
    exact Matrix.diagonal_one
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply Units.ext
    rw [LinearEquiv.coe_det, hg, LinearMap.det_toLin, Matrix.det_diagonal]
    rw [show (∏ i, (D i : k)) = ((s⁻¹ : kˣ) : k) ^ m from by
      rw [show (fun i : Fin d => (D i : k))
          = (fun i : Fin d => if (i : ℕ) < m then ((s⁻¹ : kˣ) : k) else 1) from funext hDcoe]
      exact prod_fin_ite_lt d m hm ((s⁻¹ : kˣ) : k)]
    exact (map_pow (Units.coeHom k) (s⁻¹) m).symm
  ·
    apply LinearEquiv.toLinearMap_injective
    change LinearEquiv.automorphismGroup.toLinearMapMonoidHom (g ^ orderOf s) = 1
    rw [map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := k) (M := X)) g
      (orderOf s)]
    change ((g : X →ₗ[k] X) ^ orderOf s) = 1
    rw [hg, ← Matrix.toLin_pow, hpowM, Matrix.toLin_one]
    rfl
  ·
    intro x hx
    have hrepr : b.repr (g x) = M.mulVec (b.repr x) := by
      change b.repr ((g : X →ₗ[k] X) x) = M.mulVec (b.repr x)
      rw [hg]
      exact Matrix.repr_toLin b b M x
    have h5 : M.mulVec (b.repr x) = (s : k) • (b.repr x : Fin d → k) := by
      rw [← hrepr, hx, map_smul]
      rfl
    have hcoord : ∀ i : Fin d, b.repr x i = 0 := by
      intro i
      by_contra hne
      have h6 := congrFun h5 i
      rw [show (M.mulVec (b.repr x)) i = (D i : k) * (b.repr x i) from by
        rw [show M = Matrix.diagonal (fun i => (D i : k)) from rfl, Matrix.mulVec_diagonal],
        Pi.smul_apply] at h6
      exact hD_ne i (mul_right_cancel₀ hne h6)
    have hzero : b.repr x = 0 := by
      ext i
      exact hcoord i
    exact b.repr.injective (by simpa using hzero)
  ·
    intro hm'
    let i₀ : Fin d := ⟨m, hm'⟩
    have hDi₀ : (D i₀ : k) = 1 := by
      have h : ¬ (i₀ : ℕ) < m := by
        rw [show (i₀ : ℕ) = m from rfl]
        exact lt_irrefl m
      rw [hDcoe i₀, if_neg h]
    refine ⟨b i₀, b.ne_zero i₀, ?_⟩
    change (g : X →ₗ[k] X) (b i₀) = b i₀
    rw [hg, Matrix.toLin_self]
    rw [Finset.sum_eq_single i₀]
    · rw [show M i₀ i₀ = (D i₀ : k) from by
        rw [show M = Matrix.diagonal (fun i => (D i : k)) from rfl, Matrix.diagonal_apply_eq]]
      rw [hDi₀, one_smul]
    · intro j _ hj
      rw [show M j i₀ = 0 from by
        rw [show M = Matrix.diagonal (fun i => (D i : k)) from rfl,
          Matrix.diagonal_apply_ne _ hj]]
      simp
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  ·
    intro hm'
    let i₀ : Fin d := ⟨m, hm'⟩
    have hDi₀ : (D i₀ : k) = 1 := by
      have h : ¬ (i₀ : ℕ) < m := by
        rw [show (i₀ : ℕ) = m from rfl]
        exact lt_irrefl m
      rw [hDcoe i₀, if_neg h]
    refine ⟨b.coord i₀, ?_, ?_⟩
    · intro hf
      have h1 : b.coord i₀ (b i₀) = 1 := by simp [Basis.coord_apply]
      rw [hf] at h1
      simpa using h1
    · have hfg : ∀ y : X, b.coord i₀ (g y) = b.coord i₀ y := by
        intro y
        have hrepr : b.repr (g y) = M.mulVec (b.repr y) := by
          change b.repr ((g : X →ₗ[k] X) y) = M.mulVec (b.repr y)
          rw [hg]
          exact Matrix.repr_toLin b b M y
        rw [Basis.coord_apply, Basis.coord_apply, hrepr]
        rw [show (M.mulVec (b.repr y)) i₀ = (D i₀ : k) * (b.repr y) i₀ from by
          rw [show M = Matrix.diagonal (fun i => (D i : k)) from rfl, Matrix.mulVec_diagonal]]
        rw [hDi₀, one_mul]
      ext x
      change b.coord i₀ (g.symm x) = b.coord i₀ x
      have hy : g (g.symm x) = x := g.apply_symm_apply x
      calc b.coord i₀ (g.symm x) = b.coord i₀ (g (g.symm x)) := (hfg (g.symm x)).symm
        _ = b.coord i₀ x := by rw [hy]

end CFSG.LinearAlgebra.RootGroupSL
