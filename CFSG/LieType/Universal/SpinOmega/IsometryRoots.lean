module

public import CFSG.LieType.Universal.SpinOmega.PlusIncl
import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryBasic
import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
import CFSG.LieType.Universal.SpinOmega.Kernel
import CFSG.RankThree.PartOne.KC.OrthogonalSupportedMaps

public section

namespace CFSG.LieType.Universal.Spin

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

variable {m n : ℕ} {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem coe_commutatorEquivSpinPlusOfIsometry_symm_apply (e : Q.IsometryEquiv (quadPlus n K))
    (hn : 3 ≤ n) (h2 : (2 : K) = 0) (x : spinGroup (quadPlus n K)) :
    ((commutatorEquivSpinPlusOfIsometry e hn h2).symm x : V ≃ₗ[K] V) =
      (LinearEquiv.autCongr e.toLinearEquiv).symm (spinAction (quadPlus n K) x) := by
  have h := spinAction_commutatorEquivSpinPlusOfIsometry_apply e hn h2
    ((commutatorEquivSpinPlusOfIsometry e hn h2).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, MulEquiv.symm_apply_apply]

private theorem isometryEquiv_polar_symm (e : Q.IsometryEquiv (quadPlus n K))
    (a b : Fin n ⊕ Fin n → K) :
    polar Q (e.symm a) (e.symm b) = polar (quadPlus n K) a b := by
  rw [← CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_isometry e
    (e.symm a) (e.symm b), e.apply_symm_apply, e.apply_symm_apply]

theorem coe_commutatorEquivSpinPlusOfIsometry_symm_longRoot
    (e : Q.IsometryEquiv (quadPlus n K)) (hn : 3 ≤ n) (h2 : (2 : K) = 0) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (c : K) :
    ((commutatorEquivSpinPlusOfIsometry e hn h2).symm
        ((plusFrame n K hn).longRoot hij s t (Multiplicative.ofAdd c)) : V ≃ₗ[K] V) =
      eichler Q (e.symm (plusVec n K j t)) (c • e.symm (plusVec n K i s)) := by
  rw [coe_commutatorEquivSpinPlusOfIsometry_symm_apply e hn h2,
    HypFrame.spinAction_longRoot_eq_eichler,
    CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.eichler_isometry_symm]
  simp

private theorem eichler_mem_orthDerived_of_ne_zero_ne_one
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W] {R : QuadraticForm F W}
    (hR : (polarBilin R).Nondegenerate) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (u w : W) :
    eichler R u w ∈ CFSG.RankThree.Classical2.orthDerived R := by
  by_cases h : R u = 0 ∧ polar R u w = 0
  swap
  · rw [eichler_of_not h]
    exact one_mem _
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact one_mem _
  obtain ⟨y, hy⟩ : ∃ y, polar R u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hR.1 u fun v => by rw [polarBilin_apply_apply]; exact hcon v)
  obtain ⟨y', hy'⟩ : ∃ y', polar R u y' = 1 :=
    ⟨(polar R u y)⁻¹ • y, by rw [polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have huu : polar R u u = 0 := polar_self_eq_zero h.1
  obtain ⟨f, hQf, hpf⟩ : ∃ f, R f = 0 ∧ polar R u f = 1 := by
    refine ⟨y' + (-R y') • u, ?_, ?_⟩
    · rw [QuadraticMap.map_add R, QuadraticMap.map_smul, h.1, smul_zero, add_zero,
        polar_smul_right, polar_comm, hy', smul_eq_mul, mul_one, add_neg_cancel]
    · rw [polar_add_right, polar_smul_right, huu, smul_zero, add_zero, hy']
  let P : HypPair R := ⟨u, f, h.1, hQf, hpf⟩
  have hw₀ : P.proj w ∈ P.perp := P.proj_mem_perp w
  have hwu : polar R w u = 0 := by rw [polar_comm]; exact h.2
  have hw : w = P.proj w + polar R w f • u := by
    change w = (w - polar R w f • u - polar R w u • f) + polar R w f • u
    rw [hwu, zero_smul, sub_zero, sub_add_cancel]
  have hE : eichler R u w = eichler R P.e (P.proj w) := by
    change eichler R u w = eichler R u (P.proj w)
    conv_lhs => rw [hw]
    exact eichler_add_smul_self h.1 _ _
  rw [hE]
  exact CFSG.RankThree.Classical.eichler_mem_commutator_orthogonalGroup hc0 hc1 P hw₀

theorem map_longRoot_range_le_supportedDerived (hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1)
    (e : Q.IsometryEquiv (quadPlus n K)) (hn : 3 ≤ n) (h2 : (2 : K) = 0)
    {P : Submodule K V} (hP : (polarBilin (Q.comp P.subtype)).Nondegenerate) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool) (hi : e.symm (plusVec n K i s) ∈ P)
    (hj : e.symm (plusVec n K j t) ∈ P) :
    ((plusFrame n K hn).longRoot hij s t).range.map
        (commutatorEquivSpinPlusOfIsometry e hn h2).symm.toMonoidHom ≤
      (supportedDerived Q P).subgroupOf
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rintro y hy
  rw [Subgroup.mem_subgroupOf]
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨c, rfl⟩ := Multiplicative.ofAdd.surjective a
  change ((commutatorEquivSpinPlusOfIsometry e hn h2).symm
      ((plusFrame n K hn).longRoot hij s t (Multiplicative.ofAdd c)) : V ≃ₗ[K] V) ∈
    supportedDerived Q P
  rw [coe_commutatorEquivSpinPlusOfIsometry_symm_longRoot e hn h2 hij s t c]
  obtain ⟨c₀, hc0, hc1⟩ := hK
  refine eichler_mem_supportedDerived hj (P.smul_mem c hi) ?_ ?_ ?_
  · rw [← e.map_app (e.symm (plusVec n K j t)), e.apply_symm_apply, quadPlus_plusVec]
  · rw [polar_smul_right_eq, isometryEquiv_polar_symm e (plusVec n K j t) (plusVec n K i s),
      polar_quadPlus_plusVec, if_neg (fun h => hij h.1.symm), mul_zero]
  · exact eichler_mem_orthDerived_of_ne_zero_ne_one hP hc0 hc1 _ _

private theorem autCongrLinear_symm_eq {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    (LinearEquiv.autCongr e).symm = LinearEquiv.autCongr e.symm := by
  ext f
  rw [LinearEquiv.autCongr_symm_apply, LinearEquiv.autCongr_apply, LinearEquiv.symm_symm]

theorem map_range_spinGroupMap_plusIncl [Finite K] (e : Q.IsometryEquiv (quadPlus n K))
    (hn : 3 ≤ n) (h2 : (2 : K) = 0) (hm : 3 ≤ m) (σ : Fin m ↪ Fin n) :
    (plusIncl (K := K) σ).spinGroupMap.range.map
        (commutatorEquivSpinPlusOfIsometry e hn h2).symm.toMonoidHom =
      (supportedDerived Q
          ((plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap)).subgroupOf
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have : Algebra.IsCentral K (CliffordAlgebra (quadPlus n K)) :=
    isCentral_cliffordAlgebra_quadPlus (K := K) (n := n)
  have hf : Function.Injective (spinAction (quadPlus n K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinAction_eq_bot_of_isCentral (quadPlus n K) h2)
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    have hx' : spinAction (quadPlus n K) x ∈
        supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) := by
      rw [← map_spinAction_range_spinGroupMap_plusIncl h2 hm σ]
      exact Subgroup.mem_map_of_mem _ hx
    have hx'' : LinearEquiv.autCongr e.symm.toLinearEquiv (spinAction (quadPlus n K) x) ∈
        supportedDerived Q
          ((plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap) := by
      rw [← map_supportedDerived_isometryEquiv (e := e.symm)
        (R := plusInclRange (K := K) σ)]
      exact Subgroup.mem_map_of_mem _ hx'
    change ((commutatorEquivSpinPlusOfIsometry e hn h2).symm x : V ≃ₗ[K] V) ∈
      supportedDerived Q ((plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap)
    rw [coe_commutatorEquivSpinPlusOfIsometry_symm_apply, autCongrLinear_symm_eq]
    exact hx''
  · intro g hg
    have hgS : (g : V ≃ₗ[K] V) ∈ supportedDerived Q
        ((plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap) := by
      rwa [Subgroup.mem_subgroupOf] at hg
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm]
    have hmap : ((plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap).map
        e.toLinearEquiv.toLinearMap = plusInclRange (K := K) σ := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨w, hw, hzw⟩
        rw [← hzw]
        simpa using hw
      · intro hy
        refine ⟨e.symm y, ⟨y, hy, rfl⟩, ?_⟩
        exact e.apply_symm_apply y
    have hx'' : LinearEquiv.autCongr e.toLinearEquiv (g : V ≃ₗ[K] V) ∈
        supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) := by
      rw [← hmap, ← map_supportedDerived_isometryEquiv (e := e)
        (R := (plusInclRange (K := K) σ).map e.symm.toLinearEquiv.toLinearMap)]
      exact Subgroup.mem_map_of_mem _ hgS
    have hxSd' : spinAction (quadPlus n K)
        (commutatorEquivSpinPlusOfIsometry e hn h2 g) ∈
        supportedDerived (quadPlus n K) (plusInclRange (K := K) σ) := by
      rw [spinAction_commutatorEquivSpinPlusOfIsometry_apply]
      exact hx''
    have hmemmap : spinAction (quadPlus n K)
        (commutatorEquivSpinPlusOfIsometry e hn h2 g) ∈
        (plusIncl (K := K) σ).spinGroupMap.range.map (spinAction (quadPlus n K)) := by
      rw [map_spinAction_range_spinGroupMap_plusIncl h2 hm σ]
      exact hxSd'
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hmemmap
    rwa [hf haeq] at ha

end CFSG.LieType.Universal.Spin

end
