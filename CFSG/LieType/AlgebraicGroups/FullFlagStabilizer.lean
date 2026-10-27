module

public import CFSG.LieType.AlgebraicGroups.FullFlagRepresentation
public import CFSG.LieType.AlgebraicGroups.MaximalTorusConjugacy
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Dimension

public noncomputable section

open WithConv TauCeti.Comodule
open scoped TensorProduct MatrixGroups

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v

section TensorGeometry

variable {k W E : Type u} [Field k]
variable [AddCommGroup W] [Module k W] [AddCommGroup E] [Module k E]

theorem left_mem_span_of_tmul_mem_span {x x₀ : W} {y y₀ : E} (hy : y ≠ 0)
    (h : x ⊗ₜ[k] y ∈ k ∙ (x₀ ⊗ₜ[k] y₀)) : x ∈ k ∙ x₀ := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hy
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have he := congrArg (contract (k := k) (W := W) φ) hc
  have hx : (c * φ y₀) • x₀ = x := by
    simpa only [map_smul, contract_tmul, hφ, one_smul, smul_smul] using he
  exact Submodule.mem_span_singleton.mpr ⟨c * φ y₀, hx⟩

theorem right_mem_span_of_tmul_mem_span {x x₀ : W} {y y₀ : E} (hx : x ≠ 0)
    (h : x ⊗ₜ[k] y ∈ k ∙ (x₀ ⊗ₜ[k] y₀)) : y ∈ k ∙ y₀ := by
  apply left_mem_span_of_tmul_mem_span hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact Submodule.mem_span_singleton.mpr ⟨c, by
    simpa only [map_smul, TensorProduct.comm_tmul] using
      congrArg (TensorProduct.comm k W E) hc⟩

theorem exists_basis_extending_family [FiniteDimensional k W] {r : ℕ}
    (v : Fin r → W) (hv : LinearIndependent k v) :
    ∃ (n : ℕ) (b : Module.Basis (Fin (r + n)) k W),
      ∀ i, b (Fin.castAdd n i) = v i := by
  classical
  let U : Submodule k W := Submodule.span k (Set.range v)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl U
  let bU : Module.Basis (Fin r) k U := Module.Basis.span hv
  let b₀ := (bU.prod (Module.finBasis k C)).map (Submodule.prodEquivOfIsCompl U C hC)
  refine ⟨_, b₀.reindex finSumFinEquiv, ?_⟩
  intro i
  simp only [Module.Basis.reindex_apply, finSumFinEquiv_symm_apply_castAdd,
    Module.Basis.map_apply, Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_fst,
    Module.Basis.prod_apply_inl_snd, ZeroMemClass.coe_zero, add_zero, b₀]
  exact Module.Basis.coe_span_apply hv i

theorem exists_basis_extending_family_fin [FiniteDimensional k W] {r d : ℕ}
    (b₀ : Module.Basis (Fin d) k W) (v : Fin r → W) (hv : LinearIndependent k v) (hr : r ≤ d) :
    ∃ b : Module.Basis (Fin d) k W, ∀ i, b (Fin.castLE hr i) = v i := by
  obtain ⟨n, b, hb⟩ := exists_basis_extending_family v hv
  have hd : r + n = d := by
    have h₁ := Module.finrank_eq_card_basis b
    have h₂ := Module.finrank_eq_card_basis b₀
    simpa only [Fintype.card_fin] using h₁.symm.trans h₂
  refine ⟨b.reindex (finCongr hd), ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  have hcast : (finCongr hd).symm (Fin.castLE hr i) = Fin.castAdd n i := by
    apply Fin.ext
    rfl
  rw [hcast, hb]

theorem exteriorBasis_eq_of_eq_on {I : Type*} [Fintype I] [LinearOrder I]
    (b c : Module.Basis I k W) (s : Finset I) (h : ∀ i ∈ s, b i = c i) :
    b.ExteriorAlgebra s = c.ExteriorAlgebra s := by
  classical
  rw [ExteriorAlgebra.basis_apply, ExteriorAlgebra.basis_apply]
  simp only [ExteriorAlgebra.ιMulti_family]
  congr 1
  funext i
  apply h
  exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _).mp
    (Set.mem_range_self i)

theorem initialWedge_eq_of_eq_on {d : ℕ} (b c : Module.Basis (Fin d) k W)
    (r : ℕ) (hr : r ≤ d) (h : ∀ i ∈ firstIndices d r, b i = c i) :
    initialWedge b r hr = initialWedge c r hr := by
  apply Subtype.ext
  rw [initialWedge_coe, initialWedge_coe]
  exact exteriorBasis_eq_of_eq_on b c _ h

theorem basisFlagTensor_eq_of_eq_on {d : ℕ} (b c : Module.Basis (Fin d) k W) :
    ∀ (r : ℕ) (hr : r ≤ d), (∀ i ∈ firstIndices d r, b i = c i) →
      basisFlagTensor b r hr = basisFlagTensor c r hr := by
  intro r
  induction r with
  | zero => intro hr h; rfl
  | succ r ih =>
    intro hr h
    have hprev : ∀ i ∈ firstIndices d r, b i = c i :=
      fun i hi => h i (firstIndices_mono d (Nat.le_succ r) hi)
    rw [basisFlagTensor, basisFlagTensor, ih _ hprev, initialWedge_eq_of_eq_on b c _ _ h]

theorem iota_mul_initialWedge_mem_span {d r : ℕ} (b : Module.Basis (Fin d) k W)
    (hr : r + 1 ≤ d) :
    ExteriorAlgebra.ι k (b ⟨r, by omega⟩) *
        (initialWedge b r (by omega) : ExteriorAlgebra k W) ∈
      k ∙ (initialWedge b (r + 1) hr : ExteriorAlgebra k W) := by
  classical
  let j : Fin d := ⟨r, by omega⟩
  have hj : j ∉ firstIndices d r := by simp [j]
  have hs : insert j (firstIndices d r) = firstIndices d (r + 1) := by
    ext i
    simp only [Finset.mem_insert, mem_firstIndices, Fin.ext_iff, j]
    omega
  change ExteriorAlgebra.ι k (b j) * (initialWedge b r _ : ExteriorAlgebra k W) ∈ _
  simp only [initialWedge_coe]
  rw [TauCeti.ExteriorAlgebra.ι_mul_basis, if_neg hj, hs]
  rcases Int.units_eq_one_or
      (TauCeti.ExteriorAlgebra.basisEraseSign j (firstIndices d (r + 1))) with hsign | hsign
  · simp [hsign]
  · simp [hsign]

theorem exists_basis_of_wedge_extension [FiniteDimensional k W] {d r : ℕ}
    (b : Module.Basis (Fin d) k W) (hr : r + 1 ≤ d) (q : ⋀[k]^(r + 1) W)
    (hq : q ≠ 0) (v : W)
    (hv : (q : ExteriorAlgebra k W) = ExteriorAlgebra.ι k v *
      (initialWedge b r (by omega) : ExteriorAlgebra k W)) :
    ∃ c : Module.Basis (Fin d) k W,
      (∀ i ∈ firstIndices d r, b i = c i) ∧ q ∈ k ∙ initialWedge c (r + 1) hr := by
  let hr₀ : r ≤ d := by omega
  let prior : Fin r → W := fun i => b (Fin.castLE hr₀ i)
  have hprior : LinearIndependent k prior :=
    b.linearIndependent.comp (Fin.castLE hr₀) (by
      intro i j h
      exact Fin.ext (congrArg (fun a : Fin d => a.val) h))
  have hrange : Set.range prior = b '' (firstIndices d r : Set (Fin d)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.castLE hr₀ i, (mem_firstIndices _).mpr i.isLt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i.val, (mem_firstIndices _).mp hi⟩, ?_⟩
      apply congrArg b
      apply Fin.ext
      rfl
  have hnot : v ∉ Submodule.span k (Set.range prior) := by
    rw [hrange]
    intro hmem
    apply hq
    apply Subtype.ext
    rw [hv, initialWedge_coe]
    exact (b.ι_mul_exteriorAlgebra_eq_zero_iff _ v).mpr hmem
  obtain ⟨c, hc⟩ := exists_basis_extending_family_fin b (Fin.snoc prior v)
    (hprior.finSnoc hnot) hr
  have hprefix : ∀ i ∈ firstIndices d r, b i = c i := by
    intro i hi
    let a : Fin r := ⟨i.val, (mem_firstIndices _).mp hi⟩
    have hcast₁ : Fin.castLE hr a.castSucc = i := by apply Fin.ext; rfl
    have hcast₂ : Fin.castLE hr₀ a = i := by apply Fin.ext; rfl
    simpa only [Fin.snoc_castSucc, prior, hcast₁, hcast₂] using (hc a.castSucc).symm
  let j : Fin d := ⟨r, by omega⟩
  have hlast : c j = v := by
    have hcast : Fin.castLE hr (Fin.last r) = j := by apply Fin.ext; rfl
    simpa only [Fin.snoc_last, hcast] using hc (Fin.last r)
  have hline : (q : ExteriorAlgebra k W) ∈
      k ∙ (initialWedge c (r + 1) hr : ExteriorAlgebra k W) := by
    rw [hv, initialWedge_eq_of_eq_on b c r hr₀ hprefix, ← hlast]
    exact iota_mul_initialWedge_mem_span c hr
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hline
  exact ⟨c, hprefix, Submodule.mem_span_singleton.mpr ⟨a, Subtype.ext ha⟩⟩

theorem exists_basis_extension_of_incidence [FiniteDimensional k W] {d r : ℕ}
    (b : Module.Basis (Fin d) k W) (hr : r + 1 ≤ d) (q : ⋀[k]^(r + 1) W)
    (hq : q ≠ 0)
    (hinc : CFSG.LinearAlgebra.ExteriorIncidence.incidence b
      ((initialWedge b r (by omega) : ExteriorAlgebra k W) ⊗ₜ[k]
        (q : ExteriorAlgebra k W)) = 0) :
    ∃ c : Module.Basis (Fin d) k W,
      (∀ i ∈ firstIndices d r, b i = c i) ∧ q ∈ k ∙ initialWedge c (r + 1) hr := by
  have hcard : (firstIndices d r).card = r := card_firstIndices (by omega)
  let q' : ⋀[k]^((firstIndices d r).card + 1) W :=
    ⟨q, by simpa only [hcard] using q.property⟩
  obtain ⟨v, hv⟩ := CFSG.LinearAlgebra.ExteriorIncidence.exists_eq_ι_mul_basis_of_incidence b
    (firstIndices d r) q' (by simpa only [initialWedge_coe] using hinc)
  exact exists_basis_of_wedge_extension b hr q hq v (by
    simpa only [initialWedge_coe] using hv)

theorem exists_basis_of_mem_flagCone [FiniteDimensional k W] {d : ℕ}
    (b₀ : Module.Basis (Fin d) k W) :
    ∀ (r : ℕ) (hr : r ≤ d) (w : FlagTensor k W r),
      w ∈ flagCone b₀ r → w ≠ 0 →
        ∃ b : Module.Basis (Fin d) k W, w ∈ k ∙ basisFlagTensor b r hr := by
  intro r
  induction r with
  | zero =>
    intro hr w hw hw0
    refine ⟨b₀, Submodule.mem_span_singleton.mpr ⟨w, ?_⟩⟩
    change w • (1 : k) = w
    simp
  | succ r ih =>
    intro hr w hw hw0
    have hfac : w ∈ tensorCone k (⋀[k]^(r + 1) W) (flagCone b₀ r) := by
      cases r with
      | zero => exact hw
      | succ r => exact hw.1
    obtain ⟨p, hp, q, rfl⟩ := hfac
    have hp0 : p ≠ 0 := by
      intro h
      exact hw0 (by simp [h])
    have hq0 : q ≠ 0 := by
      intro h
      exact hw0 (by simp [h])
    obtain ⟨b, hb⟩ := ih (by omega) p hp hp0
    have hinc : CFSG.LinearAlgebra.ExteriorIncidence.incidence b
        ((initialWedge b r (by omega) : ExteriorAlgebra k W) ⊗ₜ[k]
          (q : ExteriorAlgebra k W)) = 0 := by
      cases r with
      | zero =>
        rw [initialWedge_coe]
        apply (CFSG.LinearAlgebra.ExteriorIncidence.incidence_basis_tmul_eq_zero_iff b _ _).mpr
        intro i hi
        have : i.val < 0 := (mem_firstIndices i).mp hi
        omega
      | succ r =>
        have hk := LinearMap.mem_ker.mp hw.2
        rw [lastIncidence_eq b₀ b] at hk
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hb
        have ha0 : a ≠ 0 := by
          rintro rfl
          exact hp0 (by simpa only [zero_smul] using ha.symm)
        rw [← ha, ← TensorProduct.smul_tmul', map_smul] at hk
        have hk' := (smul_eq_zero.mp hk).resolve_left ha0
        rw [basisFlagTensor, lastIncidence_tmul_tmul] at hk'
        have hzero := right_mem_span_of_tmul_mem_span (x₀ := 0) (y₀ := 0)
          (basisFlagTensor_ne_zero b r (by omega)) (by
            rw [hk']
            exact Submodule.zero_mem _)
        simpa only [Submodule.span_zero_singleton, Submodule.mem_bot] using hzero
    obtain ⟨c, hc, hq⟩ := exists_basis_extension_of_incidence b hr q hq0 hinc
    have hp' : p ∈ k ∙ basisFlagTensor c r (by omega) := by
      rw [← basisFlagTensor_eq_of_eq_on b c r (by omega) hc]
      exact hb
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hp'
    obtain ⟨a', ha'⟩ := Submodule.mem_span_singleton.mp hq
    refine ⟨c, Submodule.mem_span_singleton.mpr ⟨a * a', ?_⟩⟩
    change (a * a') • (basisFlagTensor c r _ ⊗ₜ[k] initialWedge c (r + 1) hr) = p ⊗ₜ[k] q
    rw [← ha, ← ha']
    exact (TensorProduct.smul_tmul_smul _ _ _ _).symm

end TensorGeometry

section LinearStabilizers

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

theorem initialWedge_map {d : ℕ} (b : Module.Basis (Fin d) k V) (f : V ≃ₗ[k] V)
    (r : ℕ) (hr : r ≤ d) :
    exteriorPower.map r f.toLinearMap (initialWedge b r hr) =
      initialWedge (b.map f) r hr := by
  apply Subtype.ext
  simp only [exteriorPower.coe_map, initialWedge_coe, Module.Basis.map_exteriorAlgebra]

theorem flagMap_basisFlagTensor {d : ℕ} (b : Module.Basis (Fin d) k V) (f : V ≃ₗ[k] V) :
    ∀ (r : ℕ) (hr : r ≤ d),
      flagMap f.toLinearMap r (basisFlagTensor b r hr) = basisFlagTensor (b.map f) r hr := by
  intro r
  induction r with
  | zero => intro hr; rfl
  | succ r ih =>
    intro hr
    rw [basisFlagTensor, flagMap_tmul, ih, initialWedge_map, basisFlagTensor]

theorem map_initialSpan_eq_of_initialWedge_line {d r : ℕ}
    (b : Module.Basis (Fin d) k V) (f : V ≃ₗ[k] V) (hr : r ≤ d)
    (h : exteriorPower.map r f.toLinearMap (initialWedge b r hr) ∈ k ∙ initialWedge b r hr) :
    (Submodule.span k (b '' (firstIndices d r : Set (Fin d)))).map f.toLinearMap =
      Submodule.span k (b '' (firstIndices d r : Set (Fin d))) := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul, initialWedge_map] at ha
    exact initialWedge_ne_zero (b.map f) r hr ha.symm
  have hcoe : a • b.ExteriorAlgebra (firstIndices d r) =
      ExteriorAlgebra.map f.toLinearMap (b.ExteriorAlgebra (firstIndices d r)) := by
    simpa only [Submodule.coe_smul, exteriorPower.coe_map, initialWedge_coe] using
      congrArg (fun p : ⋀[k]^r V => (p : ExteriorAlgebra k V)) ha
  have hline : (k ∙ b.ExteriorAlgebra (firstIndices d r)).map
      (ExteriorAlgebra.map f.toLinearMap).toLinearMap =
        k ∙ b.ExteriorAlgebra (firstIndices d r) := by
    rw [Submodule.map_span, Set.image_singleton, AlgHom.toLinearMap_apply, ← hcoe,
      Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha0)]
  exact (b.map_span_exteriorAlgebra_eq_iff (firstIndices d r) f).mp hline

theorem map_initialSpans_eq_of_flagLine {d : ℕ}
    (b : Module.Basis (Fin d) k V) (f : V ≃ₗ[k] V) :
    ∀ (r : ℕ) (hr : r ≤ d),
      flagMap f.toLinearMap r (basisFlagTensor b r hr) ∈ k ∙ basisFlagTensor b r hr →
      ∀ s ≤ r,
        (Submodule.span k (b '' (firstIndices d s : Set (Fin d)))).map f.toLinearMap =
          Submodule.span k (b '' (firstIndices d s : Set (Fin d))) := by
  intro r
  induction r with
  | zero =>
    intro hr h s hs
    have : s = 0 := by omega
    subst s
    have he : firstIndices d 0 = ∅ := by ext i; simp
    simp [he]
  | succ r ih =>
    intro hr h s hs
    simp only [basisFlagTensor] at h
    have hp0 : exteriorPower.map (r + 1) f.toLinearMap (initialWedge b (r + 1) hr) ≠ 0 := by
      rw [initialWedge_map]
      exact initialWedge_ne_zero (b.map f) (r + 1) hr
    have ht0 : flagMap f.toLinearMap r (basisFlagTensor b r (by omega)) ≠ 0 := by
      rw [flagMap_basisFlagTensor]
      exact basisFlagTensor_ne_zero (b.map f) r (by omega)
    have ht := left_mem_span_of_tmul_mem_span hp0 h
    have hp := right_mem_span_of_tmul_mem_span ht0 h
    by_cases hsr : s ≤ r
    · exact ih (by omega) ht s hsr
    · have heq : s = r + 1 := by omega
      subst s
      exact map_initialSpan_eq_of_initialWedge_line b f hr hp

theorem toMatrix_isUpperTriangular_of_flagLine {d : ℕ}
    (b : Module.Basis (Fin d) k V) (f : V ≃ₗ[k] V)
    (h : flagMap f.toLinearMap d (basisFlagTensor b d le_rfl) ∈
      k ∙ basisFlagTensor b d le_rfl) :
    (LinearMap.toMatrix b b f.toLinearMap).IsUpperTriangular := by
  intro i j hji
  rw [LinearMap.toMatrix_apply]
  have hspan := map_initialSpans_eq_of_flagLine b f d le_rfl h (j.val + 1) (by omega)
  have hj : b j ∈ Submodule.span k (b '' (firstIndices d (j.val + 1) : Set (Fin d))) :=
    Submodule.subset_span ⟨j, (mem_firstIndices _).mpr (Nat.lt_succ_self _), rfl⟩
  have hfj : f (b j) ∈ Submodule.span k (b '' (firstIndices d (j.val + 1) : Set (Fin d))) := by
    rw [← hspan]
    exact Submodule.mem_map_of_mem hj
  by_contra hne
  have his : i ∈ (b.repr (f (b j))).support := Finsupp.mem_support_iff.mpr hne
  have himem := (b.mem_span_image).mp hfj his
  have hival : i.val < j.val + 1 := (mem_firstIndices i).mp himem
  have hjival : j.val < i.val := hji
  omega

theorem isSolvable_of_faithful_flagLine [FiniteDimensional k V]
    {G : Type v} [Group G] {d : ℕ} (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hρ : Function.Injective ρ) (b₀ : Module.Basis (Fin d) k V) (w : FlagTensor k V d)
    (hw : w ∈ flagCone b₀ d) (hw0 : w ≠ 0) (P : Subgroup G)
    (hP : ∀ g ∈ P, flagMap (ρ g : Module.End k V) d w ∈ k ∙ w) :
    Group.IsSolvable P := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_of_mem_flagCone b₀ d le_rfl w hw hw0
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw0 (by simpa only [zero_smul] using ha.symm)
  have hspan : k ∙ w = k ∙ basisFlagTensor b d le_rfl := by
    rw [← ha, Submodule.span_singleton_smul_eq (IsUnit.mk0 a ha0)]
  let Φ : LinearMap.GeneralLinearGroup k V ≃* GL (Fin d) k :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let μ : G →* GL (Fin d) k := Φ.toMonoidHom.comp ρ
  have htri : ∀ g : P, μ (g : G) ∈ TauCeti.upperTriangularGroup (Fin d) k := by
    intro g
    let f : V ≃ₗ[k] V := LinearMap.GeneralLinearGroup.generalLinearEquiv k V (ρ (g : G))
    have hf : f.toLinearMap = (ρ (g : G) : Module.End k V) :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap _
    have hgw := hP (g : G) g.property
    rw [hspan, ← ha, map_smul] at hgw
    have hgf : flagMap f.toLinearMap d (basisFlagTensor b d le_rfl) ∈
        k ∙ basisFlagTensor b d le_rfl := by
      rw [hf]
      have hi := (k ∙ basisFlagTensor b d le_rfl).smul_mem a⁻¹ hgw
      simpa only [smul_smul, inv_mul_cancel₀ ha0, one_smul] using hi
    have hmat := toMatrix_isUpperTriangular_of_flagLine b f hgf
    rw [hf] at hmat
    rw [TauCeti.UpperTriangularGroup.mem_iff]
    intro i j hji
    have hji' : j.val < i.val := by
      change j.val < i.val at hji
      exact hji
    simpa [μ, Φ, LinearMap.toMatrix_apply, LinearMap.toMatrixAlgEquiv_apply] using hmat hji'
  let ψ : P →* TauCeti.upperTriangularGroup (Fin d) k :=
    (μ.comp P.subtype).codRestrict _ htri
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply Subtype.ext
    apply hρ
    apply Φ.injective
    exact congrArg (fun z : TauCeti.upperTriangularGroup (Fin d) k => (z : GL (Fin d) k)) hgh
  exact Group.isSolvable_of_isSolvable_injective (f := ψ) hψ

end LinearStabilizers

section FaithfulComodule

variable {k : Type u} [Field k]

theorem exists_finite_faithful_pointComodule
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : TauCeti.Comodule k H V)
      (_ : Module.Finite k V),
      Function.Injective (basePointsRepresentation (R := k) (H := H) V) := by
  obtain ⟨E, hEfin, hEtop⟩ :=
    TauCeti.Comodule.exists_finite_subcomodule_matrixCoefficientSubalgebra_eq_top
      (k := k) (C := H)
  let : Module.Finite k E := hEfin
  let : AddCommGroup E := Module.addCommMonoidToAddCommGroup k
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro g g' h
  exact RegularCocharacter.eq_of_basePointsRepresentation_eq H E hEtop h

theorem exists_faithful_closed_flagOrbit [IsAlgClosed k]
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module k V) (_ : TauCeti.Comodule k H V)
      (_ : Module.Finite k V), Function.Injective (basePointsRepresentation (R := k) (H := H) V) ∧
      ∃ w ∈ flagCone (Module.finBasis k V) (Module.finrank k V), w ≠ 0 ∧
        IsZariskiClosed k (orbitCone k H w) := by
  obtain ⟨V, hAdd, hMod, hCoact, hFinite, hFaithful⟩ :=
    exists_finite_faithful_pointComodule (k := k) H
  let _ : AddCommGroup V := hAdd
  let _ : Module k V := hMod
  let _ : TauCeti.Comodule k H V := hCoact
  let _ : Module.Finite k V := hFinite
  exact ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, hFaithful,
    exists_isZariskiClosed_orbitCone_flag (k := k) (H := H) (V := V)⟩

end FaithfulComodule

section Points

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

theorem isSolvable_lineStabilizer_flag {H : Type u} [CommRing H] [HopfAlgebra k H]
    [TauCeti.Comodule k H V] [FiniteDimensional k V]
    (hFaithful : Function.Injective (basePointsRepresentation (R := k) (H := H) V))
    (w : FlagTensor k V (Module.finrank k V))
    (hw : w ∈ flagCone (Module.finBasis k V) (Module.finrank k V)) (hw0 : w ≠ 0) :
    Group.IsSolvable (TorusConjugacy.lineStabilizer k H w) := by
  let ρ : WithConv (H →ₐ[k] k) →* LinearMap.GeneralLinearGroup k V :=
    Representation.asGroupHom (basePointsRepresentation (R := k) (H := H) V)
  have hρ : Function.Injective ρ := by
    intro g g' h
    apply hFaithful
    have hu := congrArg (fun f : LinearMap.GeneralLinearGroup k V => (f : Module.End k V)) h
    simpa only [ρ, Representation.asGroupHom_apply] using hu
  apply isSolvable_of_faithful_flagLine ρ hρ (Module.finBasis k V) w hw hw0
    (TorusConjugacy.lineStabilizer k H w)
  intro g hg
  have h := (TorusConjugacy.mem_lineStabilizer_iff (H := H) hw0 g).mp hg
  simpa only [ρ, Representation.asGroupHom_apply, basePointsRepresentation_flag] using h

theorem exists_closedOrbitLine_solvable [IsAlgClosed k]
    (H : TauCeti.FiniteTypeCommHopfAlgCat.{u,u} k) [IsDomain H] :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : TauCeti.Comodule k H W)
      (_ : Module.Finite k W) (w : W), w ≠ 0 ∧ IsZariskiClosed k (orbitCone k H w) ∧
      ∃ P : Subgroup (WithConv (H →ₐ[k] k)),
        (∀ g, g ∈ P ↔ basePointsRepresentation (H := H) W g w ∈ k ∙ w) ∧ Group.IsSolvable P := by
  obtain ⟨V, hAdd, hMod, hCoact, hFinite, hFaithful, w, hw, hw0, hX⟩ :=
    exists_faithful_closed_flagOrbit (k := k) H
  let _ : AddCommGroup V := hAdd
  let _ : Module k V := hMod
  let _ : TauCeti.Comodule k H V := hCoact
  let _ : Module.Finite k V := hFinite
  refine ⟨FlagTensor k V (Module.finrank k V), inferInstance, inferInstance, inferInstance,
    inferInstance, w, hw0, hX, TorusConjugacy.lineStabilizer k H w, ?_, ?_⟩
  · exact fun g => TorusConjugacy.mem_lineStabilizer_iff hw0 g
  · exact isSolvable_lineStabilizer_flag (H := H) hFaithful w hw hw0

end Points

end CFSG.LieType.AlgebraicGroups.ClosedCone

