module

public import CFSG.HardMathSupport.GuralnickMalle.SL6Exterior3F.Compare

public section

namespace CFSG.HardMathSupport.GuralnickMalle

open Module

variable {K : Type} [Field K]

@[expose] noncomputable def transvectionLinearEquiv (e : Fin 6 → K)
    (φ : (Fin 6 → K) →ₗ[K] K) (h : φ e = 0) :
    (Fin 6 → K) ≃ₗ[K] (Fin 6 → K) where
  toFun v := v + φ v • e
  invFun v := v - φ v • e
  left_inv v := by
    show (v + φ v • e) - φ (v + φ v • e) • e = v
    rw [map_add, map_smul, h, smul_eq_mul, mul_zero, add_zero]
    abel
  right_inv v := by
    show (v - φ v • e) + φ (v - φ v • e) • e = v
    rw [map_sub, map_smul, h, smul_eq_mul, mul_zero, sub_zero]
    abel
  map_add' v w := by
    show (v + w) + φ (v + w) • e = (v + φ v • e) + (w + φ w • e)
    rw [map_add, add_smul]
    abel
  map_smul' c v := by
    show c • v + φ (c • v) • e = c • (v + φ v • e)
    rw [map_smul, smul_add, smul_eq_mul, smul_smul]

@[expose] noncomputable def transvectionGL (e : Fin 6 → K)
    (φ : (Fin 6 → K) →ₗ[K] K) (h : φ e = 0) : GL (Fin 6) K :=
  (Matrix.GeneralLinearGroup.toLin (n := Fin 6) (R := K)).symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv (transvectionLinearEquiv e φ h))

@[simp] theorem toLin_transvectionGL (e : Fin 6 → K) (φ : (Fin 6 → K) →ₗ[K] K)
    (h : φ e = 0) (v : Fin 6 → K) :
    Matrix.toLin' ((transvectionGL e φ h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) v =
      v + φ v • e := by
  have h1 : Matrix.GeneralLinearGroup.toLin (transvectionGL e φ h) =
      LinearMap.GeneralLinearGroup.ofLinearEquiv (transvectionLinearEquiv e φ h) :=
    MulEquiv.apply_symm_apply _ _
  have h2 : ((Matrix.GeneralLinearGroup.toLin (transvectionGL e φ h) :
      LinearMap.GeneralLinearGroup K (Fin 6 → K)) : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) =
      Matrix.toLin' ((transvectionGL e φ h : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) :=
    (glNaturalRep_eq_toLin _).symm
  rw [← h2, h1, LinearMap.GeneralLinearGroup.coe_ofLinearEquiv]
  change (transvectionLinearEquiv e φ h).toFun v = v + φ v • e
  rfl

theorem ker_sub_one_le_span_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type*} [AddCommGroup W] [Module K W] {B : Basis ι K W}
    {M : Finset ι} {rep : ι → ι} (hrep_inj : Set.InjOn rep (↑M : Set ι))
    {S : W →ₗ[K] W} (hS : ∀ i, S (B i) = if i ∈ M then B i + B (rep i) else B i) :
    LinearMap.ker (S - 1) ≤ Submodule.span K (B '' (↑M : Set ι)ᶜ) := by
  classical
  intro w hw
  rw [LinearMap.mem_ker] at hw
  have hstep : ∀ i, (S - 1) (B i) = if i ∈ M then B (rep i) else 0 := by
    intro i
    rw [LinearMap.sub_apply, Module.End.one_apply, hS i]
    by_cases hi : i ∈ M
    · rw [if_pos hi, if_pos hi]; abel
    · rw [if_neg hi, if_neg hi, sub_self]
  have hcalc : (S - 1) w = ∑ i : ↥M, B.repr w i.1 • B (rep i) := by
    conv_lhs => rw [(B.sum_repr w).symm]
    rw [map_sum]
    rw [show (∑ i, (S - 1) (B.repr w i • B i)) =
        ∑ i, B.repr w i • (if i ∈ M then B (rep i) else 0) from
      Finset.sum_congr rfl (fun i _ => by rw [map_smul, hstep i])]
    rw [← Finset.sum_subset (s₁ := M) (fun x _ => Finset.mem_univ x)
      (fun x _ hx => by simp [hx])]
    rw [Finset.sum_congr rfl (fun i hi => by rw [if_pos hi])]
    exact (Finset.sum_coe_sort M (fun i => B.repr w i • B (rep i))).symm
  have hzero : ∑ i : ↥M, B.repr w i.1 • B (rep i) = 0 := by
    rw [← hcalc]
    exact hw
  have hindep : LinearIndependent K (fun i : ↥M => B (rep i.1)) :=
    B.linearIndependent.comp (fun i : ↥M => rep i.1)
      (fun i j hij => Subtype.ext (hrep_inj i.2 j.2 hij))
  have hall : ∀ i : ↥M, B.repr w i.1 = 0 :=
    Fintype.linearIndependent_iff.mp hindep (fun i : ↥M => B.repr w i.1) hzero
  rw [mem_span_basis_image_iff]
  intro i hi
  exact hall ⟨i, by simpa using hi⟩

theorem replace_inj {n k : ℕ} {a b : Fin n} {I J : Set.powersetCard (Fin n) k}
    (hbI : b ∈ I.val) (haI : a ∉ I.val) (hbJ : b ∈ J.val) (haJ : a ∉ J.val)
    (h : CFSG.LieType.Chevalley.ExteriorCube.replace I hbI haI =
      CFSG.LieType.Chevalley.ExteriorCube.replace J hbJ haJ) : I = J := by
  have hval : insert a (I.val.erase b) = insert a (J.val.erase b) := congrArg Subtype.val h
  have hIa : a ∉ I.val.erase b := fun hh => haI (Finset.mem_of_mem_erase hh)
  have hJa : a ∉ J.val.erase b := fun hh => haJ (Finset.mem_of_mem_erase hh)
  have h1 : I.val.erase b = J.val.erase b := by
    have := congrArg (fun s => s.erase a) hval
    rwa [Finset.erase_insert hIa, Finset.erase_insert hJa] at this
  have h2 : insert b (I.val.erase b) = insert b (J.val.erase b) := by rw [h1]
  rw [Finset.insert_erase hbI, Finset.insert_erase hbJ] at h2
  exact Subtype.ext h2

theorem replace_injOn {n k : ℕ} {a b : Fin n} (M : Finset (Set.powersetCard (Fin n) k))
    (hM : ∀ I ∈ M, b ∈ I.val ∧ a ∉ I.val) :
    Set.InjOn (fun I : Set.powersetCard (Fin n) k =>
      if h : b ∈ I.val ∧ a ∉ I.val then
        CFSG.LieType.Chevalley.ExteriorCube.replace I h.1 h.2 else I) (↑M : Set _) := by
  intro I hI J hJ hIJ
  have hI' := hM I (Finset.mem_coe.mp hI)
  have hJ' := hM J (Finset.mem_coe.mp hJ)
  have h1 : (if h : b ∈ I.val ∧ a ∉ I.val then
      CFSG.LieType.Chevalley.ExteriorCube.replace I h.1 h.2 else I) =
      CFSG.LieType.Chevalley.ExteriorCube.replace I hI'.1 hI'.2 := dif_pos hI'
  have h2 : (if h : b ∈ J.val ∧ a ∉ J.val then
      CFSG.LieType.Chevalley.ExteriorCube.replace J h.1 h.2 else J) =
      CFSG.LieType.Chevalley.ExteriorCube.replace J hJ'.1 hJ'.2 := dif_pos hJ'
  beta_reduce at hIJ
  rw [h1, h2] at hIJ
  exact replace_inj hI'.1 hI'.2 hJ'.1 hJ'.2 hIJ

theorem linearIndependent_adapted {W : Submodule K (Fin 6 → K)}
    {φ ψ : (Fin 6 → K) →ₗ[K] K}
    (hW : ∀ w, w ∈ W ↔ φ w = 0 ∧ ψ w = 0)
    {L D : Submodule K W} (hLD : IsCompl L D) {e : W} (he : e ≠ 0)
    (hL : L = Submodule.span K {e}) (c : Basis (Fin 3) K D)
    (u v : Fin 6 → K) (huφ : φ u = 1) (huψ : ψ u = 0) (hvφ : φ v = 0) (hvψ : ψ v = 1) :
    LinearIndependent K
      (![(e : Fin 6 → K), ((c 0 : D) : Fin 6 → K), ((c 1 : D) : Fin 6 → K),
        ((c 2 : D) : Fin 6 → K), u, v] : Fin 6 → (Fin 6 → K)) := by
  classical
  have hφW : ∀ w ∈ W, φ w = 0 := fun w hw => (hW w).mp hw |>.1
  have hψW : ∀ w ∈ W, ψ w = 0 := fun w hw => (hW w).mp hw |>.2
  have hcφ : ∀ j : Fin 3, φ (((c j : D) : W) : Fin 6 → K) = 0 :=
    fun j => hφW _ ((c j : D) : W).2
  have hcψ : ∀ j : Fin 3, ψ (((c j : D) : W) : Fin 6 → K) = 0 :=
    fun j => hψW _ ((c j : D) : W).2
  set F : Fin 6 → (Fin 6 → K) :=
    ![(e : Fin 6 → K), ((c 0 : D) : Fin 6 → K), ((c 1 : D) : Fin 6 → K),
      ((c 2 : D) : Fin 6 → K), u, v] with hF
  have hF0 : F 0 = (e : Fin 6 → K) := by simp [hF]
  have hF1 : F 1 = ((c 0 : D) : Fin 6 → K) := by simp [hF]
  have hF2 : F 2 = ((c 1 : D) : Fin 6 → K) := by simp [hF]
  have hF3 : F 3 = ((c 2 : D) : Fin 6 → K) := by simp [hF]
  have hF4 : F 4 = u := by simp [hF]
  have hF5 : F 5 = v := by simp [hF]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hφF : ∀ i, φ (F i) = if i = 4 then 1 else 0 := by
    intro i
    fin_cases i
    · simp [hF, hφW e e.2]
    · simp [hF, hcφ 0]
    · simp [hF, hcφ 1]
    · simp [hF, hcφ 2]
    · simp [hF, huφ]
    · simp [hF, hvφ]
  have hψF : ∀ i, ψ (F i) = if i = 5 then 1 else 0 := by
    intro i
    fin_cases i
    · simp [hF, hψW e e.2]
    · simp [hF, hcψ 0]
    · simp [hF, hcψ 1]
    · simp [hF, hcψ 2]
    · simp [hF, huψ]
    · simp [hF, hvψ]
  have hsumφ : ∑ i, g i * φ (F i) = 0 := by
    have h := congrArg φ hg
    simpa using h
  have hsumψ : ∑ i, g i * ψ (F i) = 0 := by
    have h := congrArg ψ hg
    simpa using h
  have h4 : g 4 = 0 := by
    have h1 : ∑ i, g i * φ (F i) = g 4 * φ (F 4) := by
      refine Finset.sum_eq_single 4 (fun b _ hb => by rw [hφF b, if_neg hb, mul_zero]) ?_
      intro h
      exact absurd (Finset.mem_univ 4) h
    rw [hsumφ, hφF 4, if_pos rfl, mul_one] at h1
    exact h1.symm
  have h5 : g 5 = 0 := by
    have h1 : ∑ i, g i * ψ (F i) = g 5 * ψ (F 5) := by
      refine Finset.sum_eq_single 5 (fun b _ hb => by rw [hψF b, if_neg hb, mul_zero]) ?_
      intro h
      exact absurd (Finset.mem_univ 5) h
    rw [hsumψ, hψF 5, if_pos rfl, mul_one] at h1
    exact h1.symm
  have hz : (g 0 • e + (g 1 • c 0 + g 2 • c 1 + g 3 • c 2) : W) = 0 := by
    have h' := hg
    rw [Fin.sum_univ_six, h4, h5, zero_smul, zero_smul, add_zero, add_zero] at h'
    rw [hF0, hF1, hF2, hF3] at h'
    apply Subtype.ext
    simpa [add_assoc] using h'
  have hmem : g 0 • e ∈ L ⊓ D := by
    refine ⟨?_, ?_⟩
    · rw [hL]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · have hneg : g 0 • e = -(g 1 • c 0 + g 2 • c 1 + g 3 • c 2) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hz
      rw [hneg]
      exact Submodule.neg_mem _ (Submodule.add_mem _
        (Submodule.add_mem _ (Submodule.smul_mem _ _ (c 0).2) (Submodule.smul_mem _ _ (c 1).2))
        (Submodule.smul_mem _ _ (c 2).2))
  have hg0 : g 0 = 0 := by
    have h0 : g 0 • e = 0 := by
      have hdisj := hLD.disjoint
      rw [Submodule.disjoint_def] at hdisj
      exact hdisj _ hmem.1 hmem.2
    by_contra hne
    have hzero : e = 0 := by
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h hne
      · exact h
    exact he hzero
  have hD0 : (∑ j : Fin 3, (![g 1, g 2, g 3] : Fin 3 → K) j • c j : D) = 0 := by
    have hz' := hz
    rw [hg0, zero_smul, zero_add] at hz'
    apply Subtype.ext
    rw [Fin.sum_univ_three]
    simpa using hz'
  have h123 : ∀ j : Fin 3, (![g 1, g 2, g 3] : Fin 3 → K) j = 0 := by
    intro j
    have h1 := congrArg (fun x : D => c.repr x j) hD0
    rw [map_sum, map_zero, Fin.sum_univ_three] at h1
    simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
      Finsupp.coe_add, Pi.add_apply] at h1
    fin_cases j <;> simpa using h1
  intro i
  fin_cases i
  · exact hg0
  · have := h123 0; simpa using this
  · have := h123 1; simpa using this
  · have := h123 2; simpa using this
  · exact h4
  · exact h5

theorem exists_adapted_vectors [CharP K 2] (e : Fin 6 → K) (he : e ≠ 0)
    {φ ψ : (Fin 6 → K) →ₗ[K] K} (hφe : φ e = 0) (hψe : ψ e = 0)
    (hind : ∀ c d : K, c • φ + d • ψ = 0 → c = 0 ∧ d = 0) :
    ∃ (c : Fin 3 → (Fin 6 → K)) (u v : Fin 6 → K),
      LinearIndependent K (![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) ∧
      φ u = 1 ∧ ψ u = 0 ∧ φ v = 0 ∧ ψ v = 1 ∧
      (∀ j, φ (c j) = 0 ∧ ψ (c j) = 0) := by
  classical
  have hφ0 : φ ≠ 0 := by
    intro h
    exact one_ne_zero (hind 1 0 (by rw [h]; simp)).1
  have hψ0 : ψ ≠ 0 := by
    intro h
    exact one_ne_zero (hind 0 1 (by rw [h]; simp)).2
  obtain ⟨x, hx⟩ : ∃ x : Fin 6 → K, φ x = 1 := by
    have hne : ∃ y, φ y ≠ 0 := by
      by_contra h
      exact hφ0 (LinearMap.ext fun y => by
        by_contra hy
        exact h ⟨y, hy⟩)
    obtain ⟨y, hy⟩ := hne
    exact ⟨(φ y)⁻¹ • y, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy]⟩
  have hnotle : ¬ (LinearMap.ker φ ≤ LinearMap.ker ψ) := by
    intro hle
    set c₀ : K := ψ x with hc₀
    have hprop : ψ = c₀ • φ := by
      refine LinearMap.ext fun w => ?_
      have hw : w - φ w • x ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker, map_sub, map_smul, hx, smul_eq_mul, mul_one, sub_self]
      have h2 := hle hw
      rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at h2
      rw [h2, hc₀, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
    have h0 : (-c₀) • φ + (1 : K) • ψ = 0 := by
      rw [hprop, one_smul, ← add_smul, neg_add_cancel, zero_smul]
    exact one_ne_zero (hind (-c₀) 1 h0).2
  obtain ⟨z, hzφ, hzψ⟩ : ∃ z : Fin 6 → K, φ z = 0 ∧ ψ z ≠ 0 := by
    by_contra h
    refine hnotle (fun w hw => ?_)
    by_contra hwψ
    exact h ⟨w, hw, hwψ⟩
  obtain ⟨v, hvφ, hvψ⟩ : ∃ v : Fin 6 → K, φ v = 0 ∧ ψ v = 1 :=
    ⟨(ψ z)⁻¹ • z, by rw [map_smul, hzφ, smul_zero],
      by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hzψ]⟩
  obtain ⟨u, huφ, huψ⟩ : ∃ u : Fin 6 → K, φ u = 1 ∧ ψ u = 0 := by
    refine ⟨x - ψ x • v, ?_, ?_⟩
    · rw [map_sub, map_smul, hvφ, smul_zero, sub_zero, hx]
    · rw [map_sub, map_smul, hvψ, smul_eq_mul, mul_one, sub_self]
  set W : Submodule K (Fin 6 → K) := LinearMap.ker φ ⊓ LinearMap.ker ψ with hW
  have memW : ∀ {w : Fin 6 → K}, w ∈ W ↔ φ w = 0 ∧ ψ w = 0 := by
    intro w
    rw [hW, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker]
  have hφW : ∀ w ∈ W, φ w = 0 := fun w hw => (memW.mp hw).1
  have hψW : ∀ w ∈ W, ψ w = 0 := fun w hw => (memW.mp hw).2
  have heW : e ∈ W := memW.mpr ⟨hφe, hψe⟩
  have htop : (φ.prod ψ).range = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨a, b⟩
    refine LinearMap.mem_range.mpr ⟨a • u + b • v, ?_⟩
    rw [LinearMap.prod_apply]
    show (φ (a • u + b • v), ψ (a • u + b • v)) = (a, b)
    have h1 : φ (a • u + b • v) = a := by
      rw [map_add, map_smul, map_smul, huφ, hvφ]
      simp
    have h2 : ψ (a • u + b • v) = b := by
      rw [map_add, map_smul, map_smul, huψ, hvψ]
      simp
    rw [h1, h2]
  have hdim : finrank K W = 4 := by
    have h := LinearMap.finrank_range_add_finrank_ker (φ.prod ψ)
    rw [htop, LinearMap.ker_prod, ← hW, finrank_top] at h
    have h2 : finrank K (K × K) = 2 := by simp
    have h3 : finrank K (Fin 6 → K) = 6 := by simp
    rw [h2, h3] at h
    omega
  set L : Submodule K W := Submodule.span K {(⟨e, heW⟩ : W)} with hL
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl L
  have hL1 : finrank K L = 1 := by
    rw [hL]
    exact finrank_span_singleton (v := (⟨e, heW⟩ : W)) (fun h => he (congrArg Subtype.val h))
  have hD3 : finrank K D = 3 := by
    have h := Submodule.finrank_add_eq_of_isCompl hD
    rw [hL1, hdim] at h
    omega
  obtain ⟨c, hcφ, hcψ⟩ : ∃ c : Basis (Fin 3) K D,
      (∀ j, φ ((c j : D) : W) = 0) ∧ (∀ j, ψ ((c j : D) : W) = 0) := by
    have : Module.Free K D := Module.Free.of_divisionRing K D
    let c₀ : Basis (Fin 3) K D := Module.finBasisOfFinrankEq (R := K) (M := D) (n := 3) hD3
    exact ⟨c₀, fun j => hφW _ (((c₀ j : D) : W)).2,
      fun j => hψW _ (((c₀ j : D) : W)).2⟩
  refine ⟨fun j => ((c j : D) : W), u, v, ?_, huφ, huψ, hvφ, hvψ, fun j => ⟨hcφ j, hcψ j⟩⟩
  exact linearIndependent_adapted (W := W) (fun w => memW) hD (e := ⟨e, heW⟩)
    (fun h0 => he (congrArg Subtype.val h0)) hL c u v huφ huψ hvφ hvψ

theorem exists_adapted_basis [CharP K 2] (e : Fin 6 → K) (he : e ≠ 0)
    {φ ψ : (Fin 6 → K) →ₗ[K] K} (hφe : φ e = 0) (hψe : ψ e = 0)
    (hind : ∀ c d : K, c • φ + d • ψ = 0 → c = 0 ∧ d = 0) :
    ∃ b : Basis (Fin 6) K (Fin 6 → K), b 0 = e ∧ φ (b 4) = 1 ∧ ψ (b 4) = 0 ∧
      φ (b 5) = 0 ∧ ψ (b 5) = 1 ∧ ∀ i, i ≠ 4 → i ≠ 5 → φ (b i) = 0 ∧ ψ (b i) = 0 := by
  classical
  obtain ⟨c, u, v, hli, huφ, huψ, hvφ, hvψ, hc⟩ := exists_adapted_vectors e he hφe hψe hind
  have hcφ : ∀ j : Fin 3, φ (c j) = 0 := fun j => (hc j).1
  have hcψ : ∀ j : Fin 3, ψ (c j) = 0 := fun j => (hc j).2
  have hF0 : (![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) 0 = e := by simp
  have hF4 : (![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) 4 = u := by simp
  have hF5 : (![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) 5 = v := by simp
  have hφF : ∀ i, φ ((![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) i) =
      if i = 4 then 1 else 0 := by
    intro i
    fin_cases i
    · simpa using hφe
    · exact hcφ 0
    · exact hcφ 1
    · exact hcφ 2
    · simpa using huφ
    · simpa using hvφ
  have hψF : ∀ i, ψ ((![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) i) =
      if i = 5 then 1 else 0 := by
    intro i
    fin_cases i
    · simpa using hψe
    · exact hcψ 0
    · exact hcψ 1
    · exact hcψ 2
    · simpa using huψ
    · simpa using hvψ
  have hcard : Fintype.card (Fin 6) = finrank K (Fin 6 → K) := by
    simp
  let b : Basis (Fin 6) K (Fin 6 → K) := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = (![e, c 0, c 1, c 2, u, v] : Fin 6 → (Fin 6 → K)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = e := by rw [hb]; exact hF0
  have hb4φ : φ (b 4) = 1 := by rw [hb]; rw [hφF 4]; exact if_pos rfl
  have hb4ψ : ψ (b 4) = 0 := by
    rw [hb]; rw [hψF 4]; exact if_neg (by decide : (4 : Fin 6) ≠ 5)
  have hb5φ : φ (b 5) = 0 := by
    rw [hb]; rw [hφF 5]; exact if_neg (by decide : (5 : Fin 6) ≠ 4)
  have hb5ψ : ψ (b 5) = 1 := by rw [hb]; rw [hψF 5]; exact if_pos rfl
  have hother : ∀ i, i ≠ 4 → i ≠ 5 → φ (b i) = 0 ∧ ψ (b i) = 0 := by
    intro i hi4 hi5
    rw [hb]
    fin_cases i
    · exact ⟨hφe, hψe⟩
    · exact hc 0
    · exact hc 1
    · exact hc 2
    · exact absurd rfl hi4
    · exact absurd rfl hi5
  exact ⟨b, hb0, hb4φ, hb4ψ, hb5φ, hb5ψ, hother⟩

theorem finrank_fix_le_eleven_of_independent_transvections [CharP K 2]
    (e : Fin 6 → K) (he : e ≠ 0)
    {φ ψ : (Fin 6 → K) →ₗ[K] K} (hφe : φ e = 0) (hψe : ψ e = 0)
    (hind : ∀ c d : K, c • φ + d • ψ = 0 → c = 0 ∧ d = 0)
    (a b : GL (Fin 6) K)
    (ha : Matrix.toLin' ((a : Matrix (Fin 6) (Fin 6) K)) = 1 + φ.smulRight e)
    (hb : Matrix.toLin' ((b : Matrix (Fin 6) (Fin 6) K)) = 1 + ψ.smulRight e) :
    finrank K (fixSubGen (glExterior3Rep K) (Subgroup.closure {a, b})) ≤ 11 := by
  classical
  obtain ⟨bs, hbs0, hφ4, hψ4, hφ5, hψ5, hker⟩ := exists_adapted_basis e he hφe hψe hind
  let allTriples : Finset (Set.powersetCard (Fin 6) 3) :=
    Finset.subtype (fun s : Finset (Fin 6) => s.card = 3) Finset.univ
  have hAll : ∀ I : Set.powersetCard (Fin 6) 3, I ∈ allTriples := fun I => by
    change (⟨I.val, I.2⟩ : Subtype (fun s : Finset (Fin 6) => s.card = 3)) ∈
      Finset.subtype (fun s : Finset (Fin 6) => s.card = 3) Finset.univ
    rw [Finset.mem_subtype]
    simp
  let M₁ : Finset (Set.powersetCard (Fin 6) 3) :=
    allTriples.filter (fun I => (4 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val)
  let M₂ : Finset (Set.powersetCard (Fin 6) 3) :=
    allTriples.filter (fun I => (5 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val)
  have hM₁ : ∀ I ∈ M₁, (4 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val := fun I hI => by
    simp only [M₁, Finset.mem_filter] at hI
    exact hI.2
  have hM₂ : ∀ I ∈ M₂, (5 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val := fun I hI => by
    simp only [M₂, Finset.mem_filter] at hI
    exact hI.2
  let rep₁ : Set.powersetCard (Fin 6) 3 → Set.powersetCard (Fin 6) 3 := fun I =>
    if h : (4 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val then
      CFSG.LieType.Chevalley.ExteriorCube.replace I h.1 h.2 else I
  let rep₂ : Set.powersetCard (Fin 6) 3 → Set.powersetCard (Fin 6) 3 := fun I =>
    if h : (5 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val then
      CFSG.LieType.Chevalley.ExteriorCube.replace I h.1 h.2 else I
  have hinj₁ : Set.InjOn rep₁ (↑M₁ : Set _) := replace_injOn M₁ hM₁
  have hinj₂ : Set.InjOn rep₂ (↑M₂ : Set _) := replace_injOn M₂ hM₂
  have hT₁ : ∀ i, (1 + φ.smulRight e : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) (bs i) =
      bs i + (if i = 4 then (1 : K) • bs 0 else 0) := by
    intro i
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smulRight_apply]
    have hφi : φ (bs i) = if i = 4 then 1 else 0 := by
      by_cases h4 : i = 4
      · subst h4; rw [hφ4]; simp
      · by_cases h5 : i = 5
        · subst h5; rw [hφ5]; simp
        · rw [(hker i h4 h5).1]; simp [h4]
    rw [hφi, ← hbs0]
    by_cases h4 : i = 4 <;> simp [h4]
  have hT₂ : ∀ i, (1 + ψ.smulRight e : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) (bs i) =
      bs i + (if i = 5 then (1 : K) • bs 0 else 0) := by
    intro i
    rw [LinearMap.add_apply, Module.End.one_apply, LinearMap.smulRight_apply]
    have hψi : ψ (bs i) = if i = 5 then 1 else 0 := by
      by_cases h5 : i = 5
      · subst h5; rw [hψ5]; simp
      · by_cases h4 : i = 4
        · subst h4; rw [hψ4]; simp
        · rw [(hker i h4 h5).2]; simp [h5]
    rw [hψi, ← hbs0]
    by_cases h5 : i = 5 <;> simp [h5]
  have hS₁ : ∀ I, (glExterior3Rep K) a (bs.exteriorPower 3 I) =
      if I ∈ M₁ then bs.exteriorPower 3 I + bs.exteriorPower 3 (rep₁ I)
      else bs.exteriorPower 3 I := by
    intro I
    rw [glExterior3Rep_apply, glNaturalRep_eq_toLin, ha]
    rw [exteriorPower_map_basis_transvection (K := K) (n := 6) (k := 3) (b := bs)
      (a := (0 : Fin 6)) (c := (4 : Fin 6)) (by decide) (1 : K) (1 + φ.smulRight e) hT₁ I]
    by_cases hI : (4 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val
    · rw [dif_pos hI, if_pos (by simp only [M₁, Finset.mem_filter]; exact ⟨hAll I, hI⟩),
        one_smul]
      congr 1
      simp only [rep₁, dif_pos hI]
    · rw [dif_neg hI, if_neg (by simp only [M₁, Finset.mem_filter]; exact fun h => hI h.2)]
  have hS₂ : ∀ I, (glExterior3Rep K) b (bs.exteriorPower 3 I) =
      if I ∈ M₂ then bs.exteriorPower 3 I + bs.exteriorPower 3 (rep₂ I)
      else bs.exteriorPower 3 I := by
    intro I
    rw [glExterior3Rep_apply, glNaturalRep_eq_toLin, hb]
    rw [exteriorPower_map_basis_transvection (K := K) (n := 6) (k := 3) (b := bs)
      (a := (0 : Fin 6)) (c := (5 : Fin 6)) (by decide) (1 : K) (1 + ψ.smulRight e) hT₂ I]
    by_cases hI : (5 : Fin 6) ∈ I.val ∧ (0 : Fin 6) ∉ I.val
    · rw [dif_pos hI, if_pos (by simp only [M₂, Finset.mem_filter]; exact ⟨hAll I, hI⟩),
        one_smul]
      congr 1
      simp only [rep₂, dif_pos hI]
    · rw [dif_neg hI, if_neg (by simp only [M₂, Finset.mem_filter]; exact fun h => hI h.2)]
  have hle₁ : LinearMap.ker ((glExterior3Rep K) a - 1) ≤
      Submodule.span K ((bs.exteriorPower 3) '' (↑M₁ : Set _)ᶜ) :=
    ker_sub_one_le_span_compl (B := bs.exteriorPower 3) hinj₁ hS₁
  have hle₂ : LinearMap.ker ((glExterior3Rep K) b - 1) ≤
      Submodule.span K ((bs.exteriorPower 3) '' (↑M₂ : Set _)ᶜ) :=
    ker_sub_one_le_span_compl (B := bs.exteriorPower 3) hinj₂ hS₂
  have hgen : fixSubGen (glExterior3Rep K) (Subgroup.closure {a, b}) =
      fixSubGen (glExterior3Rep K) (Subgroup.closure {a}) ⊓
        fixSubGen (glExterior3Rep K) (Subgroup.closure {b}) := by
    rw [← fixSubGen_sup]
    congr 1
    rw [show ({a, b} : Set (GL (Fin 6) K)) = {a} ∪ {b} from by ext x; simp [or_comm],
      Subgroup.closure_union]
  have hset : ((↑M₁ : Set (Set.powersetCard (Fin 6) 3))ᶜ ∩ (↑M₂ : Set _)ᶜ) =
      (↑(allTriples \ (M₁ ∪ M₂)) : Set (Set.powersetCard (Fin 6) 3)) := by
    ext I
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff,
      Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hAll I, ?_⟩
      rintro (h | h)
      · exact h1 h
      · exact h2 h
    · rintro ⟨-, h3⟩
      exact ⟨fun h1 => h3 (Or.inl h1), fun h2 => h3 (Or.inr h2)⟩
  have hle : LinearMap.ker ((glExterior3Rep K) a - 1) ⊓ LinearMap.ker ((glExterior3Rep K) b - 1) ≤
      Submodule.span K ((bs.exteriorPower 3) '' (↑(allTriples \ (M₁ ∪ M₂)) : Set _)) := by
    refine (le_inf (inf_le_left.trans hle₁) (inf_le_right.trans hle₂)).trans ?_
    rw [inf_span_basis_image, hset]
  rw [hgen, fixSubGen_closure_singleton, fixSubGen_closure_singleton]
  refine (Submodule.finrank_mono hle).trans ?_
  refine (finrank_span_basis_finset_le (bs.exteriorPower 3) (allTriples \ (M₁ ∪ M₂))).trans ?_
  have hcard : (allTriples \ (M₁ ∪ M₂)).card = 11 := by decide
  rw [hcard]

end CFSG.HardMathSupport.GuralnickMalle
