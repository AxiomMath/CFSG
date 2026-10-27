module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.GroupTheory.WeirSylow.Symplectic

public section

namespace CFSG.GroupTheory.WeirSylow

open Module Finset QuadraticMap

variable {K : Type} [Field K]

section Spaces

@[expose] def IsQuadSpace (S : FormSpace K K) : Prop :=
  ∃ Q : QuadraticForm K S.V, (∀ x y, S.F x y = Q x) ∧ (polarBilin Q).Nondegenerate

@[expose] def IsPlusQuadSpace (S : FormSpace K K) : Prop :=
  ∃ Q : QuadraticForm K S.V, (∀ x y, S.F x y = Q x) ∧ (polarBilin Q).Nondegenerate ∧ IsPlusType Q

theorem polar_pi {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] (Q : ∀ i, QuadraticForm K (V i)) (x y : ∀ i, V i) :
    polar (QuadraticMap.pi Q) x y = ∑ i, polar (Q i) (x i) (y i) := by
  simp [polar, QuadraticMap.pi_apply, Finset.sum_sub_distrib]

theorem nondegenerate_polarBilin_pi {ι : Type} [Fintype ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] {Q : ∀ i, QuadraticForm K (V i)}
    (hQ : ∀ i, (polarBilin (Q i)).Nondegenerate) :
    (polarBilin (QuadraticMap.pi Q)).Nondegenerate := by
  classical
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  funext i
  refine (hQ i).1 (x i) fun z => ?_
  have := hx (Pi.single i z)
  rwa [polar_pi, Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj,
    polar_zero_right]) (by simp), Pi.single_eq_same] at this

theorem isPlusType_pi {ι : Type} [Fintype ι] {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)] {Q : ∀ i, QuadraticForm K (V i)}
    (hQ : ∀ i, IsPlusType (Q i)) : IsPlusType (QuadraticMap.pi Q) := by
  choose W hW hWs using hQ
  let j : (∀ i, W i) →ₗ[K] (∀ i, V i) := LinearMap.pi fun i => (W i).subtype.comp (LinearMap.proj i)
  have hj : Function.Injective j := fun x y hxy => funext fun i =>
    Subtype.ext (congrFun hxy i)
  refine ⟨LinearMap.range j, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hj, Module.finrank_pi_fintype, Module.finrank_pi_fintype,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hW i
  · rintro _ ⟨x, rfl⟩
    rw [QuadraticMap.pi_apply]
    exact Finset.sum_eq_zero fun i _ => hWs i _ (x i).2

theorem isQuadSpace_pi {ι : Type} [Fintype ι] (S : ι → FormSpace K K)
    (hS : ∀ i, IsQuadSpace (S i)) : IsQuadSpace (FormSpace.pi S) := by
  choose Q hQF hQ using hS
  refine ⟨QuadraticMap.pi Q, fun x y => ?_, nondegenerate_polarBilin_pi hQ⟩
  change ∑ i, (S i).F (x i) (y i) = _
  rw [QuadraticMap.pi_apply]
  exact Finset.sum_congr rfl fun i _ => hQF i _ _

theorem isPlusQuadSpace_pi {ι : Type} [Fintype ι] (S : ι → FormSpace K K)
    (hS : ∀ i, IsPlusQuadSpace (S i)) : IsPlusQuadSpace (FormSpace.pi S) := by
  choose Q hQF hQ hQp using hS
  refine ⟨QuadraticMap.pi Q, fun x y => ?_, nondegenerate_polarBilin_pi hQ, isPlusType_pi hQp⟩
  change ∑ i, (S i).F (x i) (y i) = _
  rw [QuadraticMap.pi_apply]
  exact Finset.sum_congr rfl fun i _ => hQF i _ _

@[expose] noncomputable def isomEquivOrthogonal (S : FormSpace K K) {Q : QuadraticForm K S.V}
    (hQ : ∀ x y, S.F x y = Q x) : S.isom ≃* TauCeti.QuadraticMap.orthogonalGroup Q :=
  MulEquiv.subgroupCongr (by
    ext g
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    change (∀ x y, S.F (g x) (g y) = S.F x y) ↔ _
    simp only [hQ]
    exact ⟨fun h x => h x x, fun h x _ => h x⟩)

end Spaces

section Split

variable {L : Type} [Field L] [Algebra K L]

@[expose] noncomputable def hypQuadForm (lam : L →ₗ[K] K) : QuadraticForm K (L × L) :=
  LinearMap.BilinMap.toQuadraticMap
    (LinearMap.mk₂ K (fun v w : L × L => lam (v.1 * w.2))
      (fun v v' w => by rw [Prod.fst_add, add_mul, map_add])
      (fun c v w => by rw [Prod.smul_fst, smul_mul_assoc, map_smul])
      (fun v w w' => by rw [Prod.snd_add, mul_add, map_add])
      (fun c v w => by rw [Prod.smul_snd, mul_smul_comm, map_smul]))

theorem hypQuadForm_apply (lam : L →ₗ[K] K) (v : L × L) : hypQuadForm lam v = lam (v.1 * v.2) :=
  rfl

theorem polar_hypQuadForm (lam : L →ₗ[K] K) (v w : L × L) :
    polar (hypQuadForm lam) v w = lam (v.1 * w.2) + lam (w.1 * v.2) :=
  LinearMap.BilinMap.polar_toQuadraticMap v w

theorem nondegenerate_polarBilin_hypQuadForm {lam : L →ₗ[K] K} (hlam : lam ≠ 0) :
    (polarBilin (hypQuadForm lam)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  refine Prod.ext (eq_zero_of_forall_mul hlam fun z => ?_) (eq_zero_of_forall_mul hlam fun z => ?_)
  · simpa [polar_hypQuadForm] using hv (0, z)
  · have := hv (z, 0)
    rw [polar_hypQuadForm, mul_zero, map_zero, zero_add, mul_comm] at this
    exact this

theorem isPlusType_hypQuadForm [FiniteDimensional K L] (lam : L →ₗ[K] K) :
    IsPlusType (hypQuadForm lam) := by
  refine ⟨LinearMap.range (LinearMap.inl K L L), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_prod]
    ring
  · rintro _ ⟨x, rfl⟩
    rw [hypQuadForm_apply, LinearMap.inl_apply, mul_zero, map_zero]

theorem hypQuadForm_prodUnitsHom (lam : L →ₗ[K] K) (u : Lˣ) (v : L × L) :
    hypQuadForm lam (prodUnitsHom K L u v) = hypQuadForm lam v := by
  rw [hypQuadForm_apply, hypQuadForm_apply, prodUnitsHom_apply]
  congr 1
  rw [mul_mul_mul_comm, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

end Split

section Aniso

variable {L : Type} [Field L] [Algebra K L]

@[expose] noncomputable def twistQuadForm (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) :
    QuadraticForm K L :=
  LinearMap.BilinMap.toQuadraticMap (twistSympForm lam σ)

theorem twistQuadForm_apply (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) (x : L) :
    twistQuadForm lam σ x = lam (x * σ x) :=
  rfl

theorem polar_twistQuadForm (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) (x y : L) :
    polar (twistQuadForm lam σ) x y = lam (x * σ y + y * σ x) := by
  rw [twistQuadForm, LinearMap.BilinMap.polar_toQuadraticMap, twistSympForm_apply,
    twistSympForm_apply, map_add]

theorem nondegenerate_polarBilin_twistQuadForm {lam : L →ₗ[K] K} {σ : L ≃ₐ[K] L}
    (hσ : ∀ x, σ (σ x) = x) {z₀ : L} (hz₀ : lam (z₀ + σ z₀) ≠ 0) :
    (polarBilin (twistQuadForm lam σ)).Nondegenerate := by
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun x hx => ?_
  by_contra hx0
  apply hz₀
  have := hx (σ (x⁻¹ * z₀))
  have key : σ x⁻¹ * σ z₀ * σ x = σ z₀ := by
    rw [mul_right_comm, ← map_mul, inv_mul_cancel₀ hx0, map_one, one_mul]
  rw [polar_twistQuadForm, hσ, mul_inv_cancel_left₀ hx0, map_mul, key] at this
  exact this

theorem twistQuadForm_toModuleAut (lam : L →ₗ[K] K) (σ : L ≃ₐ[K] L) {u : Lˣ}
    (hu : (u : L) * σ u = 1) (x : L) :
    twistQuadForm lam σ (DistribMulAction.toModuleAut K L u x) = twistQuadForm lam σ x :=
  toModuleAut_mem_twist lam σ hu x x

end Aniso

section Sigma

variable [Fintype K]

theorem exists_sigmaModel_rep_plus {p : ℕ} [hp : Fact p.Prime] {e a : ℕ} (he : 0 < e)
    (ha : p ^ a ∣ Fintype.card K ^ e - 1) (N : ℕ) :
    ∃ S : FormSpace K K, IsPlusQuadSpace S ∧ finrank K S.V = 2 * e * (N / e) ∧
      ∃ φ : sigmaModel p e a N →* S.isom, Function.Injective φ := by
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) e
  have hLdim : finrank K L = e := FiniteField.finrank_extension K _ e
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq (L := L) (d := p ^ a)
    (by rwa [FiniteField.natCard_extension, Nat.card_eq_fintype_card])
  obtain ⟨lam, hlam⟩ := exists_ne_zero_dual (K := K) L
  let S₀ : FormSpace K K := ⟨L × L, fun v _ => hypQuadForm lam v⟩
  have hS₀ : IsPlusQuadSpace S₀ := ⟨hypQuadForm lam, fun _ _ => rfl,
    nondegenerate_polarBilin_hypQuadForm hlam, isPlusType_hypQuadForm lam⟩
  have hmem : prodUnitsHom K L ζ ∈ S₀.isom := fun v _ => hypQuadForm_prodUnitsHom lam ζ v
  obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem
    (by rw [orderOf_injective _ (prodUnitsHom_injective K L), hζ])
  obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p IsPlusQuadSpace
    (fun ι _ S hS => isPlusQuadSpace_pi S hS) S₀ hS₀ (inferInstanceAs (Nontrivial (L × L)))
    ρ hρ e N
  refine ⟨S, hS, ?_, φ, hφ⟩
  rw [hSdim]
  change finrank K (L × L) * (N / e) = _
  rw [Module.finrank_prod, hLdim, two_mul]

theorem exists_sigmaModel_rep_aniso {p : ℕ} [hp : Fact p.Prime] {f a : ℕ} (hf : 0 < f)
    (ha : p ^ a ∣ Fintype.card K ^ f + 1) (N : ℕ) :
    ∃ S : FormSpace K K, IsQuadSpace S ∧ finrank K S.V = 2 * f * (N / (2 * f)) ∧
      ∃ φ : sigmaModel p (2 * f) a N →* S.isom, Function.Injective φ := by
  set e := 2 * f with hedef
  have he : 0 < e := by omega
  have : NeZero e := ⟨he.ne'⟩
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  let L := FiniteField.Extension K (ringChar K) e
  have hLdim : finrank K L = e := FiniteField.finrank_extension K _ e
  have hq1 : 1 ≤ Fintype.card K := Fintype.card_pos
  have hdvd : p ^ a ∣ Nat.card L - 1 := by
    rw [FiniteField.natCard_extension, Nat.card_eq_fintype_card]
    refine ha.trans ⟨Fintype.card K ^ f - 1, ?_⟩
    have h1 : 1 ≤ Fintype.card K ^ f := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Fintype.card K ^ e := Nat.one_le_pow _ _ hq1
    zify [h1, h2]
    rw [hedef, pow_mul']
    ring
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_eq hdvd
  let σ : L ≃ₐ[K] L := FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ f
  have hσσ : ∀ x, σ (σ x) = x := frob_pow_frob_pow (by rw [hLdim])
  have hζσ : (ζ : L) * σ ζ = 1 := by
    rw [frob_pow_apply, ← pow_succ']
    have : ζ ^ (Fintype.card K ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ ha)
    have h' := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h'
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : L, z₀ + σ z₀ ≠ 0 := by
    by_contra! h
    obtain ⟨x, hx⟩ := exists_pow_ne_self (K := K) (L := L) hf (by rw [hLdim]; omega)
    have h1 : σ 1 = -1 := eq_neg_of_add_eq_zero_right (h 1)
    rw [map_one] at h1
    have hx' : σ x = -x := eq_neg_of_add_eq_zero_right (h x)
    apply hx
    rw [← frob_pow_apply, hx']
    have h2 : (2 : L) = 0 := by linear_combination h1
    linear_combination (-x) * h2
  obtain ⟨lam, hlam⟩ : ∃ lam : L →ₗ[K] K, lam (z₀ + σ z₀) ≠ 0 := by
    by_contra! h
    exact hz₀ ((Module.forall_dual_apply_eq_zero_iff K _).1 h)
  let S₀ : FormSpace K K := ⟨L, fun x _ => twistQuadForm lam σ x⟩
  have hS₀ : IsQuadSpace S₀ :=
    ⟨twistQuadForm lam σ, fun _ _ => rfl, nondegenerate_polarBilin_twistQuadForm hσσ hlam⟩
  have hmem : DistribMulAction.toModuleAut K L ζ ∈ S₀.isom := fun x _ =>
    twistQuadForm_toModuleAut lam σ hζσ x
  obtain ⟨ρ, hρ⟩ := exists_injective_hom_of_orderOf_eq hmem (by rw [orderOf_toModuleAut, hζ])
  obtain ⟨S, hS, hSdim, φ, hφ⟩ := exists_sigmaModel_rep p IsQuadSpace
    (fun ι _ S hS => isQuadSpace_pi S hS) S₀ hS₀ (inferInstanceAs (Nontrivial L)) ρ hρ e N
  refine ⟨S, hS, ?_, φ, hφ⟩
  rw [hSdim]
  change finrank K L * (N / e) = _
  rw [hLdim]

end Sigma

end CFSG.GroupTheory.WeirSylow
