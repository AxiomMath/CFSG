module

public import CFSG.CharacterTheory.Wreathed.AbelianQuotientTwists
public import CFSG.CharacterTheory.OddOrderBasics.Schur

public section

open scoped BigOperators Classical

namespace CFSG.OddOrderBasics

theorem exists_common_eigenvector_aux {ι : Type*} (n : ℕ) :
    ∀ {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V],
    Module.finrank ℂ V = n → ∀ (f : ι → Module.End ℂ V), (∀ i j, f i * f j = f j * f i) →
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i v = μ • v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ hn f hf
  by_cases hscalar : ∀ i, ∃ c : ℂ, f i = c • 1
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    refine ⟨v, hv, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hscalar i
    exact ⟨c, by rw [hc]; rfl⟩
  ·
    obtain ⟨i, hi⟩ := not_forall.mp hscalar
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (f i)
    set W := (f i).eigenspace μ with hW
    have hWbot : W ≠ ⊥ := hμ
    have hWtop : W ≠ ⊤ := by
      intro htop
      apply hi
      refine ⟨μ, LinearMap.ext fun v => ?_⟩
      have hv : v ∈ W := htop ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      rw [hv]
      rfl
    have hmaps : ∀ j, ∀ v ∈ W, f j v ∈ W := by
      intro j v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [← Module.End.mul_apply, hf i j, Module.End.mul_apply, hv, map_smul]
    let g : ι → Module.End ℂ W := fun j => (f j).restrict (hmaps j)
    have hg : ∀ j k, g j * g k = g k * g j := by
      intro j k
      ext w
      have h := congrArg (fun F : Module.End ℂ V => F (w : V)) (hf j k)
      simpa [g, Module.End.mul_apply] using h
    have hlt : Module.finrank ℂ W < n := hn ▸ Submodule.finrank_lt hWtop
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hWbot
    obtain ⟨w, hw, hweig⟩ := ih _ hlt rfl g hg
    refine ⟨w, fun h => hw (Subtype.ext h), fun j => ?_⟩
    obtain ⟨c, hc⟩ := hweig j
    refine ⟨c, ?_⟩
    have h := congrArg Subtype.val hc
    simpa [g] using h

theorem exists_common_eigenvector {ι V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (f : ι → Module.End ℂ V)
    (hf : ∀ i j, f i * f j = f j * f i) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ μ : ℂ, f i v = μ • v :=
  exists_common_eigenvector_aux _ rfl f hf

theorem exists_eq_smul_of_conj {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ K V) (hρ : ρ.IsIrreducible) (φ : K → K)
    (A : Module.End ℂ V) (B : (Module.End ℂ V)ˣ)
    (hA : ∀ k, A * ρ k = ρ (φ k) * A) (hB : ∀ k, (B : Module.End ℂ V) * ρ k = ρ (φ k) * B) :
    ∃ c : ℂ, A = c • (B : Module.End ℂ V) := by
  set C : Module.End ℂ V := ((B⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) with hCdef
  have hCB : C * B = 1 := Units.inv_mul B
  have hBC : (B : Module.End ℂ V) * C = 1 := Units.mul_inv B
  have hcomm : ∀ k, (C * A) ∘ₗ ρ k = ρ k ∘ₗ (C * A) := by
    intro k
    have h1 : C * ρ (φ k) = ρ k * C := by
      calc C * ρ (φ k) = C * (ρ (φ k) * B) * C := by
            rw [mul_assoc, mul_assoc, hBC, mul_one]
        _ = C * (B * ρ k) * C := by rw [hB]
        _ = ρ k * C := by rw [← mul_assoc, hCB, one_mul]
    change C * A * ρ k = ρ k * (C * A)
    rw [mul_assoc, hA, ← mul_assoc, h1, mul_assoc]
  obtain ⟨c, hc⟩ := complex_irreducible_commuting_scalar ρ hρ _ hcomm
  refine ⟨c, ?_⟩
  calc A = (B : Module.End ℂ V) * (C * A) := by rw [← mul_assoc, hBC, one_mul]
    _ = (B : Module.End ℂ V) * (c • (1 : Module.End ℂ V)) := by rw [hc]; rfl
    _ = c • (B : Module.End ℂ V) := by rw [mul_smul_comm, mul_one]

theorem exists_unit_intertwining_of_character_eq {K V : Type*} [Group K] [Fintype K]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ σ : Representation ℂ K V)
    (hρ : ρ.IsIrreducible) (hchar : σ.character = ρ.character) :
    ∃ U : (Module.End ℂ V)ˣ, ∀ k, (U : Module.End ℂ V) * ρ k = σ k * U := by
  let : ρ.IsIrreducible := hρ
  let : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hdim := Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ σ
  have hρρ := Representation.char_orthonormal ρ ρ
  rw [ite_eq_left ⟨Representation.Equiv.refl ρ⟩] at hρρ
  rw [hchar, hρρ] at hdim
  obtain ⟨f, hf⟩ : ∃ f : Representation.IntertwiningMap ρ σ, f ≠ 0 := by
    by_contra h
    simp only [ne_eq, not_exists, not_not] at h
    have : Subsingleton (Representation.IntertwiningMap ρ σ) :=
      ⟨fun a b => (h a).trans (h b).symm⟩
    rw [Module.finrank_zero_of_subsingleton] at hdim
    norm_num at hdim
  have hinj : Function.Injective f :=
    (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  have hsurj : Function.Surjective f.toLinearMap :=
    LinearMap.injective_iff_surjective.mp hinj
  let e := LinearEquiv.ofBijective f.toLinearMap ⟨hinj, hsurj⟩
  let U : (Module.End ℂ V)ˣ :=
    { val := e.toLinearMap
      inv := e.symm.toLinearMap
      val_inv := LinearMap.ext fun v => by simp
      inv_val := LinearMap.ext fun v => by simp }
  refine ⟨U, fun k => LinearMap.ext fun v => ?_⟩
  exact Representation.IntertwiningMap.isIntertwining ρ σ f k v

theorem intertwiners_commute_of_coprime {X V : Type*} [Group X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {H : Subgroup X} [H.Normal]
    (ρ : Representation ℂ H V) (hρ : ρ.IsIrreducible) {s t : X} (hst : s * t = t * s)
    {n : ℕ} (hsn : s ^ n = 1) (hcop : (Module.finrank ℂ V).Coprime n)
    (Us Ut : (Module.End ℂ V)ˣ)
    (hUs : ∀ h : H, (Us : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal s h) * Us)
    (hUt : ∀ h : H, (Ut : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal t h) * Ut) :
    (Us : Module.End ℂ V) * Ut = Ut * Us := by
  have : Nontrivial V := Wreathed.nontrivial_of_isIrreducible ρ hρ
  have hUU : ∀ (a b : X) (Ua Ub : (Module.End ℂ V)ˣ),
      (∀ h : H, (Ua : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal a h) * Ua) →
      (∀ h : H, (Ub : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal b h) * Ub) →
      ∀ h : H, ((Ua : Module.End ℂ V) * Ub) * ρ h =
        ρ (MulAut.conjNormal (a * b) h) * (Ua * Ub) := by
    intro a b Ua Ub ha hb h
    rw [mul_assoc, hb h, ← mul_assoc, ha, mul_assoc, map_mul, MulAut.mul_apply]
  obtain ⟨c, hc⟩ := exists_eq_smul_of_conj ρ hρ (MulAut.conjNormal (s * t)) (Us * Ut) (Ut * Us)
    (hUU s t Us Ut hUs hUt) (fun h => by rw [Units.val_mul, hUU t s Ut Us hUt hUs h, hst])
  rw [Units.val_mul] at hc
  have hdet : c ^ Module.finrank ℂ V = 1 := by
    have h1 := congrArg LinearMap.det hc
    rw [LinearMap.det_smul, map_mul, map_mul] at h1
    have ha : LinearMap.det (Us : Module.End ℂ V) ≠ 0 := (Us.isUnit.map _).ne_zero
    have hb : LinearMap.det (Ut : Module.End ℂ V) ≠ 0 := (Ut.isUnit.map _).ne_zero
    have h2 : c ^ Module.finrank ℂ V * (LinearMap.det (Us : Module.End ℂ V) *
        LinearMap.det (Ut : Module.End ℂ V)) =
        1 * (LinearMap.det (Us : Module.End ℂ V) * LinearMap.det (Ut : Module.End ℂ V)) := by
      linear_combination -h1
    exact mul_right_cancel₀ (mul_ne_zero ha hb) h2
  have hpow : ∀ (k : ℕ) (h : H), (Us : Module.End ℂ V) ^ k * ρ h =
      ρ (MulAut.conjNormal (s ^ k) h) * (Us : Module.End ℂ V) ^ k := by
    intro k
    induction k with
    | zero => intro h; simp
    | succ k ih =>
      intro h
      rw [pow_succ', mul_assoc, ih, ← mul_assoc, hUs, mul_assoc, pow_succ', map_mul,
        MulAut.mul_apply]
  have hord : c ^ n = 1 := by
    obtain ⟨c', hc'⟩ := exists_eq_smul_of_conj ρ hρ id ((Us : Module.End ℂ V) ^ n) 1
      (fun h => by rw [hpow, hsn, map_one, MulAut.one_apply, id]) (fun h => by simp)
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      rw [zero_smul, ← Units.val_pow_eq_pow_val] at hc'
      exact (Us ^ n).ne_zero hc'
    have hcomm_pow : ∀ k : ℕ, (Us : Module.End ℂ V) ^ k * Ut =
        c ^ k • ((Ut : Module.End ℂ V) * (Us : Module.End ℂ V) ^ k) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc (Us : Module.End ℂ V) ^ (k + 1) * Ut
            = Us * ((Us : Module.End ℂ V) ^ k * Ut) := by rw [pow_succ', mul_assoc]
          _ = Us * (c ^ k • ((Ut : Module.End ℂ V) * (Us : Module.End ℂ V) ^ k)) := by
            rw [ih]
          _ = c ^ k • (((Us : Module.End ℂ V) * Ut) * (Us : Module.End ℂ V) ^ k) := by
            rw [mul_smul_comm, mul_assoc]
          _ = c ^ k • ((c • ((Ut : Module.End ℂ V) * Us)) * (Us : Module.End ℂ V) ^ k) := by
            rw [hc]
          _ = c ^ (k + 1) • ((Ut : Module.End ℂ V) * (Us : Module.End ℂ V) ^ (k + 1)) := by
            rw [smul_mul_assoc, smul_smul, ← pow_succ, mul_assoc, ← pow_succ']
    have h1 := hcomm_pow n
    rw [hc', Units.val_one, mul_smul_comm, mul_one, smul_mul_assoc, one_mul, smul_smul] at h1
    have h2 := smul_left_injective ℂ Ut.ne_zero h1
    have h3 : c' * (c ^ n - 1) = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hc'0
    · exact sub_eq_zero.mp h4
  have hc1 : c = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hdet, hord⟩
  rw [hc, hc1, one_smul]

theorem exists_hom_of_commuting_intertwiners {X V : Type*} [Group X] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {H : Subgroup X} [H.Normal]
    (ρ : Representation ℂ H V) (hρ : ρ.IsIrreducible) (T : Subgroup X)
    (U : T → (Module.End ℂ V)ˣ)
    (hU : ∀ (t : T) (h : H),
      (U t : Module.End ℂ V) * ρ h = ρ (MulAut.conjNormal (t : X) h) * U t)
    (hcomm : ∀ s t : T, (U s : Module.End ℂ V) * U t = U t * U s) :
    ∃ W : T →* Module.End ℂ V,
      ∀ (t : T) (h : H), W t * ρ h = ρ (MulAut.conjNormal (t : X) h) * W t := by
  have : Nontrivial V := Wreathed.nontrivial_of_isIrreducible ρ hρ
  obtain ⟨v, hv0, hveig⟩ := exists_common_eigenvector (fun t : T => (U t : Module.End ℂ V)) hcomm
  choose μ hμ using hveig
  have hμ0 : ∀ t, μ t ≠ 0 := by
    intro t h0
    apply hv0
    have h1 := hμ t
    rw [h0, zero_smul] at h1
    have h2 := congrArg (fun w => (((U t)⁻¹ : (Module.End ℂ V)ˣ) : Module.End ℂ V) w) h1
    simp only [map_zero] at h2
    rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at h2
    exact h2
  let Wf : T → Module.End ℂ V := fun t => (μ t)⁻¹ • (U t : Module.End ℂ V)
  have hWv : ∀ t, Wf t v = v := by
    intro t
    change (μ t)⁻¹ • (U t : Module.End ℂ V) v = v
    rw [hμ, smul_smul, inv_mul_cancel₀ (hμ0 t), one_smul]
  have hWρ : ∀ (t : T) (h : H), Wf t * ρ h = ρ (MulAut.conjNormal (t : X) h) * Wf t := by
    intro t h
    change (μ t)⁻¹ • (U t : Module.End ℂ V) * ρ h = ρ _ * ((μ t)⁻¹ • (U t : Module.End ℂ V))
    rw [smul_mul_assoc, hU, mul_smul_comm]
  have hscal : ∀ (t : T) (A : Module.End ℂ V),
      (∀ h, A * ρ h = ρ (MulAut.conjNormal (t : X) h) * A) → A v = v → A = Wf t := by
    intro t A hA hAv
    obtain ⟨c, hc⟩ := exists_eq_smul_of_conj ρ hρ (MulAut.conjNormal (t : X)) A (U t) hA (hU t)
    have h1 : (c * μ t) • v = (1 : ℂ) • v := by
      rw [one_smul, mul_smul, ← hμ, ← LinearMap.smul_apply, ← hc, hAv]
    have hc' : c = (μ t)⁻¹ := eq_inv_of_mul_eq_one_left (smul_left_injective ℂ hv0 h1)
    rw [hc, hc']
  let W : T →* Module.End ℂ V :=
    { toFun := Wf
      map_one' := (hscal 1 1 (fun h => by simp) rfl).symm
      map_mul' := fun s t => (hscal (s * t) (Wf s * Wf t)
        (fun h => by
          rw [mul_assoc, hWρ t h, ← mul_assoc, hWρ s, mul_assoc, Subgroup.coe_mul, map_mul,
            MulAut.mul_apply])
        (by rw [Module.End.mul_apply, hWv, hWv])).symm }
  exact ⟨W, hWρ⟩

theorem exists_extension_of_compatible {X V : Type*} [Group X] [AddCommGroup V] [Module ℂ V]
    (H T : Subgroup X) [H.Normal] (hHT : H.IsComplement' T) (ρ : Representation ℂ H V)
    (W : T →* Module.End ℂ V)
    (hW : ∀ (t : T) (h : H), W t * ρ h = ρ (MulAut.conjNormal (t : X) h) * W t) :
    ∃ ρ' : Representation ℂ X V, ∀ h : H, ρ' h = ρ h := by
  let φ : T →* MulAut H := MulAut.conjNormal.comp T.subtype
  have hφ : ∀ t, H.subtype.comp (φ t).toMonoidHom =
      (MulAut.conj (T.subtype t)).toMonoidHom.comp H.subtype := by
    intro t
    ext h
    simp [φ, MulAut.conjNormal_apply]
  let e : H ⋊[φ] T ≃* X := MulEquiv.ofBijective (SemidirectProduct.lift H.subtype T.subtype hφ)
    ((SemidirectProduct.equivProd.bijective_comp _).mpr hHT)
  let ρu : H →* (Module.End ℂ V)ˣ := ρ.toHomUnits
  let Wu : T →* (Module.End ℂ V)ˣ := W.toHomUnits
  have hkey : ∀ (t : T) (h : H), ρ (MulAut.conjNormal (t : X) h) = W t * ρ h * W t⁻¹ := by
    intro t h
    rw [hW, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have hcond : ∀ t, ρu.comp (φ t).toMonoidHom = (MulAut.conj (Wu t)).toMonoidHom.comp ρu := by
    intro t
    refine MonoidHom.ext fun h => Units.ext ?_
    change ρ (MulAut.conjNormal (t : X) h) = W t * ρ h * ((W.toHomUnits t)⁻¹ : (Module.End ℂ V)ˣ)
    rw [← map_inv, MonoidHom.coe_toHomUnits, hkey]
  let Φ := SemidirectProduct.lift ρu Wu hcond
  refine ⟨(Units.coeHom _).comp (Φ.comp e.symm.toMonoidHom), fun h => ?_⟩
  have he : e.symm (h : X) = SemidirectProduct.inl h := by
    rw [MulEquiv.symm_apply_eq]
    change (h : X) = SemidirectProduct.lift H.subtype T.subtype hφ (SemidirectProduct.inl h)
    rw [SemidirectProduct.lift_inl]
    rfl
  change ((Φ (e.symm (h : X)) : (Module.End ℂ V)ˣ) : Module.End ℂ V) = ρ h
  rw [he, SemidirectProduct.lift_inl]
  rfl

end CFSG.OddOrderBasics
