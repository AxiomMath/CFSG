module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module Submodule
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K]

theorem sign_eq_neg_one_of_involution {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} (h2 : σ ^ 2 = 1) (hfix : ∀ x, σ x ≠ x) {m : ℕ}
    (hcard : Fintype.card α = 2 * m) (hm : Odd m) : Equiv.Perm.sign σ = -1 := by
  rw [Equiv.Perm.sign_of_pow_two_eq_one h2]
  have h0 : Fintype.card (Function.fixedPoints σ) = 0 :=
    Fintype.card_eq_zero_iff.2 ⟨fun x => hfix x.1 x.2⟩
  rw [h0, Nat.sub_zero, hcard, Nat.mul_div_cancel_left m two_pos]
  exact hm.neg_one_pow

theorem hom_eq_one_of_isPerfect {G : Type*} [Group G] [Group.IsPerfect G] (f : G →* ℤˣ)
    (g : G) : f g = 1 :=
  MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker f Group.IsPerfect.mem_commutator)

section Perm

variable {W : Type*} [AddCommGroup W] [Module K W] {Q₂ : QuadraticForm K W}

theorem map_coe_mul (a b : W ≃ₗ[K] W) (L : Submodule K W) :
    L.map ((a * b : W ≃ₗ[K] W) : W →ₗ[K] W) = (L.map (b : W →ₗ[K] W)).map (a : W →ₗ[K] W) := by
  rw [← Submodule.map_comp]
  rfl

theorem map_coe_one (L : Submodule K W) : L.map ((1 : W ≃ₗ[K] W) : W →ₗ[K] W) = L :=
  Submodule.map_id L

theorem map_mem_singularSubspaces {k : ℕ} {e : W ≃ₗ[K] W} (he : ∀ x, Q₂ (e x) = Q₂ x)
    {L : Submodule K W} (hL : L ∈ singularSubspaces Q₂ k) :
    L.map (e : W →ₗ[K] W) ∈ singularSubspaces Q₂ k := by
  refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact hL.1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [LinearEquiv.coe_coe, he]
  exact hL.2 y hy

variable (Q₂) in
@[expose] noncomputable def singPermHom (k : ℕ) :
    TauCeti.QuadraticMap.orthogonalGroup Q₂ →* Equiv.Perm (singularSubspaces Q₂ k) where
  toFun e :=
    { toFun := fun L => ⟨L.1.map (e.1 : W →ₗ[K] W), map_mem_singularSubspaces (map_of_mem e.2) L.2⟩
      invFun := fun L =>
        ⟨L.1.map ((e⁻¹).1 : W →ₗ[K] W), map_mem_singularSubspaces (map_of_mem (e⁻¹).2) L.2⟩
      left_inv := fun L => Subtype.ext (by
        change (L.1.map _).map _ = L.1
        rw [← map_coe_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, map_coe_one])
      right_inv := fun L => Subtype.ext (by
        change (L.1.map _).map _ = L.1
        rw [← map_coe_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_coe_one]) }
  map_one' := Equiv.ext fun L => Subtype.ext (map_coe_one L.1)
  map_mul' e e' := Equiv.ext fun L => Subtype.ext (map_coe_mul e.1 e'.1 L.1)

theorem coe_singPermHom_apply {k : ℕ} (e : TauCeti.QuadraticMap.orthogonalGroup Q₂)
    (L : singularSubspaces Q₂ k) :
    ((singPermHom Q₂ k e L : singularSubspaces Q₂ k) : Submodule K W) =
      (L : Submodule K W).map (e.1 : W →ₗ[K] W) :=
  rfl

theorem map_symm_map_equiv {W' : Type*} [AddCommGroup W'] [Module K W'] (φ : W ≃ₗ[K] W')
    (L : Submodule K W) :
    (L.map (φ : W →ₗ[K] W')).map (φ.symm : W' →ₗ[K] W) = L := by
  ext v
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, Submodule.mem_map_equiv,
    LinearEquiv.symm_apply_apply]

theorem card_singularSubspaces_eq {W' : Type*} [AddCommGroup W'] [Module K W']
    {Q' : QuadraticForm K W'} (φ : W ≃ₗ[K] W') (hφ : ∀ x, Q' (φ x) = Q₂ x) (k : ℕ) :
    Nat.card (singularSubspaces Q₂ k) = Nat.card (singularSubspaces Q' k) := by
  have hφ' : ∀ y, Q₂ (φ.symm y) = Q' y := fun y => by rw [← hφ, LinearEquiv.apply_symm_apply]
  refine Nat.card_congr
    { toFun := fun L => ⟨L.1.map (φ : W →ₗ[K] W'), ?_⟩
      invFun := fun L => ⟨L.1.map (φ.symm : W' →ₗ[K] W), ?_⟩
      left_inv := fun L => Subtype.ext (map_symm_map_equiv φ L.1)
      right_inv := fun L => Subtype.ext (by
        have := map_symm_map_equiv φ.symm L.1
        rwa [LinearEquiv.symm_symm] at this) }
  · refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact L.2.1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, hφ]
    exact L.2.2 y hy
  · refine ⟨by rw [LinearEquiv.finrank_map_eq]; exact L.2.1, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [LinearEquiv.coe_coe, hφ']
    exact L.2.2 y hy

theorem map_reflect_ne [FiniteDimensional K W] (hQ₂ : (polarBilin Q₂).Nondegenerate) {k : ℕ}
    (hW : finrank K W = 2 * k) {L : Submodule K W} (hL : L ∈ singularSubspaces Q₂ k) {u : W}
    (hu : Q₂ u ≠ 0) : L.map (reflect Q₂ u : W →ₗ[K] W) ≠ L := by
  intro h
  have hmem : ∀ z ∈ L, (polar Q₂ u z / Q₂ u) • u ∈ L := fun z hz => by
    have hs : reflect Q₂ u z ∈ L := h ▸ ⟨z, hz, rfl⟩
    rw [reflect_apply hu] at hs
    have := L.sub_mem hz hs
    rwa [sub_sub_cancel] at this
  have huL : u ∈ L := by
    by_cases hc : ∀ z ∈ L, polar Q₂ u z = 0
    ·
      have hrefl : (polarBilin Q₂).IsRefl := fun x y h => by
        rw [polarBilin_apply_apply] at h ⊢
        rwa [polar_comm]
      have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl L
      rw [LinearMap.BilinForm.orthogonal_top_eq_bot hQ₂, inf_bot_eq, finrank_bot, add_zero,
        hW] at hdim
      have hLk := hL.1
      have hle : L ≤ LinearMap.BilinForm.orthogonal (polarBilin Q₂) L := fun x hx =>
        LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => by
          rw [polarBilin_apply_apply]
          exact polar_eq_zero_of_singular hL.2 hy hx
      have heq : L = LinearMap.BilinForm.orthogonal (polarBilin Q₂) L :=
        eq_of_le_of_finrank_eq hle (by omega)
      rw [heq]
      refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun y hy => ?_
      rw [polarBilin_apply_apply, polar_comm]
      exact hc y hy
    · obtain ⟨z, hz, hc⟩ := not_forall₂.1 hc
      have := L.smul_mem (polar Q₂ u z / Q₂ u)⁻¹ (hmem z hz)
      rwa [smul_smul, inv_mul_cancel₀ (div_ne_zero hc hu), one_smul] at this
  exact hu (hL.2 u huL)

end Perm

section Doubled

variable {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] noncomputable def doubleHom :
    TauCeti.QuadraticMap.orthogonalGroup Q →* TauCeti.QuadraticMap.orthogonalGroup (Q.prod Q) where
  toFun g := ⟨g.1.prodCongr (LinearEquiv.refl K V),
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun x => by
      rw [LinearEquiv.prodCongr_apply, QuadraticMap.prod_apply, QuadraticMap.prod_apply,
        map_of_mem g.2]
      rfl⟩
  map_one' := Subtype.ext (LinearEquiv.ext fun _ => rfl)
  map_mul' _ _ := Subtype.ext (LinearEquiv.ext fun _ => rfl)

theorem coe_doubleHom (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    ((doubleHom Q g : TauCeti.QuadraticMap.orthogonalGroup (Q.prod Q)) : (V × V) ≃ₗ[K] _) =
      g.1.prodCongr (LinearEquiv.refl K V) :=
  rfl

theorem prodCongr_reflect {v : V} (hv : Q v ≠ 0) :
    (reflect Q v).prodCongr (LinearEquiv.refl K V) = reflect (Q.prod Q) (v, 0) := by
  have hv' : Q.prod Q (v, 0) ≠ 0 := by
    rwa [QuadraticMap.prod_apply, QuadraticMap.map_zero, add_zero]
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.prodCongr_apply, reflect_apply hv, reflect_apply hv', polar_prod,
    QuadraticMap.prod_apply, polar_zero_left, add_zero, QuadraticMap.map_zero, add_zero]
  ext <;> simp

theorem nondegenerate_polarBilin_prod (hQ : (polarBilin Q).Nondegenerate) :
    (polarBilin (Q.prod Q)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall fun v hv => ?_
  have h1 : v.1 = 0 := eq_zero_of_polar_eq_zero hQ fun w => by
    have := hv (w, 0)
    rwa [polar_prod, polar_zero_right, add_zero] at this
  have h2 : v.2 = 0 := eq_zero_of_polar_eq_zero hQ fun w => by
    have := hv (0, w)
    rwa [polar_prod, polar_zero_right, zero_add] at this
  exact Prod.ext h1 h2

theorem exists_diag_totSing [FiniteDimensional K V] [CharP K 2] :
    ∃ T : Submodule K (V × V), finrank K T = finrank K V ∧ ∀ x ∈ T, Q.prod Q x = 0 := by
  refine ⟨LinearMap.range (LinearMap.prod LinearMap.id LinearMap.id),
    LinearMap.finrank_range_of_inj fun x y h => (Prod.ext_iff.1 h).1, ?_⟩
  rintro _ ⟨v, rfl⟩
  change Q.prod Q (v, v) = 0
  rw [QuadraticMap.prod_apply]
  exact CharTwo.add_self_eq_zero _

theorem card_singularSubspaces_prod [Finite K] [FiniteDimensional K V] [CharP K 2]
    (hQ : (polarBilin Q).Nondegenerate) (hd : 1 ≤ finrank K V) :
    Nat.card (singularSubspaces (Q.prod Q) (finrank K V)) =
      2 * ∏ i ∈ Finset.Icc 1 (finrank K V - 1), (Nat.card K ^ i + 1) := by
  set d := finrank K V with hddef
  have hW : finrank K (V × V) = 2 * d := by
    rw [Module.finrank_prod, two_mul]
  obtain ⟨b, -, -, -, -, hb⟩ := (orthogonal_geometry_split_Witt_flags
    (nondegenerate_polarBilin_prod hQ) hW exists_diag_totSing).1 0 (Nat.zero_le _)
    (fun _ => ⊥) (fun i hi => by rw [show i = 0 by omega, finrank_bot])
    (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun x hx => by
      rw [(mem_bot K).1 hx, QuadraticMap.map_zero])
  have hφ : ∀ x, Q.prod Q (b.equivFun.symm x) = quadPlus d K x := fun x => by
    rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, hb, quadPlus_apply]
  have h := (orthogonal_geometry_split_singular_subspace_count (K := K) hd le_rfl).2.2
  rw [card_singularSubspaces_eq b.equivFun.symm hφ d] at h
  exact_mod_cast h

theorem odd_prod_pow_add_one {q : ℕ} (hq : Even q) (n : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 n, (q ^ i + 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one fun i hi => ?_
  have hi0 : i ≠ 0 := by
    have := (Finset.mem_Icc.1 hi).1
    omega
  exact ((Nat.even_pow' hi0).2 hq).add_one

theorem even_card_of_charTwo [Finite K] [CharP K 2] : Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact even_iff_two_dvd.2 ((CharP.cast_eq_zero_iff K 2 _).1 (FiniteField.cast_card_eq_zero K))

end Doubled

theorem orthogonal_geometry_char_two_reflection_separation {K V : Type*} [Field K] [Finite K]
    [CharP K 2] [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) :
    ∃ χ : TauCeti.QuadraticMap.orthogonalGroup Q →* ℤˣ,
      (∀ g (hg : g ∈ orthElementaryGroup Q), χ ⟨g, orthElementaryGroup_le Q hg⟩ = 1) ∧
      (∀ v, Q v ≠ 0 → χ ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ = -1) ∧
      ∀ v, Q v ≠ 0 → reflect Q v ∉ orthElementaryGroup Q := by
  classical
  set d := finrank K V with hddef
  have hd : 1 ≤ d := by
    obtain ⟨T, hT3, -⟩ := hT
    have := Submodule.finrank_le T
    omega
  have : Finite (V × V) := Module.finite_of_finite K
  have : Finite (Submodule K (V × V)) := Finite.of_injective _ SetLike.coe_injective
  let : Fintype (singularSubspaces (Q.prod Q) d) := Fintype.ofFinite _
  set χ : TauCeti.QuadraticMap.orthogonalGroup Q →* ℤˣ :=
    Equiv.Perm.sign.comp ((singPermHom (Q.prod Q) d).comp (doubleHom Q)) with hχ
  have hE : ∀ g (hg : g ∈ orthElementaryGroup Q), χ ⟨g, orthElementaryGroup_le Q hg⟩ = 1 := by
    intro g hg
    have := (orthogonal_elementary_perfect hQ hT).1
    exact hom_eq_one_of_isPerfect (χ.comp (Subgroup.inclusion (orthElementaryGroup_le Q))) ⟨g, hg⟩
  have hs : ∀ v, Q v ≠ 0 → χ ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩ = -1 := by
    intro v hv
    set s : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨reflect Q v, reflect_mem_orthogonalGroup Q v⟩
    have hs2 : s ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact reflect_mul_self Q v)
    refine sign_eq_neg_one_of_involution (σ := singPermHom (Q.prod Q) d (doubleHom Q s))
      (by rw [← map_pow, ← map_pow, hs2, map_one, map_one]) (fun L hL => ?_)
      (m := ∏ i ∈ Finset.Icc 1 (d - 1), (Nat.card K ^ i + 1))
      (by rw [← Nat.card_eq_fintype_card, card_singularSubspaces_prod hQ hd])
      (odd_prod_pow_add_one even_card_of_charTwo _)
    have hL' := congrArg Subtype.val hL
    rw [coe_singPermHom_apply, coe_doubleHom, prodCongr_reflect hv] at hL'
    have hW : finrank K (V × V) = 2 * d := by
      rw [Module.finrank_prod, two_mul]
    exact map_reflect_ne (nondegenerate_polarBilin_prod hQ) hW L.2
      (by rwa [QuadraticMap.prod_apply, QuadraticMap.map_zero, add_zero]) hL'
  refine ⟨χ, hE, hs, fun v hv hmem => ?_⟩
  have h1 := hE _ hmem
  rw [hs v hv] at h1
  exact absurd h1 (by decide)

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
