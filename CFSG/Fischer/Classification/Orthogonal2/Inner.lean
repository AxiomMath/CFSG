module

public import CFSG.Fischer.Classification.Orthogonal2.LocalData

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Fischer.Classification.Recognition.SymO

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem span_map_eq_one_eq_top [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V) :
    Submodule.span (ZMod 2) {u : V | Q u = 1} = ⊤ := by
  rw [eq_top_iff]
  intro x _
  by_cases hx : Q x = 1
  · exact Submodule.subset_span hx
  obtain ⟨r, hr1, -, hr3⟩ := exists_polar_eq_zero_map_ne_zero hnd h5 x x
  have hQr : Q r = 1 := zmod_two_eq_one_of_ne_zero hr3
  have hQx0 : Q x = 0 := (zmod_two_eq_zero_or_eq_one _).resolve_right hx
  have hxr : Q (x + r) = 1 := by
    rw [QuadraticMap.map_add (⇑Q) x r, hQx0, hQr, hr1, zero_add, add_zero]
  have hrr : r + r = 0 := by
    rw [← two_smul (ZMod 2) r, show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hx' : x = (x + r) + r := by rw [add_assoc, hrr, add_zero]
  rw [hx']
  exact add_mem (Submodule.subset_span hxr) (Submodule.subset_span hQr)

theorem exists_eq_conj_of_reflClass [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank (ZMod 2) V)
    (ψ : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q))
    (hψ : ∀ g, g ∈ reflClass Q ↔ ψ g ∈ reflClass Q) :
    ∃ g : TauCeti.QuadraticMap.orthogonalGroup Q, ∀ t ∈ reflClass Q, ψ t = g * t * g⁻¹ := by
  classical
  have hspan := span_map_eq_one_eq_top hnd h5
  let T : V → TauCeti.QuadraticMap.orthogonalGroup Q := fun u =>
    ⟨reflect Q u, reflect_mem_orthogonalGroup Q u⟩
  have hex : ∀ u : V, Q u = 1 → ∃ v, Q v = 1 ∧
      ((ψ (T u) : TauCeti.QuadraticMap.orthogonalGroup Q) : V ≃ₗ[ZMod 2] V) = reflect Q v :=
    fun u hu => (hψ (T u)).mp ⟨u, hu, rfl⟩
  choose! π hπ1 hπ using hex
  have hpol : ∀ u w, Q u = 1 → Q w = 1 → polar Q (π u) (π w) = polar Q u w := by
    intro u w hu hw
    have e1 := mul_comm_iff_polar_eq_zero (g := ψ (T u)) (h := ψ (T w)) (hπ1 u hu) (hπ1 w hw)
      (hπ u hu) (hπ w hw)
    have e2 := mul_comm_iff_polar_eq_zero (g := T u) (h := T w) hu hw rfl rfl
    have e3 : ψ (T u) * ψ (T w) = ψ (T w) * ψ (T u) ↔ T u * T w = T w * T u := by
      rw [← map_mul, ← map_mul]
      exact ψ.injective.eq_iff
    rcases zmod_two_eq_zero_or_eq_one (polar Q u w) with h0 | h0 <;>
      rcases zmod_two_eq_zero_or_eq_one (polar Q (π u) (π w)) with h1 | h1
    · rw [h0, h1]
    · exact absurd (e1.mp (e3.mpr (e2.mpr h0))) (by rw [h1]; exact one_ne_zero)
    · exact absurd (e2.mp (e3.mp (e1.mpr h1))) (by rw [h0]; exact one_ne_zero)
    · rw [h0, h1]
  have hsurj : ∀ v, Q v = 1 → ∃ u, Q u = 1 ∧ π u = v := by
    intro v hv
    have hm : ψ.symm (T v) ∈ reflClass Q :=
      (hψ _).mpr (by rw [MulEquiv.apply_symm_apply]; exact ⟨v, hv, rfl⟩)
    obtain ⟨u, hu, hut⟩ := hm
    refine ⟨u, hu, ?_⟩
    have hTu : T u = ψ.symm (T v) := Subtype.ext hut.symm
    have h2 := hπ u hu
    rw [hTu, MulEquiv.apply_symm_apply] at h2
    exact (eq_of_reflect_eq hnd hv h2 (hπ1 u hu)).symm
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent (ZMod 2) {u : V | Q u = 1}
  have hbtop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan, hspan]
  let bas : Basis b (ZMod 2) V := Basis.mk hbli hbtop
  have hbas : ∀ i, bas i = (i : V) := fun i => Basis.mk_apply hbli hbtop i
  let g₀ : V →ₗ[ZMod 2] V := bas.constr (ZMod 2) fun i => π (i : V)
  have hg₀b : ∀ i : b, g₀ (i : V) = π (i : V) := fun i => by
    have := bas.constr_basis (ZMod 2) (fun i : b => π (i : V)) i
    rw [hbas] at this
    exact this
  have key : ∀ x w, Q w = 1 → polar Q (g₀ x) (π w) = polar Q x w := by
    intro x w hw
    have hL : ((polarBilin Q).flip (π w)).comp g₀ = (polarBilin Q).flip w := by
      refine bas.ext fun i => ?_
      rw [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.flip_apply,
        polarBilin_apply_apply, polarBilin_apply_apply, hbas, hg₀b,
        hpol _ _ (hbS i.2) hw]
    have := LinearMap.congr_fun hL x
    rwa [LinearMap.comp_apply, LinearMap.flip_apply, LinearMap.flip_apply,
      polarBilin_apply_apply, polarBilin_apply_apply] at this
  have hg₀S : ∀ u, Q u = 1 → g₀ u = π u := by
    intro u hu
    have hle : Submodule.span (ZMod 2) {u : V | Q u = 1} ≤
        LinearMap.ker (polarBilin Q (g₀ u - π u)) := by
      rw [Submodule.span_le]
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hsurj v hv
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply, polar_sub_left,
        key u w hw, hpol u w hu hw, sub_self]
    have h0 : g₀ u - π u = 0 := hnd.1 _ fun y => by
      have hy : y ∈ Submodule.span (ZMod 2) {u : V | Q u = 1} := hspan ▸ Submodule.mem_top
      exact LinearMap.mem_ker.mp (hle hy)
    exact sub_eq_zero.mp h0
  have hpres : ∀ x y, polar Q (g₀ x) (g₀ y) = polar Q x y := by
    intro x y
    have hL : (polarBilin Q (g₀ x)).comp g₀ = polarBilin Q x := by
      refine bas.ext fun i => ?_
      rw [LinearMap.comp_apply, polarBilin_apply_apply, polarBilin_apply_apply, hbas,
        hg₀b, key x _ (hbS i.2)]
    have := LinearMap.congr_fun hL y
    rwa [LinearMap.comp_apply, polarBilin_apply_apply, polarBilin_apply_apply] at this
  have hQ : ∀ x, Q (g₀ x) = Q x := by
    intro x
    have hx : x ∈ Submodule.span (ZMod 2) {u : V | Q u = 1} := hspan ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem u hu =>
      have hu' : Q u = 1 := hu
      rw [hg₀S u hu', hπ1 u hu', hu']
    | zero => rw [map_zero]
    | add x y _ _ hx hy =>
      rw [map_add, QuadraticMap.map_add (⇑Q) (g₀ x), QuadraticMap.map_add (⇑Q) x, hx, hy,
        hpres]
    | smul c x _ hx =>
      rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
      · rw [zero_smul, map_zero]
      · rw [one_smul, hx]
  have hinj : Function.Injective g₀ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    refine hnd.1 x fun y => ?_
    rw [polarBilin_apply_apply, ← hpres, LinearMap.mem_ker.mp hx, polar_zero_left]
  let g : V ≃ₗ[ZMod 2] V := LinearEquiv.ofInjectiveEndo g₀ hinj
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact hQ
  refine ⟨⟨g, hgO⟩, ?_⟩
  rintro t ⟨u, hu, htu⟩
  have ht : t = T u := Subtype.ext htu
  subst ht
  apply Subtype.ext
  rw [hπ u hu, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  change reflect Q (π u) = g * reflect Q u * g⁻¹
  rw [reflect_conj hgO u]
  congr 1
  exact (hg₀S u hu).symm

open CFSG.Open Matrix in
theorem exists_eq_conj_of_fischerLinearModel {G : Type} [Group G] {D : Set G}
    (hgen : Subgroup.closure D = ⊤) {m : ℕ} (hm : 3 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hO : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))
    (ψ : MulAut G) (hψ : ∀ g, g ∈ D ↔ ψ g ∈ D) : ∃ x : G, ψ = MulAut.conj x := by
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_orthogonalGroup hO
  have hnd' : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩
  have hdim : finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m := Module.finrank_fin_fun _
  have hD : ∀ y, y ∈ D ↔ Φ y ∈ reflClass Q := fun y => by
    rw [← hΦ]
    exact (Φ.injective.mem_set_image).symm
  let ψ' : MulAut (TauCeti.QuadraticMap.orthogonalGroup Q) := (Φ.symm.trans ψ).trans Φ
  have hψ'apply : ∀ y, ψ' (Φ y) = Φ (ψ y) := fun y => by
    simp [ψ']
  have hψ' : ∀ g, g ∈ reflClass Q ↔ ψ' g ∈ reflClass Q := by
    intro g
    obtain ⟨y, rfl⟩ := Φ.surjective g
    rw [hψ'apply, ← hD, ← hD]
    exact hψ y
  obtain ⟨g₀, hg₀⟩ := exists_eq_conj_of_reflClass hnd' (by omega) ψ' hψ'
  refine ⟨Φ.symm g₀, MulEquiv.ext fun y => ?_⟩
  have hy : y ∈ Subgroup.closure D := hgen ▸ Subgroup.mem_top y
  induction hy using Subgroup.closure_induction with
  | mem d hd =>
    have h1 := hg₀ (Φ d) ((hD d).mp hd)
    rw [MulAut.conj_apply]
    apply Φ.injective
    rw [← hψ'apply, h1, map_mul, map_mul, map_inv, Φ.apply_symm_apply]
  | one => rw [map_one, map_one]
  | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
  | inv a _ ha => rw [map_inv, map_inv, ha]

end CFSG.Fischer.Classification.Orth2
