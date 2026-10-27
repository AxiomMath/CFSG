module

public import CFSG.LargeExtraspecial.OrthoF2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2

namespace S2

theorem eq_of_one_smul_eq {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {a b : W}
    (h : (1 : ZMod 2) • a = (1 : ZMod 2) • b) : a = b := by
  simpa using h

section Fix

variable {G : Type*} [Group G] {X : Subgroup G}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

@[expose] def fixOf (ρ : X →* (M ≃ₗ[ZMod 2] M)) (S : Set G) : Submodule (ZMod 2) M where
  carrier := {v | ∀ g : X, (g : G) ∈ S → ρ g v = v}
  add_mem' {u v} hu hv g hg := by rw [map_add, hu g hg, hv g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c v hv g hg := by rw [map_smul, hv g hg]

variable (ρ : X →* (M ≃ₗ[ZMod 2] M))

theorem mem_fixOf {S : Set G} {v : M} : v ∈ fixOf ρ S ↔ ∀ g : X, (g : G) ∈ S → ρ g v = v :=
  Iff.rfl

theorem fixOf_anti {S T : Set G} (h : S ⊆ T) : fixOf ρ T ≤ fixOf ρ S :=
  fun _ hv g hg => hv g (h hg)

theorem fixOf_union (S T : Set G) : fixOf ρ (S ∪ T) = fixOf ρ S ⊓ fixOf ρ T := by
  ext v
  simp only [Submodule.mem_inf, mem_fixOf, Set.mem_union]
  exact ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun h g hg => hg.elim (h.1 g) (h.2 g)⟩

theorem fixOf_closure {S : Set G} (hS : S ⊆ X) :
    fixOf ρ (Subgroup.closure S : Set G) = fixOf ρ S := by
  refine le_antisymm (fixOf_anti ρ Subgroup.subset_closure) fun v hv => ?_
  have hle : Subgroup.closure S ≤ X := (Subgroup.closure_le X).mpr hS
  suffices h : ∀ g ∈ Subgroup.closure S, ∀ hg : g ∈ X, ρ ⟨g, hg⟩ v = v by
    intro g hg
    exact h g hg g.2
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact fun hX => hv ⟨x, hX⟩ hx
  | one =>
    intro h1
    rw [show (⟨1, h1⟩ : X) = 1 from rfl, map_one, LinearEquiv.coe_one, id]
  | mul x y hx hy ihx ihy =>
    intro hxy
    have e : (⟨x * y, hxy⟩ : X) = ⟨x, hle hx⟩ * ⟨y, hle hy⟩ := rfl
    rw [e, map_mul, LinearEquiv.mul_apply, ihy (hle hy), ihx (hle hx)]
  | inv x hx ihx =>
    intro hxi
    have e : (⟨x⁻¹, hxi⟩ : X) = (⟨x, hle hx⟩ : X)⁻¹ := rfl
    rw [e, map_inv]
    conv_lhs => rw [← ihx (hle hx)]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ v

theorem map_fixOf_conj (g : X) {S T : Set G} (hST : ∀ x, x ∈ T ↔ (g : G)⁻¹ * x * g ∈ S) :
    (fixOf ρ S).map (ρ g : M →ₗ[ZMod 2] M) = fixOf ρ T := by
  have key : ∀ (h : X) {S T : Set G}, (∀ x, x ∈ T ↔ (h : G)⁻¹ * x * h ∈ S) →
      (fixOf ρ S).map (ρ h : M →ₗ[ZMod 2] M) ≤ fixOf ρ T := by
    rintro h S T hST _ ⟨v, hv, rfl⟩ k hk
    have hk' : ((h⁻¹ * k * h : X) : G) ∈ S := by
      have := (hST k).mp hk
      simpa using this
    have hfix := hv _ hk'
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hfix
    change ρ k (ρ h v) = ρ h v
    have e := congrArg (ρ h) hfix
    rw [map_inv, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply'] at e
    exact e
  refine le_antisymm (key g hST) fun w hw => ?_
  refine ⟨ρ g⁻¹ w, ?_, ?_⟩
  · refine key g⁻¹ (S := T) (T := S) (fun x => ?_) ⟨w, hw, rfl⟩
    rw [hST, InvMemClass.coe_inv, inv_inv]
    group
  · change ρ g (ρ g⁻¹ w) = w
    rw [map_inv, CFSG.ClassicalGroups.Orthogonal.LinearEquiv.apply_inv_apply']

theorem finrank_fixOf_conj [FiniteDimensional (ZMod 2) M] (g : X) {S T : Set G}
    (hST : ∀ x, x ∈ T ↔ (g : G)⁻¹ * x * g ∈ S) :
    finrank (ZMod 2) (fixOf ρ T) = finrank (ZMod 2) (fixOf ρ S) := by
  rw [← map_fixOf_conj ρ g hST]
  exact LinearEquiv.finrank_map_eq (ρ g) _

theorem fixSpace_eq_of_isCompl {L L₁ : Set G} (hc : IsCompl (fixOf ρ L) (fixOf ρ L₁))
    (hLX : L ⊆ X) (x : X) (hx : (x : G) ∈ L₁)
    (hgen : L₁ ⊆ Subgroup.closure (insert (x : G) L)) :
    fixSpace (ρ x) = fixOf ρ L₁ := by
  have hB : fixOf ρ L₁ ≤ fixSpace (ρ x) := fun v hv => mem_fixSpace.mpr (hv x hx)
  have hA : fixSpace (ρ x) ⊓ fixOf ρ L ≤ fixOf ρ L₁ := by
    rintro v ⟨hvx, hvL⟩
    have hins : insert (x : G) L ⊆ X := Set.insert_subset x.2 hLX
    have hv : v ∈ fixOf ρ (insert (x : G) L) := by
      intro g hg
      rcases hg with hg | hg
      · rw [show g = x from Subtype.ext hg]
        exact mem_fixSpace.mp hvx
      · exact hvL g hg
    rw [← fixOf_closure ρ hins] at hv
    exact fixOf_anti ρ hgen hv
  have h0 : fixOf ρ L ⊓ fixSpace (ρ x) = ⊥ := by
    rw [eq_bot_iff, ← hc.inf_eq_bot]
    intro v hv
    exact ⟨hv.1, hA ⟨hv.2, hv.1⟩⟩
  calc fixSpace (ρ x) = (fixOf ρ L₁ ⊔ fixOf ρ L) ⊓ fixSpace (ρ x) := by
        rw [sup_comm, hc.sup_eq_top, top_inf_eq]
    _ = fixOf ρ L₁ ⊔ fixOf ρ L ⊓ fixSpace (ρ x) := sup_inf_assoc_of_le _ hB
    _ = fixOf ρ L₁ := by rw [h0, sup_bot_eq]

theorem inf_fixSpace_eq_of_compl {L L₁ : Set G} {N : Submodule (ZMod 2) M}
    (hsup : (N ⊓ fixOf ρ L) ⊔ (N ⊓ fixOf ρ L₁) = N)
    (hinf : (N ⊓ fixOf ρ L) ⊓ (N ⊓ fixOf ρ L₁) = ⊥) (hLX : L ⊆ X) (x : X) (hx : (x : G) ∈ L₁)
    (hgen : L₁ ⊆ Subgroup.closure (insert (x : G) L)) :
    N ⊓ fixSpace (ρ x) = N ⊓ fixOf ρ L₁ := by
  have hB : N ⊓ fixOf ρ L₁ ≤ N ⊓ fixSpace (ρ x) :=
    fun v hv => ⟨hv.1, mem_fixSpace.mpr (hv.2 x hx)⟩
  have hA : fixSpace (ρ x) ⊓ fixOf ρ L ≤ fixOf ρ L₁ := by
    rintro v ⟨hvx, hvL⟩
    have hins : insert (x : G) L ⊆ X := Set.insert_subset x.2 hLX
    have hv : v ∈ fixOf ρ (insert (x : G) L) := by
      intro g hg
      rcases hg with hg | hg
      · rw [show g = x from Subtype.ext hg]
        exact mem_fixSpace.mp hvx
      · exact hvL g hg
    rw [← fixOf_closure ρ hins] at hv
    exact fixOf_anti ρ hgen hv
  have h0 : (N ⊓ fixOf ρ L) ⊓ (N ⊓ fixSpace (ρ x)) = ⊥ := by
    rw [eq_bot_iff, ← hinf]
    rintro v ⟨⟨hvN, hvL⟩, -, hvx⟩
    exact ⟨⟨hvN, hvL⟩, hvN, hA ⟨hvx, hvL⟩⟩
  calc N ⊓ fixSpace (ρ x) = ((N ⊓ fixOf ρ L₁) ⊔ (N ⊓ fixOf ρ L)) ⊓ (N ⊓ fixSpace (ρ x)) := by
        rw [sup_comm, hsup, ← inf_assoc, inf_idem]
    _ = (N ⊓ fixOf ρ L₁) ⊔ (N ⊓ fixOf ρ L) ⊓ (N ⊓ fixSpace (ρ x)) := sup_inf_assoc_of_le _ hB
    _ = N ⊓ fixOf ρ L₁ := by rw [h0, sup_bot_eq]

end Fix

section Involution

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem finrank_le_two_mul_inf_fixSpace [FiniteDimensional (ZMod 2) M] {t : M ≃ₗ[ZMod 2] M}
    (htt : t * t = 1) {W : Submodule (ZMod 2) M} (hW : ∀ w ∈ W, t w ∈ W) :
    finrank (ZMod 2) W ≤ 2 * finrank (ZMod 2) ↥(W ⊓ fixSpace t) := by
  let φ : W →ₗ[ZMod 2] M := ((t : M →ₗ[ZMod 2] M) - 1).comp W.subtype
  have hφ : ∀ w : W, φ w = t w - w := fun w => rfl
  have hker : (LinearMap.ker φ).map W.subtype = W ⊓ fixSpace t := by
    ext v
    rw [Submodule.mem_map, Submodule.mem_inf, mem_fixSpace]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [LinearMap.mem_ker, hφ, sub_eq_zero] at hw
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hfix⟩
      exact ⟨⟨v, hv⟩, by rw [LinearMap.mem_ker, hφ, sub_eq_zero]; exact hfix, rfl⟩
  have hrange : LinearMap.range φ ≤ W ⊓ fixSpace t := by
    rintro _ ⟨w, rfl⟩
    rw [hφ]
    exact ⟨W.sub_mem (hW w w.2) w.2, commSpace_le_fixSpace htt (sub_mem_commSpace t w)⟩
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have h1 := Submodule.finrank_mono hrange
  have h2 : finrank (ZMod 2) (LinearMap.ker φ) = finrank (ZMod 2) ↥(W ⊓ fixSpace t) := by
    rw [← hker, Submodule.finrank_map_subtype_eq]
  omega

theorem sup_inf_fixSpace_eq [FiniteDimensional (ZMod 2) M] {a b : M ≃ₗ[ZMod 2] M}
    (ha : a * a = 1) (hb : b * b = 1) {W : Submodule (ZMod 2) M} (haW : ∀ w ∈ W, a w ∈ W)
    (hbW : ∀ w ∈ W, b w ∈ W) (hab : W ⊓ fixSpace a ⊓ fixSpace b = ⊥) :
    (W ⊓ fixSpace a) ⊔ (W ⊓ fixSpace b) = W := by
  refine Submodule.eq_of_le_of_finrank_le (sup_le inf_le_left inf_le_left) ?_
  have h1 := finrank_le_two_mul_inf_fixSpace ha haW
  have h2 := finrank_le_two_mul_inf_fixSpace hb hbW
  have hinf : (W ⊓ fixSpace a) ⊓ (W ⊓ fixSpace b) = ⊥ := by
    rw [← hab]
    ext v
    simp only [Submodule.mem_inf]
    tauto
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (W ⊓ fixSpace a) (W ⊓ fixSpace b)
  rw [hinf, finrank_bot] at h3
  omega

theorem commSpace_eq_fixSpace_of_finrank [FiniteDimensional (ZMod 2) M] {t : M ≃ₗ[ZMod 2] M}
    (htt : t * t = 1) (h : 2 * finrank (ZMod 2) (fixSpace t) = finrank (ZMod 2) M) :
    commSpace t = fixSpace t := by
  refine Submodule.eq_of_le_of_finrank_le (commSpace_le_fixSpace htt) ?_
  have := finrank_commSpace_add_finrank_fixSpace t
  omega

theorem fixSpace_mul_eq_bot {x y : M ≃ₗ[ZMod 2] M} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : fixSpace x ⊓ fixSpace y = ⊥) : fixSpace (x * y) = ⊥ := by
  have hxx : ∀ v, x (x v) = v := fun v => by rw [← LinearEquiv.mul_apply, hx]; rfl
  have hyy : ∀ v, y (y v) = v := fun v => by rw [← LinearEquiv.mul_apply, hy]; rfl
  rw [eq_bot_iff]
  intro v hv
  rw [mem_fixSpace, LinearEquiv.mul_apply] at hv
  have hyv : y v = x v := by
    have := congrArg x hv
    rwa [hxx] at this
  have hyxv : y (x v) = v := by rw [← hyv, hyy]
  set u := x v + v with hu
  have hxu : x u = u := by rw [hu, map_add, hxx, add_comm]
  have hyu : y u = u := by rw [hu, map_add, hyxv, hyv, add_comm]
  have hu0 : u = 0 := by
    have : u ∈ fixSpace x ⊓ fixSpace y := ⟨mem_fixSpace.mpr hxu, mem_fixSpace.mpr hyu⟩
    rwa [hxy, Submodule.mem_bot] at this
  have hxv' : x v = v := by
    rw [hu, add_eq_zero_iff_eq_neg, vec_neg] at hu0
    exact hu0
  have : v ∈ fixSpace x ⊓ fixSpace y :=
    ⟨mem_fixSpace.mpr hxv', mem_fixSpace.mpr (by rw [hyv, hxv'])⟩
  rwa [hxy, Submodule.mem_bot] at this

theorem finrank_map_sub_one_add [FiniteDimensional (ZMod 2) M] (t : M ≃ₗ[ZMod 2] M)
    (N : Submodule (ZMod 2) M) :
    finrank (ZMod 2) (N.map ((t : M →ₗ[ZMod 2] M) - 1)) +
      finrank (ZMod 2) ↥(N ⊓ fixSpace t) = finrank (ZMod 2) N := by
  let φ : N →ₗ[ZMod 2] M := ((t : M →ₗ[ZMod 2] M) - 1).comp N.subtype
  have hrange : LinearMap.range φ = N.map ((t : M →ₗ[ZMod 2] M) - 1) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : (LinearMap.ker φ).map N.subtype = N ⊓ fixSpace t := by
    ext v
    rw [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, hw⟩
    · rintro ⟨hv, hfix⟩
      exact ⟨⟨v, hv⟩, hfix, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker φ
  rw [hrange] at h
  rw [← hker, Submodule.finrank_map_subtype_eq]
  exact h

theorem map_sub_one_le_inf_fixSpace {t : M ≃ₗ[ZMod 2] M} (htt : t * t = 1)
    {N : Submodule (ZMod 2) M} (hN : ∀ v ∈ N, t v ∈ N) :
    N.map ((t : M →ₗ[ZMod 2] M) - 1) ≤ N ⊓ fixSpace t := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨N.sub_mem (hN v hv) hv, commSpace_le_fixSpace htt (sub_mem_commSpace t v)⟩

theorem map_sub_one_eq_inf_fixSpace [FiniteDimensional (ZMod 2) M] {t : M ≃ₗ[ZMod 2] M}
    (htt : t * t = 1) {N : Submodule (ZMod 2) M} (hN : ∀ v ∈ N, t v ∈ N)
    (h : 2 * finrank (ZMod 2) ↥(N ⊓ fixSpace t) = finrank (ZMod 2) N) :
    N.map ((t : M →ₗ[ZMod 2] M) - 1) = N ⊓ fixSpace t := by
  refine Submodule.eq_of_le_of_finrank_le (map_sub_one_le_inf_fixSpace htt hN) ?_
  have := finrank_map_sub_one_add t N
  omega

theorem inf_fixSpace_mul_eq_bot {x y : M ≃ₗ[ZMod 2] M} (hx : x * x = 1) (hy : y * y = 1)
    {N : Submodule (ZMod 2) M} (hxN : ∀ v ∈ N, x v ∈ N)
    (hxy : N ⊓ fixSpace x ⊓ fixSpace y = ⊥) : N ⊓ fixSpace (x * y) = ⊥ := by
  have hxx : ∀ v, x (x v) = v := fun v => by rw [← LinearEquiv.mul_apply, hx]; rfl
  have hyy : ∀ v, y (y v) = v := fun v => by rw [← LinearEquiv.mul_apply, hy]; rfl
  rw [eq_bot_iff]
  intro v hv'
  obtain ⟨hvN, hv⟩ := Submodule.mem_inf.mp hv'
  rw [mem_fixSpace, LinearEquiv.mul_apply] at hv
  have hyv : y v = x v := by
    have := congrArg x hv
    rwa [hxx] at this
  have hyxv : y (x v) = v := by rw [← hyv, hyy]
  set u := x v + v with hu
  have hxu : x u = u := by rw [hu, map_add, hxx, add_comm]
  have hyu : y u = u := by rw [hu, map_add, hyxv, hyv, add_comm]
  have hu0 : u = 0 := by
    have : u ∈ N ⊓ fixSpace x ⊓ fixSpace y :=
      ⟨⟨N.add_mem (hxN v hvN) hvN, mem_fixSpace.mpr hxu⟩, mem_fixSpace.mpr hyu⟩
    rwa [hxy, Submodule.mem_bot] at this
  have hxv' : x v = v := by
    rw [hu, add_eq_zero_iff_eq_neg, vec_neg] at hu0
    exact hu0
  have : v ∈ N ⊓ fixSpace x ⊓ fixSpace y :=
    ⟨⟨hvN, mem_fixSpace.mpr hxv'⟩, mem_fixSpace.mpr (by rw [hyv, hxv'])⟩
  rwa [hxy, Submodule.mem_bot] at this

end Involution

section OrderFive

open Polynomial

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem natDegree_dvd_finrank_of_aeval_eq_zero [FiniteDimensional (ZMod 2) M]
    {P : (ZMod 2)[X]} (hP : Irreducible P) {T : Module.End (ZMod 2) M} (hT : aeval T P = 0) :
    P.natDegree ∣ finrank (ZMod 2) M := by
  have : Fact (Irreducible P) := ⟨hP⟩
  let ψ : AdjoinRoot P →+* Module.End (ZMod 2) M :=
    Ideal.Quotient.lift (Ideal.span {P}) (aeval T).toRingHom (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      simp [hT])
  let _ : Module (AdjoinRoot P) M := Module.compHom M ψ
  have hψ : ∀ c : ZMod 2, ψ (algebraMap (ZMod 2) (AdjoinRoot P) c) = algebraMap _ _ c := by
    intro c
    change (aeval T) (C c) = _
    rw [aeval_C]
  have : IsScalarTower (ZMod 2) (AdjoinRoot P) M := by
    constructor
    intro c k m
    change ψ (c • k) m = c • ψ k m
    rw [Algebra.smul_def, map_mul, hψ]
    rfl
  have hpb := (AdjoinRoot.powerBasis hP.ne_zero).finrank
  rw [AdjoinRoot.powerBasis_dim] at hpb
  have : Module.Finite (AdjoinRoot P) M := Module.Finite.of_restrictScalars_finite (ZMod 2) _ _
  rw [← Module.finrank_mul_finrank (ZMod 2) (AdjoinRoot P) M, hpb]
  exact dvd_mul_right _ _

theorem irreducible_cyclotomic_five : Irreducible (cyclotomic 5 (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 2) (n := 5) (by norm_num)
    dvd_rfl ?_
  rw [natDegree_cyclotomic, show Nat.totient 5 = 4 by decide]
  symm
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨?_, ?_⟩
  · ext
    simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Nat.cast_ofNat, Units.val_one]
    decide
  · intro m hm hm0
    interval_cases m <;>
      (intro h; have := congrArg Units.val h; simp at this; revert this; decide)

theorem four_dvd_finrank_of_pow_five [FiniteDimensional (ZMod 2) M] {r : M ≃ₗ[ZMod 2] M}
    (h5 : r ^ 5 = 1) (hfix : fixSpace r = ⊥) : 4 ∣ finrank (ZMod 2) M := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set T : Module.End (ZMod 2) M := (r : M →ₗ[ZMod 2] M) with hTdef
  have hT5 : T ^ 5 = 1 := by
    ext v
    have h := LinearEquiv.congr_fun h5 v
    rw [LinearEquiv.coe_one, id, LinearEquiv.pow_apply] at h
    rw [hTdef, Module.End.pow_apply, Module.End.one_apply]
    exact h
  have hS : aeval T (cyclotomic 5 (ZMod 2)) = 0 := by
    rw [cyclotomic_prime, map_sum]
    simp only [map_pow, aeval_X]
    ext v
    have h : ((T - 1) * ∑ i ∈ Finset.range 5, T ^ i) v = 0 := by
      rw [mul_geom_sum, hT5, sub_self]
      rfl
    have hmem : (∑ i ∈ Finset.range 5, T ^ i) v ∈ fixSpace r := by
      rw [LinearMap.mem_ker]
      exact h
    rw [hfix, Submodule.mem_bot] at hmem
    rw [hmem]
    rfl
  have h := natDegree_dvd_finrank_of_aeval_eq_zero irreducible_cyclotomic_five hS
  rwa [natDegree_cyclotomic, show Nat.totient 5 = 4 by decide] at h

@[expose] noncomputable def restrictOfMapsTo [FiniteDimensional (ZMod 2) M] (t : M ≃ₗ[ZMod 2] M)
    (N : Submodule (ZMod 2) M) (hN : ∀ v ∈ N, t v ∈ N) : N ≃ₗ[ZMod 2] N :=
  LinearEquiv.ofSubmodules t N N (Submodule.eq_of_le_of_finrank_eq
    (by rintro _ ⟨v, hv, rfl⟩; exact hN v hv) (LinearEquiv.finrank_map_eq t N))

theorem restrictOfMapsTo_apply [FiniteDimensional (ZMod 2) M] (t : M ≃ₗ[ZMod 2] M)
    (N : Submodule (ZMod 2) M) (hN : ∀ v ∈ N, t v ∈ N) (v : N) :
    (restrictOfMapsTo t N hN v : M) = t v :=
  rfl

theorem four_dvd_finrank_of_pow_five_of_mapsTo [FiniteDimensional (ZMod 2) M]
    {r : M ≃ₗ[ZMod 2] M} (h5 : r ^ 5 = 1) {N : Submodule (ZMod 2) M} (hN : ∀ v ∈ N, r v ∈ N)
    (hfix : N ⊓ fixSpace r = ⊥) : 4 ∣ finrank (ZMod 2) N := by
  set r' := restrictOfMapsTo r N hN with hr'
  have hpow : ∀ (n : ℕ) (v : N), ((r' ^ n) v : M) = (r ^ n) v := by
    intro n
    induction n with
    | zero => intro v; rfl
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, pow_succ, LinearEquiv.mul_apply]
      rfl
  refine four_dvd_finrank_of_pow_five (r := r') ?_ ?_
  · ext v
    rw [hpow, h5]
    rfl
  · rw [eq_bot_iff]
    intro v hv
    rw [mem_fixSpace] at hv
    have h1 : r v = v := by
      have := congrArg Subtype.val hv
      rwa [restrictOfMapsTo_apply] at this
    have : (v : M) ∈ N ⊓ fixSpace r := ⟨v.2, mem_fixSpace.mpr h1⟩
    rw [hfix, Submodule.mem_bot] at this
    exact (Submodule.mem_bot _).mpr (Subtype.ext this)

end OrderFive

end S2

end CFSG.LargeExtraspecial
