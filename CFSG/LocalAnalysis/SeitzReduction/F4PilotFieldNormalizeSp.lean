module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpDescent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6Hom
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTISymplectic

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OutcomeLocal
  (even_symplectic_involution_centralizers_component_free)

section Entrywise

variable {r : ℕ} {K : Type} [Field K]

theorem fieldSp_eq_statedSpMap (σ : K ≃+* K) (g : StatedSp r K) :
    fieldSp r K σ g = statedSpMap (σ : K →+* K) r g := by
  ext i j
  rw [coe_fieldSp, coe_statedSpMap, coe_map_GL]
  rfl

theorem fieldSp_statedSpMap {k : Type} [Field k] (ι : k →+* K) {ρ : k ≃+* k} {ρ' : K ≃+* K}
    (h : ∀ c, ρ' (ι c) = ι (ρ c)) (g : StatedSp r k) :
    fieldSp r K ρ' (statedSpMap ι r g) = statedSpMap ι r (fieldSp r k ρ g) := by
  ext i j
  rw [coe_fieldSp, coe_statedSpMap, coe_statedSpMap, coe_map_GL, coe_map_GL, coe_fieldSp]
  simp only [Matrix.map_apply]
  exact h _

theorem eqLocus_fieldSp_eq_range {k : Type} [Field k] (ι : k →+* K) {σ : K ≃+* K}
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) :
    MonoidHom.eqLocus (fieldSp r K σ : MulAut (StatedSp r K)).toMonoidHom (MonoidHom.id _) =
      (statedSpMap ι r).range := by
  rw [range_statedSpMap_eq_eqLocus ι (σ : K →+* K) hfix r]
  ext g
  change fieldSp r K σ g = g ↔ statedSpMap (σ : K →+* K) r g = g
  rw [fieldSp_eq_statedSpMap]

end Entrywise

section Proj

variable {r : ℕ} {K : Type} [Field K] [NeZero r] [CharP K 2]

variable (r K) in
@[expose] noncomputable def spProjEquiv : StatedSp r K ≃* StatedProj (StatedSp r K) :=
  MulEquiv.ofBijective (proj r K) UnitaryHigher.proj_bijective_of_charTwo

theorem spProjEquiv_apply (g : StatedSp r K) : spProjEquiv r K g = proj r K g :=
  rfl

theorem spProjEquiv_symm_proj (g : StatedSp r K) : (spProjEquiv r K).symm (proj r K g) = g :=
  (spProjEquiv r K).symm_apply_apply g

theorem mulAutCongr_spProjEquiv_conj (g : StatedSp r K) :
    MulAut.congr (spProjEquiv r K) (MulAut.conj g) = conjAut r K ⟨g, statedSp_le_gsp g.2⟩ := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  rw [conjAut_statedSp]
  change spProjEquiv r K (g * (spProjEquiv r K).symm (proj r K h) * g⁻¹) = _
  rw [spProjEquiv_symm_proj, MulAut.conj_apply, spProjEquiv_apply, map_mul, map_mul, map_inv]

theorem mulAutCongr_spProjEquiv_fieldSp (σ : K ≃+* K) :
    MulAut.congr (spProjEquiv r K) (fieldSp r K σ) = fieldAut r K σ := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective x
  change spProjEquiv r K (fieldSp r K σ ((spProjEquiv r K).symm (proj r K h))) = _
  rw [spProjEquiv_symm_proj, fieldAut_proj]
  rfl

end Proj

section FiniteField

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_natCard_eq_two_pow_of_charTwo : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem exists_ringEquiv_eq_sq_of_charTwo : ∃ φ : K ≃+* K, ∀ c, φ c = c ^ 2 := by
  obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨φ, hφ, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  exact ⟨φ, hφ⟩

theorem exists_pow_eq_of_charTwo (ρ : K ≃+* K) : ∃ m : ℕ, ∀ c, ρ c = c ^ 2 ^ m := by
  obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨φ, hφ, hord, hzp, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp
    (hfin.mem_powers_iff_mem_zpowers.mpr (hzp ▸ Subgroup.mem_top ρ))
  exact ⟨m, fun c => by
    rw [← hm, CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringAut_pow_apply_of_sq hφ]⟩

theorem exists_ringEquiv_comp_eq {k : Type} [Field k] [Finite k] [CharP k 2] (ι : k →+* K)
    (ρ : k ≃+* k) : ∃ ρ' : K ≃+* K, ∀ c, ρ' (ι c) = ι (ρ c) := by
  obtain ⟨m, hm⟩ := exists_pow_eq_of_charTwo ρ
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_eq_sq_of_charTwo (K := K)
  exact ⟨φ ^ m, fun c => by
    rw [CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringAut_pow_apply_of_sq hφ, hm,
      map_pow]⟩

end FiniteField

section Descent

variable {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_eq_conj_mul_fieldSp_mul_conj_inv (hr : 3 ≤ r) {σ : K ≃+* K}
    (hσ : orderOf σ = 2) {β : MulAut (StatedSp r K)} (hβ : β * β = 1)
    (hβi : β ∉ (MulAut.conj : StatedSp r K →* MulAut (StatedSp r K)).range) :
    ∃ h : StatedSp r K, β = MulAut.conj h * fieldSp r K σ * (MulAut.conj h)⁻¹ := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charTwo (K := K)
  set a := MulAut.congr (spProjEquiv r K) β with ha_def
  have ha : a * a = 1 := by rw [ha_def, ← map_mul, hβ, map_one]
  obtain ⟨A, ρ, hA⟩ := (automorphism_generation (K := K) hr).2 a
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  have hag : a = conjAut r K ⟨s, statedSp_le_gsp s.2⟩ * fieldAut r K ρ := by rw [hA, hs]
  have hρ : ρ ≠ 1 := by
    rintro rfl
    apply hβi
    refine ⟨s, (MulAut.congr (spProjEquiv r K)).injective ?_⟩
    rw [mulAutCongr_spProjEquiv_conj, ← ha_def, hag, map_one, mul_one]
  obtain ⟨-, hρt, -, -, -, -, -, -, -, -, h, hh⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_symplectic_quadratic_involution_descent
      (by omega) hf hK ha s ρ hag hρ
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  obtain ⟨-, hσt, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.ringEquiv_involution_facts hf hK hσσ hσ1
  have hσρ : σ = ρ := RingEquiv.ext fun t => by rw [hσt, hρt]
  refine ⟨h, (MulAut.congr (spProjEquiv r K)).injective ?_⟩
  rw [← ha_def, hh, map_mul, map_mul, map_inv, mulAutCongr_spProjEquiv_conj,
    mulAutCongr_spProjEquiv_fieldSp, hσρ]

theorem exists_mulAut_statedSpMap_comm {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (hr : 3 ≤ r) (δ : MulAut (StatedSp r k)) :
    ∃ δ' : MulAut (StatedSp r K), ∀ g, δ' (statedSpMap ι r g) = statedSpMap ι r (δ g) := by
  have : NeZero r := ⟨by omega⟩
  obtain ⟨A, ρ, hA⟩ := (automorphism_generation (K := k) hr).2 (MulAut.congr (spProjEquiv r k) δ)
  obtain ⟨s, hs⟩ := UnitaryHigher.exists_conjAut_eq_statedSp A
  have hδ : δ = MulAut.conj s * fieldSp r k ρ := by
    apply (MulAut.congr (spProjEquiv r k)).injective
    rw [hA, hs, map_mul, mulAutCongr_spProjEquiv_conj, mulAutCongr_spProjEquiv_fieldSp]
  obtain ⟨ρ', hρ'⟩ := exists_ringEquiv_comp_eq ι ρ
  refine ⟨MulAut.conj (statedSpMap ι r s) * fieldSp r K ρ', fun g => ?_⟩
  rw [hδ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
    fieldSp_statedSpMap ι hρ', map_mul, map_mul, map_inv]

end Descent

section Normalize

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem commutator_top_statedSp_three (k : Type) [Field k] [Finite k] :
    ⁅(⊤ : Subgroup (StatedSp 3 k)), (⊤ : Subgroup (StatedSp 3 k))⁆ =
      (⊤ : Subgroup (StatedSp 3 k)) :=
  (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 k (by norm_num)
    sp6_field_condition).1.commutator_eq_top

theorem exists_mulEquiv_statedSpMap_eq {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M] (ψ : StatedSp 3 K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (hθi : θ ∉ (MulAut.conj : M →* MulAut M).range)
    (ε : StatedSp 3 k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp 3 K ≃* M, ∀ g, ψ' (statedSpMap ι 3 g) = ε g := by
  set β := MulAut.congr ψ.symm θ with hβdef
  have hβapp : ∀ y, β y = ψ.symm (θ (ψ y)) := fun _ => rfl
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  have hβi : β ∉ (MulAut.conj : StatedSp 3 K →* MulAut (StatedSp 3 K)).range := by
    rintro ⟨s, hs⟩
    apply hθi
    refine ⟨ψ s, MulEquiv.ext fun x => ?_⟩
    have h1 := hβapp (ψ.symm x)
    rw [← hs, MulAut.conj_apply, ψ.apply_symm_apply] at h1
    rw [MulAut.conj_apply, ← ψ.apply_symm_apply (θ x), ← h1, map_mul, map_mul, map_inv,
      ψ.apply_symm_apply]
  obtain ⟨h, hh⟩ := exists_eq_conj_mul_fieldSp_mul_conj_inv le_rfl hσ hβ hβi
  set ψ₁ : StatedSp 3 K ≃* M := (MulAut.conj h).trans ψ with hψ₁
  have hψ₁app : ∀ x, ψ₁ x = ψ (h * x * h⁻¹) := fun _ => rfl
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (fieldSp 3 K σ x) := by
    intro x
    have h1 := hβapp (h * x * h⁻¹)
    rw [hh, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_inv_apply, MulAut.conj_apply,
      show h⁻¹ * (h * x * h⁻¹) * h = x by group] at h1
    rw [hψ₁app, hψ₁app, ← ψ.apply_symm_apply (θ (ψ (h * x * h⁻¹))), ← h1]
  have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M) =
      (statedSpMap ι 3).range.map ψ₁.toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply, ← eqLocus_fieldSp_eq_range ι hfix]
    change θ (ψ₁ x) = ψ₁ x ↔ fieldSp 3 K σ x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have hperf : ⁅(statedSpMap ι 3).range.map ψ₁.toMonoidHom,
      (statedSpMap ι 3).range.map ψ₁.toMonoidHom⁆ =
        (statedSpMap ι 3).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator,
      commutator_top_statedSp_three]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp (statedSpMap ι 3)).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp (statedSpMap ι 3)) :=
    ψ₁.injective.comp (statedSpMap_injective ι 3)
  set δ : MulAut (StatedSp 3 k) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδdef
  have hδ : ∀ g, ψ₁ (statedSpMap ι 3 (δ g)) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := exists_mulAut_statedSpMap_comm ι (le_refl 3) δ
  exact ⟨δ'.trans ψ₁, fun g => by rw [MulEquiv.trans_apply, hδ', hδ]⟩

end Normalize

section NotInner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem eq_one_of_fieldSp_eq_one {r : ℕ} [NeZero r] {σ : K ≃+* K} (h : fieldSp r K σ = 1) :
    σ = 1 := by
  have h1 : fieldAut r K σ = fieldAut r K 1 := by
    rw [← mulAutCongr_spProjEquiv_fieldSp, h, map_one, map_one]
  refine (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.spInner_mul_fieldAut_inj
    (r := r) (K := K) (g := 1) (h := 1) (φ := σ) (ψ := 1) ?_).2
  rw [h1]

theorem map_centralizer_singleton_mulEquiv' {A B : Type*} [Group A] [Group B] (f : A ≃* B)
    (u : A) : (centralizer ({u} : Set A)).map f.toMonoidHom = centralizer ({f u} : Set B) := by
  ext x
  rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg f h
    rwa [map_mul, map_mul, f.apply_symm_apply] at h1
  · intro h
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply, h]

theorem not_mem_range_conj_of_range_eq_perfectCore {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M] (ψ : StatedSp 3 K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (ε : StatedSp 3 k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    θ ∉ (MulAut.conj : M →* MulAut M).range := by
  rintro ⟨z, rfl⟩
  have : Finite M := Finite.of_equiv _ ψ.toEquiv
  have hZ : center M = ⊥ := by
    rw [← map_center_eq ψ, CFSG.Timmesfeld.LieEmbed.center_statedSp_eq_bot, Subgroup.map_bot]
  have hzz : z * z = 1 := by
    have h2 : z * z ∈ center M := by
      rw [mem_center_iff]
      intro y
      have h3 := DFunLike.congr_fun hθ y
      rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (z * z) = z * (z * y * z⁻¹) * z⁻¹ * (z * z) := by rw [h3]
        _ = z * z * y := by group
    rw [hZ, mem_bot] at h2
    exact h2
  have hperfM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M) := by
    have h1 := congrArg (Subgroup.map ψ.toMonoidHom) (commutator_top_statedSp_three K)
    rwa [map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 ψ.surjective] at h1
  by_cases hz1 : z = 1
  ·
    subst hz1
    have htop : MonoidHom.eqLocus (MulAut.conj (1 : M)).toMonoidHom (MonoidHom.id M) = ⊤ := by
      rw [map_one]
      exact eq_top_iff.2 fun y _ => rfl
    rw [htop, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperfM] at hεr
    have hεs : Function.Surjective ε := MonoidHom.range_eq_top.1 hεr
    have hcard : Nat.card (StatedSp 3 k) = Nat.card (StatedSp 3 K) :=
      (Nat.card_eq_of_bijective ε ⟨hε, hεs⟩).trans (Nat.card_congr ψ.toEquiv).symm
    have hιs : Function.Surjective (statedSpMap ι 3) :=
      ((statedSpMap_injective ι 3).bijective_of_nat_card_le hcard.ge).2
    have hσ1 : fieldSp 3 K σ = 1 := by
      have h1 := eqLocus_fieldSp_eq_range (r := 3) ι hfix
      rw [MonoidHom.range_eq_top.2 hιs] at h1
      refine MulEquiv.ext fun g => ?_
      have h2 : g ∈ MonoidHom.eqLocus (fieldSp 3 K σ : MulAut (StatedSp 3 K)).toMonoidHom
          (MonoidHom.id _) := h1 ▸ mem_top g
      exact h2
    have := eq_one_of_fieldSp_eq_one hσ1
    subst this
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  ·
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hzz]) hz1
    set C := centralizer ({z} : Set M) with hC
    have hfixC : MonoidHom.eqLocus (MulAut.conj z).toMonoidHom (MonoidHom.id M) = C := by
      ext y
      change z * y * z⁻¹ = y ↔ y ∈ C
      rw [hC, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
      exact eq_comm
    rw [hfixC] at hεr
    set D₀ := perfectCore C with hD₀
    have hD₀C : D₀ ≤ C := CFSG.Quasithin.perfectCore_le C
    have hcomp : CFSG.IsComponent (D₀.subgroupOf C) := by
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hεr)).trans
          (subgroupOfEquivOfLe hD₀C).symm)
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 3 k (by norm_num)
          sp6_field_condition), ?_⟩
      exact (CFSG.Quasithin.perfectCore_normal C).isSubnormal
    set χ : M ≃* StatedProj (StatedSp 3 K) := ψ.symm.trans (spProjEquiv 3 K) with hχ
    have hχz : orderOf (χ z) = 2 := by rw [MulEquiv.orderOf_eq, hzord]
    set φC : C ≃* centralizer ({χ z} : Set (StatedProj (StatedSp 3 K))) :=
      (C.equivMapOfInjective χ.toMonoidHom χ.injective).trans
        (MulEquiv.subgroupCongr (map_centralizer_singleton_mulEquiv' χ z)) with hφC
    obtain ⟨f, hf, hK⟩ := exists_natCard_eq_two_pow_of_charTwo (K := K)
    exact even_symplectic_involution_centralizers_component_free
      hf (by norm_num) hK (χ z) hχz _ (CFSG.LocalCores.isComponent_map_mulEquiv φC hcomp)

theorem exists_mulEquiv_statedSpMap_eq_of_involution {k : Type} [Field k] [Finite k]
    [CharP k 2] (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type*} [Group M] (ψ : StatedSp 3 K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (ε : StatedSp 3 k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : StatedSp 3 K ≃* M, ∀ g, ψ' (statedSpMap ι 3 g) = ε g :=
  exists_mulEquiv_statedSpMap_eq ι hσ hfix ψ hθ
    (not_mem_range_conj_of_range_eq_perfectCore ι hσ hfix ψ hθ ε hε hεr) ε hε hεr

end NotInner

end CFSG.SeitzReduction.F4Pilot
