module

public import CFSG.LargeExtraspecial.AS35QIxLin
public import CFSG.LargeExtraspecial.OrthoF2PairsCases

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QIx

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Submodule
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {ζ : V ≃ₗ[ZMod 2] V}

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_eq_zero_of_mem_fixSpace (hq : q.polarBilin.Nondegenerate) {σ : V ≃ₗ[ZMod 2] V}
    (hσO : σ ∈ orthogonalGroup q) {u w : V} (hu : u ∈ commSpace σ) (hw : σ w = w) :
    polar q u w = 0 := by
  have hw' : w ∈ fixSpace σ := mem_fixSpace.mpr hw
  rw [fixSpace_eq_orthogonal_commSpace_of_mem hq hσO] at hw'
  exact LinearMap.BilinForm.mem_orthogonal_iff.mp hw' u hu

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_commSpace_eq_zero (hq : q.polarBilin.Nondegenerate) {σ : V ≃ₗ[ZMod 2] V}
    (hσO : σ ∈ orthogonalGroup q) (hσσ : σ * σ = 1) {u u' : V} (hu : u ∈ commSpace σ)
    (hu' : u' ∈ commSpace σ) : polar q u u' = 0 :=
  polar_eq_zero_of_mem_fixSpace hq hσO hu (mem_fixSpace.mp (commSpace_le_fixSpace hσσ hu'))

omit [FiniteDimensional (ZMod 2) V] in
theorem zeta_mem_commSpace {σ : V ≃ₗ[ZMod 2] V} (hσζ : ∀ v, σ (ζ v) = ζ (σ v)) {u : V}
    (hu : u ∈ commSpace σ) : ζ u ∈ commSpace σ := by
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
  exact mem_commSpace.mpr ⟨ζ v, by rw [map_sub, hσζ]⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_ne_zero_mem_commSpace {σ : V ≃ₗ[ZMod 2] V} (hσ1 : σ ≠ 1) :
    ∃ a ∈ commSpace σ, a ≠ 0 := by
  by_contra h
  push Not at h
  apply hσ1
  ext v
  have := h (σ v - v) (sub_mem_commSpace σ v)
  rw [sub_eq_zero] at this
  simpa using this

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_apply_of_mul_self {τ : V ≃ₗ[ZMod 2] V} (hττ : τ * τ = 1) (v : V) :
    τ (τ v) = v := by
  rw [← LinearEquiv.mul_apply, hττ]
  rfl

section Comm

variable (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
  (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hqζ : ∀ v, q (ζ v) = q v)
include hq hV hζ hqζ

theorem commSpace_eq_span_of_comm {σ : V ≃ₗ[ZMod 2] V} (hσO : σ ∈ orthogonalGroup q)
    (hσσ : σ * σ = 1) (hσζ : ∀ v, σ (ζ v) = ζ (σ v)) {a : V} (ha : a ∈ commSpace σ)
    (ha0 : a ≠ 0) : commSpace σ = span (ZMod 2) {a, ζ a} := by
  apply le_antisymm
  · exact le_span_of_isotropic hq hV hζ hqζ (fun u hu => zeta_mem_commSpace hσζ hu)
      (fun u hu u' hu' => polar_commSpace_eq_zero hq hσO hσσ hu hu') ha ha0
  · rw [span_le]
    rintro x (rfl | rfl)
    · exact ha
    · exact zeta_mem_commSpace hσζ ha

theorem isTypeA_two_of_comm {σ : V ≃ₗ[ZMod 2] V} (hσO : σ ∈ orthogonalGroup q)
    (hσσ : σ * σ = 1) (hσζ : ∀ v, σ (ζ v) = ζ (σ v)) (hσ1 : σ ≠ 1) : IsTypeA q σ 2 := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_mem_commSpace hσ1
  refine ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hσO, hσ1, hσσ, ?_, ?_⟩
  · rw [commSpace_eq_span_of_comm hq hV hζ hqζ hσO hσσ hσζ ha ha0]
    exact finrank_span_pair hζ ha0
  · intro x hx
    rw [q_eq_polar hζ hqζ]
    exact polar_commSpace_eq_zero hq hσO hσσ hx (zeta_mem_commSpace hσζ hx)

theorem apply_eq_of_mem_commSpace {σ τ : V ≃ₗ[ZMod 2] V} (hσO : σ ∈ orthogonalGroup q)
    (hσσ : σ * σ = 1) (hσζ : ∀ v, σ (ζ v) = ζ (σ v)) (hττ : τ * τ = 1)
    (hτζ : ∀ v, τ (ζ v) = ζ (τ v)) (hστ : σ * τ = τ * σ) {u : V} (hu : u ∈ commSpace σ) :
    τ u = u := by
  by_cases hu0 : u = 0
  · rw [hu0, map_zero]
  have hA := commSpace_eq_span_of_comm hq hV hζ hqζ hσO hσσ hσζ hu hu0
  have hτu : τ u ∈ commSpace σ := by
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hu
    refine mem_commSpace.mpr ⟨τ v, ?_⟩
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hστ]
  rw [hA] at hτu
  obtain ⟨c, d, hcd⟩ := mem_span_pair_zeta.mp hτu
  have hτ2 := apply_apply_of_mul_self hττ u
  rcases AS35QTh.zmod2_cases c with rfl | rfl <;> rcases AS35QTh.zmod2_cases d with rfl | rfl
  · rw [zero_smul, zero_smul, add_zero] at hcd
    exact absurd (τ.injective (by rw [← hcd, map_zero])) hu0
  · exfalso
    rw [zero_smul, zero_add, one_smul] at hcd
    rw [← hcd, hτζ, ← hcd] at hτ2
    exact hu0 (eq_zero_of_zeta_zeta_eq hζ hτ2)
  · rw [zero_smul, add_zero, one_smul] at hcd
    exact hcd.symm
  · exfalso
    rw [one_smul, one_smul, add_comm, ← zeta_zeta hζ] at hcd
    rw [← hcd, hτζ, hτζ, ← hcd, zeta_cube hζ] at hτ2
    exact hu0 (eq_zero_of_zeta_eq hζ hτ2)

theorem eq_of_commute_of_comm {σ τ : V ≃ₗ[ZMod 2] V} (hσO : σ ∈ orthogonalGroup q)
    (hτO : τ ∈ orthogonalGroup q) (hσσ : σ * σ = 1) (hττ : τ * τ = 1)
    (hσζ : ∀ v, σ (ζ v) = ζ (σ v)) (hτζ : ∀ v, τ (ζ v) = ζ (τ v)) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hστ : σ * τ = τ * σ) : σ = τ := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_mem_commSpace hσ1
  have hA := commSpace_eq_span_of_comm hq hV hζ hqζ hσO hσσ hσζ ha ha0
  have h1 : ∀ u ∈ commSpace σ, ∀ u' ∈ commSpace τ, polar q u u' = 0 := by
    intro u hu u' hu'
    have hfix := apply_eq_of_mem_commSpace hq hV hζ hqζ hσO hσσ hσζ hττ hτζ hστ hu
    rw [polar_comm]
    exact polar_eq_zero_of_mem_fixSpace hq hτO hu' hfix
  have hle : commSpace τ ≤ commSpace σ := by
    have hU := le_span_of_isotropic hq hV hζ hqζ (U := commSpace σ ⊔ commSpace τ)
      (fun u hu => by
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.mp hu
        rw [map_add]
        exact add_mem (mem_sup_left (zeta_mem_commSpace hσζ hx))
          (mem_sup_right (zeta_mem_commSpace hτζ hy)))
      (fun u hu u' hu' => by
        obtain ⟨x, hx, y, hy, rfl⟩ := mem_sup.mp hu
        obtain ⟨x', hx', y', hy', rfl⟩ := mem_sup.mp hu'
        rw [polar_add_left, polar_add_right, polar_add_right,
          polar_commSpace_eq_zero hq hσO hσσ hx hx', h1 x hx y' hy', polar_comm q y x',
          h1 x' hx' y hy, polar_commSpace_eq_zero hq hτO hττ hy hy']
        simp)
      (mem_sup_left ha) ha0
    rw [hA]
    exact le_trans le_sup_right hU
  have heq : commSpace σ = commSpace τ := by
    symm
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    rw [(isTypeA_two_of_comm hq hV hζ hqζ hσO hσσ hσζ hσ1).2.2.2.1,
      (isTypeA_two_of_comm hq hV hζ hqζ hτO hττ hτζ hτ1).2.2.2.1]
  exact OrthoF2.eq_of_commSpace_eq hq (isTypeA_two_of_comm hq hV hζ hqζ hσO hσσ hσζ hσ1)
    (isTypeA_two_of_comm hq hV hζ hqζ hτO hττ hτζ hτ1) heq

theorem mem_commSpace_of_singular {t : V ≃ₗ[ZMod 2] V} (htO : t ∈ orthogonalGroup q)
    (htt : t * t = 1) (htζ : ∀ v, t (ζ v) = ζ (t v)) (ht1 : t ≠ 1) {v : V} (hv : t v = v)
    (hqv : q v = 0) : v ∈ commSpace t := by
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_mem_commSpace ht1
  have hA := commSpace_eq_span_of_comm hq hV hζ hqζ htO htt htζ ha ha0
  by_contra hv'
  rw [hA] at hv'
  have htζv : t (ζ v) = ζ v := by rw [htζ, hv]
  have hζa := zeta_mem_commSpace htζ ha
  exact false_of_four hq hV hζ hqζ ha0 hv' (polar_eq_zero_of_mem_fixSpace hq htO ha hv)
    (polar_eq_zero_of_mem_fixSpace hq htO ha htζv)
    (polar_eq_zero_of_mem_fixSpace hq htO hζa hv)
    (polar_eq_zero_of_mem_fixSpace hq htO hζa htζv)
    ((isTypeA_two_of_comm hq hV hζ hqζ htO htt htζ ht1).2.2.2.2 a ha) hqv

end Comm

section Inv

variable {c : V ≃ₗ[ZMod 2] V}

omit [FiniteDimensional (ZMod 2) V] in
theorem eq_zero_of_fix_of_inv (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0)
    (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) {v : V} (hv : c v = v) (hζv : c (ζ v) = ζ v) : v = 0 := by
  rw [hcζ, hv] at hζv
  exact eq_zero_of_zeta_eq hζ (ζ.injective hζv)

theorem finrank_fixSpace_le_of_inv (hV : finrank (ZMod 2) V = 6)
    (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) :
    finrank (ZMod 2) (fixSpace c) ≤ 3 := by
  set F := fixSpace c with hF
  set F' := F.map (ζ : V →ₗ[ZMod 2] V) with hF'
  have hinf : F ⊓ F' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, hxF'⟩ := mem_inf.mp hx
    obtain ⟨u, huF, rfl⟩ := mem_map.mp hxF'
    have hu : c u = u := mem_fixSpace.mp huF
    have hζu : c (ζ u) = ζ u := mem_fixSpace.mp hxF
    rw [mem_bot]
    change ζ u = 0
    rw [eq_zero_of_fix_of_inv hζ hcζ hu hζu, map_zero]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq F F'
  rw [hinf, finrank_bot, add_zero] at h1
  have h2 : finrank (ZMod 2) F' = finrank (ZMod 2) F := LinearEquiv.finrank_map_eq ζ F
  have h3 : finrank (ZMod 2) (F ⊔ F' : Submodule (ZMod 2) V) ≤ 6 := hV ▸ Submodule.finrank_le _
  omega

theorem commSpace_eq_fixSpace_of_inv (hV : finrank (ZMod 2) V = 6)
    (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) (hcc : c * c = 1) :
    commSpace c = fixSpace c := by
  apply Submodule.eq_of_le_of_finrank_le (commSpace_le_fixSpace hcc)
  have h1 := finrank_commSpace_add_finrank_fixSpace c
  have h2 := finrank_fixSpace_le_of_inv hV hζ hcζ
  omega

theorem finrank_fixSpace_of_inv (hV : finrank (ZMod 2) V = 6)
    (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0) (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) (hcc : c * c = 1) :
    finrank (ZMod 2) (fixSpace c) = 3 := by
  have h1 := finrank_commSpace_add_finrank_fixSpace c
  rw [commSpace_eq_fixSpace_of_inv hV hζ hcζ hcc, hV] at h1
  omega

theorem polar_fixSpace_eq_zero_of_inv (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0)
    (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) (hcO : c ∈ orthogonalGroup q) (hcc : c * c = 1)
    {u u' : V} (hu : c u = u) (hu' : c u' = u') : polar q u u' = 0 := by
  have h := commSpace_eq_fixSpace_of_inv hV hζ hcζ hcc
  have hu1 : u ∈ commSpace c := h ▸ mem_fixSpace.mpr hu
  exact polar_eq_zero_of_mem_fixSpace hq hcO hu1 hu'

theorem exists_singular_fix_not_fix (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hζ : ∀ v, ζ (ζ v) + ζ v + v = 0)
    (hqζ : ∀ v, q (ζ v) = q v) (hcO : c ∈ orthogonalGroup q) (hcc : c * c = 1)
    (hcζ : ∀ v, c (ζ v) = ζ (ζ (c v))) {t : V ≃ₗ[ZMod 2] V} (htO : t ∈ orthogonalGroup q)
    (htt : t * t = 1) (htζ : ∀ v, t (ζ v) = ζ (t v)) (ht1 : t ≠ 1) :
    ∃ v, c v = v ∧ q v = 0 ∧ t v ≠ v := by
  by_contra hcon
  push Not at hcon
  set F := fixSpace c with hF
  have hadd : ∀ u u' : F, q ((u + u' : F) : V) = q u + q u' := by
    intro u u'
    rw [Submodule.coe_add, QuadraticMap.map_add q,
      polar_fixSpace_eq_zero_of_inv hq hV hζ hcζ hcO hcc (mem_fixSpace.mp u.2)
        (mem_fixSpace.mp u'.2), add_zero]
  have hsmul : ∀ (r : ZMod 2) (u : F), q ((r • u : F) : V) = r • q u := by
    intro r u
    rw [Submodule.coe_smul, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
    rcases AS35QTh.zmod2_cases r with rfl | rfl <;> simp
  let φ : F →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u => q u
      map_add' := hadd
      map_smul' := hsmul }
  set E : Submodule (ZMod 2) V := (LinearMap.ker φ).map F.subtype with hE
  have hEF : ∀ x ∈ E, c x = x := by
    rintro x ⟨u, -, rfl⟩
    exact mem_fixSpace.mp u.2
  have hEq : ∀ x ∈ E, q x = 0 := by
    rintro x ⟨u, hu, rfl⟩
    exact hu
  have hEfin : 2 ≤ finrank (ZMod 2) E := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : finrank (ZMod 2) (LinearMap.range φ) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    have h3 := finrank_fixSpace_of_inv hV hζ hcζ hcc
    rw [← hF] at h3
    have h4 : finrank (ZMod 2) E = finrank (ZMod 2) (LinearMap.ker φ) :=
      Submodule.finrank_map_subtype_eq F (LinearMap.ker φ)
    omega
  have hEle : E ≤ commSpace t := fun x hx =>
    mem_commSpace_of_singular hq hV hζ hqζ htO htt htζ ht1 (hcon x (hEF x hx) (hEq x hx))
      (hEq x hx)
  have hEeq : E = commSpace t := Submodule.eq_of_le_of_finrank_le hEle (by
    rw [(isTypeA_two_of_comm hq hV hζ hqζ htO htt htζ ht1).2.2.2.1]
    exact hEfin)
  obtain ⟨a, ha, ha0⟩ := exists_ne_zero_mem_commSpace ht1
  have haE : a ∈ E := hEeq ▸ ha
  have hζaE : ζ a ∈ E := hEeq ▸ zeta_mem_commSpace htζ ha
  exact ha0 (eq_zero_of_fix_of_inv hζ hcζ (hEF a haE) (hEF _ hζaE))

end Inv

end CFSG.LargeExtraspecial.AS35QIx
