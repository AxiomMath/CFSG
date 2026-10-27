module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.Types
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace AS62

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem eq_one_of_ne_zero_zmod2 {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod2_cases a).resolve_left h

theorem eq_zero_of_ne_one_zmod2 {a : ZMod 2} (h : a ≠ 1) : a = 0 :=
  (zmod2_cases a).resolve_right h

theorem polar_eq_zero_of_singular {U : Submodule (ZMod 2) V} (hUq : ∀ u ∈ U, q u = 0) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) : polar q a b = 0 := by
  rw [polar, hUq _ (U.add_mem ha hb), hUq a ha, hUq b hb, sub_zero, sub_zero]

theorem le_orthogonal_of_singular {U : Submodule (ZMod 2) V} (hUq : ∀ u ∈ U, q u = 0) :
    U ≤ LinearMap.BilinForm.orthogonal q.polarBilin U := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  rw [polarBilin_apply_apply]
  exact polar_eq_zero_of_singular hUq hn hx

theorem eq_of_mem_of_finrank_le_one [FiniteDimensional (ZMod 2) V] {K : Submodule (ZMod 2) V}
    (hK : finrank (ZMod 2) K ≤ 1) {a b : V} (ha : a ∈ K) (hb : b ∈ K) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) : a = b := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hK
  have key : ∀ x ∈ K, x ≠ 0 → x = (v : V) := by
    intro x hx hx0
    obtain ⟨c, hc⟩ := hv ⟨x, hx⟩
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul] at hc
      exact absurd (congrArg Subtype.val hc).symm hx0
    · rw [one_smul] at hc
      exact (congrArg Subtype.val hc).symm
  rw [key a ha ha0, key b hb hb0]

theorem sup_span_eq_of_ne [FiniteDimensional (ZMod 2) V] {U : Submodule (ZMod 2) V}
    (hU2 : finrank (ZMod 2) U = 2) {a b : V} (ha : a ∈ U) (hb : b ∈ U) (ha0 : a ≠ 0)
    (hb0 : b ≠ 0) (hab : a ≠ b) : (ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b) = U := by
  have hinf : (ZMod 2 ∙ a) ⊓ (ZMod 2 ∙ b) = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton.mpr fun h => by
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
      rcases zmod2_cases c with rfl | rfl
      · rw [← hc, zero_smul]
      · rw [one_smul] at hc
        exact absurd hc hab)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ a) (ZMod 2 ∙ b)
  rw [hinf, finrank_bot, finrank_span_singleton ha0, finrank_span_singleton hb0] at h1
  refine Submodule.eq_of_le_of_finrank_eq (sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr
    ha) ((Submodule.span_singleton_le_iff_mem _ _).mpr hb)) ?_
  omega

theorem eq_of_mem_of_mem [FiniteDimensional (ZMod 2) V] {ℓ ℓ' : Submodule (ZMod 2) V}
    (h2 : finrank (ZMod 2) ℓ = 2) (h2' : finrank (ZMod 2) ℓ' = 2) {a b : V} (ha : a ∈ ℓ)
    (hb : b ∈ ℓ) (ha' : a ∈ ℓ') (hb' : b ∈ ℓ') (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b) :
    ℓ = ℓ' := by
  rw [← sup_span_eq_of_ne h2 ha hb ha0 hb0 hab, sup_span_eq_of_ne h2' ha' hb' ha0 hb0 hab]

theorem mem_orthogonal_sup_span_iff {a b x : V} :
    x ∈ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2 ∙ a) ⊔ (ZMod 2 ∙ b)) ↔
      polar q a x = 0 ∧ polar q b x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    have ha := h a (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a))
    have hb := h b (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))
    rw [polarBilin_apply_apply] at ha hb
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩ n hn
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polarBilin_apply_apply, polar_add_left, polar_smul_left, polar_smul_left, ha, hb,
      smul_zero, smul_zero, add_zero]

theorem finrank_inf_eq_one_of_ne [FiniteDimensional (ZMod 2) V] {ℓ₁ ℓ₂ : Submodule (ZMod 2) V}
    (h₁ : finrank (ZMod 2) ℓ₁ = 2) (h₂ : finrank (ZMod 2) ℓ₂ = 2) {u : V} (hu0 : u ≠ 0)
    (hu₁ : u ∈ ℓ₁) (hu₂ : u ∈ ℓ₂) (h12 : ℓ₁ ≠ ℓ₂) : finrank (ZMod 2) ↥(ℓ₁ ⊓ ℓ₂) = 1 := by
  have h1 := Submodule.finrank_mono
    ((Submodule.span_singleton_le_iff_mem u (ℓ₁ ⊓ ℓ₂)).mpr ⟨hu₁, hu₂⟩)
  rw [finrank_span_singleton hu0] at h1
  have hlt : ℓ₁ ⊓ ℓ₂ < ℓ₁ := lt_of_le_of_ne inf_le_left fun h =>
    h12 (Submodule.eq_of_le_of_finrank_eq (inf_eq_left.mp h) (by rw [h₁, h₂]))
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  omega

variable [FiniteDimensional (ZMod 2) V]

theorem orthogonal_eq_self_of_singular (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2)
    (hUq : ∀ u ∈ U, q u = 0) : LinearMap.BilinForm.orthogonal q.polarBilin U = U := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_orthogonal_of_singular hUq) ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal hq, hV, hU2]

theorem mem_of_polar_eq_zero (hV : finrank (ZMod 2) V = 4) (hq : q.polarBilin.Nondegenerate)
    {ℓ : Submodule (ZMod 2) V} (hℓ2 : finrank (ZMod 2) ℓ = 2) (hℓq : ∀ v ∈ ℓ, q v = 0)
    {y z x : V} (hy : y ∈ ℓ) (hz : z ∈ ℓ) (hy0 : y ≠ 0) (hz0 : z ≠ 0) (hyz : y ≠ z)
    (hyx : polar q y x = 0) (hzx : polar q z x = 0) : x ∈ ℓ := by
  rw [← orthogonal_eq_self_of_singular hV hq hℓ2 hℓq, ← sup_span_eq_of_ne hℓ2 hy hz hy0 hz0 hyz]
  exact mem_orthogonal_sup_span_iff.mpr ⟨hyx, hzx⟩

theorem sup_span_eq_top_of_not_mem {K : Submodule (ZMod 2) V}
    (hK : finrank (ZMod 2) K + 1 = finrank (ZMod 2) V) {x : V} (hx : x ∉ K) :
    K ⊔ (ZMod 2 ∙ x) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq K (ZMod 2 ∙ x)
  have h2 : K ⊓ (ZMod 2 ∙ x) = ⊥ :=
    disjoint_iff.mp (Submodule.disjoint_span_singleton.mpr fun h => absurd h hx)
  rw [h2, finrank_bot, finrank_span_singleton (by rintro rfl; exact hx K.zero_mem)] at h1
  omega

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_not_mem_of_finrank_lt {K : Submodule (ZMod 2) V}
    (hK : finrank (ZMod 2) K < finrank (ZMod 2) V) : ∃ x, x ∉ K := by
  by_contra! h
  have hKt : K = ⊤ := eq_top_iff.mpr fun x _ => h x
  rw [hKt, finrank_top] at hK
  exact lt_irrefl _ hK

section FixPlane

variable (hV : finrank (ZMod 2) V = 4) (hq : q.polarBilin.Nondegenerate)
  {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2) (hUq : ∀ u ∈ U, q u = 0)
  {ρ : V ≃ₗ[ZMod 2] V} (hρ : ρ ∈ TauCeti.QuadraticMap.orthogonalGroup q)
  (hρU : ∀ u ∈ U, ρ u = u)
include hV hq hU2 hUq hρ hρU

theorem sub_mem_of_fix_tsPlane (v : V) : ρ v - v ∈ U := by
  rw [← orthogonal_eq_self_of_singular hV hq hU2 hUq, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have h1 : polar q n (ρ v) = polar q n v := by
    calc polar q n (ρ v) = polar q (ρ n) (ρ v) := by rw [hρU n hn]
      _ = polar q n v := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hρ n v
  rw [polarBilin_apply_apply, polar_sub_right, h1, sub_self]

theorem polar_sub_self_eq_zero (v : V) : polar q v (ρ v - v) = 0 := by
  have hd := sub_mem_of_fix_tsPlane hV hq hU2 hUq hρ hρU v
  have h1 : q (ρ v) = q v := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hρ v
  have h2 : ρ v = v + (ρ v - v) := by abel
  rw [h2, map_add_eq, hUq _ hd, add_zero] at h1
  linear_combination h1

theorem polar_sub_comm (x y : V) : polar q x (ρ y - y) = polar q y (ρ x - x) := by
  have h := polar_sub_self_eq_zero hV hq hU2 hUq hρ hρU (x + y)
  rw [map_add, show ρ x + ρ y - (x + y) = (ρ x - x) + (ρ y - y) by abel] at h
  simp only [polar_add_left, polar_add_right] at h
  rw [polar_sub_self_eq_zero hV hq hU2 hUq hρ hρU x,
    polar_sub_self_eq_zero hV hq hU2 hUq hρ hρU y, zero_add, add_zero] at h
  rw [← sub_eq_zero, CharTwo.sub_eq_add]
  first | exact h | (rw [add_comm]; exact h)

theorem eq_one_of_fix_tsPlane_of_fix {v : V} (hvU : v ∉ U) (hρv : ρ v = v) : ρ = 1 := by
  set K := U ⊔ (ZMod 2 ∙ v) with hK
  have hKfix : ∀ k ∈ K, ρ k = k := by
    intro k hk
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hk
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add, map_smul, hρU u hu, hρv]
  have hKdim : finrank (ZMod 2) K + 1 = finrank (ZMod 2) V := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (ZMod 2 ∙ v)
    have h2 : U ⊓ (ZMod 2 ∙ v) = ⊥ :=
      disjoint_iff.mp (Submodule.disjoint_span_singleton.mpr fun h => absurd h hvU)
    rw [h2, finrank_bot, hU2, finrank_span_singleton (by rintro rfl; exact hvU U.zero_mem),
      ← hK] at h1
    omega
  obtain ⟨x₀, hx₀⟩ := exists_not_mem_of_finrank_lt (K := K) (by omega)
  have hsup := sup_span_eq_top_of_not_mem hKdim hx₀
  have hx₀fix : ρ x₀ = x₀ := by
    refine sub_eq_zero.mp (hq.1 _ fun y => ?_)
    rw [polarBilin_apply_apply]
    have hy : y ∈ K ⊔ (ZMod 2 ∙ x₀) := hsup ▸ Submodule.mem_top
    obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_add_right, polar_smul_right, QuadraticMap.polar_comm _ (ρ x₀ - x₀) k,
      QuadraticMap.polar_comm _ (ρ x₀ - x₀) x₀, polar_sub_comm hV hq hU2 hUq hρ hρU k x₀,
      hKfix k hk, sub_self, polar_zero_right, polar_sub_self_eq_zero hV hq hU2 hUq hρ hρU x₀,
      smul_zero, add_zero]
  ext y
  have hy : y ∈ K ⊔ (ZMod 2 ∙ x₀) := hsup ▸ Submodule.mem_top
  obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_add, map_smul, hKfix k hk, hx₀fix]
  rfl

end FixPlane

theorem eq_of_fix_tsPlane (hV : finrank (ZMod 2) V = 4) (hq : q.polarBilin.Nondegenerate)
    {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2) (hUq : ∀ u ∈ U, q u = 0)
    {σ τ : V ≃ₗ[ZMod 2] V} (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup q) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hσU : ∀ u ∈ U, σ u = u) (hτU : ∀ u ∈ U, τ u = u) : σ = τ := by
  obtain ⟨v, hv⟩ := exists_not_mem_of_finrank_lt (K := U) (by omega)
  set K := U ⊓ LinearMap.ker (q.polarBilin v) with hK
  have hK1 : finrank (ZMod 2) K ≤ 1 := by
    have hlt : K < U := by
      refine lt_of_le_of_ne inf_le_left fun h => hv ?_
      rw [← orthogonal_eq_self_of_singular hV hq hU2 hUq, LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hnK : n ∈ K := h ▸ hn
      have := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hnK).2
      rw [polarBilin_apply_apply] at this ⊢
      rw [QuadraticMap.polar_comm]
      exact this
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hmem : ∀ ρ ∈ TauCeti.QuadraticMap.orthogonalGroup q, (∀ u ∈ U, ρ u = u) →
      ρ v - v ∈ K := fun ρ hρ hρU =>
    Submodule.mem_inf.mpr ⟨sub_mem_of_fix_tsPlane hV hq hU2 hUq hρ hρU v,
      LinearMap.mem_ker.mpr (by
        rw [polarBilin_apply_apply]
        exact polar_sub_self_eq_zero hV hq hU2 hUq hρ hρU v)⟩
  have hne : ∀ ρ ∈ TauCeti.QuadraticMap.orthogonalGroup q, (∀ u ∈ U, ρ u = u) → ρ ≠ 1 →
      ρ v - v ≠ 0 := fun ρ hρ hρU hρ1 h =>
    hρ1 (eq_one_of_fix_tsPlane_of_fix hV hq hU2 hUq hρ hρU hv (sub_eq_zero.mp h))
  have hστ : σ v = τ v := sub_left_inj.mp (eq_of_mem_of_finrank_le_one hK1 (hmem σ hσ hσU)
    (hmem τ hτ hτU) (hne σ hσ hσU hσ1) (hne τ hτ hτU hτ1))
  have h1 : τ⁻¹ * σ = 1 := by
    refine eq_one_of_fix_tsPlane_of_fix hV hq hU2 hUq (mul_mem (inv_mem hτ) hσ) (fun u hu => ?_)
      hv ?_
    · change τ.symm (σ u) = u
      rw [hσU u hu, LinearEquiv.symm_apply_eq, hτU u hu]
    · change τ.symm (σ v) = v
      rw [hστ, LinearEquiv.symm_apply_apply]
  exact (inv_mul_eq_one.mp h1).symm

theorem card_le_two_of_fix_tsPlane (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {U : Submodule (ZMod 2) V} (hU2 : finrank (ZMod 2) U = 2)
    (hUq : ∀ u ∈ U, q u = 0) {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup q) (hH : ∀ σ ∈ H, ∀ u ∈ U, σ u = u) :
    Nat.card H ≤ 2 := by
  classical
  by_cases h : ∃ σ ∈ H, σ ≠ 1
  · obtain ⟨σ₀, hσ₀H, hσ₀1⟩ := h
    have hsub : (H : Set (V ≃ₗ[ZMod 2] V)) ⊆ {1, σ₀} := by
      intro σ hσ
      by_cases hσ1 : σ = 1
      · exact Or.inl hσ1
      · exact Or.inr (eq_of_fix_tsPlane hV hq hU2 hUq (hHO hσ) (hHO hσ₀H) hσ1 hσ₀1 (hH σ hσ)
          (hH σ₀ hσ₀H))
    calc Nat.card H = (H : Set (V ≃ₗ[ZMod 2] V)).ncard := by
          rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
      _ ≤ ({1, σ₀} : Set (V ≃ₗ[ZMod 2] V)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  · push Not at h
    rw [(Subgroup.eq_bot_iff_forall H).mpr h, Subgroup.card_bot]
    omega

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_eq_of_mem_commSpace_of_isTypeA {σ : V ≃ₗ[ZMod 2] V} {l : ℕ} (hσ : IsTypeA q σ l)
    {v : V} (hv : v ∈ commSpace σ) : σ v = v :=
  mem_fixSpace.mp (commSpace_le_fixSpace hσ.2.2.1 hv)

theorem eq_two_of_isTypeA (hV : finrank (ZMod 2) V = 4) (hq : q.polarBilin.Nondegenerate)
    {σ : V ≃ₗ[ZMod 2] V} {l : ℕ} (hσ : IsTypeA q σ l) : l = 2 := by
  obtain ⟨hiso, hσ1, hσσ, hl, hq0⟩ := hσ
  have hO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have h1 := one_le_finrank_commSpace hσ1
  have h2 := two_mul_finrank_commSpace_le hσσ
  obtain ⟨k, hk⟩ := even_finrank_commSpace_of_forall_eq_zero hq hO hσσ hq0
  omega

theorem fixSpace_eq_commSpace_of_isTypeA (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {σ : V ≃ₗ[ZMod 2] V} {l : ℕ} (hσ : IsTypeA q σ l) :
    fixSpace σ = commSpace σ := by
  have hl := eq_two_of_isTypeA hV hq hσ
  obtain ⟨-, -, hσσ, hcl, -⟩ := hσ
  have h := finrank_commSpace_add_finrank_fixSpace σ
  exact (Submodule.eq_of_le_of_finrank_eq (commSpace_le_fixSpace hσσ) (by omega)).symm

theorem eq_of_isTypeA_of_commSpace_eq (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {σ τ : V ≃ₗ[ZMod 2] V} {l l' : ℕ} (hσ : IsTypeA q σ l)
    (hτ : IsTypeA q τ l') (h : commSpace σ = commSpace τ) : σ = τ := by
  have hl := eq_two_of_isTypeA hV hq hσ
  refine eq_of_fix_tsPlane hV hq (U := commSpace σ) (by rw [hσ.2.2.2.1, hl]) hσ.2.2.2.2
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hσ.1)
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hτ.1) hσ.2.1 hτ.2.1
    (fun v hv => apply_eq_of_mem_commSpace_of_isTypeA hσ hv)
    (fun v hv => apply_eq_of_mem_commSpace_of_isTypeA hτ (h ▸ hv))

theorem eq_one_or_eq_of_isTypeA_of_fix (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {τ : V ≃ₗ[ZMod 2] V} {l : ℕ} (hτ : IsTypeA q τ l)
    {σ : V ≃ₗ[ZMod 2] V} (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hσU : ∀ v ∈ commSpace τ, σ v = v) : σ = 1 ∨ σ = τ := by
  by_cases hσ1 : σ = 1
  · exact Or.inl hσ1
  · have hl := eq_two_of_isTypeA hV hq hτ
    exact Or.inr (eq_of_fix_tsPlane hV hq (U := commSpace τ) (by rw [hτ.2.2.2.1, hl]) hτ.2.2.2.2
      hσ (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hτ.1) hσ1 hτ.2.1 hσU
      (fun v hv => apply_eq_of_mem_commSpace_of_isTypeA hτ hv))

theorem card_le_two_of_fix_hyperplane (hq : q.polarBilin.Nondegenerate)
    {K : Submodule (ZMod 2) V} (hK : finrank (ZMod 2) K + 1 = finrank (ZMod 2) V)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hH : ∀ σ ∈ H, ∀ k ∈ K, σ k = k) : Nat.card H ≤ 2 := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨v, hv⟩ := exists_not_mem_of_finrank_lt (K := K) (by omega)
  have hsup := sup_span_eq_top_of_not_mem hK hv
  set W := LinearMap.BilinForm.orthogonal q.polarBilin K with hW
  have hW1 : finrank (ZMod 2) W = 1 := by
    rw [hW, LinearMap.BilinForm.finrank_orthogonal hq]
    omega
  have hWcard : Nat.card W = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hW1, pow_one]
  have hmem : ∀ σ : H, (σ : V ≃ₗ[ZMod 2] V) v - v ∈ W := by
    intro σ
    rw [hW, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    have h1 : polar q n ((σ : V ≃ₗ[ZMod 2] V) v) = polar q n v := by
      calc polar q n ((σ : V ≃ₗ[ZMod 2] V) v) =
            polar q ((σ : V ≃ₗ[ZMod 2] V) n) ((σ : V ≃ₗ[ZMod 2] V) v) := by
            rw [hH σ σ.2 n hn]
        _ = polar q n v := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hHO σ.2) n v
    rw [polarBilin_apply_apply, polar_sub_right, h1, sub_self]
  let f : H → W := fun σ => ⟨_, hmem σ⟩
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : (σ : V ≃ₗ[ZMod 2] V) v = (τ : V ≃ₗ[ZMod 2] V) v :=
      sub_left_inj.mp (congrArg Subtype.val hστ)
    apply Subtype.ext
    ext y
    have hy : y ∈ K ⊔ (ZMod 2 ∙ v) := hsup ▸ Submodule.mem_top
    obtain ⟨k, hk, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_add, map_add, map_smul, map_smul, hH σ σ.2 k hk, hH τ τ.2 k hk, h1]
  calc Nat.card H ≤ Nat.card W := Nat.card_le_card_of_injective f hf
    _ = 2 := hWcard

theorem card_le_two_of_fix_nondeg (hV : finrank (ZMod 2) V = 4)
    (hq : q.polarBilin.Nondegenerate) {W : Submodule (ZMod 2) V} (hW2 : finrank (ZMod 2) W = 2)
    (hWnd : W ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W = ⊥)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    (hH2 : IsPGroup 2 H) (hH : ∀ σ ∈ H, ∀ w ∈ W, σ w = w) : Nat.card H ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set W' := LinearMap.BilinForm.orthogonal q.polarBilin W with hW'
  have hW'2 : finrank (ZMod 2) W' = 2 := by
    rw [hW', LinearMap.BilinForm.finrank_orthogonal hq, hV, hW2]
  have hmem : ∀ σ ∈ H, ∀ x ∈ W', σ x ∈ W' := by
    intro σ hσ x hx
    rw [hW', LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
    intro n hn
    rw [polarBilin_apply_apply, ← hH σ hσ n hn,
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hHO hσ), ← polarBilin_apply_apply]
    exact hx n hn
  let _ : MulAction H ↥((W' : Set V) \ {0}) :=
    { smul := fun σ x => ⟨(σ : V ≃ₗ[ZMod 2] V) x, hmem σ σ.2 x x.2.1, fun h =>
        x.2.2 (((σ : V ≃ₗ[ZMod 2] V).map_eq_zero_iff).mp h)⟩
      one_smul := fun x => rfl
      mul_smul := fun σ τ x => rfl }
  have hXcard : Nat.card ↥((W' : Set V) \ {0}) = 3 := by
    rw [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem
      (show (0 : V) ∈ (W' : Set V) from W'.zero_mem), ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hW'2]
    norm_num
  obtain ⟨x, hx⟩ := hH2.nonempty_fixed_point_of_prime_not_dvd_card ↥((W' : Set V) \ {0})
    (by rw [hXcard]; norm_num)
  have hx0 : (x : V) ≠ 0 := x.2.2
  have hxW' : (x : V) ∈ W' := x.2.1
  have hxfix : ∀ σ ∈ H, σ (x : V) = x := fun σ hσ =>
    congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hx) ⟨σ, hσ⟩)
  have hxW : (x : V) ∉ W := fun h => hx0 (by
    have : (x : V) ∈ W ⊓ W' := Submodule.mem_inf.mpr ⟨h, hxW'⟩
    rwa [hWnd, Submodule.mem_bot] at this)
  set K := W ⊔ (ZMod 2 ∙ (x : V)) with hK
  have hKdim : finrank (ZMod 2) K + 1 = finrank (ZMod 2) V := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (ZMod 2 ∙ (x : V))
    have h2 : W ⊓ (ZMod 2 ∙ (x : V)) = ⊥ :=
      disjoint_iff.mp (Submodule.disjoint_span_singleton.mpr fun h => absurd h hxW)
    rw [h2, finrank_bot, hW2, finrank_span_singleton hx0, ← hK] at h1
    omega
  refine card_le_two_of_fix_hyperplane hq hKdim hHO fun σ hσ k hk => ?_
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hk
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_add, map_smul, hH σ hσ w hw, hxfix σ hσ]

end Quadratic

end AS62

end CFSG.LargeExtraspecial
