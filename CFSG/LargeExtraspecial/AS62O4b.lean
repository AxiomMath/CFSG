module

public import CFSG.LargeExtraspecial.AS62O4
public import CFSG.LargeExtraspecial.AS35DFourFiveA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
  CFSG.RankThree.Literature.FSmith

namespace AS62

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem eq_or_eq_of_tsPlane (hV : finrank (ZMod 2) V = 4) (hq : q.polarBilin.Nondegenerate)
    {u : V} (hu0 : u ≠ 0) {ℓ ℓ₁ ℓ₂ : Submodule (ZMod 2) V} (hℓ : finrank (ZMod 2) ℓ = 2)
    (hℓ₁ : finrank (ZMod 2) ℓ₁ = 2) (hℓ₂ : finrank (ZMod 2) ℓ₂ = 2) (hqℓ : ∀ v ∈ ℓ, q v = 0)
    (hqℓ₁ : ∀ v ∈ ℓ₁, q v = 0) (hqℓ₂ : ∀ v ∈ ℓ₂, q v = 0) (huℓ : u ∈ ℓ) (huℓ₁ : u ∈ ℓ₁)
    (huℓ₂ : u ∈ ℓ₂) (h12 : ℓ₁ ≠ ℓ₂) : ℓ = ℓ₁ ∨ ℓ = ℓ₂ := by
  by_contra! h
  obtain ⟨h1, h2⟩ := h
  have hnle : ∀ {X Y : Submodule (ZMod 2) V}, finrank (ZMod 2) X = 2 →
      finrank (ZMod 2) Y = 2 → X ≠ Y → ∃ x ∈ X, x ∉ Y := by
    intro X Y hX hY hXY
    by_contra! hle
    exact hXY (Submodule.eq_of_le_of_finrank_eq hle (by rw [hX, hY]))
  obtain ⟨a, ha₁, ha₂⟩ := hnle hℓ₁ hℓ₂ h12
  obtain ⟨b, hb₂, hb₁⟩ := hnle hℓ₂ hℓ₁ (Ne.symm h12)
  obtain ⟨c, hcℓ, hc₁⟩ := hnle hℓ hℓ₁ h1
  have ha0 : a ≠ 0 := by rintro rfl; exact ha₂ ℓ₂.zero_mem
  have hau : u ≠ a := by rintro rfl; exact ha₂ huℓ₂
  have hb0 : b ≠ 0 := by rintro rfl; exact hb₁ ℓ₁.zero_mem
  have hbu : u ≠ b := by rintro rfl; exact hb₁ huℓ₁
  have hc0 : c ≠ 0 := by rintro rfl; exact hc₁ ℓ₁.zero_mem
  have hcu : u ≠ c := by rintro rfl; exact hc₁ huℓ₁
  have hua : polar q u a = 0 := polar_eq_zero_of_singular hqℓ₁ huℓ₁ ha₁
  have hub : polar q u b = 0 := polar_eq_zero_of_singular hqℓ₂ huℓ₂ hb₂
  have huc : polar q u c = 0 := polar_eq_zero_of_singular hqℓ huℓ hcℓ
  have hab : polar q a b = 1 := by
    refine eq_one_of_ne_zero_zmod2 fun h0 => ha₂ ?_
    exact mem_of_polar_eq_zero hV hq hℓ₂ hqℓ₂ huℓ₂ hb₂ hu0 hb0 hbu hua
      (by rw [QuadraticMap.polar_comm]; exact h0)
  have hac : polar q a c = 1 := by
    refine eq_one_of_ne_zero_zmod2 fun h0 => h1 ?_
    have haℓ : a ∈ ℓ := mem_of_polar_eq_zero hV hq hℓ hqℓ huℓ hcℓ hu0 hc0 hcu hua
      (by rw [QuadraticMap.polar_comm]; exact h0)
    exact eq_of_mem_of_mem hℓ hℓ₁ huℓ haℓ huℓ₁ ha₁ hu0 ha0 hau
  have hbc : polar q b c = 1 := by
    refine eq_one_of_ne_zero_zmod2 fun h0 => h2 ?_
    have hbℓ : b ∈ ℓ := mem_of_polar_eq_zero hV hq hℓ hqℓ huℓ hcℓ hu0 hc0 hcu hub
      (by rw [QuadraticMap.polar_comm]; exact h0)
    exact eq_of_mem_of_mem hℓ hℓ₂ huℓ hbℓ huℓ₂ hb₂ hu0 hb0 hbu
  obtain ⟨w, hw⟩ : ∃ w, w = c + a + b := ⟨_, rfl⟩
  have hwu : polar q u w = 0 := by
    rw [hw, polar_add_right, polar_add_right, huc, hua, hub, add_zero, add_zero]
  have hwa : polar q a w = 0 := by
    rw [hw, polar_add_right, polar_add_right, hac, polar_self_eq_zero, hab]
    decide
  have hwb : polar q b w = 0 := by
    rw [hw, polar_add_right, polar_add_right, hbc, QuadraticMap.polar_comm _ b a, hab,
      polar_self_eq_zero]
    decide
  have hw₁ : w ∈ ℓ₁ := mem_of_polar_eq_zero hV hq hℓ₁ hqℓ₁ huℓ₁ ha₁ hu0 ha0 hau hwu hwa
  have hc : w + (a + b) = c := by
    rw [hw, show c + a + b + (a + b) = c + (a + a) + (b + b) by abel, ZModModule.add_self,
      ZModModule.add_self, add_zero, add_zero]
  have hqc := hqℓ c hcℓ
  rw [← hc, map_add_eq, map_add_eq, hqℓ₁ w hw₁, hqℓ₁ a ha₁, hqℓ₂ b hb₂, hab, polar_add_right,
    QuadraticMap.polar_comm _ w a, hwa, QuadraticMap.polar_comm _ w b, hwb] at hqc
  exact absurd hqc (by decide)

theorem exists_finrank_inf_map_eq_one (hq : q.polarBilin.Nondegenerate) {u : V} (hu0 : u ≠ 0)
    {ℓ : Submodule (ZMod 2) V}
    (hℓ : finrank (ZMod 2) ℓ = 2) (hqℓ : ∀ v ∈ ℓ, q v = 0) (huℓ : u ∈ ℓ) :
    ∃ σ ∈ TauCeti.QuadraticMap.orthogonalGroup q, σ u = u ∧
      finrank (ZMod 2) ↥(ℓ ⊓ ℓ.map (σ : V →ₗ[ZMod 2] V)) = 1 := by
  obtain ⟨a, haℓ, hau⟩ : ∃ a ∈ ℓ, a ∉ (ZMod 2 ∙ u) := by
    by_contra! h
    have := Submodule.finrank_mono (show ℓ ≤ ZMod 2 ∙ u from h)
    rw [hℓ, finrank_span_singleton hu0] at this
    omega
  have hrefl : q.polarBilin.IsRefl := (QuadraticMap.isSymm_polarBilin q).isRefl
  obtain ⟨b₀, hb₀u, hb₀a⟩ : ∃ b₀, polar q u b₀ = 0 ∧ polar q a b₀ = 1 := by
    by_contra! h
    apply hau
    have hle : LinearMap.BilinForm.orthogonal q.polarBilin (ZMod 2 ∙ u) ≤
        LinearMap.BilinForm.orthogonal q.polarBilin (ZMod 2 ∙ a) := by
      intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx ⊢
      intro n hn
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hn
      have hux : polar q u x = 0 := by
        have := hx u (Submodule.mem_span_singleton_self u)
        rwa [polarBilin_apply_apply] at this
      rw [polarBilin_apply_apply, polar_smul_left, eq_zero_of_ne_one_zmod2 (h x hux), smul_zero]
    have h2 := LinearMap.BilinForm.orthogonal_le (B := q.polarBilin) hle
    rw [LinearMap.BilinForm.orthogonal_orthogonal hq hrefl,
      LinearMap.BilinForm.orthogonal_orthogonal hq hrefl] at h2
    exact h2 (Submodule.mem_span_singleton_self a)
  obtain ⟨b, hbq, hbu, hba⟩ : ∃ b, q b = 0 ∧ polar q u b = 0 ∧ polar q a b = 1 := by
    rcases zmod2_cases (q b₀) with h0 | h1
    · exact ⟨b₀, h0, hb₀u, hb₀a⟩
    · refine ⟨b₀ + a, ?_, ?_, ?_⟩
      · rw [map_add_eq, h1, hqℓ a haℓ, QuadraticMap.polar_comm, hb₀a]
        decide
      · rw [polar_add_right, hb₀u, polar_eq_zero_of_singular hqℓ huℓ haℓ, add_zero]
      · rw [polar_add_right, hb₀a, polar_self_eq_zero, add_zero]
  have hv : q (a + b) = 1 := by
    rw [map_add_eq, hqℓ a haℓ, hbq, hba]
    decide
  have hbℓ : b ∉ ℓ := fun h => by
    have := polar_eq_zero_of_singular hqℓ haℓ h
    rw [hba] at this
    exact one_ne_zero this
  let _ : Invertible (q (a + b)) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
  set σ := TauCeti.QuadraticMap.reflection q (a + b) with hσ
  have hσapp : ∀ y, σ y = y + polar q (a + b) y • (a + b) := by
    intro y
    have hinv : ⅟(q (a + b)) = 1 := by rw [invOf_eq_inv, hv, inv_one]
    rw [hσ, TauCeti.QuadraticMap.reflection_apply, hinv, one_mul, sub_eq_add_vec (ZMod 2)]
  have hσu : σ u = u := by
    rw [hσapp, polar_add_left, QuadraticMap.polar_comm _ a u, polar_eq_zero_of_singular hqℓ huℓ haℓ,
      QuadraticMap.polar_comm _ b u, hbu, add_zero, zero_smul, add_zero]
  have hσa : σ a = b := by
    rw [hσapp, polar_add_left, polar_self_eq_zero, QuadraticMap.polar_comm _ b a, hba, zero_add,
      one_smul, ← add_assoc, ZModModule.add_self, zero_add]
  refine ⟨σ, TauCeti.QuadraticMap.reflection_mem_orthogonalGroup q (a + b), hσu, ?_⟩
  have hmap2 : finrank (ZMod 2) ↥(ℓ.map (σ : V →ₗ[ZMod 2] V)) = 2 := by
    rw [LinearEquiv.finrank_map_eq, hℓ]
  have huσ : u ∈ ℓ.map (σ : V →ₗ[ZMod 2] V) := ⟨u, huℓ, hσu⟩
  have hbσ : b ∈ ℓ.map (σ : V →ₗ[ZMod 2] V) := ⟨a, haℓ, hσa⟩
  exact finrank_inf_eq_one_of_ne hℓ hmap2 hu0 huℓ huσ fun h => hbℓ (h ▸ hbσ)

theorem exists_tsPlane_ne (hq : q.polarBilin.Nondegenerate) {u : V} (hu0 : u ≠ 0)
    {ℓ₁ : Submodule (ZMod 2) V} (hℓ₁ : finrank (ZMod 2) ℓ₁ = 2)
    (hqℓ₁ : ∀ v ∈ ℓ₁, q v = 0) (huℓ₁ : u ∈ ℓ₁) :
    ∃ ℓ₂ : Submodule (ZMod 2) V, finrank (ZMod 2) ℓ₂ = 2 ∧ (∀ v ∈ ℓ₂, q v = 0) ∧ u ∈ ℓ₂ ∧
      ℓ₂ ≠ ℓ₁ ∧ finrank (ZMod 2) ↥(ℓ₁ ⊓ ℓ₂) = 1 := by
  obtain ⟨σ, hσO, hσu, hσ1⟩ := exists_finrank_inf_map_eq_one hq hu0 hℓ₁ hqℓ₁ huℓ₁
  refine ⟨ℓ₁.map (σ : V →ₗ[ZMod 2] V), by rw [LinearEquiv.finrank_map_eq, hℓ₁], ?_,
    ⟨u, huℓ₁, hσu⟩, fun h => ?_, hσ1⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [LinearEquiv.coe_coe, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hσO]
    exact hqℓ₁ v hv
  · rw [h, inf_idem, hℓ₁] at hσ1
    omega

end Quadratic

end AS62

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem finrank_Qt_of_width_two (hw : S.width = 2) : finrank (ZMod 2) S.Qt = 4 := by
  rw [S.finrank_Qt_eq_two_mul_width, hw]

theorem eq_two_of_typeA (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) {m : ℕ}
    (hA : IsTypeA S.q (S.rhoL hxM) m) : m = 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  exact AS62.eq_two_of_isTypeA (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hA

theorem fixSpace_eq_commSpace_of_typeA (hw : S.width = 2) {x : G} (hxM : x ∈ S.M) {m : ℕ}
    (hA : IsTypeA S.q (S.rhoL hxM) m) : fixSpace (S.rhoL hxM) = commSpace (S.rhoL hxM) := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  exact AS62.fixSpace_eq_commSpace_of_isTypeA (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hA

theorem rhoL_eq_of_commSpace_eq (hw : S.width = 2) {x y : G} (hxM : x ∈ S.M) (hyM : y ∈ S.M)
    {m m' : ℕ} (hx : IsTypeA S.q (S.rhoL hxM) m) (hy : IsTypeA S.q (S.rhoL hyM) m')
    (h : commSpace (S.rhoL hxM) = commSpace (S.rhoL hyM)) : S.rhoL hxM = S.rhoL hyM := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  exact AS62.eq_of_isTypeA_of_commSpace_eq (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hx hy h

theorem eq_one_or_eq_rhoL_of_fix (hw : S.width = 2) {t : G} (htM : t ∈ S.M) {m : ℕ}
    (ht : IsTypeA S.q (S.rhoL htM) m) {σ : S.Qt ≃ₗ[ZMod 2] S.Qt} (hσ : σ ∈ S.O)
    (hσU : ∀ v ∈ commSpace (S.rhoL htM), σ v = v) : σ = 1 ∨ σ = S.rhoL htM := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  exact AS62.eq_one_or_eq_of_isTypeA_of_fix (S.finrank_Qt_of_width_two hw) S.q_nondegenerate ht
    hσ hσU

theorem mem_QG_or_rhoL_eq_of_fix (hw : S.width = 2) {t x : G} (htM : t ∈ S.M) (hxM : x ∈ S.M)
    {m : ℕ} (ht : IsTypeA S.q (S.rhoL htM) m)
    (hfix : ∀ v ∈ commSpace (S.rhoL htM), S.rhoL hxM v = v) :
    x ∈ S.QG ∨ S.rhoL hxM = S.rhoL htM := by
  rcases S.eq_one_or_eq_rhoL_of_fix hw htM ht (S.rhoL_mem hxM) hfix with h | h
  · exact Or.inl ((S.ρ_eq_one_iff ⟨x, hxM⟩).mp (Subtype.ext h))
  · exact Or.inr h

theorem injective_rho_comp_inclusion {P : Subgroup G} (hPM : P ≤ S.M) (hPQ : P ⊓ S.QG = ⊥) :
    Function.Injective (S.O.subtype.comp (S.ρ.comp (Subgroup.inclusion hPM))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : S.ρ (Subgroup.inclusion hPM x) = 1 := Subtype.ext hx
  have h2 : (x : G) ∈ P ⊓ S.QG := mem_inf.mpr ⟨x.2, (S.ρ_eq_one_iff _).mp h1⟩
  rw [hPQ, mem_bot] at h2
  exact Subtype.ext h2

theorem card_le_two_of_rhoL_fix_tsPlane (hw : S.width = 2) {U : Submodule (ZMod 2) S.Qt}
    (hU2 : finrank (ZMod 2) U = 2) (hUq : ∀ u ∈ U, S.q u = 0) {P : Subgroup G}
    (hPM : P ≤ S.M) (hPQ : P ⊓ S.QG = ⊥)
    (hfix : ∀ x (hx : x ∈ P), ∀ u ∈ U, S.rhoL (hPM hx) u = u) : Nat.card P ≤ 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  rw [Nat.card_congr (MonoidHom.ofInjective (S.injective_rho_comp_inclusion hPM hPQ)).toEquiv]
  refine AS62.card_le_two_of_fix_tsPlane (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hU2 hUq
    ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact (S.ρ _).2
  · rintro _ ⟨x, rfl⟩ u hu
    exact hfix x x.2 u hu

theorem card_le_two_of_rhoL_fix_nondeg (hw : S.width = 2) {W : Submodule (ZMod 2) S.Qt}
    (hW2 : finrank (ZMod 2) W = 2)
    (hWnd : W ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin W = ⊥) {P : Subgroup G}
    (hPM : P ≤ S.M) (hPQ : P ⊓ S.QG = ⊥) (hP2 : IsPGroup 2 P)
    (hfix : ∀ x (hx : x ∈ P), ∀ w ∈ W, S.rhoL (hPM hx) w = w) : Nat.card P ≤ 2 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  have hinj := S.injective_rho_comp_inclusion hPM hPQ
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  refine AS62.card_le_two_of_fix_nondeg (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hW2 hWnd
    ?_ (hP2.of_surjective _ (MonoidHom.rangeRestrict_surjective _)) ?_
  · rintro _ ⟨x, rfl⟩
    exact (S.ρ _).2
  · rintro _ ⟨x, rfl⟩ w hw
    exact hfix x x.2 w hw

theorem eq_or_eq_of_tsPlane (hw : S.width = 2) {u : S.Qt} (hu0 : u ≠ 0)
    {ℓ ℓ₁ ℓ₂ : Submodule (ZMod 2) S.Qt} (hℓ : finrank (ZMod 2) ℓ = 2)
    (hℓ₁ : finrank (ZMod 2) ℓ₁ = 2) (hℓ₂ : finrank (ZMod 2) ℓ₂ = 2) (hqℓ : ∀ v ∈ ℓ, S.q v = 0)
    (hqℓ₁ : ∀ v ∈ ℓ₁, S.q v = 0) (hqℓ₂ : ∀ v ∈ ℓ₂, S.q v = 0) (huℓ : u ∈ ℓ) (huℓ₁ : u ∈ ℓ₁)
    (huℓ₂ : u ∈ ℓ₂) (h12 : ℓ₁ ≠ ℓ₂) : ℓ = ℓ₁ ∨ ℓ = ℓ₂ := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  exact AS62.eq_or_eq_of_tsPlane (S.finrank_Qt_of_width_two hw) S.q_nondegenerate hu0 hℓ hℓ₁ hℓ₂
    hqℓ hqℓ₁ hqℓ₂ huℓ huℓ₁ huℓ₂ h12

theorem exists_mem_O_finrank_inf_map_eq_one {u : S.Qt} (hu0 : u ≠ 0)
    {ℓ : Submodule (ZMod 2) S.Qt} (hℓ : finrank (ZMod 2) ℓ = 2) (hqℓ : ∀ v ∈ ℓ, S.q v = 0)
    (huℓ : u ∈ ℓ) :
    ∃ σ : S.O, (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u ∧
      finrank (ZMod 2) ↥(ℓ ⊓ ℓ.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt)) = 1 := by
  have : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite
  obtain ⟨σ, hσ, hσu, h1⟩ := AS62.exists_finrank_inf_map_eq_one S.q_nondegenerate hu0 hℓ hqℓ huℓ
  exact ⟨⟨σ, hσ⟩, hσu, h1⟩

end Setting

end CFSG.LargeExtraspecial
