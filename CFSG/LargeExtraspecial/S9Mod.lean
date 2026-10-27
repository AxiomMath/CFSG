module

public import CFSG.LargeExtraspecial.S2SpOne

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_spTransvection_le (hf : f.IsAlt) (p : V) :
    commSpace (spTransvection f hf p) ≤ (ZMod 2) ∙ p := by
  intro v hv
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  rw [spTransvection_apply, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self p)

omit [FiniteDimensional (ZMod 2) V] in
theorem not_isSpTypeA_spTransvection (hf : f.IsAlt) (p : V) :
    ¬ IsSpTypeA f (spTransvection f hf p) 2 := by
  intro h
  have h1 := Submodule.finrank_mono (commSpace_spTransvection_le hf p)
  have h2 := finrank_span_le_card (R := ZMod 2) ({p} : Set V)
  rw [Set.toFinset_singleton, Finset.card_singleton] at h2
  have := h.2.2.2.1
  omega

@[expose] noncomputable def spTv (hf : f.IsAlt) (p : V) : TauCeti.BilinForm.isometryGroup f :=
  ⟨spTransvection f hf p, spTransvection_mem_isometryGroup hf p⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem coe_spTv (hf : f.IsAlt) (p : V) :
    ((spTv hf p : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) =
      spTransvection f hf p :=
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem spTv_mul_self (hf : f.IsAlt) (p : V) : spTv hf p * spTv hf p = 1 := by
  apply Subtype.ext
  change spTransvection f hf p * spTransvection f hf p = 1
  ext x
  rw [LinearEquiv.mul_apply, spTransvection_apply, spTransvection_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, hf.self_eq_zero, smul_zero, add_zero, add_assoc,
    vec_add_self, add_zero, LinearEquiv.coe_one, id]

variable [FiniteDimensional (ZMod 2) M] (ρ : TauCeti.BilinForm.isometryGroup f →* (M ≃ₗ[ZMod 2] M))

theorem fixSpace_spTv (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) :
    fixSpace (ρ (spTv hf p₁)) = fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) ∧
      (⊤ : Submodule (ZMod 2) M).map ((ρ (spTv hf p₁) : M →ₗ[ZMod 2] M) - 1) =
        fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) := by
  obtain ⟨-, hp₁0, -⟩ :=
    linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hmem : ((spTv hf p₁ : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) ∈
      spRadFix f ⊥ p₁ := by
    rw [coe_spTv, spRadFix_bot]
    exact spTransvection_mem_spPointRadical hf p₁
  have hne : ((spTv hf p₁ : TauCeti.BilinForm.isometryGroup f) : V ≃ₗ[ZMod 2] V) ≠ 1 := by
    rw [coe_spTv]
    exact spTransvection_ne_one hf hnd hp₁0
  have hb0 := sp_timmesfeld_2_1_b0 ρ hf hnd (F := ⊥) (bot_inf_eq _) (m := m)
    (by rw [spPerp_bot, finrank_top]; exact hdim) (N := ⊤) (fun _ _ v _ => Submodule.mem_top)
    (by rw [spPerp_bot]; exact Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    hpp₁ hD (spTv hf p₁) hmem hne (not_isSpTypeA_spTransvection hf p₁)
  rw [top_inf_eq, top_inf_eq, spRadFix_bot] at hb0
  exact hb0

theorem spRadDecomp_of_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) {U : Submodule (ZMod 2) M}
    (hU : ∀ x, ∀ u ∈ U, ρ x u ∈ U) : SpRadDecomp ρ ⊥ U p p₁ := by
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  obtain ⟨hx, -⟩ := fixSpace_spTv ρ hf hnd hdim hpp₁ hD
  obtain ⟨hy, -⟩ := fixSpace_spTv ρ hf hnd hdim hp₁p hD.symm
  rw [SpRadDecomp, spRadFix_bot, spRadFix_bot]
  have hinf := hD.2
  rw [spRadFix_bot, spRadFix_bot, top_inf_eq, top_inf_eq] at hinf
  have hxx : ρ (spTv hf p₁) * ρ (spTv hf p₁) = 1 := by rw [← map_mul, spTv_mul_self, map_one]
  have hyy : ρ (spTv hf p) * ρ (spTv hf p) = 1 := by rw [← map_mul, spTv_mul_self, map_one]
  have hsup := sup_inf_fixSpace_eq hxx hyy (hU _) (hU _) (by
    rw [hx, hy, eq_bot_iff]
    rintro v ⟨⟨-, hv1⟩, hv2⟩
    have : v ∈ fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)) ⊓
        fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) := ⟨hv2, hv1⟩
    rwa [hinf] at this)
  rw [hx, hy] at hsup
  refine ⟨by rw [sup_comm]; exact hsup, ?_⟩
  rw [eq_bot_iff]
  rintro v ⟨⟨-, hv1⟩, -, hv2⟩
  have : v ∈ fixOf ρ (spPointRadical f p : Set (V ≃ₗ[ZMod 2] V)) ⊓
      fixOf ρ (spPointRadical f p₁ : Set (V ≃ₗ[ZMod 2] V)) := ⟨hv1, hv2⟩
  rwa [hinf] at this

theorem pow_dvd_finrank_of_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) {U : Submodule (ZMod 2) M}
    (hU : ∀ x, ∀ u ∈ U, ρ x u ∈ U) : 2 ^ m ∣ finrank (ZMod 2) U :=
  sp_timmesfeld_2_1_b_dvd ρ hf hnd m (bot_inf_eq _) hm
    (by rw [spPerp_bot, finrank_top]; exact hdim) (fun x _ u hu => hU x u hu)
    (by rw [spPerp_bot]; exact Submodule.mem_top) (by rw [spPerp_bot]; exact Submodule.mem_top)
    hpp₁ (spRadDecomp_of_invariant ρ hf hnd hdim hpp₁ hD hU)

theorem pow_le_finrank_of_invariant (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) {U : Submodule (ZMod 2) M}
    (hU : ∀ x, ∀ u ∈ U, ρ x u ∈ U) (hU0 : U ≠ ⊥) : 2 ^ m ≤ finrank (ZMod 2) U := by
  have h1 := pow_dvd_finrank_of_invariant ρ hf hnd hm hdim hpp₁ hD hU
  have h2 : 0 < finrank (ZMod 2) U :=
    Nat.pos_of_ne_zero fun h => hU0 (Submodule.finrank_eq_zero.mp h)
  exact Nat.le_of_dvd h2 h1

theorem sup_map_sub_one_eq_top (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hpp₁ : f p p₁ = 1)
    (hD : SpRadDecomp ρ ⊥ ⊤ p p₁) :
    (⊤ : Submodule (ZMod 2) M).map ((ρ (spTv hf p) : M →ₗ[ZMod 2] M) - 1) ⊔
      (⊤ : Submodule (ZMod 2) M).map ((ρ (spTv hf p₁) : M →ₗ[ZMod 2] M) - 1) = ⊤ := by
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  rw [(fixSpace_spTv ρ hf hnd hdim hpp₁ hD).2, (fixSpace_spTv ρ hf hnd hdim hp₁p hD.symm).2]
  have h1 := hD.1
  rw [spRadFix_bot, spRadFix_bot, top_inf_eq, top_inf_eq] at h1
  exact h1

end CFSG.LargeExtraspecial.S9
