module

public import CFSG.LargeExtraspecial.S10Conj
public import CFSG.LargeExtraspecial.S10FourI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem map_cK_eq_of_conj_mem {K : Subgroup S.O} {k : S.M}
    (h : ∀ y ∈ K, S.ρ k * y * (S.ρ k)⁻¹ ∈ K) : K.map (cK S k) = K := by
  have hle : K.map (cK S k) ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    rw [cK_apply]
    exact h y hy
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (cK_injective k)]

theorem map_cK_mul_eq {K : Subgroup S.O} {k₁ k₂ : S.M} (h₁ : K.map (cK S k₁) = K)
    (h₂ : K.map (cK S k₂) = K) : K.map (cK S (k₁ * k₂)) = K := by
  have e : cK S (k₁ * k₂) = (cK S k₁).comp (cK S k₂) := by
    ext x
    simp only [cK_apply, MonoidHom.comp_apply, map_mul]
    group
  rw [e, ← Subgroup.map_map, h₂, h₁]

theorem map_cK_one (K : Subgroup S.O) : K.map (cK S 1) = K :=
  map_cK_eq_of_conj_mem fun y hy => by simpa using hy

theorem exists_finrank_three {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (P : V → Prop)
    {x y w : V} (hind : ∀ a b c : ZMod 2, a • x + b • y + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hP : ∀ a b c : ZMod 2, a • x + b • y + c • w ≠ 0 → P (a • x + b • y + c • w)) :
    ∃ U : Submodule (ZMod 2) V, finrank (ZMod 2) U = 3 ∧ ∀ v ∈ U, v ≠ 0 → P v := by
  have hsum : ∀ f : Fin 3 → ZMod 2, ∑ i, f i • ![x, y, w] i = f 0 • x + f 1 • y + f 2 • w := by
    intro f
    rw [Fin.sum_univ_three]
    rfl
  have hli : LinearIndependent (ZMod 2) ![x, y, w] := by
    rw [Fintype.linearIndependent_iff]
    intro f hf i
    rw [hsum] at hf
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ hf
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  refine ⟨Submodule.span (ZMod 2) (Set.range ![x, y, w]), ?_, fun v hv hv0 => ?_⟩
  · rw [finrank_span_eq_card hli, Fintype.card_fin]
  · obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hv
    rw [hsum] at hv0 ⊢
    exact hP _ _ _ hv0

@[expose] def E10 : M2 := !![0, 0; 1, 0]

theorem E10_facts : qf E10 = 0 ∧ qf (E10 + E00) = 0 ∧ pf E00 E10 = 0 ∧ act τ₂ E10 = E10 ∧
    E10 ≠ 0 ∧ E10 + E00 ≠ 0 := by
  decide +kernel

theorem fix_τ₂_sing : ∀ m : M2, act τ₂ m = m → qf m = 0 ∧ qf (m + E00) = 0 := by
  decide +kernel

theorem E10_ne_comb : ∀ γ : Gm, γ.1 = 1 → ∀ a b : ZMod 2, E10 ≠ a • E00 + b • act γ E00 := by
  decide +kernel

theorem eq_of_fix_iff (H : Hyp4 S g) (C : Cons311 S g) {σ τ : S.O} (hσ : σ ∈ S.Lbar g)
    (hτ : τ ∈ S.Lbar g)
    (hfix : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g),
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v ↔ (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) : σ = τ := by
  have haQ := H.conj_mem
  have ha0 : S.cl (g * S.z * g⁻¹) ≠ 0 := fun h => by
    rcases (S.cl_eq_zero_iff haQ).mp h with h1 | h1
    · exact conj_z_ne_one S g h1
    · exact H.conj_ne h1
  have hagree : ∀ v ∈ S.clSub (S.QG ⊓ S.Qa g),
      (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro v hv
    rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' haQ hv hσ) with h1 | h1 <;>
      rcases mem_span_singleton_zmod2.mp (Lbar_apply_sub_mem_span' haQ hv hτ) with h2 | h2
    · rw [sub_eq_zero.mp h1, sub_eq_zero.mp h2]
    · exact absurd ((hfix v hv).mp (sub_eq_zero.mp h1)) (by
        rw [← sub_eq_zero, h2]
        exact ha0)
    · exact absurd ((hfix v hv).mpr (sub_eq_zero.mp h2)) (by
        rw [← sub_eq_zero, h1]
        exact ha0)
    · rw [sub_eq_iff_eq_add.mp h1, sub_eq_iff_eq_add.mp h2]
  have hK : zpowers (σ * τ) ≤ S.Lbar g := zpowers_le.mpr (mul_mem hσ hτ)
  have hfixK : S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S (zpowers (σ * τ)) =
      S.clSub (S.QG ⊓ S.Qa g) ⊓ fixSub S ⊥ := by
    ext v
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨hv, -⟩
      exact ⟨hv, fun x hx => by rw [(mem_bot.mp hx)]; rfl⟩
    · rintro ⟨hv, -⟩
      refine ⟨hv, fun x hx => ?_⟩
      have hst : σ * τ ∈ vecStab S v := by
        rw [mem_vecStab, Subgroup.coe_mul, LinearEquiv.mul_apply, ← hagree v hv]
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, S4.mul_self_of_mem_Lbar S haQ hσ]
        rfl
      exact (mem_vecStab.mp ((zpowers_le.mpr hst) hx))
  have h1 := card_mul_two_pow_finrank_fix H C hK
  have h2 := card_mul_two_pow_finrank_fix H C (bot_le : (⊥ : Subgroup S.O) ≤ S.Lbar g)
  rw [hfixK, ← h2, Subgroup.card_bot, one_mul] at h1
  have hcard : Nat.card (zpowers (σ * τ)) = 1 :=
    (Nat.mul_eq_right (by positivity)).mp h1
  have hone : σ * τ = 1 := by
    have := (Subgroup.card_eq_one.mp hcard)
    have hmem : σ * τ ∈ zpowers (σ * τ) := mem_zpowers _
    rw [this] at hmem
    exact (mem_bot.mp hmem)
  have hσσ := S4.mul_self_of_mem_Lbar S haQ hσ
  calc σ = σ * (σ * τ) := by rw [hone, mul_one]
    _ = τ := by rw [← mul_assoc, hσσ, one_mul]

theorem eq_of_fixSpace_eq (H : Hyp4 S g) (C : Cons311 S g) {σ τ : S.O} (hσ : σ ∈ S.Lbar g)
    (hτ : τ ∈ S.Lbar g)
    (h : fixSpace (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) = fixSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) : σ = τ :=
  eq_of_fix_iff H C hσ hτ fun v _ => by rw [← mem_fixSpace, ← mem_fixSpace, h]

theorem Vt_ne_of_ne (X : Hyp10 S g t) {τ : S.O} (Y : Hyp10 S g τ) (hτt : τ ≠ t) :
    Vt S g τ ≠ Vt S g t := by
  intro hV
  refine hτt (eq_of_fixSpace_eq X.H X.C Y.ht X.ht ?_)
  rw [(commSpace_t_eq X.H X.C X.ht X.ht1 X.hVQ).2, (commSpace_t_eq Y.H Y.C Y.ht Y.ht1 Y.hVQ).2,
    Wt, Wt, hV]

end CFSG.LargeExtraspecial.S10
