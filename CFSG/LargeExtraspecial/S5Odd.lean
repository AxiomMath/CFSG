module

public import CFSG.LargeExtraspecial.S5Gen
public import CFSG.LargeExtraspecial.S4Span
public import CFSG.LargeExtraspecial.S4Weak
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem mem_normalizer_of_commute {x : S.O} (hcomm : ∀ s ∈ S.Lbar g, s * x = x * s) :
    x ∈ normalizer (S.Lbar g : Set S.O) := by
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    rw [← hcomm s hs, mul_inv_cancel_right]
    exact hs
  · intro hs
    have h := hcomm _ hs
    have e : s = x * s * x⁻¹ := by
      calc s = x⁻¹ * (x * s * x⁻¹) * x := by group
        _ = x⁻¹ * (x * (x * s * x⁻¹)) * x⁻¹ * x * x⁻¹ * x := by
          rw [← h]; group
        _ = x * s * x⁻¹ := by group
    rw [e]
    exact hs

theorem card_le_two_of_subset {A : Subgroup S.O} {t : S.O} (h : ∀ x ∈ A, x = 1 ∨ x = t) :
    Nat.card A ≤ 2 := by
  classical
  have hsub : (A : Set S.O) ⊆ {1, t} := fun x hx => h x hx
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_insert_le (1 : S.O) ({t} : Set S.O)
  rw [Set.ncard_singleton] at h2
  rw [← Nat.card_coe_set_eq] at h1
  exact h1.trans h2

theorem eq_one_of_pow_eq_one_of_commute (H : S4.Hyp4 S g) {x : S.O} {m : ℕ} (hm : Odd m)
    (hxm : x ^ m = 1) (hcomm : ∀ s ∈ S.Lbar g, s * x = x * s) : x = 1 := by
  by_contra hx1
  set e : S.Qt ≃ₗ[ZMod 2] S.Qt := (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  set f : S.Qt →ₗ[ZMod 2] S.Qt := (e : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id with hf
  set U : Submodule (ZMod 2) S.Qt := LinearMap.range f with hU
  have hUne : U ≠ ⊥ := by
    intro h0
    apply hx1
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv : f v ∈ U := LinearMap.mem_range_self f v
    rw [h0, Submodule.mem_bot, hf, LinearMap.sub_apply, sub_eq_zero] at hv
    simpa [he] using hv
  have hinv : ∀ s ∈ S.Lbar g, ∀ u ∈ U, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ U := by
    rintro s hs _ ⟨w, rfl⟩
    refine ⟨(s : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
    have hc : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (e w) = e ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w) := by
      have := congrArg (fun y : S.O => (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) (hcomm s hs)
      simpa [he, LinearEquiv.mul_apply] using this
    simp [hf, map_sub, hc]
  obtain ⟨w, hw⟩ := S4.cl_a_mem_of_invariant H hUne hinv
  have hfix : e (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    S4.fix_of_mem_normalizer H (mem_normalizer_of_commute hcomm)
  have hpow : e ^ m = 1 := by
    rw [he, ← Subgroup.coe_pow, hxm]
    rfl
  have hw' : e w - w = S.cl (g * S.z * g⁻¹) := by simpa [hf] using hw
  exact S4.cl_conj_z_ne_zero S H.conj_mem H.conj_ne
    (eq_zero_of_apply_eq_of_sub_eq hm hpow hfix hw')

theorem eq_one_of_mem_of_commute (H : S4.Hyp4 S g) {F : Subgroup S.O}
    (hodd : Odd (Nat.card F)) {x : S.O} (hx : x ∈ F) (hcomm : ∀ s ∈ S.Lbar g, s * x = x * s) :
    x = 1 := by
  refine eq_one_of_pow_eq_one_of_commute H hodd ?_ hcomm
  have := pow_card_eq_one' (G := F) (x := ⟨x, hx⟩)
  exact congrArg Subtype.val this

theorem four_le_card_Lbar (H : S4.Hyp4 S g) (C : S4.Cons311 S g) : 4 ≤ Nat.card (S.Lbar g) := by
  rw [C.card_Lbar]
  have h := H.two_lt_width
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem sixteen_le_card_Lbar (C : S4.Cons311 S g) (hn : 4 < S.width) :
    16 ≤ Nat.card (S.Lbar g) := by
  rw [C.card_Lbar]
  calc 16 = 2 ^ 4 := by norm_num
    _ ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.LargeExtraspecial.S5
