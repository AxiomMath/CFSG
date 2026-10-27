module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.AFive
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isEmpty_mulEquiv_stabilizer (σ : A5 × A5 →* (V ≃ₗ[ZMod 2] V))
    (VA W : Submodule (ZMod 2) V) (hc : IsCompl VA W) (h4A : finrank (ZMod 2) VA = 4)
    (h4W : finrank (ZMod 2) W = 4)
    (hVA : ∀ g : A5 × A5, ∀ u ∈ VA, σ g u ∈ VA) (hW : ∀ g : A5 × A5, ∀ u ∈ W, σ g u ∈ W)
    (hB : ∀ y : A5, ∀ u ∈ VA, σ (1, y) u = u) (hA : ∀ x : A5, ∀ u ∈ W, σ (x, 1) u = u)
    (v : V) (S : Subgroup (A5 × A5)) (hS : ∀ g, g ∈ S ↔ σ g v = v) : IsEmpty (S ≃* A5) := by
  classical
  have hv : v ∈ VA ⊔ W := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨vA, hvA, w, hw, hvw⟩ := Submodule.mem_sup.mp hv
  have hmemA : ∀ x : A5, (x, 1) ∈ S ↔ σ (x, 1) vA = vA := by
    intro x
    rw [hS]
    have h1 : σ (x, 1) v = σ (x, 1) vA + w := by
      rw [← hvw, map_add, hA x w hw]
    rw [h1, ← hvw]
    exact add_right_cancel_iff
  have hmemB : ∀ y : A5, (1, y) ∈ S ↔ σ (1, y) w = w := by
    intro y
    rw [hS]
    have h1 : σ (1, y) v = vA + σ (1, y) w := by
      rw [← hvw, map_add, hB y vA hvA]
    rw [h1, ← hvw]
    exact add_left_cancel_iff
  have hcardA5 : Nat.card A5 = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
    decide
  have hcardVA : Nat.card VA = 16 := by
    haveI : Fintype VA := Fintype.ofFinite VA
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), h4A, ZMod.card]
    norm_num
  have hcardW : Nat.card W = 16 := by
    haveI : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), h4W, ZMod.card]
    norm_num
  let fA : A5 → VA := fun x => ⟨σ (x, 1) vA, hVA (x, 1) vA hvA⟩
  have hnotInjA : ¬ Function.Injective fA := by
    intro hinj
    have hle : Nat.card A5 ≤ Nat.card VA := Nat.card_le_card_of_injective fA hinj
    rw [hcardA5, hcardVA] at hle
    omega
  obtain ⟨x, x', hfxx', hxx'⟩ := Function.not_injective_iff.mp hnotInjA
  have heqA : σ (x, 1) vA = σ (x', 1) vA := by
    change (fA x : V) = (fA x' : V)
    exact congrArg (fun y : VA => (y : V)) hfxx'
  let x₀ : A5 := x'⁻¹ * x
  have hx0ne : x₀ ≠ 1 := fun h => hxx' (inv_mul_eq_one.mp h).symm
  have hfixA : σ (x₀, 1) vA = vA := by
    have hpair : (x₀, (1 : A5)) = (x', (1 : A5))⁻¹ * (x, (1 : A5)) := by
      rw [Prod.inv_mk, Prod.mk_mul_mk]
      simp only [x₀, inv_one, one_mul]
    calc σ (x₀, 1) vA = σ ((x', (1 : A5))⁻¹ * (x, (1 : A5))) vA := by rw [hpair]
      _ = (σ ((x', 1)⁻¹) * σ (x, 1)) vA := by rw [map_mul]
      _ = σ ((x', 1)⁻¹) (σ (x, 1) vA) := rfl
      _ = (σ (x', 1))⁻¹ (σ (x, 1) vA) := by rw [map_inv]
      _ = (σ (x', 1))⁻¹ (σ (x', 1) vA) := by rw [heqA]
      _ = vA := by simp
  have hx0S : (x₀, 1) ∈ S := (hmemA x₀).mpr hfixA
  let fB : A5 → W := fun y => ⟨σ (1, y) w, hW (1, y) w hw⟩
  have hnotInjB : ¬ Function.Injective fB := by
    intro hinj
    have hle : Nat.card A5 ≤ Nat.card W := Nat.card_le_card_of_injective fB hinj
    rw [hcardA5, hcardW] at hle
    omega
  obtain ⟨y, y', hfyy', hyy'⟩ := Function.not_injective_iff.mp hnotInjB
  have heqB : σ (1, y) w = σ (1, y') w := by
    change (fB y : V) = (fB y' : V)
    exact congrArg (fun z : W => (z : V)) hfyy'
  let y₀ : A5 := y'⁻¹ * y
  have hy0ne : y₀ ≠ 1 := fun h => hyy' (inv_mul_eq_one.mp h).symm
  have hfixB : σ (1, y₀) w = w := by
    have hpair : ((1 : A5), y₀) = ((1 : A5), y')⁻¹ * ((1 : A5), y) := by
      rw [Prod.inv_mk, Prod.mk_mul_mk]
      simp only [y₀, inv_one, one_mul]
    calc σ (1, y₀) w = σ (((1 : A5), y')⁻¹ * ((1 : A5), y)) w := by rw [hpair]
      _ = (σ ((1, y')⁻¹) * σ (1, y)) w := by rw [map_mul]
      _ = σ ((1, y')⁻¹) (σ (1, y) w) := rfl
      _ = (σ (1, y'))⁻¹ (σ (1, y) w) := by rw [map_inv]
      _ = (σ (1, y'))⁻¹ (σ (1, y') w) := by rw [heqB]
      _ = w := by simp
  have hy0S : (1, y₀) ∈ S := (hmemB y₀).mpr hfixB
  refine ⟨fun e => ?_⟩
  haveI : IsSimpleGroup S := e.isSimpleGroup
  let K₁ : Subgroup S := MonoidHom.ker ((MonoidHom.snd A5 A5).comp S.subtype)
  let K₂ : Subgroup S := MonoidHom.ker ((MonoidHom.fst A5 A5).comp S.subtype)
  have hx0K1 : (⟨(x₀, 1), hx0S⟩ : S) ∈ K₁ := by
    change ((MonoidHom.snd A5 A5).comp S.subtype) ⟨(x₀, 1), hx0S⟩ = 1
    rfl
  have hy0K2 : (⟨(1, y₀), hy0S⟩ : S) ∈ K₂ := by
    change ((MonoidHom.fst A5 A5).comp S.subtype) ⟨(1, y₀), hy0S⟩ = 1
    rfl
  have hK12 : K₁ ⊓ K₂ = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    obtain ⟨hs1, hs2⟩ := Subgroup.mem_inf.mp hs
    apply Subtype.ext
    have h1 : (s : A5 × A5).1 = 1 := by
      change ((MonoidHom.fst A5 A5).comp S.subtype) s = 1 at hs2
      exact hs2
    have h2 : (s : A5 × A5).2 = 1 := by
      change ((MonoidHom.snd A5 A5).comp S.subtype) s = 1 at hs1
      exact hs1
    exact Prod.ext h1 h2
  have hK1ne : K₁ ≠ ⊥ := by
    intro hbot
    have hmem : (⟨(x₀, 1), hx0S⟩ : S) ∈ (⊥ : Subgroup S) := hbot ▸ hx0K1
    have hone : (⟨(x₀, 1), hx0S⟩ : S) = 1 := Subgroup.mem_bot.mp hmem
    have hpair : (x₀, 1) = (1 : A5 × A5) := congrArg (fun s : S => (s : A5 × A5)) hone
    exact hx0ne (by simpa using hpair)
  have hK1neTop : K₁ ≠ ⊤ := by
    intro htop
    have hK2bot : K₂ = ⊥ := by simpa [htop] using hK12
    have hmem : (⟨(1, y₀), hy0S⟩ : S) ∈ (⊥ : Subgroup S) := hK2bot ▸ hy0K2
    have hone : (⟨(1, y₀), hy0S⟩ : S) = 1 := Subgroup.mem_bot.mp hmem
    have hpair : (1, y₀) = (1 : A5 × A5) := congrArg (fun s : S => (s : A5 × A5)) hone
    exact hy0ne (by simpa using hpair)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K₁ with h | h
  · exact hK1ne h
  · exact hK1neTop h

end CFSG.EvenSporadicStandard.HNRecog.Fpf
