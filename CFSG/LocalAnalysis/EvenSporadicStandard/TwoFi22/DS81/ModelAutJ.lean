module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueCP
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFC
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueGlue

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup FrameJ CFSG.Sporadic.Fi22 CFSG.Monster.B.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem mem_map_conj_iff {G : Type*} [Group G] (K : Subgroup G) (g y : G) :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem map_conj_map {G : Type*} [Group G] (K : Subgroup G) (g h : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      K.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_transport {G H : Type*} [Group G] [Group H] (e : H ≃* G)
    (hG : ∀ W₁ W₂ : Subgroup G, (∀ w ∈ W₁, w ^ 2 = 1) → Nat.card W₁ = 2 ^ 10 →
      (∀ w ∈ W₂, w ^ 2 = 1) → Nat.card W₂ = 2 ^ 10 →
        ∃ g : G, W₁ = W₂.map (MulAut.conj g).toMonoidHom)
    (V₁ V₂ : Subgroup H) (h₁ : ∀ v ∈ V₁, v ^ 2 = 1) (c₁ : Nat.card V₁ = 2 ^ 10)
    (h₂ : ∀ v ∈ V₂, v ^ 2 = 1) (c₂ : Nat.card V₂ = 2 ^ 10) :
    ∃ h : H, V₁ = V₂.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨g, hg⟩ := hG (V₁.map e.toMonoidHom) (V₂.map e.toMonoidHom)
    (UniqueGlue.sq_eq_one_of_mem_map e.toMonoidHom V₁ h₁)
    (by rw [Subgroup.card_map_of_injective e.injective, c₁])
    (UniqueGlue.sq_eq_one_of_mem_map e.toMonoidHom V₂ h₂)
    (by rw [Subgroup.card_map_of_injective e.injective, c₂])
  refine ⟨e.symm g, ?_⟩
  ext x
  have e1 : x ∈ V₁ ↔ e x ∈ V₁.map e.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [e1, hg, mem_map_conj_iff, mem_map_conj_iff, Subgroup.mem_map_equiv]
  simp

section J


theorem card_closure_D_slvl :
    Nat.card (Subgroup.closure {x : J | x ∈ D ∧ x ∈ slvl 0}) = 2 ^ 10 := by
  obtain ⟨g, hg⟩ := UniqueGlue.exists_conj_sup_mem_slvl_zero (E := E0.map piC) (B := ⊥)
    (UniqueGlue.sq_eq_one_of_mem_map piC E0 E0_sq)
    (fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]) bot_le
  have hgE : ∀ x ∈ E0.map piC, g * x * g⁻¹ ∈ slvl 0 := fun x hx =>
    hg x (Subgroup.mem_sup_left hx)
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hcl := UniqueGlue.closure_D_slvl_eq hgE
  rw [hcl, Subgroup.card_map_of_injective hinj, UniqueGlue.card_map_piC_E0]


theorem J_unique (V : Subgroup J) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hVcard : Nat.card V = 2 ^ 10) :
    ∃ g : J, V = (Subgroup.closure {x : J | x ∈ D ∧ x ∈ slvl 0}).map
      (MulAut.conj g).toMonoidHom := by
  have hcard := card_closure_D_slvl
  have hsyl : Nat.card (slvl 0) = 2 ^ (Nat.card J).factorization 2 := by
    rw [card_slvl_zero, card_J, show (64561751654400 : ℕ) = 2 ^ 17 * 492567075 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  exact AutConj.exists_conj_eq_of_unique hV2 hVcard (Sylow.ofCard (slvl 0) hsyl) rfl
    (fun A hA hsq hc => cp_of_fc fcSpec_data hA hsq hc hcard) hcard

theorem J_conj (V₁ V₂ : Subgroup J) (h₁ : ∀ v ∈ V₁, v ^ 2 = 1) (c₁ : Nat.card V₁ = 2 ^ 10)
    (h₂ : ∀ v ∈ V₂, v ^ 2 = 1) (c₂ : Nat.card V₂ = 2 ^ 10) :
    ∃ g : J, V₁ = V₂.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g₁, hg₁⟩ := J_unique V₁ h₁ c₁
  obtain ⟨g₀, hg₀⟩ := J_unique V₂ h₂ c₂
  refine ⟨g₁ * g₀⁻¹, ?_⟩
  have e : g₁ * g₀⁻¹ * g₀ = g₁ := inv_mul_cancel_right g₁ g₀
  rw [hg₁, hg₀, map_conj_map, e]


theorem exists_conj_P (V₁ V₂ : Subgroup fi22P) (h₁ : ∀ v ∈ V₁, v ^ 2 = 1)
    (c₁ : Nat.card V₁ = 2 ^ 10) (h₂ : ∀ v ∈ V₂, v ^ 2 = 1) (c₂ : Nat.card V₂ = 2 ^ 10) :
    ∃ g : fi22P, V₁ = V₂.map (MulAut.conj g).toMonoidHom := by
  have step1 := exists_conj_transport (G := J) (H := fi22P) fiJP.symm
  refine step1 ?_ V₁ V₂ h₁ c₁ h₂ c₂
  intro W₁ W₂ a b c d
  exact J_conj W₁ W₂ a b c d

end J

end CFSG.EvenSporadicStandard.TwoFi22.DS81
