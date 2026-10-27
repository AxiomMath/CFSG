module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6QA
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6PGrp

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Fischer
open scoped MatrixGroups

section One

variable {V Γ : Type*} [Group V] [Finite V] [Group Γ] [Finite Γ]

theorem one_sided (ρ : Γ →* MulAut V) (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1)
    {Γ₁ Γ₂ U₁ : Subgroup Γ} (e₁ : ↥Γ₁ ≃* SL(2, F4))
    (hcommΓ : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a) (hU₁ : U₁ ≤ Γ₁)
    (hlow : ∀ (g : Γ) (hg : g ∈ U₁),
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hnt : ∃ (g : Γ) (hg : g ∈ U₁), e₁ ⟨g, hU₁ hg⟩ ≠ 1)
    (hZcard : Nat.card (ModSplit.fixSub ρ Γ₂) = 2 ^ 4)
    (hZfix : ModSplit.fixSub ρ Γ₂ ⊓ ModSplit.fixSub ρ Γ₁ = ⊥) :
    Nat.card ↥(ModSplit.fixSub ρ Γ₂ ⊓ ModSplit.fixSub ρ U₁) ≤ 4 ∧
      (Nat.card ↥(ModSplit.fixSub ρ Γ₂ ⊓ ModSplit.fixSub ρ U₁) = 4 →
        (∀ u ∈ U₁, ∀ v ∈ ModSplit.fixSub ρ Γ₂,
          ρ u v * v⁻¹ ∈ ModSplit.fixSub ρ Γ₂ ⊓ ModSplit.fixSub ρ U₁) ∧
        (∀ c ∈ ModSplit.fixSub ρ Γ₂ ⊓ ModSplit.fixSub ρ U₁, ∃ u ∈ U₁,
          ∃ v ∈ ModSplit.fixSub ρ Γ₂, c = ρ u v * v⁻¹)) := by
  set Z := ModSplit.fixSub ρ Γ₂ with hZ
  have hZinv : ∀ g ∈ Γ₁, ∀ z ∈ Z, ρ g z ∈ Z := fun g hg z hz =>
    ModSplit.ρ_mem_fixSub_of_comm ρ (fun s hs => (hcommΓ g hg s hs).symm) hz
  set ρ₁ : ↥Γ₁ →* MulAut ↥Z := ModSplit.restrictAct ρ Γ₁ Z hZinv with hρ₁
  have hρ₁apply : ∀ (g : ↥Γ₁) (z : ↥Z), ((ρ₁ g z : ↥Z) : V) = ρ (g : Γ) (z : V) :=
    fun g z => ModSplit.restrictAct_apply ρ Γ₁ Z hZinv g z
  have hWc : ∀ a b : ↥Z, a * b = b * a := fun a b => Subtype.ext (hc a b)
  have hW2 : ∀ w : ↥Z, w * w = 1 := fun w => Subtype.ext (hV w)
  have hWcard : Nat.card ↥Z = 2 ^ 4 := hZcard
  have hfixW : ∀ w : ↥Z, (∀ g : ↥Γ₁, ρ₁ g w = w) → w = 1 := by
    intro w hw
    have h1 : (w : V) ∈ ModSplit.fixSub ρ Γ₁ := fun g hg => by
      have := congrArg Subtype.val (hw ⟨g, hg⟩)
      rwa [hρ₁apply] at this
    have h2 : (w : V) ∈ Z ⊓ ModSplit.fixSub ρ Γ₁ := ⟨w.2, h1⟩
    rw [hZfix] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  set U : Subgroup ↥Γ₁ := U₁.subgroupOf Γ₁ with hUdef
  have hU : ∀ g ∈ U, (e₁ g : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₁ g : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧ (e₁ g : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1 :=
    fun g hg => hlow (g : Γ) (Subgroup.mem_subgroupOf.1 hg)
  have hmap : (ModSplit.fixSub ρ₁ U).map Z.subtype = Z ⊓ ModSplit.fixSub ρ U₁ := by
    ext v
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun u hu => ?_⟩
      have := congrArg Subtype.val (hz ⟨u, hU₁ hu⟩ (Subgroup.mem_subgroupOf.2 hu))
      rwa [hρ₁apply] at this
    · rintro ⟨hvZ, hvU⟩
      refine ⟨⟨v, hvZ⟩, fun g hg => Subtype.ext ?_, rfl⟩
      rw [hρ₁apply]
      exact hvU (g : Γ) (Subgroup.mem_subgroupOf.1 hg)
  have hcardC : Nat.card ↥(Z ⊓ ModSplit.fixSub ρ U₁) = Nat.card ↥(ModSplit.fixSub ρ₁ U) := by
    rw [← hmap, Subgroup.card_map_of_injective Z.subtype_injective]
  obtain ⟨g₀, hg₀, hg₀1⟩ := hnt
  have hu₀ : (⟨g₀, hU₁ hg₀⟩ : ↥Γ₁) ∈ U := Subgroup.mem_subgroupOf.2 hg₀
  refine ⟨?_, fun h4 => ?_⟩
  · rw [hcardC]
    exact card_fixSub_le_four hWc hW2 hWcard ρ₁ e₁ hfixW hU hu₀ hg₀1
  have hCU : Nat.card ↥(ModSplit.fixSub ρ₁ U) = 4 := by rw [← hcardC]; exact h4
  refine ⟨fun u hu v hv => ?_, fun c hc' => ?_⟩
  · have := comm1_mem_fixSub hWc hW2 hWcard ρ₁ e₁ hfixW hU hCU
      (u := ⟨u, hU₁ hu⟩) (Subgroup.mem_subgroupOf.2 hu) ⟨v, hv⟩
    have hmem : ((comm1 hWc ρ₁ ⟨u, hU₁ hu⟩ ⟨v, hv⟩ : ↥Z) : V) ∈ Z ⊓ ModSplit.fixSub ρ U₁ := by
      rw [← hmap]
      exact ⟨_, this, rfl⟩
    have e1 : ((comm1 hWc ρ₁ ⟨u, hU₁ hu⟩ ⟨v, hv⟩ : ↥Z) : V) = ρ u v * v⁻¹ := by
      rw [comm1_apply hWc, Subgroup.coe_mul, hρ₁apply]
      rfl
    rwa [e1] at hmem
  · rw [← hmap] at hc'
    obtain ⟨z, hz, rfl⟩ := hc'
    have hr := range_comm1_eq_fixSub hWc hW2 hWcard ρ₁ e₁ hfixW hU hCU hu₀ hg₀1
    rw [← hr] at hz
    obtain ⟨v', hv'⟩ := hz
    refine ⟨g₀, hg₀, v', v'.2, ?_⟩
    have := congrArg Subtype.val hv'
    rw [comm1_apply hWc, Subgroup.coe_mul, hρ₁apply] at this
    exact this.symm

end One

section Two

variable {V Γ : Type*} [Group V] [Finite V] [Group Γ] [Finite Γ]

theorem quad_gen_of_split (ρ : Γ →* MulAut V) (hc : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) {Γ₁ Γ₂ U₁ U₂ : Subgroup Γ} (e₁ : ↥Γ₁ ≃* SL(2, F4))
    (e₂ : ↥Γ₂ ≃* SL(2, F4)) (hcommΓ : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a)
    (hU₁ : U₁ ≤ Γ₁) (hU₂ : U₂ ≤ Γ₂)
    (hlow₁ : ∀ (g : Γ) (hg : g ∈ U₁),
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (e₁ ⟨g, hU₁ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hlow₂ : ∀ (g : Γ) (hg : g ∈ U₂),
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧
      (e₂ ⟨g, hU₂ hg⟩ : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hnt₁ : ∃ (g : Γ) (hg : g ∈ U₁), e₁ ⟨g, hU₁ hg⟩ ≠ 1)
    (hnt₂ : ∃ (g : Γ) (hg : g ∈ U₂), e₂ ⟨g, hU₂ hg⟩ ≠ 1)
    (hV₁card : Nat.card (ModSplit.fixSub ρ Γ₁) = 2 ^ 4)
    (hV₂card : Nat.card (ModSplit.fixSub ρ Γ₂) = 2 ^ 4)
    (hsup : ModSplit.fixSub ρ Γ₁ ⊔ ModSplit.fixSub ρ Γ₂ = ⊤)
    (hinf : ModSplit.fixSub ρ Γ₁ ⊓ ModSplit.fixSub ρ Γ₂ = ⊥)
    (hplus : Nat.card (ModSplit.fixSub ρ (U₁ ⊔ U₂)) = 2 ^ 4) :
    (∀ u ∈ U₁, ∀ v : V, ρ u v * v⁻¹ ∈ ModSplit.fixSub ρ (U₁ ⊔ U₂)) ∧
      (∀ u ∈ U₂, ∀ v : V, ρ u v * v⁻¹ ∈ ModSplit.fixSub ρ (U₁ ⊔ U₂)) ∧
      (∀ c ∈ ModSplit.fixSub ρ (U₁ ⊔ U₂), ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, ∃ v₁ v₂ : V,
        c = (ρ u₁ v₁ * v₁⁻¹) * (ρ u₂ v₂ * v₂⁻¹)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V₁ := ModSplit.fixSub ρ Γ₁ with hV₁
  set V₂ := ModSplit.fixSub ρ Γ₂ with hV₂
  have hnorm : ∀ A B : Subgroup V, A ≤ normalizer (B : Set V) := fun A B a _ =>
    mem_normalizer_iff.2 fun h => by
      rw [hc a h, mul_assoc, mul_inv_cancel, mul_one]
  have hcommΓ' : ∀ a ∈ Γ₂, ∀ b ∈ Γ₁, a * b = b * a := fun a ha b hb => (hcommΓ b hb a ha).symm
  obtain ⟨hC₂le, hC₂⟩ := one_sided ρ hc hV e₁ hcommΓ hU₁ hlow₁ hnt₁ hV₂card (by rw [inf_comm, hinf])
  obtain ⟨hC₁le, hC₁⟩ := one_sided ρ hc hV e₂ hcommΓ' hU₂ hlow₂ hnt₂ hV₁card (by rw [hinf])
  set C₁ := V₁ ⊓ ModSplit.fixSub ρ U₂ with hC₁def
  set C₂ := V₂ ⊓ ModSplit.fixSub ρ U₁ with hC₂def
  have hCinf : C₁ ⊓ C₂ = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have : x ∈ V₁ ⊓ V₂ := ⟨hx.1.1, hx.2.1⟩
    rw [hinf] at this
    exact this
  have hplusEq : ModSplit.fixSub ρ (U₁ ⊔ U₂) = C₁ ⊔ C₂ := by
    apply le_antisymm
    · intro v hv
      rw [ModSplit.fixSub_sup] at hv
      obtain ⟨hv1, hv2⟩ := hv
      have hvtop : v ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
        (hnorm V₁ V₂) hvtop
      have h1 : ∀ u ∈ U₁, ρ u v₂ = v₂ := fun u hu => by
        have := hv1 u hu
        rw [map_mul, hv₁ u (hU₁ hu)] at this
        exact mul_left_cancel this
      have h2 : ∀ u ∈ U₂, ρ u v₁ = v₁ := fun u hu => by
        have := hv2 u hu
        rw [map_mul, hv₂ u (hU₂ hu)] at this
        exact mul_right_cancel this
      exact Subgroup.mul_mem _ (mem_sup_left ⟨hv₁, h2⟩) (mem_sup_right ⟨hv₂, h1⟩)
    · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [ModSplit.fixSub_sup]
        refine ⟨fun u hu => hx.1 u (hU₁ hu) |>.trans rfl |> fun h => ?_, hx.2⟩
        exact hx.1 u (hU₁ hu)
      · rw [ModSplit.fixSub_sup]
        exact ⟨hx.2, fun u hu => hx.1 u (hU₂ hu)⟩
  have hcard := PGrp.card_sup_mul_card_inf (hnorm C₁ C₂)
  rw [hCinf, Subgroup.card_bot, mul_one, ← hplusEq, hplus] at hcard
  have hc1 : Nat.card ↥C₁ = 4 ∧ Nat.card ↥C₂ = 4 := by
    have h1 := hC₁le
    have h2 := hC₂le
    have hpos1 : 0 < Nat.card ↥C₁ := Nat.card_pos
    have hpos2 : 0 < Nat.card ↥C₂ := Nat.card_pos
    constructor <;> nlinarith
  obtain ⟨hQ₂a, hQ₂b⟩ := hC₂ hc1.2
  obtain ⟨hQ₁a, hQ₁b⟩ := hC₁ hc1.1
  have hC₂V : C₂ ≤ ModSplit.fixSub ρ (U₁ ⊔ U₂) := hplusEq ▸ le_sup_right
  have hC₁V : C₁ ≤ ModSplit.fixSub ρ (U₁ ⊔ U₂) := hplusEq ▸ le_sup_left
  refine ⟨fun u hu v => ?_, fun u hu v => ?_, fun c hcc => ?_⟩
  · have hvtop : v ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
      (hnorm V₁ V₂) hvtop
    have e1 : ρ u (v₁ * v₂) * (v₁ * v₂)⁻¹ = ρ u v₂ * v₂⁻¹ := by
      rw [map_mul, hv₁ u (hU₁ hu), _root_.mul_inv_rev]
      have := hc (ρ u v₂) v₁
      calc v₁ * ρ u v₂ * (v₂⁻¹ * v₁⁻¹) = v₁ * (ρ u v₂ * v₂⁻¹) * v₁⁻¹ := by group
        _ = (ρ u v₂ * v₂⁻¹) * v₁ * v₁⁻¹ := by rw [hc v₁ (ρ u v₂ * v₂⁻¹)]
        _ = ρ u v₂ * v₂⁻¹ := by group
    rw [e1]
    exact hC₂V (hQ₂a u hu v₂ hv₂)
  · have hvtop : v ∈ V₁ ⊔ V₂ := by rw [hsup]; trivial
    obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
      (hnorm V₁ V₂) hvtop
    have e1 : ρ u (v₁ * v₂) * (v₁ * v₂)⁻¹ = ρ u v₁ * v₁⁻¹ := by
      rw [map_mul, hv₂ u (hU₂ hu), _root_.mul_inv_rev]
      calc ρ u v₁ * v₂ * (v₂⁻¹ * v₁⁻¹) = ρ u v₁ * (v₂ * v₂⁻¹) * v₁⁻¹ := by group
        _ = ρ u v₁ * v₁⁻¹ := by group
    rw [e1]
    exact hC₁V (hQ₁a u hu v₁ hv₁)
  · rw [hplusEq] at hcc
    obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := PGrp.exists_mul_of_mem_sup_of_le_normalizer
      (hnorm C₁ C₂) hcc
    obtain ⟨u₂, hu₂, v₁, hv₁, hcv₁⟩ := hQ₁b c₁ hc₁
    obtain ⟨u₁, hu₁, v₂, hv₂, hcv₂⟩ := hQ₂b c₂ hc₂
    exact ⟨u₁, hu₁, u₂, hu₂, v₂, v₁, by rw [hcv₁, hcv₂, hc]⟩

end Two


end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
