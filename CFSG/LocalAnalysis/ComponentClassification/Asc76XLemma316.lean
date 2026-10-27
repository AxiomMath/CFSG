module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76XLemma315

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_two {W Z : Subgroup G} {w : G} (hw : w ∈ W)
    (h : ∀ x ∈ W, x ∈ Z ∨ w * x ∈ Z) : Z.relIndex W ≤ 2 := by
  have hsub : (W : Set G) ⊆ ((Z ⊓ W : Subgroup G) : Set G) ∪
      (fun x => w⁻¹ * x) '' ((Z ⊓ W : Subgroup G) : Set G) := by
    intro x hx
    rcases h x hx with hxZ | hxZ
    · exact Or.inl ⟨hxZ, hx⟩
    · exact Or.inr ⟨w * x, ⟨hxZ, mul_mem hw hx⟩, by simp⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le ((Z ⊓ W : Subgroup G) : Set G)
    ((fun x => w⁻¹ * x) '' ((Z ⊓ W : Subgroup G) : Set G))
  have h3 : ((fun x => w⁻¹ * x) '' ((Z ⊓ W : Subgroup G) : Set G)).ncard =
      ((Z ⊓ W : Subgroup G) : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_right_injective w⁻¹)
  have hW : Nat.card W = (W : Set G).ncard := rfl
  have hZW : Nat.card (Z ⊓ W : Subgroup G) = ((Z ⊓ W : Subgroup G) : Set G).ncard := rfl
  have hmul := Subgroup.relIndex_mul_card Z W
  have hpos : 0 < Nat.card (Z ⊓ W : Subgroup G) := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have h4 : 3 * Nat.card (Z ⊓ W : Subgroup G) ≤ Nat.card W := by
    rw [← hmul]
    exact Nat.mul_le_mul_right _ hlt
  omega

namespace Config

variable {Ω : Set (Subgroup G)} {K J R T S : Subgroup G}

theorem lemma316 (hc : Config Ω K J R T S) (hM : MinCounter Ω) (hI : Sec3Inputs)
    (hesc : GoldschmidtEscape) :
    ∀ z ∈ omega1 R ⊔ omega1 T, ∀ g : G, g⁻¹ * z * g ∈ S →
      g⁻¹ * z * g ∈ omega1 R ⊔ omega1 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.setting
  set Z := omega1 R ⊔ omega1 T with hZdef
  have hZab := hc.isElemAbelian_Z hM hI
  obtain ⟨-, h315⟩ := hc.lemma315 hM hI
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, g, hgS, hgZ⟩ := hcon
  obtain ⟨U, hUZ, h, hWS, hWZ, hW⟩ := hesc G S Z hc.sylowS hc.Z_le hZab
    (fun g hg => hc.weaklyClosed hM hI hg) ⟨z, hz, g, hgS, hgZ⟩
  have hWinv : ∀ w ∈ rightConjugate U h, w ∈ S ∧ w ^ 2 = 1 ∧ ∃ h' : G, h'⁻¹ * w * h' ∈ Z := by
    intro w hw
    have hw' : h * w * h⁻¹ ∈ U := (mem_rightConjugate_iff U h w).mp hw
    refine ⟨hWS hw, ?_, h⁻¹, by simpa using hUZ hw'⟩
    have h1 := hZab.2 _ (hUZ hw')
    rw [conj_pow] at h1
    have e : h⁻¹ * (h * w ^ 2 * h⁻¹) * h = w ^ 2 := by group
    rw [← e, h1]
    group
  have hRw : ∀ w ∈ rightConjugate U h, w ∉ Z → rightConjugate R w = T := fun w hw hwZ => by
    obtain ⟨hwS, hw2, hfus⟩ := hWinv w hw
    exact h315 w hwS hwZ hw2 hfus
  obtain ⟨w₁, hw₁, hw₁Z⟩ : ∃ w ∈ rightConjugate U h, w ∉ Z := by
    by_contra hne
    push Not at hne
    exact hWZ hne
  have h4 : 4 ≤ Nat.card (⁅Z, zpowers w₁⁆ : Subgroup G) := by
    obtain ⟨E, hER, hE, hE4⟩ := exists_fourGroup_le (hΩ.rank K hc.mem R hc.sylowR).1
    have hEZ : E ≤ Z := fun e he => mem_sup_left (mem_omega1_of_sq (hER he) (hE.2 e he))
    have hww : w₁ * w₁ = 1 := by rw [← sq]; exact (hWinv w₁ hw₁).2.1
    have hRw₁ := hRw w₁ hw₁ hw₁Z
    have hRT : ∀ e ∈ R, w₁ * e * w₁⁻¹ ∈ T := fun e he => by
      rw [← hRw₁, mem_rightConjugate_iff]
      have e' : w₁ * (w₁ * e * w₁⁻¹) * w₁⁻¹ = e := by
        calc w₁ * (w₁ * e * w₁⁻¹) * w₁⁻¹ = (w₁ * w₁) * e * (w₁ * w₁)⁻¹ := by group
          _ = e := by rw [hww, one_mul, inv_one, mul_one]
      rw [e']
      exact he
    let f : E → (⁅Z, zpowers w₁⁆ : Subgroup G) := fun e =>
      ⟨⁅(e : G), w₁⁆, commutator_mem_commutator (hEZ e.2) (mem_zpowers w₁)⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h1 : ⁅(a : G), w₁⁆ = ⁅(b : G), w₁⁆ := congrArg Subtype.val hab
      rw [commutatorElement_def, commutatorElement_def] at h1
      have h2 : (a : G) * w₁ * (a : G)⁻¹ = b * w₁ * (b : G)⁻¹ := mul_right_cancel h1
      have hcomm : (b : G)⁻¹ * a * w₁ = w₁ * ((b : G)⁻¹ * a) := by
        calc (b : G)⁻¹ * a * w₁ = (b : G)⁻¹ * ((a : G) * w₁ * (a : G)⁻¹) * a := by group
          _ = (b : G)⁻¹ * (b * w₁ * (b : G)⁻¹) * a := by rw [h2]
          _ = w₁ * ((b : G)⁻¹ * a) := by group
      have hbaR : (b : G)⁻¹ * a ∈ R := mul_mem (inv_mem (hER b.2)) (hER a.2)
      have hbaT : (b : G)⁻¹ * a ∈ T := by
        have e : (b : G)⁻¹ * a = w₁ * ((b : G)⁻¹ * a) * w₁⁻¹ := by
          rw [← hcomm]
          group
        rw [e]
        exact hRT _ hbaR
      have hba : (b : G)⁻¹ * a ∈ R ⊓ T := mem_inf.mpr ⟨hbaR, hbaT⟩
      rw [hc.inf_RT hΩ, mem_bot] at hba
      apply Subtype.ext
      calc (a : G) = b * ((b : G)⁻¹ * a) := by group
        _ = b := by rw [hba, mul_one]
    have hcard := Nat.card_le_card_of_injective f hf
    rwa [hE4] at hcard
  have hidx : 4 ≤ Z.relIndex (rightConjugate U h) := h4.trans (hW w₁ hw₁)
  obtain ⟨w₂, hw₂, hw₂Z, hw₁₂Z⟩ : ∃ w₂ ∈ rightConjugate U h, w₂ ∉ Z ∧ w₁ * w₂ ∉ Z := by
    by_contra hne
    push Not at hne
    have h2 := relIndex_le_two (Z := Z) hw₁ fun x hx => by
      by_cases hxZ : x ∈ Z
      · exact Or.inl hxZ
      · exact Or.inr (hne x hx hxZ)
    omega
  have hw₂2 := (hWinv w₂ hw₂).2.1
  have e₁ := hRw w₁ hw₁ hw₁Z
  have e₂ := hRw w₂ hw₂ hw₂Z
  have e₁₂ := hRw (w₁ * w₂) (mul_mem hw₁ hw₂) hw₁₂Z
  have hTw₂ : rightConjugate T w₂ = R := by
    rw [← e₂, rightConjugate_mul, ← sq, hw₂2, rightConjugate_one]
  apply hc.R_ne_T hΩ
  rw [← e₁₂, ← rightConjugate_mul, e₁, hTw₂]

end Config

end CFSG.ComponentClassification.Asc76X
