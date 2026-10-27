module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.FusionInterface
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

theorem mem_conjSub {g x : G} {A : Subgroup G} : x ∈ conjSub g A ↔ g⁻¹ * x * g ∈ A := by
  unfold conjSub
  rw [mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem card_conjSub (g : G) (A : Subgroup G) : Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem conjSub_conjSub_inv (g : G) (A : Subgroup G) : conjSub g (conjSub g⁻¹ A) = A := by
  ext x
  rw [mem_conjSub, mem_conjSub]
  simp [mul_assoc]

theorem isSylowOf_T0 [Finite G] (hD : LocalData L U T0) : IsSylowOf 2 T0 L := by
  have := Fact.mk Nat.prime_two
  exact isSylowOf_iff.2 ⟨hD.T0_le_L, hD.T0_pGroup, hD.T0_index_odd⟩

theorem isPGroup_of_sq {A : Subgroup G} (h : ∀ a ∈ A, a * a = 1) : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  have := h a a.2
  simpa [pow_two] using this

theorem exists_conj_eq_U [Finite G] (hD : LocalData L U T0) {A : Subgroup G} (hAL : A ≤ L)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : 2 ^ 11 ≤ Nat.card A) : ∃ l ∈ L, A = conjSub l U := by
  have := Fact.mk Nat.prime_two
  obtain ⟨k, hkL, hk⟩ := exists_conj_le_of_isSylowOf (isSylowOf_T0 hD) hAL (isPGroup_of_sq hA2)
  have hAT : conjSub k⁻¹ A ≤ T0 := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have h1 := hk _ hx
    have e : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rwa [e] at h1
  have hU : conjSub k⁻¹ A = U := by
    refine hD.unique _ hAT ?_ ?_ ?_
    · intro a ha
      rw [mem_conjSub] at ha
      have := hA2 _ ha
      calc a * a = k⁻¹ * (k * a * k⁻¹ * (k * a * k⁻¹)) * k := by group
        _ = 1 := by
          have e : k⁻¹⁻¹ = k := inv_inv k
          rw [e] at this
          rw [this]; group
    · intro a ha b hb
      rw [mem_conjSub] at ha hb
      have e : k⁻¹⁻¹ = k := inv_inv k
      rw [e] at ha hb
      have := hAc _ ha _ hb
      calc a * b = k⁻¹ * (k * a * k⁻¹ * (k * b * k⁻¹)) * k := by group
        _ = k⁻¹ * (k * b * k⁻¹ * (k * a * k⁻¹)) * k := by rw [this]
        _ = b * a := by group
    · rw [card_conjSub]; exact hcard
  refine ⟨k, hkL, ?_⟩
  rw [← hU, conjSub_conjSub_inv]

theorem card_le_of_elem_abelian [Finite G] (hD : LocalData L U T0) {A : Subgroup G} (hAL : A ≤ L)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    Nat.card A ≤ 2 ^ 11 := by
  by_contra h
  have h' : 2 ^ 11 < Nat.card A := not_le.1 h
  obtain ⟨l, -, hAe⟩ := exists_conj_eq_U hD hAL hA2 hAc h'.le
  have : Nat.card A = 2 ^ 11 := by rw [hAe, card_conjSub, hD.card_U]
  omega

theorem card_le_two_mul_of_split [Finite G] {B B' : Subgroup G} {b₀ : G}
    (h : ∀ b ∈ B, b ∈ B' ∨ b₀⁻¹ * b ∈ B') : Nat.card B ≤ 2 * Nat.card B' := by
  have hsub : (B : Set G) ⊆ (B' : Set G) ∪ (fun x => b₀ * x) '' (B' : Set G) := by
    intro b hb
    rcases h b hb with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨b₀⁻¹ * b, h1, by group⟩
  have h1 : Nat.card B ≤ ((B' : Set G) ∪ (fun x => b₀ * x) '' (B' : Set G)).ncard := by
    rw [show Nat.card B = (B : Set G).ncard from Nat.card_coe_set_eq (B : Set G)]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (B' : Set G) ((fun x => b₀ * x) '' (B' : Set G))
  have h3 : ((fun x => b₀ * x) '' (B' : Set G)).ncard ≤ (B' : Set G).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h4 : Nat.card B' = (B' : Set G).ncard := Nat.card_coe_set_eq (B' : Set G)
  omega

section Rank

variable (hS : Setting L z)
include hS

theorem cent_split {B : Subgroup G} (hBc : ∀ b ∈ B, b * z = z * b) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hb₀L : b₀ ∉ L) : ∀ b ∈ B, b ∈ B ⊓ L ∨ b₀⁻¹ * b ∈ B ⊓ L := by
  intro b hb
  by_cases hbL : b ∈ L
  · exact Or.inl ⟨hb, hbL⟩
  · right
    refine mem_inf.2 ⟨mul_mem (inv_mem hb₀) hb, ?_⟩
    obtain ⟨l, hl, hbl⟩ := hS.centralizer_z b (hBc b hb).symm
    obtain ⟨l₀, hl₀, hb₀l⟩ := hS.centralizer_z b₀ (hBc b₀ hb₀).symm
    have hbl' : b = l * z := hbl.resolve_left (fun h => hbL (h ▸ hl))
    have hb₀l' : b₀ = l₀ * z := hb₀l.resolve_left (fun h => hb₀L (h ▸ hl₀))
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
    have : b₀⁻¹ * b = l₀⁻¹ * l := by
      calc b₀⁻¹ * b = (l₀ * z)⁻¹ * (l * z) := by rw [hb₀l', hbl']
        _ = z⁻¹ * (l₀⁻¹ * l) * z := by group
        _ = z * (l₀⁻¹ * l) * z := by rw [hzi]
        _ = (l₀⁻¹ * l) * z * z := by rw [hS.z_comm _ (mul_mem (inv_mem hl₀) hl)]
        _ = l₀⁻¹ * l := by rw [mul_assoc, hS.z_mul_self, mul_one]
    rw [this]
    exact mul_mem (inv_mem hl₀) hl

variable [Finite G] (hD : LocalData L U T0)
include hD

theorem rankData_of : RankData L U z := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hS.z_mul_self
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  refine ⟨?_, ?_⟩
  · intro B hBc hB2 hBa
    by_cases hBL : B ≤ L
    · have := card_le_of_elem_abelian hD hBL hB2 hBa
      calc Nat.card B ≤ 2 ^ 11 := this
        _ ≤ 2 ^ 12 := by norm_num
    · obtain ⟨b₀, hb₀, hb₀L⟩ := IsConcreteLE.not_le_iff_exists.1 hBL
      have hsplit := cent_split hS hBc hb₀ hb₀L
      have h1 := card_le_two_mul_of_split hsplit
      have h2 : Nat.card (B ⊓ L : Subgroup G) ≤ 2 ^ 11 :=
        card_le_of_elem_abelian hD inf_le_right (fun a ha => hB2 a ha.1)
          (fun a ha b hb => hBa a ha.1 b hb.1)
      omega
  · intro B hzB hBc hB2 hBa hcard
    have hzL : z ∉ L := hS.z_not_mem
    have hsplit := cent_split hS hBc hzB hzL
    have h1 := card_le_two_mul_of_split hsplit
    have h2 : 2 ^ 11 ≤ Nat.card (B ⊓ L : Subgroup G) := by omega
    obtain ⟨l, hl, hB'⟩ := exists_conj_eq_U hD inf_le_right (fun a ha => hB2 a ha.1)
      (fun a ha b hb => hBa a ha.1 b hb.1) h2
    refine ⟨l, hl, ?_⟩
    ext x
    rw [mem_conjSub, mem_Vsub_iff hS hUL]
    have hlz : z * l⁻¹ = l⁻¹ * z := hS.z_comm _ (inv_mem hl)
    have hlz' : z⁻¹ * l⁻¹ = l⁻¹ * z⁻¹ := by rw [hzi]; exact hlz
    constructor
    · intro hx
      rcases hsplit x hx with h | h
      · have := (mem_conjSub (g := l) (A := U)).1 (hB' ▸ h)
        exact ⟨l⁻¹ * x * l, this, Or.inl rfl⟩
      · have h' : l⁻¹ * (z⁻¹ * x) * l ∈ U := (mem_conjSub (g := l) (A := U)).1 (hB' ▸ h)
        refine ⟨z⁻¹ * (l⁻¹ * x * l), ?_, Or.inr ?_⟩
        · have e : z⁻¹ * (l⁻¹ * x * l) = l⁻¹ * (z⁻¹ * x) * l := by
            calc z⁻¹ * (l⁻¹ * x * l) = (z⁻¹ * l⁻¹) * x * l := by group
              _ = (l⁻¹ * z⁻¹) * x * l := by rw [hlz']
              _ = l⁻¹ * (z⁻¹ * x) * l := by group
          rw [e]; exact h'
        · group
    · rintro ⟨u, hu, hxu⟩
      have hxl : x = l * (l⁻¹ * x * l) * l⁻¹ := by group
      rcases hxu with hxu | hxu
      · have : x ∈ conjSub l U := (mem_conjSub (g := l) (A := U)).2 (by rw [hxu]; exact hu)
        rw [← hB'] at this
        exact this.1
      · have hx' : x = z * (l * u * l⁻¹) := by
          calc x = l * (l⁻¹ * x * l) * l⁻¹ := hxl
            _ = l * (z * u) * l⁻¹ := by rw [hxu]
            _ = (l * z) * u * l⁻¹ := by group
            _ = (z * l) * u * l⁻¹ := by rw [← hS.z_comm l hl]
            _ = z * (l * u * l⁻¹) := by group
        have h1 : l * u * l⁻¹ ∈ conjSub l U :=
          (mem_conjSub (g := l) (A := U)).2 (by simpa [mul_assoc] using hu)
        rw [← hB'] at h1
        rw [hx']
        exact mul_mem hzB h1.1

end Rank

end CFSG.EvenSporadicStandard.J4Std
