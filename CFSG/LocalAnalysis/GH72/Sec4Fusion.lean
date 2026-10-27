module

public import CFSG.LocalAnalysis.GH72.Sec4Balance

public section

namespace CFSG.GH72

open Subgroup

namespace G4c

open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff)

section Restrict

variable {G : Type*} [Group G]

theorem ddDecomp_subgroupOf {S S₁ S₂ H : Subgroup G} (hd : DDDecomp S S₁ S₂) (hSH : S ≤ H) :
    DDDecomp (S.subgroupOf H) (S₁.subgroupOf H) (S₂.subgroupOf H) where
  sup_eq := by
    rw [← subgroupOf_sup_of_le (hd.le_left.trans hSH) (hd.le_right.trans hSH), hd.sup_eq]
  inf_eq := by
    rw [eq_bot_iff]
    rintro x ⟨h₁, h₂⟩
    have hx : (x : G) ∈ S₁ ⊓ S₂ := ⟨h₁, h₂⟩
    rw [hd.inf_eq, mem_bot] at hx
    rw [mem_bot]
    exact Subtype.ext hx
  commute := by
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (hd.comm hx hy)
  dih₁ := by
    obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₁
    exact ⟨a, ha, ⟨(subgroupOfEquivOfLe (hd.le_left.trans hSH)).trans e⟩⟩
  dih₂ := by
    obtain ⟨a, ha, ⟨e⟩⟩ := hd.dih₂
    exact ⟨a, ha, ⟨(subgroupOfEquivOfLe (hd.le_right.trans hSH)).trans e⟩⟩

theorem exists_ne_one_of_isKleinFour {V : Subgroup G} (hV : IsKleinFour V) : ∃ v ∈ V, v ≠ 1 := by
  by_contra h
  push Not at h
  have hle : V = ⊥ := eq_bot_iff.mpr fun v hv => mem_bot.mpr (h v hv)
  have h4 : Nat.card V = 4 := IsKleinFour.card_four
  rw [hle, card_bot] at h4
  omega

variable [Finite G]

theorem noIndexTwo_of_le_O2 {H : Subgroup G} (S : Sylow 2 G) (hSH : (S : Subgroup G) ≤ O2 H) :
    ∀ N : Subgroup H, N.Normal → N.index ≠ 2 := by
  intro N hN h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.map H.subtype with hN'
  have hN'H : N' ≤ H := map_subtype_le N
  have hsub : N'.subgroupOf H = N := by
    rw [hN', subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  have hnorm : H ≤ normalizer (N' : Set G) := CFSG.ABGLocalTools.le_normalizer_map_subtype H N
  have hidx : N'.relIndex H = 2 ^ 1 := by rw [relIndex, hsub, h2, pow_one]
  have hSN : (S : Subgroup G) ≤ N' := hSH.trans (O2_le_of_relIndex hN'H hnorm hidx)
  have hSH' : (S : Subgroup G) ≤ H := hSH.trans (O2_le H)
  have hdvd : N'.relIndex H ∣ (S : Subgroup G).index :=
    (Dvd.intro_left _ (relIndex_mul_relIndex _ _ _ hSN hN'H)).trans
      (relIndex_dvd_index_of_le hSH')
  rw [hidx, pow_one] at hdvd
  exact S.not_dvd_index hdvd

end Restrict

end G4c

namespace Sec4Setting

open G4c
open CFSG.CGT.Foote81L6.TStruct (isElemAbelian_two_iff)

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}
  (hAS : A ≤ 𝔖.S) (hA : IsE16 A)

include hAS hA in
theorem lemma_4_12_of
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h32_37 : ∀ (K : Subgroup G) (𝔗 : Sec3Setting K), ∃ S₁' S₂' : Subgroup K,
      DDDecomp (𝔗.S : Subgroup K) S₁' S₂' ∧ HasProductFusion S₁' S₂')
    (H : Subgroup G) (_hH : H ≠ ⊤) (hM : 𝔖.M A ≤ H) (hN : 𝔖.N A ≤ H) :
    ∀ t ∈ H, orderOf t = 2 → ∃ h ∈ H, h * t * h⁻¹ ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht ht2
  have hS₂M : 𝔖.S₂ ≤ 𝔖.M A := fun s hs =>
    mem_centralizer_iff.mpr fun x hx => 𝔖.decomp.comm (X_le_S₁ hx) hs
  have hS₁N : 𝔖.S₁ ≤ 𝔖.N A := fun s hs =>
    mem_centralizer_iff.mpr fun y hy => (𝔖.decomp.comm hs (Y_le_S₂ hy)).symm
  have hSO2 : (𝔖.S : Subgroup G) ≤ O2 H := by
    rw [S_eq]
    refine sup_le ((h48.2.1.le.trans ?_).trans (O2_mono hN))
      ((h47.2.1.le.trans ?_).trans (O2_mono hM))
    · exact sup_le (G4c.commutator_le_of_le le_rfl le_rfl) (O_le_O2 _)
    · exact sup_le (G4c.commutator_le_of_le le_rfl le_rfl) (O_le_O2 _)
  have hSH : (𝔖.S : Subgroup G) ≤ H := hSO2.trans (O2_le H)
  have hAH : A ≤ H := hAS.trans hSH
  let 𝔗 : Sec3Setting H :=
    { S := 𝔖.S.subtype hSH
      S₁ := 𝔖.S₁.subgroupOf H
      S₂ := 𝔖.S₂.subgroupOf H
      decomp := by
        rw [Sylow.coe_subtype]
        exact ddDecomp_subgroupOf 𝔖.decomp hSH
      noIndexTwo := noIndexTwo_of_le_O2 𝔖.S hSO2 }
  obtain ⟨T₁, T₂, hd, hpf⟩ := h32_37 H 𝔗
  set A' : Subgroup H := A.subgroupOf H with hA'
  have hA'S : A' ≤ (𝔗.S : Subgroup H) := fun a ha => by
    show a ∈ (𝔖.S : Subgroup G).subgroupOf H
    exact hAS ha
  have hA'2 : ∀ b ∈ A', b * b = 1 := fun b hb =>
    Subtype.ext (isElemAbelian_two_iff.1 hA.1 _ hb)
  have hA'16 : IsE16 A' :=
    ⟨isElemAbelian_two_iff.2 hA'2, by rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]; exact hA.2⟩
  obtain ⟨-, hK₁, hK₂, -⟩ := dd_e16_split _ T₁ T₂ hd A' hA'S hA'16
  have hord : ∀ b ∈ A', b ≠ 1 → orderOf b = 2 := fun b hb hb1 =>
    orderOf_eq_prime (by rw [pow_two]; exact hA'2 b hb) hb1
  obtain ⟨a₁, ha₁, ha₁1⟩ := exists_ne_one_of_isKleinFour hK₁
  obtain ⟨a₂, ha₂, ha₂1⟩ := exists_ne_one_of_isKleinFour hK₂
  set t' : H := ⟨t, ht⟩ with ht'
  have ht'2 : orderOf t' = 2 := by rw [ht', Subgroup.orderOf_mk]; exact ht2
  have hQ : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht'2, pow_one])
  obtain ⟨c, -, hc⟩ := exists_mem_map_cj_le 𝔗.S (le_top : (𝔗.S : Subgroup H) ≤ ⊤) le_top hQ
  set s : H := c * t' * c⁻¹ with hs
  have hsS : s ∈ (𝔗.S : Subgroup H) := hc (mem_map_of_mem (cj c) (mem_zpowers t'))
  have hsT : s ∈ T₁ ⊔ T₂ := hd.sup_eq ▸ hsS
  have hs2 : orderOf s = 2 := by
    rw [hs, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ht'2
  have key : ∀ b ∈ A', IsConj s b → ∃ h ∈ H, h * t * h⁻¹ ∈ A := by
    intro b hb hsb
    obtain ⟨d, hdb⟩ := isConj_iff.mp hsb
    refine ⟨((d * c : H) : G), (d * c).2, ?_⟩
    have e : ((d * c * t' * (d * c)⁻¹ : H) : G) = ((d * c : H) : G) * t * ((d * c : H) : G)⁻¹ :=
      rfl
    rw [← e, show d * c * t' * (d * c)⁻¹ = d * s * d⁻¹ by rw [hs]; group, hdb]
    exact hb
  by_cases h₁ : s ∈ T₁
  · exact key a₁ ha₁.1 (hpf.conj₁ s h₁ a₁ ha₁.2 hs2 (hord a₁ ha₁.1 ha₁1))
  by_cases h₂ : s ∈ T₂
  · exact key a₂ ha₂.1 (hpf.conj₂ s h₂ a₂ ha₂.2 hs2 (hord a₂ ha₂.1 ha₂1))
  have hb₁ : a₁ * a₂ ∉ T₁ := fun h => ha₂1 (by
    have h' : a₂ ∈ T₁ ⊓ T₂ := ⟨by simpa using T₁.mul_mem (T₁.inv_mem ha₁.2) h, ha₂.2⟩
    rwa [hd.inf_eq, mem_bot] at h')
  have hb₂ : a₁ * a₂ ∉ T₂ := fun h => ha₁1 (by
    have h' : a₁ ∈ T₁ ⊓ T₂ := ⟨ha₁.2, by simpa using T₂.mul_mem h (T₂.inv_mem ha₂.2)⟩
    rwa [hd.inf_eq, mem_bot] at h')
  have hb1 : a₁ * a₂ ≠ 1 := fun h => hb₁ (h ▸ one_mem _)
  exact key _ (mul_mem ha₁.1 ha₂.1) (hpf.conj₃ s hsT _ (mul_mem_sup ha₁.2 ha₂.2) h₁ h₂ hb₁ hb₂
    hs2 (hord _ (mul_mem ha₁.1 ha₂.1) hb1))

end Sec4Setting

end CFSG.GH72
