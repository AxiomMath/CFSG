module

public import CFSG.GH74.Uniqueness.Section5Basic
public import CFSG.GH74.Uniqueness.Section7Cor713Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

namespace Cor713

section Pure

variable {G K : Type*} [Group G] [Group K]

theorem exists_twoTransitive_of_surjective (ψ : G →* K) (hψ : Function.Surjective ψ)
    {B : Subgroup K} {Y : Subgroup G} (hY : ∀ g : G, ψ g ∈ B ↔ g ∈ Y)
    (h2 : ∀ a b c d : K ⧸ B, a ≠ b → c ≠ d → ∃ k : K, k • a = c ∧ k • b = d)
    {a₁ b₁ a₂ b₂ : G} (h₁ : a₁ * b₁⁻¹ ∉ Y) (h₂ : a₂ * b₂⁻¹ ∉ Y) :
    ∃ l : G, a₁ * l * a₂⁻¹ ∈ Y ∧ b₁ * l * b₂⁻¹ ∈ Y := by
  have hne : ∀ x y : G, x * y⁻¹ ∉ Y →
      (QuotientGroup.mk (ψ x)⁻¹ : K ⧸ B) ≠ QuotientGroup.mk (ψ y)⁻¹ := by
    intro x y hxy heq
    apply hxy
    rw [QuotientGroup.eq] at heq
    rw [← hY]
    simpa using heq
  obtain ⟨k, hk1, hk2⟩ := h2 _ _ _ _ (hne a₁ b₁ h₁) (hne a₂ b₂ h₂)
  obtain ⟨l, hl⟩ := hψ k⁻¹
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at hk1 hk2
  refine ⟨l, ?_, ?_⟩
  · rw [← hY, map_mul, map_mul, map_inv, hl]
    simpa [mul_assoc] using hk1
  · rw [← hY, map_mul, map_mul, map_inv, hl]
    simpa [mul_assoc] using hk2

end Pure

section Count

variable {G K : Type} [Group G] [Finite G] [Group K]

theorem ncard_involutions_eq (ψ : G →* K) (hψ : Function.Surjective ψ) {N : Subgroup G}
    (hker : ψ.ker = N) (hNodd : Odd (Nat.card N)) (hNc : ∀ o ∈ N, ∀ g : G, o * g = g * o)
    {B : Subgroup K} {Y : Subgroup G} (hY : ∀ g : G, ψ g ∈ B ↔ g ∈ Y) :
    {y : G | y ∈ Y ∧ orderOf y = 2}.ncard = {k : K | k ∈ B ∧ orderOf k = 2}.ncard := by
  have hsq : ∀ y : G, orderOf y = 2 → y * y = 1 := fun y hy => by
    rw [← pow_two, ← hy]; exact pow_orderOf_eq_one y
  have hne : ∀ y : G, orderOf y = 2 → ψ y ≠ 1 := by
    intro y hy h1
    have : y ∈ N := by rw [← hker]; exact h1
    exact CFSG.OddInversion.notMem_of_odd_card hNodd hy this
  have himage : ψ '' {y : G | y ∈ Y ∧ orderOf y = 2} = {k : K | k ∈ B ∧ orderOf k = 2} := by
    ext k
    constructor
    · rintro ⟨y, ⟨hyY, hy2⟩, rfl⟩
      refine ⟨(hY y).mpr hyY, orderOf_eq_prime ?_ (hne y hy2)⟩
      rw [pow_two, ← map_mul, hsq y hy2, map_one]
    · rintro ⟨hkB, hk2⟩
      obtain ⟨g, rfl⟩ := hψ k
      have hgY : g ∈ Y := (hY g).mp hkB
      have hkk : ψ g * ψ g = 1 := by
        rw [← pow_two, ← hk2]; exact pow_orderOf_eq_one _
      have hgg : g * g ∈ N := by
        rw [← hker, MonoidHom.mem_ker, map_mul]; exact hkk
      have hgN : g ∉ N := by
        intro h
        have : ψ g = 1 := by rw [← MonoidHom.mem_ker, hker]; exact h
        rw [this, orderOf_one] at hk2
        exact absurd hk2 (by norm_num)
      obtain ⟨y, hy, hy2, hyN⟩ := exists_involution_mem_zpowers_coset hNodd hgg hgN
      have hyY : y ∈ Y := Subgroup.zpowers_le.mpr hgY hy
      have hψy : ψ y = ψ g := by
        have h1 : ψ (y * g⁻¹) = 1 := by rw [← MonoidHom.mem_ker, hker]; exact hyN
        rw [map_mul, map_inv, mul_inv_eq_one] at h1
        exact h1
      exact ⟨y, ⟨hyY, hy2⟩, hψy⟩
  have hinj : Set.InjOn ψ {y : G | y ∈ Y ∧ orderOf y = 2} := by
    rintro y ⟨-, hy2⟩ y' ⟨-, hy2'⟩ hyy'
    have ho : y⁻¹ * y' ∈ N := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyy', inv_mul_cancel]
    have hoo : (y⁻¹ * y') * (y⁻¹ * y') = 1 := by
      set o := y⁻¹ * y' with ho'
      have hy'eq : y' = y * o := by simp [ho']
      have h2 : (y * o) * (y * o) = 1 := by rw [← hy'eq]; exact hsq y' hy2'
      have h3 : (y * o) * (y * o) = (y * y) * (o * o) := by
        calc (y * o) * (y * o) = y * (o * y) * o := by group
          _ = y * (y * o) * o := by rw [hNc o ho y]
          _ = (y * y) * (o * o) := by group
      rw [h3, hsq y hy2, one_mul] at h2
      exact h2
    exact inv_mul_eq_one.mp (eq_one_of_mem_of_sq_eq_one hNodd ho hoo)
  rw [← himage, hinj.ncard_image]

end Count

section BenderK

variable {K : Type} [Group K] [Finite K]

theorem bender_twoTransitive_and_card
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (T₀ : Sylow 2 K) :
    (∀ a b c d : K ⧸ normalizer ((T₀ : Subgroup K) : Set K), a ≠ b → c ≠ d →
      ∃ k : K, k • a = c ∧ k • b = d) ∧
    ∃ n : ℕ, 2 ≤ n ∧
      {k : K | k ∈ normalizer ((T₀ : Subgroup K) : Set K) ∧ orderOf k = 2}.ncard = 2 ^ n - 1 := by
  obtain ⟨n, i, e, hT⟩ := exists_benderType_of_isBenderGroup hK
  obtain ⟨t, hc⟩ := hT.exists_benderCore T₀
  refine ⟨?_, n, hT.two_le.2, ?_⟩
  · have h := hc.isMultiplyPretransitive
    rw [MulAction.is_two_pretransitive_iff] at h
    exact fun a b c d hab hcd => h hab hcd
  · have e1 : {k : K | k ∈ normalizer ((T₀ : Subgroup K) : Set K) ∧ orderOf k = 2} =
        ((Bender.rootCenter (T₀ : Subgroup K) : Subgroup K) : Set K) \ {1} := by
      ext g
      exact hc.involution_iff
    rw [e1, Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
    have h2 : ((Bender.rootCenter (T₀ : Subgroup K) : Subgroup K) : Set K).ncard = 2 ^ n := by
      rw [← Nat.card_coe_set_eq]
      exact hc.card_center
    rw [h2]

end BenderK

section Borel

variable {G K : Type} [Group G] [Group K] [Finite K]

theorem borel_witness (ψ : G →* K) (hψ : Function.Surjective ψ) (hker : ψ.ker = center G)
    {Y : Subgroup G} {T₀ : Sylow 2 K}
    (hY : ∀ g : G, ψ g ∈ normalizer ((T₀ : Subgroup K) : Set K) ↔ g ∈ Y) :
    ∃ T : Sylow 2 (G ⧸ center G), Y.map (QuotientGroup.mk' (center G)) =
      normalizer ((T : Subgroup (G ⧸ center G)) : Set (G ⧸ center G)) := by
  let e : G ⧸ center G ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have he : ∀ g : G, e (QuotientGroup.mk g) = ψ g := fun g => rfl
  refine ⟨T₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
  rw [Sylow.coe_mapSurjective e.symm.surjective T₀,
    ← Subgroup.map_normalizer_eq_of_bijective _ e.symm.bijective]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨ψ y, (hY y).mpr hy, ?_⟩
    apply e.injective
    simp [he]
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨g, rfl⟩ := hψ k
    refine ⟨g, (hY g).mp hk, ?_⟩
    apply e.injective
    simp [he]

end Borel

end Cor713

section XLevel

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.cor713_twoTransitive_alphaOrbit (S : ZDSetup X Z M) {F : Subgroup X} (hFM : ¬ F ≤ M)
    (hne : (Z ∩ ((F ⊓ M : Subgroup X) : Set X)).Nonempty) {K : Type} [Group K]
    (ψ : ↥(zHull Z F) →* K) (hψ : Function.Surjective ψ) {B : Subgroup K}
    (hY : ∀ g : ↥(zHull Z F), ψ g ∈ B ↔ (g : X) ∈ M)
    (h2 : ∀ a b c d : K ⧸ B, a ≠ b → c ≠ d → ∃ k : K, k • a = c ∧ k • b = d) :
    ∀ β₁ ∈ alphaOrbit M F, ∀ γ₁ ∈ alphaOrbit M F, β₁ ≠ γ₁ →
      ∀ β₂ ∈ alphaOrbit M F, ∀ γ₂ ∈ alphaOrbit M F, β₂ ≠ γ₂ →
        ∃ g ∈ zHull Z F, conjugate β₁ g = β₂ ∧ conjugate γ₁ g = γ₂ := by
  rw [S.cor713_alphaOrbit_eq hFM hne]
  rintro _ ⟨a₁, ha₁, rfl⟩ _ ⟨b₁, hb₁, rfl⟩ h₁ _ ⟨a₂, ha₂, rfl⟩ _ ⟨b₂, hb₂, rfl⟩ h₂
  have hY' : ∀ g : ↥(zHull Z F), ψ g ∈ B ↔ g ∈ M.comap (zHull Z F).subtype := hY
  have hn₁ : (⟨a₁, ha₁⟩ : ↥(zHull Z F)) * (⟨b₁, hb₁⟩ : ↥(zHull Z F))⁻¹ ∉
      M.comap (zHull Z F).subtype := by
    intro h
    exact h₁ (S.prodDisc.conjugate_eq_of_mul_inv_mem (Subgroup.mem_comap.mp h))
  have hn₂ : (⟨a₂, ha₂⟩ : ↥(zHull Z F)) * (⟨b₂, hb₂⟩ : ↥(zHull Z F))⁻¹ ∉
      M.comap (zHull Z F).subtype := by
    intro h
    exact h₂ (S.prodDisc.conjugate_eq_of_mul_inv_mem (Subgroup.mem_comap.mp h))
  obtain ⟨l, hl₁, hl₂⟩ := Cor713.exists_twoTransitive_of_surjective ψ hψ hY' h2 hn₁ hn₂
  refine ⟨l, l.2, ?_, ?_⟩
  · rw [conjugate_conjugate]
    exact S.prodDisc.conjugate_eq_of_mul_inv_mem (Subgroup.mem_comap.mp hl₁)
  · rw [conjugate_conjugate]
    exact S.prodDisc.conjugate_eq_of_mul_inv_mem (Subgroup.mem_comap.mp hl₂)

theorem ZDSetup.cor713_eq_mul_of_twoTransitive (S : ZDSetup X Z M) {F : Subgroup X}
    (h2t : ∀ β₁ ∈ alphaOrbit M F, ∀ γ₁ ∈ alphaOrbit M F, β₁ ≠ γ₁ →
      ∀ β₂ ∈ alphaOrbit M F, ∀ γ₂ ∈ alphaOrbit M F, β₂ ≠ γ₂ →
        ∃ g ∈ zHull Z F, conjugate β₁ g = β₂ ∧ conjugate γ₁ g = γ₂)
    {β : Subgroup X} (hβ : β ∈ alphaOrbit M F) (hβM : β ≠ M) :
    (F : Set X) = (zHull Z F : Set X) * ((F ⊓ M ⊓ β : Subgroup X) : Set X) := by
  apply Set.Subset.antisymm
  · intro x hxF
    have hx'F : x⁻¹ ∈ F := F.inv_mem hxF
    have hMmem : M ∈ alphaOrbit M F := ⟨1, F.one_mem, conjugate_one M⟩
    obtain ⟨f, hf, rfl⟩ := hβ
    have hβΩ : conjugate M f ∈ omega M := ⟨f, rfl⟩
    have h1 : conjugate M x⁻¹ ∈ alphaOrbit M F := ⟨x⁻¹, hx'F, rfl⟩
    have h2 : conjugate (conjugate M f) x⁻¹ ∈ alphaOrbit M F :=
      ⟨f * x⁻¹, F.mul_mem hf hx'F, (conjugate_conjugate M f x⁻¹).symm⟩
    have hne1 : conjugate M x⁻¹ ≠ conjugate (conjugate M f) x⁻¹ := fun h =>
      hβM (conjugate_injective x⁻¹ h).symm
    obtain ⟨g, hg, hg1, hg2⟩ := h2t _ h1 _ h2 hne1 M hMmem (conjugate M f) ⟨f, hf, rfl⟩ hβM.symm
    have hhM : x⁻¹ * g ∈ M := by
      have := conjugate_eq_iff_mem_normalizer.mp (by
        rw [conjugate_conjugate] at hg1
        exact hg1)
      rwa [S.prodDisc.normalizer_eq_self] at this
    have hhβ : x⁻¹ * g ∈ conjugate M f := by
      have := conjugate_eq_iff_mem_normalizer.mp (by
        rw [conjugate_conjugate] at hg2
        exact hg2)
      rwa [S.prodDisc.normalizer_eq_of_mem_omega hβΩ] at this
    have hgF : g ∈ F := Cor713.zHull_le F hg
    refine ⟨g, hg, (x⁻¹ * g)⁻¹, ?_, ?_⟩
    · exact Subgroup.inv_mem _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨F.mul_mem hx'F hgF, hhM⟩, hhβ⟩)
    · group
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact F.mul_mem (Cor713.zHull_le F ha) (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).1

end XLevel

end CFSG.GH74.Uniqueness
