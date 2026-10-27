module

public import CFSG.LocalAnalysis.ZStar
public import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools

section ZStarForm

variable {Ω : Type*} [Group Ω]

theorem isPGroup_two_closure_pair {a b : Ω} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) : IsPGroup 2 (Subgroup.closure ({a, b} : Set Ω)) := by
  set s : Set Ω := {a, b} with hs
  have h1 : ∀ x ∈ Subgroup.closure s, ∀ z ∈ s, z * x = x * z := by
    intro x hx z hz
    have hle : Subgroup.closure s ≤ Subgroup.centralizer s := by
      rw [Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        first | rfl | exact hab | exact hab.symm
    exact Subgroup.mem_centralizer_iff.1 (hle hx) z hz
  have hcomm : ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure s ≤ Subgroup.centralizer ({x} : Set Ω) := by
      rw [Subgroup.closure_le]
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (h1 v hx u hu).symm
    exact Subgroup.mem_centralizer_iff.1 (hle hy) x rfl
  have hsq : ∀ x ∈ Subgroup.closure s, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => simp
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hcomm y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx =>
      rw [← mul_inv_rev, ihx, inv_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one, show (2 : ℕ) = 1 + 1 from rfl, pow_succ, pow_one]
  exact Subtype.ext (hsq g g.2)

end ZStarForm

section ZStarForm

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_oddNormal_of_isolated_in_sylow (H T : Subgroup Ω) (hT : IsSylowOf 2 T H) (τ : Ω)
    (hτT : τ ∈ T) (hτ1 : τ ≠ 1) (hτ2 : τ * τ = 1)
    (hiso : ∀ g ∈ H, g⁻¹ * τ * g ∈ T → g⁻¹ * τ * g = τ) :
    ∃ N : Subgroup Ω, N ≤ H ∧ (N.subgroupOf H).Normal ∧ Odd (Nat.card N) ∧
      ∀ g ∈ H, g * τ * g⁻¹ * τ⁻¹ ∈ N := by
  have hτH : τ ∈ H := hT.le hτT
  let t : H := ⟨τ, hτH⟩
  have _ : Fintype H := Fintype.ofFinite H
  have hisolated : ∀ g : H, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    have hg' : ((g : Ω) * τ * (g : Ω)⁻¹) * τ = τ * ((g : Ω) * τ * (g : Ω)⁻¹) :=
      congrArg Subtype.val hg
    have hu2 : ((g : Ω) * τ * (g : Ω)⁻¹) * ((g : Ω) * τ * (g : Ω)⁻¹) = 1 := by
      calc ((g : Ω) * τ * (g : Ω)⁻¹) * ((g : Ω) * τ * (g : Ω)⁻¹)
          = (g : Ω) * (τ * τ) * (g : Ω)⁻¹ := by group
        _ = 1 := by rw [hτ2]; group
    set R := Subgroup.closure ({τ, (g : Ω) * τ * (g : Ω)⁻¹} : Set Ω) with hR
    have hRp : IsPGroup 2 R := isPGroup_two_closure_pair hτ2 hu2 hg'.symm
    have hRH : R ≤ H := by
      rw [hR, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hτH
      · exact H.mul_mem (H.mul_mem g.2 hτH) (H.inv_mem g.2)
    obtain ⟨T', hRT', hT'⟩ := exists_isSylowOf_ge hRp hRH
    obtain ⟨x, hxH, hx⟩ := isSylowOf_exists_conj hT hT'
    have hτR : τ ∈ R := Subgroup.subset_closure (Set.mem_insert _ _)
    have hτ'R : (g : Ω) * τ * (g : Ω)⁻¹ ∈ R :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    have e1 : x⁻¹ * τ * x = τ := hiso x hxH ((hx τ).1 (hRT' hτR))
    have hgx : (g : Ω)⁻¹ * x ∈ H := H.mul_mem (H.inv_mem g.2) hxH
    have hu_eq : x⁻¹ * ((g : Ω) * τ * (g : Ω)⁻¹) * x =
        ((g : Ω)⁻¹ * x)⁻¹ * τ * ((g : Ω)⁻¹ * x) := by group
    have e2 : ((g : Ω)⁻¹ * x)⁻¹ * τ * ((g : Ω)⁻¹ * x) = τ := by
      refine hiso _ hgx ?_
      rw [← hu_eq]
      exact (hx _).1 (hRT' hτ'R)
    have e3 : x⁻¹ * ((g : Ω) * τ * (g : Ω)⁻¹) * x = x⁻¹ * τ * x := by
      rw [e1, hu_eq, e2]
    have : (g : Ω) * τ * (g : Ω)⁻¹ = τ :=
      mul_left_cancel (mul_right_cancel e3)
    exact Subtype.ext this
  have ht1 : t ≠ 1 := fun h => hτ1 (congrArg Subtype.val h)
  have ht2 : t * t = 1 := Subtype.ext hτ2
  obtain ⟨N', hN'n, hN'odd, hN'⟩ := CFSG.ZStar.glauberman_zStar H t ht1 ht2 hisolated
  refine ⟨N'.map H.subtype, Subgroup.map_subtype_le N', ?_, ?_, ?_⟩
  · rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hN'n
  · rw [Subgroup.card_map_of_injective H.subtype_injective]
    exact hN'odd
  · intro g hg
    exact ⟨⟨g, hg⟩ * t * ⟨g, hg⟩⁻¹ * t⁻¹, hN' ⟨g, hg⟩, rfl⟩

end ZStarForm

end CFSG.ClassicalInvolution.GlaubermanAut
