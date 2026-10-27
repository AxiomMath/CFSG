module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TClique
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Assembly
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section ZStar

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem exists_commuting_conj_ne (hnab : ∃ a b : F, a * b ≠ b * a) {t : F} (ht : orderOf t = 2) :
    ∃ g : F, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  by_contra hcon
  have hiso : ∀ g : F, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    by_contra hne
    exact hcon ⟨g, hne, hg⟩
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have := Fintype.ofFinite F
  obtain ⟨N, hN, hodd, hc⟩ := CFSG.ZStar.glauberman_zStar F t ht1 ht2 hiso
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · apply ht1
    refine Hat2A7.center_trivial_of_simple hnab t fun y => ?_
    have h1 := hc y
    rw [h, Subgroup.mem_bot] at h1
    have h2 : y * t * y⁻¹ = t := by
      calc y * t * y⁻¹ = y * t * y⁻¹ * t⁻¹ * t := by group
        _ = t := by rw [h1]; group
    calc t * y = (y * t * y⁻¹) * y := by rw [h2]
      _ = y * t := by group
  · rw [h, Subgroup.card_top] at hodd
    have h2 : 2 ∣ Nat.card F := ht ▸ orderOf_dvd_natCard t
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite F] [IsSimpleGroup F] in
theorem isClassical2A7_map_conj {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) (g : F) :
    IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
  have h1 := hK.conj g
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

theorem exists_commuting_conj_member (hnab : ∃ a b : F, a * b ≠ b * a) {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z) :
    ∃ g : F, g * z * g⁻¹ ≠ z ∧ (g * z * g⁻¹) * z = z * (g * z * g⁻¹) ∧
      IsClassical2A7 ⊤ (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
  obtain ⟨g, h1, h2⟩ := exists_commuting_conj_ne hnab hK.orderOf_eq_two
  exact ⟨g, h1, h2, isClassical2A7_map_conj hK g⟩

theorem false_of_noBadPair_of_cliqueInv_subsingleton (hnab : ∃ a b : F, a * b ≠ b * a)
    {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hnb : ∀ g : F, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) →
      CommOrEq K (K.map (MulAut.conj g).toMonoidHom))
    (hcl : ∀ u ∈ cliqueInv K, u = z) : False := by
  obtain ⟨g, h1, h2, h3⟩ := exists_commuting_conj_member hnab hK
  exact h1 (hcl _ ⟨_, h3, hnb g h2⟩)

end ZStar

end CFSG.ClassicalInvolution.Hat2A7T
