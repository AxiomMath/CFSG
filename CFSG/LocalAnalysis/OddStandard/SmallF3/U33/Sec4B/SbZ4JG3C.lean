module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG3A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Ctx4Z


variable (hz : Ctx4Z t L S x₁ x₂ lam rho tau) {Ng : Subgroup G} [(hz.z4iSub Ng).Normal]

theorem z4j_e16 (hN : Z4IOdd t tau x₁ x₂ rho Ng) {Vc : Subgroup ↥(ctxNQ t tau x₁ x₂ rho)}
    {Vh : Subgroup (↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng)}
    (hVc : S4B.Z4JLift (hz.z4iSub Ng) Vc Vh)
    {F : Subgroup (↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng)} (hFV : F ≤ Vh)
    (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hF2 : ∀ a ∈ F, a * a = 1)
    (hF : Nat.card F = 16) :
    {u : ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng | u ∈ F ∧ hz.z4jT (Ng := Ng) u}.ncard ≤ 4 := by
  let π : ↥(ctxNQ t tau x₁ x₂ rho) →* ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng :=
    S4B.z4iπ (hz.z4iSub Ng)
  let F' : Subgroup ↥(ctxNQ t tau x₁ x₂ rho) := Vc ⊓ F.comap π
  let Fg : Subgroup G := F'.map (Subgroup.subtype (ctxNQ t tau x₁ x₂ rho))
  let A : Set ↥(ctxNQ t tau x₁ x₂ rho) :=
    {x | x ∈ F' ∧ ∃ g : G, (x : G) = g * t * g⁻¹}
  let B : Set G := {u | u ∈ Fg ∧ ∃ g : G, u = g * t * g⁻¹}
  have hF'card : Nat.card F' = 16 := (hVc.card_sub hFV).trans hF
  have hFgcard : Nat.card Fg = 16 :=
    (Subgroup.card_map_of_injective (K := F') (Subgroup.subtype_injective _)).trans hF'card
  have hFgab : ∀ a ∈ Fg, ∀ b ∈ Fg, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    have haVc : a' ∈ Vc := (Subgroup.mem_inf.mp ha').1
    have hbVc : b' ∈ Vc := (Subgroup.mem_inf.mp hb').1
    have haF : π a' ∈ F := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ha').2
    have hbF : π b' ∈ F := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hb').2
    exact congrArg Subtype.val (hVc.comm haVc hbVc (hFab (π a') haF (π b') hbF))
  have hFg2 : ∀ a ∈ Fg, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    have haVc : a' ∈ Vc := (Subgroup.mem_inf.mp ha').1
    have haF : π a' ∈ F := Subgroup.mem_comap.mp (Subgroup.mem_inf.mp ha').2
    exact congrArg Subtype.val (hVc.mul_self_eq_one haVc (hF2 (π a') haF))
  have hboundFg : B.ncard ≤ 4 := by
    simpa [B] using hz.z4j_card_tG_elem16 hFgab hFg2 hFgcard
  have hsub : {u : ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng |
      u ∈ F ∧ hz.z4jT (Ng := Ng) u} ⊆ π '' A := by
    rintro u ⟨huF, huT⟩
    have huT' : hz.z4jT (Ng := Ng) u := huT
    obtain ⟨x, hxπ, gx, hgx⟩ := huT
    obtain ⟨a, haVc, haπ⟩ := hVc.exists_lift (hFV huF)
    have haF : π a ∈ F := by rw [haπ]; exact huF
    have haF' : a ∈ F' := Subgroup.mem_inf.mpr ⟨haVc, Subgroup.mem_comap.mpr haF⟩
    have hx2 : x * x = 1 := by
      apply Subtype.ext
      show (x : G) * (x : G) = (1 : G)
      rw [hgx]
      calc (gx * t * gx⁻¹) * (gx * t * gx⁻¹) = gx * (t * t) * gx⁻¹ := by group
        _ = 1 := by rw [hz.t_mul_self]; group
    have hx1 : x ≠ 1 := by
      intro hx1
      apply hz.t_ne_one
      have hx1' : (x : G) = 1 := by rw [hx1]; rfl
      rw [hgx] at hx1'
      calc t = gx⁻¹ * (gx * t * gx⁻¹) * gx := by group
        _ = gx⁻¹ * 1 * gx := by rw [hx1']
        _ = 1 := by group
    have hud : u ≠ 1 := by
      rw [← hxπ]
      exact S4B.z4i_map_ne_one (hz.z4iSub Ng) hVc.odd hx2 hx1
    have ha2 : a * a = 1 :=
      hVc.mul_self_eq_one haVc (by rw [haπ]; exact hF2 u huF)
    have ha1 : a ≠ 1 := by
      intro ha1
      exact hud (by rw [← haπ, ha1, map_one])
    have hTπa : hz.z4jT (Ng := Ng) (π a) := by rw [haπ]; exact huT'
    obtain ⟨g, hg⟩ := (hz.z4jT_map_iff (Ng := Ng) hN ha2 ha1).mp hTπa
    exact ⟨a, ⟨haF', g, hg⟩, haπ⟩
  have hAB : Subtype.val '' A ⊆ B := by
    rintro _ ⟨a, ⟨haF', g, hg⟩, rfl⟩
    exact ⟨Subgroup.mem_map.mpr ⟨a, haF', rfl⟩, g, hg⟩
  calc {u : ↥(ctxNQ t tau x₁ x₂ rho) ⧸ hz.z4iSub Ng |
        u ∈ F ∧ hz.z4jT (Ng := Ng) u}.ncard
      ≤ (π '' A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ A.ncard := Set.ncard_image_le
    _ = (Subtype.val '' A).ncard := (Set.ncard_image_of_injective A Subtype.val_injective).symm
    _ ≤ B.ncard := Set.ncard_le_ncard hAB (Set.toFinite _)
    _ ≤ 4 := hboundFg

end Ctx4Z

end CFSG.OddStandard.SmallF3.HarrisU33
