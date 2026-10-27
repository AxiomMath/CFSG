module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Lambda
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiU1Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryU1Twist

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_coord_sup {K : Type*} [AddCommGroup K] {L₀ T₁ R₂ : Subgroup G} {t₀ : G} {f₀ : ℕ}
    (hR : U3R2 G L₀ T₁ R₂ t₀ f₀) {u : G → K}
    (hu : ∀ w ∈ T₁, ∀ w' ∈ T₁, w⁻¹ * w' ∈ T₁ ⊓ R₂ → u w = u w') :
    ∃ ψ : G → K, ∀ w ∈ T₁, ∀ r ∈ R₂, ψ (w * r) = u w := by
  classical
  refine ⟨fun x => if hx : x ∈ T₁ ⊔ R₂ then u (Classical.choose (hR.mem_sup_iff.mp hx)) else 0,
    fun w hw r hr => ?_⟩
  have hx : w * r ∈ T₁ ⊔ R₂ := mul_mem (mem_sup_left hw) (mem_sup_right hr)
  simp only [hx, dite_true]
  obtain ⟨hw', r', hr', hwr'⟩ := Classical.choose_spec (hR.mem_sup_iff.mp hx)
  set w' := Classical.choose (hR.mem_sup_iff.mp hx)
  refine hu _ hw' _ hw (mem_inf.mpr ⟨mul_mem (inv_mem hw') hw, ?_⟩)
  have e : w'⁻¹ * w = r' * r⁻¹ := by
    calc w'⁻¹ * w = w'⁻¹ * (w * r) * r⁻¹ := by group
      _ = w'⁻¹ * (w' * r') * r⁻¹ := by rw [hwr']
      _ = r' * r⁻¹ := by group
  rw [e]
  exact mul_mem hr' (inv_mem hr)

section Certificates


theorem comm_mem_of_mem_u3U₁_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hΩ : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2)
    {E : Subgroup (Equiv.Perm (u3Omega L T R₂ t))} (hE : E ≤ (u3OmegaAction L T R₂ t).range)
    (hEn : (E.subgroupOf (u3OmegaAction L T R₂ t).range).Normal)
    (hEreg : ∀ a b : u3Omega L T R₂ t, ∃! x : E, (x : Equiv.Perm (u3Omega L T R₂ t)) a = b)
    {x y : G} (hx : x ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G))
    (hy : y ∈ u3U L T R₂ t E ⊓ centralizer (R₂ : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ R₂ := by
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hNA, -, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨htriv, hcH, hU₁c, -⟩ := h.u3U_lambda_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  obtain ⟨hYU₁, -, -, -, -, hcov⟩ := h.u3U₁_facts_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  set U := u3U L T R₂ t E with hU
  set U₁ := u3U L T R₂ t E ⊓ centralizer (R₂ : Set G) with hU₁
  set H := szT₁ L T ⊔ R₂ with hH
  have hUY := u3U_le_normalizer L T R₂ t E
  have hUH : U ≤ normalizer (H : Set G) := fun y hy => (mem_inf.mp (hNR₁ (hUY hy))).1
  have hU₁U : U₁ ≤ U := inf_le_left
  obtain ⟨K, _, _, _, σ, hKcard, -, u, uu, hcoord, hA₁u, d, hdL, hdT, μ, hμ0, hμord, hdμ⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have hdA : d ∈ normalizer (szA L T t : Set G) := h.inf_normalizer_le_normalizer_szA ⟨hdL, hdT⟩
  have hdU₁ : d ∈ normalizer (U₁ : Set G) := hYU₁ (hNA hdA)
  have hdH : d ∈ normalizer (H : Set G) := (mem_inf.mp (hNR₁ (hNA hdA))).1
  have hdR₂ : d ∈ normalizer (R₂ : Set G) := (mem_inf.mp (hNR₁ (hNA hdA))).2
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  obtain ⟨ψ, hψ⟩ := exists_coord_sup hR (u := u) fun w hw w' hw' hww' => by
    have h1 : w⁻¹ * w' ∈ szA₁ (szT₁ L T) := by rw [← hR.inf]; exact hww'
    have h2 := (hA₁u _ (mul_mem (inv_mem hw) hw')).mp h1
    rw [hcoord.u_mul_inv hw hw'] at h2
    exact (sub_eq_zero.mp h2).symm
  have hψadd : ∀ a ∈ H, ∀ b ∈ H, ψ (a * b) = ψ a + ψ b := by
    intro a ha b hb
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    obtain ⟨w', hw', r', hr', rfl⟩ := hR.mem_sup_iff.mp hb
    have hrw : r * w' = w' * r := (hR.commT₁ w' hw' r hr).symm
    have e : w * r * (w' * r') = (w * w') * (r * r') := by
      calc w * r * (w' * r') = w * (r * w') * r' := by group
        _ = w * (w' * r) * r' := by rw [hrw]
        _ = (w * w') * (r * r') := by group
    rw [e, hψ _ (mul_mem hw hw') _ (mul_mem hr hr'), hψ w hw r hr, hψ w' hw' r' hr',
      hcoord.mul_u w hw w' hw']
  have hψ0 : ∀ a ∈ H, ψ a = 0 ↔ a ∈ R₂ := by
    intro a ha
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    rw [hψ w hw r hr, ← hA₁u w hw]
    constructor
    · intro hwA
      exact mul_mem (hR.le hwA) hr
    · intro hwr
      have h1 : w ∈ szT₁ L T ⊓ R₂ := mem_inf.mpr ⟨hw, by
        have := mul_mem hwr (inv_mem hr)
        rwa [mul_inv_cancel_right] at this⟩
      rwa [hR.inf] at h1
  have hψR₂ : ∀ a ∈ R₂, ψ a = 0 := fun a ha => (hψ0 a (mem_sup_right ha)).mpr ha
  have hψconj : ∀ v ∈ U, ∀ a ∈ H, ψ (v * a * v⁻¹) = ψ a := by
    intro v hv a ha
    have h1 := htriv v hv a ha
    have e : v * a * v⁻¹ = a * (a⁻¹ * (v * a * v⁻¹)) := by group
    rw [e, hψadd _ ha _ (mem_sup_right h1), hψR₂ _ h1, add_zero]
  have hψd : ∀ a ∈ H, ψ (d * a * d⁻¹) = μ * ψ a := by
    intro a ha
    obtain ⟨w, hw, r, hr, rfl⟩ := hR.mem_sup_iff.mp ha
    have e : d * (w * r) * d⁻¹ = (d * w * d⁻¹) * (d * r * d⁻¹) := by group
    rw [e, hψ _ ((mem_normalizer_iff.mp hdT w).mp hw) _ ((mem_normalizer_iff.mp hdR₂ r).mp hr),
      hψ w hw r hr, hdμ w hw]
  set l : G → K := fun z => ψ (z * t * z⁻¹ * t⁻¹) with hl
  have hcH₁ : ∀ z ∈ U₁, z * t * z⁻¹ * t⁻¹ ∈ H := fun z hz => hcH z (hU₁U hz)
  have hladd : ∀ z ∈ U₁, ∀ z' ∈ U₁, l (z * z') = l z + l z' := by
    intro z hz z' hz'
    have e : z * z' * t * (z * z')⁻¹ * t⁻¹ =
        (z * (z' * t * z'⁻¹ * t⁻¹) * z⁻¹) * (z * t * z⁻¹ * t⁻¹) := by group
    have hmem : z * (z' * t * z'⁻¹ * t⁻¹) * z⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hUH (hU₁U hz)) _).mp (hcH₁ z' hz')
    simp only [hl]
    rw [e, hψadd _ hmem _ (hcH₁ z hz), hψconj z (hU₁U hz) _ (hcH₁ z' hz'), add_comm]
  have hlsurj : ∀ a : K, ∃ z ∈ U₁, l z = a := by
    intro a
    obtain ⟨w, hw, hwa⟩ := hcoord.u_surj a
    obtain ⟨z, hz, r, hr, hzt⟩ := hcov w hw
    refine ⟨z, hz, ?_⟩
    have e : z * t * z⁻¹ * t⁻¹ = w * r := by
      rw [hzt, mul_inv_cancel_right]
      exact (hR.commT₁ w hw r hr).symm
    simp only [hl]
    rw [e, hψ w hw r hr, hwa]
  have hlker : ∀ z ∈ U₁, l z = 0 → z ∈ H := by
    intro z hz hlz
    refine h.mem_sup_of_mem_u3U₁_of_card_sylow hS2 hR hc hΩ hE hEn hEreg hz ?_
    have h1 := (hψ0 _ (hcH₁ z hz)).mp hlz
    have e : t * z * t⁻¹ * z⁻¹ = (z * t * z⁻¹ * t⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  have hld : ∀ z ∈ U₁, l (d * z * d⁻¹) = μ * l z := by
    intro z hz
    have e : d * z * d⁻¹ * t * (d * z * d⁻¹)⁻¹ * t⁻¹ = d * (z * t * z⁻¹ * t⁻¹) * d⁻¹ := by
      have hdt' : d⁻¹ * t = t * d⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hdt, mul_inv_cancel_right]
      calc d * z * d⁻¹ * t * (d * z * d⁻¹)⁻¹ * t⁻¹ = d * z * (d⁻¹ * t) * d * z⁻¹ * d⁻¹ * t⁻¹ := by
            group
        _ = d * z * (t * d⁻¹) * d * z⁻¹ * d⁻¹ * t⁻¹ := by rw [hdt']
        _ = d * z * t * z⁻¹ * (d⁻¹ * t⁻¹) := by group
        _ = d * z * t * z⁻¹ * (t⁻¹ * d⁻¹) := by
            rw [show d⁻¹ * t⁻¹ = t⁻¹ * d⁻¹ by
              rw [← mul_inv_rev, ← mul_inv_rev, hdt]]
        _ = d * (z * t * z⁻¹ * t⁻¹) * d⁻¹ := by group
    simp only [hl]
    rw [e, hψd _ (hcH₁ z hz)]
  set P : G → G → K := fun z z' => ψ (z * z' * z⁻¹ * z'⁻¹) with hP
  have hP1 : ∀ z ∈ U₁, ∀ z' ∈ U₁, ∀ w ∈ U₁, P (z * z') w = P z w + P z' w := by
    intro z hz z' hz' w hw
    have e : z * z' * w * (z * z')⁻¹ * w⁻¹ =
        (z * (z' * w * z'⁻¹ * w⁻¹) * z⁻¹) * (z * w * z⁻¹ * w⁻¹) := by group
    have hmem : z * (z' * w * z'⁻¹ * w⁻¹) * z⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hUH (hU₁U hz)) _).mp (hU₁c z' hz' w hw)
    simp only [hP]
    rw [e, hψadd _ hmem _ (hU₁c z hz w hw), hψconj z (hU₁U hz) _ (hU₁c z' hz' w hw), add_comm]
  have hP2 : ∀ z ∈ U₁, ∀ w ∈ U₁, ∀ w' ∈ U₁, P z (w * w') = P z w + P z w' := by
    intro z hz w hw w' hw'
    have e : z * (w * w') * z⁻¹ * (w * w')⁻¹ =
        (z * w * z⁻¹ * w⁻¹) * (w * (z * w' * z⁻¹ * w'⁻¹) * w⁻¹) := by group
    have hmem : w * (z * w' * z⁻¹ * w'⁻¹) * w⁻¹ ∈ H :=
      (mem_normalizer_iff.mp (hUH (hU₁U hw)) _).mp (hU₁c z hz w' hw')
    simp only [hP]
    rw [e, hψadd _ (hU₁c z hz w hw) _ hmem, hψconj w (hU₁U hw) _ (hU₁c z hz w' hw')]
  have hPl : ∀ z ∈ U₁, l z = 0 → ∀ w ∈ U₁, P z w = 0 := by
    intro z hz hlz w hw
    have hzH := hlker z hz hlz
    have h1 := htriv w (hU₁U hw) z⁻¹ (inv_mem hzH)
    rw [inv_inv] at h1
    simp only [hP]
    have e : z * w * z⁻¹ * w⁻¹ = z * (w * z⁻¹ * w⁻¹) := by group
    rw [e]
    exact hψR₂ _ h1
  have hPr : ∀ w ∈ U₁, l w = 0 → ∀ z ∈ U₁, P z w = 0 := by
    intro w hw hlw z hz
    have hwH := hlker w hw hlw
    have h1 := htriv z (hU₁U hz) w hwH
    have hwR : w ∈ normalizer (R₂ : Set G) := (sup_le hR.T₁_le_normalizer Subgroup.le_normalizer :
      H ≤ normalizer (R₂ : Set G)) hwH
    have h2 := (mem_normalizer_iff.mp hwR _).mp h1
    simp only [hP]
    have e : z * w * z⁻¹ * w⁻¹ = w * (w⁻¹ * (z * w * z⁻¹)) * w⁻¹ := by group
    rw [e]
    exact hψR₂ _ h2
  obtain ⟨β, hβ1, hβ2, hβP⟩ :=
    exists_biadditive_of_descends hladd hlsurj hladd hlsurj hP1 hP2 hPl hPr
  have hβalt : ∀ a, β a a = 0 := by
    intro a
    obtain ⟨z, hz, rfl⟩ := hlsurj a
    rw [← hβP z hz z hz]
    simp only [hP]
    rw [show z * z * z⁻¹ * z⁻¹ = (1 : G) by group]
    exact hψR₂ 1 (one_mem _)
  have hβeq : ∀ a b, β (μ * a) (μ * b) = μ * β a b := by
    intro a b
    obtain ⟨z, hz, rfl⟩ := hlsurj a
    obtain ⟨w, hw, rfl⟩ := hlsurj b
    have hdz : d * z * d⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hdU₁ z).mp hz
    have hdw : d * w * d⁻¹ ∈ U₁ := (mem_normalizer_iff.mp hdU₁ w).mp hw
    rw [← hld z hz, ← hld w hw, ← hβP _ hdz _ hdw, ← hβP z hz w hw]
    simp only [hP]
    rw [show d * z * d⁻¹ * (d * w * d⁻¹) * (d * z * d⁻¹)⁻¹ * (d * w * d⁻¹)⁻¹ =
      d * (z * w * z⁻¹ * w⁻¹) * d⁻¹ by group, hψd _ (hU₁c z hz w hw)]
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = (2 ^ f) ^ 2 := by rw [← Nat.card_eq_fintype_card, hKcard]
  have hβ0 := bilinear_eq_zero_of_alternating_equivariant_of_unitary_cartan h.two_le hK
    (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (β a) (hβ2 a))
      fun a a' => AddMonoidHom.ext fun b => hβ1 a a' b) hμ0 hμord hβeq hβalt
  have h1 : P x y = 0 := by
    rw [hβP x hx y hy]
    exact congrArg (fun b : K →+ K →+ K => b (l x) (l y)) hβ0
  exact (hψ0 _ (hU₁c x hx y hy)).mp h1

end Certificates

end U3Start

end CFSG.SeitzReduction.RankOne
