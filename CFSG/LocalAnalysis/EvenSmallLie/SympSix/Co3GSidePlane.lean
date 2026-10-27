module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3GSideEdge

public section

namespace CFSG.EvenSmallLie.SympSix.Co3Ident

open Subgroup CFSG.Sporadic.Schreier.Co3

variable
    {G : Type*} [Group G] {s : G} (θ : co3M ≃* centralizer ({s} : Set G))

@[expose] noncomputable def letterImg
    (sG : G) (i : Fin 7) : G :=
  if i = 3 then sG else θ (mGen i)

theorem letterImg_three
    (sG : G) : letterImg θ sG 3 = sG := ite_eq_left rfl

theorem letterImg_of_ne
    (sG : G) {i : Fin 7} (hi : i ≠ 3) :
    letterImg θ sG i = thetaHom θ (mGen i) :=
  ite_eq_right hi

theorem wordOf_letterImg
    (sG : G) {l : List (Fin 7)} (hl : ∀ i ∈ l, i ≠ 3) :
    wordOf (letterImg θ sG) l = θ (mWord l) :=
  wordOf_of_hom (thetaHom θ) (fun _ hi => letterImg_of_ne θ sG hi) hl

theorem relsC0_letterImg
    (sG : G) :
    ∀ r ∈ relsC0, FreeGroup.lift (letterImg θ sG) (FreeGroup.mk r) = 1 :=
  lift_relsC0_of_hom (thetaHom θ) (fun _ hi => letterImg_of_ne θ sG hi) relsC0_M

theorem bcb_letterImg
    (sG : G) :
    letterImg θ sG 1 * letterImg θ sG 2 * letterImg θ sG 1 = θ bcbM := by
  rw [letterImg_of_ne θ sG (by decide), letterImg_of_ne θ sG (by decide), thetaHom_apply,
    thetaHom_apply, ← theta_mul, ← theta_mul]

theorem edge_letterImg
    {sG : G} (hsG : sG * sG = 1)
    (hψ : ∀ x : edgeGroup, sG * θ (x : co3M) * sG⁻¹ = θ (psi x : co3M)) :
    ∀ p ∈ edgePairs, letterImg θ sG 3 * wordOf (letterImg θ sG) p.1 * letterImg θ sG 3 =
      wordOf (letterImg θ sG) p.2 := by
  intro p hp
  obtain ⟨x, hx1, hx2⟩ := modelFacts.psi_facts.2.2.2.2.2 p hp
  have hl := edgePairs_letters p hp
  rw [letterImg_three, wordOf_letterImg θ sG hl.1, wordOf_letterImg θ sG hl.2, ← hx1, ← hx2,
    ← hψ x, inv_eq_of_mul_eq_one_right hsG]

theorem not_wrong_plane
    (hθ : (θ co3ZM : G) = s) {sG : G} (hsG : sG * sG = 1)
    (hψ : ∀ x : edgeGroup, sG * θ (x : co3M) * sG⁻¹ = θ (psi x : co3M))
    (hw : ((θ bcbM : G) * sG) ^ 3 = θ (kpM * mc)) : False := by
  have hrels : ∀ r ∈ relsVw, FreeGroup.lift (letterImg θ sG) (FreeGroup.mk r) = 1 := by
    rw [lift_relsVw_iff]
    refine ⟨relsC0_letterImg θ sG, ?_, edge_letterImg θ hsG hψ, ?_⟩
    · rw [letterImg_three]
      exact hsG
    · rw [bcb_letterImg, letterImg_three, hw, theta_mul, wordOf_letterImg θ sG kpWord_letters,
        letterImg_of_ne θ sG (by decide), thetaHom_apply]
  have hgen : closure ((fun i : Fin 7 => (PresentedGroup.of i : Vw)) '' {i | i ≠ 3}) = ⊤ :=
    vwGenerated
  have hrange : (vwLift (letterImg θ sG) hrels).range ≤ (thetaHom θ).range := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, vwLift_of, letterImg_of_ne θ sG hi]
    exact ⟨mGen i, rfl⟩
  obtain ⟨x, hx⟩ := hrange ⟨PresentedGroup.of 3, by rw [vwLift_of]⟩
  rw [letterImg_three, thetaHom_apply] at hx
  have hc : sG * s = s * sG := by
    rw [← hx]
    exact theta_comm_s θ x
  have e := hψ eH
  rw [theta_eH θ hθ, psi_eH, hc, mul_inv_cancel_right] at e
  exact theta_ma_ne_s θ hθ e.symm

theorem plane_relator
    (hθ : (θ co3ZM : G) = s) {sG : G} (hsG : sG * sG = 1)
    (hψ : ∀ x : edgeGroup, sG * θ (x : co3M) * sG⁻¹ = θ (psi x : co3M)) :
    ((θ bcbM : G) * sG) ^ 3 = θ kpM := by
  set u : G := (θ bcbM : G) * sG with hu
  have hμ : ∀ x : edgeGroup, (θ (bcbM * psi x * bcbM⁻¹) : G) = u * θ (x : co3M) * u⁻¹ := by
    intro x
    rw [theta_conj, ← hψ, hu]
    group
  have hs : u * s * u⁻¹ = θ yM := by
    have e := hμ eH
    rw [psi_eH, theta_eH θ hθ] at e
    rw [← e]
    exact congrArg (fun x => (θ x : G)) bcb_facts.2.1
  have hy : u * θ yM * u⁻¹ = θ ma := by
    have e := hμ yH
    rw [psi_yH] at e
    rw [← coe_yH, ← e]
    exact congrArg (fun x => (θ x : G)) bcb_facts.2.2.1
  have ha : u * θ ma * u⁻¹ = s := by
    have e := hμ aH
    rw [psi_aH] at e
    rw [show (θ ma : G) = θ (aH : co3M) from rfl, ← e,
      show ((eH : edgeGroup) : co3M) = me from rfl, me_comm bcbM, mul_inv_cancel_right,
      theta_me θ hθ]
  obtain ⟨k, hk, hku⟩ := exists_cube θ hs hy ha
  have hchain : ∀ x₀ x₁ x₂ : edgeGroup, x₀ * yH = yH * x₀ →
      (x₁ : co3M) = bcbM * psi x₀ * bcbM⁻¹ → (x₂ : co3M) = bcbM * psi x₁ * bcbM⁻¹ →
      bcbM * psi x₂ * bcbM⁻¹ = ((k * x₀ * k⁻¹ : edgeGroup) : co3M) :=
    fun x₀ x₁ x₂ _ e1 e2 =>
      chain_of_conj θ (μ := fun x => bcbM * psi x * bcbM⁻¹) hμ hku x₀ x₁ x₂ e1 e2
  have hkfix : bcbM * psi k * bcbM⁻¹ = k := by
    apply theta_inj θ
    rw [hμ, hku, pow_three]
    group
  rcases (cubeData.1 k hk).1 ⟨hchain, hkfix⟩ with h | h
  · rw [← hku, h]
  · exact (not_wrong_plane θ hθ hsG hψ (by rw [← hu, ← hku, h])).elim

end CFSG.EvenSmallLie.SympSix.Co3Ident
