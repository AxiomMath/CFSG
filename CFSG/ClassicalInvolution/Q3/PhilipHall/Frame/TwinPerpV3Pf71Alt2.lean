module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf49Wk

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Alt2






variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem exists_noncomm_rep (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω)
    (hnab : ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x) :
    ∃ ρ σ : Rep Ω W, ρ.img * σ.img ≠ σ.img * ρ.img := by
  by_contra hcon
  push Not at hcon
  apply hnab
  have hcomm : ∀ x ∈ muDelta Ω W, ∀ y ∈ muDelta Ω W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hx
    obtain ⟨σ, hσ⟩ := exists_rep_of_mem_muDelta hy
    apply Subtype.ext
    show (x : NQuot (W ⊔ OCW W)) * y = y * x
    rw [← hρ, ← hσ]
    exact hcon ρ σ
  have hcenter : ∀ y ∈ muDelta Ω W, ∀ x : ↥(muGroup Ω W), x * y = y * x := by
    intro y hy x
    have hx : x ∈ Subgroup.closure (muDelta Ω W) := by
      rw [closure_muDelta_eq_top]; trivial
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx y hy
    | one => simp
    | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
    | inv a _ ha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [ha]
        _ = y * a⁻¹ := by group
  intro x y
  have hy : y ∈ Subgroup.closure (muDelta Ω W) := by
    rw [closure_muDelta_eq_top]; trivial
  induction hy using Subgroup.closure_induction with
  | mem y hy => exact hcenter y hy x
  | one => simp
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | inv a _ ha =>
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [ha]
      _ = a⁻¹ * x := by group

theorem false_of_alt2_of_noncomm (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {S₀ : Sylow 2 G}
    (hWS₀ : W ≤ (S₀ : Subgroup G))
    (h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S₀ : Subgroup G)) → K ⊓ (S₀ : Subgroup G) ∈ RSet Ω)
    (ρ σ : Rep Ω W) (hnc : ρ.img * σ.img ≠ σ.img * ρ.img) : False := by
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP hW
  have hΩ := hP.hyp
  have hS₀2 : IsPGroup 2 ↥(S₀ : Subgroup G) := S₀.isPGroup'
  have hbig : ∀ τ : Rep Ω W, 4 ≤ Nat.card ↥(τ.K ⊓ (S₀ : Subgroup G)) := by
    intro τ
    have h := Q3CL.Thompson.inf_W_of_mem_D hΩ hW τ.hR τ.hK τ.hRK
    exact le_trans h.2.2.2.1
      (Subgroup.card_le_of_le (h.1 ▸ (inf_le_inf_left τ.K hWS₀ : τ.K ⊓ W ≤ τ.K ⊓ S₀)))
  have hne : ρ.K ≠ σ.K := by
    intro h
    exact hnc (by rw [c.img_eq_of_K_eq σ ρ h.symm])
  have hρ1 := h2 ρ.K ρ.hK (by have := hbig ρ; omega)
  have hσ1 := h2 σ.K σ.hK (by have := hbig σ; omega)
  have hne' : ρ.K ⊓ (S₀ : Subgroup G) ≠ σ.K ⊓ (S₀ : Subgroup G) := by
    intro h
    have hle : ρ.K ⊓ (S₀ : Subgroup G) ≤ σ.K := h ▸ inf_le_left
    exact hne (Sec6Gen.eq_of_le_of_le hΩ ρ.hK σ.hK (hS₀2.to_le inf_le_right) (hbig ρ)
      inf_le_left hle)
  have hab := Q3.Q3CP.l67Gen G Ω hΩ S₀ _ hρ1 _ hσ1 inf_le_right inf_le_right hne'
  have hDρ := Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS₀ hρ1 inf_le_right
  have hDσ := Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hW hWS₀ hσ1 inf_le_right
  have hSρ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ ρ.hK hρ1 inf_le_left
  have hSσ := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ σ.hK hσ1 inf_le_left
  let ρa := Q3CL.T8.mkRep hP hW ρ.hK hDρ hSρ
  let σa := Q3CL.T8.mkRep hP hW σ.hK hDσ hSσ
  have hia : ρa.img = ρ.img := c.img_eq_of_K_eq ρa ρ rfl
  have hib : σa.img = σ.img := c.img_eq_of_K_eq σa σ rfl
  apply hnc
  rw [← hia, ← hib]
  unfold Rep.img
  rw [← piG_mul ρa.r_mem_normalizer σa.r_mem_normalizer,
    ← piG_mul σa.r_mem_normalizer ρa.r_mem_normalizer,
    hab _ ρa.hr _ σa.hr]

theorem false_of_alt2_of_nonabelian (hP : Q3CL.PartIHypG Ω) (hW : W ∈ WSet Ω) {S₀ : Sylow 2 G}
    (hWS₀ : W ≤ (S₀ : Subgroup G))
    (h2 : ∀ K ∈ Ω, 2 < Nat.card ↥(K ⊓ (S₀ : Subgroup G)) → K ⊓ (S₀ : Subgroup G) ∈ RSet Ω)
    (hnab : ¬ ∀ x y : ↥(muGroup Ω W), x * y = y * x) : False := by
  obtain ⟨ρ, σ, h⟩ := exists_noncomm_rep hP hW hnab
  exact false_of_alt2_of_noncomm hP hW hWS₀ h2 ρ σ h

variable {n : ℕ}

theorem v3WAlt2_proved : V3WAlt2 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin S₀ ⟨η, hη, hinv⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hStd, -⟩ := hin
  have hCore := CoreData.of_S hStd.perp.core
  have hPI : Q3CL.PartIHypG (CoreAssembly.conjClass (tightCore R)) := hCore.partIHypG
  have hW : (⨆ U ∈ η, U : Subgroup Y) ∈ WSet (CoreAssembly.conjClass (tightCore R)) :=
    ⟨η, ⟨S₀, hη, hinv⟩, rfl⟩
  have hWS₀ : (⨆ U ∈ η, U : Subgroup Y) ≤ (S₀ : Subgroup Y) :=
    iSup₂_le fun U hU => (hη.1 hU).2
  obtain ⟨e⟩ := hStd.wyl _ hW
  refine false_of_alt2_of_nonabelian hPI hW hWS₀ hcon ?_
  intro habel
  apply s26_coxeterD4_not_comm
  intro u v
  have h1 := habel (e.symm u) (e.symm v)
  calc u * v = e (e.symm u * e.symm v) := by simp
    _ = e (e.symm v * e.symm u) := by rw [h1]
    _ = v * u := by simp

end Alt2

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
