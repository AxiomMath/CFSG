module

public import CFSG.GF2Type.Smith1979.GammaU.Dict2
public import CFSG.GF2Type.Smith1979.GammaU.Step4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

structure ThetaInputs (S : Setting G) (g : G) (θ : S.O) : Prop where
  mem : θ ∈ S.Mbar
  pow_three : θ ^ 3 = 1
  fix : ∀ v, (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v → v = 0
  canon : ∀ m ∈ S.Mbar, (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) = aT S g →
    m * θ * m⁻¹ = θ ∨ m * θ * m⁻¹ = θ⁻¹
  anti : ∀ s ∈ S.Lbar g, s * θ = θ⁻¹ * s → finrank (ZMod 2) (Vt S g s) ≤ 2
  config : ∀ s ∈ S.Lbar g, s ≠ 1 → s * θ = θ * s → 4 ≤ finrank (ZMod 2) (Vt S g s) →
    ∃ h : S.M, s ∈ S.Lbar ((h : G) * g) ∧
      (∀ l ∈ S.Lbar ((h : G) * g), l * θ * l⁻¹ = θ ∨ l * θ * l⁻¹ = θ⁻¹) ∧
      aT S ((h : G) * g) ∈ Dt S g ∧
      (∃ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = aT S ((h : G) * g)) ∧
      aT S ((h : G) * g) ≠ aT S g ∧
      aT S ((h : G) * g) ≠ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g) ∧
      aT S ((h : G) * g) ≠ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)) ∧
      aT S g ∈ Dt S ((h : G) * g) ∧
      Nat.card (Subgroup.closure ((S.Lbar g : Set S.O) ∪ (S.Lbar ((h : G) * g) : Set S.O) ∪
        {θ})) = 1152
  two : ∃ s₁ ∈ S.Lbar g, ∃ s₂ ∈ S.Lbar g, s₁ ≠ s₂ ∧ s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ s₁ * θ = θ * s₁ ∧
    s₂ * θ = θ * s₂ ∧ 4 ≤ finrank (ZMod 2) (Vt S g s₁) ∧ 4 ≤ finrank (ZMod 2) (Vt S g s₂)

theorem mem_Mtr_iff_rho {φ : S.Qt ≃ₗ[ZMod 2] V12} {u : V12 ≃ₗ[ZMod 2] V12} :
    u ∈ Mtr S φ ↔ ∃ k : S.M, trEquiv φ ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = u := by
  rw [mem_Mtr]
  constructor
  · rintro ⟨m, ⟨k, rfl⟩, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨S.ρ k, ⟨k, rfl⟩, rfl⟩

theorem tr_rho_a0 {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
    (H : Hyp4 S g) (k : S.M) :
    trEquiv φ ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (vecOf a0) = φ (aT S ((k : G) * g)) := by
  rw [← hφ.base, trEquiv_apply_φ, aT, ρ_cl_conj_z S k H.conj_mem]

theorem exists_realize {i : ℕ} (hi : i = 0 ∨ i = 1) {θ : S.O}
    {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ) {r : Array ℕ} (hr : r ∈ compOf i) :
    ∃ s ∈ S.Lbar g, ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y := by
  obtain ⟨l, hl⟩ := realized_of_mem_compOf Certificates.certificate16966 (by omega) hr
  obtain ⟨s, hs, hsl⟩ := mem_Ltr.1 ((hφ.frame l).2 ⟨r, hr, hl⟩)
  exact ⟨s, hs, fun y => by rw [hsl, hl]⟩

theorem frame_le_Mtr {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
    {l : V12 ≃ₗ[ZMod 2] V12} (hl : RowsSet (compOf i) l) : l ∈ Mtr S φ := by
  obtain ⟨s, hs, rfl⟩ := mem_Ltr.1 ((hφ.frame l).2 hl)
  exact tr_mem_Mtr (S.Lbar_le_Mbar g hs)

theorem mem_Lbar_of_inFrame {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
    {r : Array ℕ} {s : S.O} (hsr : ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y)
    (k : S.M) (hin : Viol.InFrame (compOf i)
      (trEquiv φ ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) r) :
    s ∈ S.Lbar ((k : G) * g) := by
  obtain ⟨r', hr', hrr⟩ := hin
  set u := trEquiv φ ((S.ρ k : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hrows : RowsSet (compOf i) (u⁻¹ * trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) * u) :=
    ⟨r', hr', fun x => by rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsr, hrr]⟩
  obtain ⟨s', hs', hs'e⟩ := mem_Ltr.1 ((hφ.frame _).2 hrows)
  have heq : s' = (S.ρ k)⁻¹ * s * S.ρ k := by
    apply Subtype.ext
    apply (trEquiv φ).injective
    rw [hs'e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, u]
  rw [mem_Lbar_mul_iff, ← heq]
  exact hs'

theorem mem_Vt_of_inFrame {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ)
    (H : Hyp4 S g) {r : Array ℕ} {s : S.O}
    (hsr : ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y) {u : V12 ≃ₗ[ZMod 2] V12}
    (hu : u ∈ Mtr S φ) (hin : Viol.InFrame (compOf i) u r) :
    φ.symm (u (vecOf a0)) ∈ Vt S g s := by
  obtain ⟨k, rfl⟩ := mem_Mtr_iff_rho.1 hu
  have hs := mem_Lbar_of_inFrame hφ hsr k hin
  rw [tr_rho_a0 hφ H, LinearEquiv.symm_apply_apply]
  exact Submodule.subset_span ⟨k, hs, by rw [aT, mul_assoc]⟩

theorem three_le_finrank {W : Submodule (ZMod 2) V12} {x y w : V12} (hx : x ∈ W) (hy : y ∈ W)
    (hw : w ∈ W) (h : Viol.F2Indep3 x y w) : 3 ≤ finrank (ZMod 2) W := by
  have hli : LinearIndependent (ZMod 2) ![(⟨x, hx⟩ : W), ⟨y, hy⟩, ⟨w, hw⟩] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • x + c 1 • y + c 2 • w = 0 := by
      have := congrArg Subtype.val hc
      simpa [Fin.sum_univ_three] using this
    obtain ⟨h0, h1, h2⟩ := h _ _ _ hc'
    intro j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  simpa using hli.fintype_card_le_finrank

theorem finrank_map_Vt (φ : S.Qt ≃ₗ[ZMod 2] V12) (s : S.O) :
    finrank (ZMod 2) ((Vt S g s).map (φ : S.Qt →ₗ[ZMod 2] V12)) = finrank (ZMod 2) (Vt S g s) :=
  LinearEquiv.finrank_map_eq φ _

theorem mem_map_Vt_of_inFrame {i : ℕ} {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12}
    (hφ : NormTr S g θ i φ) (H : Hyp4 S g) {r : Array ℕ} {s : S.O}
    (hsr : ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y) {u : V12 ≃ₗ[ZMod 2] V12}
    (hu : u ∈ Mtr S φ) (hin : Viol.InFrame (compOf i) u r) :
    u (vecOf a0) ∈ (Vt S g s).map (φ : S.Qt →ₗ[ZMod 2] V12) :=
  ⟨_, mem_Vt_of_inFrame hφ H hsr hu hin, by simp⟩

theorem trS_injective (φ : S.Qt ≃ₗ[ZMod 2] V12) :
    Function.Injective fun s : S.O => trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  fun _ _ h => Subtype.ext ((trEquiv φ).injective h)

theorem inverts_of_anti {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hθ : ThetaCompat φ θ) {s : S.O}
    (ha : ∀ x, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (theta0 x) =
      theta0 (theta0 (trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x))) :
    s * θ = θ⁻¹ * s := by
  set X := trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hX : X * thetaU = thetaU⁻¹ * X := LinearEquiv.ext fun x => by
    simp only [LinearEquiv.mul_apply, thetaU_apply, thetaU_inv_apply, ha]
  apply trS_injective φ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  change X * trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) = (trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt))⁻¹ * X
  rcases tr_theta hθ with hT | hT
  · rw [hT, hX]
  · rw [hT, inv_inv]
    calc X * thetaU⁻¹ = X * thetaU⁻¹ * X⁻¹ * X := by group
      _ = (X * thetaU * X⁻¹)⁻¹ * X := by group
      _ = thetaU * X := by
        rw [show X * thetaU * X⁻¹ = thetaU⁻¹ by rw [hX, mul_inv_cancel_right], inv_inv]

theorem comm_of_unitary {θ : S.O} {φ : S.Qt ≃ₗ[ZMod 2] V12} (hθ : ThetaCompat φ θ) {s : S.O}
    (hu : ∀ x, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (theta0 x) =
      theta0 (trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x)) :
    s * θ = θ * s := by
  set X := trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt)
  have hX : X * thetaU = thetaU * X := LinearEquiv.ext fun x => by
    simp only [LinearEquiv.mul_apply, thetaU_apply, hu]
  apply trS_injective φ
  simp only [Subgroup.coe_mul, map_mul]
  change X * trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) = trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) * X
  rcases tr_theta hθ with hT | hT
  · rw [hT, hX]
  · rw [hT]
    calc X * thetaU⁻¹ = (thetaU * X⁻¹)⁻¹ := by group
      _ = (X⁻¹ * thetaU)⁻¹ := by
        congr 1
        calc thetaU * X⁻¹ = X⁻¹ * (X * thetaU) * X⁻¹ := by group
          _ = X⁻¹ * thetaU := by rw [hX]; group
      _ = thetaU⁻¹ * X := by group

section

variable {i : ℕ} (hi : i = 0 ∨ i = 1) {θ : S.O}
  {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ) (H : Hyp4 S g) (T : ThetaInputs S g θ)
include hi hφ H T

theorem not_d1 {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hN : N ≤ Mtr S φ) :
    ¬ ∃ h ∈ N, h (vecOf a0) = vecOf a0 ∧ ∃ r ∈ compOf i,
      ¬ ∃ r' ∈ compOf i, ∀ x, h (linOfRows r (h⁻¹ x)) = linOfRows r' x := by
  rintro ⟨h, hhN, hfix, r, hr, hno⟩
  obtain ⟨k, rfl⟩ := mem_Mtr_iff_rho.1 (hN hhN)
  rw [tr_rho_a0 hφ H, ← hφ.base] at hfix
  have hcl := φ.injective hfix
  have hL := Lbar_eq_of_cl_eq S H.conj_mem H.conj_ne (conj_mem_QG' S k.2 H.conj_mem) hcl
  obtain ⟨s, hs, hsr⟩ := exists_realize hi hφ hr
  have hs' : S.ρ k * s * (S.ρ k)⁻¹ ∈ S.Lbar g := by
    rw [← hL]
    exact conj_mem_Lbar_mul S k hs
  obtain ⟨r', hr', hrr⟩ := (hφ.frame _).1 (mem_Ltr.2 ⟨_, hs', rfl⟩)
  refine hno ⟨r', hr', fun x => ?_⟩
  rw [← hrr]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, LinearEquiv.mul_apply, hsr]

theorem step4Hyp_Mtr : Step4Hyp i (Mtr S φ) where
  frame := fun _ hl => frame_le_Mtr hφ hl
  theta := thetaU_mem_Mtr hφ.theta T.mem
  noViol := by
    intro N hN hV
    rcases hV with h1 | ⟨r, hr, -, hrH, -⟩ | ⟨r, hr, ha, u₁, hu₁, u₂, hu₂, u₃, hu₃, hi₁, hi₂, hi₃, hind⟩
    · exact not_d1 hi hφ H T hN h1
    · exact hrH hr
    · obtain ⟨s, hs, hsr⟩ := exists_realize hi hφ hr
      have hanti : s * θ = θ⁻¹ * s := inverts_of_anti hφ.theta fun x => by
        rw [hsr, hsr, ha]
      have h3 := three_le_finrank (mem_map_Vt_of_inFrame hφ H hsr (hN hu₁) hi₁)
        (mem_map_Vt_of_inFrame hφ H hsr (hN hu₂) hi₂) (mem_map_Vt_of_inFrame hφ H hsr (hN hu₃) hi₃)
        hind
      rw [finrank_map_Vt] at h3
      have := T.anti s hs hanti
      omega

end

end CFSG.GF2Type.Smith1979.GammaU.Dict
