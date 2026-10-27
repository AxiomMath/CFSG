module

public import CFSG.GF2Type.Smith1979.GammaU.Dict3
public import CFSG.LargeExtraspecial.S4FiveA
public import CFSG.GF2Type.Smith1979.GammaU.Step6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.GammaU.Dict

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA Module
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem zmod2_cases' (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem four_le_finrank {W : Submodule (ZMod 2) V12} (hW : ∀ w ∈ W, theta0 w ∈ W) {x y : V12}
    (hx : x ∈ W) (hy : y ∈ W) (h : Viol.F4Indep x y) : 4 ≤ finrank (ZMod 2) W := by
  obtain ⟨hx0, hxy⟩ := h
  have h3 : ∀ v, theta0 (theta0 (theta0 v)) = v := theta0_theta0_theta0
  have hli : LinearIndependent (ZMod 2)
      ![(⟨x, hx⟩ : W), ⟨theta0 x, hW x hx⟩, ⟨y, hy⟩, ⟨theta0 y, hW y hy⟩] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : c 0 • x + c 1 • theta0 x + c 2 • y + c 3 • theta0 y = 0 := by
      have := congrArg Subtype.val hc
      simpa [Fin.sum_univ_four, add_assoc] using this
    have hy23 : c 2 = 0 ∧ c 3 = 0 := by
      rcases zmod2_cases' (c 2) with h2 | h2 <;> rcases zmod2_cases' (c 3) with h3' | h3'
      · exact ⟨h2, h3'⟩
      ·
        exfalso
        rw [h2, h3', zero_smul, add_zero, one_smul] at hc'
        have hty : theta0 y = c 0 • x + c 1 • theta0 x := (Viol.eq_of_add_eq_zero hc').symm
        apply hxy (c 0 + c 1) (c 0)
        have := congrArg (fun v => theta0 (theta0 v)) hty
        rw [h3] at this
        simp only [map_add, map_smul] at this
        rw [h3, theta0_theta0_eq] at this
        rw [this]
        module
      ·
        exfalso
        rw [h2, h3', zero_smul, add_zero, one_smul] at hc'
        exact hxy (c 0) (c 1) (Viol.eq_of_add_eq_zero hc').symm
      ·
        exfalso
        rw [h2, h3', one_smul, one_smul] at hc'
        have hty : y + theta0 y = c 0 • x + c 1 • theta0 x := by
          rw [← sub_eq_zero, vec_sub_eq_add, ← hc']
          abel
        apply hxy (c 1) (c 0 + c 1)
        have := congrArg theta0 hty
        rw [← theta0_theta0_eq, h3, map_add, map_smul, map_smul, theta0_theta0_eq] at this
        rw [this]
        module
    obtain ⟨h2, h3'⟩ := hy23
    rw [h2, h3', zero_smul, zero_smul, add_zero, add_zero] at hc'
    have h01 : c 0 = 0 ∧ c 1 = 0 := by
      rcases zmod2_cases' (c 0) with h0 | h0 <;> rcases zmod2_cases' (c 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · exfalso
        rw [h0, h1, zero_smul, zero_add, one_smul] at hc'
        exact hx0 (by rw [← h3 x, hc', map_zero, map_zero])
      · exfalso
        rw [h0, h1, zero_smul, add_zero, one_smul] at hc'
        exact hx0 hc'
      · exfalso
        rw [h0, h1, one_smul, one_smul] at hc'
        exact hx0 (theta0_fix (Viol.eq_of_add_eq_zero hc').symm)
    intro j
    fin_cases j
    · exact h01.1
    · exact h01.2
    · exact h2
    · exact h3'
  simpa using hli.fintype_card_le_finrank

theorem theta_mem_Vt (H : Hyp4 S g) {θ : S.O} (hθ : θ ∈ S.Mbar) {s : S.O} (hs : s * θ = θ * s)
    {v : S.Qt} (hv : v ∈ Vt S g s) : (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g s := by
  obtain ⟨k₀, rfl⟩ := hθ
  have hle : Vt S g s ≤ (Vt S g s).comap
      (((S.ρ k₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, hsh, rfl⟩
    refine Submodule.subset_span ⟨k₀ * h, ?_, ?_⟩
    · have := conj_mem_Lbar_mul S k₀ hsh
      have hcs : S.ρ k₀ * s * (S.ρ k₀)⁻¹ = s := by rw [← hs, mul_inv_cancel_right]
      rw [hcs, ← mul_assoc] at this
      exact this
    · change ((S.ρ k₀ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
        S.cl (((k₀ * h : S.M) : G) * g * S.z * (((k₀ * h : S.M) : G) * g)⁻¹)
      have hQ := conj_mem_QG' S h.2 H.conj_mem
      rw [show (h : G) * g * S.z * ((h : G) * g)⁻¹ = ((h : G) * g) * S.z * ((h : G) * g)⁻¹ by
        group] at hQ ⊢
      rw [ρ_cl_conj_z S k₀ hQ]
      congr 1
      simp only [Subgroup.coe_mul]
      group
  exact hle hv

theorem theta0_mem_map_Vt (H : Hyp4 S g) {θ : S.O} (hθ : θ ∈ S.Mbar) {φ : S.Qt ≃ₗ[ZMod 2] V12}
    (hc : ThetaCompat φ θ) {s : S.O} (hs : s * θ = θ * s) :
    ∀ w ∈ (Vt S g s).map (φ : S.Qt →ₗ[ZMod 2] V12),
      theta0 w ∈ (Vt S g s).map (φ : S.Qt →ₗ[ZMod 2] V12) := by
  rintro _ ⟨v, hv, rfl⟩
  have h1 := theta_mem_Vt H hθ hs hv
  rcases hc with hc | hc
  · exact ⟨_, h1, by simp [hc]⟩
  · refine ⟨_, theta_mem_Vt H hθ hs h1, ?_⟩
    change φ _ = theta0 (φ v)
    rw [hc, hc, theta0_theta0_theta0]

theorem vecOf_xor_eq {r : Array ℕ} (hr : ∀ x ∈ r, x < 4096) (m : ℕ) :
    vecOf (appN r m ^^^ m) = linOfRows r (vecOf m) + vecOf m := by
  rw [vecOf_xor, vecOf_appN]

section

variable {i : ℕ} (hi : i = 0 ∨ i = 1) {θ : S.O}
  {φ : S.Qt ≃ₗ[ZMod 2] V12} (hφ : NormTr S g θ i φ) (H : Hyp4 S g) (C : Cons311 S g)
  (hw : S.width = 6)
include hi hφ H C hw

theorem hasConfig_of_data {r : Array ℕ} (hr : r ∈ compOf i) {s : S.O}
    (hsr : ∀ y, trEquiv φ (s : S.Qt ≃ₗ[ZMod 2] S.Qt) y = linOfRows r y) (h : S.M)
    (c1 : s ∈ S.Lbar ((h : G) * g))
    (c2 : ∀ l ∈ S.Lbar ((h : G) * g), l * θ * l⁻¹ = θ ∨ l * θ * l⁻¹ = θ⁻¹)
    (c3 : aT S ((h : G) * g) ∈ Dt S g)
    (c4 : ∃ v, (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v = aT S ((h : G) * g))
    (c5a : aT S ((h : G) * g) ≠ aT S g)
    (c5b : aT S ((h : G) * g) ≠ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g))
    (c5c : aT S ((h : G) * g) ≠
      (θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)))
    (c6 : aT S g ∈ Dt S ((h : G) * g))
    (c7 : Nat.card (Subgroup.closure ((S.Lbar g : Set S.O) ∪ (S.Lbar ((h : G) * g) : Set S.O) ∪
      {θ})) = 1152) :
    HasConfig i (Mtr S φ) r := by
  have hcr := canon_of_mem_compOf Certificates.certificate16964 (by omega) hr
  set e := aT S ((h : G) * g) with he
  have H' := H.mul h
  have C' := C.mul h
  have hle' : Ltr S ((h : G) * g) φ ≤ gammaU := Ltr_le_gammaU hφ.isom hφ.theta c2
  have Hy := hyp_tr H' C' hw hφ.isom hle'
  refine ⟨Ltr S ((h : G) * g) φ, codeOf (φ e), ?_, (Dt S ((h : G) * g)).map
    (φ : S.Qt →ₗ[ZMod 2] V12), by rwa [vecOf_codeOf], ⟨_, mem_Ltr.2 ⟨s, c1, rfl⟩, hsr⟩,
    ⟨aT S g, c6, hφ.base⟩, ?_, ?_⟩
  ·
    have hinj : ∀ v w : S.Qt, codeOf (φ v) = codeOf (φ w) → v = w := fun v w h' => by
      apply φ.injective
      rw [← vecOf_codeOf (φ v), h', vecOf_codeOf]
    have hθa : theta0 (vecOf a0) = φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)) ∨
        theta0 (vecOf a0) = φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g))) := by
      rcases hφ.theta with hc | hc
      · left
        rw [hc, hφ.base]
      · right
        rw [hc, hc, hφ.base, theta0_theta0_theta0]
    have hθθa : vecOf a0 + theta0 (vecOf a0) =
        φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g))) ∨
        vecOf a0 + theta0 (vecOf a0) = φ ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) (aT S g)) := by
      rcases hφ.theta with hc | hc
      · left
        rw [hc, hc, hφ.base, theta0_theta0_eq]
      · right
        rw [hc, hφ.base, theta0_theta0_eq]
    rw [mem_colPts]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mem_spanList_iff d0_lt (codeOf_lt _), vecOf_codeOf, ← hφ.dmap]
      exact ⟨e, c3, rfl⟩
    · intro h0
      apply aT_ne_zero H'
      apply φ.injective
      rw [← vecOf_codeOf (φ e), h0, vecOf_zero, map_zero]
    · have hq := q0_vecOf (codeOf (φ e))
      rw [vecOf_codeOf, hφ.isom, he, q_aT H'] at hq
      cases hb : q0b (codeOf (φ e))
      · rfl
      · rw [hb] at hq
        exact absurd hq (by decide)
    · intro h0
      apply c5a
      apply φ.injective
      rw [← vecOf_codeOf (φ e), h0, hφ.base]
    · intro h0
      have hv : φ e = theta0 (vecOf a0) := by
        rw [← vecOf_codeOf (φ e), h0, vecOf_theta0N a0_lt]
      rcases hθa with h1 | h1 <;> rw [h1] at hv
      · exact c5b (φ.injective hv)
      · exact c5c (φ.injective hv)
    · intro h0
      have hv : φ e = vecOf a0 + theta0 (vecOf a0) := by
        rw [← vecOf_codeOf (φ e), h0, vecOf_xor, vecOf_theta0N a0_lt]
      rcases hθθa with h1 | h1 <;> rw [h1] at hv
      · exact c5c (φ.injective hv)
      · exact c5b (φ.injective hv)
    · obtain ⟨v, hv⟩ := c4
      refine ⟨codeOf (φ v), codeOf_lt _, ?_⟩
      apply vecOf_inj (xor_lt (appN_lt hcr.2 _) (codeOf_lt _)) (codeOf_lt _)
      rw [vecOf_xor_eq hcr.2, vecOf_codeOf, vecOf_codeOf, ← hsr, trEquiv_apply_φ, ← vec_sub_eq_add,
        ← map_sub, hv]
  ·
    intro l hl
    obtain ⟨s', hs', rfl⟩ := mem_Ltr.1 hl
    exact tr_mem_Mtr (S.Lbar_le_Mbar _ hs')
  ·
    let f : S.O →* (V12 ≃ₗ[ZMod 2] V12) := (trEquiv φ).toMonoidHom.comp S.O.subtype
    have hf : Function.Injective f := fun a b hab => trS_injective φ hab
    have himg : (Subgroup.closure ((S.Lbar g : Set S.O) ∪ (S.Lbar ((h : G) * g) : Set S.O) ∪
        {θ})).map f = Subgroup.closure ({l | RowsSet (compOf i) l} ∪
          ↑(Ltr S ((h : G) * g) φ) ∪ {trEquiv φ (θ : S.Qt ≃ₗ[ZMod 2] S.Qt)}) := by
      have hA : f '' ↑(S.Lbar g) = {l | RowsSet (compOf i) l} := by
        ext l
        simp only [Set.mem_image, Set.mem_setOf_eq, SetLike.mem_coe]
        rw [← hφ.frame, mem_Ltr]
        rfl
      have hB : f '' ↑(S.Lbar ((h : G) * g)) = ↑(Ltr S ((h : G) * g) φ) := by
        ext l
        simp only [Set.mem_image, SetLike.mem_coe]
        rw [mem_Ltr]
        rfl
      rw [MonoidHom.map_closure, Set.image_union, Set.image_union, Set.image_singleton, hA, hB]
      rfl
    have hcard := Subgroup.card_map_of_injective (K := Subgroup.closure ((S.Lbar g : Set S.O) ∪
      (S.Lbar ((h : G) * g) : Set S.O) ∪ {θ})) hf
    rw [himg, c7] at hcard
    rcases tr_theta hφ.theta with hT | hT
    · rw [hT] at hcard
      exact hcard
    · rw [hT, closure_theta_inv] at hcard
      exact hcard

end

end CFSG.GF2Type.Smith1979.GammaU.Dict
