module

public import CFSG.GH74.GLS.LU.Local.SL2Aux
public import CFSG.GH74.GLS.LU.Local.Gen
public import CFSG.GH74.GLS.LU.Local.Core3

public section

open Matrix CFSG.Semidihedral.OddFieldSL2 CFSG.GH74.GLS.LU.Local.SL2 Subgroup

namespace CFSG.GH74.GLS.LU.Local.SL2

variable {F : Type} [Field F]

theorem cayley2 (M : Matrix (Fin 2) (Fin 2) F) :
    M * M = (M 0 0 + M 1 1) • M - M.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem trace_zero_of_sq (M : Matrix (Fin 2) (Fin 2) F) (hd : M.det = 1)
    (hM : M * M = -1) : M 0 0 + M 1 1 = 0 := by
  have h := cayley2 M
  rw [hM, hd] at h
  have h1 : (M 0 0 + M 1 1) • M = 0 := by
    calc (M 0 0 + M 1 1) • M = ((M 0 0 + M 1 1) • M - (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F)) +
        (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by abel
      _ = -1 + (1 : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by rw [← h]
      _ = 0 := by simp
  by_contra hne
  have hM0 : M = 0 := by
    have := congrArg (fun N => (M 0 0 + M 1 1)⁻¹ • N) h1
    simpa [smul_smul, inv_mul_cancel₀ hne] using this
  rw [hM0] at hd
  simp at hd


theorem exists_order_three (h2 : (2 : F) ≠ 0) (A B : Matrix (Fin 2) (Fin 2) F)
    (hAd : A.det = 1) (hBd : B.det = 1)
    (hA : A * A = -1) (hB : B * B = -1) (hBA : B * A = -(A * B)) :
    ∃ G : Matrix (Fin 2) (Fin 2) F, G.det = 1 ∧ G * G * G = 1 ∧ G ≠ 1 ∧ G * A = (A * B) * G ∧
      G * B = A * G := by
  set C := A * B with hC
  have hCC : C * C = -1 := by
    calc C * C = A * (B * A) * B := by rw [hC]; noncomm_ring
      _ = A * (-(A * B)) * B := by rw [hBA]
      _ = -((A * A) * (B * B)) := by noncomm_ring
      _ = -1 := by rw [hA, hB]; noncomm_ring
  have hAC : A * C = -B := by
    calc A * C = (A * A) * B := by rw [hC]; noncomm_ring
      _ = -B := by rw [hA]; noncomm_ring
  have hCA : C * A = B := by
    calc C * A = A * (B * A) := by rw [hC]; noncomm_ring
      _ = A * (-(A * B)) := by rw [hBA]
      _ = -((A * A) * B) := by noncomm_ring
      _ = B := by rw [hA]; noncomm_ring
  have hBC : B * C = A := by
    calc B * C = (B * A) * B := by rw [hC]; noncomm_ring
      _ = (-(A * B)) * B := by rw [hBA]
      _ = -(A * (B * B)) := by noncomm_ring
      _ = A := by rw [hB]; noncomm_ring
  have hCB : C * B = -A := by
    calc C * B = A * (B * B) := by rw [hC]; noncomm_ring
      _ = -A := by rw [hB]; noncomm_ring
  have hBA' : B * A = -C := hBA
  have trA := trace_zero_of_sq A hAd hA
  have trB := trace_zero_of_sq B hBd hB
  have trC : C 0 0 + C 1 1 = 0 := by
    have h1 : Matrix.trace (B * A) = Matrix.trace (A * B) := Matrix.trace_mul_comm B A
    rw [hBA, Matrix.trace_neg] at h1
    have h3 : (2 : F) * Matrix.trace C = 0 := by
      rw [hC]; linear_combination -h1
    have := (mul_eq_zero.mp h3).resolve_left h2
    rwa [Matrix.trace_fin_two] at this
  obtain ⟨h, hh⟩ : ∃ h : F, 2 * h = 1 := ⟨(2 : F)⁻¹, mul_inv_cancel₀ h2⟩
  set S : Matrix (Fin 2) (Fin 2) F := A + B + C with hS
  have hS2 : S * S = -(1 + 1 + 1) := by
    have e : S * S = A * A + A * B + A * C + B * A + B * B + B * C + C * A + C * B + C * C := by
      rw [hS]; noncomm_ring
    rw [e, hA, ← hC, hAC, hBA', hB, hBC, hCA, hCB, hCC]
    abel
  set X : Matrix (Fin 2) (Fin 2) F := S - 1 with hX
  have hXX : X * X = (-2 : F) • (1 : Matrix (Fin 2) (Fin 2) F) + (-2 : F) • S := by
    calc X * X = S * S - S - S + 1 := by rw [hX]; noncomm_ring
      _ = _ := by rw [hS2]; module
  set G : Matrix (Fin 2) (Fin 2) F := h • X with hG
  have hGG : G * G = -G - 1 := by
    have e1 : G * G = (h * h * (-2)) • (1 : Matrix (Fin 2) (Fin 2) F) + (h * h * (-2)) • S := by
      rw [hG, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hXX]
      module
    have hh2 : h * h * (-2) = -h := by linear_combination (-h) * hh
    have e2 : -G - 1 = (-h) • S + (h - 1) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hG, hX]; module
    rw [e1, e2, hh2, show h - 1 = -h by linear_combination hh]
    abel
  have hG3 : G * G * G = 1 := by
    calc G * G * G = (-G - 1) * G := by rw [hGG]
      _ = -(G * G) - G := by noncomm_ring
      _ = 1 := by rw [hGG]; noncomm_ring
  have htrG : G 0 0 + G 1 1 = -1 := by
    have : Matrix.trace G = -1 := by
      rw [hG, Matrix.trace_smul, hX, hS, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add,
        Matrix.trace_fin_two A, Matrix.trace_fin_two B, Matrix.trace_fin_two C, trA, trB, trC]
      simp
      linear_combination hh
    rwa [Matrix.trace_fin_two] at this
  have hdetG : G.det = 1 := by
    have h1 := cayley2 G
    rw [hGG, htrG] at h1
    have h3 := congrFun (congrFun h1 0) 0
    simp [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq] at h3
    linear_combination -h3
  have hGA : G * A = C * G := by
    have e1 : G * A = h • (A * A + B * A + C * A - A) := by
      rw [hG, hX, hS, Matrix.smul_mul]; congr 1; noncomm_ring
    have e2 : C * G = h • (C * A + C * B + C * C - C) := by
      rw [hG, hX, hS, Matrix.mul_smul]; congr 1; noncomm_ring
    rw [e1, e2, hA, hBA', hCA, hCB, hCC]
    module
  have hGB : G * B = A * G := by
    have e1 : G * B = h • (A * B + B * B + C * B - B) := by
      rw [hG, hX, hS, Matrix.smul_mul]; congr 1; noncomm_ring
    have e2 : A * G = h • (A * A + A * B + A * C - A) := by
      rw [hG, hX, hS, Matrix.mul_smul]; congr 1; noncomm_ring
    rw [e1, e2, hB, hCB, hA, hAC, ← hC]
    module
  have hG1 : G ≠ 1 := by
    intro hG1
    rw [hG1, one_mul, mul_one] at hGA
    have hAB : A = A * B := hGA
    have h6 : A * A = A * A * B := by
      calc A * A = A * (A * B) := by rw [← hAB]
        _ = A * A * B := by rw [mul_assoc]
    rw [hA] at h6
    have h7 : B = 1 := by
      have : (-1 : Matrix (Fin 2) (Fin 2) F) * (B - 1) = 0 := by
        calc (-1 : Matrix (Fin 2) (Fin 2) F) * (B - 1) = (-1) * B - (-1) := by noncomm_ring
          _ = 0 := by rw [← h6]; noncomm_ring
      have h8 : B - 1 = 0 := by
        have := congrArg (fun N => (-1 : Matrix (Fin 2) (Fin 2) F) * N) this
        simpa using this
      exact sub_eq_zero.mp h8
    rw [h7] at hB
    have h9 := congrFun (congrFun hB 0) 0
    simp at h9
    apply h2
    linear_combination h9
  exact ⟨G, hdetG, hG3, hG1, hGA, hGB⟩


section Q8

theorem q8_gens (h2 : (2 : F) ≠ 0) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F))
    (φ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup 2) :
    ∃ α β : SpecialLinearGroup (Fin 2) F, α ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ∧
      β ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ∧ α * α = minusIdentity F ∧
      β * β = minusIdentity F ∧ β * α = α * β * minusIdentity F ∧
      ∀ x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), x ∈ Subgroup.closure ({α, β} : Set _) := by
  set a₁ : QuaternionGroup 2 := QuaternionGroup.a 1 with ha₁
  set b₁ : QuaternionGroup 2 := QuaternionGroup.xa 0 with hb₁
  have hz₀ : ((φ.symm (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) :
      ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F) = minusIdentity F := by
    apply (orderOf_eq_two_iff F h2 _).mp
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_a_n (n := 2)
  have haa : a₁ * a₁ = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by decide
  have hbb : b₁ * b₁ = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by decide
  have hba : b₁ * a₁ = a₁ * b₁ * QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by decide
  set α : SpecialLinearGroup (Fin 2) F :=
    ((φ.symm a₁ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F) with hα
  set β : SpecialLinearGroup (Fin 2) F :=
    ((φ.symm b₁ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F) with hβ
  refine ⟨α, β, (φ.symm a₁).2, (φ.symm b₁).2, ?_, ?_, ?_, ?_⟩
  · rw [← hz₀, ← haa, map_mul]; rfl
  · rw [← hz₀, ← hbb, map_mul]; rfl
  · have h := congrArg (fun w : QuaternionGroup 2 =>
      ((φ.symm w : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F)) hba
    simp only [map_mul, Subgroup.coe_mul] at h
    rw [← hz₀]; exact h
  · intro x hx
    have key : ∀ w : QuaternionGroup 2, ((φ.symm w : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
        SpecialLinearGroup (Fin 2) F) ∈ Subgroup.closure ({α, β} : Set _) := by
      have hαm : α ∈ Subgroup.closure ({α, β} : Set _) := Subgroup.subset_closure (by simp)
      have hβm : β ∈ Subgroup.closure ({α, β} : Set _) := Subgroup.subset_closure (by simp)
      have e : ∀ w₁ w₂ : QuaternionGroup 2, ((φ.symm (w₁ * w₂) : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
          SpecialLinearGroup (Fin 2) F) = ((φ.symm w₁ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
          SpecialLinearGroup (Fin 2) F) * ((φ.symm w₂ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
          SpecialLinearGroup (Fin 2) F) := fun w₁ w₂ => by rw [map_mul]; rfl
      intro w
      have hw : ∀ w, w = 1 ∨ w = a₁ ∨ w = a₁ * a₁ ∨ w = a₁ * a₁ * a₁ ∨ w = b₁ ∨ w = b₁ * a₁ ∨
          w = b₁ * a₁ * a₁ ∨ w = b₁ * a₁ * a₁ * a₁ := by decide
      rcases hw w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp only [map_one, Subgroup.coe_one]; exact Subgroup.one_mem _
      · exact hαm
      · rw [e]; exact Subgroup.mul_mem _ hαm hαm
      · rw [e, e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hαm hαm) hαm
      · exact hβm
      · rw [e]; exact Subgroup.mul_mem _ hβm hαm
      · rw [e, e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hβm hαm) hαm
      · rw [e, e, e]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hβm hαm) hαm) hαm
    have := key (φ ⟨x, hx⟩)
    simpa using this

end Q8


section Q8Aut

theorem card_mulAut_q8_le : Nat.card (MulAut (QuaternionGroup 2)) ≤ 24 := by
  classical
  let S : Finset (QuaternionGroup 2 × QuaternionGroup 2) :=
    Finset.univ.filter (fun p => p.1 * p.1 = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) ∧
      p.2 * p.2 = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) ∧
      p.2 * p.1 = p.1 * p.2 * QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)))
  have hS : S.card = 24 := by decide
  have hz : ∀ ρ : MulAut (QuaternionGroup 2),
      ρ (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) = QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by
    intro ρ
    have h1 : ρ (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) *
        ρ (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) = 1 := by
      rw [← map_mul]
      have : (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) : QuaternionGroup 2) *
          QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) = 1 := by decide
      rw [this, map_one]
    have h2 : ρ (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) ≠ 1 := by
      intro h
      have := ρ.injective (h.trans (map_one ρ).symm)
      revert this; decide
    revert h1 h2
    generalize ρ (QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2))) = w
    revert w; decide
  let f : MulAut (QuaternionGroup 2) → ↥S := fun ρ =>
    ⟨(ρ (QuaternionGroup.a 1), ρ (QuaternionGroup.xa 0)), by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← map_mul]
        have : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
            QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by decide
        rw [this, hz]
      · rw [← map_mul]
        have : (QuaternionGroup.xa 0 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
            QuaternionGroup.a ((2 : ℕ) : ZMod (2 * 2)) := by decide
        rw [this, hz]
      · rw [← map_mul, ← map_mul, ← hz ρ, ← map_mul]
        congr 1⟩
  have hf : Function.Injective f := by
    intro ρ₁ ρ₂ h
    have h1 : ρ₁ (QuaternionGroup.a 1) = ρ₂ (QuaternionGroup.a 1) := congrArg (fun x => x.1.1) h
    have h2 : ρ₁ (QuaternionGroup.xa 0) = ρ₂ (QuaternionGroup.xa 0) := congrArg (fun x => x.1.2) h
    ext w
    have hw : ∀ w : QuaternionGroup 2, w = 1 ∨ w = QuaternionGroup.a 1 ∨
        w = QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.a 1 * QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨ w = QuaternionGroup.xa 0 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 * QuaternionGroup.a 1 ∨
        w = QuaternionGroup.xa 0 * QuaternionGroup.a 1 * QuaternionGroup.a 1 * QuaternionGroup.a 1 := by
      decide
    rcases hw w with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [map_mul, map_one, h1, h2]
  calc Nat.card (MulAut (QuaternionGroup 2)) ≤ Nat.card ↥S := Nat.card_le_card_of_injective f hf
    _ = 24 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hS]

end Q8Aut


section Q8Norm

theorem q8_normalizer (h2 : (2 : F) ≠ 0) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F))
    (φ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup 2) :
    ∃ g : SpecialLinearGroup (Fin 2) F,
      g ∈ normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) : Set (SpecialLinearGroup (Fin 2) F)) ∧
        orderOf g = 3 := by
  obtain ⟨α, β, hαP, hβP, hαα, hββ, hβα, hgen⟩ := q8_gens h2 P φ
  have hneg : ((minusIdentity F : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = -1 := by
    rw [minusIdentity_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
  have hA : (α : Matrix (Fin 2) (Fin 2) F) * α = -1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hαα
    simpa [hneg] using this
  have hB : (β : Matrix (Fin 2) (Fin 2) F) * β = -1 := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hββ
    simpa [hneg] using this
  have hBA : (β : Matrix (Fin 2) (Fin 2) F) * α = -((α : Matrix (Fin 2) (Fin 2) F) * β) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hβα
    simpa [hneg] using this
  obtain ⟨G, hGd, hG3, hG1, hGA, hGB⟩ := exists_order_three h2 _ _ α.2 β.2 hA hB hBA
  obtain ⟨g, hg3', hg1, hgα, hgβ⟩ : ∃ g : SpecialLinearGroup (Fin 2) F, g * g * g = 1 ∧ g ≠ 1 ∧
      g * α = (α * β) * g ∧ g * β = α * g :=
    ⟨⟨G, hGd⟩, Subtype.ext hG3, fun h => hG1 (congrArg (fun x : SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) h), Subtype.ext hGA, Subtype.ext hGB⟩
  have hg3 : g ^ 3 = 1 := by
    rw [pow_succ, pow_two]; exact hg3'
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hginv : g⁻¹ = g * g := by
    have : g * (g * g) = 1 := by rw [← mul_assoc]; exact hg3'
    exact inv_eq_of_mul_eq_one_right this
  have hαβP : α * β ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := Subgroup.mul_mem _ hαP hβP
  have hconj : ∀ x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), g * x * g⁻¹ ∈
      (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    intro x hx
    have hx' := hgen x hx
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈
      (P : Subgroup (SpecialLinearGroup (Fin 2) F))) ?_ ?_ ?_ ?_ hx'
    · intro y hy
      have hy' : y = α ∨ y = β := by simpa using hy
      rcases hy' with h | h
      · have : g * y * g⁻¹ = α * β := by
          rw [h, hgα]; group
        rw [this]; exact hαβP
      · have : g * y * g⁻¹ = α := by
          rw [h, hgβ]; group
        rw [this]; exact hαP
    · simp
    · intro y z _ _ hy hz
      have : g * (y * z) * g⁻¹ = (g * y * g⁻¹) * (g * z * g⁻¹) := by group
      rw [this]; exact Subgroup.mul_mem _ hy hz
    · intro y _ hy
      have : g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ := by group
      rw [this]; exact Subgroup.inv_mem _ hy
  refine ⟨g, ?_, hgord⟩
  refine mem_normalizer_iff.mpr (fun x => ⟨hconj x, fun hx => ?_⟩)
  have h1 := hconj _ hx
  have h2 := hconj _ h1
  have : x = g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ := by
    have e : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * x * (g * g * g)⁻¹ := by group
    rw [e, hg3']; group
  rw [this]; exact h2

end Q8Norm


section Q8Final

omit [Field F] in
theorem normalizerMonoidHom_coe' {M : Type} [Group M] (K : Subgroup M) (c : normalizer (K : Set M)) (x : ↥K) :
    ((K.normalizerMonoidHom c x : ↥K) : M) = (c : M) * x * (c : M)⁻¹ := by
  simp

variable [Finite F]

omit [Finite F] in
theorem eq_one_or_minus_of_mem_center {n : SpecialLinearGroup (Fin 2) F}
    (hc : n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : n = 1 ∨ n = minusIdentity F := by
  obtain ⟨r, hr, hrs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr' : (r - 1) * (r + 1) = 0 := by
    have : r ^ 2 = 1 := by simpa using hr
    linear_combination this
  rcases mul_eq_zero.mp hr' with h | h
  · left
    have : r = 1 := by linear_combination h
    apply Subtype.ext
    rw [← hrs, this]; simp
  · right
    have : r = -1 := by linear_combination h
    apply Subtype.ext
    rw [← hrs, this, minusIdentity_matrix]

theorem ker_normalizerMonoidHom_card_le (hodd : Odd (Nat.card F))
    (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) :
    Nat.card ↥((P : Subgroup (SpecialLinearGroup (Fin 2) F)).normalizerMonoidHom).ker ≤ 2 := by
  have h2 := two_ne_zero_of_odd_card F hodd
  set 𝔥 := (P : Subgroup (SpecialLinearGroup (Fin 2) F)).normalizerMonoidHom with h𝔥
  have hzp : Nat.card ↥(zpowers (minusIdentity F)) = 2 := by
    rw [Nat.card_zpowers]; exact minusIdentity_orderOf F h2
  have hmem : ∀ k : ↥𝔥.ker, ((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
      Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F) ∈ zpowers (minusIdentity F) := by
    intro k
    have hk := k.2
    rw [MonoidHom.mem_ker] at hk
    have hcomm : ∀ y ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)),
        ((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
          Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F) * y =
        y * ((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
          Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F) := by
      intro y hy
      have h1 := congrArg (fun φ : MulAut ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) =>
        ((φ ⟨y, hy⟩ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F)) hk
      have e : ((𝔥 k ⟨y, hy⟩ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
          SpecialLinearGroup (Fin 2) F) =
          ((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
            Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F) * y *
          ((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
            Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F)⁻¹ := by
        exact normalizerMonoidHom_coe' _ _ _
      simp only [e, MulAut.one_apply] at h1
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hc := cent_sylow_le_center hodd P hcomm
    rcases eq_one_or_minus_of_mem_center hc with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers _
  have hinj : Function.Injective (fun k : ↥𝔥.ker =>
      (⟨((k : ↥(normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) :
        Set (SpecialLinearGroup (Fin 2) F)))) : SpecialLinearGroup (Fin 2) F), hmem k⟩ :
        ↥(zpowers (minusIdentity F)))) := by
    intro k₁ k₂ h
    have h' := congrArg (fun x : ↥(zpowers (minusIdentity F)) => (x : SpecialLinearGroup (Fin 2) F)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card ↥𝔥.ker ≤ Nat.card ↥(zpowers (minusIdentity F)) := Nat.card_le_card_of_injective _ hinj
    _ = 2 := hzp



theorem aut_sylow_odd_q8 (hodd : Odd (Nat.card F)) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F))
    (φ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup 2)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα : Odd (orderOf α))
    (hQ : ∀ x, x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ↔
      α x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
    ∃ n ∈ normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) : Set (SpecialLinearGroup (Fin 2) F)),
      ∀ x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), α x = n * x * n⁻¹ := by
  have h2 := two_ne_zero_of_odd_card F hodd
  obtain ⟨g, hgN, hgord⟩ := q8_normalizer h2 P φ
  set Q : Subgroup (SpecialLinearGroup (Fin 2) F) := (P : Subgroup (SpecialLinearGroup (Fin 2) F)) with hQdef
  set ρ : MulAut ↥Q := resAut Q α hQ with hρ
  have hρodd : Odd (orderOf ρ) := Odd.of_dvd_nat hα (resAut_orderOf_dvd Q α hQ)
  have hQcard : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hAut : Nat.card (MulAut ↥Q) ≤ 24 := by
    rw [Nat.card_congr (MulAut.congr φ).toEquiv]
    exact card_mulAut_q8_le
  have hN24 : 24 ≤ Nat.card ↥(normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) := by
    have h8 : 8 ∣ Nat.card ↥(normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) := by
      rw [← hQcard]; exact Subgroup.card_dvd_of_le (Subgroup.le_normalizer)
    have h3 : 3 ∣ Nat.card ↥(normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) := by
      have := Subgroup.orderOf_dvd_natCard (normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) hgN
      rwa [hgord] at this
    have h24 : 24 ∣ Nat.card ↥(normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3
    exact Nat.le_of_dvd Nat.card_pos h24
  have hker := ker_normalizerMonoidHom_card_le hodd P
  have hprod : Nat.card ↥Q.normalizerMonoidHom.ker * Nat.card ↥Q.normalizerMonoidHom.range =
      Nat.card ↥(normalizer (Q : Set (SpecialLinearGroup (Fin 2) F))) := by
    rw [← Q.normalizerMonoidHom.ker.card_mul_index, Subgroup.index_ker]
  have hrange : 12 ≤ Nat.card ↥Q.normalizerMonoidHom.range := by
    by_contra hlt
    push Not at hlt
    nlinarith
  have hidx : Q.normalizerMonoidHom.range.index ≤ 2 := by
    have := Q.normalizerMonoidHom.range.card_mul_index
    by_contra hgt
    push Not at hgt
    nlinarith
  have hρH : ρ ∈ Q.normalizerMonoidHom.range := by
    have hpos : 0 < Q.normalizerMonoidHom.range.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rcases (by omega : Q.normalizerMonoidHom.range.index = 1 ∨ Q.normalizerMonoidHom.range.index = 2) with h1 | h2'
    · rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top _
    · have hn : Q.normalizerMonoidHom.range.Normal := Subgroup.normal_of_index_eq_two h2'
      have hsq : ρ ^ Q.normalizerMonoidHom.range.index ∈ Q.normalizerMonoidHom.range :=
        Subgroup.pow_index_mem _ ρ
      rw [h2'] at hsq
      obtain ⟨k, hk⟩ := hρodd
      have hr : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
      have : ρ = (ρ ^ 2) ^ (k + 1) := by
        rw [← pow_mul]
        have e : 2 * (k + 1) = orderOf ρ + 1 := by omega
        rw [e, pow_succ, hr, one_mul]
      rw [this]
      exact Subgroup.pow_mem _ hsq _
  obtain ⟨⟨n, hn⟩, hnρ⟩ := hρH
  refine ⟨n, hn, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥Q => ((φ ⟨x, hx⟩ : ↥Q) : SpecialLinearGroup (Fin 2) F)) hnρ
  simp only [hρ, resAut_apply] at h1
  rw [normalizerMonoidHom_coe'] at h1
  exact h1.symm

end Q8Final


section Final

variable [Finite F]

theorem aut_sylow_odd_large (P : Sylow 2 (SpecialLinearGroup (Fin 2) F)) {j : ℕ} (hj : 2 ≤ j)
    (φ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup (2 ^ j))
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα : Odd (orderOf α))
    (hQ : ∀ x, x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ↔
      α x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
    ∀ x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), α x = x := by
  set ρ := resAut (P : Subgroup (SpecialLinearGroup (Fin 2) F)) α hQ with hρ
  have hρodd : Odd (orderOf ρ) := Odd.of_dvd_nat hα (resAut_orderOf_dvd _ α hQ)
  have h1 : (MulAut.congr φ ρ) ^ (orderOf ρ) = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h2 := aut_odd_eq_one hj (MulAut.congr φ ρ) hρodd h1
  have h3 : ρ = 1 := (MulAut.congr φ).injective (by rw [h2, map_one])
  intro x hx
  have := congrArg (fun r : MulAut ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) =>
    ((r ⟨x, hx⟩ : ↥(P : Subgroup (SpecialLinearGroup (Fin 2) F))) : SpecialLinearGroup (Fin 2) F)) h3
  simpa [hρ, resAut_apply] using this

theorem aut_sylow_odd (hodd : Odd (Nat.card F)) (P : Sylow 2 (SpecialLinearGroup (Fin 2) F))
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) (hα : Odd (orderOf α))
    (hQ : ∀ x, x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ↔
      α x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F))) :
    ∃ n ∈ normalizer ((P : Subgroup (SpecialLinearGroup (Fin 2) F)) : Set (SpecialLinearGroup (Fin 2) F)),
      ∀ x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)), α x = n * x * n⁻¹ := by
  obtain ⟨m, hm, ⟨φ⟩⟩ := sylow_two_quaternion F hodd P
  obtain ⟨j, hj1, ⟨φ'⟩⟩ : ∃ j : ℕ, 1 ≤ j ∧
      Nonempty (↥(P : Subgroup (SpecialLinearGroup (Fin 2) F)) ≃* QuaternionGroup (2 ^ j)) :=
    ⟨m - 2, by omega, ⟨φ⟩⟩
  rcases (by omega : j = 1 ∨ 2 ≤ j) with rfl | hj2
  · exact aut_sylow_odd_q8 hodd P φ' α hα hQ
  · refine ⟨1, Subgroup.one_mem _, fun x hx => ?_⟩
    rw [aut_sylow_odd_large P hj2 φ' α hα hQ x hx]; group

end Final


open CFSG.GH74.GLS.LU.Local in
theorem sl2SylowLeaf : SL2SylowLeaf := by
  intro K _ _ q hmod hodd _ Q hQ
  obtain ⟨F, _, _, hFq, ⟨e⟩⟩ := hmod
  have hoddF : Odd (Nat.card F) := by rw [hFq]; exact hodd
  let ε : K ≃* SpecialLinearGroup (Fin 2) F :=
    e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  set Q' : Subgroup (SpecialLinearGroup (Fin 2) F) := Q.map ε.toMonoidHom with hQ'
  have hQ'card : Nat.card ↥Q' = 2 ^ (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization 2 := by
    rw [hQ', Subgroup.card_map_of_injective ε.injective, hQ, Nat.card_congr ε.toEquiv]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 (SpecialLinearGroup (Fin 2) F) := Sylow.ofCard Q' hQ'card
  have hP : (P : Subgroup (SpecialLinearGroup (Fin 2) F)) = Q' := Sylow.coe_ofCard Q' hQ'card
  have hmemP : ∀ x : K, x ∈ Q ↔ ε x ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    intro x
    rw [hP, hQ']
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := ε.injective hyx
      rwa [← this]
  refine ⟨fun x hx => ?_, fun α hα hQα => ?_⟩
  · have hc := cent_sylow_le_center hoddF P (x := ε x) (fun y hy => by
      obtain ⟨y₀, rfl⟩ := ε.surjective y
      have hy₀ : y₀ ∈ Q := (hmemP y₀).mpr hy
      rw [← map_mul, ← map_mul, hx y₀ hy₀])
    exact (mem_center_equiv_iff ε).mp hc
  · set α' : MulAut (SpecialLinearGroup (Fin 2) F) := MulAut.congr ε α with hα'
    have hα'odd : Odd (orderOf α') := by rw [hα', MulEquiv.orderOf_eq]; exact hα
    have hα'apply : ∀ x : K, α' (ε x) = ε (α x) := by
      intro x
      simp [hα', MulAut.congr_apply]
    have hQ'' : ∀ y, y ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) ↔
        α' y ∈ (P : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
      intro y
      obtain ⟨x, rfl⟩ := ε.surjective y
      rw [hα'apply, ← hmemP, ← hmemP]
      exact hQα x
    obtain ⟨n, hn, hnx⟩ := aut_sylow_odd hoddF P α' hα'odd hQ''
    refine ⟨ε.symm n, ?_, fun x hx => ?_⟩
    · refine mem_normalizer_iff.mpr (fun x => ?_)
      have h1 := mem_normalizer_iff.mp hn (ε x)
      rw [hmemP, hmemP]
      have e1 : ε (ε.symm n * x * (ε.symm n)⁻¹) = n * ε x * n⁻¹ := by simp
      rw [e1]
      exact h1
    · have hx' := (hmemP x).mp hx
      have h1 := hnx (ε x) hx'
      rw [hα'apply] at h1
      apply ε.injective
      rw [h1]; simp

end CFSG.GH74.GLS.LU.Local.SL2
