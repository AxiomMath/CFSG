module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightDerData
import Mathlib.Tactic.Abel
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Matrix

theorem sp8d_add_self (X : Sp8dMat) : X + X = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (X i j)

theorem sp8d_add_add (a b c : Sp8dMat) : (a + b) + (b + c) = a + c := by
  rw [add_assoc, ← add_assoc b, sp8d_add_self, zero_add]

theorem sp8d_add_add_comm (a b : Sp8dMat) : (a + b) + (b + a) = 0 := by
  rw [sp8d_add_add, sp8d_add_self]

theorem Sp8dInS.add {a b : Sp8dMat} (ha : Sp8dInS a) (hb : Sp8dInS b) : Sp8dInS (a + b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact Or.inl (add_zero 0)
  · exact Or.inr (zero_add _)
  · exact Or.inr (add_zero _)
  · exact Or.inl (sp8d_add_self _)

theorem Sp8dInS.conj {B a : Sp8dMat} (hB : B * sp8dS * Bᵀ = sp8dS) (ha : Sp8dInS a) :
    Sp8dInS (B * a * Bᵀ) := by
  rcases ha with rfl | rfl
  · exact Or.inl (by rw [Matrix.mul_zero, Matrix.zero_mul])
  · exact Or.inr hB

theorem sp8d_conj_add (B x y : Sp8dMat) : B * (x + y) * Bᵀ = B * x * Bᵀ + B * y * Bᵀ := by
  rw [Matrix.mul_add, Matrix.add_mul]

theorem sp8d_conj_conj (A B x : Sp8dMat) : A * (B * x * Bᵀ) * Aᵀ = (A * B) * x * (A * B)ᵀ := by
  rw [transpose_mul]
  simp only [Matrix.mul_assoc]

theorem sp8d_d8_fixed (W : Set Sp8dMat) (hadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W)
    (hg : ∀ x ∈ W, sp8dG * x * sp8dGᵀ ∈ W) (hh : ∀ x ∈ W, sp8dH * x * sp8dHᵀ ∈ W)
    {v : Sp8dMat} (hv : v ∈ W) (hvS : ¬ Sp8dInS v) :
    ∃ w ∈ W, ¬ Sp8dInS w ∧ Sp8dInS (sp8dG * w * sp8dGᵀ + w) ∧
      Sp8dInS (sp8dH * w * sp8dHᵀ + w) := by
  obtain ⟨hg4, hh2, hgh⟩ := sp8d_dihedral
  obtain ⟨-, hgS, hhS⟩ := sp8d_gens_mem_sp
  set Lg : Sp8dMat → Sp8dMat := fun x => sp8dG * x * sp8dGᵀ with hLg
  set Lh : Sp8dMat → Sp8dMat := fun x => sp8dH * x * sp8dHᵀ with hLh
  have Lg_add : ∀ x y, Lg (x + y) = Lg x + Lg y := fun x y => sp8d_conj_add _ _ _
  have Lh_add : ∀ x y, Lh (x + y) = Lh x + Lh y := fun x y => sp8d_conj_add _ _ _
  have Lg4 : ∀ x, Lg (Lg (Lg (Lg x))) = x := by
    intro x
    simp only [hLg, sp8d_conj_conj, ← Matrix.mul_assoc, hg4, Matrix.one_mul, transpose_one,
      Matrix.mul_one]
  have Lh2 : ∀ x, Lh (Lh x) = x := by
    intro x
    simp only [hLh, sp8d_conj_conj, hh2, Matrix.one_mul, transpose_one, Matrix.mul_one]
  have Lgh : ∀ x, Lg (Lh x) = Lh (Lg (Lg (Lg x))) := by
    intro x
    simp only [hLg, hLh, sp8d_conj_conj, ← Matrix.mul_assoc]
    rw [hgh]
    simp only [Matrix.mul_assoc]
  have hLgS : ∀ {a}, Sp8dInS a → Sp8dInS (Lg a) := fun ha => Sp8dInS.conj hgS ha
  have hLhS : ∀ {a}, Sp8dInS a → Sp8dInS (Lh a) := fun ha => Sp8dInS.conj hhS ha
  obtain ⟨v₁, hv₁, hv₁S, hz⟩ : ∃ v₁ ∈ W, ¬ Sp8dInS v₁ ∧ Sp8dInS (Lg (Lg v₁) + v₁) := by
    by_cases h1 : Sp8dInS (Lg (Lg v) + v)
    · exact ⟨v, hv, hvS, h1⟩
    · refine ⟨v + Lg (Lg v), hadd _ hv _ (hg _ (hg _ hv)), fun h => h1 (by rwa [add_comm]), ?_⟩
      show Sp8dInS (Lg (Lg (v + Lg (Lg v))) + (v + Lg (Lg v)))
      rw [Lg_add, Lg_add, Lg4, sp8d_add_add_comm]
      exact Or.inl rfl
  obtain ⟨v₂, hv₂, hv₂S, hg₂⟩ : ∃ v₂ ∈ W, ¬ Sp8dInS v₂ ∧ Sp8dInS (Lg v₂ + v₂) := by
    by_cases h2 : Sp8dInS (Lg v₁ + v₁)
    · exact ⟨v₁, hv₁, hv₁S, h2⟩
    · refine ⟨v₁ + Lg v₁, hadd _ hv₁ _ (hg _ hv₁), fun h => h2 (by rwa [add_comm]), ?_⟩
      show Sp8dInS (Lg (v₁ + Lg v₁) + (v₁ + Lg v₁))
      have e : Lg (v₁ + Lg v₁) + (v₁ + Lg v₁) = Lg (Lg v₁) + v₁ := by
        rw [Lg_add, add_comm v₁ (Lg v₁), add_comm (Lg v₁) (Lg (Lg v₁)), sp8d_add_add]
      rw [e]
      exact hz
  by_cases h3 : Sp8dInS (Lh v₂ + v₂)
  · exact ⟨v₂, hv₂, hv₂S, hg₂, h3⟩
  · refine ⟨v₂ + Lh v₂, hadd _ hv₂ _ (hh _ hv₂), fun h => h3 (by rwa [add_comm]), ?_, ?_⟩
    ·
      have h31 : Sp8dInS (Lg (Lg (Lg v₂)) + v₂) := by
        have a1 : Sp8dInS (Lg (Lg (Lg v₂)) + Lg (Lg v₂)) := by
          rw [← Lg_add, ← Lg_add]
          exact hLgS (hLgS hg₂)
        have a2 : Sp8dInS (Lg (Lg v₂) + Lg v₂) := by
          rw [← Lg_add]
          exact hLgS hg₂
        have := (a1.add a2).add hg₂
        rwa [sp8d_add_add, sp8d_add_add] at this
      have h32 : Sp8dInS (Lg (Lh v₂) + Lh v₂) := by
        rw [Lgh, ← Lh_add]
        exact hLhS h31
      have e : Lg (v₂ + Lh v₂) + (v₂ + Lh v₂) = (Lg v₂ + v₂) + (Lg (Lh v₂) + Lh v₂) := by
        rw [Lg_add]
        abel
      show Sp8dInS (Lg (v₂ + Lh v₂) + (v₂ + Lh v₂))
      rw [e]
      exact hg₂.add h32
    · show Sp8dInS (Lh (v₂ + Lh v₂) + (v₂ + Lh v₂))
      rw [Lh_add, Lh2, sp8d_add_add_comm]
      exact Or.inl rfl

@[expose] def Sp8dTwisted (F : Sp8dMat → Sp8dMat) (B : Sp8dMat) : Prop :=
  ∃ T : Sp8dMat, Tᵀ * sp8dS * T = sp8dS ∧ ∀ Z, Sp8dIsQ5 Z → B * F Z * Bᵀ = F (T * Z * Tᵀ)

theorem sp8d_exists_mem_O15 (F : Sp8dMat → Sp8dMat) (hsym : ∀ X, Sp8dIsQ5 X → (F X)ᵀ = F X)
    (hadd : ∀ X Y, Sp8dIsQ5 X → Sp8dIsQ5 Y → F (X + Y) = F X + F Y)
    (hinj : ∀ X Y, Sp8dIsQ5 X → Sp8dIsQ5 Y → F X = F Y → X = Y) (hS : F sp8dS = sp8dS)
    (hB1 : Sp8dTwisted F sp8dB1) (hG : Sp8dTwisted F sp8dG) (hH : Sp8dTwisted F sp8dH) :
    ∃ X ∈ sp8dO15, F X ∈ sp8dO15 := by
  have hF0 : F 0 = 0 := by
    have h := hadd 0 0 sp8dIsQ5_zero sp8dIsQ5_zero
    rw [add_zero] at h
    have h2 : F 0 + F 0 = 0 := sp8d_add_self _
    rwa [← h] at h2
  let W : Set Sp8dMat := {Y | ∃ Z, Sp8dIsQ5 Z ∧ F Z = Y}
  have hWadd : ∀ x ∈ W, ∀ y ∈ W, x + y ∈ W := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨Y, hY, rfl⟩
    exact ⟨X + Y, hX.add hY, hadd X Y hX hY⟩
  have hWB : ∀ {B}, Sp8dTwisted F B → ∀ x ∈ W, B * x * Bᵀ ∈ W := by
    rintro B ⟨T, hT, hTF⟩ _ ⟨Z, hZ, rfl⟩
    exact ⟨T * Z * Tᵀ, sp8dIsQ5_conj hT hZ, (hTF Z hZ).symm⟩
  have hWsym : ∀ x ∈ W, xᵀ = x := by
    rintro _ ⟨Z, hZ, rfl⟩
    exact hsym Z hZ
  have hWS : sp8dS ∈ W := ⟨sp8dS, sp8dIsQ5_S, hS⟩
  have hW0 : (0 : Sp8dMat) ∈ W := ⟨0, sp8dIsQ5_zero, hF0⟩
  have hv0 : F sp8dZ0 ∈ W := ⟨sp8dZ0, sp8dZ0_isQ5, rfl⟩
  have hv0S : ¬ Sp8dInS (F sp8dZ0) := by
    rintro (h | h)
    · exact sp8dZ0_ne.1 (hinj _ _ sp8dZ0_isQ5 sp8dIsQ5_zero (h.trans hF0.symm))
    · exact sp8dZ0_ne.2 (hinj _ _ sp8dZ0_isQ5 sp8dIsQ5_S (h.trans hS.symm))
  obtain ⟨w, hwW, hwS, hwg, hwh⟩ := sp8d_d8_fixed W hWadd (hWB hG) (hWB hH) hv0 hv0S
  have hshift : ∀ {x c : Sp8dMat}, x ∈ W → Sp8dInS (x + c) → c ∈ W := by
    intro x c hx hxc
    have e : c = x + (x + c) := by rw [← add_assoc, sp8d_add_self, zero_add]
    rcases hxc with h | h
    · rw [e, h, add_zero]
      exact hx
    · rw [e, h]
      exact hWadd _ hx _ hWS
  have hz0 : sp8dZ0 ∈ W := by
    rcases sp8d_fixModS (hWsym w hwW) hwg hwh with h | h | h | h
    · exact absurd h hwS
    · exact hshift hwW h
    · have hy0 : sp8dY0 ∈ W := hshift hwW h
      rw [← sp8d_prog_y0]
      exact hWadd _ (hWB hB1 _ hy0) _ (hWB hG _ (hWB hG _ (hWB hB1 _ hy0)))
    · have hu : sp8dY0 + sp8dZ0 ∈ W := hshift hwW (by rw [← add_assoc]; exact h)
      rw [← sp8d_prog_u]
      exact hWadd _ (hWadd _ hu _ (hWB hB1 _ hu)) _ (hWB hG _ (hWB hB1 _ hu))
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hsmul : ∀ (c : ZMod 2) {x : Sp8dMat}, x ∈ W → c • x ∈ W := by
    intro c x hx
    rcases h01 c with rfl | rfl
    · rw [zero_smul]
      exact hW0
    · rwa [one_smul]
  have hQ5W : ∀ q, Sp8dIsQ5 q → q ∈ W := by
    intro q hq
    rw [eq_sp8dQ5mk_of_isQ5 hq, sp8dQ5mk_eq_basis]
    have hb := hWB hB1 _ hz0
    exact hWadd _ (hWadd _ (hWadd _ (hWadd _ (hsmul _ hWS) _ (hsmul _ hb)) _ (hsmul _ hz0)) _
      (hsmul _ (hWB hB1 _ hb))) _ (hsmul _ (hWB hG _ hb))
  have hFQ5 : ∀ Z, Sp8dIsQ5 Z → Sp8dIsQ5 (F Z) := by
    let Q : Finset Sp8dMat :=
      (Finset.univ : Finset (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)).image
        (fun p => sp8dQ5mk p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    have hmemQ : ∀ Y, Y ∈ Q ↔ Sp8dIsQ5 Y := by
      intro Y
      constructor
      · intro hY
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hY
        exact sp8dIsQ5_mk _ _ _ _ _
      · intro hY
        rw [eq_sp8dQ5mk_of_isQ5 hY]
        exact Finset.mem_image.2 ⟨(Y 0 1, Y 0 2, Y 0 3, Y 1 2, Y 1 3), Finset.mem_univ _, rfl⟩
    have hsub : Q ⊆ Q.image F := by
      intro q hq
      obtain ⟨Z, hZ, hFZ⟩ := hQ5W q ((hmemQ q).1 hq)
      exact Finset.mem_image.2 ⟨Z, (hmemQ Z).2 hZ, hFZ⟩
    have heq := Finset.eq_of_subset_of_card_le hsub Finset.card_image_le
    intro Z hZ
    have h := Finset.mem_image_of_mem F ((hmemQ Z).2 hZ)
    rw [← heq] at h
    exact (hmemQ _).1 h
  have hFcases : ∀ X ∈ sp8dO15, F X ∈ sp8dO15 ∨ F X ∈ sp8dZ15 := by
    intro X hX
    have hXQ := sp8dO15_isQ5 hX
    rcases sp8dIsQ5_cases (hFQ5 X hXQ) with h | h | h | h
    · exact absurd (hinj _ _ hXQ sp8dIsQ5_zero (h.trans hF0.symm)) (sp8dO15_ne_zero hX)
    · exact absurd (hinj _ _ hXQ sp8dIsQ5_S (h.trans hS.symm)) (sp8dO15_ne_S hX)
    · exact Or.inl h
    · exact Or.inr h
  by_contra hcon
  push Not at hcon
  have hZ : ∀ X ∈ sp8dO15, F X ∈ sp8dZ15 := fun X hX => (hFcases X hX).resolve_left (hcon X hX)
  have hle := Finset.card_le_card_of_injOn F (s := sp8dO15.filter (fun Y => sp8dX0 + Y ∈ sp8dO15))
    (t := sp8dZ15.filter (fun Y => F sp8dX0 + Y ∈ sp8dZ15)) ?_ ?_
  · rw [card_sp8dO15_filter] at hle
    have := card_sp8dZ15_filter_le (hZ _ sp8dX0_mem)
    omega
  · intro Y hY
    rw [Finset.mem_coe, Finset.mem_filter] at hY ⊢
    refine ⟨hZ Y hY.1, ?_⟩
    rw [← hadd _ _ (sp8dO15_isQ5 sp8dX0_mem) (sp8dO15_isQ5 hY.1)]
    exact hZ _ hY.2
  · intro Y hY Y' hY' h
    rw [Finset.mem_coe, Finset.mem_filter] at hY hY'
    exact hinj _ _ (sp8dO15_isQ5 hY.1) (sp8dO15_isQ5 hY'.1) h

end CFSG.SeitzReduction.SymplecticPilot
