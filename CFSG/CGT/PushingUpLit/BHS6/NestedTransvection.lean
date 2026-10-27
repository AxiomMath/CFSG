module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem false_of_transvection {F W : Subgroup Γ} {k : ℕ} (hk2 : 2 ≤ k) (hnat : IsNatSL F W k)
    (hFW : F ≤ Subgroup.normalizer (W : Set Γ)) {f c : Γ} (hf : f ∈ F) (hc : c ∈ W)
    (hc1 : c ≠ 1) (hcomm : ∀ w ∈ W, ⁅f, w⁆ = 1 ∨ ⁅f, w⁆ = c) (hex : ∃ w ∈ W, ⁅f, w⁆ = c) :
    False := by
  classical
  obtain ⟨φ, ψ, hφs, hφk, hψs, hψk, hψe⟩ := hnat
  have hfn : ∀ w ∈ W, f * w * f⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp (hFW hf) w).mp hw
  have hcW : ∀ w ∈ W, ⁅f, w⁆ ∈ W := fun w hw => by
    rw [commutatorElement_def]
    exact W.mul_mem (hfn w hw) (W.inv_mem hw)
  set s := φ ⟨f, hf⟩ with hs
  set v : Fin 2 → GaloisField 2 k := Multiplicative.toAdd (ψ ⟨c, hc⟩) with hv
  have hψcomm : ∀ w : ↥W, Multiplicative.toAdd (ψ ⟨⁅f, (w : Γ)⁆, hcW w w.2⟩) =
      (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec (Multiplicative.toAdd (ψ w)) -
        Multiplicative.toAdd (ψ w) := by
    intro w
    have e : (⟨⁅f, (w : Γ)⁆, hcW w w.2⟩ : ↥W) = ⟨f * w * f⁻¹, hfn w w.2⟩ * w⁻¹ := by
      apply Subtype.ext
      show ⁅f, (w : Γ)⁆ = f * (w : Γ) * f⁻¹ * (w : Γ)⁻¹
      exact commutatorElement_def _ _
    rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hψe ⟨f, hf⟩ w (hfn w w.2), toAdd_ofAdd]
    abel
  have key2 : ∀ x : Fin 2 → GaloisField 2 k,
      (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x - x = 0 ∨
        (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x - x = v := by
    intro x
    obtain ⟨w, hw⟩ := hψs (Multiplicative.ofAdd x)
    have hx : Multiplicative.toAdd (ψ w) = x := by rw [hw, toAdd_ofAdd]
    rw [← hx, ← hψcomm w]
    rcases hcomm w w.2 with h | h
    · left
      have : (⟨⁅f, (w : Γ)⁆, hcW w w.2⟩ : ↥W) = 1 := Subtype.ext h
      rw [this, map_one, toAdd_one]
    · right
      have : (⟨⁅f, (w : Γ)⁆, hcW w w.2⟩ : ↥W) = ⟨c, hc⟩ := Subtype.ext h
      rw [this]
  obtain ⟨w₁, hw₁, hw₁c⟩ := hex
  set x₁ := Multiplicative.toAdd (ψ ⟨w₁, hw₁⟩) with hx₁
  have key3 : (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x₁ - x₁ = v := by
    rw [hx₁, ← hψcomm ⟨w₁, hw₁⟩]
    have : (⟨⁅f, w₁⁆, hcW w₁ hw₁⟩ : ↥W) = ⟨c, hc⟩ := Subtype.ext hw₁c
    show Multiplicative.toAdd (ψ ⟨⁅f, w₁⁆, hcW w₁ hw₁⟩) = v
    rw [this]
  by_cases hv0 : v = 0
  ·
    have hall : ∀ x : Fin 2 → GaloisField 2 k,
        (s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x = x := by
      intro x
      rcases key2 x with h | h
      · exact sub_eq_zero.mp h
      · rw [hv0] at h
        exact sub_eq_zero.mp h
    have hs1 : s = 1 := by
      apply Subtype.ext
      ext i j
      have := congrFun (hall (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have hker : (⟨f, hf⟩ : ↥F) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hs1
    rw [hφk, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hker
    have hfc : f ∈ Subgroup.centralizer (W : Set Γ) := hker.2
    apply hc1
    rw [← hw₁c, commutatorElement_def]
    have := Subgroup.mem_centralizer_iff.mp hfc w₁ hw₁
    rw [← this]
    group
  ·
    have hscal : ∀ l : GaloisField 2 k, l = 0 ∨ l = 1 := by
      intro l
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hv0 (funext hcon)
      rcases key2 (l • x₁) with h | h
      · left
        have h1 : l • ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x₁ - x₁) = 0 := by
          rw [smul_sub, ← Matrix.mulVec_smul]
          exact h
        rw [key3] at h1
        have := congrFun h1 i
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        exact (mul_eq_zero.mp this).resolve_right hi
      · right
        have h1 : l • ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 k)).mulVec x₁ - x₁) = v := by
          rw [smul_sub, ← Matrix.mulVec_smul]
          exact h
        rw [key3] at h1
        have := congrFun h1 i
        simp only [Pi.smul_apply, smul_eq_mul] at this
        have h2 : (l - 1) * v i = 0 := by rw [sub_mul, this, one_mul, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hi)
    have hinj : Function.Injective (fun l : GaloisField 2 k => decide (l = 1)) := by
      intro a b hab
      rcases hscal a with ha | ha <;> rcases hscal b with hb | hb
      · rw [ha, hb]
      · exfalso
        rw [ha, hb] at hab
        simp at hab
      · exfalso
        rw [ha, hb] at hab
        simp at hab
      · rw [ha, hb]
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [GaloisField.card 2 k (by omega), Nat.card_eq_fintype_card, Fintype.card_bool] at hcard
    have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega

end CFSG.CGT.PushingUpLit.BHS6
