module

public import Certificates.Data.Kernel.Fi22RkInv.Defs
public import CFSG.Certificates.Kernel.Fi22Gen.Sound
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.Fi22RkInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Fi22Gen

theorem BS_lt : ∀ b < 5, BS b < 3510 := by decide

theorem ptK_spec {F : Nat → Nat → Nat} {X : Nat → Nat} {s t u : List Nat} {b : Nat}
    (h : ptK F X s t u b = true) :
    wAp F s (wAp F s b) = b ∧ wAp F s (X (wAp F s (X b))) = b ∧ wAp F t (wAp F t b) = b ∧
      wAp F u (wAp F u b) = b ∧ wAp F t (X b) = X (wAp F t b) ∧
      wAp F u (X b) = X (wAp F u b) ∧
      wAp F t (wAp F u (wAp F t (wAp F u (wAp F t (wAp F u b))))) = b := by
  unfold ptK at h
  simp only [bAnd_iff, Nat.beq_eq] at h
  exact h

section Group

variable {G : Type*} [Group G] [MulAction G (Fin 3510)]

@[expose] def ActsAs (h : G) (f : Nat → Nat) : Prop :=
  ∀ y (hy : y < 3510), (h • (⟨y, hy⟩ : Fin 3510)).val = f y

theorem ActsAs.lt {h : G} {f : Nat → Nat} (H : ActsAs h f) {y : Nat} (hy : y < 3510) :
    f y < 3510 := by
  rw [← H y hy]
  exact (h • (⟨y, hy⟩ : Fin 3510)).isLt

theorem ActsAs.mul {h₁ h₂ : G} {f₁ f₂ : Nat → Nat} (H₁ : ActsAs h₁ f₁) (H₂ : ActsAs h₂ f₂) :
    ActsAs (h₁ * h₂) fun y => f₁ (f₂ y) := by
  intro y hy
  have e : h₂ • (⟨y, hy⟩ : Fin 3510) = ⟨f₂ y, H₂.lt hy⟩ := Fin.ext (H₂ y hy)
  rw [mul_smul, e, H₁]

theorem ActsAs.one : ActsAs (1 : G) fun y => y := fun _ _ => by rw [one_smul]

theorem eq_of_base
    (hsep : ∀ x : G, (∀ b < 5, ∀ hb : BS b < 3510, x • (⟨BS b, hb⟩ : Fin 3510) = ⟨BS b, hb⟩) →
      x = 1)
    {h₁ h₂ : G} {f₁ f₂ : Nat → Nat} (H₁ : ActsAs h₁ f₁) (H₂ : ActsAs h₂ f₂)
    (h : ∀ b < 5, f₁ (BS b) = f₂ (BS b)) : h₁ = h₂ := by
  have e := hsep (h₂⁻¹ * h₁) fun b hb hb' => by
    rw [mul_smul, inv_smul_eq_iff]
    exact Fin.ext (by rw [H₁ _ hb', H₂ _ hb', h b hb])
  exact (inv_mul_eq_one.1 e).symm

theorem invK_sound {F : Nat → Nat → Nat} {X : Nat → Nat} {s t u : List Nat} {m : Nat}
    (g : Nat → G) (hg : ∀ l < 32, ∀ y (hy : y < 3510), (g l • (⟨y, hy⟩ : Fin 3510)).val = F l y)
    {x : G} (hx : ActsAs x X)
    (hsep : ∀ x : G, (∀ b < 5, ∀ hb : BS b < 3510, x • (⟨BS b, hb⟩ : Fin 3510) = ⟨BS b, hb⟩) →
      x = 1)
    (h : invK F X s t u m = true) :
    (∃ a : G, a ^ 2 = 1 ∧ a * x * a = x⁻¹) ∧
      ∃ c d : G, c ^ 2 = 1 ∧ d ^ 2 = 1 ∧ c * x = x * c ∧ d * x = x * d ∧
        (c * d) ^ 3 = 1 ∧ c * d ≠ 1 := by
  unfold invK at h
  simp only [bAnd_iff] at h
  obtain ⟨hs, ht, hu, hall, hm, hmv⟩ := h
  have S : ActsAs (wG g s) (wAp F s) := wG_smul g F 32 hg s (lettersLt_spec hs)
  have T : ActsAs (wG g t) (wAp F t) := wG_smul g F 32 hg t (lettersLt_spec ht)
  have U : ActsAs (wG g u) (wAp F u) := wG_smul g F 32 hg u (lettersLt_spec hu)
  have P : ∀ b < 5, _ := fun b hb => ptK_spec (Raw.Orb.allN_iff.1 hall b hb)
  have TU := T.mul U
  refine ⟨⟨wG g s, ?_, ?_⟩, wG g t, wG g u, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sq]
    exact eq_of_base hsep (S.mul S) ActsAs.one fun b hb => (P b hb).1
  · have e : wG g s * x * (wG g s * x) = 1 :=
      eq_of_base hsep ((S.mul hx).mul (S.mul hx)) ActsAs.one fun b hb => (P b hb).2.1
    rw [← mul_assoc] at e
    exact mul_eq_one_iff_eq_inv.1 e
  · rw [sq]
    exact eq_of_base hsep (T.mul T) ActsAs.one fun b hb => (P b hb).2.2.1
  · rw [sq]
    exact eq_of_base hsep (U.mul U) ActsAs.one fun b hb => (P b hb).2.2.2.1
  · exact eq_of_base hsep (T.mul hx) (hx.mul T) fun b hb => (P b hb).2.2.2.2.1
  · exact eq_of_base hsep (U.mul hx) (hx.mul U) fun b hb => (P b hb).2.2.2.2.2.1
  · rw [pow_three]
    exact eq_of_base hsep (TU.mul (TU.mul TU)) ActsAs.one fun b hb => (P b hb).2.2.2.2.2.2
  · intro e
    rw [Nat.blt_eq] at hm
    have hv := TU (BS m) (BS_lt m hm)
    rw [e, one_smul] at hv
    rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Nat.beq_eq] at hmv
    exact hmv hv.symm

end Group

end CFSG.KS.Fi22RkInv

end
