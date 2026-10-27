module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import CFSG.GH74.GLS.C3.Prop121.Card7F4Inputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F4Inputs
public import Certificates.Certificate5078

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem mem_N4L {f : F7} : f ∈ N4L ↔ XF f ∧ (f : Amb 7).2 ≠ 1 := by simp [N4L, mem_F7L]

theorem mem_I40L {f : F7} : f ∈ I40L ↔ IsInv f ∧ (f : Amb 7).2 = 1 := by simp [I40L, mem_F7L]

theorem chk_nm4 :
    ∀ f ∈ N4L, ¬ (ccardB f f ∣ 1152) :=
  Certificates.certificate5078.1

theorem chk_conj40 :
    ∀ f ∈ I40L, ∃ k ∈ F7L, k * f * k⁻¹ = u0 :=
  Certificates.certificate5078.2

theorem nat_card_centralizer_eq_ccardB (f : F7) :
    Nat.card (centralizer ({f} : Set F7)) = ccardB f f := by
  rw [← ccard_eq_ccardB]
  unfold ccard
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  rw [mem_centralizer_singleton_iff, and_self]

theorem F7_nm4_forced : ∀ f : F7, IsInv f → nm7 (f : Amb 7) = 4 →
    (f : Amb 7).2 = 1 ∨ ¬ (Nat.card (centralizer ({f} : Set F7)) ∣ 1152) := by
  intro f hf h4
  by_cases h1 : (f : Amb 7).2 = 1
  · exact Or.inl h1
  · right
    rw [nat_card_centralizer_eq_ccardB]
    exact chk_nm4 f (mem_N4L.2 ⟨⟨hf, h4⟩, h1⟩)

theorem F7_conj_inv40 :
    ∀ f f' : F7, IsInv f → IsInv f' → (f : Amb 7).2 = 1 → (f' : Amb 7).2 = 1 →
    ∃ k : F7, k * f * k⁻¹ = f' := by
  intro f f' hf hf' h1 h1'
  obtain ⟨k, -, hk⟩ := chk_conj40 f (mem_I40L.2 ⟨hf, h1⟩)
  obtain ⟨k', -, hk'⟩ := chk_conj40 f' (mem_I40L.2 ⟨hf', h1'⟩)
  refine ⟨k'⁻¹ * k, ?_⟩
  calc k'⁻¹ * k * f * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * f * k⁻¹) * k' := by group
    _ = k'⁻¹ * u0 * k' := by rw [hk]
    _ = f' := by rw [← hk']; group

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
