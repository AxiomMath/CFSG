module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.C3.Layer1.Thm1End
public import CFSG.GH74.GLS.C3.Layer1.Thm1Notation
public import CFSG.GH74.GLS.C3.Layer1.Thm1P310Two
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1

theorem exists_l2_model_card {H : Type} [Group H] {r : ℕ} (hr : Odd r) (hr5 : 5 ≤ r)
    (h : HasL2Model H (fun q => q = r)) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ∧ L2Field F ∧ Nonempty (H ≃* L2 F) := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  rcases hL with ⟨-, hadm, F, hF, hFin, hcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hc : Nat.card F = r := by rw [hcard]; exact hP
    exact ⟨F, hF, hFin, hc, ⟨by rw [hc]; exact hr, by rw [hc]; omega⟩, ⟨e⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem secD_eq_inf_cmk {G : Type} [Group G] {K V : Subgroup G} {f : G}
    (hsup : pumpJ K f = layerI K f ⊔ pPrimeCoreOf 2 (pumpJ K f))
    (hVC : V ≤ centralizer ({f} : Set G)) :
    secD K f V = V ⊓ CMK (centralizer ({f} : Set G)) (pumpJ K f) := by
  unfold secD CMK
  rw [← hsup, ← inf_assoc, inf_eq_left.2 hVC]

theorem mul_self_eq_one_of_mem_klein {G : Type} [Group G] {x f d : G} (hx : x * x = 1)
    (hf : f * f = 1) (hxf : x * f = f * x) (hd : d ∈ zpowers x ⊔ zpowers f) : d * d = 1 := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Thm1P310.exists_mul_of_mem_sup (P := zpowers x) (D := zpowers f)
    (fun u hu w hw => by
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
      exact (Commute.zpow_zpow (show Commute x f from hxf) i j).eq) hd
  have hc : ∀ i j : ℤ, x ^ i * f ^ j = f ^ j * x ^ i := fun i j =>
    (Commute.zpow_zpow (show Commute x f from hxf) i j).eq
  rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hx hu with h1 | h1 <;>
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers hf hw with h2 | h2 <;> rw [h1, h2]
  · simp
  · simpa using hf
  · simpa using hx
  · calc x * f * (x * f) = x * (f * x) * f := by group
      _ = x * (x * f) * f := by rw [← hxf]
      _ = (x * x) * (f * f) := by group
      _ = 1 := by rw [hx, hf, one_mul]

end CFSG.GH74.GLS
