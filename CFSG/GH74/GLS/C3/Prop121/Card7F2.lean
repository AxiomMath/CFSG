module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7F1
public import Certificates.Certificate5076

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.FF

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem chk_ord3 :
    ∀ f ∈ F7L, f ^ 3 = 1 → f ≠ 1 → Ty3 f ∨ Ty33 f :=
  Certificates.certificate5076.1

theorem chk_conj3 :
    ∀ f ∈ F7L, Ty3 f → ∃ k ∈ F7L, k * f * k⁻¹ = f0 :=
  Certificates.certificate5076.2.1

theorem chk_card_f0 : ccardB f0 f0 = 288 :=
  Certificates.certificate5076.2.2.1

theorem chk_conj33 :
    ∀ f ∈ F7L, Ty33 f → ∃ k ∈ F7L, k * f * k⁻¹ = g0 :=
  Certificates.certificate5076.2.2.2.1

theorem chk_card_g0 : ccardB g0 g0 = 72 :=
  Certificates.certificate5076.2.2.2.2.1

theorem chk_inv_nm :
    ∀ f ∈ F7L, IsInv f → nm7 (f : Amb 7) = 4 ∨ nm7 (f : Amb 7) = 8 :=
  Certificates.certificate5076.2.2.2.2.2

theorem F7_ord3 :
    ∀ f : F7, f ^ 3 = 1 → f ≠ 1 → Ty3 f ∨ Ty33 f := fun f => chk_ord3 f (mem_F7L f)

theorem F7_conj3 : ∀ f : F7, Ty3 f → ∃ k : F7, k * f * k⁻¹ = f0 := by
  intro f hf
  obtain ⟨k, -, hk⟩ := chk_conj3 f (mem_F7L f) hf
  exact ⟨k, hk⟩

theorem F7_card_f0 : ccard F7 f0 f0 = 288 := by
  rw [ccard_eq_ccardB]
  exact chk_card_f0

theorem F7_conj33 :
    ∀ f : F7, Ty33 f → ∃ k : F7, k * f * k⁻¹ = g0 := by
  intro f hf
  obtain ⟨k, -, hk⟩ := chk_conj33 f (mem_F7L f) hf
  exact ⟨k, hk⟩

theorem F7_card_ty33 : ∀ f : F7, Ty33 f → ccard F7 f f = 72 := by
  intro f hf
  obtain ⟨k, hk⟩ := F7_conj33 f hf
  rw [← ccard_conj k f f, hk, ccard_eq_ccardB]
  exact chk_card_g0

theorem F7_inv_nm :
    ∀ f : F7, IsInv f → nm7 (f : Amb 7) = 4 ∨ nm7 (f : Amb 7) = 8 :=
  fun f => chk_inv_nm f (mem_F7L f)

end CFSG.GH74.GLS.C3.Prop121.Card7.FF
