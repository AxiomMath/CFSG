module

public import CFSG.LocalAnalysis.OddStandard.Harada75Iota
public import CFSG.LocalAnalysis.OddStandard.Harada75Extra
public import CFSG.LocalAnalysis.OddStandard.Harada75Basic

public section

namespace CFSG.OddStandard.Harada75

open Heis

variable {S : Type} [Group S]

theorem Pres.swap₁ {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z) : Pres f₁ e₂ e₁ f₂ z where
  z_sq := P.z_sq
  z_ne := P.z_ne
  z_cent := P.z_cent
  e₁_sq := P.f₁_sq
  e₂_sq := P.e₂_sq
  f₁_sq := P.e₁_sq
  f₂_sq := P.f₂_sq
  e₁e₂ := P.f₁e₂
  f₁f₂ := P.e₁f₂
  e₁f₁ := P.f₁e₁
  e₂f₂ := P.e₂f₂
  e₁f₂ := P.f₁f₂
  e₂f₁ := P.e₁e₂.symm

namespace Pres

variable {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z)
include P

theorem iota_e₁ : P.iota ⟨e1, 0⟩ = e₁ := by
  simp [iota_apply, e1, Ee, Ff, pw_zero, pw_one]

theorem iota_e₂ : P.iota ⟨e2, 0⟩ = e₂ := by
  simp [iota_apply, e2, Ee, Ff, pw_zero, pw_one]

theorem iota_f₁ : P.iota ⟨f1, 0⟩ = f₁ := by
  simp [iota_apply, f1, Ee, Ff, pw_zero, pw_one]

theorem iota_f₂ : P.iota ⟨f2, 0⟩ = f₂ := by
  simp [iota_apply, f2, Ee, Ff, pw_zero, pw_one]

theorem iota_z : P.iota z₀ = z := by
  rw [← Zc_one, P.iota_Zc, pw_one]

theorem iota_mem_of_mem_E₀ {E : Subgroup S} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (hz : z ∈ E) {h : Heis}
    (hh : h ∈ E₀) : P.iota h ∈ E := by
  have pwmem : ∀ {g : S}, g ∈ E → ∀ c : ZMod 2, pw g c ∈ E := by
    intro g hg c
    rcases zmod2_cases c with rfl | rfl
    · rw [pw_zero]; exact E.one_mem
    · rw [pw_one]; exact hg
  rw [iota_apply, hh.1, hh.2]
  simp only [Ff, pw_zero, mul_one]
  exact E.mul_mem (E.mul_mem (pwmem he₁ _) (pwmem he₂ _)) (pwmem hz _)

end Pres

theorem noE32_of_pres [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S} (h : Cfg S A E)
    {e₁ e₂ f₁ f₂ z : S} (P : Pres e₁ e₂ f₁ f₂ z) (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (hz : z ∈ E)
    (hA : ∀ a ∈ A, a ∈ Subgroup.closure ({e₁, e₂, f₁, f₂, z} : Set S)) : NoE32 S := by
  have hmap : E₀.map P.iota = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact P.iota_mem_of_mem_E₀ he₁ he₂ hz hx
    · rw [Subgroup.card_map_of_injective P.iota_injective, card_E₀, h.E_card]
  have hf₁ : f₁ ∈ P.iota.range := ⟨⟨f1, 0⟩, P.iota_f₁⟩
  have hf₂ : f₂ ∈ P.iota.range := ⟨⟨f2, 0⟩, P.iota_f₂⟩
  have hzr : z ∈ P.iota.range := ⟨z₀, P.iota_z⟩
  have he₁r : e₁ ∈ P.iota.range := ⟨⟨e1, 0⟩, P.iota_e₁⟩
  have he₂r : e₂ ∈ P.iota.range := ⟨⟨e2, 0⟩, P.iota_e₂⟩
  have hcl : Subgroup.closure ({e₁, e₂, f₁, f₂, z} : Set S) ≤ P.iota.range := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact he₁r
    · exact he₂r
    · exact hf₁
    · exact hf₂
    · exact hzr
  have D : Setup P.iota :=
    { inj := P.iota_injective
      z_cent := fun s => by rw [P.iota_z]; exact P.z_cent s
      E_norm := fun t x hx => by
        have h1 : t * P.iota x * t⁻¹ ∈ E :=
          h.E_norm t _ (P.iota_mem_of_mem_E₀ he₁ he₂ hz hx)
        rw [← hmap] at h1
        obtain ⟨y, hy, hyeq⟩ := h1
        exact ⟨y, hy, hyeq.symm⟩
      C_le := fun x hx => by
        have hxA : x ∈ A := by
          apply h.A_cent
          intro a ha
          have := hcl (hA a ha)
          exact hx a this
        exact hcl (hA x hxA) }
  exact D.noE32_of_setup hS

end CFSG.OddStandard.Harada75
