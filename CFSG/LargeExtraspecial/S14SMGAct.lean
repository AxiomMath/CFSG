module

public import CFSG.LargeExtraspecial.S14SMGBits
public import CFSG.LargeExtraspecial.S14C12SmQ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMG

open Subgroup

variable {G : Type} [Group G] (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 20 → ZMod 2))

theorem psi_add (u v : S.Qt) : code (φ (u + v)) = code (φ u) ^^^ code (φ v) := by
  rw [map_add, code_add]

theorem psi_zero : code (φ 0) = 0 := by
  rw [map_zero, code_zero]

theorem psi_lt (v : S.Qt) : code (φ v) < 2 ^ 20 := code_lt _

theorem psi_inj {u v : S.Qt} (h : code (φ u) = code (φ v)) : u = v :=
  φ.injective (code_injective h)

theorem exists_psi {c : Nat} (hc : c < 2 ^ 20) : ∃ u ∈ S.QG, code (φ (S.cl u)) = c := by
  obtain ⟨v, rfl⟩ := exists_code hc
  obtain ⟨u, hu, huv⟩ := S.exists_cl (φ.symm v)
  exact ⟨u, hu, by rw [huv, φ.apply_symm_apply]⟩

@[expose] def Acts (g : G) (F : Nat → Nat) : Prop :=
  ∀ u ∈ S.QG, code (φ (S.cl (g * u * g⁻¹))) = F (code (φ (S.cl u)))

variable {S φ}

theorem Acts.mul {g h : G} {F H : Nat → Nat} (hh : h ∈ S.M) (hg : Acts S φ g F)
    (hH : Acts S φ h H) : Acts S φ (g * h) (fun c => F (H c)) := by
  intro u hu
  have e : g * h * u * (g * h)⁻¹ = g * (h * u * h⁻¹) * g⁻¹ := by group
  rw [e, hg _ (S.conj_mem_QG hh hu), hH u hu]

theorem Acts.lt {g : G} {F : Nat → Nat} (hg : Acts S φ g F) {c : Nat} (hc : c < 2 ^ 20) :
    F c < 2 ^ 20 := by
  obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
  rw [← hg u hu]
  exact psi_lt S φ _

theorem mem_QG_of_acts [Finite G] {g : G} {F : Nat → Nat} (hgM : g ∈ S.M) (hg : Acts S φ g F)
    (hF : ∀ c < 2 ^ 20, F c = c) : g ∈ S.QG :=
  S.mem_QG_of_cl_conj hgM fun u hu => psi_inj S φ (by rw [hg u hu, hF _ (psi_lt S φ _)])

theorem cl_conj_of_mem_QG {g u : G} (hg : g ∈ S.QG) (hu : u ∈ S.QG) :
    S.cl (g * u * g⁻¹) = S.cl u := by
  rcases S.commutator_eq_one_or_z hg hu with h | h
  · have e : g * u * g⁻¹ = u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = u := by rw [h, one_mul]
    rw [e]
  · have e : g * u * g⁻¹ = S.z * u := by
      calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
        _ = S.z * u := by rw [h]
    rw [e, S.cl_mul S.z_mem_QG hu, S.cl_z, zero_add]

theorem acts_of_mem_QG {g : G} {F : Nat → Nat} (hgQ : g ∈ S.QG) (hg : Acts S φ g F) :
    ∀ c < 2 ^ 20, F c = c := by
  intro c hc
  obtain ⟨u, hu, rfl⟩ := exists_psi S φ hc
  rw [← hg u hu, cl_conj_of_mem_QG hgQ hu]

theorem Acts.invol {x : G} {F : Nat → Nat} (hx : IsConj S.z x) (hxM : x ∈ S.M)
    (hF : Acts S φ x F) : ∀ c < 2 ^ 20, F (F c) = c := by
  have h1 : x * x = 1 := SmithQ.mul_self_eq_one_of_isConj S hx
  apply acts_of_mem_QG (g := x * x) (by rw [h1]; exact S.QG.one_mem) (hF.mul hxM hF)

end CFSG.LargeExtraspecial.S14.SMG
