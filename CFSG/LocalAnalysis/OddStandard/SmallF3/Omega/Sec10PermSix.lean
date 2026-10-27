module

public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem nonempty_mulEquiv_perm_six {M : Type*} [Group M] {D K : Subgroup M} (hKD : K ≤ D)
    (hD : Nat.card D = 720) (hK : Nat.card K = 120)
    (hcore : ∀ d ∈ D, (∀ g ∈ D, g * d * g⁻¹ ∈ K) → d = 1) :
    Nonempty (↥D ≃* Equiv.Perm (Fin 6)) := by
  classical
  haveI : Finite ↥D := Nat.finite_of_card_ne_zero (by omega)
  have hK' : Nat.card (K.subgroupOf D) = 120 := by
    rw [← hK]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKD).toEquiv
  have hidx : (K.subgroupOf D).index = 6 := by
    have h := (K.subgroupOf D).card_mul_index
    rw [hD, hK'] at h
    omega
  have hcardQ : Nat.card (↥D ⧸ K.subgroupOf D) = 6 := by
    rw [← (K.subgroupOf D).index_eq_card, hidx]
  have hker : (MulAction.toPermHom ↥D (↥D ⧸ K.subgroupOf D)).ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker, eq_bot_iff]
    intro d hd
    have hd' : ∀ b : ↥D, b * d * b⁻¹ ∈ K.subgroupOf D := hd
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hcore d d.2 fun g hg => ?_
    have := hd' ⟨g, hg⟩
    rwa [Subgroup.mem_subgroupOf] at this
  have hinj : Function.Injective (MulAction.toPermHom ↥D (↥D ⧸ K.subgroupOf D)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hcardP : Nat.card (Equiv.Perm (↥D ⧸ K.subgroupOf D)) = Nat.card ↥D := by
    rw [Nat.card_perm, hcardQ, hD]
    rfl
  have hbij : Function.Bijective (MulAction.toPermHom ↥D (↥D ⧸ K.subgroupOf D)) :=
    (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, hcardP.symm⟩
  exact ⟨(MulEquiv.ofBijective _ hbij).trans
    ((Finite.equivFin (↥D ⧸ K.subgroupOf D)).trans (finCongr hcardQ)).permCongrHom⟩

end CFSG.OddStandard.SmallF3.Omega
