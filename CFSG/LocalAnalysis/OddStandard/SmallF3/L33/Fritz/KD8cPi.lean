module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cTfree

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem interCard_eq_16 : ∀ i j : Fin 8, interCard i j = 16 → i = j := by decide

namespace Conf

variable (K : Conf S T₁)

@[expose] def NormR1 (n : X) : Prop := ∀ g ∈ K.R1, n * g * n⁻¹ ∈ K.R1

theorem Ex_injective {i j : Fin 8} (h : K.Ex i = K.Ex j) : i = j := by
  have := K.card_inf_Ex i j
  rw [h, inf_idem, K.card_Ex] at this
  exact interCard_eq_16 i j this.symm

theorem exists_conj_Ex {n : X} (hn : K.NormR1 n) (i : Fin 8) :
    ∃ j : Fin 8, (K.Ex i).map (MulAut.conj n).toMonoidHom = K.Ex j := by
  have he := K.elem_Ex i
  refine K.eq_Ex_of ?_ (KD46.elem_map he n).comm ?_ ?_
  · rintro _ ⟨e, he', rfl⟩
    exact hn e (K.Ex_le_R1 i he')
  · intro a ha
    rw [← pow_two]; exact (KD46.elem_map he n).sq_eq_one a ha
  · rw [card_map_of_injective (MulAut.conj n).injective, K.card_Ex]

noncomputable def pi {n : X} (hn : K.NormR1 n) (i : Fin 8) : Fin 8 :=
  Classical.choose (K.exists_conj_Ex hn i)

theorem pi_spec {n : X} (hn : K.NormR1 n) (i : Fin 8) :
    (K.Ex i).map (MulAut.conj n).toMonoidHom = K.Ex (K.pi hn i) :=
  Classical.choose_spec (K.exists_conj_Ex hn i)

theorem conj_mem_pi {n : X} (hn : K.NormR1 n) {i : Fin 8} {e : X} (he : e ∈ K.Ex i) :
    n * e * n⁻¹ ∈ K.Ex (K.pi hn i) := by
  rw [← K.pi_spec hn i]
  exact ⟨e, he, rfl⟩

theorem pi_eq_of {n : X} (hn : K.NormR1 n) {i j : Fin 8}
    (h : ∀ e ∈ K.Ex i, n * e * n⁻¹ ∈ K.Ex j) : K.pi hn i = j := by
  apply K.Ex_injective
  rw [← K.pi_spec hn i, K.conj_Ex_of_le h]

theorem interCard_pi {n : X} (hn : K.NormR1 n) (i j : Fin 8) :
    interCard (K.pi hn i) (K.pi hn j) = interCard i j := by
  rw [← K.card_inf_Ex, ← K.card_inf_Ex, ← K.pi_spec hn i, ← K.pi_spec hn j,
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective,
    card_map_of_injective (MulAut.conj n).injective]

theorem pi_injective {n : X} (hn : K.NormR1 n) : Function.Injective (K.pi hn) := by
  intro i j h
  have := K.interCard_pi hn i j
  rw [h, show interCard (K.pi hn j) (K.pi hn j) = 16 by simp [interCard]] at this
  exact interCard_eq_16 i j this.symm

theorem normR1_mul {n m : X} (hn : K.NormR1 n) (hm : K.NormR1 m) : K.NormR1 (n * m) := by
  intro g hg
  rw [show n * m * g * (n * m)⁻¹ = n * (m * g * m⁻¹) * n⁻¹ by group]
  exact hn _ (hm g hg)

theorem pi_mul {n m : X} (hn : K.NormR1 n) (hm : K.NormR1 m) (i : Fin 8) :
    K.pi (K.normR1_mul hn hm) i = K.pi hn (K.pi hm i) := by
  refine K.pi_eq_of _ fun e he => ?_
  rw [show n * m * e * (n * m)⁻¹ = n * (m * e * m⁻¹) * n⁻¹ by group]
  exact K.conj_mem_pi hn (K.conj_mem_pi hm he)

theorem normR1_of_mem_R1 {g : X} (hg : g ∈ K.R1) : K.NormR1 g := fun _ ha =>
  mul_mem (mul_mem hg ha) (inv_mem hg)

theorem pi_of_mem_R1 {g : X} (hg : g ∈ K.R1) (i : Fin 8) : K.pi (K.normR1_of_mem_R1 hg) i = i :=
  K.pi_eq_of _ fun _ he => K.R1_conj_Ex hg he

theorem normR1_w₂ : K.NormR1 (K.ι MC.w₂) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := K.mem_R1.mp hg
  rw [← map_inv, ← map_mul, ← map_mul]
  have key : ∀ a : MC, inR1 a = true → inR1 (MC.w₂ * a * MC.w₂⁻¹) = true := by decide +kernel
  exact K.ι_mem_R1 (key a ha)

theorem pi_w₂ (i : Fin 8) : K.pi K.normR1_w₂ i = sig21 i :=
  K.pi_eq_of _ fun _ he => K.w₂_conj_Ex he

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
