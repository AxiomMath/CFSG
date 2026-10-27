module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888L5a1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem s888l5a2_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private theorem s888l5a2_sup_le_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    K₁ ⊔ K₂ ≤ L :=
  sup_le (fun _ hx => (c.pocket₁.2.1 hx).1) (fun _ hx => (c.pocket₂.2.1 hx).1)

theorem qsub_inf_centralizer_le_C6 (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Qsub K₁ K₂ h ⊓ centralizer ({t} : Set G) ≤ Sec5C6 L K₁ K₂ := by
  intro q hq
  obtain ⟨hqQ, hqt⟩ := hq
  have hquad := sec5b517_quad h514 c
  have hQ : Qsub K₁ K₂ h = Sec5B517Q8 hquad := by
    rw [sec5b517_Qsub_eq, hquad.core_eq]
  have hq8 : q ∈ Sec5B517Q8 hquad := hQ ▸ hqQ
  obtain ⟨a, ha12, b, hb23, hqab⟩ := Sec5B517Q8.exists_pair_mul hquad hq8
  have ha_core : a ∈ twoCoreIn (K₁ ⊔ K₂) := by
    have hpair := Sec5B517Q8.twoCoreIn_sup_eq_pair hquad (i := 0) (j := 1) (by decide)
    rw [show Kfam5 K₁ K₂ h 0 = K₁ by simp [Kfam5],
      show Kfam5 K₁ K₂ h 1 = K₂ by simp [Kfam5]] at hpair
    rw [hpair]
    exact ha12
  have haC6 : a ∈ Sec5C6 L K₁ K₂ := by
    rw [Sec5C6]
    exact Subgroup.mem_sup_left ha_core
  have haCt : a ∈ centralizer ({t} : Set G) :=
    c.component.le (s888l5a2_sup_le_L c (s888l5a2_twoCoreIn_le_self _ ha_core))
  have hbCt : b ∈ centralizer ({t} : Set G) := by
    have hb_eq : b = a⁻¹ * q := by rw [hqab]; group
    rw [hb_eq]
    exact mul_mem (inv_mem haCt) hqt
  have hbK34 : b ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := by
    simpa [Kfam5] using hb23.2
  have hb_cent : b ∈ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h14 := h514 G t L S z r B A K₁ K₂ h c
    have hmem := Subgroup.commutator_mem_commutator hx hbK34
    rw [h14.1] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hmem)
  have hbN : b ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (sec5_conj_L h52a c hbCt)
  have hbC6 : b ∈ Sec5C6 L K₁ K₂ := by
    rw [Sec5C6]
    exact Subgroup.mem_sup_right ⟨hbN, hb_cent⟩
  rw [hqab]
  exact mul_mem haC6 hbC6

end CFSG.OddStandard.SmallF3.Omega
