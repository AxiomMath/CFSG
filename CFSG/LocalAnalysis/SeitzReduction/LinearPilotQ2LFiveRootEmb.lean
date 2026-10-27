module

public import CFSG.RankThree.PartTwo.KFacts.L34Automizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWModel

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup MulAction CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Count

variable {E X : Type*} [Group E] [MulAction E X]

theorem false_of_card_fixedBy_eq [Finite E] [Finite X] (hE : Nat.card E = 9)
    (hX : Nat.card X = 32) (hdvd : ∀ g : E, Nat.card (fixedBy X g) ∣ 32)
    (hne : ∀ g : E, g ≠ 1 → Nat.card (fixedBy X g) ≠ 32)
    (heq : ∀ g h : E, g ≠ 1 → h ≠ 1 → Nat.card (fixedBy X g) = Nat.card (fixedBy X h)) :
    False := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have : Fintype X := Fintype.ofFinite X
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group E X
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : E, g₀ ≠ 1 := by
    by_contra h
    push Not at h
    have : Subsingleton E := ⟨fun a b => (h a).trans (h b).symm⟩
    rw [Nat.card_unique] at hE
    norm_num at hE
  set f := Nat.card (fixedBy X g₀) with hf
  have hsum : ∑ g : E, Fintype.card (fixedBy X g) = 32 + 8 * f := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : E))]
    have h1 : Fintype.card (fixedBy X (1 : E)) = 32 := by
      rw [← Nat.card_eq_fintype_card, fixedBy_one_eq_univ, Nat.card_univ, hX]
    have h2 : ∀ g ∈ (Finset.univ : Finset E).erase 1, Fintype.card (fixedBy X g) = f := by
      intro g hg
      rw [← Nat.card_eq_fintype_card, hf]
      exact heq g g₀ (Finset.ne_of_mem_erase hg) hg₀
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, ← Nat.card_eq_fintype_card, hE, smul_eq_mul]
  rw [hsum, ← Nat.card_eq_fintype_card (α := E), hE] at hburn
  have hdiv : 9 ∣ 32 + 8 * f := ⟨_, hburn.trans (mul_comm _ _)⟩
  have hf32 : f ∣ 32 := hdvd g₀
  have hfne : f ≠ 32 := hne g₀ hg₀
  have hfle : f ≤ 32 := Nat.le_of_dvd (by norm_num) hf32
  interval_cases f <;> omega

end Count

section Fixed

variable {ι R : Type*} [DecidableEq ι] [Fintype ι] [CommRing R]

@[expose] def specialLinearFixedAddSubgroup (A : Matrix.SpecialLinearGroup ι R) :
    AddSubgroup (ι → R) where
  carrier := fixedBy (ι → R) A
  add_mem' := fun {v w} hv hw => by
    rw [mem_fixedBy] at hv hw ⊢
    rw [smul_add, hv, hw]
  zero_mem' := by rw [mem_fixedBy, smul_zero]
  neg_mem' := fun {v} hv => by
    rw [mem_fixedBy] at hv ⊢
    rw [smul_neg, hv]

theorem card_fixedBy_specialLinear_dvd (A : Matrix.SpecialLinearGroup ι R) :
    Nat.card (fixedBy (ι → R) A) ∣ Nat.card (ι → R) :=
  AddSubgroup.card_addSubgroup_dvd_card (specialLinearFixedAddSubgroup A)

theorem specialLinear_eq_one_of_forall_smul_eq {A : Matrix.SpecialLinearGroup ι R}
    (h : ∀ v : ι → R, A • v = v) : A = 1 := by
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro v
  have hv := h v
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec] at hv
  rw [hv, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem card_fixedBy_specialLinear_ne [Finite R] {A : Matrix.SpecialLinearGroup ι R}
    (hA : A ≠ 1) :
    Nat.card (fixedBy (ι → R) A) ≠ Nat.card (ι → R) := by
  intro h
  apply hA
  refine specialLinear_eq_one_of_forall_smul_eq fun v => ?_
  have hu : fixedBy (ι → R) A = Set.univ := by
    rw [Set.eq_univ_iff_ncard, ← Nat.card_coe_set_eq, h]
  have hv : v ∈ fixedBy (ι → R) A := by rw [hu]; exact Set.mem_univ v
  exact hv

end Fixed

theorem natCard_fixedBy_conj {M Y : Type*} [Group M] [MulAction M Y] (g h : M) :
    Nat.card (fixedBy Y (h * g * h⁻¹)) = Nat.card (fixedBy Y g) := by
  rw [← smul_fixedBy, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_smul_set]

section Embedding

open CFSG.RankThree.PartTwo.KFacts.L34

variable {F K : Type*} [Field F] [Field K]

theorem not_injective_projectiveSL_three_four_specialLinear_five_two (hF : Nat.card F = 4)
    (hK : Nat.card K = 2) {ρ : projectiveSL 3 F →* Matrix.SpecialLinearGroup (Fin 5) K}
    (hρ : Function.Injective ρ) : False := by
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set E' : Subgroup (Matrix.SpecialLinearGroup (Fin 5) K) := (eZero F).map ρ with hE'
  have hE'c : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective hρ, card_eZero hF]
  have hE'fin : Finite E' := Nat.finite_of_card_ne_zero (by omega)
  have hX : Nat.card (Fin 5 → K) = 32 := by
    rw [Nat.card_fun, hK, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hfix : ∀ g : E', fixedBy (Fin 5 → K) g =
      fixedBy (Fin 5 → K) (g : Matrix.SpecialLinearGroup (Fin 5) K) := fun g => rfl
  refine false_of_card_fixedBy_eq hE'c hX (fun g => ?_) (fun g hg => ?_) (fun g h hg hh => ?_)
  · rw [hfix, ← hX]
    exact card_fixedBy_specialLinear_dvd _
  · rw [hfix, ← hX]
    exact card_fixedBy_specialLinear_ne fun h1 => hg (Subtype.ext h1)
  · obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.1 h.2
    have hx1 : x ≠ 1 := by
      rintro rfl
      apply hg
      apply Subtype.ext
      rw [← hxg, map_one]
      rfl
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hh
      apply Subtype.ext
      rw [← hyh, map_one]
      rfl
    obtain ⟨m, -, hm⟩ :=
      exists_mem_normalizer_conj_eq_of_card_eq_nine hF (card_eZero hF) hx hx1 hy hy1
    rw [hfix, hfix, ← hyh, ← hm, map_mul, map_mul, map_inv, hxg, natCard_fixedBy_conj]

theorem not_injective_projectiveSL_three_four_five_two (hF : Nat.card F = 4)
    (hK : Nat.card K = 2) {ρ : projectiveSL 3 F →* projectiveSL 5 K}
    (hρ : Function.Injective ρ) : False := by
  set π : Matrix.SpecialLinearGroup (Fin 5) K ≃* projectiveSL 5 K :=
    MulEquiv.ofBijective (proj 5 K) ⟨proj_injective_of_natCard_eq_two hK, proj_surjective 5 K⟩
  exact not_injective_projectiveSL_three_four_specialLinear_five_two hF hK
    (ρ := π.symm.toMonoidHom.comp ρ) (π.symm.injective.comp hρ)

end Embedding

end CFSG.SeitzReduction.LinearPilot
