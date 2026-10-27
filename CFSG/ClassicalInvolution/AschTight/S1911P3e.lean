module

public import CFSG.ClassicalInvolution.AschTight.S1911P3d

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem surjective_hom_of_card_eq_one (D : LieSystemData p f X Φ) (hcard : D.card = 1)
    (i : Fin D.card) : Function.Surjective (D.hom i) := by
  have : Subsingleton (Fin D.card) := by rw [hcard]; infer_instance
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← D.generate]
  exact iSup_le fun j => by rw [Subsingleton.elim j i]

noncomputable def ih8Model_of_lieSystemData (D : LieSystemData p f X Φ) (hcard : D.card = 1)
    (i : Fin D.card) (hconj : ConjInvariant Φ) :
    Ih8Model p f Φ (D.tag i) (D.rank i) (D.exp i) where
  isFundTag := D.isFundTag i
  admissible := D.admissible i
  exp_eq := D.exp_eq i
  ψ := D.hom i
  ker_le_center := D.ker_le_center i
  surj := surjective_hom_of_card_eq_one D hcard i
  cls := {R | R ∈ fundamentalSubgroups (D.tag i)
    (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D ∧ R.map (D.hom i) ∈ Φ}
  cls_sub := fun _ h => h.1
  mem_iff := by
    intro L
    constructor
    · intro hL
      obtain ⟨j, R, hR, rfl⟩ := D.fundamental L hL
      have : Subsingleton (Fin D.card) := by rw [hcard]; infer_instance
      obtain rfl : j = i := Subsingleton.elim j i
      exact ⟨R, ⟨hR, hL⟩, rfl⟩
    · rintro ⟨R, ⟨-, hR⟩, rfl⟩
      exact hR
  cls_conj := by
    rintro R ⟨⟨g', γ, hγ, rfl⟩, hR⟩ g
    refine ⟨⟨g * g', γ, hγ, (conjSub_mul g g' _).symm⟩, ?_⟩
    rw [← conjSub_map]
    exact hconj _ _ hR

theorem isSimpleGroup_of_lieSystemData [Finite X] [Nontrivial X] (hM3 : FactM3) (hp2 : p ≠ 2)
    (D : LieSystemData p f X Φ) (hcard : D.card = 1) (i : Fin D.card)
    (htag : IsT6Tag (D.tag i) (D.rank i)) (hO : classicalInvolutionOddCore X = ⊥) :
    IsSimpleGroup X := by
  have hsurj := surjective_hom_of_card_eq_one D hcard i
  have hq := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero (D.tag i) (D.rank i) p
    (D.exp i) Fact.out (D.isFundTag i) (D.admissible i)).1
  have hZ := hM3 p (D.exp i) Fact.out hp2 _ _ htag (D.admissible i)
  refine ⟨fun N hN => ?_⟩
  set M := N.comap (D.hom i) with hM
  have hMn : M.Normal := hN.comap _
  have := hq.2
  have : (M.map (QuotientGroup.mk' (Subgroup.center
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K))) with h | h
  · left
    have hMZ : M ≤ Subgroup.center _ := by
      intro x hx
      have : (QuotientGroup.mk' _ x : _ ⧸ Subgroup.center _) ∈ M.map (QuotientGroup.mk' _) :=
        ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hNle : N ≤ (Subgroup.center _).map (D.hom i) := by
      intro y hy
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, hMZ hy, rfl⟩
    have hodd : Odd (Nat.card N) :=
      hZ.of_dvd_nat ((Subgroup.card_dvd_of_le hNle).trans (Subgroup.card_map_dvd _ _))
    have : N ≤ classicalInvolutionOddCore X := le_sSup ⟨hN, hodd⟩
    rw [hO] at this
    exact le_bot_iff.mp this
  · right
    have hMtop : M = ⊤ := by
      refine eq_top_of_perfect_of_sup_center hq.1 ?_
      rw [eq_top_iff]
      intro x _
      have hx : (QuotientGroup.mk' _ x : _ ⧸ Subgroup.center _) ∈ M.map (QuotientGroup.mk' _) := by
        rw [h]
        trivial
      obtain ⟨y, hy, hyx⟩ := hx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hyx
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hy hyx
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    have : x ∈ M := hMtop ▸ Subgroup.mem_top x
    exact this

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
