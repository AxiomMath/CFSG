module

public import CFSG.GH74.GLS.C3.Layer2.L5C3a
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3a
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
public meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
public meta import CFSG.GH74.GLS.C3.Layer2.FinModelEnum
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
public meta import CFSG.GH74.GLS.C3.Layer2.L5A1
public meta import CFSG.GH74.GLS.C3.Layer2.L5B2
public meta import CFSG.GH74.GLS.C3.Layer2.L5C0
public import CFSG.GH74.GLS.C3.Layer2.L5C3bInputs
public meta import CFSG.GH74.GLS.C3.Layer2.L5C3bInputs
public import Certificates.Certificate5051
public import Certificates.Certificate5060

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer2.Model

section Words

variable {M N : Type*} [Monoid M] [Monoid N]

theorem getD_map_hom (f : M →* N) (gens : List M) (i : ℕ) :
    (gens.map f).getD i 1 = f (gens.getD i 1) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : gens[i]? with
  | none => simp
  | some x => simp

theorem wval_map (f : M →* N) (gens : List M) (w : List ℕ) :
    f (wval gens w) = wval (gens.map f) w := by
  unfold wval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (getD_map_hom f gens i).symm

end Words

theorem gensS0_eq : gensS0 = [tr1 1, tr1 2, tr1 4, tr1 8, gS1, gS2] := map_nrm _

theorem noCHatChk_true : noCHatChk S0L1 = true :=
  Certificates.certificate5060

theorem tr1_mem_S0 (i : Fin 16) : tr1 i ∈ S0subP1 := by
  have h := RhatL1_sub
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  exact h (tr1 i) (by
    unfold RhatL1
    exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)

theorem sh1_S0_no_cHat :
    ¬ ∃ γ : ↥S0subP1 ≃* ↥S0subP1, ∀ (s : ↥S0subP1) (i : Fin 16),
    (s : Perm (Fin 16)) = tr1 i → ((γ s : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat i) := by
  rintro ⟨γ, hγ⟩
  have hchk := noCHatChk_true
  unfold noCHatChk at hchk
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true', map_nrm] at hchk
  obtain ⟨⟨⟨hsound, hcompl⟩, hgens⟩, hcand⟩ := hchk
  have hg : ∀ g ∈ gensS0, g ∈ S0subP1 := fun g hg' => mem_S0subP1.2 (hgens g hg')
  rw [gensS0_eq] at hg hsound
  let x1 : ↥S0subP1 := ⟨tr1 1, tr1_mem_S0 1⟩
  let x2 : ↥S0subP1 := ⟨tr1 2, tr1_mem_S0 2⟩
  let x4 : ↥S0subP1 := ⟨tr1 4, tr1_mem_S0 4⟩
  let x8 : ↥S0subP1 := ⟨tr1 8, tr1_mem_S0 8⟩
  let y1 : ↥S0subP1 := ⟨gS1, hg gS1 (by simp)⟩
  let y2 : ↥S0subP1 := ⟨gS2, hg gS2 (by simp)⟩
  let gensG : List ↥S0subP1 := [x1, x2, x4, x8, y1, y2]
  have hgensG : gensG.map S0subP1.subtype =
      [tr1 1, tr1 2, tr1 4, tr1 8, gS1, gS2] := rfl
  let u₁ : Perm (Fin 16) := ((γ y1 : ↥S0subP1) : Perm (Fin 16))
  let u₂ : Perm (Fin 16) := ((γ y2 : ↥S0subP1) : Perm (Fin 16))
  have hu₁S : u₁ ∈ S0L1 := mem_S0subP1.1 (γ y1).2
  have hu₂S : u₂ ∈ S0L1 := mem_S0subP1.1 (γ y2).2
  let images : List (Perm (Fin 16)) :=
    [tr1 (cHat 1), tr1 (cHat 2), tr1 (cHat 4), tr1 (cHat 8), u₁, u₂]
  have himg : (gensG.map γ.toMonoidHom).map S0subP1.subtype = images := by
    have e1 : ((γ x1 : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat 1) := hγ x1 1 rfl
    have e2 : ((γ x2 : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat 2) := hγ x2 2 rfl
    have e4 : ((γ x4 : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat 4) := hγ x4 4 rfl
    have e8 : ((γ x8 : ↥S0subP1) : Perm (Fin 16)) = tr1 (cHat 8) := hγ x8 8 rfl
    show [((γ x1 : ↥S0subP1) : Perm (Fin 16)), ((γ x2 : ↥S0subP1) : Perm (Fin 16)),
      ((γ x4 : ↥S0subP1) : Perm (Fin 16)), ((γ x8 : ↥S0subP1) : Perm (Fin 16)), u₁, u₂] = images
    rw [e1, e2, e4, e8]
  have hγword : ∀ e ∈ tabS0, ∀ (he : e.1 ∈ S0subP1),
      ((γ ⟨e.1, he⟩ : ↥S0subP1) : Perm (Fin 16)) = wval images e.2 := by
    intro e he hmem
    obtain ⟨hev, -⟩ := hsound e he
    have h1 : wval gensG e.2 = ⟨e.1, hmem⟩ := by
      apply Subtype.ext
      have h0 := wval_map S0subP1.subtype gensG e.2
      rw [hgensG] at h0
      show ((wval gensG e.2 : ↥S0subP1) : Perm (Fin 16)) = e.1
      exact h0.trans hev
    have h2 := wval_map γ.toMonoidHom gensG e.2
    have h3 := wval_map S0subP1.subtype (gensG.map γ.toMonoidHom) e.2
    rw [himg] at h3
    rw [← h1]
    show ((γ.toMonoidHom (wval gensG e.2) : ↥S0subP1) : Perm (Fin 16)) = _
    rw [h2]
    exact h3
  have hhom : homTab tabS0 images = true := by
    unfold homTab
    simp only [List.all_eq_true, List.any_eq_true, List.mem_map, Bool.and_eq_true, beq_iff_eq,
      map_nrm, nrm_eq]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨haev, haS⟩ := hsound a ha
    obtain ⟨hbev, hbS⟩ := hsound b hb
    have haS' : a.1 ∈ S0subP1 := mem_S0subP1.2 haS
    have hbS' : b.1 ∈ S0subP1 := mem_S0subP1.2 hbS
    have hab : a.1 * b.1 ∈ S0subP1 := mul_mem haS' hbS'
    obtain ⟨c, hc, hca⟩ := hcompl _ (mem_S0subP1.1 hab)
    have hcS : c.1 ∈ S0subP1 := by rw [hca]; exact hab
    refine ⟨_, ⟨c, hc, rfl⟩, hca, ?_⟩
    have h1 := hγword a ha haS'
    have h2 := hγword b hb hbS'
    have h3 := hγword c hc hcS
    have hmul : (⟨c.1, hcS⟩ : ↥S0subP1) = ⟨a.1, haS'⟩ * ⟨b.1, hbS'⟩ := Subtype.ext hca
    rw [← h1, ← h2, ← h3, hmul, map_mul, Subgroup.coe_mul]
  have hcont := hcand u₁ hu₁S u₂ hu₂S
  rw [hhom] at hcont
  exact Bool.noConfusion hcont

end CFSG.GH74.GLS.C3.Layer2.L5
