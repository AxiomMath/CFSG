module

import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalComp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Coprime
import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen.Lift
public import CFSG.GroupTheory.SylowIntersectionControl.GomiFact36Inputs

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2NonsplitGen

variable {W : Type} [CommGroup W]

private theorem commute_conj_maps_fap [Finite (MulAut W)]
    {Y L C S : Subgroup (MulAut W)} (hSY : S ≤ Y) (hLY : L ≤ Y)
    (hLc : IsComponent (L.subgroupOf Y)) (hCL : C ≤ L)
    (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W))) {s t : MulAut W} (hs : s ∈ S)
    (ht : t ∈ S) {x y : MulAut W} (hx : x ∈ C.map (MulAut.conj s).toMonoidHom)
    (hy : y ∈ C.map (MulAut.conj t).toMonoidHom) : x * y = y * x := by
  by_cases hst : L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom
  · obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    have hyL : y ∈ L.map (MulAut.conj s).toMonoidHom := by
      rw [hst]
      exact Subgroup.map_mono hCL hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hyL
    have hcl : l * c = c * l := Subgroup.mem_centralizer_iff.mp (hCZ hc) l hl
    exact Commute.map hcl.symm (MulAut.conj s)
  · refine CFSG.ComponentClassification.GrSLit.HeKN.commute_of_components
      (CFSG.ComponentClassification.GrSLit.HeKN.map_conj_le (D := Y) (K := L) hLY
        (hSY hs))
      (CFSG.ComponentClassification.GrSLit.HeKN.map_conj_le (D := Y) (K := L) hLY
        (hSY ht))
      (CFSG.ComponentClassification.GrSLit.HeKN.isComponent_map_conj (D := Y) (K := L) hLc
        ⟨s, hSY hs⟩)
      (CFSG.ComponentClassification.GrSLit.HeKN.isComponent_map_conj (D := Y) (K := L) hLc
        ⟨t, hSY ht⟩) hst x (Subgroup.map_mono hCL hx) y (Subgroup.map_mono hCL hy)

private theorem image_conj_conjSet_fap {G : Type} [Group G] (C S : Subgroup G) {u : G}
    (hu : u ∈ S) :
    (MulAut.conj u).toMonoidHom '' {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} =
      {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} := by
  ext x
  constructor
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    exact ⟨u * s, S.mul_mem hu hs, by
      rw [← CFSG.ComponentClassification.GrSLit.HeKN.map_conj_map_conj C u s]
      exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hy⟩
  · rintro ⟨s, hs, hx⟩
    refine ⟨(MulAut.conj u⁻¹).toMonoidHom x,
      ⟨u⁻¹ * s, S.mul_mem (S.inv_mem hu) hs, ?_⟩, ?_⟩
    · rw [← CFSG.ComponentClassification.GrSLit.HeKN.map_conj_map_conj C u⁻¹ s]
      exact Subgroup.mem_map_of_mem (MulAut.conj u⁻¹).toMonoidHom hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

private theorem le_normalizer_closure_conj_fap {G : Type} [Group G] (C S : Subgroup G) :
    S ≤ Subgroup.normalizer
      (Subgroup.closure {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} :
        Set G) := by
  set E : Subgroup G :=
    Subgroup.closure {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} with hE
  have hmaps : ∀ u ∈ S, ∀ x ∈ E, (MulAut.conj u).toMonoidHom x ∈ E := by
    intro u hu x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        have himg : (MulAut.conj u).toMonoidHom y ∈
            (MulAut.conj u).toMonoidHom ''
              {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} :=
          Set.mem_image_of_mem _ hy
        rw [image_conj_conjSet_fap C S hu] at himg
        exact Subgroup.subset_closure himg
    | one => rw [map_one]; exact E.one_mem
    | mul a b _ _ iha ihb => rw [map_mul]; exact E.mul_mem iha ihb
    | inv a _ iha => rw [map_inv]; exact E.inv_mem iha
  intro u hu
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact hmaps u hu y hy
  · intro x hx
    have hx' := hmaps u⁻¹ (S.inv_mem hu) x hx
    have hround : (MulAut.conj u).toMonoidHom ((MulAut.conj u⁻¹).toMonoidHom x) = x := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [← hround]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx'

private theorem pow_card_of_mem_closure_fap {G : Type} [Group G] {C S : Subgroup G}
    {K : Set G} (hK : K = {x : G | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom})
    (hpair : K.Pairwise Commute) {x : G} (hx : x ∈ Subgroup.closure K) :
    x ^ Nat.card C = 1 := by
  have hn : ∀ k ∈ K, k ^ Nat.card C = 1 := by
    rintro k hk
    rw [hK] at hk
    obtain ⟨s, -, hm⟩ := hk
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hm
    have hcp : c ^ Nat.card C = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard C hc)
    rw [← map_pow (MulAut.conj s).toMonoidHom, hcp, map_one]
  exact pow_eq_one_of_mem_closure hpair hn hx

theorem GomiFact36Hyp.eq_bot_of_fixV_le [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y S L : Subgroup (MulAut W)} (h : GomiFact36Hyp Y S L) {C : Subgroup (MulAut W)}
    (hCL : C ≤ L) (hCZ : C ≤ Subgroup.centralizer (L : Set (MulAut W)))
    (hodd : Odd (Nat.card C)) (hfix : fixV S ≤ fixV C) : C = ⊥ := by
  classical
  obtain ⟨hSY, hLY, hLc, -, -, -, -⟩ := h
  set K : Set (MulAut W) := {x | ∃ s ∈ S, x ∈ C.map (MulAut.conj s).toMonoidHom} with hK
  have hCE : C ≤ Subgroup.closure K := by
    intro c hc
    refine Subgroup.subset_closure ⟨1, S.one_mem, ?_⟩
    simpa [MulAut.conj_apply] using
      Subgroup.mem_map_of_mem (MulAut.conj (1 : MulAut W)).toMonoidHom hc
  have hpair : K.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨t, ht, hyt⟩ := hy
    exact commute_conj_maps_fap hSY.1 hLY hLc hCL hCZ hs ht hxs hyt
  have hEexp : ∀ x ∈ Subgroup.closure K, x ^ Nat.card C = 1 := fun x hx =>
    pow_card_of_mem_closure_fap hK hpair hx
  have h2C : ¬ 2 ∣ Nat.card C := fun hd =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)
  have hE2 : ¬ 2 ∣ Nat.card (Subgroup.closure K) :=
    not_dvd_card_of_pow_eq_one Nat.prime_two h2C _ hEexp
  have hSE : S ≤ Subgroup.normalizer (Subgroup.closure K : Set (MulAut W)) :=
    le_normalizer_closure_conj_fap C S
  have hEfix : Subgroup.closure K ≤ centSub (fixV S) := by
    refine (Subgroup.closure_le (centSub (fixV S))).mpr ?_
    rintro x ⟨s, hs, hx⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    refine mem_centSub.mpr ?_
    intro v hv
    have hsv : (s⁻¹ : MulAut W) v = v := mem_fixV.mp hv s⁻¹ (S.inv_mem hs)
    have hcv : c v = v := mem_fixV.mp (hfix hv) c hc
    have hsv' : s v = v := mem_fixV.mp hv s hs
    show (MulAut.conj s).toMonoidHom c v = v
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [MulAut.mul_apply, hsv, hcv, hsv']
  have hbot : Subgroup.closure K = ⊥ := by
    have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16c11_inf_centSub_fixV_eq_bot
      (W := W) hW (P := Subgroup.closure K) (S := S) hE2 hSY.2.1 hSE
    rwa [inf_eq_left.mpr hEfix] at h
  exact eq_bot_iff.mpr (hbot ▸ hCE)

end CFSG.GroupTheory
