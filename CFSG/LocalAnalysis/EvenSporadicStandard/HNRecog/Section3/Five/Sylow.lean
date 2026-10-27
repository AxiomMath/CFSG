module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.FiveLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Klein
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongr

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem exists_mulEquiv_Gxy_coe {G : Type} [Group G] {a x : G} (hx : x ∈ Gx a) :
    ∃ e : ↥(Gxy a x) ≃* ↥(Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a))),
      ∀ g : ↥(Gxy a x),
        (((e g : ↥(Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a)))) : ↥(Gx a)) : G) =
          (g : G) := by
  have hcentral : Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a)) =
      (Gx x).subgroupOf (Gx a) := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, mem_Gx]
    exact ⟨fun h => (congrArg Subtype.val h).symm, fun h => Subtype.ext h.symm⟩
  have hsub : (Gx a ⊓ Gx x).subgroupOf (Gx a) = (Gx x).subgroupOf (Gx a) := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2, h⟩⟩
  let e1 : ↥(Gxy a x) ≃* ↥(Gx a ⊓ Gx x) := MulEquiv.subgroupCongr (Gxy_eq_inf a x)
  let e2 : ↥(Gx a ⊓ Gx x) ≃* ↥((Gx a ⊓ Gx x).subgroupOf (Gx a)) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : Gx a ⊓ Gx x ≤ Gx a)).symm
  let e3 : ↥((Gx a ⊓ Gx x).subgroupOf (Gx a)) ≃* ↥((Gx x).subgroupOf (Gx a)) :=
    MulEquiv.subgroupCongr hsub
  let e4 : ↥((Gx x).subgroupOf (Gx a)) ≃*
      ↥(Subgroup.centralizer ({(⟨x, hx⟩ : ↥(Gx a))} : Set ↥(Gx a))) :=
    (MulEquiv.subgroupCongr hcentral).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4)), fun g => rfl⟩

theorem exists_sylow_two_five_Gxy {G : Type} [Group G] {a z : G} {z₀ b u : ↥(Gx a)}
    (hF : TwoHSFacts ↥(Gx a) (GxSelf a) z₀ b u) (hu : IsConj z (u : G))
    (hau : IsConj z (a * (u : G))) {ρ : G} (hρ : ρ ∈ Gx a) (h5 : orderOf ρ = 5)
    (hshape : IsShapeCentralizerFiveB ↥(Gxy a ρ)) (T : Sylow 2 ↥(Gxy a ρ)) :
    ∃ u' : G, IsConj z u' ∧ IsConj z (a * u') ∧
      (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype = Subgroup.closure {a, u'} := by
  have h5' : orderOf (⟨ρ, hρ⟩ : ↥(Gx a)) = 5 := by
    rw [Subgroup.orderOf_mk, h5]
  obtain ⟨e, he⟩ := exists_mulEquiv_Gxy_coe (G := G) (a := a) (x := ρ) hρ
  haveI : Finite ↥(Gxy a ρ) := by
    obtain ⟨φ⟩ := hshape
    exact Finite.of_injective φ φ.injective
  have hshape' : IsShapeCentralizerFiveB
      ↥(Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a))) :=
    IsShapeCentralizerFiveB.of_mulEquiv e hshape
  let T' : Sylow 2 ↥(Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a))) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  obtain ⟨u₁, hu₁, hT'⟩ := hF.sylow_two_five (⟨ρ, hρ⟩ : ↥(Gx a)) h5' hshape' T'
  have hcoe : (T' : Subgroup ↥(Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a)))) =
      (T : Subgroup ↥(Gxy a ρ)).map e.toMonoidHom := rfl
  have hcomp : (Gxy a ρ).subtype =
      (Gx a).subtype.comp
        ((Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a))).subtype.comp e.toMonoidHom) := by
    ext g
    exact (he g).symm
  have hmap : (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype =
      ((T' : Subgroup ↥(Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a)))).map
        (Subgroup.centralizer ({(⟨ρ, hρ⟩ : ↥(Gx a))} : Set ↥(Gx a))).subtype).map (Gx a).subtype := by
    rw [hcomp, ← Subgroup.map_map, ← Subgroup.map_map, hcoe]
  refine ⟨(u₁ : G), hu.trans (MonoidHom.map_isConj (Gx a).subtype hu₁), ?_, ?_⟩
  · obtain ⟨h, hh⟩ := isConj_iff.1 hu₁
    have hhG : (h : G) * (u : G) * (h : G)⁻¹ = (u₁ : G) := by
      have := congrArg (fun z : ↥(Gx a) => (z : G)) hh
      simpa using this
    have hcomm : a * (h : G) = (h : G) * a := mem_Gx.mp h.2
    refine hau.trans ?_
    refine isConj_iff.mpr ⟨(h : G), ?_⟩
    calc (h : G) * (a * (u : G)) * (h : G)⁻¹
        = ((h : G) * a) * (u : G) * (h : G)⁻¹ := by rw [← mul_assoc]
      _ = (a * (h : G)) * (u : G) * (h : G)⁻¹ := by rw [hcomm.symm]
      _ = a * ((h : G) * (u : G) * (h : G)⁻¹) := by simp only [mul_assoc]
      _ = a * (u₁ : G) := by rw [hhG]
  · rw [hmap, hT', MonoidHom.map_closure, Set.image_pair]
    rfl

theorem five_sylow (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Fusion1Facts a z) (hF2 : Fusion2Facts a z) : FiveSylowFacts a z := by
  refine ⟨fun ρ hρ h5 hshape T => ?_⟩
  obtain ⟨z₀, b, u, hF, hz₀, _⟩ := hF1.rep_z
  obtain ⟨hu, hau, _⟩ := (hF2.reps_bu z₀ b u hF hz₀).2
  obtain ⟨u', hu', hau', hT⟩ := exists_sylow_two_five_Gxy hF hu hau hρ h5 hshape T
  have hnotconj : ¬ IsConj a z := not_isConj_of_isF5Type hI h
  have horder_u' : orderOf u' = 2 := by
    obtain ⟨c, hc⟩ := hu'
    exact (SemiconjBy.orderOf_eq (c : G) hc).symm.trans h.orderOf_z
  have ha2 : a * a = 1 := by
    rw [← pow_two, ← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have hu'2 : u' * u' = 1 := by
    rw [← pow_two, ← horder_u']
    exact pow_orderOf_eq_one u'
  have ha_ne_one : a ≠ 1 := by
    intro h1
    have h1' : orderOf a = 1 := by rw [h1, orderOf_one]
    rw [h.orderOf_a] at h1'
    exact (by decide : (2 : ℕ) ≠ 1) h1'
  have hu'_ne_one : u' ≠ 1 := by
    intro h1
    have h1' : orderOf u' = 1 := by rw [h1, orderOf_one]
    rw [horder_u'] at h1'
    exact (by decide : (2 : ℕ) ≠ 1) h1'
  have haneq : a ≠ u' := by
    intro heq
    apply hnotconj
    rw [heq]
    exact hu'.symm
  have hu'L : u' ∈ Gxy a ρ := by
    have hmem : u' ∈ (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype := by
      rw [hT]
      exact Subgroup.subset_closure (by simp)
    exact Subgroup.map_subtype_le (T : Subgroup ↥(Gxy a ρ)) hmem
  have hau'comm : a * u' = u' * a := mem_Gx.mp (mem_Gxy.mp hu'L).1
  have hcardT : Nat.card ↥(T : Subgroup ↥(Gxy a ρ)) = 4 := by
    rw [← Subgroup.card_subtype (Gxy a ρ) (T : Subgroup ↥(Gxy a ρ))]
    rw [hT]
    exact card_closure_pair_of_involutions ha2 hu'2 hau'comm ha_ne_one hu'_ne_one haneq
  have hpad : padicValNat 2 (Nat.card ↥(Gx ρ)) = 2 := by
    have hN : ∀ n ∈ Gx ρ, n ∈ Subgroup.normalizer
        (((T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype : Subgroup G) : Set G) → n ∈ Gxy a ρ := by
      intro n hnρ hnN
      rw [mem_Gxy]
      refine ⟨?_, hnρ⟩
      have haT : a ∈ (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype := by
        rw [hT]
        exact Subgroup.subset_closure (by simp)
      have hna : n * a * n⁻¹ ∈ (T : Subgroup ↥(Gxy a ρ)).map (Gxy a ρ).subtype :=
        (Subgroup.mem_set_normalizer_iff.mp hnN a).mp haT
      rw [hT, mem_closure_pair_iff_of_involutions ha2 hu'2 hau'comm] at hna
      rcases hna with h1 | ha | hu'case | haucase
      · exact (ha_ne_one (isConj_one_left.mp (isConj_iff.mpr ⟨n, h1⟩))).elim
      · rw [mem_Gx]
        have hcomm : n * a = a * n := by
          have := congrArg (fun x => x * n) ha
          simpa [mul_assoc] using this
        exact hcomm.symm
      · exact (hnotconj ((isConj_iff.mpr ⟨n, hu'case⟩).trans hu'.symm)).elim
      · exact (hnotconj ((isConj_iff.mpr ⟨n, haucase⟩).trans hau'.symm)).elim
    have hpad' := padicValNat_card_eq_of_normalizer_le (p := 2) (K := Gx ρ) (L := Gxy a ρ)
      (fun g hg => (mem_Gxy.mp hg).2) T hN
    have h4 : padicValNat 2 4 = 2 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact padicValNat_base_pow (by norm_num : 1 < 2) 2
    rw [hpad', hcardT]
    exact h4
  exact ⟨u', hu', hau', hcardT, hT, hpad⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
