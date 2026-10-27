module

public import CFSG.Sporadic.SmallOddCore.Co3Local

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.SeitzReduction.SporadicRefine

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Blueprint
open CFSG.Sporadic.SmallOddCore CFSG.LocalAnalysis.ComponentInitial

theorem card_center_and_quotient_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (center G) = Nat.card (center H) ∧
      Nat.card (G ⧸ center G) = Nat.card (H ⧸ center H) := by
  have hmap : (center G).map e.toMonoidHom = center H := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg e (Subgroup.mem_center_iff.1 hx (e.symm g))
      simpa using h1
    · intro hy
      refine ⟨e.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
      have h1 := congrArg e.symm (Subgroup.mem_center_iff.1 hy (e g))
      simpa using h1
  exact ⟨Nat.card_congr (Subgroup.centerCongr e).toEquiv,
    Nat.card_congr (QuotientGroup.congr _ _ e hmap).toEquiv⟩

theorem co3P_component_card
    {τ : Equiv.Perm (Fin 276)} (hτP : τ ∈ co3P) (hτ : orderOf τ = 2)
    {B : Subgroup (Equiv.Perm (Fin 276))}
    (hB : CFSG.Assembly.IsComponentOf B (co3P ⊓ centralizer ({τ} : Set _))) :
    (Nat.card (center B) = 2 ∧ Nat.card (B ⧸ center B) = 1451520) ∨
      (Nat.card (center B) = 1 ∧ Nat.card (B ⧸ center B) = 95040) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hcl, -, -⟩ := ctuc_co3_complete_inner_involution_classes
  have hrep : ∃ g ∈ co3P, ∃ r : Equiv.Perm (Fin 276), τ = g * r * g⁻¹ ∧
      ((co3P ⊓ centralizer ({r} : Set _) = co3M) ∨ (co3P ⊓ centralizer ({r} : Set _) = co3M1)) := by
    by_cases h : ∃ g ∈ co3P, τ = g * co3Z * g⁻¹
    · obtain ⟨g, hg, rfl⟩ := h
      exact ⟨g, hg, co3Z, rfl, Or.inl co3M_eq_centralizer.symm⟩
    · have h' : ∃ g ∈ co3P, τ = g * co3Tt * g⁻¹ := by
        by_contra h''
        exact h ((hcl τ hτP hτ).2 h'')
      obtain ⟨g, hg, rfl⟩ := h'
      exact ⟨g, hg, co3Tt, rfl, Or.inr co3M1_eq_centralizer.symm⟩
  obtain ⟨g, hg, r, rfl, hr⟩ := hrep
  have hfinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hgr : g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r := by group
  have hBr : CFSG.Assembly.IsComponentOf (B.map (MulAut.conj g⁻¹).toMonoidHom)
      (co3P ⊓ centralizer ({r} : Set _)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [Subgroup.map_inf _ _ _ hfinj, map_conj_self (co3P.inv_mem hg), map_conj_centralizer,
      Set.image_singleton, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgr] at h
  obtain ⟨hc1, hc2⟩ :=
    card_center_and_quotient_of_mulEquiv (B.equivMapOfInjective _ hfinj)
  rw [hc1, hc2]
  rcases hr with hM | hM1
  · rw [hM] at hBr
    have hBM : B.map (MulAut.conj g⁻¹).toMonoidHom = co3M :=
      isComponentOf_eq_of_isQuasisimple hBr co3M_isQuasisimple (p := 2)
        (IsPGroup.of_card (n := 1) (by rw [card_co3M_center, pow_one]))
    left
    rw [hBM]
    refine ⟨card_co3M_center, ?_⟩
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (center co3M)
    rw [card_co3M, card_co3M_center] at h
    omega
  · rw [hM1] at hBr
    right
    have hLn : co3M1 ≤ normalizer (co3L : Set (Equiv.Perm (Fin 276))) :=
      (normal_subgroupOf_iff_le_normalizer co3L_le_M1).1 co3L1_normal
    have hBL : B.map (MulAut.conj g⁻¹).toMonoidHom = co3L := by
      rcases isComponentOf_le_or_commute hBr co3L_le_M1 hLn with hle | hcomm
      · have : IsSimpleGroup co3L := by
          have := CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
          exact co3LEquivM12.isSimpleGroup
        have hnab : ∃ a b : co3L, a * b ≠ b * a := by
          refine ⟨co3LEquivM12.symm CFSG.Sporadic.Mathieu.m12a,
            co3LEquivM12.symm CFSG.Sporadic.Mathieu.m12b, fun h => m12_not_comm ?_⟩
          have := congrArg co3LEquivM12 h
          simpa only [map_mul, MulEquiv.apply_symm_apply] using this
        obtain ⟨hLq, hLZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
        exact isComponentOf_eq_of_isQuasisimple (isComponentOf_of_le hBr hle co3L_le_M1) hLq
          (p := 2) (by rw [hLZ]; exact IsPGroup.of_bot)
      · exfalso
        have hle : B.map (MulAut.conj g⁻¹).toMonoidHom ≤
            co3M1 ⊓ centralizer (co3L : Set (Equiv.Perm (Fin 276))) := by
          intro x hx
          refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
          rw [mem_centralizer_iff]
          intro y hy
          have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
          rw [mem_centralizer_iff] at this
          exact this y hy
        exact not_le_of_isPGroup hBr.2.2
          (isPGroup_two_of_card (k := 1) (by rw [card_co3M1_centralizer_L]; norm_num)) hle
    rw [hBL]
    refine ⟨by rw [co3L_center, Subgroup.card_bot], ?_⟩
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq co3L_center).trans
      QuotientGroup.quotientBot).toEquiv, card_co3L]

theorem co3_involution_component_card
    {T : Type*} [Group T]
    (hT : Nonempty (T ≃* NativeSporadic.Co3)) {t : T} (ht : orderOf t = 2)
    {B : Subgroup (centralizer ({t} : Set T))} (hB : CFSG.IsComponent B) :
    (Nat.card (center B) = 2 ∧ Nat.card (B ⧸ center B) = 1451520) ∨
      (Nat.card (center B) = 1 ∧ Nat.card (B ⧸ center B) = 95040) := by
  obtain ⟨e⟩ := hT
  set ι : T →* Equiv.Perm (Fin 276) := co3P.subtype.comp (e.trans co3PermEquiv).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (e.trans co3PermEquiv).injective
  have hrange : ι.range = co3P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (e.trans co3PermEquiv).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι t ∈ co3P := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  set B₀ : Subgroup T := B.map (centralizer ({t} : Set T)).subtype
  have hB₀ : CFSG.Assembly.IsComponentOf B₀ (centralizer ({t} : Set T)) :=
    (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le B)).2
      (by
        rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective
          (centralizer ({t} : Set T)).subtype_injective]
        exact hB)
  have hB' : CFSG.Assembly.IsComponentOf (B₀.map ι)
      (co3P ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 276)))) := by
    have := (isComponentOf_map_iff hι).2 hB₀
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  have eB : B ≃* B₀.map ι :=
    (B.equivMapOfInjective _ (centralizer ({t} : Set T)).subtype_injective).trans
      (B₀.equivMapOfInjective ι hι)
  obtain ⟨h1, h2⟩ := card_center_and_quotient_of_mulEquiv eB
  rw [h1, h2]
  exact co3P_component_card hτP hτ hB'

end CFSG.SeitzReduction.SporadicRefine
