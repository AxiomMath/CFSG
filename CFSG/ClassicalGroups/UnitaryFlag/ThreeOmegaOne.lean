module

public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.ClassicalGroups.UnitaryFlag.ThreeRootGroups
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts

variable {n : ℕ} {F : Type} [Field F] [Finite F]

private theorem omegaOneOf_map_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) {T : Subgroup X} (hT : IsPGroup 2 T) :
    (omegaOneOf T).map e.toMonoidHom = omegaOneOf (T.map e.toMonoidHom) := by
  apply omegaOneOf_map_of_odd_ker e.toMonoidHom _ hT
  rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective, Subgroup.card_bot]
  exact ⟨0, by norm_num⟩

private theorem omegaOneOf_map_sylowMap {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) (T : Sylow 2 X) :
    (omegaOneOf (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T : Sylow 2 Y) :
        Subgroup Y) = (omegaOneOf (T : Subgroup X)).map e.toMonoidHom := by
  rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective]
  exact (omegaOneOf_map_mulEquiv e T.isPGroup').symm

private theorem exists_sup_three_omegaOne_eq_top_unitarySU
    (h : UnitaryFieldData 2 n F) (hn : 2 ≤ n)
    (T T' : Sylow 2 ↥(unitarySU 2 n F 3)) (hTT' : T ≠ T') :
    ∃ T'' : Sylow 2 ↥(unitarySU 2 n F 3),
      omegaOneOf (T : Subgroup ↥(unitarySU 2 n F 3)) ⊔
        omegaOneOf (T' : Subgroup ↥(unitarySU 2 n F 3)) ⊔
        omegaOneOf (T'' : Subgroup ↥(unitarySU 2 n F 3)) = ⊤ := by
  obtain ⟨L, hL, hΩ⟩ := omegaOneOf_sylow_eq_isotropicTransvectionGroup (h := h) T
  obtain ⟨L', hL', hΩ'⟩ := omegaOneOf_sylow_eq_isotropicTransvectionGroup (h := h) T'
  have hLL' : L ≠ L' := by
    intro hEq
    apply hTT'
    apply eq_of_omegaOneOf_sylow_eq h
    rw [hΩ, hΩ', hEq]
  obtain ⟨L₃, hL₃, hspan⟩ := exists_isotropic_sup_eq_top (h := h) hL hL' hLL'
  obtain ⟨T'', hΩ''⟩ := exists_sylow_omegaOneOf_eq_isotropicTransvectionGroup (h := h) hL₃
  exact ⟨T'', by
    rw [hΩ, hΩ', hΩ'']
    exact sup_three_isotropicTransvectionGroup_eq_top h hn hL hL' hL₃ hspan⟩

private theorem exists_sup_three_omegaOne_eq_top_unitaryPSU
    (h : UnitaryFieldData 2 n F) (hn : 2 ≤ n)
    (T T' : Sylow 2 (unitaryPSU h 3)) (hTT' : T ≠ T') :
    ∃ T'' : Sylow 2 (unitaryPSU h 3),
      omegaOneOf (T : Subgroup (unitaryPSU h 3)) ⊔
        omegaOneOf (T' : Subgroup (unitaryPSU h 3)) ⊔
        omegaOneOf (T'' : Subgroup (unitaryPSU h 3)) = ⊤ := by
  have hbij := sylowMapUnitaryProj_bijective h
  obtain ⟨S, hS⟩ := hbij.2 T
  obtain ⟨S', hS'⟩ := hbij.2 T'
  have hSS' : S ≠ S' := by
    intro hEq
    apply hTT'
    rw [← hS, ← hS', hEq]
  obtain ⟨S'', hSU⟩ := exists_sup_three_omegaOne_eq_top_unitarySU h hn S S' hSS'
  refine ⟨sylowMapUnitaryProj h S'', ?_⟩
  have htop : (⊤ : Subgroup ↥(unitarySU 2 n F 3)).map (unitaryProj h 3) = ⊤ :=
    Subgroup.map_top_of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
  have hmap : ((omegaOneOf (S : Subgroup ↥(unitarySU 2 n F 3)) ⊔
      omegaOneOf (S' : Subgroup ↥(unitarySU 2 n F 3)) ⊔
      omegaOneOf (S'' : Subgroup ↥(unitarySU 2 n F 3))).map (unitaryProj h 3)) = ⊤ := by
    rw [hSU, htop]
  rw [Subgroup.map_sup, Subgroup.map_sup, omegaOneOf_map_sylowMapUnitaryProj h S,
    omegaOneOf_map_sylowMapUnitaryProj h S', omegaOneOf_map_sylowMapUnitaryProj h S''] at hmap
  rwa [hS, hS'] at hmap

private theorem exists_sup_three_omegaOne_eq_top_of_mulEquiv {X Y : Type*}
    [Group X] [Finite X] [Group Y] [Finite Y] (e : X ≃* Y)
    (hY : ∀ T T' : Sylow 2 Y, T ≠ T' →
      ∃ T'' : Sylow 2 Y, omegaOneOf (T : Subgroup Y) ⊔ omegaOneOf (T' : Subgroup Y) ⊔
        omegaOneOf (T'' : Subgroup Y) = ⊤)
    (T T' : Sylow 2 X) (hTT' : T ≠ T') :
    ∃ T'' : Sylow 2 X, omegaOneOf (T : Subgroup X) ⊔ omegaOneOf (T' : Subgroup X) ⊔
      omegaOneOf (T'' : Subgroup X) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : X →* Y := e.toMonoidHom
  let T₁ : Sylow 2 Y := Sylow.mapSurjective (f := f) e.surjective T
  let T₁' : Sylow 2 Y := Sylow.mapSurjective (f := f) e.surjective T'
  have hT₁T₁' : T₁ ≠ T₁' := by
    intro hEq
    apply hTT'
    apply Sylow.ext
    have hsub : (T : Subgroup X).map f = (T' : Subgroup X).map f := by
      have h' := congrArg (fun S : Sylow 2 Y => (S : Subgroup Y)) hEq
      simpa only [T₁, T₁', Sylow.coe_mapSurjective (f := f) e.surjective] using h'
    exact Subgroup.map_injective e.injective hsub
  obtain ⟨T₁'', hT₁''⟩ := hY T₁ T₁' hT₁T₁'
  obtain ⟨T'', hT''⟩ := (Sylow.mapSurjective_surjective (f := f) e.surjective) 2 T₁''
  refine ⟨T'', ?_⟩
  have hΩ : (omegaOneOf (T₁ : Subgroup Y)) = (omegaOneOf (T : Subgroup X)).map f := by
    simpa only [T₁] using omegaOneOf_map_sylowMap (e := e) T
  have hΩ' : (omegaOneOf (T₁' : Subgroup Y)) = (omegaOneOf (T' : Subgroup X)).map f := by
    simpa only [T₁'] using omegaOneOf_map_sylowMap (e := e) T'
  have hΩ'' : (omegaOneOf (T₁'' : Subgroup Y)) = (omegaOneOf (T'' : Subgroup X)).map f := by
    rw [← hT'']
    simpa only [f] using omegaOneOf_map_sylowMap (e := e) T''
  have htop : (⊤ : Subgroup X).map f = ⊤ := Subgroup.map_top_of_surjective f e.surjective
  have hmap : ((omegaOneOf (T : Subgroup X) ⊔ omegaOneOf (T' : Subgroup X) ⊔
      omegaOneOf (T'' : Subgroup X)).map f) = ⊤ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, ← hΩ, ← hΩ', ← hΩ'']
    exact hT₁''
  exact Subgroup.map_injective e.injective (hmap.trans htop.symm)

theorem exists_sup_three_omegaOne_eq_top {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] [Finite X]
    {F : Type} [Field F] [Finite F] (hFc : Nat.card F = (2 ^ n) ^ 2)
    (hX : Nonempty (X ≃* StatedSU 3 (2 ^ n) F) ∨
      Nonempty (X ≃* StatedProj (StatedSU 3 (2 ^ n) F)))
    (T T' : Sylow 2 X) (hTT' : T ≠ T') :
    ∃ T'' : Sylow 2 X, omegaOneOf (T : Subgroup X) ⊔ omegaOneOf (T' : Subgroup X) ⊔
      omegaOneOf (T'' : Subgroup X) = ⊤ := by
  let h : UnitaryFieldData 2 n F := unitaryFieldDataOfCard hFc
  rcases hX with ⟨⟨eSU⟩⟩ | ⟨⟨ePSU⟩⟩
  · haveI : Finite ↥(unitarySU 2 n F 3) := model3U4_finite_group h
    let e : X ≃* ↥(unitarySU 2 n F 3) := eSU
    exact exists_sup_three_omegaOne_eq_top_of_mulEquiv e
      (fun T T' hne => exists_sup_three_omegaOne_eq_top_unitarySU h hn T T' hne) T T' hTT'
  · haveI : Finite ↥(unitarySU 2 n F 3) := model3U4_finite_group h
    haveI : Finite (unitaryPSU h 3) :=
      Finite.of_surjective (unitaryProj h 3) (unitaryProj_surjective h 3)
    let e : X ≃* unitaryPSU h 3 := ePSU.trans (unitaryPSUEquivStated hFc).symm
    exact exists_sup_three_omegaOne_eq_top_of_mulEquiv e
      (fun T T' hne => exists_sup_three_omegaOne_eq_top_unitaryPSU h hn T T' hne) T T' hTT'

end CFSG.ClassicalGroups.UnitaryFlag

end
