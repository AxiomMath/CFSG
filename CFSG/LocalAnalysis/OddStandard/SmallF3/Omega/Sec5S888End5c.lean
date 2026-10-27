module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End5b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End5c1

public section

open CFSG.Open CFSG.Goldschmidt Subgroup CFSG.GH74.GLS.Th2.P412

namespace CFSG.OddStandard.SmallF3.Omega

private lemma map_three_eq {Y : Type} [Group Y] {τ : Y ≃* Y}
    (hcube : ∀ y, τ (τ (τ y)) = y) (J : Subgroup Y) :
    ((J.map τ.toMonoidHom).map τ.toMonoidHom).map τ.toMonoidHom = J := by
  have hcomp : (τ.toMonoidHom.comp τ.toMonoidHom).comp τ.toMonoidHom = MonoidHom.id Y := by
    ext y
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
    exact hcube y
  rw [Subgroup.map_map, Subgroup.map_map, hcomp, Subgroup.map_id]

private lemma orbit_independent {Y : Type} [Group Y] [Finite Y] {τ : Y ≃* Y}
    (hcube : ∀ y, τ (τ (τ y)) = y) {J : Subgroup Y} (hJ : IsComponentOf J ⊤)
    (hne : J.map τ.toMonoidHom ≠ J)
    (hZ : Subgroup.center Y = ⊥) (hlayer : goldschmidtLayer Y = ⊤) :
    ∀ x ∈ J, ∀ y ∈ J.map τ.toMonoidHom,
      ∀ w ∈ (J.map τ.toMonoidHom).map τ.toMonoidHom,
        x * y * w = 1 → x = 1 ∧ y = 1 ∧ w = 1 := by
  have hJ' : IsComponentOf (J.map τ.toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff τ J).mpr hJ
  have hJ'' : IsComponentOf ((J.map τ.toMonoidHom).map τ.toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff τ (J.map τ.toMonoidHom)).mpr hJ'
  have hmap3 : ((J.map τ.toMonoidHom).map τ.toMonoidHom).map τ.toMonoidHom = J :=
    map_three_eq hcube J
  have hne'' : (J.map τ.toMonoidHom).map τ.toMonoidHom ≠ J.map τ.toMonoidHom := by
    intro heq
    have h2 : ((J.map τ.toMonoidHom).map τ.toMonoidHom).map τ.toMonoidHom
        = (J.map τ.toMonoidHom).map τ.toMonoidHom :=
      congrArg (fun X => X.map τ.toMonoidHom) heq
    rw [hmap3] at h2
    exact hne (h2.trans heq).symm
  have hneJ : (J.map τ.toMonoidHom).map τ.toMonoidHom ≠ J := by
    intro heq
    have h2 : ((J.map τ.toMonoidHom).map τ.toMonoidHom).map τ.toMonoidHom
        = J.map τ.toMonoidHom :=
      congrArg (fun X => X.map τ.toMonoidHom) heq
    rw [hmap3] at h2
    exact hne h2.symm
  have hZJ' : Subgroup.center ↥(J.map τ.toMonoidHom) = ⊥ :=
    GoldY.component_center_eq_bot hZ hlayer hJ'
  have hJ'cent : J.map τ.toMonoidHom ≤ Subgroup.centralizer (J : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne
        (J.map τ.toMonoidHom) J hJ' hJ hne)
  have hJ''cent : (J.map τ.toMonoidHom).map τ.toMonoidHom ≤
      Subgroup.centralizer (J : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne
        ((J.map τ.toMonoidHom).map τ.toMonoidHom) J hJ'' hJ hneJ)
  have hinf'' : J.map τ.toMonoidHom ⊓ (J.map τ.toMonoidHom).map τ.toMonoidHom = ⊥ :=
    GoldY.inf_component_eq_bot (Ne.symm hne'') hJ' hJ'' hZJ'
  intro x hx y hy w hw h
  have hxcentY : x ∈ Subgroup.centralizer (J : Set Y) := by
    have hxyw : x * (y * w) = 1 := by rwa [mul_assoc] at h
    have hxeq : x = (y * w)⁻¹ := eq_inv_of_mul_eq_one_left hxyw
    rw [hxeq]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (hJ'cent hy) (hJ''cent hw))
  have hxcenter : (⟨x, hx⟩ : J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxcentY g g.2)
  have hx1 : x = 1 := by
    have hmem : (⟨x, hx⟩ : J) ∈ (⊥ : Subgroup J) := by
      rw [← GoldY.component_center_eq_bot hZ hlayer hJ]
      exact hxcenter
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  have hyw : y * w = 1 := by
    rw [hx1, one_mul] at h
    exact h
  have hy1 : y = 1 := by
    have hybot : y ∈ J.map τ.toMonoidHom ⊓ (J.map τ.toMonoidHom).map τ.toMonoidHom := by
      refine ⟨hy, ?_⟩
      have hyeq : y = w⁻¹ := eq_inv_of_mul_eq_one_left hyw
      rw [hyeq]
      exact Subgroup.inv_mem _ hw
    rw [hinf''] at hybot
    exact Subgroup.mem_bot.mp hybot
  refine ⟨hx1, hy1, ?_⟩
  rw [hy1, one_mul] at hyw
  exact hyw

theorem tau_map_component_eq (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    (hY : IsGoldSemisimple Y) (D : Sylow 2 Y) {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y}
    (hP : IsPlanes (D : Subgroup Y) W) (hτ : IsPlaneAuts (D : Subgroup Y) W τ) (i : Fin 4)
    {J : Subgroup Y} (hJ : IsComponentOf J ⊤) : J.map (τ i).toMonoidHom = J := by
  classical
  by_contra hne
  have hZY := GoldY.center_eq_bot hY.o2 hY.odd hY.layer
  have hind := orbit_independent (hτ.cube i) hJ hne hZY hY.layer
  have hle := card_inf_le_two_of_orbit (Y := Y) (D := (D : Subgroup Y)) (W := W i)
    (τ := τ i) hP.comm (hP.le i) (hP.card i) (hτ.cube i) (hτ.mem_D i)
    (comm_mem_plane hP hτ i) hind
  have h4 := four_le_card_inf_component hN11b hY D hP.comm hJ
  omega

theorem plane_le_component (hN11b : S_N11b) {Y : Type} [Group Y] [Finite Y]
    (hY : IsGoldSemisimple Y) (D : Sylow 2 Y) {W : Fin 4 → Subgroup Y} {τ : Fin 4 → Y ≃* Y}
    (hP : IsPlanes (D : Subgroup Y) W) (hτ : IsPlaneAuts (D : Subgroup Y) W τ)
    {J : Subgroup Y} (hJ : IsComponentOf J ⊤) :
    1 ≤ Nat.card {i : Fin 4 // W i ≤ J} ∧
      Nat.card ↥((D : Subgroup Y) ⊓ J) = 4 ^ Nat.card {i : Fin 4 // W i ≤ J} := by
  classical
  set E : Subgroup Y := (D : Subgroup Y) ⊓ J with hEdef
  have hED : E ≤ (D : Subgroup Y) := by rw [hEdef]; exact inf_le_left
  have hEinv : ∀ i, ∀ e ∈ E, τ i e ∈ E := by
    intro i e he
    rw [hEdef] at he ⊢
    refine ⟨hτ.mem_D i e he.1, ?_⟩
    have hJfix := tau_map_component_eq hN11b hY D hP hτ i hJ
    have hmem : τ i e ∈ J.map (τ i).toMonoidHom :=
      Subgroup.mem_map_of_mem (τ i).toMonoidHom he.2
    rwa [hJfix] at hmem
  have hcardE : Nat.card E = 4 ^ Nat.card {i : Fin 4 // W i ≤ E} :=
    card_of_invariant hP hτ hED hEinv
  have hiff : ∀ i : Fin 4, W i ≤ J ↔ W i ≤ E := by
    intro i
    rw [hEdef]
    constructor
    · exact fun h => le_inf (hP.le i) h
    · exact fun h => le_trans h inf_le_right
  have hcardI : Nat.card {i : Fin 4 // W i ≤ J} = Nat.card {i : Fin 4 // W i ≤ E} :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  have h4 : 4 ≤ Nat.card E := by
    rw [hEdef]
    exact four_le_card_inf_component hN11b hY D hP.comm hJ
  have hm : Nat.card {i : Fin 4 // W i ≤ E} ≠ 0 := by
    intro h0
    have hcontra : Nat.card E = 1 := by rw [hcardE, h0, pow_zero]
    omega
  refine ⟨?_, ?_⟩
  · rw [hcardI]
    exact Nat.one_le_iff_ne_zero.mpr hm
  · rw [hcardI]
    exact hcardE

end CFSG.OddStandard.SmallF3.Omega
