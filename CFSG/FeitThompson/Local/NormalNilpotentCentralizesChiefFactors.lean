module

public import CFSG.FeitThompson.Local.ChiefFactorCentralizationCentralSeries
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.NilpotentHomImageNilpotent
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

theorem commutator_le_of_isChiefFactor_of_isSolvable [Finite G] {L X Y : Subgroup G}
    (hL : L.Normal) (hnil : Group.IsNilpotent L) (h : IsChiefFactor X Y)
    [Group.IsSolvable X] : ⁅L, X⁆ ≤ Y := by
  have := h.normal_num
  have := h.normal_den
  have := hL
  have := hnil
  have hsurj : Function.Surjective (mk' Y) := mk'_surjective Y
  have hMnormal : (X.map (mk' Y)).Normal := h.normal_num.map _ hsurj
  have : Group.IsSolvable (X.map (mk' Y)) := isSolvable_map (mk' Y) X
  have hMne : X.map (mk' Y) ≠ ⊥ := by
    obtain ⟨x, hxX, hxY⟩ := SetLike.exists_of_lt h.lt
    intro hbot
    have hmem : (mk' Y) x ∈ X.map (mk' Y) := ⟨x, hxX, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hxY ((QuotientGroup.eq_one_iff x).1 hmem)
  have hcomapM : (X.map (mk' Y)).comap (mk' Y) = X := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left]
    exact h.le
  have hmin : ∀ K : Subgroup (G ⧸ Y), K.Normal → K < X.map (mk' Y) → K = ⊥ := by
    intro K hK hKM
    have := hK
    have hZnormal : (K.comap (mk' Y)).Normal := inferInstance
    have hYle : Y ≤ K.comap (mk' Y) := by
      intro y hy
      have h1 : (mk' Y) y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      simp [Subgroup.mem_comap, h1]
    have hZX : K.comap (mk' Y) ≤ X := hcomapM ▸ Subgroup.comap_mono hKM.le
    have hK' : Subgroup.map (mk' Y) (K.comap (mk' Y)) = K :=
      Subgroup.map_comap_eq_self_of_surjective hsurj K
    rcases h.eq_or_eq hZnormal hYle hZX with hZ | hZ
    · rw [hZ, QuotientGroup.map_mk'_self] at hK'
      exact hK'.symm
    · rw [hZ] at hK'
      exact absurd hK'.symm hKM.ne
  have hMcent : X.map (mk' Y) ≤ centralizer (fittingRaw (G ⧸ Y) : Set (G ⧸ Y)) :=
    le_centralizer_fittingRaw hMne hmin
  have hLfit : L.map (mk' Y) ≤ fittingRaw (G ⧸ Y) :=
    le_fittingRaw_of_normal_of_isNilpotent (hL.map _ hsurj) (isNilpotent_map (mk' Y) L)
  have hcomm : ⁅L.map (mk' Y), X.map (mk' Y)⁆ = ⊥ := by
    rw [commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hMcent.trans (Subgroup.centralizer_le (by exact_mod_cast hLfit))
  have hmapbot : (⁅L, X⁆).map (mk' Y) = ⊥ := by rw [Subgroup.map_commutator]; exact hcomm
  have hfinal := (Subgroup.map_eq_bot_iff _).1 hmapbot
  rwa [QuotientGroup.ker_mk'] at hfinal

theorem commutator_le_of_isChiefFactor [Finite G] [Group.IsSolvable G] {L X Y : Subgroup G}
    (hL : L.Normal) (hnil : Group.IsNilpotent L) (h : IsChiefFactor X Y) : ⁅L, X⁆ ≤ Y :=
  commutator_le_of_isChiefFactor_of_isSolvable hL hnil h

theorem inv_mul_inv_mul_mul_mem_of_isChiefFactor [Finite G] [Group.IsSolvable G]
    {L X Y : Subgroup G} (hL : L.Normal) (hnil : Group.IsNilpotent L) (h : IsChiefFactor X Y)
    {a x : G} (ha : a ∈ L) (hx : x ∈ X) : a⁻¹ * x⁻¹ * a * x ∈ Y := by
  have hmem := Subgroup.commutator_mem_commutator (L.inv_mem ha) (X.inv_mem hx)
  rw [commutatorElement_def, inv_inv, inv_inv] at hmem
  exact commutator_le_of_isChiefFactor hL hnil h hmem

theorem isNilpotent_iff_forall_isChiefFactor [Finite G] [Group.IsSolvable G] (H : Subgroup G)
    [H.Normal] :
    Group.IsNilpotent H ↔ ∀ X Y : Subgroup G, IsChiefFactor X Y → X ≤ H → ⁅H, X⁆ ≤ Y :=
  ⟨fun hnil _ _ hXY _ => commutator_le_of_isChiefFactor ‹H.Normal› hnil hXY,
    isNilpotent_of_forall_isChiefFactor H⟩

end

end CFSG.FeitThompson
