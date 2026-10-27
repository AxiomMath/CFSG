module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8D8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5G8Card
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Main

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}

theorem sec5g8_dihedral (hy : Sec5B59Hyp) (h4 : Asc82FactReflCentQ6)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b)
    (hTE : sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)) ≠ sec5p510_E t a b)
    {X : Type} [Group X] (π : ↥(centralizer ({z} : Set G)) →* X)
    (hker : π.ker = (zpowers z).subgroupOf (centralizer ({z} : Set G))) :
    Nonempty (↥(((sec5p510_T t z (sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂))).subgroupOf
      (centralizer ({z} : Set G))).map π) ≃* DihedralGroup 4) := by
  let H := centralizer ({z} : Set G)
  let R := sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)
  let E := sec5p510_E t a b
  have hTR : sec5p510_T t z R = R := hs.T_cases.resolve_left hTE
  rcases hs.R_cases with hRE | ⟨hR16, hrel⟩
  · exact absurd (hTR.trans hRE) hTE
  have hz2 : orderOf z = 2 := h.pocket.1
  have hSH : S ≤ H := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.central s hs')
  have hRS : R ≤ S := inf_le_left
  have hRH : R ≤ H := hRS.trans hSH
  have hER : E ≤ R := sec5p510_E_le_R hy h4 h hs.pk.q hs.ab
  have hEH : E ≤ H := hER.trans hRH
  have hzE : z ∈ E := sec5p510_z_mem_E h hs.ab
  have hzR : z ∈ R := hER hzE
  change Nonempty (↥(((sec5p510_T t z R).subgroupOf H).map π) ≃* DihedralGroup 4)
  rw [hTR]
  let Tb := (R.subgroupOf H).map π
  let Eb := (E.subgroupOf H).map π
  have hcardTb : Nat.card ↥Tb * 2 = 16 := by
    have h1 := sec5g8_card_map hz2 π hker hRH hzR
    rw [hR16] at h1
    exact h1
  have hTb8 : Nat.card ↥Tb = 8 := by omega
  haveI : Finite ↥Tb := Nat.finite_of_card_ne_zero (by rw [hTb8]; norm_num)
  have hEb_le_Tb : Eb ≤ Tb :=
    Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono H hER)
  have hEb4 : Nat.card ↥Eb = 4 := by
    have h1 := sec5g8_card_map hz2 π hker hEH hzE
    have h2 : Nat.card ↥E = 8 := sec5p510_card_E h hs.ab
    rw [h2] at h1
    have h3 : Nat.card ↥Eb * 2 = 8 := h1
    omega
  refine sec5g8_nonempty_dihedral_of_card_eight (D := ↥Tb) ?_
    (V := Eb.subgroupOf Tb) ?_ ?_ ?_
  · exact hTb8
  · have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEb_le_Tb).toEquiv
    omega
  · intro v hv
    have hvE : (v : X) ∈ Eb := Subgroup.mem_subgroupOf.mp hv
    obtain ⟨e, he, hfe⟩ := Subgroup.mem_map.mp hvE
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have hee : e * e = 1 := by
      apply Subtype.ext
      exact sec5p510_A_sq h (sec5p510_E_le_A h hs.ab heE)
    have hvv : (v : X) * (v : X) = 1 := by
      rw [← hfe, ← map_mul, hee, map_one]
    exact Subtype.ext hvv
  · have hnle : ¬ R ≤ E := fun hle => by
      have h1 := Subgroup.relIndex_eq_one.mpr hle
      rw [hrel] at h1
      omega
    obtain ⟨d, hdR, hdE⟩ := SetLike.not_le_iff_exists.mp hnle
    have haE : a ∈ E := (sec5p510_E_gens t a b).2.1
    have hbE : b ∈ E := (sec5p510_E_gens t a b).2.2
    have haR : a ∈ R := hER haE
    have hbR : b ∈ R := hER hbE
    have hdH : d ∈ H := hRH hdR
    have haH : a ∈ H := hRH haR
    have hbH : b ∈ H := hRH hbR
    refine ⟨⟨π ⟨d, hdH⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hdR)⟩,
      ⟨π ⟨a, haH⟩, Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr haR)⟩, ?_⟩
    rintro hxy
    have hcomm : π ⟨d, hdH⟩ * π ⟨a, haH⟩ = π ⟨a, haH⟩ * π ⟨d, hdH⟩ := by
      have h1 := congrArg Subtype.val hxy
      simpa using h1
    have hb_eq : π ⟨b, hbH⟩ = π ⟨a, haH⟩ := by
      have hsw : (⟨d, hdH⟩ : ↥H) * ⟨a, haH⟩ * ⟨d, hdH⟩⁻¹ = ⟨b, hbH⟩ := by
        apply Subtype.ext
        change d * a * d⁻¹ = b
        exact (hs.swap hrel d hdR hdE).1
      calc π ⟨b, hbH⟩ = π (⟨d, hdH⟩ * ⟨a, haH⟩ * ⟨d, hdH⟩⁻¹) := by rw [hsw]
        _ = π ⟨d, hdH⟩ * π ⟨a, haH⟩ * (π ⟨d, hdH⟩)⁻¹ := by
              rw [map_mul, map_mul, map_inv]
        _ = π ⟨a, haH⟩ := by rw [hcomm]; group
    have hker_mem : (⟨a, haH⟩ : ↥H)⁻¹ * ⟨b, hbH⟩ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hb_eq, inv_mul_cancel]
    rw [hker] at hker_mem
    have hab_z : a⁻¹ * b ∈ zpowers z := by
      have h1 := Subgroup.mem_subgroupOf.mp hker_mem
      simpa using h1
    have ha2 : a * a = 1 := sec5p510_A_sq h (sec5p510_E_le_A h hs.ab haE)
    have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hab_z' : a * b ∈ zpowers z := by simpa [ha_inv] using hab_z
    rw [hs.ab.ab_eq h] at hab_z'
    have ht_z : t ∈ zpowers z := by
      have h1 : (t * z) * z⁻¹ ∈ zpowers z :=
        mul_mem hab_z' (inv_mem (Subgroup.mem_zpowers z))
      simpa using h1
    exact sec5p510_t_not_mem_zpowers h ht_z

end CFSG.OddStandard.SmallF3.Omega
