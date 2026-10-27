module

public import CFSG.GF2Type.SmithTypeE.L6.IdNoA2
public import CFSG.GF2Type.SmithTypeE.L6.IdAutCent
public import CFSG.GF2Type.SmithTypeE.LMod.AutMbar
public import CFSG.GF2Type.SmithTypeE.LMod.AutPlanes
public import CFSG.GF2Type.SmithTypeE.LMod.UaCollMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 cMbar cMbar_eq_normalizer_of_noA2 card_Lbar_ge
  mem_normalizer_map_iff mem_normalizer_subgroupOf_iff)
open CFSG.GF2Type.SmithTypeE.LMod
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Perm


@[expose] noncomputable def piM (S : Setting G) (ψ : Mbar0 S ≃* T6) :
    S.Mbar →* Equiv.Perm (Fin 1953) :=
  autPerm.comp (mbarHom S ψ)

variable (ψ : Mbar0 S ≃* T6)

theorem piM_apply (m : S.Mbar) : piM S ψ m = autPerm (mbarHom S ψ m) := rfl

theorem piM_injective : Function.Injective (piM S ψ) :=
  autPerm_injective.comp (mbarHom_injective S ψ)

theorem piM_of_mem (m : Mbar0 S) : piM S ψ m = ψ m := autPerm_mbarHom_of_mem S ψ m

theorem piM_mem_normalizer (m : S.Mbar) :
    piM S ψ m ∈ normalizer (T6 : Set (Equiv.Perm (Fin 1953))) :=
  autPerm_mem_normalizer _

theorem isTvAut_piM (m : S.Mbar) : IsTvAut (piM S ψ m) := isTvAut_autPerm _

theorem exists_piM_eq {t : Equiv.Perm (Fin 1953)} (ht : t ∈ T6) :
    ∃ m : Mbar0 S, piM S ψ m = t :=
  ⟨ψ.symm ⟨t, ht⟩, by rw [piM_of_mem, MulEquiv.apply_symm_apply]⟩

@[expose] noncomputable def planeHom (S : Setting G) (ψ : Mbar0 S ≃* T6) :
    S.Mbar →* Equiv.Perm (Fin 1395) :=
  autPlane.comp (mbarHom S ψ)

theorem image_wPlane_piM (m : S.Mbar) (i : Fin 1395) :
    ⇑(piM S ψ m) '' wPlane i = wPlane (planeHom S ψ m i) := by
  have hspec := autPlane_spec (mbarHom S ψ m) i
  ext q
  simp only [Set.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hspec p).1 hp
  · intro hq
    have hinv : (piM S ψ m) ((piM S ψ m)⁻¹ q) = q := by simp
    refine ⟨(piM S ψ m)⁻¹ q, (hspec _).2 ?_, hinv⟩
    rw [← piM_apply, hinv]
    exact hq

theorem planeHom_eq_iff (m : S.Mbar) (i j : Fin 1395) :
    planeHom S ψ m i = j ↔ ⇑(piM S ψ m) '' wPlane i = wPlane j := by
  rw [image_wPlane_piM]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (wPlane_injective (planeHom S ψ m i).2 j.2 h)⟩

theorem exists_fixed_plane {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∃ i : Fin 1395, ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g → planeHom S ψ m i = i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.isElementaryAbelian_Lbar haQ
  have : CFSG.IsElementaryAbelian 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    CFSG.IsElementaryAbelian.subgroupOf (S.Lbar_le_Mbar g)
  have hH : IsPGroup 2 (((S.Lbar g).subgroupOf S.Mbar).map (planeHom S ψ)) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 _).map _
  obtain ⟨i, hi⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Fin 1395)
    (by rw [Nat.card_fin]; decide)
  exact ⟨i, fun m hm => hi ⟨planeHom S ψ m, m, mem_subgroupOf.mpr hm, rfl⟩⟩

end Perm

section B4

variable
  (ψ : Mbar0 S ≃* T6)

theorem card_map_Lbar (g : G) :
    Nat.card (((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ)) = Nat.card (S.Lbar g) := by
  rw [card_map_of_injective (piM_injective ψ),
    Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv]

theorem Lbar_eq_UA (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃! i : Fin 1395, ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hfix⟩ := exists_fixed_plane ψ haQ
  have := S.isElementaryAbelian_Lbar haQ
  have : CFSG.IsElementaryAbelian 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    CFSG.IsElementaryAbelian.subgroupOf (S.Lbar_le_Mbar g)
  have : CFSG.IsElementaryAbelian 2 (((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ)) :=
    CFSG.IsElementaryAbelian.map _
  have hE : ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val := by
    refine elemAb_eq_UA i.2 ?_ ?_ ?_ ?_
    · rintro _ ⟨m, -, rfl⟩
      exact piM_mem_normalizer ψ m
    · rintro _ ⟨m, hm, rfl⟩
      rw [mem_stabilizer_wPlane, image_wPlane_piM, hfix m (mem_subgroupOf.mp hm)]
    · rintro _ ⟨⟨m, -, rfl⟩, hc⟩
      exact autPerm_mem_UA_of_commute i.2 (mbarHom S ψ m) fun u hu =>
        (mem_centralizer_iff.mp hc) u hu
    · rw [card_map_Lbar ψ g]
      exact card_Lbar_ge hw haQ hne
  exact ⟨i, hE, fun j hj => Fin.ext (UA_injective j.2 i.2 (hj.symm.trans hE))⟩

theorem Lbar_le_Mbar0 (ψ : Mbar0 S ≃* T6) (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : S.Lbar g ≤ (Mbar0 S).map S.Mbar.subtype := by
  intro s hs
  obtain ⟨i, hi, -⟩ := Lbar_eq_UA ψ hw haQ hne
  have h1 : piM S ψ ⟨s, S.Lbar_le_Mbar g hs⟩ ∈ UA i.val :=
    hi ▸ ⟨⟨s, S.Lbar_le_Mbar g hs⟩, mem_subgroupOf.mpr hs, rfl⟩
  obtain ⟨m₀, hm₀⟩ := exists_piM_eq ψ (UA_le_T6 h1)
  have h4 := piM_injective ψ hm₀
  exact ⟨m₀, m₀.2, by rw [Subgroup.coe_subtype, h4]⟩

@[expose] noncomputable def planeOf (S : Setting G) (ψ : Mbar0 S ≃* T6) (g : G) : Fin 1395 :=
  Classical.epsilon fun i : Fin 1395 => ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val

theorem planeOf_spec (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA (planeOf S ψ g).val :=
  Classical.epsilon_spec (Lbar_eq_UA ψ hw haQ hne).exists

theorem planeOf_eq_iff (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (i : Fin 1395) :
    planeOf S ψ g = i ↔ ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val := by
  rw [planeOf_spec ψ hw haQ hne]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (UA_injective (planeOf S ψ g).2 i.2 h)⟩

theorem planeOf_congr {g h : G} (hL : S.Lbar g = S.Lbar h) : planeOf S ψ g = planeOf S ψ h := by
  simp only [planeOf, hL]

end B4

section Stab


theorem tvP_apply_eq_self_iff {p q : Fin 1953} : tvP p q = q ↔ Commute (tvP p) (tvP q) := by
  refine ⟨commute_tvP_of_fix, fun h => ?_⟩
  have e := mul_tvP_mul_inv (tvP_mem p) q
  rw [h.eq, mul_inv_cancel_right] at e
  exact tvP_injective e.symm

theorem mem_wPlane_of_comm {i : ℕ} (hi : i < 1395) {q : Fin 1953}
    (h : ∀ p ∈ wPlane i, tvP p q = q) : q ∈ wPlane i := by
  obtain ⟨x, hx, hW⟩ := exists_image_wPlane_zero hi
  have hq : x⁻¹ q ∈ wPlane 0 := by
    refine mem_wPlane_zero_of_comm fun p hp => ?_
    have hxp : x p ∈ wPlane i := by
      rw [← hW]
      exact Set.mem_image_of_mem _ hp
    have h1 := h _ hxp
    have h2 := isTvAut_of_mem hx p
    rw [← h2, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h1
    have h3 : tvP p (x⁻¹ q) = x⁻¹ q := by
      apply x.injective
      rw [h1]
      simp
    exact h3
  have hxq : q = x (x⁻¹ q) := by simp
  rw [hxq, ← hW]
  exact Set.mem_image_of_mem _ hq

theorem mem_normalizer_UA_iff {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) {i : ℕ}
    (hi : i < 1395) :
    π ∈ normalizer (UA i : Set (Equiv.Perm (Fin 1953))) ↔ ⇑π '' wPlane i = wPlane i := by
  constructor
  · intro hN
    have hsub : ⇑π '' wPlane i ⊆ wPlane i := by
      rintro _ ⟨p, hp, rfl⟩
      have hmem : tvP (π p) ∈ UA i := by
        rw [← hπ p]
        exact (mem_normalizer_iff.1 hN _).1 (tvP_mem_UA hp)
      refine mem_wPlane_of_comm hi fun q hq => ?_
      exact tvP_apply_eq_self_iff.2
        (tvP_apply_eq_self_iff.1 (UA_apply_of_mem hi hmem hq)).symm
    exact Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_image_of_injective _ π.injective]) (wPlane_finite i)
  · intro hW
    refine mem_normalizer_iff.2 fun h => ⟨conj_mem_UA hπ hW, fun hh => ?_⟩
    have := conj_mem_UA hπ.inv (image_wPlane_inv hW) hh
    rwa [show π⁻¹ * (π * h * π⁻¹) * π⁻¹⁻¹ = h by group] at this


theorem mem_cMbar_iff [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T6)
    (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (m : S.Mbar) :
    (m : S.O) ∈ cMbar S g ↔
      ⇑(piM S ψ m) '' wPlane (planeOf S ψ g) = wPlane (planeOf S ψ g) := by
  have hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2)) := ⟨ψ.trans pslT6.symm⟩
  rw [cMbar_eq_normalizer_of_noA2 (by omega) haQ hne (noA2_of_insp5 I hw hU haQ hne), mem_inf,
    ← mem_normalizer_UA_iff (isTvAut_piM ψ m) (planeOf S ψ g).2,
    ← planeOf_spec ψ hw haQ hne, mem_normalizer_map_iff (piM_injective ψ),
    mem_normalizer_subgroupOf_iff (S.Lbar_le_Mbar g)]
  exact ⟨fun h => h.2, fun h => ⟨m.2, h⟩⟩

theorem stab_eq [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T6) (hw : S.width = 10)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : Mbar0 S) :
    ((m : S.Mbar) : S.O) ∈ cMbar S g ↔
      ((ψ m : T6) : Equiv.Perm (Fin 1953)) ∈ PA (planeOf S ψ g).val := by
  rw [mem_cMbar_iff I ψ hw haQ hne, piM_of_mem]
  exact ⟨fun h => Subgroup.mem_inf.2 ⟨(ψ m).2, mem_stabilizer_wPlane.2 h⟩,
    fun h => mem_stabilizer_wPlane.1 (Subgroup.mem_inf.1 h).2⟩

end Stab

end CFSG.GF2Type.SmithTypeE.L6
