module

public import CFSG.LargeExtraspecial.S14SMKNoA2
public import CFSG.LargeExtraspecial.SMod20AutPlanes
public import CFSG.LargeExtraspecial.SMod20CollMain
public import CFSG.LargeExtraspecial.SMod20UaShared
public import CFSG.LargeExtraspecial.S12InspSplit
public import CFSG.LargeExtraspecial.GLRMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20

structure Inputs10 : Prop where
  hRI : RootInvolutionComponentsInput.{0}
  hARS : CFSG.Timmesfeld.ARSInput
  hTri : FischerTrialityInput
  hFischer : S12FischerStatement
  hInsp : Insp5Input
  h36 : Timmesfeld36Input
  hSL : S12SL4ModuleInput
  hDW : DW.DW37Statement

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem noA2_of_insp5 [IsSimpleGroup G] (I : Inputs10) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ¬ S.HasTypeAInL g := by
  rintro ⟨α, hαL, -, hαA⟩
  have ht : S.ρ α ∈ S.Lbar g := by
    rw [← S.map_La_eq_Lbar g]
    exact ⟨α, mem_subgroupOf.mpr hαL, rfl⟩
  rcases Setting.timmesfeld_12_16_of_insp5 I.hRI I.hARS I.hTri I.hFischer I.hInsp I.h36 I.hSL
    haQ hne (by omega) ht hαA with hred | ⟨h4, -⟩ | hR | ⟨h4, -⟩
  · exact irreducible I.hDW hw hU haQ hne hred
  · omega
  · exact Setting.not_s12GammaLResidual haQ hne (by omega) hR
  · omega

theorem planePoints_eq_planeSet {i : ℕ} (hi : i < 891) : Aut.planePoints i = planeSet i := by
  have hm : maskArr[i]! = wMask i := by simp [maskArr, getElem!_pos, hi]
  ext p
  simp [Aut.planePoints, planeSet, inPlane, hm]

theorem UAloc_eq_UA {i : ℕ}
    (hi : i < 891) : Aut.UAloc i = UA i := by
  rw [Aut.UAloc, UA, wPlane_eq_planeSet hi, planePoints_eq_planeSet hi]

section Perm


@[expose] noncomputable def piM (S : Setting G) (ψ : Mbar0 S ≃* T46) :
    S.Mbar →* Equiv.Perm (Fin 693) :=
  autPerm.comp (mbarHom S ψ)

variable (ψ : Mbar0 S ≃* T46)

theorem piM_apply (m : S.Mbar) : piM S ψ m = autPerm (mbarHom S ψ m) := rfl

theorem piM_injective : Function.Injective (piM S ψ) :=
  autPerm_injective.comp (mbarHom_injective S ψ)

theorem piM_of_mem (m : Mbar0 S) : piM S ψ m = ψ m := autPerm_mbarHom_of_mem S ψ m

theorem piM_mem_normalizer (m : S.Mbar) :
    piM S ψ m ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693))) :=
  autPerm_mem_normalizer _

theorem isPolarAut_piM
    (m : S.Mbar) : IsPolarAut (piM S ψ m) :=
  isPolarAut_of_mem_normalizer (piM_mem_normalizer ψ m)

theorem exists_piM_eq {t : Equiv.Perm (Fin 693)} (ht : t ∈ T46) :
    ∃ m : Mbar0 S, piM S ψ m = t :=
  ⟨ψ.symm ⟨t, ht⟩, by rw [piM_of_mem, MulEquiv.apply_symm_apply]⟩


@[expose] noncomputable def planeHom (S : Setting G) (ψ : Mbar0 S ≃* T46) :
    S.Mbar →* Equiv.Perm (Fin 891) :=
  autPlane.comp (mbarHom S ψ)

theorem image_wPlane_piM (m : S.Mbar) (i : Fin 891) :
    ⇑(piM S ψ m) '' wPlane i = wPlane (planeHom S ψ m i) := by
  rw [wPlane_eq_planeSet i.2, wPlane_eq_planeSet (planeHom S ψ m i).2,
    ← planePoints_eq_planeSet i.2, ← planePoints_eq_planeSet (planeHom S ψ m i).2]
  have hspec := autPlane_spec (mbarHom S ψ m) i
  ext q
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hspec p).1 hp
  · intro hq
    refine ⟨(piM S ψ m)⁻¹ q, (hspec _).2 ?_, perm_apply_inv_self _ q⟩
    rw [← piM_apply, perm_apply_inv_self]
    exact hq

theorem planeHom_eq_iff (m : S.Mbar) (i j : Fin 891) :
    planeHom S ψ m i = j ↔ ⇑(piM S ψ m) '' wPlane i = wPlane j := by
  rw [image_wPlane_piM]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (wPlane_injective (planeHom S ψ m i).2 j.2 h)⟩

theorem exists_fixed_plane {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    ∃ i : Fin 891, ∀ m : S.Mbar, (m : S.O) ∈ S.Lbar g → planeHom S ψ m i = i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := S.isElementaryAbelian_Lbar haQ
  have : CFSG.IsElementaryAbelian 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    CFSG.IsElementaryAbelian.subgroupOf (S.Lbar_le_Mbar g)
  have hH : IsPGroup 2 (((S.Lbar g).subgroupOf S.Mbar).map (planeHom S ψ)) :=
    (CFSG.IsElementaryAbelian.isPGroup 2 _).map _
  obtain ⟨i, hi⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card (Fin 891)
    (by rw [Nat.card_fin]; decide)
  exact ⟨i, fun m hm => hi ⟨planeHom S ψ m, m, mem_subgroupOf.mpr hm, rfl⟩⟩

end Perm

section B4

variable
  (ψ : Mbar0 S ≃* T46)

theorem card_map_Lbar (g : G) :
    Nat.card (((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ)) = Nat.card (S.Lbar g) := by
  rw [card_map_of_injective (piM_injective ψ),
    Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv]

theorem Lbar_eq_UA (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ∃! i : Fin 891, ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val := by
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
      rw [← UAloc_eq_UA i.2]
      refine autPerm_mem_UAloc_of_commute i.2 (mbarHom S ψ m) fun u hu => ?_
      rw [UAloc_eq_UA i.2] at hu
      exact ((mem_centralizer_iff.mp hc) u hu).symm
    · rw [card_map_Lbar ψ g]
      exact card_Lbar_ge hw haQ hne
  exact ⟨i, hE, fun j hj => Fin.ext (UA_injective j.2 i.2 (hj.symm.trans hE))⟩

theorem Lbar_le_Mbar0 (ψ : Mbar0 S ≃* T46) (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : S.Lbar g ≤ (Mbar0 S).map S.Mbar.subtype := by
  intro s hs
  obtain ⟨i, hi, -⟩ := Lbar_eq_UA ψ hw haQ hne
  have h1 : piM S ψ ⟨s, S.Lbar_le_Mbar g hs⟩ ∈ UA i.val :=
    hi ▸ ⟨⟨s, S.Lbar_le_Mbar g hs⟩, mem_subgroupOf.mpr hs, rfl⟩
  obtain ⟨m₀, hm₀⟩ := exists_piM_eq ψ (UA_le_T46 h1)
  have h4 := piM_injective ψ hm₀
  exact ⟨m₀, m₀.2, by rw [Subgroup.coe_subtype, h4]⟩

@[expose] noncomputable def planeOf (S : Setting G) (ψ : Mbar0 S ≃* T46) (g : G) : Fin 891 :=
  Classical.epsilon fun i : Fin 891 => ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val

theorem planeOf_spec (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA (planeOf S ψ g).val :=
  Classical.epsilon_spec (Lbar_eq_UA ψ hw haQ hne).exists

theorem planeOf_eq_iff (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (i : Fin 891) :
    planeOf S ψ g = i ↔ ((S.Lbar g).subgroupOf S.Mbar).map (piM S ψ) = UA i.val := by
  rw [planeOf_spec ψ hw haQ hne]
  exact ⟨fun h => by rw [h], fun h => Fin.ext (UA_injective (planeOf S ψ g).2 i.2 h)⟩

theorem planeOf_congr {g h : G} (hL : S.Lbar g = S.Lbar h) : planeOf S ψ g = planeOf S ψ h := by
  simp only [planeOf, hL]

end B4

section Stab

theorem mem_normalizer_UA_iff
    {π : Equiv.Perm (Fin 693)} (hπ : IsPolarAut π) {i : ℕ}
    (hi : i < 891) :
    π ∈ normalizer (UA i : Set (Equiv.Perm (Fin 693))) ↔ ⇑π '' wPlane i = wPlane i := by
  constructor
  · intro hN
    have hsub : ⇑π '' wPlane i ⊆ wPlane i := by
      rintro _ ⟨p, hp, rfl⟩
      have hmem : tvP (π p) ∈ UA i := by
        rw [← hπ.mul_tvP_mul_inv p]
        exact (mem_normalizer_iff.1 hN _).1 (tvP_mem_UA hp)
      exact mem_wPlane_of_perp hi fun q hq =>
        perp_comm.1 (tvP_apply_eq_self_iff.1 (UA_apply_of_mem hi hmem hq))
    exact Set.eq_of_subset_of_ncard_le hsub
      (by rw [Set.ncard_image_of_injective _ π.injective]) (wPlane_finite i)
  · intro hW
    refine mem_normalizer_iff.2 fun h => ⟨conj_mem_UA hπ hW, fun hh => ?_⟩
    have := conj_mem_UA hπ.inv (image_wPlane_inv hW) hh
    rwa [show π⁻¹ * (π * h * π⁻¹) * π⁻¹⁻¹ = h by group] at this

theorem mem_normalizer_map_iff {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (H : Subgroup A) (a : A) :
    f a ∈ normalizer ((H.map f : Subgroup B) : Set B) ↔ a ∈ normalizer (H : Set A) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    rw [← mem_map_iff_mem hf, h (f x), ← map_inv, ← map_mul, ← map_mul, mem_map_iff_mem hf]
  · intro h y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨a * x * a⁻¹, (h x).1 hx, by simp⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨a⁻¹ * x * a, (h _).2 ?_, ?_⟩
      · rwa [show a * (a⁻¹ * x * a) * a⁻¹ = x by group]
      · rw [map_mul, map_mul, map_inv, hxy]
        group

theorem mem_normalizer_subgroupOf_iff {K : Subgroup S.O} (hK : K ≤ S.Mbar) (m : S.Mbar) :
    m ∈ normalizer ((K.subgroupOf S.Mbar : Subgroup S.Mbar) : Set S.Mbar) ↔
      (m : S.O) ∈ normalizer (K : Set S.O) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h s
    constructor
    · intro hs
      exact mem_subgroupOf.mp ((h ⟨s, hK hs⟩).1 (mem_subgroupOf.mpr hs))
    · intro hs
      have hsM : s ∈ S.Mbar := by
        have := S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.inv_mem m.2) (hK hs)) m.2
        rwa [show (m : S.O)⁻¹ * ((m : S.O) * s * (m : S.O)⁻¹) * (m : S.O) = s by group] at this
      exact mem_subgroupOf.mp ((h ⟨s, hsM⟩).2 (mem_subgroupOf.mpr hs))
  · intro h y
    rw [mem_subgroupOf, mem_subgroupOf]
    exact h y


theorem mem_cMbar_iff [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T46)
    (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (m : S.Mbar) :
    (m : S.O) ∈ cMbar S g ↔
      ⇑(piM S ψ m) '' wPlane (planeOf S ψ g) = wPlane (planeOf S ψ g) := by
  have hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6) := ⟨ψ.trans tpsuT46.symm⟩
  rw [cMbar_eq_normalizer_of_noA2 (by omega) haQ hne (noA2_of_insp5 I hw hU haQ hne), mem_inf,
    ← mem_normalizer_UA_iff (isPolarAut_piM ψ m) (planeOf S ψ g).2,
    ← planeOf_spec ψ hw haQ hne, mem_normalizer_map_iff (piM_injective ψ),
    mem_normalizer_subgroupOf_iff (S.Lbar_le_Mbar g)]
  exact ⟨fun h => h.2, fun h => ⟨m.2, h⟩⟩

theorem stab_eq [IsSimpleGroup G] (I : Inputs10) (ψ : Mbar0 S ≃* T46) (hw : S.width = 10)
    {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (m : Mbar0 S) :
    ((m : S.Mbar) : S.O) ∈ cMbar S g ↔
      ((ψ m : T46) : Equiv.Perm (Fin 693)) ∈ PA (planeOf S ψ g).val := by
  rw [mem_cMbar_iff I ψ hw haQ hne, piM_of_mem]
  exact ⟨fun h => Subgroup.mem_inf.2 ⟨(ψ m).2, mem_stabilizer_wPlane.2 h⟩,
    fun h => mem_stabilizer_wPlane.1 (Subgroup.mem_inf.1 h).2⟩

end Stab

end CFSG.LargeExtraspecial.S14.SMK
