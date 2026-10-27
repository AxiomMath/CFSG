module

public import CFSG.Holt.H78.Sec4FinalC3

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section WPrime

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem U_le_centralizer (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    D.U ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
  fun _ hu => C.centralizer_Y_le hS (D.Mc_le (D.U_le hu))

theorem mul_self_mem_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) {u : G} (hu : u ∈ D.U) :
    u * u ∈ D.V := by
  have hM := C.isNaturalSE_Dv C.i
  have huC := C.U_le_centralizer hS D hu
  have huu := mul_mem hu hu
  have h1 : C.piM hS ⟨u * u, C.U_le_centralizer hS D huu⟩ ∈
      rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) := by
    rw [show (⟨u * u, C.U_le_centralizer hS D huu⟩ : Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, huC⟩ * ⟨u, huC⟩ from rfl, map_mul]
    exact hM.mul_self_mem_rootCenter_seRadical (D.piM_U_mem u hu)
  refine (D.mem_V_iff _ huu).mpr (D.piM_eq_one _ (mul_mem huu huu) ?_)
  rw [show (⟨u * u * (u * u), C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem huu huu)))⟩ :
    Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
      ⟨u * u, C.U_le_centralizer hS D huu⟩ * ⟨u * u, C.U_le_centralizer hS D huu⟩ from rfl,
    map_mul]
  exact hM.mul_self_eq_one_of_mem_rootCenter h1

theorem exists_mem_V_piM_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) {m : Equiv.Perm _}
    (hm : m ∈ rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i))) :
    ∃ u, ∃ hu : u ∈ D.V, C.piM hS ⟨u, C.U_le_centralizer hS D (D.V_le hu)⟩ = m := by
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨u, hu, hum⟩ := D.exists_piM_U m (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hm)
  have huC := C.U_le_centralizer hS D hu
  have hu2 : u * u = 1 := D.piM_eq_one (u * u) (mul_mem hu hu) (by
    rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu hu)))⟩ :
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, huC⟩ * ⟨u, huC⟩
      from rfl, map_mul, show C.piM hS ⟨u, huC⟩ = m from hum]
    exact hM.mul_self_eq_one_of_mem_rootCenter hm)
  exact ⟨u, (D.mem_V_iff u hu).mpr hu2, hum⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem α_ne_γ : α ≠ (C.γ : Ω) := fun h => by
  obtain ⟨t, ht, htγ⟩ := mem_holtDelta.mp C.γ.2
  rw [← h] at htγ
  exact C.ne (htγ.symm.trans ht.2)

theorem smul_fixSet_x_of_normalizes_U (hS : Sec4Setting G Ω) (D : C.Splitting hS)
    {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {h : G} (hh : ∀ u ∈ D.U, h * u * h⁻¹ ∈ D.U) :
    h • fixSet Ω (Subgroup.zpowers C.x) = fixSet Ω (Subgroup.zpowers C.x) := by
  have hxU := D.V_le D.x_mem_V
  have hr : h * C.x * h⁻¹ ∈ D.V := (D.mem_V_iff _ (hh _ hxU)).mpr (by
    rw [show h * C.x * h⁻¹ * (h * C.x * h⁻¹) = h * (C.x * C.x) * h⁻¹ by group,
      C.x_mul_self hS, mul_one, mul_inv_cancel])
  have hx1 : C.x ≠ 1 := fun h1 => C.ne (by
    have h2 := (C.x_smul hS).1
    rwa [h1, one_smul] at h2)
  have hr1 : h * C.x * h⁻¹ ≠ 1 := by
    have := conj_ne_one (g := h⁻¹) hx1
    rwa [inv_inv] at this
  rw [← fixSet_zpowers_conj, C.fixSet_eq_of_mem_V hS D hT hUT hxv hr hr1]

theorem U_inf_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) :
    D.U ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) = D.V ∨
      D.U ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) = D.U := by
  have hM := C.isNaturalSE_Dv C.i
  set Px := fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x))
  set Cv := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i
  have hVPx := C.V_le_fixingSubgroup_x hS D hT hUT hxv
  have hUC := C.U_le_centralizer hS D
  set W := (((D.U ⊓ Px).subgroupOf Cv).map (C.piM hS))
  have hmemW : ∀ {u : G} (hu : u ∈ D.U ⊓ Px),
      C.piM hS ⟨u, hUC (Subgroup.mem_inf.mp hu).1⟩ ∈ W := fun {u} hu =>
    ⟨⟨u, hUC (Subgroup.mem_inf.mp hu).1⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hZW : rootCenter (seRadical (C.Dv.M C.i) γi) ≤ W := fun m hm => by
    obtain ⟨u, hu, rfl⟩ := C.exists_mem_V_piM_eq hS D hm
    exact hmemW (Subgroup.mem_inf.mpr ⟨D.V_le hu, hVPx hu⟩)
  have hWR : W ≤ seRadical (C.Dv.M C.i) γi := by
    rintro _ ⟨⟨u, huC⟩, hu, rfl⟩
    exact D.piM_U_mem u (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hu)).1
  have hαγ : C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i ≠ C.Dv.coord C.a C.i := fun h => C.α_ne_γ (by
    have h1 := (C.smul_eq_iff_piM_apply hS 1 C.a ⟨C.γ, C.γ_mem⟩).mpr
      (by rw [map_one, Equiv.Perm.one_apply]; exact h.symm)
    rwa [OneMemClass.coe_one, one_smul] at h1)
  have hinv : ∀ d ∈ C.Dv.M C.i, d γi = γi → d (C.Dv.coord C.a C.i) = C.Dv.coord C.a C.i →
      ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
    rintro d hdM hdγ - _ ⟨⟨u, huC⟩, hu, rfl⟩
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hu)
    obtain ⟨h, hhMc, -, hhU, hhd⟩ := D.exists_lift d hdM hdγ
    have hhx := C.smul_fixSet_x_of_normalizes_U hS D hT hUT hxv hhU
    have hhuPx : h * u * h⁻¹ ∈ Px := (mem_fixingSubgroup_iff G).mpr fun ω hω => by
      have h1 : h⁻¹ • ω ∈ fixSet Ω (Subgroup.zpowers C.x) :=
        Set.mem_smul_set_iff_inv_smul_mem.mp (by rw [hhx]; exact hω)
      rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hu2 _ h1, smul_inv_smul]
    have hhC := C.centralizer_Y_le hS (D.Mc_le hhMc)
    have hmem : h * u * h⁻¹ ∈ D.U ⊓ Px := Subgroup.mem_inf.mpr ⟨hhU u hu1, hhuPx⟩
    refine ⟨⟨h * u * h⁻¹, hUC (hhU u hu1)⟩, Subgroup.mem_subgroupOf.mpr hmem, ?_⟩
    rw [show (⟨h * u * h⁻¹, hUC (hhU u hu1)⟩ : Cv) = ⟨h, hhC⟩ * ⟨u, huC⟩ * (⟨h, hhC⟩)⁻¹ from rfl,
      map_mul, map_mul, map_inv, hhd]
  rcases hM.eq_rootCenter_or_eq_seRadical hαγ hZW hWR hinv with hW | hW
  · left
    refine le_antisymm (fun u hu => ?_) (le_inf D.V_le hVPx)
    have hu1 := (Subgroup.mem_inf.mp hu).1
    have hw := hmemW hu
    rw [hW] at hw
    refine (D.mem_V_iff u hu1).mpr (D.piM_eq_one (u * u) (mul_mem hu1 hu1) ?_)
    rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu1 hu1)))⟩ : Cv) =
      ⟨u, hUC hu1⟩ * ⟨u, hUC hu1⟩ from rfl, map_mul]
    exact hM.mul_self_eq_one_of_mem_rootCenter hw
  · right
    refine le_antisymm inf_le_left fun u hu => ?_
    have hw : C.piM hS ⟨u, hUC hu⟩ ∈ W := hW ▸ D.piM_U_mem u hu
    obtain ⟨⟨u', hu'C⟩, hu', hu'e⟩ := hw
    have hu'm := Subgroup.mem_subgroupOf.mp hu'
    have hu'U := (Subgroup.mem_inf.mp hu'm).1
    have h1 := D.piM_eq_one (u'⁻¹ * u) (mul_mem (inv_mem hu'U) hu) (by
      rw [show (⟨u'⁻¹ * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le
        (mul_mem (inv_mem hu'U) hu)))⟩ : Cv) = (⟨u', hu'C⟩)⁻¹ * ⟨u, hUC hu⟩ from rfl,
        map_mul, map_inv, hu'e, inv_mul_cancel])
    rw [← inv_mul_eq_one.mp h1]
    exact hu'm


theorem exists_mem_Z_piM_conj_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x)
    {m : Equiv.Perm (C.Dv.Ψc C.i)}
    (hm : m ∈ rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i))) :
    ∃ z, ∃ hz : z ∈ C.Z,
      C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))⟩ = m := by
  obtain ⟨n, i, e, hA⟩ := (C.isNaturalSE_Dv C.i).exists_isBenderAction
  set R := rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i))
  set f : C.Z → R := fun z => ⟨_, C.piM_conj_Z_mem hS hg₀ z.2⟩
  have hf : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨fun z₁ z₂ h => Subtype.ext (C.piM_conj_Z_injective hS hg₀ z₁.2 z₂.2 (congrArg Subtype.val h)),
      by rw [← C.card_V_eq_card_Z hS D hT hUT hxv, C.card_V_eq hS D,
        hA.card_rootCenter_seRadical, hA.card_rootCenter_seRadical]⟩
  obtain ⟨z, hz⟩ := hf.2 ⟨m, hm⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

theorem mem_fixingSubgroup_x_of_piM_conj_eq_one (hS : Sec4Setting G Ω) {g₀ : G}
    (hg₀ : g₀ * v * g₀⁻¹ = C.x) {y : G} (hy : C.x * y = y * C.x)
    (h1 : C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ hy⟩ = 1) :
    y ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) := by
  have h2 := (C.piM_eq_one_iff hS _).mp h1
  refine (mem_fixingSubgroup_iff G).mpr fun ω hω => ?_
  rw [← hg₀, fixSet_zpowers_conj] at hω
  obtain ⟨ω', hω', rfl⟩ := hω
  have h3 := h2 ω' hω'
  simp only at h3
  rw [mul_smul, mul_smul, inv_smul_eq_iff] at h3
  exact h3

theorem piM_conj_eq_one_of_mem_fixingSubgroup_x (hS : Sec4Setting G Ω) {g₀ : G}
    (hg₀ : g₀ * v * g₀⁻¹ = C.x) {y : G} (hy : C.x * y = y * C.x)
    (hyP : y ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x))) :
    C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ hy⟩ = 1 := by
  refine (C.piM_eq_one_iff hS _).mpr fun ω hω => ?_
  have h1 : g₀ • ω ∈ fixSet Ω (Subgroup.zpowers C.x) := by
    rw [← hg₀, fixSet_zpowers_conj]
    exact Set.smul_mem_smul_set hω
  show (g₀⁻¹ * y * g₀) • ω = ω
  rw [mul_smul, mul_smul, (mem_fixingSubgroup_iff G).mp hyP _ h1, inv_smul_smul]

theorem card_U_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    Nat.card D.U = Nat.card (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) := by
  have hUC := C.U_le_centralizer hS D
  refine Nat.card_eq_of_bijective (fun u : D.U => ⟨_, D.piM_U_mem u u.2⟩) ⟨fun u₁ u₂ h => ?_,
    fun m => ?_⟩
  · have h1 := congrArg Subtype.val h
    simp only at h1
    have hU : (u₁ : G)⁻¹ * u₂ ∈ D.U := mul_mem (inv_mem u₁.2) u₂.2
    have h2 := D.piM_eq_one _ hU (by
      rw [show (⟨(u₁ : G)⁻¹ * u₂, C.centralizer_Y_le hS (D.Mc_le (D.U_le hU))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          (⟨u₁, hUC u₁.2⟩)⁻¹ * ⟨u₂, hUC u₂.2⟩ from rfl, map_mul, map_inv, h1, inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · obtain ⟨u, hu, hum⟩ := D.exists_piM_U m m.2
    exact ⟨⟨u, hu⟩, Subtype.ext hum⟩

theorem exists_mem_Z_mul_mem (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {u : G} (hu : u ∈ D.U) :
    ∃ z ∈ C.Z, z * u ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) := by
  have hM := C.isNaturalSE_Dv C.i
  obtain ⟨n, i, e, hA⟩ := hM.exists_isBenderAction
  obtain ⟨hi1, hi3, hn⟩ := hA.params
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hxv
  have hVPx := C.V_le_fixingSubgroup_x hS D hT hUT hxv
  have hUC := C.U_le_centralizer hS D
  have hux : ∀ {w : G}, w ∈ D.U → C.x * w = w * C.x := fun hw => C.commute_x_of_mem_U hS D hw
  have hcase : u ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) →
      ∃ z ∈ C.Z, z * u ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) := fun h =>
    ⟨1, one_mem _, by rwa [one_mul]⟩
  rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
  ·
    refine hcase (hVPx ((D.mem_V_iff u hu).mpr (D.piM_eq_one (u * u) (mul_mem hu hu) ?_)))
    rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu hu)))⟩ :
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, hUC hu⟩ *
        ⟨u, hUC hu⟩ from rfl, map_mul]
    have h1 := D.piM_U_mem u hu
    rw [← hA.rootCenter_seRadical_eq_self rfl] at h1
    exact hM.mul_self_eq_one_of_mem_rootCenter h1
  ·
    set uC : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
      ⟨_, C.conj_mem_centralizer_v hg₀ (hux hu)⟩
    have hu2 : C.x * (u * u) = u * u * C.x := by
      rw [← mul_assoc, hux hu, mul_assoc, hux hu, mul_assoc]
    have hū2 : C.piM hS uC * C.piM hS uC = 1 := by
      rw [← map_mul, show uC * uC = ⟨_, C.conj_mem_centralizer_v hg₀ hu2⟩ from Subtype.ext (by
        show g₀⁻¹ * u * g₀ * (g₀⁻¹ * u * g₀) = g₀⁻¹ * (u * u) * g₀
        group)]
      exact C.piM_conj_eq_one_of_mem_fixingSubgroup_x hS hg₀ hu2
        (hVPx (C.mul_self_mem_V hS D hu))
    have hūM := hA.mem_of_mul_self_eq_one_of_suzuki (C.piM_mem_normalizer hS uC) hū2
    have hūc : C.piM hS uC (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i) =
        C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i := by
      refine (C.smul_eq_iff_piM_apply_eq hS uC ⟨_, C.inv_smul_γ_mem hS hg₀⟩).mp ?_
      show (g₀⁻¹ * u * g₀) • g₀⁻¹ • (C.γ : Ω) = g₀⁻¹ • (C.γ : Ω)
      rw [mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp (D.U_le_stabilizer hu)]
    obtain ⟨z, hz, hzū⟩ := C.exists_mem_Z_piM_conj_eq hS D hT hUT hxv hg₀
      (hM.mem_rootCenter_seRadical hūM hūc hū2)
    have hzx := C.commute_x hS (C.Z_le_Y hz)
    have hzux : C.x * (z⁻¹ * u) = z⁻¹ * u * C.x := by
      have hzx' : C.x * z⁻¹ = z⁻¹ * C.x := by
        calc C.x * z⁻¹ = z⁻¹ * (z * C.x) * z⁻¹ := by group
          _ = z⁻¹ * (C.x * z) * z⁻¹ := by rw [hzx]
          _ = z⁻¹ * C.x := by group
      rw [← mul_assoc, hzx', mul_assoc, hux hu, mul_assoc]
    refine ⟨z⁻¹, inv_mem hz, C.mem_fixingSubgroup_x_of_piM_conj_eq_one hS hg₀ hzux ?_⟩
    rw [show (⟨_, C.conj_mem_centralizer_v hg₀ hzux⟩ : Subgroup.centralizer
      ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        (⟨_, C.conj_mem_centralizer_v hg₀ hzx⟩)⁻¹ * uC from Subtype.ext (by
          show g₀⁻¹ * (z⁻¹ * u) * g₀ = (g₀⁻¹ * z * g₀)⁻¹ * (g₀⁻¹ * u * g₀)
          group), map_mul, map_inv, hzū, inv_mul_cancel]
  ·
    rcases C.U_inf_eq hS D hT hUT hxv with h | h
    · exfalso
      let φ : D.U →* Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
        { toFun := fun w => ⟨_, C.conj_mem_centralizer_v hg₀ (hux w.2)⟩
          map_one' := Subtype.ext (by
            show g₀⁻¹ * (1 : G) * g₀ = 1
            group)
          map_mul' := fun a b => Subtype.ext (by
            show g₀⁻¹ * ((a : G) * b) * g₀ = g₀⁻¹ * a * g₀ * (g₀⁻¹ * b * g₀)
            group) }
      set ϑ := (C.piM hS).comp φ
      have hsq : ∀ y ∈ ϑ.range, y * y = 1 := by
        rintro _ ⟨w, rfl⟩
        have hw2 : C.x * ((w : G) * w) = (w : G) * w * C.x := by
          rw [← mul_assoc, hux w.2, mul_assoc, hux w.2, mul_assoc]
        rw [← map_mul]
        rw [show ϑ (w * w) = C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ hw2⟩ from rfl]
        exact C.piM_conj_eq_one_of_mem_fixingSubgroup_x hS hg₀ hw2
          (hVPx (C.mul_self_mem_V hS D w.2))
      have hrange := (hA.card_le_of_mul_self_eq_one (E := ϑ.range)
        (by rintro _ ⟨w, rfl⟩; exact C.piM_mem_normalizer hS _) hsq).1
      have hker : ϑ.ker ≤ D.V.subgroupOf D.U := fun w hw => by
        have h1 : C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (hux w.2)⟩ = 1 := hw
        have h2 := C.mem_fixingSubgroup_x_of_piM_conj_eq_one hS hg₀ (hux w.2) h1
        rw [Subgroup.mem_subgroupOf, ← h]
        exact Subgroup.mem_inf.mpr ⟨w.2, h2⟩
      have hkerV : Nat.card ϑ.ker ≤ Nat.card D.V :=
        Nat.card_le_card_of_injective (fun w : ϑ.ker =>
          (⟨((w : D.U) : G), Subgroup.mem_subgroupOf.mp (hker w.2)⟩ : D.V))
          fun w₁ w₂ h => Subtype.ext (Subtype.ext (by
            have h1 := congrArg Subtype.val h
            simpa using h1))
      have hU := Subgroup.card_mul_index ϑ.ker
      rw [Subgroup.index_ker, C.card_U_eq hS D, hA.card_seRadical] at hU
      rw [C.card_V_eq hS D, hA.card_rootCenter_seRadical] at hkerV
      have h3 : (2 ^ n) ^ 3 ≤ 2 ^ n * 2 ^ (n + 1) := by
        rw [← hU]
        exact Nat.mul_le_mul hkerV hrange
      rw [← pow_mul, ← pow_add, Nat.pow_le_pow_iff_right (by norm_num)] at h3
      omega
    · exact hcase (Subgroup.mem_inf.mp (show u ∈ D.U ⊓ _ by rw [h]; exact hu)).2

end WPrime


section Lemma53

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

omit [Finite G] [FaithfulSMul G Ω] in
theorem eq_one_of_odd_of_pow {g : G} (hodd : Odd (orderOf g)) {k : ℕ} (hk : g ^ 2 ^ k = 1) :
    g = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 := (Nat.coprime_two_right.mpr hodd).pow_right k
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 h1)

theorem psi_eq_one_of_mem_oddCoreOf (hS : Sec4Setting G Ω) {q : G}
    (hq : q ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) :
    C.psi ⟨q, C.fixingSubgroup_le_pair (Subgroup.map_subtype_le _ hq)⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqP : q ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) := Subgroup.map_subtype_le _ hq
  have hqp := C.fixingSubgroup_le_pair hqP
  have hqγ : q • (C.γ : Ω) = C.γ := (mem_fixingSubgroup_iff G).mp hqP _ C.γ_mem
  have hodd : ∀ {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)), Odd (orderOf g) →
      Odd (orderOf (C.psi ⟨g, hg⟩)) := fun {g} hg hodd =>
    hodd.of_dvd_nat (orderOf_map_dvd C.psi ⟨g, hg⟩ |>.trans
      (by rw [Subgroup.orderOf_mk]))
  have hcomm : ∀ r ∈ C.Rhat, C.psi ⟨q, hqp⟩ * r = r * C.psi ⟨q, hqp⟩ := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y_of_mem_Rhat hS hr
    have hyP := C.Y_le_fixingSubgroup hS hy
    have hyp := C.fixingSubgroup_le_pair hyP
    have hc : q * y * q⁻¹ * y⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
      have h1 := FinalC.conj_mem_oddCoreOf_of_mem hyP (inv_mem hq)
      rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
      exact mul_mem hq h1
    have hcp : q * y * q⁻¹ * y⁻¹ ∈ stabilizer G ({α, β} : Set Ω) :=
      mul_mem (mul_mem (mul_mem hqp hyp) (inv_mem hqp)) (inv_mem hyp)
    have hψc : C.psi ⟨q * y * q⁻¹ * y⁻¹, hcp⟩ =
        C.psi ⟨q, hqp⟩ * C.psi ⟨y, hyp⟩ * (C.psi ⟨q, hqp⟩)⁻¹ * (C.psi ⟨y, hyp⟩)⁻¹ := by
      rw [show (⟨q * y * q⁻¹ * y⁻¹, hcp⟩ : stabilizer G ({α, β} : Set Ω)) =
        ⟨q, hqp⟩ * ⟨y, hyp⟩ * ⟨q, hqp⟩⁻¹ * ⟨y, hyp⟩⁻¹ from rfl]
      simp only [map_mul, map_inv]
    have hR : C.psi ⟨q * y * q⁻¹ * y⁻¹, hcp⟩ ∈ C.Rhat := by
      rw [hψc]
      exact mul_mem (conj_mem_seRadical (C.psi_mem_normalizer _) (C.psi_apply_bγ hqγ)
        (C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy))) (inv_mem (C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy)))
    obtain ⟨k, hk⟩ := C.isNaturalSE_N.isPGroup_seRadical C.bγ ⟨_, hR⟩
    have hk' : C.psi ⟨q * y * q⁻¹ * y⁻¹, hcp⟩ ^ 2 ^ k = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
        congrArg Subtype.val hk
    have h1 := eq_one_of_odd_of_pow (hodd hcp (FinalC.odd_orderOf_of_mem_oddCoreOf hc)) hk'
    rw [hψc] at h1
    calc C.psi ⟨q, hqp⟩ * C.psi ⟨y, hyp⟩ =
        C.psi ⟨q, hqp⟩ * C.psi ⟨y, hyp⟩ * (C.psi ⟨q, hqp⟩)⁻¹ * (C.psi ⟨y, hyp⟩)⁻¹ *
          (C.psi ⟨y, hyp⟩ * C.psi ⟨q, hqp⟩) := by group
      _ = C.psi ⟨y, hyp⟩ * C.psi ⟨q, hqp⟩ := by rw [h1, one_mul]
  have hZ := C.isNaturalSE_N.mem_rootCenter_seRadical_of_commute (C.psi_mem_normalizer _) hcomm
  obtain ⟨k, hk⟩ := C.isNaturalSE_N.isPGroup_seRadical C.bγ ⟨_, C.Zhat_le_Rhat hZ⟩
  have hk' : C.psi ⟨q, hqp⟩ ^ 2 ^ k = 1 := by
    simpa only [Subgroup.coe_pow, Subgroup.coe_mk, OneMemClass.coe_one] using
      congrArg Subtype.val hk
  exact eq_one_of_odd_of_pow (hodd hqp (FinalC.odd_orderOf_of_mem_oddCoreOf hq)) hk'

theorem exists_mem_Y_inv_mul_conj_mem (hS : Sec4Setting G Ω) {d : G}
    (hd : d ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) {y : G} (hy : y ∈ C.Y) :
    ∃ y' ∈ C.Y, y'⁻¹ * (d * y * d⁻¹) ∈
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hyP := C.Y_le_fixingSubgroup hS hy
  have hdp := C.fixingSubgroup_le_pair hd
  have hyp := C.fixingSubgroup_le_pair hyP
  have hdγ : d • (C.γ : Ω) = C.γ := (mem_fixingSubgroup_iff G).mp hd _ C.γ_mem
  have hcP : d * y * d⁻¹ ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    mul_mem (mul_mem hd hyP) (inv_mem hd)
  have hR : C.psi ⟨d * y * d⁻¹, C.fixingSubgroup_le_pair hcP⟩ ∈ C.Rhat := by
    rw [show (⟨d * y * d⁻¹, C.fixingSubgroup_le_pair hcP⟩ : stabilizer G ({α, β} : Set Ω)) =
      ⟨d, hdp⟩ * ⟨y, hyp⟩ * ⟨d, hdp⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
    exact conj_mem_seRadical (C.psi_mem_normalizer _) (C.psi_apply_bγ hdγ)
      (C.psi_mem_Rhat_of_mem_X (C.Y_le_X hy))
  obtain ⟨y', hy', hy'e⟩ := C.exists_mem_Y_of_mem_Rhat hS hR
  have hy'P := C.Y_le_fixingSubgroup hS hy'
  refine ⟨y', hy', C.mem_oddCoreOf_of_psi_eq_one hS (mul_mem (inv_mem hy'P) hcP) ?_⟩
  rw [show (⟨y'⁻¹ * (d * y * d⁻¹), C.fixingSubgroup_le_pair (mul_mem (inv_mem hy'P) hcP)⟩ :
    stabilizer G ({α, β} : Set Ω)) = ⟨y', C.fixingSubgroup_le_pair hy'P⟩⁻¹ *
      ⟨d * y * d⁻¹, C.fixingSubgroup_le_pair hcP⟩ from rfl, map_mul, map_inv, hy'e,
    inv_mul_cancel]

theorem exists_mem_Z_inv_mul_mem_of_commute (hS : Sec4Setting G Ω) {e : G}
    (he : e ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))
    (hc : ∀ y ∈ C.Y, e * y * e⁻¹ * y⁻¹ ∈
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)))) :
    ∃ z ∈ C.Z, z⁻¹ * e ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  have hep := C.fixingSubgroup_le_pair he
  have hcomm : ∀ r ∈ C.Rhat, C.psi ⟨e, hep⟩ * r = r * C.psi ⟨e, hep⟩ := by
    intro r hr
    obtain ⟨y, hy, rfl⟩ := C.exists_mem_Y_of_mem_Rhat hS hr
    have hyp := C.fixingSubgroup_le_pair (C.Y_le_fixingSubgroup hS hy)
    have h1 := C.psi_eq_one_of_mem_oddCoreOf hS (hc y hy)
    rw [show (⟨e * y * e⁻¹ * y⁻¹, _⟩ : stabilizer G ({α, β} : Set Ω)) =
      ⟨e, hep⟩ * ⟨y, hyp⟩ * ⟨e, hep⟩⁻¹ * ⟨y, hyp⟩⁻¹ from rfl] at h1
    simp only [map_mul, map_inv] at h1
    calc C.psi ⟨e, hep⟩ * C.psi ⟨y, hyp⟩ =
        C.psi ⟨e, hep⟩ * C.psi ⟨y, hyp⟩ * (C.psi ⟨e, hep⟩)⁻¹ * (C.psi ⟨y, hyp⟩)⁻¹ *
          (C.psi ⟨y, hyp⟩ * C.psi ⟨e, hep⟩) := by group
      _ = C.psi ⟨y, hyp⟩ * C.psi ⟨e, hep⟩ := by rw [h1, one_mul]
  have hZ := C.isNaturalSE_N.mem_rootCenter_seRadical_of_commute (C.psi_mem_normalizer _) hcomm
  obtain ⟨z, hz, hzψ⟩ := C.exists_mem_Z_of_mem_Zhat hS hZ
  have hzP := C.Z_le_fixingSubgroup hS hz
  refine ⟨z, hz, C.mem_oddCoreOf_of_psi_eq_one hS (mul_mem (inv_mem hzP) he) ?_⟩
  rw [show (⟨z⁻¹ * e, C.fixingSubgroup_le_pair (mul_mem (inv_mem hzP) he)⟩ :
    stabilizer G ({α, β} : Set Ω)) = ⟨z, C.fixingSubgroup_le_pair hzP⟩⁻¹ * ⟨e, hep⟩ from rfl,
    map_mul, map_inv, hzψ, inv_mul_cancel]

theorem exists_mem_Z_inv_mul_commutator_mem (hS : Sec4Setting G Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer (C.Y : Set G)) {d : G}
    (hd : d ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    ∃ z ∈ C.Z, z⁻¹ * (c * d * c⁻¹ * d⁻¹) ∈
      oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set Q := oddCoreOf P
  have hcv := C.centralizer_Y_le hS hc
  have hcP : ∀ b, b ∈ P ↔ c * b * c⁻¹ ∈ P := conj_mem_fixingSubgroup_iff hcv
  have hcP' : ∀ b, b ∈ P ↔ c⁻¹ * b * c⁻¹⁻¹ ∈ P := conj_mem_fixingSubgroup_iff (inv_mem hcv)
  have he : c * d * c⁻¹ * d⁻¹ ∈ P := mul_mem ((hcP d).mp hd) (inv_mem hd)
  refine C.exists_mem_Z_inv_mul_mem_of_commute hS he fun y hy => ?_
  have hyP := C.Y_le_fixingSubgroup hS hy
  obtain ⟨y₁, hy₁, hq₁⟩ := C.exists_mem_Y_inv_mul_conj_mem hS (inv_mem hd) hy
  rw [inv_inv] at hq₁
  have hcy : y * c = c * y := Subgroup.mem_centralizer_iff.mp hc y hy
  have hcy₁ : y₁ * c = c * y₁ := Subgroup.mem_centralizer_iff.mp hc y₁ hy₁
  have h1 : y * c * y⁻¹ = c := by rw [hcy, mul_inv_cancel_right]
  have h2 : y₁ * c⁻¹ * y₁⁻¹ = c⁻¹ := by
    calc y₁ * c⁻¹ * y₁⁻¹ = c⁻¹ * (c * y₁) * c⁻¹ * y₁⁻¹ := by group
      _ = c⁻¹ * (y₁ * c) * c⁻¹ * y₁⁻¹ := by rw [hcy₁]
      _ = c⁻¹ := by group
  have key : c * d * c⁻¹ * d⁻¹ * y * (c * d * c⁻¹ * d⁻¹)⁻¹ * y⁻¹ =
      y * (c * d * (y₁⁻¹ * (d⁻¹ * y * d))⁻¹ * (c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c) * d⁻¹ * c⁻¹) *
        y⁻¹ := by
    calc c * d * c⁻¹ * d⁻¹ * y * (c * d * c⁻¹ * d⁻¹)⁻¹ * y⁻¹ =
        (y * c * y⁻¹) * d * (y₁ * c⁻¹ * y₁⁻¹) * d⁻¹ * y * d * c * d⁻¹ * c⁻¹ * y⁻¹ := by
          rw [h1, h2]; group
      _ = _ := by group
  rw [key]
  have hq₂ : c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c ∈ Q := by
    have := FinalC.conj_mem_oddCoreOf_of_normalizes hcP' hq₁
    rwa [inv_inv] at this
  have hq₃ : c * d * (y₁⁻¹ * (d⁻¹ * y * d))⁻¹ * (c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c) * d⁻¹ * c⁻¹ ∈
      Q := by
    have h3 : d * ((y₁⁻¹ * (d⁻¹ * y * d))⁻¹ * (c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c)) * d⁻¹ ∈ Q :=
      FinalC.conj_mem_oddCoreOf_of_mem hd (mul_mem (inv_mem hq₁) hq₂)
    have h4 := FinalC.conj_mem_oddCoreOf_of_normalizes hcP h3
    rw [show c * d * (y₁⁻¹ * (d⁻¹ * y * d))⁻¹ * (c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c) * d⁻¹ * c⁻¹ =
      c * (d * ((y₁⁻¹ * (d⁻¹ * y * d))⁻¹ * (c⁻¹ * (y₁⁻¹ * (d⁻¹ * y * d)) * c)) * d⁻¹) * c⁻¹
      by group]
    exact h4
  exact FinalC.conj_mem_oddCoreOf_of_mem hyP hq₃

theorem commutator_mem_of_mem_commutator (hS : Sec4Setting G Ω) {c : G}
    (hc : c ∈ ⁅Subgroup.centralizer (C.Y : Set G), Subgroup.centralizer (C.Y : Set G)⁆) {d : G}
    (hd : d ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    c * d * c⁻¹ * d⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set Q := oddCoreOf P
  set CY := Subgroup.centralizer (C.Y : Set G)
  have hcQ : ∀ {g : G}, g ∈ CY → ∀ {q : G}, q ∈ Q → g * q * g⁻¹ ∈ Q := fun {g} hg {q} hq =>
    FinalC.conj_mem_oddCoreOf_of_normalizes
      (conj_mem_fixingSubgroup_iff (C.centralizer_Y_le hS hg)) hq
  have hcZ : ∀ {g : G}, g ∈ CY → ∀ {z : G}, z ∈ C.Z → z * g = g * z := fun {g} hg {z} hz =>
    Subgroup.mem_centralizer_iff.mp hg z (C.Z_le_Y hz)
  have hinvc : ∀ {g z : G}, z * g = g * z → g * z⁻¹ = z⁻¹ * g := fun {g z} h => by
    calc g * z⁻¹ = z⁻¹ * (z * g) * z⁻¹ := by group
      _ = z⁻¹ * (g * z) * z⁻¹ := by rw [h]
      _ = z⁻¹ * g := by group
  have R2 : ∀ {g g' z z' : G}, g ∈ CY → z ∈ C.Z → z' ∈ C.Z →
      z⁻¹ * (g * d * g⁻¹ * d⁻¹) ∈ Q → z'⁻¹ * (g' * d * g'⁻¹ * d⁻¹) ∈ Q →
        (z' * z)⁻¹ * (g * g' * d * (g * g')⁻¹ * d⁻¹) ∈ Q := by
    intro g g' z z' hg hz hz' h1 h2
    have hzP := C.Z_le_fixingSubgroup hS hz
    have e1 : g * z'⁻¹ = z'⁻¹ * g := hinvc (hcZ hg hz')
    have h4 := FinalC.conj_mem_oddCoreOf_of_mem (inv_mem hzP) (hcQ hg h2)
    rw [inv_inv] at h4
    have key : (z' * z)⁻¹ * (g * g' * d * (g * g')⁻¹ * d⁻¹) =
        z⁻¹ * (g * (z'⁻¹ * (g' * d * g'⁻¹ * d⁻¹)) * g⁻¹) * z * (z⁻¹ * (g * d * g⁻¹ * d⁻¹)) := by
      calc (z' * z)⁻¹ * (g * g' * d * (g * g')⁻¹ * d⁻¹) =
          z⁻¹ * (z'⁻¹ * g) * g' * d * g'⁻¹ * g⁻¹ * d⁻¹ := by group
        _ = z⁻¹ * (g * z'⁻¹) * g' * d * g'⁻¹ * g⁻¹ * d⁻¹ := by rw [e1]
        _ = _ := by group
    rw [key]
    exact mul_mem h4 h1
  have R3 : ∀ {g z : G}, g ∈ CY → z ∈ C.Z → z⁻¹ * (g * d * g⁻¹ * d⁻¹) ∈ Q →
      z⁻¹⁻¹ * (g⁻¹ * d * g⁻¹⁻¹ * d⁻¹) ∈ Q := by
    intro g z hg hz h1
    have hzP := C.Z_le_fixingSubgroup hS hz
    have e2 : g⁻¹ * z * g = z := by rw [mul_assoc, hcZ hg hz, inv_mul_cancel_left]
    have h2 := hcQ (inv_mem hg) (inv_mem h1)
    rw [inv_inv] at h2
    have h3 := FinalC.conj_mem_oddCoreOf_of_mem hzP h2
    have key : z⁻¹⁻¹ * (g⁻¹ * d * g⁻¹⁻¹ * d⁻¹) =
        z * (g⁻¹ * (z⁻¹ * (g * d * g⁻¹ * d⁻¹))⁻¹ * g) * z⁻¹ := by
      calc z⁻¹⁻¹ * (g⁻¹ * d * g⁻¹⁻¹ * d⁻¹) = z * (g⁻¹ * d * g * d⁻¹) * z * z⁻¹ := by group
        _ = z * (g⁻¹ * d * g * d⁻¹) * (g⁻¹ * z * g) * z⁻¹ := by rw [e2]
        _ = _ := by group
    rw [key]
    exact h3
  let K : Subgroup G :=
    { carrier := {g | g ∈ CY ∧ g * d * g⁻¹ * d⁻¹ ∈ Q}
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
        rw [show a * b * d * (a * b)⁻¹ * d⁻¹ = a * (b * d * b⁻¹ * d⁻¹) * a⁻¹ *
          (a * d * a⁻¹ * d⁻¹) by group]
        exact mul_mem (hcQ ha.1 hb.2) ha.2⟩
      one_mem' := ⟨one_mem _, by
        rw [show (1 : G) * d * 1⁻¹ * d⁻¹ = 1 by group]
        exact one_mem _⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        rw [show a⁻¹ * d * a⁻¹⁻¹ * d⁻¹ = a⁻¹ * (a * d * a⁻¹ * d⁻¹)⁻¹ * a⁻¹⁻¹ by group]
        exact hcQ (inv_mem ha.1) (inv_mem ha.2)⟩ }
  have hle : ⁅CY, CY⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨z₁, hz₁, h₁⟩ := C.exists_mem_Z_inv_mul_commutator_mem hS hg₁ hd
    obtain ⟨z₂, hz₂, h₂⟩ := C.exists_mem_Z_inv_mul_commutator_mem hS hg₂ hd
    have h₁' := R3 hg₁ hz₁ h₁
    have h₂' := R3 hg₂ hz₂ h₂
    have s1 := R2 hg₁ hz₁ hz₂ h₁ h₂
    have s2 := R2 (mul_mem hg₁ hg₂) (mul_mem hz₂ hz₁) (inv_mem hz₁) s1 h₁'
    have s3 := R2 (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁))
      (mul_mem (inv_mem hz₁) (mul_mem hz₂ hz₁)) (inv_mem hz₂) s2 h₂'
    have hz : z₂⁻¹ * (z₁⁻¹ * (z₂ * z₁)) = 1 := by
      rw [C.commute_of_mem_Z hS hz₂ (C.Z_le_Y hz₁)]
      group
    rw [hz, inv_one, one_mul] at s3
    exact ⟨Subgroup.commutator_mem_commutator hg₁ hg₂ |> (Subgroup.commutator_le_self _ ·),
      by rw [commutatorElement_def]; exact s3⟩
  exact (hle hc).2

theorem commutator_mem_oddCoreOf (hS : Sec4Setting G Ω) (D : C.Splitting hS) {c : G}
    (hc : c ∈ D.Mc) {d : G} (hd : d ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) :
    c * d * c⁻¹ * d⁻¹ ∈ oddCoreOf (fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) := by
  set P := fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))
  set Q := oddCoreOf P
  set Cv := Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)
  set CY := Subgroup.centralizer (C.Y : Set G)
  have hMcv : D.Mc ≤ Cv := D.Mc_le.trans (C.centralizer_Y_le hS)
  have hperf : ⁅C.Dv.M C.i, C.Dv.M C.i⁆ = C.Dv.M C.i := by
    rw [← Subgroup.map_subtype_commutator, (C.Dv.isPerfect_M C.i).commutator_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hlift : ∀ m ∈ ⁅C.Dv.M C.i, C.Dv.M C.i⁆, ∃ c' : Cv, (c' : G) ∈ ⁅D.Mc, D.Mc⁆ ∧
      C.piM hS c' = m := by
    intro m hm
    rw [Subgroup.commutator_def] at hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hm
      obtain ⟨ca, hca, hcae⟩ := D.exists_piM a ha
      obtain ⟨cb, hcb, hcbe⟩ := D.exists_piM b hb
      refine ⟨(⟨ca, hMcv hca⟩ : Cv) * ⟨cb, hMcv hcb⟩ * (⟨ca, hMcv hca⟩ : Cv)⁻¹ *
        (⟨cb, hMcv hcb⟩ : Cv)⁻¹, ?_, ?_⟩
      · have h1 := Subgroup.commutator_mem_commutator hca hcb
        rw [commutatorElement_def] at h1
        exact h1
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcae, hcbe, commutatorElement_def]
    | one => exact ⟨1, one_mem _, map_one _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨cx, hcx, hcxe⟩ := hx
      obtain ⟨cy, hcy, hcye⟩ := hy
      exact ⟨cx * cy, mul_mem hcx hcy, by rw [map_mul, hcxe, hcye]⟩
    | inv x _ hx =>
      obtain ⟨cx, hcx, hcxe⟩ := hx
      exact ⟨cx⁻¹, inv_mem hcx, by rw [map_inv, hcxe]⟩
  obtain ⟨c', hc'K, hc'e⟩ := hlift _ (hperf.symm ▸ D.piM_mem c hc)
  have hc'Mc : (c' : G) ∈ D.Mc := Subgroup.commutator_le_self _ hc'K
  have hc'Y : (c' : G) ∈ CY := D.Mc_le hc'Mc
  have hqP : (c' : G)⁻¹ * c ∈ P := by
    have h1 : C.piM hS (c'⁻¹ * ⟨c, hMcv hc⟩) = 1 := by
      rw [map_mul, map_inv, hc'e, inv_mul_cancel]
    exact (mem_fixingSubgroup_iff G).mpr ((C.piM_eq_one_iff hS _).mp h1)
  have hqQ : (c' : G)⁻¹ * c ∈ Q := D.mem_oddCore _ (mul_mem (inv_mem hc'Mc) hc) hqP
  have hc'd : (c' : G) * d * (c' : G)⁻¹ * d⁻¹ ∈ Q :=
    C.commutator_mem_of_mem_commutator hS (Subgroup.commutator_mono D.Mc_le D.Mc_le hc'K) hd
  have hqd : (c' : G)⁻¹ * c * d * ((c' : G)⁻¹ * c)⁻¹ * d⁻¹ ∈ Q := by
    have h1 := FinalC.conj_mem_oddCoreOf_of_mem hd (inv_mem hqQ)
    rw [show (c' : G)⁻¹ * c * d * ((c' : G)⁻¹ * c)⁻¹ * d⁻¹ =
      ((c' : G)⁻¹ * c) * (d * ((c' : G)⁻¹ * c)⁻¹ * d⁻¹) by group]
    exact mul_mem hqQ h1
  have h2 := FinalC.conj_mem_oddCoreOf_of_normalizes
    (conj_mem_fixingSubgroup_iff (C.centralizer_Y_le hS hc'Y)) hqd
  rw [show c * d * c⁻¹ * d⁻¹ = (c' : G) * ((c' : G)⁻¹ * c * d * ((c' : G)⁻¹ * c)⁻¹ * d⁻¹) *
    (c' : G)⁻¹ * ((c' : G) * d * (c' : G)⁻¹ * d⁻¹) by group]
  exact mul_mem h2 hc'd

end Lemma53

end FinConfig

end CFSG.Holt.H78
