module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sl23PocketIn_comap_cover {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    (Y : Subgroup G) (ρ : ↥Y →* P) (h : OddCentralCover ρ) {z : G} (hzY : z ∈ Y)
    (hz : z * z = 1) {K : Subgroup P} (hK : Sl23PocketIn (⊤ : Subgroup P) (ρ ⟨z, hzY⟩) K)
    (hSL : Nonempty (↥K ≃* SL2F3)) :
    Sl23PocketIn Y z ((K.comap ρ).map Y.subtype) := by
  have hzz : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz
  have hcen := h.centralizer_singleton_eq_comap hzz
  have hcomm : ∀ k : ↥Y, ρ k ∈ K → (k : G) * z = z * (k : G) := by
    intro k hk
    have hkC : ρ k ∈ centralizer ({ρ ⟨z, hzY⟩} : Set P) := (Subgroup.mem_inf.mp (hK.2.1 hk)).2
    have hk' : k ∈ centralizer ({(⟨z, hzY⟩ : ↥Y)} : Set ↥Y) := by
      rw [hcen]
      exact hkC
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk')
  let C : Subgroup G := Y ⊓ centralizer ({z} : Set G)
  let CP : Subgroup P := ⊤ ⊓ centralizer ({ρ ⟨z, hzY⟩} : Set P)
  have hψ : ∀ c : ↥C, (ρ.comp (Subgroup.inclusion (inf_le_left : C ≤ Y))) c ∈ CP := by
    intro c
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change ρ (Subgroup.inclusion (inf_le_left : C ≤ Y) c) * ρ ⟨z, hzY⟩ =
      ρ ⟨z, hzY⟩ * ρ (Subgroup.inclusion (inf_le_left : C ≤ Y) c)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2.2)
  let ψ : ↥C →* ↥CP := (ρ.comp (Subgroup.inclusion (inf_le_left : C ≤ Y))).codRestrict CP hψ
  have hsub : ((K.subgroupOf CP).comap ψ).IsSubnormal := hK.2.2.1.comap ψ
  have heq : ((K.comap ρ).map Y.subtype).subgroupOf C = (K.subgroupOf CP).comap ψ := by
    ext c
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨k, hk, hkc⟩
      have hkc' : k = ⟨(c : G), c.2.1⟩ := Subtype.ext hkc
      rw [hkc'] at hk
      exact hk
    · intro hc
      exact ⟨⟨(c : G), c.2.1⟩, hc, rfl⟩
  refine ⟨⟨⟨z, hzY⟩, hK.1, rfl⟩, le_inf (Subgroup.map_subtype_le _) ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm k hk
  · rw [heq]
    exact hsub
  · exact isSL23Mod_of_mulEquiv ((K.comap ρ).equivMapOfInjective Y.subtype Y.subtype_injective)
      (h.isSL23Mod_comap hSL)

theorem exists_lift_mem_pCore {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    (Y : Subgroup G) (ρ : ↥Y →* P) (h : OddCentralCover ρ) {K R : Subgroup P} (hRK : R ≤ K)
    (hRn : (R.subgroupOf K).Normal) (hR2 : IsPGroup 2 ↥R) {r : P} (hr : r ∈ R) :
    ∃ x : ↥Y, ρ x = r ∧
      (x : G) ∈ CFSG.inSubgroup (CFSG.pCore 2) ((K.comap ρ).map Y.subtype) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Kt : Subgroup ↥Y := K.comap ρ
  let ρK : ↥Kt →* ↥K := ρ.subgroupComap K
  have hK : OddCentralCover ρK := h.subgroupComap K
  let R₀ : Subgroup ↥K := R.subgroupOf K
  have hR₀2 : IsPGroup 2 ↥R₀ := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRK).symm
  haveI : Group.IsNilpotent ↥R₀ := hR₀2.isNilpotent
  obtain ⟨a, ha⟩ := h.surjective r
  have haKt : a ∈ Kt := by
    change ρ a ∈ K
    rw [ha]
    exact hRK hr
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hrk : (ρ a) ^ (2 ^ k) = 1 := by
    rw [ha]
    exact congrArg Subtype.val hk
  obtain ⟨m, hm1, hm2⟩ := h.exists_lift_pow_two_pow hrk
  have hxKt : a ^ m ∈ Kt := pow_mem haKt m
  let N' : Subgroup ↥Kt := R₀.comap ρK
  haveI hN'n : N'.Normal := hRn.comap ρK
  have hN'nil : Group.IsNilpotent ↥N' :=
    Subgroup.isNilpotent_of_ker_le_center (ρK.subgroupComap R₀) (hK.subgroupComap_ker_le_center R₀)
  have hxN' : (⟨a ^ m, hxKt⟩ : ↥Kt) ∈ N' := by
    change ρ (a ^ m) ∈ R
    rw [hm1, ha]
    exact hr
  have hx2 : (⟨a ^ m, hxKt⟩ : ↥Kt) ^ (2 ^ k) = 1 := Subtype.ext hm2
  have hpc := mem_pCore_two_of_nilpotent_normal N' hN'nil hxN' hx2
  let ι : ↥Kt ≃* ↥(Kt.map Y.subtype) := Kt.equivMapOfInjective Y.subtype Y.subtype_injective
  have hmem : ι ⟨a ^ m, hxKt⟩ ∈ CFSG.pCore 2 ↥(Kt.map Y.subtype) := by
    rw [← CFSG.pCore_map_iso 2 ι]
    exact Subgroup.mem_map_of_mem _ hpc
  exact ⟨a ^ m, by rw [hm1, ha], ι ⟨a ^ m, hxKt⟩, hmem, rfl⟩

theorem genPocketCore_le_map {G P : Type} [Group G] [Finite G] [Group P] [Finite P]
    (Y : Subgroup G) (ρ : ↥Y →* P) (h : OddCentralCover ρ) {z : G} (hzY : z ∈ Y)
    (hz : z * z = 1) :
    genPocketCore (ρ ⟨z, hzY⟩) ≤ ((pocketCore2 Y z).comap Y.subtype).map ρ := by
  refine iSup_le fun K => iSup_le fun R => iSup_le fun hP => ?_
  intro r hr
  obtain ⟨x, hxr, hx⟩ := exists_lift_mem_pCore Y ρ h hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2 hr
  refine ⟨x, ?_, hxr⟩
  have hpocket := sl23PocketIn_comap_cover Y ρ h hzY hz hP.1 hP.2.1
  exact (le_iSup₂ (f := fun (K' : Subgroup G) (_ : Sl23PocketIn Y z K') =>
    CFSG.inSubgroup (CFSG.pCore 2) K') _ hpocket) hx

end CFSG.OddStandard.SmallF3.Omega
