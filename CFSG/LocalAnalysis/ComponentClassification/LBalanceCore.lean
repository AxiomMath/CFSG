module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceCoreOrbit
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreFreeTwoLayer

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem pComponent_centralizer_le_layer {p : ℕ} [Fact p.Prime] (hO : pPrimeCore p H = ⊥)
    {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1)
    (hout : ∀ K : Subgroup H, IsComponent K →
      Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K)))
    {L : Subgroup H} (hLC : L ≤ centralizer ({x} : Set H))
    (hL : IsPComponent p (L.subgroupOf (centralizer ({x} : Set H)))) : L ≤ layer H := by
  obtain ⟨n, hxn⟩ := hx
  have : (layer H).Characteristic := layer_characteristic
  have hE : (layer H).Normal := inferInstance
  set Z := (center (layer H)).map (layer H).subtype
  have hLperf : Group.IsPerfect L := by
    have := CatalogueBHeldSmallCore.pComponent_perfect p _ hL
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLC).toMonoidHom)
      (subgroupOfEquivOfLe hLC).surjective
  have hLP : ⁅L, pCore p H⁆ = ⊥ := by
    have hS : IsPGroup p (zpowers x) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hxn)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hCS : centralizer ((zpowers x : Subgroup H) : Set H) ≤ centralizer ({x} : Set H) :=
      centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers x))
    have hLS : (L.subgroupOf (centralizer ({x} : Set H))).map (centralizer ({x} : Set H)).subtype
        ≤ centralizer ((zpowers x : Subgroup H) : Set H) := by
      rw [map_subgroupOf_eq_of_le hLC, le_centralizer_iff, zpowers_le, mem_centralizer_iff]
      intro l hl
      exact mem_centralizer_singleton_iff.mp (hLC hl)
    have h := LiteratureLocal.p_component_commutator_eq_bot_of_le_centralizer hS pCore_normal
      pCore_isPGroup hCS hL hLS
    rwa [map_subgroupOf_eq_of_le hLC] at h
  have hFP : fittingSubgroup H ≤ pCore p H :=
    le_sSup ⟨inferInstance, isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO⟩
  have hLF : ⁅L, fittingSubgroup H⁆ = ⊥ := le_bot_iff.mp (hLP ▸ commutator_mono le_rfl hFP)
  have hLZ : L ≤ centralizer (Z : Set H) := commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp (hLF ▸ commutator_mono le_rfl
      UnbalancedLayer.center_layer_le_fittingSubgroup))
  set U := UnbalancedLayer.displacementSubgroup Z x
  have hCU := UnbalancedLayer.centralizer_inf_le_displacementSubgroup Z x
  have hLCC : L ≤ centralizer (Z : Set H) ⊓ centralizer ({x} : Set H) := le_inf hLZ hLC
  have hLU : IsPComponent p (L.subgroupOf U) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hLCC hCU
      (UnbalancedLayer.centralizer_inf_normal_displacementSubgroup Z x).isSubnormal).mpr
      (CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hLCC inf_le_right hL)
  have hNn : ((layer H ⊓ U).subgroupOf U).Normal := by
    rw [inf_subgroupOf_right]
    exact hE.subgroupOf U
  rcases CatalogueBPrimeJoin.contains_or_normalizes_core p (L.subgroupOf U)
      ((layer H ⊓ U).subgroupOf U) hLU hNn.isSubnormal with hLN | ⟨-, hcore⟩
  · exact (le_of_subgroupOf_le (hLCC.trans hCU) hLN).trans inf_le_left
  set O : Subgroup H := ((pPrimeCore p (L.subgroupOf U)).map (L.subgroupOf U).subtype).map
    U.subtype with hOdef
  have hOcop : Nat.Coprime p (Nat.card O) := by
    rw [hOdef, card_map_of_injective U.subtype_injective,
      card_map_of_injective (L.subgroupOf U).subtype_injective]
    exact pPrimeCore_coprime_card
  have hdisp : ∀ l ∈ L, ∀ w ∈ layer H ⊓ U, l * w * l⁻¹ * w⁻¹ ∈ O := by
    intro l hl w hw
    have hlU : l ∈ U := hCU (hLCC hl)
    have hmem : ⁅(⟨l, hlU⟩ : U), (⟨w, (Subgroup.mem_inf.mp hw).2⟩ : U)⁆ ∈
        ⁅L.subgroupOf U, (layer H ⊓ U).subgroupOf U⁆ :=
      commutator_mem_commutator (mem_subgroupOf.mpr hl) (mem_subgroupOf.mpr hw)
    have h := mem_map_of_mem U.subtype (hcore hmem)
    simpa only [commutatorElement_def, coe_subtype, coe_mul, coe_inv] using h
  have hnorm : ∀ K : Subgroup H, IsComponent K → L ≤ normalizer (K : Set H) := by
    intro K hK
    obtain ⟨u, huM, ⟨a, hua⟩, ⟨k₀, hk₀, hk₀u⟩, hz⟩ :=
      Core.exists_orbit_witness hxn hK (Core.prime_dvd_card_center_quotient hO hK)
    have huE : u ∈ layer H := Core.orbitJoin_le_layer hK x huM
    have huC : u ∈ centralizer (Z : Set H) := by
      rw [mem_centralizer_iff]
      intro z hzZ
      exact (mem_centralizer_iff.mp ((mem_map_center_iff _).mp hzZ).2 u huE).symm
    have huN : u ∈ layer H ⊓ U := Subgroup.mem_inf.mpr
      ⟨huE, UnbalancedLayer.mem_displacementSubgroup.mpr ⟨huC, hz⟩⟩
    have horb := Core.conjugate_mem_orbit hK hLC hOcop huM hua hk₀ hk₀u
      fun l hl => hdisp l hl u huN
    refine Core.le_normalizer_of_perfect hLperf hLC fun l hl => ?_
    have h := horb l⁻¹ (inv_mem hl)
    rwa [inv_inv] at h
  exact LocalAnalysis.ComponentInitial.unique_perfect_component_normalizer_enters_layer hLperf
    hLF hnorm hout

theorem pLayer_centralizer_le_layer {p : ℕ} [Fact p.Prime] (hO : pPrimeCore p H = ⊥)
    {x : H} (hx : ∃ n : ℕ, x ^ p ^ n = 1)
    (hout : ∀ K : Subgroup H, IsComponent K →
      Group.IsSolvable (OuterAutomorphisms.Outer (K ⧸ center K))) :
    (pLayer (centralizer ({x} : Set H)) p).map (centralizer ({x} : Set H)).subtype ≤
      layer H := by
  rw [map_le_iff_le_comap]
  refine sSup_le fun L' hL' => ?_
  rw [← map_le_iff_le_comap]
  have hL'eq : (L'.map (centralizer ({x} : Set H)).subtype).subgroupOf
      (centralizer ({x} : Set H)) = L' :=
    comap_map_eq_self_of_injective (centralizer ({x} : Set H)).subtype_injective L'
  exact pComponent_centralizer_le_layer hO hx hout (map_subtype_le L') (by rw [hL'eq]; exact hL')

end CFSG.ComponentClassification.LBalance
