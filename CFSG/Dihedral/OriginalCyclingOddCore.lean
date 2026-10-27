module

public import CFSG.Dihedral.ASevenCyclingOddCore
public import CFSG.Dihedral.PSL2CyclingOddCore
public import CFSG.Dihedral.PrimeClassTransport
public import CFSG.Dihedral.OriginalASevenPrimeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cycles_map_equiv {X : Type} [Group X] (e : G ≃* X)
    (H V : Subgroup G) (hc : Cycles H V) :
    Cycles (H.map e.toMonoidHom) (V.map e.toMonoidHom) := by
  obtain ⟨x, hxH, hxN, hxmove⟩ := hc
  refine ⟨e x, Subgroup.mem_map_of_mem e.toMonoidHom hxH, ?_, ?_⟩
  · rw [← Subgroup.map_normalizer_eq_of_bijective V e.bijective]
    exact Subgroup.mem_map_of_mem e.toMonoidHom hxN
  · intro v hv hvone hfix
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
    have hwone : w ≠ 1 := fun h => hvone (by simp [h])
    apply hxmove w hw hwone
    apply e.injective
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using hfix

namespace OriginalData

variable (d : OriginalData G)

theorem t_mem_fourgroup (V : Subgroup G) (hV : IsKleinFour V)
    (hVS : V ≤ (d.S : Subgroup G)) : d.t ∈ V := by
  have htS : d.t ∈ (d.S : Subgroup G) := d.S.pow_mem d.r_mem_sylow _
  have htcenter : (⟨d.t, htS⟩ : (d.S : Subgroup G)) ∈
      Subgroup.center (d.S : Subgroup G) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hycent : (y : G) ∈ Subgroup.centralizer ({d.t} : Set G) := by
      simpa only [d.centralizer, t] using d.sylow_le_centralizer y.property
    exact Subgroup.mem_centralizer_singleton_iff.mp hycent
  obtain ⟨e⟩ := d.sylow_mulEquiv_dihedral
  exact center_mem_kleinFour_of_dihedral_mulEquiv (by have := d.three_le; omega) e
    (V.subgroupOf (d.S : Subgroup G)) (isKleinFour_subgroupOf hVS hV) htcenter

theorem cycling_oddCore_centralizes (d : OriginalData G) [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H V : Subgroup G)
    (hV : IsKleinFour V) (hVH : V ≤ H) (hc : Cycles H V) :
    oddCoreOf H ≤ Subgroup.centralizer (V : Set G) := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact oddCoreOf_centralizes_cycling_fourgroup_of_aSeven_model hA.some H V hV hVH hc
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let : Fact r.Prime := hr
    have hk : k ≠ 0 := by intro h; simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    have hmapV := isKleinFour_map_of_injective V hV e.toMonoidHom e.injective
    have hbot := psl2_cycling_oddCoreOf_eq_bot (GaloisField r k) hK
      (H.map e.toMonoidHom) (V.map e.toMonoidHom) hmapV
      (Subgroup.map_mono hVH) (cycles_map_equiv e H V hc)
    rw [oddCoreOf_map_equiv] at hbot
    have heq := (Subgroup.map_eq_bot_iff_of_injective (oddCoreOf H) e.injective).mp hbot
    rw [heq]
    exact bot_le

theorem cycling_oddCore_le_original [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (V H : Subgroup G)
    (hV : IsFourGroup V) (hVS : V ≤ (d.S : Subgroup G))
    (hVH : V ≤ H) (hc : Cycles H V) :
    oddCoreOf H ≤ d.R ⊓ Subgroup.centralizer (V : Set G) ⊓ H := by
  have hVK := isKleinFour_of_isFourGroup V hV
  have hcent := d.cycling_oddCore_centralizes hnonab H V hVK hVH hc
  have htV := d.t_mem_fourgroup V hVK hVS
  have hJC : oddCoreOf H ≤ d.C := by
    rw [d.centralizer]
    change oddCoreOf H ≤ Subgroup.centralizer ({d.t} : Set G)
    exact hcent.trans (Subgroup.centralizer_le (by
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      exact hv ▸ htV))
  exact le_inf (le_inf (d.odd_subgroup_le_R_of_le_C _ hJC (oddCoreOf_odd H)) hcent)
    (oddCoreOf_le H)

theorem cycling_local_core_and_inverted [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∀ (V H : Subgroup G), IsFourGroup V → V ≤ (d.S : Subgroup G) →
      V ≤ H → H ≠ ⊤ → Cycles H V →
      oddCoreOf H ≤ d.R ⊓ Subgroup.centralizer (V : Set G) ⊓ H ∧
      ∀ v ∈ V, v ≠ 1 → v ≠ d.t → IsCyclic (d.invertedSubgroup H v) := by
  intro V H hV hVS hVH _ hc
  exact ⟨d.cycling_oddCore_le_original hnonab V H hV hVS hVH hc,
    fun v _ _ _ => d.invertedSubgroup_isCyclic hnonab H v⟩

theorem both_cycles_oddCore_centralizes_sylow [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H)
    (hc0 : Cycles H (d.V 0)) (hc1 : Cycles H (d.V 1)) :
    oddCoreOf H ≤ Subgroup.centralizer (d.S : Set G) := by
  have h0 := d.cycling_oddCore_centralizes hnonab H (d.V 0)
    (d.V_isKleinFour_general 0) ((d.V_le_sylow 0).trans hSH) hc0
  have h1 := d.cycling_oddCore_centralizes hnonab H (d.V 1)
    (d.V_isKleinFour_general 1) ((d.V_le_sylow 1).trans hSH) hc1
  intro u hu
  have hV0 : d.V 0 ≤ Subgroup.centralizer ({u} : Set G) := by
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h0 hu) v hv)
  have hV1 : d.V 1 ≤ Subgroup.centralizer ({u} : Set G) := by
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (h1 hu) v hv)
  have hSC : (d.S : Subgroup G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [← d.V_sup_eq_sylow]
    exact sup_le hV0 hV1
  exact Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp (hSC hv)

end OriginalData

end CFSG.DihedralBlueprint
