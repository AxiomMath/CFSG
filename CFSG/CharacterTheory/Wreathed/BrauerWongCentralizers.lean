module

public import CFSG.CharacterTheory.Wreathed.BrauerWongSubgroup
public import CFSG.CharacterTheory.Wreathed.BrauerWongInvolutions
public import CFSG.CharacterTheory.Wreathed.CyclicWeakClosure

public noncomputable section

namespace CFSG.Wreathed.BrauerWong

open CFSG.Wreathed

universe u

variable {G : Type u} [Group G]

theorem x_mem_zpowers_of_mem_Z (n : ℕ) (hn : 1 ≤ n) (w : Wreath (2 ^ n))
    (hw : w ∈ Original.Z (2 ^ n)) (hw1 : w ≠ 1) :
    Original.x (2 ^ n) ∈ Subgroup.zpowers w := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (wreath_isPGroup n) w
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hw1 hk
  have hord0 : orderOf w ≠ 0 := by rw [hk]; positivity
  have h2 : 2 ∣ orderOf w := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  have hinv := orderOf_pow_orderOf_div hord0 h2
  have hcen : w ^ (orderOf w / 2) ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [← Original.Z_eq _ (Nat.one_lt_two_pow (by omega))]
    exact (Original.Z _).pow_mem hw _
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hx := unique_central_involution j _ hinv hcen
  have hxeq : Original.x (2 ^ (j + 1)) = w ^ (orderOf w / 2) := by
    rw [hx, x_eq_element, show 2 ^ (j + 1) / 2 = 2 ^ j by
      rw [pow_succ, Nat.mul_div_cancel _ two_pos]]
  rw [hxeq]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

variable {n : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))

theorem modelHom_x_mem_zpowers (hn : 1 ≤ n) {z : G} (hz : z ∈ modelCenter S e) (hz1 : z ≠ 1) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ Subgroup.zpowers z := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hw1 : w ≠ 1 := fun h => hz1 (by rw [h, map_one])
  rw [← MonoidHom.map_zpowers]
  exact Subgroup.mem_map_of_mem _ (x_mem_zpowers_of_mem_Z n hn w hw hw1)

theorem sylow_le_centralizer_of_mem_modelCenter (hn : 2 ≤ n) {z : G}
    (hz : z ∈ modelCenter S e) :
    (S : Subgroup G) ≤ Subgroup.centralizer {z} := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := modelCenter_conj S e hn hz hs
  calc
    s * z = s * (s⁻¹ * z * s) := by rw [h]
    _ = z * s := by group

variable [Finite G]

theorem vNormalizer_le_centralizer_of_mem_modelCenter (hn : 2 ≤ n) {z : G}
    (hz : z ∈ modelCenter S e) :
    Subgroup.normalizer (modelV S e : Set G) ≤ Subgroup.centralizer {z} := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (modelVNormalizer_le_center_centralizer n hn S e hg)
    z hz).symm

theorem centralizer_base_order_two (hn : 2 ≤ n) {z : G} (hz : z ∈ modelCenter S e)
    (hz1 : z ≠ 1) :
    let X := Subgroup.centralizer ({z} : Set G)
    let hSX := sylow_le_centralizer_of_mem_modelCenter S e hn hz
    Nat.card (Subgroup.normalizer (modelBase (subSylow S X hSX) (subCoordinates S e X hSX) :
        Set X) ⧸
      (Subgroup.centralizer (modelBase (subSylow S X hSX) (subCoordinates S e X hSX) :
          Set X)).subgroupOf
        (Subgroup.normalizer (modelBase (subSylow S X hSX) (subCoordinates S e X hSX) :
          Set X))) = 2 := by
  intro X hSX
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  set P := subSylow S X hSX
  set f := subCoordinates S e X hSX
  set j := wreathModelHom P f
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) P f with htwo | hsix
  · exact htwo
  · exfalso
    obtain ⟨g, -, hconj⟩ := modelBaseNormalizer_involutions_transitive n (by omega) P f hsix
      (j (Original.x (2 ^ n))) (j (Original.x2 (2 ^ n)))
      ((mem_modelBase_iff P f _).mpr (by rw [Original.x_eq, element_mem_base]))
      ((mem_modelBase_iff P f _).mpr (by rw [Original.x2_eq, element_mem_base]))
      (by rw [orderOf_injective _ (wreathModelHom_injective P f)];
          exact hstr.involution_orders.1)
      (by rw [orderOf_injective _ (wreathModelHom_injective P f)];
          exact hstr.involution_orders.2.1)
    have hxz := modelHom_x_mem_zpowers S e (by omega) hz hz1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
    have hcomm : (g : G) * wreathModelHom S e (Original.x (2 ^ n)) =
        wreathModelHom S e (Original.x (2 ^ n)) * g := by
      rw [← hk]
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp g.property) k).eq
    have hval := congrArg Subtype.val hconj
    change (g : G) * wreathModelHom S e (Original.x (2 ^ n)) * (g : G)⁻¹ =
      wreathModelHom S e (Original.x2 (2 ^ n)) at hval
    rw [hcomm, mul_inv_cancel_right] at hval
    exact modelHom_x_ne_x2 S e (by omega) hval

theorem centralizer_noAbelian_and_typeII (hn : 2 ≤ n)
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3))) {z : G} (hz : z ∈ modelCenter S e) (hz1 : z ≠ 1) :
    (S : Subgroup G) ≤ Subgroup.centralizer {z} ∧
      NoAbelianTwoPowerIndexIntersection ↥(Subgroup.centralizer ({z} : Set G))
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {z})) ∧
      IsTypeII ↥(Subgroup.centralizer ({z} : Set G))
        ((S : Subgroup G).subgroupOf (Subgroup.centralizer {z})) n := by
  set X := Subgroup.centralizer ({z} : Set G)
  have hSX := sylow_le_centralizer_of_mem_modelCenter S e hn hz
  have hN := vNormalizer_le_centralizer_of_mem_modelCenter S e hn hz
  have hsixX := subVSym3 S e X hSX hN hn hsix
  have hcoe := subSylow_coe S X hSX
  refine ⟨hSX, ?_, ?_⟩
  · rw [← hcoe]
    exact noAbelian_of_vSym3 n hn _ _ hsixX
  · rw [← hcoe]
    exact typeII_of_base_order_two n hn _ _ (centralizer_base_order_two S e hn hz hz1) hsixX

theorem eq_centralizer_mul_pPrimeCore_of_base_order_two (hn : 2 ≤ n)
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    {z : G} (hz : z ∈ modelCenter S e) (g : G) :
    ∃ c ∈ Subgroup.centralizer {z}, ∃ o ∈ CFSG.pPrimeCore 2 G, g = c * o := by
  have hcyc : IsCyclic (modelCenter S e) := by
    rw [modelCenter_eq_zpowers]
    infer_instance
  have hAC : modelCenter S e ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h := modelCenter_conj S e hn hc hs
    calc
      s * c = s * (s⁻¹ * c * s) := by rw [h]
      _ = c * s := by group
  obtain ⟨-, hfac⟩ := cyclic_weakly_closed_central_sylow_subgroup_central_mod_odd_core S
    (modelCenter S e) (modelCenter_le_sylow S e) hAC
    (fun c hc g hg => modelCenter_isolated_of_base_order_two hn S e hcard hc g hg)
  obtain ⟨r, hr, c, hc, rfl⟩ := hfac g
  rw [weakClosure_oddCore_eq_pPrimeCore] at hr
  refine ⟨c, ?_, c⁻¹ * r * c, ?_, by group⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hc z hz).symm
  · have := (CFSG.pPrimeCore_normal (p := 2) (G := G)).conj_mem r hr c⁻¹
    simpa using this

end CFSG.Wreathed.BrauerWong
