module

public import CFSG.GroupTheory.InvolutionHexagon
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Wreathed.BaseNormalizer
public import CFSG.CharacterTheory.Wreathed.OriginalStructure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public noncomputable section

namespace CFSG.Wreathed.FourPointInvolutionHexagon

open CFSG.Assembly CFSG.GroupTheory.SevenInvolutionWreathLaw CFSG.GroupTheory.InvolutionHexagon

open scoped Classical

theorem s_mul_t (m : ℕ) : Original.s m * Original.t m = Original.t m * Original.s m := by
  simp only [Original.s, Original.t, element_base_mul, add_zero, zero_add]

theorem zpowers_s_inf_zpowers_t (m : ℕ) [Finite (Wreath m)] :
    Subgroup.zpowers (Original.s m) ⊓ Subgroup.zpowers (Original.t m) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgs, hgt⟩
  obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hgs)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hgt)
  rw [Subgroup.mem_bot]
  simp only [Original.s, Original.t, element_base_pow] at hj ⊢
  have hc := @element_injective m (j • 0, j • 1, 0) (i • 1, i • 0, 0) hj
  simp only [Prod.mk.injEq] at hc
  rw [← hc.1, smul_zero, smul_zero, element_zero]

theorem z_notMem_closure (m : ℕ) :
    Original.z m ∉ Subgroup.closure {Original.s m, Original.t m} := by
  change Original.z m ∉ Original.U m
  rw [Original.U_eq, Original.z, element_mem_base]
  decide

theorem z_inv (m : ℕ) : (Original.z m)⁻¹ = Original.z m :=
  inv_eq_of_mul_eq_one_right (mul_self_of_orderOf_eq_two (Original.orderOf_z m))

theorem z_inv_mul_s_mul_z (m : ℕ) :
    (Original.z m)⁻¹ * Original.s m * Original.z m = Original.t m := by
  have h := Original.z_conjugates_s m
  rw [z_inv] at h ⊢
  exact h

theorem z_inv_mul_t_mul_z (m : ℕ) :
    (Original.z m)⁻¹ * Original.t m * Original.z m = Original.s m := by
  rw [← Original.z_conjugates_s m]
  group

theorem x_eq_sq : Original.x (2 ^ 2) = (Original.s (2 ^ 2) * Original.t (2 ^ 2)) ^ 2 := by
  rw [Original.x, Original.a]
  norm_num

variable {G : Type} [Group G]

theorem wreathModelHom_generators [Finite (Wreath (2 ^ 2))] (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ 2)) :
    let φ := wreathModelHom S e
    φ (Original.s (2 ^ 2)) * φ (Original.t (2 ^ 2)) =
        φ (Original.t (2 ^ 2)) * φ (Original.s (2 ^ 2)) ∧
      orderOf (φ (Original.s (2 ^ 2))) = 4 ∧ orderOf (φ (Original.t (2 ^ 2))) = 4 ∧
      Subgroup.zpowers (φ (Original.s (2 ^ 2))) ⊓ Subgroup.zpowers (φ (Original.t (2 ^ 2))) = ⊥ ∧
      orderOf (φ (Original.z (2 ^ 2))) = 2 ∧
      φ (Original.z (2 ^ 2)) ∉
        Subgroup.closure {φ (Original.s (2 ^ 2)), φ (Original.t (2 ^ 2))} ∧
      (φ (Original.z (2 ^ 2)))⁻¹ * φ (Original.s (2 ^ 2)) * φ (Original.z (2 ^ 2)) =
        φ (Original.t (2 ^ 2)) ∧
      (φ (Original.z (2 ^ 2)))⁻¹ * φ (Original.t (2 ^ 2)) * φ (Original.z (2 ^ 2)) =
        φ (Original.s (2 ^ 2)) := by
  intro φ
  have hφ := wreathModelHom_injective S e
  refine ⟨by rw [← map_mul, ← map_mul, s_mul_t], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective _ hφ, Original.orderOf_s]
    norm_num
  · rw [orderOf_injective _ hφ, Original.orderOf_t]
    norm_num
  · rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, ← Subgroup.map_inf_eq _ _ _ hφ,
      zpowers_s_inf_zpowers_t, Subgroup.map_bot]
  · rw [orderOf_injective _ hφ, Original.orderOf_z]
  · rw [← Set.image_pair, ← MonoidHom.map_closure, Subgroup.mem_map_iff_mem hφ]
    exact z_notMem_closure _
  · rw [← map_inv, ← map_mul, ← map_mul, z_inv_mul_s_mul_z]
  · rw [← map_inv, ← map_mul, ← map_mul, z_inv_mul_t_mul_z]

theorem commute_x_of_mem (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) {g : G}
    (hg : g ∈ (S : Subgroup G)) :
    g * wreathModelHom S e (Original.x (2 ^ 2)) = wreathModelHom S e (Original.x (2 ^ 2)) * g := by
  rw [← wreathModelHom_range S e] at hg
  obtain ⟨w, rfl⟩ := hg
  have hx : Original.x (2 ^ 2) ∈ Subgroup.center (Wreath (2 ^ 2)) := by
    rw [← Original.Z_eq _ (by norm_num)]
    exact ⟨2 ^ 2 / 2, rfl⟩
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx w)]

theorem card_sylow (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ 2)) : Nat.card (S : Subgroup G) = 32 := by
  rw [Nat.card_congr e.toEquiv, card_wreath]
  norm_num

theorem ncard_involutions_centralizer_of_valency
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6)
    {x : G} (hx : orderOf x = 2) :
    {g : G | g ∈ Subgroup.centralizer {x} ∧ orderOf g = 2}.ncard = 7 := by
  have hset : {g : G | g ∈ Subgroup.centralizer {x} ∧ orderOf g = 2} =
      insert x (Subtype.val '' (involutionGraph G).neighborSet ⟨x, hx⟩) := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image, SimpleGraph.mem_neighborSet]
    constructor
    · rintro ⟨hgc, hg2⟩
      by_cases hgx : g = x
      · exact Or.inl hgx
      · refine Or.inr ⟨⟨g, hg2⟩, adj_iff_ne_and_commute.mpr ⟨fun h => hgx ?_, ?_⟩, rfl⟩
        · exact (congrArg Subtype.val h).symm
        · exact (Subgroup.mem_centralizer_singleton_iff.mp hgc).symm
    · rintro (rfl | ⟨u, hu, rfl⟩)
      · exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hx⟩
      · exact ⟨mem_centralizer_of_adj hu, u.2⟩
  have hnot : x ∉ Subtype.val '' (involutionGraph G).neighborSet ⟨x, hx⟩ := by
    rintro ⟨u, hu, hux⟩
    exact coe_ne_of_adj hu hux.symm
  have hfin : (Subtype.val '' (involutionGraph G).neighborSet ⟨x, hx⟩).Finite := by
    refine Set.finite_of_ncard_pos ?_
    rw [Set.ncard_image_of_injective _ Subtype.val_injective, hval]
    norm_num
  rw [hset, Set.ncard_insert_of_notMem hnot hfin,
    Set.ncard_image_of_injective _ Subtype.val_injective, hval]

theorem localData [Finite G] [Finite (Wreath (2 ^ 2))]
    (hconj : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ 2))
    (hval : ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6) :
    InvolutionProductLaw G ∧
      ∀ z : {g : G // orderOf g = 2}, ((involutionGraph G).neighborSet z).ncard = 6 := by
  obtain ⟨hst, hs, ht, hinter, hw, hwout, hsw, htw⟩ := wreathModelHom_generators S e
  have hx2 : orderOf ((wreathModelHom S e (Original.s (2 ^ 2)) *
      wreathModelHom S e (Original.t (2 ^ 2))) ^ 2) = 2 := by
    rw [← map_mul, ← map_pow, ← x_eq_sq, orderOf_injective _ (wreathModelHom_injective S e)]
    exact (wreath_center_involution_and_quaternion_coordinates 2 le_rfl).involution_orders.1
  exact localData_of_wreath hconj hst hs ht hinter hw hwout hsw htw
    (ncard_involutions_centralizer_of_valency hval hx2)

end CFSG.Wreathed.FourPointInvolutionHexagon
