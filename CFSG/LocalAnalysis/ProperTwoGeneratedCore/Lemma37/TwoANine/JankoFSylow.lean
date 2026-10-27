module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoF
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.ThirdParty.QiuzhenCFSG.BaerSuzuki.FinalTheorem

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup CFSG.DisconnectedInvolutionGraph.Helpers

namespace Janko

variable {G : Type*} [Group G] {z : G} (hz : orderOf z = 2)
  (hH : IsTwoANine (centralizer ({z} : Set G)))
  (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 9))

@[expose] noncomputable def S₁ : Subgroup G :=
  ((default : Sylow 2 (F e)) : Subgroup (F e)).map (F e).subtype

theorem S₁_le : S₁ e ≤ F e :=
  map_subtype_le _

include hH

theorem orderOf_dvd_of_mem_F : ∀ x ∈ F e, orderOf x ∣ 120 := by
  rintro _ ⟨u, hu, rfl⟩
  rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
  have h60 : orderOf (proj e u) ∣ 60 := JankoF.orderOf_dvd_sixty_of_mem_Fbar hu
  have hc : u ^ 60 ∈ center (centralizer ({z} : Set G)) :=
    (proj_eq_one_iff e).mp (by rw [map_pow]; exact orderOf_dvd_iff_pow_eq_one.mp h60)
  apply orderOf_dvd_of_pow_eq_one
  rw [show 120 = 60 * 2 by rfl, pow_mul, hH.sq_eq_one_of_mem_center hc]

include hz in
theorem S₁_quaternion : Nonempty (S₁ e ≃* QuaternionGroup 4) := by
  have := finite_F hH e
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : Nat.card (default : Sylow 2 (F e)) = 2 ^ 4 :=
    JankoPerm.card_sylow_eq default (m := 45) (by rw [card_F hH e]; norm_num)
      (by rw [card_F hH e]; norm_num) (by norm_num)
  have hrank : NoCommutingDistinctInvolutions (default : Sylow 2 (F e)) := by
    intro a b _
    have ha := eq_z_of_mem_F hz hH e _ (a.1 : F e).2
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact a.2)
    have hb := eq_z_of_mem_F hz hH e _ (b.1 : F e).2
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact b.2)
    exact Subtype.ext (Subtype.ext (Subtype.ext (ha.trans hb.symm)))
  rcases rank_one_two_cyclic_or_quaternion (default : Sylow 2 (F e)).isPGroup' hrank with
    hcyc | ⟨n, -, ⟨φ⟩⟩
  · exfalso
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (default : Sylow 2 (F e)))
    have h120 := orderOf_dvd_of_mem_F hH e ((g : F e) : G) (g : F e).2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg, hT] at h120
    norm_num at h120
  · have hcard : 4 * 2 ^ n = 2 ^ 4 := by
      rw [← hT, ← Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hn : n = 2 := by
      have h2 : 2 ^ n = 2 ^ 2 := by omega
      exact Nat.pow_right_injective le_rfl h2
    subst hn
    exact ⟨(Subgroup.equivMapOfInjective _ (F e).subtype (F e).subtype_injective).symm.trans
      φ.symm⟩

include hz in
theorem exists_even_card : ∀ y ∈ F e, orderOf y = 3 →
    ∃ g ∈ F e, Even (Nat.card (closure ({y, g * y * g⁻¹} : Set G))) := by
  intro y hy hy3
  by_contra hcon
  have hcon' : ∀ g ∈ F e, ¬ Even (Nat.card (closure ({y, g * y * g⁻¹} : Set G))) :=
    fun g hg h => hcon ⟨g, hg, h⟩
  have := finite_F hH e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy'3 : orderOf (⟨y, hy⟩ : F e) = 3 := by rw [← Subgroup.orderOf_coe]; exact hy3
  have hall : ∀ g : F e, IsPGroup 3 (closure ({⟨y, hy⟩, g * ⟨y, hy⟩ * g⁻¹} : Set (F e))) := by
    intro g
    have hmap : (closure ({⟨y, hy⟩, g * ⟨y, hy⟩ * g⁻¹} : Set (F e))).map (F e).subtype =
        closure ({y, (g : G) * y * (g : G)⁻¹} : Set G) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    have hcard : Nat.card (closure ({⟨y, hy⟩, g * ⟨y, hy⟩ * g⁻¹} : Set (F e))) =
        Nat.card (closure ({y, (g : G) * y * (g : G)⁻¹} : Set G)) := by
      rw [← hmap, card_map_of_injective (F e).subtype_injective]
    have hodd : Odd (Nat.card (closure ({y, (g : G) * y * (g : G)⁻¹} : Set G))) :=
      Nat.not_even_iff_odd.mp (hcon' g g.2)
    have hXF : closure ({y, (g : G) * y * (g : G)⁻¹} : Set G) ≤ F e := by
      rw [← hmap]
      exact map_subtype_le _
    have h3 : 3 ∣ Nat.card (closure ({⟨y, hy⟩, g * ⟨y, hy⟩ * g⁻¹} : Set (F e))) :=
      hy'3 ▸ Subgroup.orderOf_dvd_natCard _ (subset_closure (Set.mem_insert _ _))
    rw [hcard] at h3
    rcases card_dvd_nine_or_eq_five_of_odd hH e hXF hodd with h | h
    · obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show _ ∣ 3 ^ 2 from h)
      rw [← hcard] at hk
      exact IsPGroup.of_card hk
    · omega
  have hmem : (⟨y, hy⟩ : F e) ∈ CFSG.pCore 3 (F e) := CFSG.BaerSuzuki.baer_suzuki _
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'3, pow_one])) hall
  have hBF : (CFSG.pCore 3 (F e)).map (F e).subtype ≤ F e := map_subtype_le _
  have hFB : F e ≤ normalizer (((CFSG.pCore 3 (F e)).map (F e).subtype : Subgroup G) : Set G) :=
    fun f hf => le_normalizer_map (F e).subtype
      ⟨⟨f, hf⟩, by rw [normalizer_eq_top]; exact mem_top _, rfl⟩
  have hB : (CFSG.pCore 3 (F e)).map (F e).subtype ≠ ⊥ := by
    intro h
    have hyB : y ∈ (CFSG.pCore 3 (F e)).map (F e).subtype := ⟨_, hmem, rfl⟩
    rw [h, mem_bot] at hyB
    rw [hyB, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  have hzB := z_mem_of_normal hz hH e _ hBF hFB hB
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup.map (F e).subtype) ⟨z, hzB⟩
  have hzk : z ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h2 : 2 ∣ 3 ^ k := hz ▸ orderOf_dvd_of_pow_eq_one hzk
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2) (by norm_num)

end Janko

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
