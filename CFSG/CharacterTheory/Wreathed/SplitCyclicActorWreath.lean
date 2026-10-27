module

public import CFSG.CharacterTheory.Wreathed.SplitCyclicActorSupport
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.FullSylowCoveringObstruction
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.Wreathed.SplitCyclicActor

open scoped Pointwise

universe u

variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
theorem commutator_map_normal (K : Subgroup H) [K.Normal] :
    ((commutator K).map K.subtype).Normal := by
  have h := CFSG.SignalizerFunctor.Helpers.characteristic_subgroup_map_normalized ⊤ K
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]) (commutator K)
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr h)

theorem split_actor_of_full_wreath (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 H) (e : S ≃* Wreath (2 ^ n)) (K A : Subgroup H) [K.Normal]
    (hAc : IsCyclic A) (hAcard : Nat.card A = 2 ^ n)
    (hKA : K ⊔ A = ⊤) (hKAbot : K ⊓ A = ⊥) (hAB : A ≤ modelBase S e)
    (hKindex : K.index = 2 ^ n)
    (hSK : Nat.card ((S : Subgroup H) ⊓ K : Subgroup H) = 2 * 2 ^ n) :
    (∃ N : Subgroup H, N.Normal ∧ Odd (Nat.card N) ∧ ∃ k : ℕ, N.index = 2 ^ k) ∨
    ((∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* Original.Y (2 ^ n)) ∧
        Nat.card P = 2 * 2 ^ n) ∧
      (¬ ∃ K₀ : Subgroup K, K₀.Normal ∧ K₀.index = 2) ∧
      ∀ i : K, orderOf i = 2 → CFSG.oddCore K ⊔ Subgroup.centralizer ({i} : Set K) = ⊤) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstr := wreath_center_involution_and_quaternion_coordinates n hn
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := A)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val h
  have hcommK : commutator H ≤ K := commutator_le_of_sup_eq_top K A hAcomm hKA
  have hb2 : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2 := by
    rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with h | h
    · exact h
    · exfalso
      have hle := FullSylowCoveringObstruction.modelBase_le_commutator_of_sym3 n (by omega) S e h
      have hAK : A ≤ K := hAB.trans (hle.trans hcommK)
      have hAbot : A = ⊥ := by
        rw [← hKAbot]
        exact (inf_eq_right.mpr hAK).symm
      rw [hAbot, Subgroup.card_bot] at hAcard
      have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      omega
  rcases modelVNormalizerQuotient_alternatives n hn S e with hv2 | hv6
  ·
    left
    have hFB := model_base_contains_focal_of_v_order_two n hn S e hv2
    have hFY := modelY_contains_focal_of_base_order_two n hn S e hb2
    have hBY : modelBase S e ⊓ modelY S e =
        Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
      rw [modelBase, modelY, ← Subgroup.map_inf_eq _ _ _ (wreathModelHom_injective S e),
        base_inf_quaternion_eq_zpowers n hn, MonoidHom.map_zpowers]
    have hFcyc : IsCyclic (S : Subgroup H).focalSubgroup := by
      have hle : (S : Subgroup H).focalSubgroup ≤
          Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) :=
        hBY ▸ le_inf hFB hFY
      exact Subgroup.isCyclic_of_le hle
    obtain ⟨hDn, hDidx, hDinf, -⟩ := BrauerWong.transferFocal_ker_spec S
    have := hDn
    obtain ⟨Q, hQ⟩ := CFSG.Glauberman.sylow_inf_normal S (N := (S : Subgroup H).transferFocal.ker)
    have hQcyc : IsCyclic Q := by
      have e1 : (Q : Subgroup (S : Subgroup H).transferFocal.ker) ≃*
          (S : Subgroup H).focalSubgroup :=
        ((MulEquiv.subgroupCongr hQ).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
          (MulEquiv.subgroupCongr hDinf)
      exact e1.isCyclic.mpr hFcyc
    exact normal_two_complement_of_normal_cyclic_sylow _ hDidx Q hQcyc
  · right
    have hF := BrauerWong.focal_eq_modelY_of_base_order_two n hn S e hb2 hv6
    have hYK : modelY S e ≤ K := hF ▸ ((S : Subgroup H).focalSubgroup_le_commutator.trans hcommK)
    have hYS : modelY S e ≤ (S : Subgroup H) := modelY_le_sylow S e
    have hYcard : Nat.card (modelY S e) = 2 * 2 ^ n := by
      rw [BrauerWong.modelY_card n hn S e, pow_succ, mul_comm]
    have hSKY : (S : Subgroup H) ⊓ K = modelY S e :=
      (Subgroup.eq_of_le_of_card_ge (le_inf hYS hYK) (by rw [hSK, hYcard])).symm
    obtain ⟨Q₀, hQ₀⟩ := CFSG.Glauberman.sylow_inf_normal S (N := K)
    let f₀ : (Q₀ : Subgroup K) ≃* Original.Y (2 ^ n) :=
      ((MulEquiv.subgroupCongr hQ₀).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)).trans
        ((MulEquiv.subgroupCongr hSKY).trans
          ((Original.Y (2 ^ n)).equivMapOfInjective _ (wreathModelHom_injective S e)).symm)
    have hsyl : ∀ P : Sylow 2 K, Nonempty ((P : Subgroup K) ≃* Original.Y (2 ^ n)) ∧
        Nat.card P = 2 * 2 ^ n := by
      intro P
      refine ⟨⟨(Sylow.equiv P Q₀).trans f₀⟩, ?_⟩
      rw [Nat.card_congr ((Sylow.equiv P Q₀).trans f₀).toEquiv, hstr.quaternion_card]
    refine ⟨hsyl, ?_, ?_⟩
    ·
      rintro ⟨K₀, -, hK₀⟩
      obtain ⟨g, -, hodd, -, -, -, hrel, -, -⟩ :=
        modelVNormalizer_exists_quaternion_commutator_actor n hn S e hv6
      have hgK : (g : H) ∈ K := BrauerWong.mem_of_odd_of_two_power_index K ⟨n, hKindex⟩ g
        (by rwa [Subgroup.orderOf_coe])
      have hQK : modelQ S e ≤ K := (modelQ_le_modelY n S e).trans hYK
      have hQK' := hrel K hQK hgK
      have hK'n := commutator_map_normal K
      have hdQ : wreathModelHom S e (Original.d (2 ^ n)) ∈ modelQ S e :=
        Subgroup.mem_map_of_mem _
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      have hYK' : modelY S e ≤ (commutator K).map K.subtype := by
        rw [modelY, Subgroup.map_le_iff_le_comap, ← hstr.normal_closure]
        have := hK'n.comap (wreathModelHom S e)
        exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (hQK' hdQ))
      have hcK₀ : commutator K ≤ K₀ := BrauerWong.commutator_le_of_index_two hK₀
      have hQ₀K₀ : (Q₀ : Subgroup K) ≤ K₀ := by
        rw [hQ₀, hSKY]
        intro x hx
        apply hcK₀
        obtain ⟨y, hy, hyx⟩ := hYK' hx
        have hyx' : y = x := Subtype.ext hyx
        rwa [← hyx']
      have hdvd := Subgroup.index_dvd_of_le hQ₀K₀
      rw [hK₀] at hdvd
      exact Q₀.not_dvd_index hdvd
    ·
      intro i hi
      have hip : IsPGroup 2 (Subgroup.zpowers i) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hi, pow_one])
      obtain ⟨P, hP⟩ := hip.exists_le_sylow
      obtain ⟨⟨fP⟩, -⟩ := hsyl P
      refine oddCore_sup_centralizer_eq_top_of_unique_involution P ?_ i
        (hP (Subgroup.mem_zpowers i)) hi
      intro a ha b hb hao hbo
      have h := unique_involution_of_equiv_quaternion n hn fP ⟨a, ha⟩ ⟨b, hb⟩
        (by rw [Subgroup.orderOf_mk]; exact hao) (by rw [Subgroup.orderOf_mk]; exact hbo)
      exact congrArg Subtype.val h

end CFSG.Wreathed.SplitCyclicActor
