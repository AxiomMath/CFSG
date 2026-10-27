module

public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.CharacterTheory.Semidihedral.DihedralNormalIndex
public import CFSG.CharacterTheory.Semidihedral.QuaternionDoubleCoverUniqueness

public section

namespace CFSG.Semidihedral.CharacteristicSL2Layer

open CFSG.Open

universe u v

variable {H : Type u} {G : Type v} [Group H] [Group G]

theorem twoRank_le_one_of_unique_involution [Finite H]
    (z : H) (hz : orderOf z = 2)
    (hunique : ∀ x : H, orderOf x = 2 → x = z) : twoRank H ≤ 1 := by
  apply csSup_le'
  rintro rank ⟨E, _, hE, hcard⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    omega
  have hsub : (E : Set H) ⊆ {1, z} := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    · have ho : orderOf x = 2 := orderOf_eq_prime (hE.2 x hx) hx1
      simp [hunique x ho]
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_pair hz1.symm] at hle
  change Nat.card E ≤ 2 at hle
  rw [hcard] at hle
  by_contra hn
  have hlarge : 2 ^ 2 ≤ 2 ^ rank := pow_le_pow_right' (by omega) (by omega)
  norm_num at hlarge
  omega

theorem isCyclic_map (pi : H →* G) (S : Subgroup H) (hS : IsCyclic S) :
    IsCyclic (S.map pi) := by
  let : IsCyclic S := hS
  let f : S →* S.map pi :=
    (pi.comp S.subtype).codRestrict (S.map pi)
      (fun x => Subgroup.mem_map_of_mem pi x.property)
  apply isCyclic_of_surjective f
  intro y
  obtain ⟨x, hx, hxy⟩ := y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

theorem sylow_quaternion_of_unique_involution [Finite H] [Finite G]
    (z : H) (hz : orderOf z = 2)
    (hunique : ∀ x : H, orderOf x = 2 → x = z)
    (pi : H →* G) (hpi : Function.Surjective pi)
    (hnc : ∀ P : Sylow 2 G, ¬ IsCyclic P) (S : Sylow 2 H) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (n - 2))) := by
  have hrank := twoRank_le_one_of_unique_involution z hz hunique
  have hSr : twoRank S ≤ 1 :=
    (CFSG.TwoRankLowerBound.Helpers.twoRank_subgroup_le (S : Subgroup H)).trans hrank
  obtain hcyc | hquat := CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion
    S S.isPGroup' hSr
  · have hmap := isCyclic_map pi (S : Subgroup H) hcyc
    have himage : IsCyclic (S.mapSurjective hpi) := by
      change IsCyclic ↥((S : Subgroup H).map pi)
      exact hmap
    exact False.elim (hnc (S.mapSurjective hpi) himage)
  · exact hquat

theorem subgroup_unique_involution (T : Subgroup H)
    (z : H) (hz : z ∈ T) (hunique : ∀ x : H, orderOf x = 2 → x = z) :
    ∀ x : T, orderOf x = 2 → x = (⟨z, hz⟩ : T) := by
  intro x hx
  apply Subtype.ext
  exact hunique x ((Subgroup.orderOf_coe x).trans hx)

theorem preimageProjection_kernel_zpowers (z : H) (pi : H →* G)
    (hker : pi.ker = Subgroup.zpowers z) (L : Subgroup G) :
    (QuaternionDoubleCoverUniqueness.preimageProjection pi L).ker =
      Subgroup.zpowers
        (⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
          z pi hker L⟩ : L.comap pi) := by
  apply Subgroup.map_injective (L.comap pi).subtype_injective
  rw [QuaternionDoubleCoverUniqueness.preimageProjection_ker,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (L.ker_le_comap pi),
    MonoidHom.map_zpowers]
  exact hker

theorem preimage_unique_involution (z : H) (pi : H →* G)
    (hker : pi.ker = Subgroup.zpowers z) (L J : Subgroup G) (hLJ : L ≤ J)
    (hunique : ∀ x : J.comap pi, orderOf x = 2 → (x : H) = z) :
    ∀ x : L.comap pi, orderOf x = 2 →
      x = (⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage
        z pi hker L⟩ : L.comap pi) := by
  intro x hx
  let y : J.comap pi := ⟨x, hLJ x.property⟩
  have hy : orderOf y = 2 := by
    rw [← Subgroup.orderOf_coe y, Subgroup.orderOf_coe x]
    exact hx
  exact Subtype.ext (hunique y hy)

theorem original_preimage_sylow_quaternion [Finite H] [Finite G]
    (z : H) (hz : orderOf z = 2) (pi : H →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (L J : Subgroup G) (hLJ : L ≤ J)
    (hunique : ∀ x : J.comap pi, orderOf x = 2 → (x : H) = z)
    (hnc : ∀ P : Sylow 2 L, ¬ IsCyclic P) (S : Sylow 2 (L.comap pi)) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty (S ≃* QuaternionGroup (2 ^ (n - 2))) := by
  let zL : L.comap pi :=
    ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage z pi hker L⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  apply sylow_quaternion_of_unique_involution zL hzL
    (preimage_unique_involution z pi hker L J hLJ hunique)
    (QuaternionDoubleCoverUniqueness.preimageProjection pi L)
    (QuaternionDoubleCoverUniqueness.preimageProjection_surjective pi hpi L) hnc S

theorem quotient_layer_sylow_card [Finite G]
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (U : Sylow 2 L) (hUnc : ¬ IsCyclic U) : Nat.card U = 2 ^ (k - 1) := by
  obtain ⟨hk3, _, _, _, ⟨eP⟩, _, _⟩ :=
    DihedralNormalIndex.noncyclic_normal_dihedral_fills_index_two
      k hk S eS L hLnormal J hJindex hLJ U hUnc
  let : L.Normal := hLnormal
  obtain ⟨V, hV⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 L S
  have eV : V ≃* ↥((S : Subgroup G) ⊓ L) := by
    rw [hV, ← Subgroup.inf_subgroupOf_right (S : Subgroup G) L]
    exact Subgroup.subgroupOfEquivOfLe inf_le_right
  rw [Nat.card_congr ((Sylow.equiv U V).trans eV).toEquiv,
    Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hsub : k - 1 = (k - 2) + 1 := by omega
  rw [hsub, pow_succ]
  omega

theorem original_layer_sylow_card [Finite H] [Finite G]
    (z : H) (hz : orderOf z = 2) (pi : H →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (U : Sylow 2 L) (hUnc : ¬ IsCyclic U)
    (V : Sylow 2 (L.comap pi)) : Nat.card V = 2 ^ k := by
  let zL : L.comap pi :=
    ⟨z, QuaternionDoubleCoverUniqueness.central_involution_mem_preimage z pi hker L⟩
  have hzL : orderOf zL = 2 := (Subgroup.orderOf_coe zL).symm.trans hz
  let q := QuaternionDoubleCoverUniqueness.preimageProjection pi L
  have hq := QuaternionDoubleCoverUniqueness.preimageProjection_surjective pi hpi L
  have hqker : q.ker = Subgroup.zpowers zL := preimageProjection_kernel_zpowers z pi hker L
  let W := QuaternionDoubleCoverUniqueness.preimageSylow zL hzL q hq hqker U
  rw [Nat.card_congr (Sylow.equiv V W).toEquiv]
  change Nat.card ((U : Subgroup L).comap q) = 2 ^ k
  rw [← QuaternionDoubleCoverUniqueness.two_mul_card_preimage zL hzL q hq hqker,
    quotient_layer_sylow_card k hk S eS L hLnormal J hJindex hLJ U hUnc]
  calc
    2 * 2 ^ (k - 1) = 2 ^ ((k - 1) + 1) := by rw [pow_succ]; omega
    _ = 2 ^ k := by congr 1; omega

theorem original_layer_two_part [Finite H] [Finite G]
    (z : H) (hz : orderOf z = 2) (pi : H →* G) (hpi : Function.Surjective pi)
    (hker : pi.ker = Subgroup.zpowers z)
    (k : ℕ) (hk : 2 ≤ k)
    (S : Sylow 2 G) (eS : S ≃* DihedralGroup (2 ^ (k - 1)))
    (L : Subgroup G) (hLnormal : L.Normal)
    (J : Subgroup G) (hJindex : J.index = 2) (hLJ : L ≤ J)
    (U : Sylow 2 L) (hUnc : ¬ IsCyclic U) :
    (Nat.card (L.comap pi)).factorization 2 = k := by
  let V : Sylow 2 (L.comap pi) := Sylow.nonempty.some
  apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
  exact (Sylow.card_eq_multiplicity V).symm.trans
    (original_layer_sylow_card z hz pi hpi hker k hk S eS L hLnormal J hJindex hLJ U hUnc V)

theorem original_layer_field_card_and_two_part [Finite H]
    {F : Type v} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (L : Subgroup H)
    (eta : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (k : ℕ) (hLtwo : (Nat.card L).factorization 2 = k) :
    Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) ∧
      (Nat.card F ^ 2 - 1).factorization 2 = k ∧
      2 ^ (Nat.card F ^ 2 - 1).factorization 2 = 2 ^ k := by
  have hcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) :=
    (Nat.card_congr eta.toEquiv).trans (CFSG.GorensteinWalter.sl2_card_formula F)
  have hnonzero : Nat.card F ^ 2 - 1 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcard
    exact Nat.card_pos.ne' hcard
  have hfactor : (Nat.card F ^ 2 - 1).factorization 2 = k := by
    rw [hcard, Nat.factorization_mul Nat.card_pos.ne' hnonzero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, zero_add] at hLtwo
    exact hLtwo
  exact ⟨hcard, hfactor, by rw [hfactor]⟩

end CFSG.Semidihedral.CharacteristicSL2Layer
