module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSmallReeTorus
public import CFSG.Walter.Ree.Model.Fusion
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Walter.Ree.Model
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.CatalogueBSmallRee

theorem ordProj_two_small_Ree_PSL2 (a : ℕ) :
    ordProj[2] (3 ^ (2 * a + 1) * ((3 ^ (2 * a + 1)) ^ 2 - 1) / 2) = 4 := by
  have hmod : 3 ^ (2 * a + 1) % 8 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  set q := 3 ^ (2 * a + 1) with hq
  set m := q / 8 with hm
  have hqm : q = 8 * m + 3 := by omega
  have hsq : q ^ 2 - 1 = 8 * (8 * m ^ 2 + 6 * m + 1) := by
    rw [hqm]
    have : (8 * m + 3) ^ 2 = 8 * (8 * m ^ 2 + 6 * m + 1) + 1 := by ring
    omega
  have hval : q * (q ^ 2 - 1) / 2 = 4 * ((8 * m + 3) * (8 * m ^ 2 + 6 * m + 1)) := by
    rw [hsq, hqm]
    have : (8 * m + 3) * (8 * (8 * m ^ 2 + 6 * m + 1)) =
        2 * (4 * ((8 * m + 3) * (8 * m ^ 2 + 6 * m + 1))) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  have hodd : Odd ((8 * m + 3) * (8 * m ^ 2 + 6 * m + 1)) :=
    Nat.odd_mul.2 ⟨⟨4 * m + 1, by ring⟩, ⟨4 * m ^ 2 + 3 * m, by ring⟩⟩
  rw [hval, Nat.factorization_mul (by norm_num) (Nat.pos_of_ne_zero (fun h => by
      simp [h] at hodd)).ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.2 hodd)
      (even_iff_two_dvd.2 h)), add_zero,
    show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_two, smul_eq_mul, mul_one]

theorem small_Ree_involution_components_simple_two_part_four
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    {t : ModGL ReeTag.G2.tag K} (ht : t ∈ ReeTag.G2.reeGamma K a) (ht2 : orderOf t = 2)
    {B : Subgroup (ModGL ReeTag.G2.tag K)}
    (hB : CFSG.Assembly.IsComponentOf B
      (ReeTag.G2.reeGamma K a ⊓ Subgroup.centralizer {t})) :
    1 ≤ a ∧ IsSimpleGroup B ∧ (∃ x y : B, x * y ≠ y * x) ∧ ordProj[2] (Nat.card B) = 4 := by
  classical
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set Γ := ReeTag.G2.reeGamma K a with hΓ
  set h := smallReeH a K (-1) with hh
  obtain ⟨g, hgΓ, hgt⟩ :=
    (small_Ree_prime_field_involution_fusion a K hK w₀ hw₀).2.2.2.2.2 t ht ht2
  set C := smallReeInvCentralizer a K with hCdef
  have hCmap : (Γ ⊓ Subgroup.centralizer {t}).map (MulAut.conj g).toMonoidHom = C := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hgΓ), map_centralizer_singleton,
      MulAut.conj_apply, hgt]
    rfl
  set B' := B.map (MulAut.conj g).toMonoidHom with hB'def
  have hB' : CFSG.Assembly.IsComponentOf B' C := hCmap ▸ isComponentOf_map_conj hB g
  let eB : B ≃* B' := B.equivMapOfInjective _ (MulAut.conj g).injective
  suffices H : 1 ≤ a ∧ IsSimpleGroup B' ∧ (∃ x y : B', x * y ≠ y * x) ∧
      ordProj[2] (Nat.card B') = 4 by
    obtain ⟨ha, hs, ⟨x, y, hxy⟩, hcard⟩ := H
    refine ⟨ha, eB.isSimpleGroup, ⟨eB.symm x, eB.symm y, fun hc => hxy ?_⟩, ?_⟩
    · simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eB hc
    · rw [Nat.card_congr eB.toEquiv]
      exact hcard
  have hB'C : B' ≤ C := hB'.1
  set K' := B'.subgroupOf C with hK'def
  have hK' : CFSG.IsComponent K' := (isComponentOf_iff_isComponent_subgroupOf hB'C).1 hB'
  have : Nontrivial K' := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
  have : Group.IsPerfect K' := hK'.1.1
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exfalso
    obtain ⟨-, -, hzero⟩ := small_Ree_torus_involution_centralizer_p_components 0 K hK
    have := (hzero rfl).1
    have : Group.IsSolvable K' := Group.isSolvable_of_isSolvable_injective K'.subtype_injective
    exact Group.IsPerfect.not_isSolvable K' inferInstance
  obtain ⟨ψ, hψC, -, -, -, hψone, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  rw [← hh, ← hCdef] at hsup
  rw [← hh] at hcent
  simp only [← hCdef] at hψC
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    exact hψC x
  have htC : h ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers h)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨h, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨h, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨x, hx, n, hn, rfl⟩ := hc
    refine ⟨⟨x, hx⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change QuotientGroup.mk' N x = QuotientGroup.mk' N (x * n)
    rw [map_mul, hn1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  let e' : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K
      le_rfl (Or.inr hK2) (Or.inr hK3)
  have hNs : IsSimpleGroup N := e'.isSimpleGroup
  have hnc : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := projectiveSpecialLinear_two_nonabelian K hK2 hK3
    refine ⟨e'.symm x, e'.symm y, fun hc => hxy ?_⟩
    simpa using congrArg e' hc
  have hKK : ⁅K', K'⁆ = K' := by
    have hKA := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K').2
      hK'.1
    have h1 := congrArg (Subgroup.map K'.subtype) hKA.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    exact h1
  have hK'N : K' ≤ N := by
    rw [← hKK, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact IsMulCommutative.is_comm.comm _ _
  have hKN : K' = N := by
    refine le_antisymm hK'N ?_
    have hJ := component_overgroup hK' hK'N
    have hquasi := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
    have hZ : Subgroup.center N = ⊥ := by
      rcases (Subgroup.center N).normal_of_characteristic.eq_bot_or_eq_top with hc | hc
      · exact hc
      · exfalso
        obtain ⟨x, y, hxy⟩ := hnc
        exact hxy (Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top y) x)
    have hJnt : Nontrivial (K'.subgroupOf N) := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
    rcases quasisimple_subnormal_subgroups hquasi hJ.2 with hJ1 | hJ1
    · rwa [Subgroup.subgroupOf_eq_top] at hJ1
    · exfalso
      rw [hZ] at hJ1
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩, huv⟩ := hJnt
      apply huv
      have hu' := le_bot_iff.1 hJ1 ▸ hu
      have hv' := le_bot_iff.1 hJ1 ▸ hv
      rw [Subgroup.mem_bot] at hu' hv'
      exact Subtype.ext (hu'.trans hv'.symm)
  let eK : B' ≃* K' := (Subgroup.subgroupOfEquivOfLe hB'C).symm
  let eN : B' ≃* N := eK.trans (MulEquiv.subgroupCongr hKN)
  have hcardN : Nat.card N * 2 = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have h1 : Nat.card N = Nat.card ψ.range :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLC).toEquiv
    have hneg : (-1 : SL2 K) ≠ 1 := by
      intro hc
      have h2 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) hc
      simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
        Matrix.neg_apply, Matrix.one_apply_eq] at h2
      have h3 : (2 : K) = 0 := by linear_combination -h2
      have : ringChar K = 3 := ringChar.eq K 3
      exact absurd (CharP.cast_eq_zero_iff K 3 2 |>.1 (by exact_mod_cast h3)) (by norm_num)
    have hker : Nat.card ψ.ker = 2 := by
      have hset : (ψ.ker : Set (SL2 K)) = {1, -1} := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff,
          Set.mem_singleton_iff, hψone]
      show Nat.card (ψ.ker : Set (SL2 K)) = 2
      rw [Nat.card_coe_set_eq, hset, Set.ncard_pair hneg.symm]
    have h3 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hker, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K] at h3
    rw [h1, mul_comm]
    exact h3
  refine ⟨ha, eN.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eN.symm x, eN.symm y, fun hc => hxy (by
      simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg eN hc)⟩
  · rw [Nat.card_congr eN.toEquiv, show Nat.card N = Nat.card K * (Nat.card K ^ 2 - 1) / 2 by
      omega, hK]
    exact ordProj_two_small_Ree_PSL2 a

end CFSG.LieType.Ree
