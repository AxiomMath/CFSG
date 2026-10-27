module

public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBSmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr quasisimple_subnormal_subgroups
  p_component_isomorphism_transport)

theorem projectiveSpecialLinear_two_nonabelian (K : Type) [Field K] [Finite K]
    (h2 : Nat.card K ≠ 2) (h3 : Nat.card K ≠ 3) :
    ∃ x y : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, x * y ≠ y * x := by
  have hSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 K le_rfl (Or.inr h2) (Or.inr h3)
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr h2) (Or.inr h3)
  by_contra hcomm
  push Not at hcomm
  have htop : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = ⊤ := by
    have h := congrArg
      (Subgroup.map (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))))
      hSL.commutator_eq_top
    rwa [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), ← commutator_def] at h
  have hbot : commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hcomm y x
  exact (bot_ne_top : (⊥ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) ≠ ⊤)
    (hbot.symm.trans htop)

theorem pComponent_quasisimple_of_isSimpleGroup {S : Type*} [Group S] [Finite S]
    [IsSimpleGroup S] (hnc : ∃ x y : S, x * y ≠ y * x) {p : ℕ} (J : Subgroup S)
    (hJ : CFSG.IsPComponent p J) : CFSG.IsQuasisimple J := by
  have hquasi := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  have hZ : Subgroup.center S = ⊥ := by
    rcases (Subgroup.center S).normal_of_characteristic.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnc
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have hJnt := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hJ
  obtain ⟨-, -, hJsub, -, -⟩ := hJ
  rcases quasisimple_subnormal_subgroups hquasi hJsub with h | h
  · subst h
    exact (isQuasisimple_congr Subgroup.topEquiv).2 hquasi
  · rw [hZ] at h
    exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hJnt
    apply hab
    have ha' := le_bot_iff.1 h ▸ ha
    have hb' := le_bot_iff.1 h ▸ hb
    rw [Subgroup.mem_bot] at ha' hb'
    exact Subtype.ext (ha'.trans hb'.symm)

theorem smallReeH_neg_one (a : ℕ) (K : Type) [Field K] :
    smallReeH a K (-1) =
      torusElt Tag.G2 K ⟨0, by decide⟩ (-1) * torusElt Tag.G2 K ⟨1, by decide⟩ (-1) := by
  change smallReeTorusElt a K (-1) = _
  rw [smallReeTorusElt, (Odd.pow (by decide : Odd 3)).neg_one_pow]

theorem isSolvable_of_isCyclic {G : Type*} [Group G] [IsCyclic G] : Group.IsSolvable G :=
  Group.isSolvable_of_comm fun x y => (IsCyclic.isMulCommutative (α := G)).is_comm.comm x y

theorem small_Ree_torus_involution_centralizer_p_components (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    smallReeH a K (-1) =
      torusElt Tag.G2 K ⟨0, by decide⟩ (-1) * torusElt Tag.G2 K ⟨1, by decide⟩ (-1) ∧
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup (smallReeInvCentralizer a K),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (a = 0 → Group.IsSolvable (smallReeInvCentralizer a K) ∧
      ∀ p : ℕ, p.Prime → ∀ L : Subgroup (smallReeInvCentralizer a K),
        ¬ CFSG.IsPComponent p L) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  have hzero : a = 0 → Group.IsSolvable (smallReeInvCentralizer a K) ∧
      ∀ p : ℕ, p.Prime → ∀ L : Subgroup (smallReeInvCentralizer a K),
        ¬ CFSG.IsPComponent p L := by
    rintro rfl
    have hcard := (small_Ree_torus_involution_centralizer_cells 0 K hK w₀ hw₀).2.2.2.2.2.2.2.1
    have hsolv : Group.IsSolvable (smallReeInvCentralizer 0 K) := by
      apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      rw [hcard, show 3 ^ (2 * 0 + 1) * ((3 ^ (2 * 0 + 1)) ^ 2 - 1) = 2 ^ 3 * 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_three.primeFactors]
      exact (Finset.card_union_le _ _).trans (by simp)
    refine ⟨hsolv, fun p hp L hL => ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have : Group.IsPerfect L := CatalogueBHeldSmallCore.pComponent_perfect p L hL
    have : Nontrivial L :=
      CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hL
    exact Group.IsPerfect.not_isSolvable L inferInstance
  refine ⟨smallReeH_neg_one a K, ?_, hzero⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact fun p hp L hL => absurd hL ((hzero rfl).2 p hp L)
  obtain ⟨ψ, hψC, -, -, -, -, -, ⟨hsup, -, hcent⟩, e, -⟩ :=
    small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  set C := smallReeInvCentralizer a K with hCdef
  set t := smallReeH a K (-1) with htdef
  have hLC : ψ.range ≤ C := by
    rintro _ ⟨g, rfl⟩
    exact hψC g
  have htC : t ∈ C := hsup ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  set N := ψ.range.subgroupOf C with hNdef
  have hNn : N.Normal := by
    rw [hNdef, Subgroup.normal_subgroupOf_iff_le_normalizer hLC, ← hsup]
    exact sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hT : Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N = ⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hNdef, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hLC, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' N).comp (Subgroup.zpowers (⟨t, htC⟩ : C)).subtype) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hc : c ∈ (Subgroup.zpowers (⟨t, htC⟩ : C) ⊔ N : Subgroup C) := hT ▸ Subgroup.mem_top c
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hc
    obtain ⟨x, hx, n, hn, rfl⟩ := hc
    refine ⟨⟨x, hx⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    change QuotientGroup.mk' N x = QuotientGroup.mk' N (x * n)
    rw [map_mul, hn1, mul_one]
  have : IsCyclic (C ⧸ N) := isCyclic_of_surjective _ hsurj
  have : Group.IsSolvable (C ⧸ N) := isSolvable_of_isCyclic
  have hq27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc 27 = 3 ^ (2 * 1 + 1) := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  let e' : N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hLC).trans e.symm
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CatalogueBGeneralLinear.projectiveSpecialLinear_simple 2 K le_rfl (Or.inr hK2) (Or.inr hK3)
  have : IsSimpleGroup N := e'.isSimpleGroup
  have hnc : ∃ x y : N, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := projectiveSpecialLinear_two_nonabelian K hK2 hK3
    refine ⟨e'.symm x, e'.symm y, fun h => hxy ?_⟩
    simpa using congrArg e' h
  intro p hp L hL
  have : Fact p.Prime := ⟨hp⟩
  exact pComponent_quasisimple_of_normal_solvable_quotient p N
    (fun J hJ => pComponent_quasisimple_of_isSimpleGroup hnc J hJ) L hL

end CFSG.ComponentClassification.CatalogueBSmallRee
