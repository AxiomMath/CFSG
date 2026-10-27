module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Top
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Dispatch

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LieType.Chevalley CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks (exists_lift_isComponentOf_centralizer_cases)
open CFSG.HardMathSupport.Lang.Coordinator.D4Bridge (Coord)

section Generic

variable {S : Type} [Group S] [Finite S]

theorem isTypeL2_of_threeComponent {C J : Subgroup S} (hJ : GLAPComponent 3 C J)
    (hJc : CFSG.Open.IsComponentOf J C) {q : ℕ} (hT : IsTypeL2 q (barOf 3 J)) : IsTypeL2 q ↥J := by
  have hbar : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hq : CFSG.IsQuasisimple ↥J :=
    ⟨⟨hJc.2.2.1⟩, hJc.2.2.2, CFSG.HardMathSupport.Dickson.Sec6.I923.exists_not_comm_of_quasisimple
      hJc.2.2⟩
  let π : ↥J →* barOf 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (GLAPPrimeCore.normal 3 ↥J) with h | h
    · exfalso
      have hsub : Subsingleton (barOf 3 J) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        exact QuotientGroup.eq.2 (h ▸ Subgroup.mem_top _)
      have := hbar.2.toNontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne (barOf 3 J ⧸ Subgroup.center (barOf 3 J))
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      exact hab (congrArg _ (Subsingleton.elim a b))
    · exact h
  exact (isTypeL2_congr_of_central ⟨hJc.2.2.1⟩ π hπ hker).2 hT

theorem map_centralizer_singleton {T : Type} [Group T] (e : S ≃* T) (g : S) :
    (Subgroup.centralizer ({g} : Set S)).map (e : S →* T) =
      Subgroup.centralizer ({e g} : Set T) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_coe]
    rw [← map_mul, ← map_mul, hy]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx

end Generic

section Main


theorem d4RootSL2_of_blocks (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (T2 : ∀ (K : Type) [Field K] [Finite K], LeviSelfDual K)
    (T3 : ∀ (K : Type) [Field K] [Finite K], LeviFixed K)
    (T4 : ∀ (K : Type) [Field K] [Finite K], SixNotL2 K) : D4RootSL2 := by
  intro K _ _ hK3 g J q hg hJ hT hq0
  obtain ⟨q0, hq0, hqq⟩ := hq0
  haveI := CFSG.HardMathSupport.Dickson.Sec6.I923.D4Aux.finite_adjointD4 K
  have hq64 : 64 ≤ q := by
    rw [hqq]
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q0 ^ 3 := Nat.pow_le_pow_left hq0 3
  have hJc := isComponentOf_threeComponent_D4 hK3 hg hJ
  have hJT : IsTypeL2 q ↥J := isTypeL2_of_threeComponent hJ hJc hT
  have ha : orderOf ((eTheta K).symm g) = 3 := by rw [MulEquiv.orderOf_eq]; exact hg
  have hJ'c : CFSG.Open.IsComponentOf (J.map (eTheta K).symm.toMonoidHom)
      (Subgroup.centralizer ({(eTheta K).symm g} : Set (ProjOrthDerived (quadPlus 4 K)))) := by
    have := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (eTheta K).symm hJc
    rw [map_centralizer_singleton] at this
    exact this
  have hJ'T : IsTypeL2 q ↥(J.map (eTheta K).symm.toMonoidHom) :=
    p6_isTypeL2_of_equiv (J.equivMapOfInjective (eTheta K).symm.toMonoidHom
      (eTheta K).symm.injective) hJT
  obtain ⟨x, Rep, -, hx3, hx, hRep, hcent, -⟩ := exists_lift_isComponentOf_centralizer_cases
    (nondegenerate_quadPlus_four K) (regular_quadPlus (K := K) (n := 4) (by norm_num)).2
    Nat.prime_three (by norm_num) (Ne.symm hK3) ha
  rw [hcent] at hJ'c
  obtain ⟨c, hc⟩ := rootSL2_of_component K hO hK3 (T2 K) (T3 K) (T4 K) hx3 hx hRep hJ'c hq64 hJ'T
  refine ⟨c, node0, ?_⟩
  rw [← hc]
  ext z
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · intro hz
    exact ⟨(eTheta K).symm z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw

end Main

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2
