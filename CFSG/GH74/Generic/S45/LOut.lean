module

public import CFSG.GH74.Generic.S45.PumpLeaves
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.GH74.KGroups.CoverEven
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.PairJ2Pairs
import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear

public section

namespace CFSG.GH74.Generic.S45

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Subgroup
open scoped commutatorElement

section Linear

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem commutator_mem_linearAutGroup (hn : 3 ≤ n) (α β : MulAut (projectiveSL n F)) :
    ⁅α, β⁆ ∈ linearAutGroup n F := by
  rw [commutatorElement_def]
  exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.commutator_mem_linearAutGroup hn α β

omit [Finite F] in
theorem card_map_linearAutGroup_dvd :
    Nat.card ((linearAutGroup n F).map (QuotientGroup.mk' (inner (projectiveSL n F)))) ∣
      Nat.card Fˣ := by
  let π := QuotientGroup.mk' (inner (projectiveSL n F))
  let ψ : GL (Fin n) F →* Outer (projectiveSL n F) := π.comp (conjAut n F)
  have hψ : (linearAutGroup n F).map π = ψ.range := by
    rw [linearAutGroup_eq_range, MonoidHom.range_comp]
  have hker : Matrix.GeneralLinearGroup.det.ker ≤ ψ.ker := by
    intro A hA
    rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hA
    obtain ⟨g, rfl⟩ := hA
    rw [MonoidHom.mem_ker]
    show π (conjAut n F (Matrix.SpecialLinearGroup.toGL g)) = 1
    rw [conjAut_toGL]
    exact (QuotientGroup.eq_one_iff _).2 ⟨LinearFlag.proj n F g, rfl⟩
  rw [hψ, ← Subgroup.index_ker]
  refine (Subgroup.index_dvd_of_le hker).trans ?_
  rw [Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card _

theorem card_commutator_outer_projectiveSL_dvd (hn : 3 ≤ n) :
    Nat.card (commutator (Outer (projectiveSL n F))) ∣ Nat.card Fˣ := by
  let π := QuotientGroup.mk' (inner (projectiveSL n F))
  have hle : commutator (Outer (projectiveSL n F)) ≤ (linearAutGroup n F).map π := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective _ y
    refine ⟨⁅α, β⁆, commutator_mem_linearAutGroup hn α β, ?_⟩
    exact map_commutatorElement π α β
  exact (Subgroup.card_dvd_of_le hle).trans card_map_linearAutGroup_dvd

end Linear

section Abstract

open CFSG.ComponentClassification.OuterAutomorphisms

theorem card_commutator_dvd_of_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) : Nat.card (commutator A) ∣ Nat.card (commutator B) := by
  have h1 : (commutator A).map f ≤ commutator B := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rw [← Subgroup.card_map_of_injective hf (K := commutator A)]
  exact Subgroup.card_dvd_of_le h1

theorem odd_card_commutator_outer_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Odd (Nat.card (commutator (Outer B)))) : Odd (Nat.card (commutator (Outer A))) :=
  h.of_dvd_nat (card_commutator_dvd_of_injective (equivalence e).toMonoidHom
    (equivalence e).injective)

theorem odd_card_commutator_outer_of_perfect {K : Type} [Group K] (hK : Group.IsPerfect K)
    (h : Odd (Nat.card (commutator (Outer (K ⧸ Subgroup.center K))))) :
    Odd (Nat.card (commutator (Outer K))) :=
  h.of_dvd_nat (card_commutator_dvd_of_injective (centerQuotientOuterHom K)
    (centerQuotient_outer_injective K))

theorem odd_card_commutator_of_isMulCommutative {X : Type*} [Group X] (h : IsMulCommutative X) :
    Odd (Nat.card (commutator X)) := by
  rw [(commutator_eq_bot_iff X).2 h, Subgroup.card_bot]
  exact odd_one

theorem isMulCommutative_outer_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsMulCommutative (Outer B)) : IsMulCommutative (Outer A) :=
  ⟨⟨fun a b => (equivalence e).injective (by
    rw [map_mul, map_mul]
    exact h.is_comm.comm _ _)⟩⟩

end Abstract

section Cases

open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem odd_card_commutator_outer_L34 {Q : Type} [Group Q] (h : LieModel Q .PSL 3 2 2) :
    Odd (Nat.card (commutator (Outer Q))) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have h1 := card_commutator_outer_projectiveSL_dvd (F := F) (n := 3) le_rfl
  have h2 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]; norm_num
  exact odd_card_commutator_outer_of_equiv e (Odd.of_dvd_nat (by rw [h2]; decide) h1)

theorem odd_card_commutator_outer_U34 {Q : Type} [Group Q] (h : LieModel Q .PSU 3 2 2) :
    Odd (Nat.card (commutator (Outer Q))) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psu3_of_lieModel_even (f := 2) le_rfl h
  have hmodel : CFSG.Theory.Comparator.PSU3Model 2 = CFSG.Open.PSU3 2 2 := by
    simp only [CFSG.Theory.Comparator.PSU3Model, CFSG.Open.PSU3]
  have hB := BenderType.unitary 2 le_rfl (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  obtain ⟨Dd, hDn, -, hDc, hq, -⟩ := hB.outer_unitary
  have hle : commutator (Outer Q) ≤ Dd := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hcomm : IsMulCommutative (Outer Q ⧸ Dd) := hq.isMulCommutative
    have h1 : (QuotientGroup.mk' Dd) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.2 (hcomm.is_comm.comm _ _)
    exact (QuotientGroup.eq_one_iff _).1 h1
  refine Odd.of_dvd_nat (n := Nat.gcd 3 (2 ^ 2 + 1)) (by decide) ?_
  rw [← hDc]
  exact Subgroup.card_dvd_of_le hle

theorem odd_card_commutator_outer_M12
    {Q : Type} [Group Q] (h : NativeSporadic.IsSporadic Q .M12) :
    Odd (Nat.card (commutator (Outer Q))) := by
  obtain ⟨e⟩ := h
  let e' : Q ≃* NativeSporadic.M12 := e
  exact odd_card_commutator_of_isMulCommutative
    (isMulCommutative_outer_of_equiv e' CFSG.Sporadic.Schreier.at_m12_schreier.2.1)

theorem odd_card_commutator_outer_J2
    {Q : Type} [Group Q] (h : NativeSporadic.IsSporadic Q .J2) :
    Odd (Nat.card (commutator (Outer Q))) := by
  obtain ⟨e⟩ := h
  let e' : Q ≃* NativeSporadic.J2 := e
  exact odd_card_commutator_of_isMulCommutative
    (isMulCommutative_outer_of_equiv e' CFSG.Sporadic.Schreier.AT_J2_Schreier.2.1)

theorem odd_card_commutator_outer_L216 {Q : Type} [Group Q] (h : LieModel Q .PSL 2 2 4) :
    Odd (Nat.card (commutator (Outer Q))) := by
  obtain ⟨e⟩ := CFSG.GH74.KGroups.equiv_psl2_of_lieModel_even (f := 4) (by norm_num) h
  have hB := BenderType.linear 4 (by norm_num) e
  exact odd_card_commutator_of_isMulCommutative hB.outer_linear.1.isMulCommutative

theorem b_III11_2_1 :
    B_III11_2_1 := by
  intro K _ _ hK hout
  have hperf : Group.IsPerfect K := hK.1.1
  rcases hout with h | h | h | h | h
  · exact odd_card_commutator_outer_of_perfect hperf (odd_card_commutator_outer_L34 h)
  · exact odd_card_commutator_outer_of_perfect hperf (odd_card_commutator_outer_U34 h)
  · exact odd_card_commutator_outer_of_perfect hperf (odd_card_commutator_outer_M12 h)
  · exact odd_card_commutator_outer_L216 h
  · exact odd_card_commutator_outer_J2 h

end Cases

end CFSG.GH74.Generic.S45
