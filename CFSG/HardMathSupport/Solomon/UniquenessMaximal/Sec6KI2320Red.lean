module

public import CFSG.RankThree.PartTwo.KFacts.L34TwoElements
public import CFSG.Quasithin.Background.E6TwentyFiveD
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Out
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.Sporadic.Th.Simple
public import CFSG.Sporadic.ThSchreier.AutCore

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts.L34

local notation "conjAut'" => CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut

theorem exists_conj_le_of_le (p : ℕ) [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (H P A : Subgroup G) (hPH : P ≤ H) (hP : Nat.card P = p ^ (Nat.card G).factorization p)
    (hAH : A ≤ H) (hA : IsPGroup p A) :
    ∃ h ∈ H, A ≤ P.map (MulAut.conj h).toMonoidHom := by
  have hfH : (Nat.card H).factorization p = (Nat.card G).factorization p := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
        (Subgroup.card_subgroup_dvd_card H) p
    · have h1 : p ^ (Nat.card G).factorization p ∣ Nat.card H := by
        rw [← hP]; exact Subgroup.card_dvd_of_le hPH
      exact (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').1 h1
  have hPg : Nat.card (P.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [hfH, ← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv
  let Q : Sylow p H := Sylow.ofCard (P.subgroupOf H) hPg
  have hAg : IsPGroup p (A.subgroupOf H) :=
    hA.of_injective (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hAH).injective
  obtain ⟨R, hR⟩ := hAg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Q R
  refine ⟨h, h.2, fun a ha => ?_⟩
  have haR : (⟨a, hAH ha⟩ : H) ∈ (R : Subgroup H) := hR (Subgroup.mem_subgroupOf.2 ha)
  rw [← hh, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at haR
  obtain ⟨q, hq, hqa⟩ := haR
  refine ⟨(q : G), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.1 hq
  · have := congrArg Subtype.val hqa
    simpa using this

section

variable {k : Type} [Field k]

theorem congr_toMonoidHom_eq_conj {G : Type*} [Group G] (φ : MulAut G) :
    (MulAut.congr φ).toMonoidHom = (MulAut.conj φ).toMonoidHom := by
  ext α x
  simp [MulAut.congr_apply]

theorem exists_conj_pglSylowMax (hk : Nat.card k = 4)
    {A : Subgroup (MulAut (projectiveSL 3 k))} (hA : CFSG.Open.IsElemAbelian 3 A)
    (h9 : Nat.card A = 9)
    (hinn : ¬ A ≤ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    ∃ (u : kˣ) (_ : u ≠ 1) (g : GL (Fin 3) k) (i : Fin 4), (i = 0 ∨ i = 2) ∧
      A = (pglSylowMax u i).map (MulAut.conj (conjAut' 3 k g)).toMonoidHom := by
  have hfin : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (MulAut (projectiveSL 3 k)) = 241920 := card_mulAut hk
  have : Finite (MulAut (projectiveSL 3 k)) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hK : Nat.card k = 2 ^ 2 := by rw [hk]; norm_num
  have hAH : A ≤ linearAutGroup 3 k := fun a ha =>
    CFSG.Quasithin.E6.mem_linearAutGroup_of_card_four hK (a := 1) (by simpa using hA.2 a ha)
  obtain ⟨hS27, hS9, hSmap, -, -, h23, -, -⟩ := pglSylow_transposition hk hu
  have hfac : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 :=
    CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show Nat.card (MulAut (projectiveSL 3 k)) = 3 ^ 3 * 8960 by rw [hcard]; norm_num)
      (by norm_num)
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  obtain ⟨h, hhH, hle⟩ := exists_conj_le_of_le 3 (linearAutGroup 3 k) (pglSylow u) A
    pglSylow_le_linearAutGroup (by rw [hS27, hfac]; norm_num) hAH hAp
  set A' := A.map (MulAut.conj h⁻¹).toMonoidHom with hA'
  have hA'S : A' ≤ pglSylow u := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨s, hs, hsa⟩ := hle ha
    have : (MulAut.conj h⁻¹).toMonoidHom a = s := by
      rw [← hsa]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hs
  have hA'9 : Nat.card A' = 9 := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, h9]
  obtain ⟨i, hi⟩ := hS9 A' hA'S hA'9
  have hAeq : A = A'.map (MulAut.conj h).toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨(MulAut.conj h⁻¹) x, ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have : (MulAut.conj h).toMonoidHom ((MulAut.conj h⁻¹).toMonoidHom a) = a := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [this]
      exact ha
  obtain ⟨g, hg⟩ : h ∈ (conjAut' 3 k).range := by
    rw [← CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.linearAutGroup_three_eq_range (F := k)]
    exact hhH
  have hconj : ∀ (B : Subgroup (MulAut (projectiveSL 3 k))), B.map (MulAut.conj h).toMonoidHom =
      B.map (MulAut.conj (conjAut' 3 k g)).toMonoidHom := fun B => by rw [hg]
  refine ⟨u, hu, ?_⟩
  have hcases : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hcases i with rfl | rfl | rfl | rfl
  · exact ⟨g, 0, Or.inl rfl, by rw [hAeq, hi, hconj]⟩
  · exfalso
    apply hinn
    rw [hAeq, hi]
    rintro _ ⟨a, ha, rfl⟩
    rw [pglSylowMax_one hk hu] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    refine ⟨h p, ?_⟩
    rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv]
    simp [MulAut.conj_apply]
  · exact ⟨g, 2, Or.inr rfl, by rw [hAeq, hi, hconj]⟩
  · refine ⟨g * Matrix.SpecialLinearGroup.toGL (LinearFieldFourKernel.jMat : SpecialLinearGroup (Fin 3) k),
      2, Or.inr rfl, ?_⟩
    have e : conjAut' 3 k (g * Matrix.SpecialLinearGroup.toGL
        (LinearFieldFourKernel.jMat : SpecialLinearGroup (Fin 3) k)) = h * MulAut.conj tInv := by
      rw [map_mul, hg, conjAut_toGL]
      rfl
    rw [e, hAeq, hi, ← h23, Subgroup.map_map]
    congr 1

end

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KI2320
