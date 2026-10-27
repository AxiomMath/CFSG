module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OParab
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OCompLevi
public import CFSG.HardMathSupport.Timmesfeld.Proving.ComponentCentralizer
public import CFSG.Quasithin.Background.B15P4Comp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentZ2Alt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
open CFSG.LieType.Steinberg (Sp.x)
open CFSG.RankThree.CentralCover (sl2Upper coe_sl2Upper sl2Upper_add sl2Upper_zero)
open scoped commutatorElement MatrixGroups

theorem isComponentOf_centralizer_map_symm {G H : Type} [Group G] [Group H] {M : Subgroup G}
    (e : H ≃* ↥M) {d : G} (hd : d ∈ M) {Kb : Subgroup G}
    (hK : IsComponentOf Kb (Subgroup.centralizer ({d} : Set G))) (hKM : Kb ≤ M) :
    IsComponentOf ((Kb.subgroupOf M).map e.symm.toMonoidHom)
      (Subgroup.centralizer ({e.symm ⟨d, hd⟩} : Set H)) := by
  have h1 := CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le hK hKM
  have h2 := CFSG.Quasithin.B15P4.isComponentOf_subgroupOf M h1 inf_le_right
  have h3 : (Subgroup.centralizer ({d} : Set G) ⊓ M).subgroupOf M =
      Subgroup.centralizer ({(⟨d, hd⟩ : M)} : Set M) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.1, fun h => ⟨congrArg Subtype.val h, x.2⟩⟩
  rw [h3] at h2
  have h4 := (Y10F.isComponentOf_map_iff (ι := e.symm.toMonoidHom) e.symm.injective).2 h2
  rwa [CFSG.centralizer_singleton_map e.symm] at h4

section Generic


theorem exists_conj_le_parabolicLevi_of_le_normalizer (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] {T : Subgroup ↥(adjointGroup τ K)} (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    {E X : Subgroup ↥(adjointGroup τ K)}
    (hE : E ≤ Subgroup.normalizer (T : Set ↥(adjointGroup τ K)))
    (hX : X ≤ Subgroup.normalizer (T : Set ↥(adjointGroup τ K)))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hEp : IsPGroup p E) :
    ∃ (g : ↥(adjointGroup τ K)) (J : Set (Fin τ.rank)), J ≠ Set.univ ∧
      (E.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype ≤
        parabolicLevi τ K J ∧
      (X.map (MulAut.conj g).toMonoidHom).map (adjointGroup τ K).subtype ≤
        parabolicSubgroup τ K J := by
  obtain ⟨g₁, J, hJ, hN⟩ := exists_conj_normalizer_le_parabolicSubgroup τ hT hT2
  have hE₁ : (E.map (MulAut.conj g₁).toMonoidHom).map (adjointGroup τ K).subtype ≤
      parabolicSubgroup τ K J := le_trans (Subgroup.map_mono (Subgroup.map_mono hE)) hN
  have hX₁ : (X.map (MulAut.conj g₁).toMonoidHom).map (adjointGroup τ K).subtype ≤
      parabolicSubgroup τ K J := le_trans (Subgroup.map_mono (Subgroup.map_mono hX)) hN
  have hE₁p : IsPGroup p ((E.map (MulAut.conj g₁).toMonoidHom).map (adjointGroup τ K).subtype) :=
    (hEp.map _).map _
  obtain ⟨y, hyP, hyL⟩ := exists_conj_le_parabolicLevi τ J hp hp2 hE₁ hE₁p
  have hyC : y ∈ adjointGroup τ K := parabolicSubgroup_le_adjointGroup τ K J hyP
  have hcoe : ∀ u : ↥(adjointGroup τ K),
      (((MulAut.conj (⟨y, hyC⟩ * g₁)) u : ↥(adjointGroup τ K)) : ModGL τ K) =
        y * (((MulAut.conj g₁) u : ↥(adjointGroup τ K)) : ModGL τ K) * y⁻¹ := by
    intro u
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    group
  refine ⟨⟨y, hyC⟩ * g₁, J, hJ, ?_, ?_⟩
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    apply hyL
    refine ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [hcoe]
    rfl
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have h1 : (((MulAut.conj g₁) u : ↥(adjointGroup τ K)) : ModGL τ K) ∈
        parabolicSubgroup τ K J := hX₁ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
    rw [hcoe]
    exact mul_mem (mul_mem hyP h1) (inv_mem hyP)

theorem map_subtype_le_parabolicLevi_of_isComponentOf (τ : Tag) {K : Type} [Field K] [Finite K]
    [CharP K 2] (J : Set (Fin τ.rank)) {d : ↥(adjointGroup τ K)} {Kb : Subgroup ↥(adjointGroup τ K)}
    (hcomp : IsComponentOf Kb (Subgroup.centralizer ({d} : Set ↥(adjointGroup τ K))))
    (hd : (d : ModGL τ K) ∈ parabolicLevi τ K J)
    (hK : Kb.map (adjointGroup τ K).subtype ≤ parabolicSubgroup τ K J) :
    Kb.map (adjointGroup τ K).subtype ≤ parabolicLevi τ K J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨hQP, hQn, -, hLP, -, -, huniq, -, -, -, -, -, hQgrp⟩ :=
    parabolic_root_radical_Levi_factors (τ := τ) (K := K) J
  have hQ2 : IsPGroup 2 (parabolicRadical τ K J) := (hQgrp 2).2.1
  have hQs : Group.IsSolvable ↥(parabolicRadical τ K J) := by
    haveI := hQ2.isNilpotent
    infer_instance
  have h1 := (Y10F.isComponentOf_map_iff (adjointGroup τ K).subtype_injective).2 hcomp
  rw [CFSG.ComponentClassification.CatFC.map_centralizer_subtype_eq_inf] at h1
  have h2 := CFSG.HardMathSupport.Timmesfeld.Proving.isComponentOf_inf_of_le h1 hK
  rw [inf_comm (adjointGroup τ K), inf_assoc,
    inf_eq_right.2 (parabolicSubgroup_le_adjointGroup τ K J)] at h2
  exact le_of_isComponentOf_centralizer_inf hQP hLP hQn huniq hQs hd h2

end Generic

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
