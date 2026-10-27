module

public import CFSG.ClassicalInvolution.Q3.Q3TIYRank1
public import CFSG.ClassicalInvolution.Q3.Q3TIYStmt
public import CFSG.ClassicalInvolution.Q3.Q3NGCount
public import CFSG.ClassicalInvolution.Q3.Q3TIYComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIV

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn)


section Rows

theorem twinRow_admissible3 {t : StatedLieTag} {n : ℕ} (hrow : TwinRow t n) :
    StatedLieAdmissible t n 3 1 := by
  rcases hrow with ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hn⟩ |
    ⟨-, rfl, rfl⟩
  · exact ⟨Nat.prime_three, Nat.one_pos, hn⟩
  · exact ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide, by decide⟩
  · exact ⟨Nat.prime_three, Nat.one_pos, hn, by norm_num⟩
  · exact Q3Z.statedLieAdmissible_psp2
  · exact ⟨Nat.prime_three, Nat.one_pos, hn⟩
  · exact ⟨Nat.prime_three, Nat.one_pos, by norm_num, by decide⟩

theorem twinRow_tag_facts3 {t : StatedLieTag} {n : ℕ} (hrow : TwinRow t n) :
    IsFundTag t ∧ t ≠ .G2 ∧ t ≠ .trialityD4 ∧ t ≠ .twistedE6 ∧ ¬ (t = .PSL ∧ n = 2) := by
  have h := hrow.tag_facts
  rcases hrow with ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, -⟩ |
    ⟨-, rfl, rfl⟩ <;> exact ⟨trivial, h.1, h.2.1, by decide, h.2.2⟩

theorem twinRow_of_shapeTable_two {t : StatedLieTag} {n : ℕ}
    (h : CoreAssembly.ShapeTable 2 t n) : TwinRow t n := by
  simp only [CoreAssembly.ShapeTable, CoreAssembly.ShapeSL7, CoreAssembly.ShapeSL6,
    CoreAssembly.ShapeSLs, CoreAssembly.ShapeSU7, CoreAssembly.ShapeSU6, CoreAssembly.ShapeSUs,
    CoreAssembly.ShapeSp4, CoreAssembly.ShapeSp3, CoreAssembly.ShapeE7, CoreAssembly.ShapeE8,
    CoreAssembly.ShapeTwinD, CoreAssembly.ShapeTwinSL4, CoreAssembly.ShapeTwinB,
    CoreAssembly.ShapeTwinSp2, CoreAssembly.ShapeTwinTD, CoreAssembly.ShapeTwinSU4] at h
  rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
    ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩ |
    ⟨-, rfl, hk⟩ | ⟨-, rfl, rfl⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact Or.inl ⟨rfl, rfl, hk⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hk⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hk⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))

end Rows

section Transport

theorem card_of_kind {t' : StatedLieTag} {n' : ℕ} {c : CompData} (hc : c = CompData.model t' n')
    {R₀ : Subgroup c.G} (hR₀ : R₀ ∈ c.fund) {m : ℕ}
    (h : Nat.card {S : Subgroup c.G // S ∈ c.fund ∧ Commutes S R₀} = m) :
    ∃ R₀' ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D,
      Nat.card {S : Subgroup (modelUniv t' n' 3 1 Nat.prime_three).K //
        S ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D ∧
          Commutes S R₀'} = m := by
  subst hc
  exact ⟨R₀, hR₀, h⟩

theorem three_of_kind {t' : StatedLieTag} {n' : ℕ} {c : CompData} (hc : c = CompData.model t' n')
    {A B C : Subgroup c.G} (hA : A ∈ c.fund) (hB : B ∈ c.fund) (hC : C ∈ c.fund) (hAB : A ≠ B)
    (hAC : A ≠ C) (hBC : B ≠ C) (cAB : Commutes A B) (cAC : Commutes A C) (cBC : Commutes B C) :
    ∃ A' ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D,
      ∃ B' ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D,
      ∃ C' ∈ fundamentalSubgroups t' (modelUniv t' n' 3 1 Nat.prime_three).D,
        A' ≠ B' ∧ A' ≠ C' ∧ B' ≠ C' ∧ Commutes A' B' ∧ Commutes A' C' ∧ Commutes B' C' := by
  subst hc
  exact ⟨A, hA, B, hB, C, hC, hAB, hAC, hBC, cAB, cAC, cBC⟩

end Transport

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}
  {tY : StatedLieTag} {nY : ℕ}

theorem rank_setup3 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z) (hrow : TwinRow tY nY)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z)
    (hne : Q3TIY.TwinCentralizingNe3 tY nY) :
    ∃ (J : Subgroup G) (t : G) (A : AtT3 K T J z t tY nY)
      (ã ã' : (modelUniv tY nY 3 1 Nat.prime_three).K),
      J ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      ã ∈ A.RK ∧ ã' ∈ A.RT ∧
      ã * ã * A.x⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      ã' * ã' * A.x'⁻¹ ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K ∧
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧
        Commutes N J} =
        1 + Nat.card {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
          R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
            R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} ∧
      ∃ N : Subgroup G, N ∈ centralizingMembers (conjClass3 K) {e.u} ∧ Commutes J A.J₂ ∧
        Commutes J N ∧ Commutes A.J₂ N ∧ J ≠ A.J₂ ∧ J ≠ N ∧ A.J₂ ≠ N := by
  classical
  have hncs := not_commutes_self_of_mem3 hR
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member hKiso hTiso
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts3 A e
  have hJu : J ∈ centralizingMembers (conjClass3 K) {e.u} :=
    c.mem_centralizingMembers_u e hKiso hTiso hJ hJK hJT
  have hJ₂u : A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  have hG := ncard_commuting_J3 hR hT A e huY hψu
  obtain ⟨S, hS, hSle⟩ := hne A.RK A.RT A.x A.x' ã ã' A.hdat hãR hã'R hsq hsq'
  have hfin : Finite (modelUniv tY nY 3 1 Nat.prime_three).K :=
    ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three (twinRow_tag_facts3 hrow).1
      (twinRow_admissible3 hrow)
  have hNpos : 0 < Nat.card {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
      R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
        R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} := by
    have : Nonempty {R : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K //
      R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D ∧
        R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv tY nY 3 1 Nat.prime_three).K)} :=
      ⟨⟨S, hS, hSle⟩⟩
    exact Nat.card_pos
  have hthird : ∃ N, N ∈ centralizingMembers (conjClass3 K) {e.u} ∧ Commutes N J ∧
      N ≠ A.J₂ := by
    by_contra hno
    push Not at hno
    have hsub : {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧
        Commutes N J} ⊆ {A.J₂} := fun N hN => hno N hN.1 hN.2
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton, hG] at this
    omega
  obtain ⟨N, hNu, hNJ, hNne⟩ := hthird
  have hNt : N ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hNu.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hNJ y hy t A.clsJ.mem)⟩
  refine ⟨J, t, A, ã, ã', hJu, hJ₂u, hãR, hã'R, hsq, hsq', hG, N, hNu,
    A.hJiso A.J₂ A.hJ₂t A.hJ₂J, hNJ.symm, A.hJ₂iso N hNt hNne, A.hJ₂J.symm, ?_, hNne.symm⟩
  intro h
  exact hncs J A.hJt.1 (by rw [← h] at hNJ; exact hNJ)

end Setup

section Comp

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem mem_comp_of_card_one3 (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) (i : ι)
    (hone : ∀ j : ι, j = i) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) :
    N ∈ compMembers3 Ω x D i := by
  obtain ⟨j, hj⟩ := exists_range_of_mem3 D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  exact ⟨hN, hone j ▸ hj⟩

end Comp

section Kind

theorem twinYKind3_of_model {P : StatedLieTag → ℕ → Prop}
    (hne : ∀ t n, TwinRow t n → P t n → Q3TIY.TwinCentralizingNe3 t n) :
    Q3TIY.TwinYKind3On P := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e hP1u hO3u ι _ D hcard i
  classical
  obtain ⟨J, t, A, ã, ã', hJu, hJ₂u, -, -, -, -, -, N, hNu, hJJ₂, hJN, hJ₂N, hJJ₂ne, hJNne,
    hJ₂Nne⟩ := rank_setup3 h3 hnab hR hrow hshape hT clsT e (hne tY nY hrow hP)
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have h₁ := mem_comp_of_card_one3 D i hone hJu
  have h₂ := mem_comp_of_card_one3 D i hone hJ₂u
  have h₃ := mem_comp_of_card_one3 D i hone hNu
  rcases D.valid i with ⟨t', n', hft, hadm, hk⟩ | hk | hk
  · obtain ⟨hG2, hD4⟩ := tag3_ne_of_commuting_triple hΩ hex D h₁ h₂ h₃ hJJ₂ hJN hJ₂N hadm hk
    have hnA1 := not_psl_two_of_admissible3 hadm
    have hsc := EX.singleClass_of_kind hk hft hadm hG2 hD4
    have hpc := EX.powCop3_of_kind hk hft hadm hG2 hD4
    obtain ⟨F, hF, hFinj, hFcomm, hFtwin⟩ := EX.twinFamily_of_family3 (ι' := Fin 2) hΩ hex hP1u
      hO3u D hsc hpc ![J, A.J₂]
      (fun k => by fin_cases k; exacts [h₁, h₂])
      (by
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact absurd hab hJJ₂ne
        · exact absurd hab.symm hJJ₂ne
        · rfl)
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact hJJ₂
        · exact hJJ₂.symm
        · exact absurd rfl hkl)
      (by
        intro M hM k l
        have key := A.nbhd_iff hM
        fin_cases k <;> fin_cases l
        · exact Iff.rfl
        · exact key
        · exact key.symm
        · exact Iff.rfl)
    have hmtc := EX.modelTwinClass_of_compData hk F hF hFinj hFcomm hFtwin
    have hmf := EX.mfTwin3 t' n' 2 hft hG2 hD4 hadm hnA1 le_rfl hmtc
    refine ⟨t', n', hk, ?_⟩
    rcases hmf with h | ⟨rfl, rfl, -⟩
    · exact twinRow_of_shapeTable_two h
    · exact Or.inl ⟨rfl, rfl, le_rfl⟩
  · exact absurd (eq_of_mem_compMembers_a13 hΩ hex hP1u hO3u (D := D) (i := i) hk h₁ h₂)
      hJJ₂ne
  · exact absurd hJJ₂ (not_commutes_of_m11_comp3 hΩ hex hP1u hO3u hk h₁ h₂)

end Kind

section Rank

theorem twinYRank3_of_model {P : StatedLieTag → ℕ → Prop}
    (hcount : ∀ t n, TwinRow t n → P t n → Q3TIY.TwinRank3Model t n)
    (hne : ∀ t n, TwinRow t n → P t n → Q3TIY.TwinCentralizingNe3 t n)
    (hsmall : Q3TIY.SmallNoThree3) : Q3TIY.TwinYRank3On P := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e hP1u hO3u ι _ D hcard i t' n' hk
    hrow'
  classical
  obtain ⟨J, t, A, ã, ã', hJu, hJ₂u, hãR, hã'R, hsq, hsq', hG, N, hNu, hJJ₂, hJN, hJ₂N,
    hJJ₂ne, hJNne, hJ₂Nne⟩ := rank_setup3 h3 hnab hR hrow hshape hT clsT e (hne tY nY hrow hP)
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hadm' := twinRow_admissible3 hrow'
  obtain ⟨hft, hG2, hD4, -, -⟩ := twinRow_tag_facts3 hrow'
  have hsc := EX.singleClass_of_kind hk hft hadm' hG2 hD4
  have hpc := EX.powCop3_of_kind hk hft hadm' hG2 hD4
  obtain ⟨R₀, hR₀, -, hcardR⟩ := exists_corr_commuting3 hΩ hex hP1u hO3u D i hone hsc hpc hJu
  rw [hG] at hcardR
  have hnotsmall : ¬ ((t' = .PSp ∧ n' = 2) ∨ (t' = .PSL ∧ n' = 4) ∨ (t' = .PSU ∧ n' = 4)) := by
    intro hs
    obtain ⟨A₁, hA₁, B₁, hB₁, C₁, hC₁, n₁₂, n₁₃, n₂₃, c₁₂, c₁₃, c₂₃⟩ :=
      exists_three_fund3 hΩ hex hP1u hO3u D i hone hpc hJu hJ₂u hNu hJJ₂ne hJNne hJ₂Nne hJJ₂ hJN
        hJ₂N
    obtain ⟨A', hA', B', hB', C', hC', m₁₂, m₁₃, m₂₃, d₁₂, d₁₃, d₂₃⟩ :=
      three_of_kind hk hA₁ hB₁ hC₁ n₁₂ n₁₃ n₂₃ c₁₂ c₁₃ c₂₃
    exact hsmall t' n' hadm' (by
      rcases hs with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))) A' hA' B' hB' C' hC' m₁₂ m₁₃ m₂₃ d₁₂ d₁₃ d₂₃
  obtain ⟨R₀', hR₀', hcardR'⟩ := card_of_kind hk hR₀ hcardR
  exact hcount tY nY hrow hP A.RK A.RT A.x A.x' ã ã' A.hdat hãR hã'R hsq hsq' t' n' hrow' hadm'
    hnotsmall R₀' hR₀' hcardR'

end Rank

end CFSG.ClassicalInvolution.Q3.Q3TIV
