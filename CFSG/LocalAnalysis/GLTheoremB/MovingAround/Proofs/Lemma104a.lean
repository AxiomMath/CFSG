module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma103

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_glbCore' {p : ℕ} {E A₀ : Subgroup G}
    (hA₀E : A₀ ≤ E) (h2 : 2 ≤ CFSG.Open.pRank p A₀) :
    Subgroup.centralizer (A₀ : Set G) ≤ GLBCore p 2 E := by
  have hN : Subgroup.normalizer (A₀ : Set G) ≤ GLBCore p 2 E := by
    unfold GLBCore
    exact le_sSup ⟨A₀, hA₀E, h2, rfl⟩
  exact (Subgroup.centralizer_le_normalizer _).trans hN

theorem centralizer_inf_le_M' {p : ℕ} {E A M : Subgroup G} (hU : IsUniquenessTwoLocal p E M)
    (h2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A)) :
    Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
  (centralizer_le_glbCore' inf_le_left h2).trans hU.clause_d

theorem isSCp_top_of_centralizer' {p : ℕ} {M X A₀ : Subgroup G} (hX : IsSCp p M X)
    (hA₀ : A₀ ≤ X) (hC : Subgroup.centralizer (A₀ : Set G) ≤ M) : IsSCp p ⊤ X := by
  refine ⟨le_top, hX.2.1, fun Y _ hY hXY => ?_⟩
  have hYC : Y ≤ Subgroup.centralizer (A₀ : Set G) :=
    le_centralizer_of_comm' hY (hA₀.trans hXY)
  exact hX.2.2 Y (hYC.trans hC) hY hXY

theorem ddKey_first_le' {p : ℕ} {E A E' A' : Subgroup G}
    (h : ddKey p E' A' ≤ ddKey p E A) :
    CFSG.Open.pRank p (E' ⊓ A') ≤ CFSG.Open.pRank p (E ⊓ A) := by
  unfold ddKey at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h1 | h1
  · exact h1.le
  · exact h1.1.le

theorem lemma104_ii_holds : Lemma104_iiStatement := by
  intro G _ _ m p B M h E A hEA
  have hDD := hEA.1
  have hEinD : inD p M E := hDD.1
  have hAinDp : inDp p M A := hDD.2.1
  have h2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hDD.2.2
  have hEsc : IsSCp p M E := hEinD.1.1
  have hAsc : IsSCp p M A := hAinDp.1.1
  have hCM : Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    centralizer_inf_le_M' hEinD.2 h2
  exact ⟨isSCp_top_of_centralizer' hEsc inf_le_left hCM,
    isSCp_top_of_centralizer' hAsc inf_le_right hCM⟩

theorem lemma104_i_of_lemma101_i (h101i : Lemma101_iStatement) : Lemma104_iStatement := by
  intro G _ _ m p B M h E A hEA
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hDD := hEA.1
  have hmax := hEA.2
  have hEinD : inD p M E := hDD.1
  have hAinDp : inDp p M A := hDD.2.1
  have h2 : 2 ≤ CFSG.Open.pRank p (E ⊓ A) := hDD.2.2
  have hEel : CFSG.Open.IsElemAbelian p E := hEinD.1.1.2.1
  have hAel : CFSG.Open.IsElemAbelian p A := hAinDp.1.1.2.1
  have hCM : Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤ M :=
    centralizer_inf_le_M' hEinD.2 h2
  have hEC : E ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    le_centralizer_of_comm' hEel inf_le_left
  have hAC : A ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    le_centralizer_of_comm' hAel inf_le_right
  obtain ⟨x, hxC, S, hSp, -, hES, hAxS⟩ :=
    exists_conj_le_pGroup' (K := Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
      (X := E) (Y := A) hEC (isPGroup_of_isElemAbelian' hEel) hAC
      (isPGroup_of_isElemAbelian' hAel)
  have hxM : x ∈ M := hCM hxC
  have hA' : inDp p M (GLBConj x A) := (h101i h hxM hEinD hAinDp).2
  have hcomm : ∀ a ∈ E ⊓ A, x * a * x⁻¹ = a := by
    intro a ha
    have hax := Subgroup.mem_centralizer_iff.1 hxC a ha
    rw [← hax]
    simp
  have hA₀A' : E ⊓ A ≤ E ⊓ GLBConj x A := by
    intro a ha
    obtain ⟨haE, haA⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨haE, ?_⟩
    rw [mem_gLBConj, hcomm a ha]
    exact haA
  have h2' : 2 ≤ CFSG.Open.pRank p (E ⊓ GLBConj x A) :=
    h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt hA₀A')
  have hmaxA' := hmax E (GLBConj x A) ⟨hEinD, hA', h2'⟩
  have hfirst : CFSG.Open.pRank p (E ⊓ GLBConj x A) = CFSG.Open.pRank p (E ⊓ A) :=
    le_antisymm (ddKey_first_le' hmaxA') (CFSG.SectionRank.pRank_mono hp.one_lt hA₀A')
  have hpA : CFSG.Open.pRank p (GLBConj x A) = CFSG.Open.pRank p A :=
    pRank_gLBConj' hp.one_lt x A
  have hS' : IsPGroup p ↥(E ⊔ GLBConj x A) := IsPGroup.to_le hSp (sup_le hES hAxS)
  by_contra hnot
  unfold ddKey at hmaxA'
  rw [hfirst, hpA] at hmaxA'
  simp [Prod.Lex.toLex_le_toLex, hS', hnot] at hmaxA'

theorem lemma104_i_of_conj (hconj : IsUniquenessTwoLocal_conjStatement) : Lemma104_iStatement :=
  lemma104_i_of_lemma101_i (lemma101_i_of_conj hconj)

theorem lemma104_vi_of_lemma104_v (h104v : Lemma104_vStatement) : Lemma104_viStatement := by
  intro G _ _ m p B M h E A hEA h3E
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hDD := hEA.1
  have hmax := hEA.2
  have hAinDp : inDp p M A := hDD.2.1
  have h3A : 3 ≤ CFSG.Open.pRank p A := hAinDp.1.2
  have hAsc : IsSCp p M A := hAinDp.1.1
  by_contra hne
  obtain ⟨A₁, hA₁A, hA₁e, hA₁c⟩ :=
    exists_elemAbelian_card_pow_of_le_pRank' (p := p) (k := 4) (H := A) (by omega)
  obtain ⟨R, hR, hA₁R⟩ :=
    exists_sylowIn_above (X := M) (hA₁A.trans hAsc.1) (isPGroup_of_isElemAbelian' hA₁e)
  have hEk : IsEkIn p 4 R A₁ := ⟨hA₁R, hA₁e, hA₁c⟩
  obtain ⟨-, -, A₂, hA₂D, hA₁A₂⟩ := (h104v h hEA (Or.inl h3E) hR).1 A₁ hEk
  have hrank4 : 4 ≤ CFSG.Open.pRank p (A₂ ⊓ A) :=
    CFSG.SectionRank.le_pRank hp.one_lt (le_inf hA₁A₂ hA₁A) hA₁e hA₁c
  have h2A : 2 ≤ CFSG.Open.pRank p (A₂ ⊓ A) := le_trans (by norm_num) hrank4
  have hle := hmax A₂ A ⟨hA₂D, hAinDp, h2A⟩
  have hEA_le := ddKey_first_le' hle
  have hEle : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p E :=
    CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left
  omega

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
