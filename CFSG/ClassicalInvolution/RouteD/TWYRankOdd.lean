module

public import CFSG.ClassicalInvolution.RouteD.TWYVisible
public import CFSG.ClassicalInvolution.RouteD.TWYOdd
public import CFSG.ClassicalInvolution.RouteD.TWYBridge
public import CFSG.ClassicalInvolution.RouteD.TWYArith
public import CFSG.ClassicalInvolution.RouteD.TWYLayer
public import CFSG.ClassicalInvolution.RouteD.TWYSp2
public import CFSG.ClassicalInvolution.Asc77.AscIHSectE
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs QuadraticMap

local notation "𝒞" => CoreAssembly.conjClass

section Rank

variable {p f : ℕ} [Fact p.Prime]

theorem twinYRankOn_odd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hP1 : TwinYP1On p f fun t n => t = .POmegaOdd ∧ 4 ≤ n) :
    TwinYRankOn p f fun t n => t = .POmegaOdd ∧ 4 ≤ n := by
  intro G _ _ _ hnab K z S tY nY hrow hP hshape T hT clsT e D hcard i horth'
  obtain ⟨rfl, hn⟩ := hP
  have hP1u := hP1 G hnab K z S .POmegaOdd nY hrow ⟨rfl, hn⟩ hshape T hT clsT e
  obtain ⟨d, ε, hd5, horth⟩ := horth'
  have hDi : D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := by
    rcases horth with ⟨-, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ | ⟨-, -, ht, -⟩ |
      ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩ <;> rw [ht] <;> exact ⟨by decide, by decide⟩
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4 := fun j => by
    rw [hsub.elim j i]
    exact hDi
  have hexp : D.exp i = f := (D.exp_eq i).resolve_right fun h => (hD i).2 h.1
  have hncs : ∀ L ∈ 𝒞 K, ¬ Commutes L L := fun L hL => not_commutes_self_of_mem S.inClass hL
  obtain ⟨J, J', t, hJ, hJK, hJT, hJt, htz, -, -, -, -⟩ :=
    exists_frameMembers hnab S hrow hshape hT clsT e
  obtain ⟨A⟩ := exists_atT S hrow hshape hT clsT hJ hJK hJT hJt htz
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts A e
  have hJu : J ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u hJ.1 (hT.comm_K J hJ hJK).symm (hT.comm_T J hJ hJT).symm
  have hJ₂u : A.J₂ ∈ centralizingMembers (𝒞 K) {e.u} :=
    e.mem_centralizingMembers_u A.hJ₂t.1 (hT.comm_K A.J₂ A.hJ₂z A.hJ₂K).symm
      (hT.comm_T A.J₂ A.hJ₂z A.hJ₂T).symm
  have hG := ncard_commuting_J S hT A e hJt.mem huY hψu
  have hY := card_fund_centralizing_odd hp2 hq hn A.hdat.toOn hãR hã'R hsq hsq'
  obtain ⟨R₀, hR₀, hcorr, hN⟩ := exists_corr_commuting hp2 hq S.inClass S.exact hP1u D hcard i hD
    hJu
  rw [hG] at hN
  have hq2 : 2 ≤ p ^ f := by omega
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hfr0 := framesOdd_ne_zero hq2 (nY - 3)
  have hFpos : Nat.card {R : Subgroup (modelUniv .POmegaOdd nY p f Fact.out).K //
      R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd nY p f Fact.out).D ∧
        R ≤ Subgroup.centralizer ({ã * ã'} :
          Set (modelUniv .POmegaOdd nY p f Fact.out).K)} ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hY
    omega
  have hJ₂c : Commutes A.J₂ J := A.hJ₂iso J A.hJt A.hJ₂J.symm
  have hthird : ∃ N, N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J ∧ N ≠ A.J₂ := by
    by_contra hno
    push Not at hno
    have hsub' : {N : Subgroup G | N ∈ centralizingMembers (𝒞 K) {e.u} ∧ Commutes N J} ⊆
        {A.J₂} := fun N hN => hno N hN.1 hN.2
    have := Set.ncard_le_ncard hsub' (Set.finite_singleton _)
    rw [Set.ncard_singleton, hG] at this
    omega
  have hsmall : ((D.tag i = .PSp ∧ D.rank i = 2) ∨ (D.tag i = .PSL ∧ D.rank i = 4) ∨
      (D.tag i = .PSU ∧ D.rank i = 4)) → False := by
    intro hs
    obtain ⟨N, hNu, hNJ, hNne⟩ := hthird
    have hNt : N ∈ centralizingMembers (𝒞 K) {t} :=
      ⟨hNu.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hNJ y hy t hJt.mem)⟩
    have hNJne : J ≠ N := fun h => hncs J hJ.1 (by subst h; exact hNJ)
    obtain ⟨X₁, hX₁, X₂, hX₂, X₃, hX₃, n₁₂, n₁₃, n₂₃, c₁₂, c₁₃, c₂₃⟩ :=
      exists_three_fund hp2 hq S.inClass S.exact hP1u D hcard i hD hJu hJ₂u hNu A.hJ₂J.symm hNJne
        hNne.symm (commutes_symm hJ₂c) (commutes_symm hNJ) (A.hJ₂iso N hNt hNne)
    exact CFSG.ClassicalInvolution.Asc77.smallNoThree (p := p) (D.tag i) (D.rank i) (D.exp i)
      (D.admissible i) hp2 (by rw [hexp]; exact hq)
      (by rcases hs with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))) X₁ hX₁ X₂ hX₂ X₃ hX₃ n₁₂ n₁₃ n₂₃ c₁₂ c₁₃ c₂₃
  have hcount : ∀ {Fr : ℕ}, 2 * Fr + Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (detQ (K := GaloisField p f))) =
      (1 + Nat.card {R : Subgroup (modelUniv .POmegaOdd nY p f Fact.out).K //
        R ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd nY p f Fact.out).D ∧
          R ≤ Subgroup.centralizer ({ã * ã'} : Set (modelUniv .POmegaOdd nY p f Fact.out).K)}) *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField p f))) →
      Fr = framesOdd (p ^ f) (nY - 3) := by
    intro Fr h
    rw [add_mul, one_mul, hY] at h
    omega
  show D.tag i = .POmegaOdd ∧ D.rank i = nY + 1
  rcases horth with ⟨-, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, hr⟩ | ⟨-, -, ht, -⟩ |
    ⟨-, -, -, ht, -⟩ | ⟨-, -, -, ht, -⟩
  · exact (hsmall (Or.inl ⟨ht, hr⟩)).elim
  · exact (hsmall (Or.inr (Or.inl ⟨ht, hr⟩))).elim
  · exact (hsmall (Or.inr (Or.inr ⟨ht, hr⟩))).elim
  · obtain ⟨j, hj, hk⟩ := layerCount_odd hp2 hq ht hexp (D.admissible i) hR₀ hN
    have hc := hcount hk
    rcases j with _ | j
    · exact (hfr0 (by rw [← hc]; rfl)).elim
    · have hj' : j = nY - 3 := framesOdd_inj Fact.out hf1 rfl hq hc
      exact ⟨ht, by omega⟩
  · obtain ⟨j, hj, hk⟩ := layerCount_plus hp2 hq ht hexp (D.admissible i) hR₀ hN
    exact (framesOdd_ne_framesPlus Fact.out hp2 hf1 rfl hq (nY - 3) j
      (hcount hk).symm).elim
  · obtain ⟨j, hj, hk⟩ := layerCount_minus hp2 hq ht hexp (D.admissible i) hR₀ hN
    have hc := hcount hk
    rcases j with _ | j
    · exact (hfr0 (by rw [← hc]; rfl)).elim
    · exact (framesOdd_ne_framesMinus Fact.out hp2 hf1 rfl hq (nY - 3) j
        hc.symm).elim

end Rank

end CFSG.ClassicalInvolution.RouteD.TWY
