module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Count
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29Ext
public import CFSG.HardMathSupport.Solomon.LocalBalance.TwoLocalTools

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Input11_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) ≤ 2

theorem lemma29_of_input11_2 (h : Input11_2) : Lemma29 := by
  classical
  intro G _ _ m hstd B hBel hrank X hBX hXne
  have hXrank : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B :=
    (glaTwoLocalRank_subgroup_le Nat.prime_three X).trans hrank.symm.le
  let S : Set (Subgroup G) := {J | GLAPComponent 3 X J ∧ ¬ B ≤ Subgroup.normalizer (J : Set G)}
  have hSfin : S.Finite := Set.toFinite S
  have hinput : ∀ J ∈ S, (Subgroup.normalizer (J : Set G)).relIndex B = 3 ∧
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 J))) ≤ 2 := fun J hJ =>
    (h G m 3 hstd X B J hBel hBX hXrank hJ.1 hJ.2).2
  have hcl : ∀ J ∈ S, ∀ g ∈ B, GLBConj g J ∈ S := by
    intro J hJ g hg
    have hgX : GLBConj g X = X := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hBX hg))
    refine ⟨?_, ?_⟩
    · have := glaPComponent_gLBConj g hJ.1
      rwa [hgX] at this
    · rw [le_normalizer_gLBConj_iff hBel.1 hg]
      exact hJ.2
  have hcount := card_le_card_iInf_mul_pow hBel.1 S hSfin hcl (fun J hJ => (hinput J hJ).1)
    (kerB 3 B) (fun J _ => kerB_le 3 B J) (fun J _ g hg => kerB_gLBConj 3 hBel.1 J hg)
    (fun J hJ => relIndex_kerB_le hBel (hinput J hJ).2 (hinput J hJ).1)
  set A₀ : Subgroup G := B ⊓ ⨅ J ∈ S, kerB 3 B J with hA₀
  have hA₀B : A₀ ≤ B := inf_le_left
  have hA₀ker : ∀ J ∈ S, A₀ ≤ kerB 3 B J := fun J hJ =>
    inf_le_right.trans (iInf₂_le J hJ)
  have hA₀el : IsElemAbelian 3 A₀ := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun x hx => hBel.2 x (hA₀B hx)⟩
    have := hBel.1.is_comm.comm ⟨u, hA₀B u.2⟩ ⟨v, hA₀B v.2⟩
    exact Subtype.ext (by simpa using congrArg Subtype.val this)
  obtain ⟨B', hAB', hB'X, -, hB'el, hB'card, hB'N, hB'not⟩ :=
    exists_extension (X := X) hSfin.toFinset
      (fun J hJ => ((hSfin.mem_toFinset).1 hJ).1) hA₀el (hA₀B.trans hBX)
      (fun L hL => by
        by_cases hLB : B ≤ Subgroup.normalizer (L : Set G)
        · exact hA₀B.trans hLB
        · exact (hA₀ker L ⟨hL, hLB⟩).trans (inf_le_right.trans (fun g hg => hg.1)))
      (fun J hJ => (hA₀ker J ((hSfin.mem_toFinset).1 hJ)).trans inf_le_right)
  refine ⟨B', hB'X, hB'el, ?_, hB'N, fun J hJ hJB => hB'not J
    ((hSfin.mem_toFinset).2 ⟨hJ, hJB⟩)⟩
  obtain ⟨k, hk⟩ := (GL83.isPGroup_of_isElemAbelian hBel).exists_card_eq
  obtain ⟨k', hk'⟩ := (GL83.isPGroup_of_isElemAbelian hB'el).exists_card_eq
  rw [pRank_eq_of_card Nat.prime_three hBel hk, pRank_eq_of_card Nat.prime_three hB'el hk']
  have hle : 3 ^ k ≤ 3 ^ k' := by
    rw [← hk, ← hk', hB'card]
    exact hcount
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle

end CFSG.HardMathSupport.Solomon.LocalBalance
