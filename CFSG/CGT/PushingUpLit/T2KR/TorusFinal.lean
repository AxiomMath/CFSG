module

public import CFSG.CGT.PushingUpLit.T2KR.TorusAbs
public import CFSG.CGT.PushingUpLit.T2KR.Assemble
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SNoCompCover

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement

theorem print65Torus_of_lemma214 (hL214 : Lemma214) (hSz : SzTwoPointTorus) : Print65Torus := by
  intro G _ _ L M T n D g hs hbig
  have hDQ := D_le_Q' hs
  have hDA := D_le_A hs
  have hQH := Q_le_Hc hs
  have hAH := A_le_Hc hs
  have hDB : D ≤ normIn (Aof L M g) (QOf L M) := le_inf hDA (hDQ.trans Subgroup.le_normalizer)
  have hBH : normIn (Aof L M g) (QOf L M) ≤ Hc D := inf_le_left.trans hAH
  have hDP : D ≤ normIn (QOf L M) (Aof L M g) := le_inf hDQ (hDA.trans Subgroup.le_normalizer)
  have hPH : normIn (QOf L M) (Aof L M g) ≤ Hc D := inf_le_left.trans hQH
  set ĝ : Ghat D := pi D ⟨g, hs.g_mem⟩ with hĝ
  have hWC : IsWC (star D (QOf L M)) := isWC_star hs
  have hAstar : star D (Aof L M g) = conjSubgroup ĝ (star D (QOf L M)) := star_A_eq hs
  have c := star_cfg hs
  have hne : conjSubgroup ĝ (star D (QOf L M)) ≠ star D (QOf L M) := by
    rw [← hAstar]
    exact c.left_ne_right.symm
  have hL : normIn (star D (QOf L M)) (conjSubgroup ĝ (star D (QOf L M))) ≠ ⊥ := by
    rw [← hAstar]
    exact c.ne
  have hNiP : normIn (star D (QOf L M)) (star D (Aof L M g)) =
      star D (normIn (QOf L M) (Aof L M g)) := normIn_star hDQ hDA hAH
  have hNiB : normIn (star D (Aof L M g)) (star D (QOf L M)) =
      star D (normIn (Aof L M g) (QOf L M)) := normIn_star hDA hDQ hQH
  have hbig' : 2 < (normIn (star D (QOf L M)) (conjSubgroup ĝ (star D (QOf L M)))).relIndex
      (star D (QOf L M)) := by
    rw [← hAstar, hNiP]
    have hPQ : normIn (QOf L M) (Aof L M g) ≤ QOf L M := normIn_le _ _
    have h1 : (star D (normIn (QOf L M) (Aof L M g))).relIndex (star D (QOf L M)) *
        Nat.card (star D (normIn (QOf L M) (Aof L M g))) = Nat.card (star D (QOf L M)) :=
      PairFacts.relIndex_mul_card_of_le (star_mono (D := D) hPQ)
    have h4 := Subgroup.relIndex_mul_relIndex D (normIn (QOf L M) (Aof L M g)) (QOf L M) hDP hPQ
    have e1 := card_star hPH
    have e2 := card_star hQH
    have hpos : 0 < D.relIndex (normIn (QOf L M) (Aof L M g)) := by
      have := PairFacts.relIndex_pos' D (normIn (QOf L M) (Aof L M g))
      omega
    have h5 : (star D (normIn (QOf L M) (Aof L M g))).relIndex (star D (QOf L M)) =
        (normIn (QOf L M) (Aof L M g)).relIndex (QOf L M) := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      calc (star D (normIn (QOf L M) (Aof L M g))).relIndex (star D (QOf L M)) *
            D.relIndex (normIn (QOf L M) (Aof L M g))
          = (star D (normIn (QOf L M) (Aof L M g))).relIndex (star D (QOf L M)) *
            Nat.card (star D (normIn (QOf L M) (Aof L M g))) := by rw [e1]
        _ = Nat.card (star D (QOf L M)) := h1
        _ = D.relIndex (QOf L M) := e2
        _ = D.relIndex (normIn (QOf L M) (Aof L M g)) *
            (normIn (QOf L M) (Aof L M g)).relIndex (QOf L M) := h4.symm
        _ = (normIn (QOf L M) (Aof L M g)).relIndex (QOf L M) *
            D.relIndex (normIn (QOf L M) (Aof L M g)) := mul_comm _ _
    rw [h5]
    exact hbig
  obtain ⟨k, hkT, hkT₁, hk1, hfree⟩ := pair_torus_of_lemma214 hL214 hSz hWC hne hL hbig'
  rw [← hAstar] at hkT₁ hfree
  obtain ⟨h₀, rfl⟩ := pi_surjective D k
  have hh₀M : (h₀ : G) ∈ M := by
    rw [← hs.sec6.N_Q]
    exact (mem_normalizer_star_iff hDQ hQH h₀).1 hkT
  refine ⟨(h₀ : G), hh₀M, ?_⟩
  have hcomm : ∀ a ∈ normIn (star D (Aof L M g)) (star D (QOf L M)),
      ∀ b ∈ normIn (star D (Aof L M g)) (star D (QOf L M)), a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm c.wc₁.1 (normIn_le _ _ ha) (normIn_le _ _ hb)
  have hconj : ∀ b ∈ normIn (star D (Aof L M g)) (star D (QOf L M)),
      pi D h₀ * b * (pi D h₀)⁻¹ ∈ normIn (star D (Aof L M g)) (star D (QOf L M)) := by
    intro b hb
    obtain ⟨hbA, hbN⟩ := mem_normIn.1 hb
    refine mem_normIn.2 ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hkT₁ b).1 hbA
      exact this
    · have hk' := hkT
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk' hbN) (Subgroup.inv_mem _ hk')
  have hfree' : ∀ b ∈ normIn (star D (Aof L M g)) (star D (QOf L M)),
      pi D h₀ * b * (pi D h₀)⁻¹ = b → b = 1 := fun b hb hbk =>
    hfree b (Cfg.normIn_le_cfgM_right _ _ hb) hbk
  have key := exists_comm_of_free hcomm hconj hfree'
  intro x hx
  have hx' : pi D ⟨x, hBH hx⟩ ∈ normIn (star D (Aof L M g)) (star D (QOf L M)) := by
    rw [hNiB]
    exact (mem_star_iff hDB ⟨x, hBH hx⟩).2 hx
  obtain ⟨y', hy', hxy⟩ := key _ hx'
  rw [hNiB] at hy'
  obtain ⟨x'c, rfl⟩ := pi_surjective D y'
  have hx'B : (x'c : G) ∈ normIn (Aof L M g) (QOf L M) := (mem_star_iff hDB x'c).1 hy'
  refine ⟨(x'c : G), hx'B, ?_⟩
  have h1 : pi D ⟨x, hBH hx⟩ = pi D ⁅x'c, h₀⁆ := by
    rw [map_commutatorElement]
    exact hxy
  have hd := (pi_eq_pi_iff D).1 h1
  have hc : (((⁅x'c, h₀⁆ : ↥(Hc D)) : G)) = ⁅(x'c : G), (h₀ : G)⁆ := rfl
  rw [hc] at hd
  refine ⟨((x : G)⁻¹ * ⁅(x'c : G), (h₀ : G)⁆)⁻¹, D.inv_mem hd, ?_⟩
  group

end CFSG.CGT.PushingUpLit.T2KR
