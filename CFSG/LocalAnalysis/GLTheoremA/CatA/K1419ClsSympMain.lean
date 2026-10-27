module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympData
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympB2der
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsSympBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnSympRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem k1419ClsSympFact_of_labels (hRig : CFSG.StandardType.GGLabelRigidInput)
    (hJL : K1419ClsL3U3LabelFact) : K1419ClsSympFact := by
  intro S _ _ α J labK hFam hcen hα3 hα1 hin hJc hcat hZ
  by_cases hbc : labK.tag = .B ∨ labK.tag = .C
  swap
  · have h2der : labK.tag = .B2der := by
      rcases hFam with h | h | h
      · exact absurd (Or.inl h) hbc
      · exact absurd (Or.inr h) hbc
      · exact h
    exact k1419ClsSympB2der S α J labK h2der hcen hα3 hα1 hin hJc hcat hZ
  obtain ⟨K, hK, hKf, n, m, x, J', hn, hKcard, h2, hm, hx3, hx1, hJ', ⟨ePQ⟩⟩ :=
    k1419ClsSympData hcen hbc hα3 hα1 hin hJc
  have hQ : CFSG.Open.IsQuasisimple (PQuot 3 J) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJc
  have hQ' : CFSG.Open.IsQuasisimple (PQuot 3 J') :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ'
  obtain ⟨nJ, hlab⟩ := hJL (PQuot 3 J) hQ hcat
  have hZ' : Subgroup.center (PQuot 3 J') = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    have h2' : ePQ.symm y ∈ Subgroup.center (PQuot 3 J) := by
      rw [← Subgroup.map_center_eq ePQ.symm]
      exact Subgroup.mem_map_of_mem _ hy
    rw [hZ, Subgroup.mem_bot] at h2'
    exact ePQ.symm.injective (by rw [h2', map_one])
  have ePS : PSimple 3 J ≃* PSimple 3 J' :=
    QuotientGroup.congr _ _ ePQ (Subgroup.map_center_eq ePQ)
  have hcat' : catalogIs (PSimple 3 J') l3u3Index := (catalogIs_congr ePS).1 hcat
  have hcentre : proj m K x ∈ J' → False := by
    intro hxJ
    have hj3 : (proj m K x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
    have hj1 : proj m K x ≠ 1 := by
      intro h
      have h1 := Y10GInnSympRed.pow_eq_one_of_proj_pow_eq_one (m := m) h2 (x := x) (p := 1)
        (by rw [pow_one]; exact h)
      exact hx1 (by simpa using h1)
    have hjc : ∀ j ∈ J', proj m K x * j = j * proj m K x := by
      intro j hj
      have hfix := hJ'.1 hj
      rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.conj_apply,
        mul_inv_eq_iff_eq_mul] at hfix
      exact hfix
    exact hj1 (k1419ClsCentre_eq_one hZ' hxJ hjc hj3)
  rcases k1419ClsSympBlock hKcard hn (by omega) x hx3 hx1 hJ' with
    ⟨a, k, E, hEf, hEfin, ha2, hEk, ⟨e⟩, hx⟩ |
    ⟨a, k, E, hEf, hEfin, τ, hτ, ha2, hτk, hEc, ⟨e⟩, hx⟩ |
    ⟨s, hs2, hne, ⟨e⟩⟩ | ⟨hK2, hcard⟩
  ·
    have e1 : PSimple 3 J ≃* StatedProj (StatedSL a E) := ePS.trans e
    rcases hlab with ⟨hl, hn6⟩ | ⟨hl, hn6⟩
    · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.A, 2, nJ⟩ a k
        E ha2 hEk hl ⟨e1⟩
      have hdict' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.A, a - 1, k⟩ := hdict
      injection hdict' with _ h1 _
      exact hcentre (hx (by omega))
    · have hdict := Y10GInnLin.linLabelDict_of_ggLabelRigidInput hRig (PQuot 3 J) ⟨.twA, 2, nJ⟩ a k
        E ha2 hEk hl ⟨e1⟩
      have hdict' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.A, a - 1, k⟩ := hdict
      injection hdict' with h1
      cases h1
  ·
    have e1 : PSimple 3 J ≃* heldSU a E τ hτ ⧸ Subgroup.center (heldSU a E τ hτ) := ePS.trans e
    obtain ⟨ha3, -, -⟩ := k1419ClsUniLabel hRig hlab τ hτ ha2 hτk hEc ⟨e1⟩
    exact hcentre (hx (by omega))
  ·
    have e1 : PQuot 3 J ⧸ Subgroup.center (PQuot 3 J) ≃* StatedProj (StatedSp s K) := ePS.trans e
    rcases hlab with ⟨hl, hn6⟩ | ⟨hl, hn6⟩
    · have h := Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs2 hKcard hne hl e1
      have h' : (⟨.A, 2, nJ⟩ : GLALabel) = ⟨.B, s, n⟩ := h
      injection h' with h1
      cases h1
    · have h := Y10GSympLabel.canonLabel_eq_of_quot_statedSp hRig hs2 hKcard hne hl e1
      have h' : (⟨.twA, 2, nJ⟩ : GLALabel) = ⟨.B, s, n⟩ := h
      injection h' with h1
      cases h1
  ·
    have h720 := k1419ClsSympCard hQ'.2 hcat'
    exact absurd hcard (not_le.mpr h720)

end CFSG.LocalAnalysis.GLTheoremA.K1419
