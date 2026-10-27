module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParType
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups

variable {Ω : Type} [Group Ω] [Finite Ω]


private theorem false_of_exc_parabolic_aux1 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p ≠ 3) {n k : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (hk1 : k = 1 → 5 ≤ n) (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1)
    (hJ : catalogIs (PSimple p J) (isOmPA n (2 ^ k)))
    {kf : DefChar.LieFamily} {qc : TauCeti.PrimePower} {hv : (LocalTwo.excIndex kf qc).Valid}
    (hqc : qc.p = 2) (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩))
    (hnt : Nontrivial (PSimple p X)) (hcm : ¬ CentMod p X x)
    (hJx : GLAPComponent p (X ⊓ cx x) J) (hcard : qc.card = 2 ^ qc.exponent)
    (hqp : p ∣ qc.card + 1) (hek : qc.exponent ∣ k) (htw : kf = .twistedE6) : False := by
  subst htw
  obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hQ, ⟨eJ⟩⟩ :=
    exc_lang_twE6 H.hp H.hp2 hqc H.hX hnt hcat H.hxp H.hxN hcm H.hinn hJx
  have hqp' : p ∣ SL.D.q + 1 := by rw [hq]; exact hqp
  have hen := exc_ennola_twE6 H.hp H.hp2 hp3 SL hρ hT hap hqp' i
  have hJ' : catalogIs (↥(excRatComp SL a i) ⧸ Subgroup.center ↥(excRatComp SL a i))
      (isOmPA n (2 ^ k)) := by
    obtain ⟨j, hj, ⟨f⟩⟩ := hJ
    exact ⟨j, hj, ⟨eJ.symm.trans f⟩⟩
  exact exc_rational_false H.hp H.hp2 hp3 (τ := .E6) (Or.inr (Or.inl rfl)) SL hT hap ha1 i
    qc.exponent_pos (hq.trans hcard) hqp' hen hQ hn hn3 hk hk1 hpk hek hJ'

private theorem false_of_exc_parabolic_aux2 {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω]
    {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p ≠ 3) {n k : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (hk1 : k = 1 → 5 ≤ n) (hk : 1 ≤ k) (hpk : p ∣ 2 ^ k + 1)
    (hJ : catalogIs (PSimple p J) (isOmPA n (2 ^ k)))
    {kf : DefChar.LieFamily} {qc : TauCeti.PrimePower} {hv : (LocalTwo.excIndex kf qc).Valid}
    (hqc : qc.p = 2) (hcat : Nonempty (PSimple p X ≃* LocalTwo.CatT ⟨LocalTwo.excIndex kf qc, hv⟩))
    (hkf : kf = .F4 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8)
    (hnt : Nontrivial (PSimple p X)) (hcm : ¬ CentMod p X x)
    (hJx : GLAPComponent p (X ⊓ cx x) J) (hcard : qc.card = 2 ^ qc.exponent)
    (hqp : p ∣ qc.card + 1) (hek : qc.exponent ∣ k) (htw : kf ≠ .twistedE6) : False := by
  have hk3 : kf = .F4 ∨ kf = .E7 ∨ kf = .E8 := by
    rcases hkf with h | h | h | h
    · exact Or.inl h
    · exact absurd h htw
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hk4 : kf = .F4 ∨ kf = .E6 ∨ kf = .E7 ∨ kf = .E8 := by
    rcases hk3 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  obtain ⟨L, _, _, _, SL, a, i, w, hq, hρ, hT, hap, ha1, hQ, ⟨eJ⟩⟩ :=
    exc_lang_untw H.hp H.hp2 hk4 hqc H.hX hnt hcat H.hxp H.hxN hcm H.hinn hJx
  have hqp' : p ∣ SL.D.q + 1 := by rw [hq]; exact hqp
  have hen := exc_ennola_untw H.hp H.hp2 hk3 SL hρ hT hap hqp' i
  have hJ' : catalogIs (↥(excRatComp SL a i) ⧸ Subgroup.center ↥(excRatComp SL a i))
      (isOmPA n (2 ^ k)) := by
    obtain ⟨j, hj, ⟨f⟩⟩ := hJ
    exact ⟨j, hj, ⟨eJ.symm.trans f⟩⟩
  have hτ : excTag kf = .F4 ∨ excTag kf = .E6 ∨ excTag kf = .E7 ∨ excTag kf = .E8 := by
    rcases hk3 with h | h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  exact exc_rational_false H.hp H.hp2 hp3 hτ SL hT hap ha1 i qc.exponent_pos (hq.trans hcard)
    hqp' hen hQ hn hn3 hk hk1 hpk hek hJ'

theorem false_of_exc_parabolic {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) (hp3 : p ≠ 3)
    (hpar : catalogIs (PSimple p X) ExcParIdx) : False := by
  obtain ⟨n, k, hn, hn3, hk1, hk, hpk, hJ⟩ := exc_type167J_clause_c H.htype hp3
  obtain ⟨kf, qc, hv, hkf, hqc, hcat⟩ := exc_catalog_data hpar
  have hnt : Nontrivial (PSimple p X) := exc_pSimple_nontrivial hkf hqc hcat
  have hcm : ¬ CentMod p X x := exc_not_centMod H.hX hnt H.hxX
  have hJx : GLAPComponent p (X ⊓ cx x) J := glaPComponent_inf_cx_of_eq_sup H.hDx H.hJ
  have hkf5 : kf = .F4 ∨ kf = .E6 ∨ kf = .twistedE6 ∨ kf = .E7 ∨ kf = .E8 := by
    rcases hkf with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hek : qc.exponent ∣ k := exc_fieldRel H hn3 hk hk1 hJ hkf5 hqc hcat
  have hcard : qc.card = 2 ^ qc.exponent := by rw [TauCeti.PrimePower.card_def, hqc]
  have hqp : p ∣ qc.card + 1 := by
    obtain ⟨lab, hlab, hhs⟩ := H.hhs
    obtain ⟨htag, hlabn⟩ := exc_label_of_catalog H.hp H.hX hkf hqc hcat hlab
    have h := exc_halfSplit_arith H.hp H.hp2 hp3 htag hhs hpk (by rw [hlabn]; exact hek)
    rw [hlabn] at h
    rwa [hcard]
  by_cases htw : kf = .twistedE6
  · exact false_of_exc_parabolic_aux1 H hp3 hn hn3 hk1 hk hpk hJ hqc hcat hnt hcm hJx hcard hqp hek htw
  · exact false_of_exc_parabolic_aux2 H hp3 hn hn3 hk1 hk hpk hJ hqc hcat hkf hnt hcm hJx hcard hqp hek htw

end CFSG.LocalAnalysis.GLTheoremA.I167

end
