module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU48Model

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti

theorem lieIndex_isU4eight {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 3 q).Valid), q.card = 8 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 3 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CatB.exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

section Griess


theorem multU48At_holds (G : Type) [Group G] [Finite G] : MultU48At G := by
  intro L hQ hcat
  obtain ⟨q, hv, hq8, ⟨e⟩⟩ := lieIndex_isU4eight hcat
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq8.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hQ hm
    (a := 1) (b := 1) (c := 1) (d := 1) (by decide) (by decide) (by norm_num)
  have hz : Nat.card (Subgroup.center ↥L) = 1 := Nat.dvd_one.mp (by simpa using hdvd)
  have hZ : Subgroup.center ↥L = ⊥ := Subgroup.card_eq_one.mp hz
  exact (catalogIs_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot)).1 hcat

end Griess

theorem bridge_u4eight {S : Type} [Group S] (h : catalogIs S S9.isU4eight) :
    Nonempty (S ≃* CFSG.PGLModel.projSU 4 2 3) := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieIndex_isU4eight h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype (GaloisField 2 6) := Fintype.ofFinite _
  have hc : Fintype.card K = Fintype.card (GaloisField 2 6) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card 2 6 (by norm_num)]
    norm_num
  exact ⟨e'.trans ((CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 4 (2 ^ 3)).trans
    (CFSG.RankThree.PartTwo.Sec4.projSUEquivStatedProj 4 2 3).symm)⟩

private theorem subsingleton_quot_of_subsingleton_auts {Q : Type} [Group Q] [Subsingleton Q]
    (N : Subgroup Q) : Subsingleton (Q ⧸ N) :=
  ⟨fun a b => by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim u v]⟩

theorem glaPPrimeCore_eq_bot_of_isU4eight {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hL : GLAPComponent 3 X L) (hcat : catalogIs ↥L S9.isU4eight) :
    GLAPPrimeCore 3 ↥L = ⊥ := by
  have hsimple : IsSimpleGroup ↥L := S10.isSimple_of_isU4eight hcat
  have hPS : IsSimpleGroup (PSimple 3 L) :=
    (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL).2
  haveI := hPS.toNontrivial
  have hne_top : GLAPPrimeCore 3 ↥L ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot 3 L) := by
      unfold PQuot
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PSimple 3 L) (subsingleton_quot_of_subsingleton_auts _)
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥L)).resolve_right hne_top

section AutU48

open CFSG.ComponentClassification.OuterAutomorphisms (inner congr_conj)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.RankThree.PartTwo.KFacts.KS21.U58 (card_ringAut_K)
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 equivSU4 fieldFactor4
  mem_range_conj_of_fieldFactor4_eq_one)

theorem autU48_holds (G : Type) [Group G] [Finite G] : AutU48At G := by
  intro X L A hL hcat hA hEl
  have hO := glaPPrimeCore_eq_bot_of_isU4eight hL hcat
  have eQ : PQuot 3 L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  obtain ⟨e₀⟩ := bridge_u4eight hcat
  let τ : PQuot 3 L ≃* SU4 := (eQ.trans e₀).trans equivSU4
  let Φ := (fieldFactor4.comp (MulAut.congr τ).toMonoidHom).comp
    ((barAut 3 L).comp (Subgroup.inclusion hA))
  have hPA : IsPGroup 3 ↥A := isPGroup_of_isElemAbelian hEl
  have hcardR : Nat.card Φ.range ∣ 6 := by
    rw [← card_ringAut_K]
    exact Subgroup.card_subgroup_dvd_card Φ.range
  have hdvdA : Nat.card Φ.range ∣ Nat.card ↥A :=
    Dvd.intro_left _ (Subgroup.card_ker_mul_card_range Φ)
  have hd3 : Nat.card Φ.range ∣ 3 := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hPA
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hdvdA.trans hn)
    rw [hi] at hcardR ⊢
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i <;> simp
    · exfalso
      have h9 : 3 ^ 2 ∣ 3 ^ i := pow_dvd_pow 3 h
      have h96 : 3 ^ 2 ∣ 6 := h9.trans hcardR
      norm_num at h96
  refine ⟨Φ.ker.map A.subtype, Subgroup.map_subtype_le Φ.ker, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective]
    have hsum := Subgroup.card_ker_mul_card_range Φ
    have hle : Nat.card Φ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hd3
    calc Nat.card ↥A = Nat.card Φ.ker * Nat.card Φ.range := hsum.symm
      _ ≤ Nat.card Φ.ker * 3 := Nat.mul_le_mul_left _ hle
      _ = 3 * Nat.card Φ.ker := Nat.mul_comm _ _
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    have hx1 : fieldFactor4 (MulAut.congr τ (barAut 3 L ⟨(x : G), hA x.2⟩)) = 1 := hx
    obtain ⟨g, hg⟩ := mem_range_conj_of_fieldFactor4_eq_one hx1
    have hmem : barAut 3 L ⟨(x : G), hA x.2⟩ ∈ inner (PQuot 3 L) := by
      refine ⟨τ.symm g, (MulAut.congr τ).injective ?_⟩
      rw [congr_conj, τ.apply_symm_apply]
      exact hg
    exact (inducesInnerMod_iff_barAut_mem_inner (hA x.2)).2 hmem

end AutU48

end CFSG.LocalAnalysis.GLTheoremA
