module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FSz
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FTitsAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.RankThree.PartOne.F106.OddRadRadical
public import CFSG.RankThree.PartOne.KEXC.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open scoped commutatorElement

section Pure

private theorem s265f_range_elemAbelian {M Ω : Type*} [Group M] [Group Ω] {p : ℕ} {E : Subgroup Ω}
    (hE : IsElemAbelian p E) (φ : ↥E →* M) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    show (a : M) * b = b * a
    rw [← ha', ← hb', ← map_mul, ← map_mul]
    exact congrArg φ (hE.1.is_comm.comm a' b')
  · obtain ⟨y, rfl⟩ := hx
    rw [← map_pow]
    have : y ^ p = 1 := Subtype.ext (hE.2 y y.2)
    rw [this, map_one]

end Pure

section Main


variable {G : Type} [Group G] [Finite G]

private theorem s265f_tits_model {R : Type} [Group R] (h : catalogIs R tyTits) :
    MarkedModel ⟨.twF4der, 0, 1⟩ R := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | tits =>
      have hR := CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e
      exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hR⟩))
    | _ => exact hi.elim

theorem s265f_ident_tits {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} {b : G}
    (hF : FieldOn p b L) (hbp : b ^ p = 1) (hI : Ipart p L b ≠ ⊥)
    (hJ : catalogIs (PSimple p (Ipart p L b)) tyTits) :
    ∃ lab : LargeEvenLabel, lab.tag = .twF4 ∧ lab.n = p ∧ LargeEvenInLambda2 lab ∧
      MarkedModel lab (PSimple p L) := by
  obtain ⟨lab, hlab, hM, hpn, h⟩ := s265f_ident_gen hp hp2 hF hbp hI
  have hT := s265f_tits_model hJ
  rcases h with ⟨hΛ, hMD⟩ | ⟨-, hord⟩
  · exfalso
    have hder := s265f_not_der hp hlab hpn
    have hne : (⟨.twF4der, 0, 1⟩ : LargeEvenLabel).tag ≠
        (⟨lab.tag, lab.rank, lab.n / p⟩ : LargeEvenLabel).tag := fun h => hder.2.2 h.symm
    exact (MI.derived_labelUniq (Or.inr rfl) hne hT hMD).false (MulEquiv.refl _)
  · have hcard : Nat.card (PSimple p (Ipart p L b)) = 17971200 := by
      rw [MI.card_markedModel_twF4der (lab := ⟨.twF4der, 0, 1⟩) rfl hT]
      rw [MI.ordTits_eq]
      norm_num
    obtain ⟨htag, hn⟩ := hord hcard
    exact ⟨lab, htag, hn, hlab, hM⟩

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s265f_false_of_tits {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hp5 : p = 5) (hJ : catalogIs (PSimple p (Ipart p S b)) tyTits) : False := by
  subst hp5
  have hp := cfg.prime
  have hp2 := cfg.odd
  have hF : FieldOn 5 b S := by
    rcases cfg.prop with hF | ⟨h3, -, -⟩
    · exact hF
    · exact absurd h3 (by norm_num)
  have hbp : b ^ 5 = 1 := cfg.elem.2 b cfg.hb
  obtain ⟨lab, htag, hn, hlab, hM⟩ := s265f_ident_tits hp hp2 hF hbp cfg.ipart hJ
  have hL : CFSG.Blueprint.LieModel (PSimple 5 S) .twistedF4 0 2 5 := by
    obtain ⟨t, r, n⟩ := lab
    dsimp only at htag hn
    subst htag
    subst hn
    simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM
  haveI hSn : S.Normal := cfg.normal
  let eQ : PSimple 5 S ≃* (↥S ⧸ Subgroup.center ↥S) := qu_pSimpleEquiv cfg.core
  have hL' := CFSG.Blueprint.LieModel.of_mulEquiv eQ hL
  obtain ⟨-, hmodel⟩ := hL'.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨E, hEB, hEel, hE3, hlay⟩ := cfg.gstar
  set φ : ↥E →* MulAut (↥S ⧸ Subgroup.center ↥S) := (S2019.actQuot S).comp E.subtype with hφ
  have hĒ : IsElemAbelian 5 φ.range := s265f_range_elemAbelian hEel φ
  have hSperf : ⁅S, S⁆ = S := S2019.commutator_self_eq_of_isQuasisimple cfg.quasi
  have hker : Nat.card φ.ker ≤ 5 := by
    have hmem : ∀ k : ↥φ.ker, ((k.1 : ↥E) : Ω) ∈ Subgroup.zpowers x := by
      intro k
      have hk1 : S2019.actQuot S ((k.1 : ↥E) : Ω) = 1 := k.2
      have hcen : ((k.1 : ↥E) : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
        refine S2019.le_centralizer_of_actQuot_eq_one S hSperf
          (K := Subgroup.zpowers ((k.1 : ↥E) : Ω)) ?_ (Subgroup.mem_zpowers _)
        intro c hc
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
        rw [map_zpow, hk1, one_zpow]
      have hnorm : ((k.1 : ↥E) : Ω) ∈ Subgroup.normalizer (S : Set Ω) := by
        rw [Subgroup.normalizer_eq_top_iff.2 hSn]
        exact Subgroup.mem_top _
      exact (cfg.centB _ (hEB k.1.2)).1 ((centMod_iff_centralizer cfg.core hnorm).2 hcen)
    let ι : ↥φ.ker → ↥(Subgroup.zpowers x) := fun k => ⟨((k.1 : ↥E) : Ω), hmem k⟩
    have hι : Function.Injective ι := fun k l h =>
      Subtype.ext (Subtype.ext (by
        have h' : ((k.1 : ↥E) : Ω) = ((l.1 : ↥E) : Ω) :=
          congrArg (fun z : ↥(Subgroup.zpowers x) => (z : Ω)) h
        exact h'))
    have hordx : Nat.card (Subgroup.zpowers x) = 5 := by
      rw [Nat.card_zpowers, orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1]
    calc Nat.card φ.ker ≤ Nat.card (Subgroup.zpowers x) := Nat.card_le_card_of_injective ι hι
      _ = 5 := hordx
  have h25 : 25 ≤ Nat.card φ.range := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hE3] at h1
    by_contra hlt
    push Not at hlt
    have h2 : Nat.card φ.ker * Nat.card φ.range ≤ 5 * 24 :=
      Nat.mul_le_mul hker (by omega)
    omega
  set Y : Subgroup (↥S ⧸ Subgroup.center ↥S) :=
    (S172X.csIn S E).map (QuotientGroup.mk' (Subgroup.center ↥S)) with hY
  have hYfix : ∀ y ∈ Y, ∀ ψ ∈ φ.range, ψ y = y := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨e, rfl⟩
    show S2019.actQuot S ((e : ↥E) : Ω) (QuotientGroup.mk g) = QuotientGroup.mk g
    rw [S2019.actQuot_mk]
    congr 1
    apply Subtype.ext
    have h := S172X.mem_csIn.1 hg ((e : ↥E) : Ω) e.2
    simp only [MulAut.conjNormal_apply]
    calc ((e : ↥E) : Ω) * g * ((e : ↥E) : Ω)⁻¹ = g * ((e : ↥E) : Ω) * ((e : ↥E) : Ω)⁻¹ := by rw [h]
      _ = g := by group
  haveI hsolY : Group.IsSolvable ↥Y := s265f_tits_core hmodel φ.range hĒ h25 Y hYfix
  have hsolC : Group.IsSolvable ↥(S172X.csIn S E) :=
    S172X.isSolvable_of_map_le (QuotientGroup.mk' (Subgroup.center ↥S))
      (fun g hg => (QuotientGroup.eq_one_iff g).1 hg) (le_refl Y)
  haveI : Group.IsSolvable ↥((S172X.csIn S E).map S.subtype) :=
    solvable_of_surjective (f := (Subgroup.equivMapOfInjective (S172X.csIn S E) S.subtype
      S.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective (S172X.csIn S E) S.subtype S.subtype_injective).surjective
  rw [S172X.map_csIn_subtype S E] at this
  exact hlay (S172X.glaPLayer_eq_bot_of_isSolvable hp)

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
