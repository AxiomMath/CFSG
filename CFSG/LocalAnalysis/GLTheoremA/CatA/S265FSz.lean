module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FIdent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265FAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescSuzuki
public import CFSG.LocalAnalysis.EvenBN.GMSK.TypeDetBender
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.LocalAnalysis.GL83PartI.I713.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019A
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieReduce
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.RankThree.PartOne.K159.AutCore
public import CFSG.RankThree.PartOne.K159.AutSzIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open scoped commutatorElement

@[expose] def tySz32 : TauCeti.CFSGIndex → Prop :=
  onLie fun | .suzuki 2 => True | _ => False

@[expose] def tyTits : TauCeti.CFSGIndex → Prop :=
  onLie fun | .tits => True | _ => False

theorem tyE_split {S : Type} [Group S] (h : catalogIs S tyE) :
    catalogIs S tySz32 ∨ catalogIs S tyTits := by
  obtain ⟨i, hi, he⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | suzuki m =>
      left
      have hm : m = 2 := by
        rcases m with _ | _ | _ | m <;> first | rfl | (exfalso; exact hi)
      subst hm
      exact ⟨.lie ⟨.suzuki 2, hv⟩, trivial, he⟩
    | tits =>
      right
      exact ⟨.lie ⟨.tits, hv⟩, trivial, he⟩
    | _ => exact hi.elim

private theorem s265f_suzukiModel_of_lieModel {R : Type} [Group R] {n : ℕ}
    (h : CFSG.Blueprint.LieModel R .twistedB2 0 2 n) : SuzukiModel R 2 n := by
  rcases h with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact hS

private theorem s265f_sz32_model {R : Type} [Group R] (h : catalogIs R tySz32) : SuzukiModel R 2 5 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    cases d1 with
    | suzuki m =>
      have hm : m = 2 := by
        rcases m with _ | _ | _ | m <;> first | rfl | (exfalso; exact hi)
      subst hm
      have hS := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv
      have hL : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.suzuki 2, hv⟩).Group .twistedB2 0 2 5 :=
        Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hS⟩))
      exact s265f_suzukiModel_of_lieModel (LieModel.of_mulEquiv e.symm hL)
    | _ => exact hi.elim

section Sz


private theorem s265f_sz_aut_card_le {R : Type} [Group R] [Finite R] {f : ℕ} (hS : SuzukiModel R 2 f)
    (hZ : Subgroup.center R = ⊥) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Subgroup (MulAut R)}
    (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  have h1 := HDesc.card_le_prime_mul_inf_inner hp (HDesc.suzuki_outer_cyclic hS) hA
  obtain ⟨hel, hcard⟩ := HDesc.inner_part_elemAbelian hZ hA
  have h2 : Nat.card ↥(A ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner R) ≤ p := by
    rw [← hcard]
    exact HDesc.suzuki_rank_one hS hp hp2 _ hel
  calc Nat.card A ≤ p * Nat.card ↥(A ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner R) := h1
    _ ≤ p * p := Nat.mul_le_mul_left _ h2
    _ = p ^ 2 := (sq p).symm

end Sz

section Main


theorem s265f_not_der {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hpn : p ∣ lab.n) : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  dsimp only at hl hpn
  have key : ∀ (hnn : nn = 1), False := fun hnn => by
    rw [hnn] at hpn
    exact hp.one_lt.ne' (Nat.dvd_one.1 hpn)
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> dsimp only at h <;> subst h <;> exact key hl.2

private theorem s265f_tag_twB2 {lab : LargeEvenLabel} {R : Type} [Group R] (hM : MarkedModel lab R)
    (h3 : ¬ 3 ∣ Nat.card R) (hder : lab.tag ≠ .B2der ∧ lab.tag ≠ .G2der ∧ lab.tag ≠ .twF4der) :
    lab.tag = .twB2 := by
  by_contra htag
  obtain ⟨tg, r, nn⟩ := lab
  dsimp only at htag hder
  have hchar : markChar ⟨tg, r, nn⟩ = 2 := by
    cases tg <;> simp_all [markChar]
  have hnt : markTag ⟨tg, r, nn⟩ ≠ .twistedB2 := by
    cases tg <;> simp_all [markTag] <;> split_ifs <;> simp
  have hM' : CFSG.Blueprint.LieModel R (markTag ⟨tg, r, nn⟩) (markRank ⟨tg, r, nn⟩) 2
      (markDeg ⟨tg, r, nn⟩) := by
    unfold MarkedModel at hM
    rwa [hchar] at hM
  exact h3 (CFSG.LocalAnalysis.EvenBN.GMSK.three_dvd_card_of_lieModel hM'.admissible hM' hnt)

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem s265f_false_of_sz32 {p : ℕ} {S B T : Subgroup Ω} {x b : Ω} (cfg : QUCfg p S B T x b)
    (hp5 : p = 5) (hJ : catalogIs (PSimple p (Ipart p S b)) tySz32) : False := by
  subst hp5
  have hp := cfg.prime
  have hp2 := cfg.odd
  have hF : FieldOn 5 b S := by
    rcases cfg.prop with hF | ⟨h3, -, -⟩
    · exact hF
    · exact absurd h3 (by norm_num)
  have hbp : b ^ 5 = 1 := cfg.elem.2 b cfg.hb
  have hSzJ := s265f_sz32_model hJ
  have hSylJ := HDesc.szSylow_of_model_five hSzJ
  have hcardJ : Nat.card (PSimple 5 (Ipart 5 S b)) = 32537600 := hSylJ.card
  have hN : ¬ S265FSmallOrd (Nat.card (PSimple 5 (Ipart 5 S b))) := by
    rw [hcardJ]
    unfold S265FSmallOrd
    omega
  obtain ⟨lab, hlab, hM, hpn, hΛ', hMD⟩ := s265f_ident hp hp2 hF hbp cfg.ipart hN
  have hder := s265f_not_der hp hlab hpn
  have htag : lab.tag = .twB2 :=
    s265f_tag_twB2 (lab := ⟨lab.tag, lab.rank, lab.n / 5⟩) hMD (by rw [hcardJ]; omega) hder
  have hSz : SuzukiModel (PSimple 5 S) 2 lab.n := by
    obtain ⟨tg, r, nn⟩ := lab
    dsimp only at htag
    subst htag
    exact s265f_suzukiModel_of_lieModel (by simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hM)
  obtain ⟨hsimple, hnab⟩ := chev_pSimple_simple_nonabelian hp cfg.comp
  obtain ⟨a, c, hac⟩ := hnab
  haveI := hsimple
  have hZ : Subgroup.center (PSimple 5 S) = ⊥ := FR.center_eq_bot_of_simple_nonab hac
  obtain ⟨A, hA, hA3⟩ := qu_aut_rank' cfg
  have hle := s265f_sz_aut_card_le hSz hZ hp hp2 hA
  have : (5 : ℕ) ^ 2 < 5 ^ 3 := by norm_num
  omega

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end
