module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S9.InputsClosing
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47LThree
import CFSG.RankThree.PartTwo.Sec4.Item47SpFour
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.Walter.Bender1970.S3.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265D

open CFSG.Open CFSG.Fischer CFSG.StandardType CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.ComponentClassification

private abbrev P6 : Type := LargeEvenProj (LargeEvenSUGroup (Fin 6) F4 (2 ^ 1))

private theorem two_power_mem_range_conj (t : MulAut P6)
    (ht : t ∈ InndiagSU.inndiagU hF4 (d := 6) (by norm_num)) {m : ℕ} (hm : t ^ (2 ^ m) = 1) :
    t ∈ (MulAut.conj : P6 →* MulAut P6).range := by
  have hd : 3 ≤ 6 := by norm_num
  have hq : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard⟩ :=
    unitary_prime_form_full_semilinear_realization hF4
      (isPrimeFormGram_one (K := F4) (n := 6)) hd hq
  set e := MulAut.congr (InndiagSU.projEquiv hF4 (d := 6) (by norm_num)) with he
  have ht' : e t ∈ primeFormD hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := ht
  set u : ↥(primeFormD hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := ⟨e t, ht'⟩ with hu
  have hu1 : u ^ (2 ^ m) = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one, hu]
    change (e t) ^ (2 ^ m) = 1
    rw [← map_pow, hm, map_one])
  set q := (QuotientGroup.mk u :
    ↥(primeFormD hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) ⧸
      (OuterAutomorphisms.inner (primeFormP hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))).subgroupOf
        (primeFormD hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))) with hq'
  have hq1 : q ^ (2 ^ m) = 1 := by rw [hq', ← QuotientGroup.mk_pow, hu1]; rfl
  have h1 : orderOf q ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hq1
  have h3 : orderOf q ∣ 3 := (orderOf_dvd_natCard q).trans (by simpa using hcard)
  have h2 : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left m (by norm_num : Nat.Coprime 2 3)) h1 h3
  have hq0 : q = 1 := orderOf_eq_one_iff.1 h2
  have hmem : u ∈ (OuterAutomorphisms.inner (primeFormP hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))).subgroupOf
      (primeFormD hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :=
    (QuotientGroup.eq_one_iff u).1 hq0
  have hmem' : e t ∈ OuterAutomorphisms.inner (primeFormP hF4 ((1 : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) :=
    hmem
  have hrange := InndiagSU.range_conj_eq_comap_inner hF4 (d := 6) (by norm_num)
  exact (Subgroup.ext_iff.1 hrange t).2 hmem'

theorem exists_conj_mem_two_subgroup_S6 (T : Subgroup (MulAut S6)) (hT : IsPGroup 2 T)
    (h4 : 4 ≤ Nat.card T) : ∃ s : S6, s ≠ 1 ∧ (MulAut.conj s : MulAut S6) ∈ T := by
  have hd : 3 ≤ 6 := by norm_num
  have hq : ¬ (6 = 3 ∧ 2 ^ 1 = 2) := by norm_num
  let F : ↥T →* (F4 ≃+* F4) := (InndiagSU.fieldFactorU hF4 hd hq).comp T.subtype
  have hrange : Nat.card F.range ≤ 2 :=
    (Subgroup.card_le_card_group _).trans card_ringEquiv_F4.le
  have hmul := Subgroup.card_ker_mul_card_range F
  have hker : F.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hmul
    omega
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hker
  have hkF : F (k : ↥T) = 1 := k.2
  have hkd : ((k : ↥T) : MulAut S6) ∈ InndiagSU.inndiagU hF4 (d := 6) (by norm_num) := by
    rw [← InndiagSU.ker_fieldFactorU hF4 hd hq]
    exact hkF
  obtain ⟨m, hm⟩ := hT (k : ↥T)
  have hm' : ((k : ↥T) : MulAut S6) ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨s, hs⟩ := two_power_mem_range_conj _ hkd hm'
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    apply hk1
    apply Subtype.ext
    apply Subtype.ext
    rw [← hs]
    exact map_one _
  · rw [show (MulAut.conj s : MulAut S6) = ((k : ↥T) : MulAut S6) from hs]
    exact (k : ↥T).2

private theorem congr_conj' {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (s : X) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext y
  show e (MulAut.conj s (e.symm y)) = MulAut.conj (e s) y
  simp [MulAut.conj_apply]

private theorem s265d_isU6two_of_isU6n_one (i : TauCeti.CFSGIndex) (h : S10.isU6n 1 i) : S9.isU6two i := by
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at h
  | alternating n hn => simp [S10.isU6n, onLie] at h
  | sporadic s => simp [S10.isU6n, onLie] at h
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S10.isU6n, onLie] at h
      show q.card = 2
      rw [TauCeti.PrimePower.card_def, h.1, h.2, pow_one]
    | _ => simp [S10.isU6n, onLie] at h

theorem exists_conj_mem_two_subgroup {S₀ : Type} [Group S₀] (h : catalogIs S₀ (S10.isU6n 1))
    (T : Subgroup (MulAut S₀)) (hT : IsPGroup 2 T) (h4 : 4 ≤ Nat.card T) :
    ∃ s : S₀, s ≠ 1 ∧ (MulAut.conj s : MulAut S₀) ∈ T := by
  have h6 : catalogIs S₀ S9.isU6two := by
    obtain ⟨i, hi, he⟩ := h
    exact ⟨i, s265d_isU6two_of_isU6n_one i hi, he⟩
  obtain ⟨e⟩ := HSubT.nonempty_S6_of_isU6two h6
  have hT' : IsPGroup 2 (T.map (MulAut.congr e).toMonoidHom) := hT.map _
  have h4' : 4 ≤ Nat.card (T.map (MulAut.congr e).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective]
    exact h4
  obtain ⟨s, hs1, hsT⟩ := exists_conj_mem_two_subgroup_S6 _ hT' h4'
  obtain ⟨t, htT, hts⟩ := hsT
  refine ⟨e.symm s, fun h1 => hs1 ?_, ?_⟩
  · simpa using congrArg e h1
  · have : t = MulAut.conj (e.symm s) := by
      apply (MulAut.congr e).injective
      rw [congr_conj', MulEquiv.apply_symm_apply]
      exact hts
    rw [← this]
    exact htT

end CFSG.LocalAnalysis.GLTheoremA.S265D

end
