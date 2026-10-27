module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4EFrame
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports LevelLieSp4E
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def KDLieRowSp4EightField : Prop :=
  ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid), q.card = 8 →
    ∀ α : MulAut (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group, α ^ 3 = 1 →
      α ∉ (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group →* _).range →
      ∀ I : Subgroup (TauCeti.CFSGIndex.lie ⟨.B 2 q, hv⟩).Group,
        GLAPComponent 3 (fixSubgroup α) I → kLevel 3 (PSimple 3 I) ≤ 2

@[expose] def KDLieRowSp4EightFreeBlock : Prop :=
  ∀ A : ↥(StatedSp 2 (GaloisField 2 3)), A ^ 3 = 1 → Pm (mat A) = 0 →
    ∀ I : Subgroup ↥(StatedSp 2 (GaloisField 2 3)),
      GLAPComponent 3 (Subgroup.centralizer ({A} : Set ↥(StatedSp 2 (GaloisField 2 3)))) I →
        kLevel 3 (PSimple 3 I) ≤ 2

end CFSG.LocalAnalysis.GLTheoremA

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E

open CFSG.Open CFSG.Open.StatedAPI CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.Assembly.LowTwoRank CFSG.Adapters.RankTwoModelTransports
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem not_comm_H : ¬ IsMulCommutative ↥(StatedSp 2 (GaloisField 2 3)) := by
  intro h
  apply not_comm_D0 (K := GaloisField 2 3)
  exact ⟨⟨fun a b => Subtype.ext (h.is_comm.comm (a : ↥(StatedSp 2 (GaloisField 2 3))) b)⟩⟩


theorem charP_two_of_card_eight (K : Type) [Field K] [Fintype K] (h : Fintype.card K = 8) :
    CharP K 2 := by
  obtain ⟨p, hc, n, hp, hn⟩ := FiniteField.card' K
  have h8 : p ∣ 8 := by
    rw [← h, hn]
    exact dvd_pow_self p (PNat.ne_zero n)
  have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by norm_num; exact h8)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  subst hp2
  exact hc

theorem bridge_B2 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.B 2 q).Valid)
    (hq : q.card = 8) :
    Nonempty ((TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group ≃*
      ↥(StatedSp 2 (GaloisField 2 3))) := by
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 3) (by norm_num)
    (hq.trans (by norm_num))
  rcases CFSG.Models.lieModel_B 2 q hv (MulEquiv.refl _) with hm | hm
  · rw [h1, h2] at hm
    obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
    haveI : Fintype K := Fintype.ofFinite K
    haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite (GaloisField 2 3)
    haveI : CharP K 2 := charP_two_of_card_eight K (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 3) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
        GaloisField.card 2 3 (by norm_num)]
    let φ : K ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq hcard
    let eP : StatedProj (StatedSp 2 K) ≃* ↥(StatedSp 2 (GaloisField 2 3)) :=
      (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSp_eq_bot (n := 2) (K := K))).trans
        (QuotientGroup.quotientBot.trans
          ((MulEquiv.subgroupMap (glCongr (ι := Fin 2 ⊕ Fin 2) φ) (StatedSp 2 K)).trans
            (MulEquiv.subgroupCongr (glCongr_statedSp φ 2))))
    exact ⟨e'.trans eP⟩
  · exact absurd (show 3 ≤ 2 from hm.admissible.2.2.1) (by norm_num)


theorem fixSubgroup_conj_eq {G : Type} [Group G] (s : G) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer {s} := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have : s * x = x * s := by
      calc s * x = s * x * s⁻¹ * s := by group
        _ = x * s := by rw [h]
    exact this.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem center_eq_bot_of_simple' {G : Type} [Group G] [IsSimpleGroup G] (hnc : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a ∈ Subgroup.center G := by
      rw [h]
      exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem eq_one_of_conj_eq_one' {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) {z : G}
    (h : MulAut.conj z = 1) : z = 1 := by
  have hz : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut G => φ g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  rw [hZ, Subgroup.mem_bot] at hz
  exact hz

theorem eq_one_of_Pm_eq_one {K : Type} [Field K] [CharP K 2] {A : ↥(StatedSp 2 K)}
    (hP : Pm (mat A) = 1) : A = 1 := by
  have h1 : mat A * mat A + mat A = 0 := by
    have h := hP
    unfold Pm at h
    have := congrArg (fun M : Matrix Ix Ix K => M - 1) h
    simpa using this
  have h2 : mat A * (mat A + 1) = 0 := by
    rw [mul_add, mul_one]
    exact h1
  have hinv : (((A⁻¹ : ↥(StatedSp 2 K)) : GL Ix K) : Matrix Ix Ix K) * mat A = 1 := by
    simp [mat]
  have h3 : mat A + 1 = 0 := by
    calc mat A + 1 = (((A⁻¹ : ↥(StatedSp 2 K)) : GL Ix K) : Matrix Ix Ix K) * (mat A * (mat A + 1)) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = 0 := by rw [h2, mul_zero]
  have h4 : mat A = 1 := by
    have h5 : mat A = -1 := eq_neg_of_add_eq_zero_left h3
    rw [h5, CharTwo.neg_eq]
  apply Subtype.ext
  apply Units.ext
  exact h4

theorem Pm_ne_one_of_ne_one {K : Type} [Field K] [CharP K 2] {A : ↥(StatedSp 2 K)} (hA1 : A ≠ 1) :
    Pm (mat A) ≠ 1 :=
  fun hP => hA1 (eq_one_of_Pm_eq_one hP)

theorem isSimple_H : IsSimpleGroup ↥(StatedSp 2 (GaloisField 2 3)) := by
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have h4 : 4 ≤ Nat.card (GaloisField 2 3) := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  exact CFSG.SeitzReduction.SymplecticPilot.isSimpleGroup_statedSp h4 (by norm_num)

theorem downLe_of_parts {S : Type} [Group S] (e : S ≃* ↥(StatedSp 2 (GaloisField 2 3)))
    (hB : KDLieRowSp4EightFreeBlock) (hS : catalogIs S (k2 3))
    (hout : ∀ α : MulAut S, α ^ 3 = 1 → α ∉ (MulAut.conj : S →* MulAut S).range →
      ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup α) I → kLevel 3 (PSimple 3 I) ≤ 2) :
    DownLe 3 2 S := by
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hK : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have hcard : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  haveI : Finite S := Finite.of_equiv _ e.symm.toEquiv
  haveI : IsSimpleGroup ↥(StatedSp 2 (GaloisField 2 3)) := isSimple_H
  haveI : IsSimpleGroup S := e.isSimpleGroup
  have hnc : ¬ IsMulCommutative S := not_comm_of_mulEquiv e not_comm_H
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_simple' hnc
  have h3S : 3 ∣ Nat.card S := by
    rw [Nat.card_congr e.toEquiv]
    have h := Subgroup.card_subgroup_dvd_card (D0 (GaloisField 2 3))
    rw [card_D0 hK] at h
    exact (by norm_num : 3 ∣ 504).trans h
  intro α hα I hI
  by_cases hin : α ∈ (MulAut.conj : S →* MulAut S).range
  · obtain ⟨s, rfl⟩ := hin
    rw [fixSubgroup_conj_eq] at hI
    have hs3 : s ^ 3 = 1 := by
      apply eq_one_of_conj_eq_one' hZ
      rw [map_pow]
      exact hα
    by_cases hs1 : s = 1
    · subst hs1
      have htop : Subgroup.centralizer ({(1 : S)} : Set S) = ⊤ := by
        apply (Subgroup.eq_top_iff' _).2
        intro x
        rw [Subgroup.mem_centralizer_singleton_iff]
        simp
      rw [htop] at hI
      have hIt : I = ⊤ := by
        rcases CFSG.Open.IsSubnormal.eq_bot_or_top hI.2.1 with h | h
        · exact absurd h (glaPComponent_ne_bot' hI)
        · exact h
      haveI : IsSimpleGroup (⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
      have h3top : 3 ∣ Nat.card (⊤ : Subgroup S) := by
        rw [Subgroup.card_top]
        exact h3S
      have hnctop : ¬ IsMulCommutative (⊤ : Subgroup S) :=
        not_comm_of_mulEquiv Subgroup.topEquiv hnc
      obtain ⟨eP⟩ := pSimple_equiv_of_simple' (⊤ : Subgroup S) hnctop h3top
      rw [hIt, kLevel_congr 3 eP, kLevel_congr 3 Subgroup.topEquiv]
      exact kLevel_le_two_of_k2' hS
    · have hI' := glaPComponent_map_mulEquiv Nat.prime_three e hI
      rw [map_centralizer_equiv'] at hI'
      have hs'3 : (e s) ^ 3 = 1 := by
        rw [← map_pow, hs3, map_one]
      have hs'1 : e s ≠ 1 := fun h => hs1 (e.injective (h.trans (map_one e).symm))
      have hk : kLevel 3 (PSimple 3 (I.map e.toMonoidHom)) ≤ 2 := by
        by_cases h0 : Pm (mat (e s)) = 0
        · exact hB (e s) hs'3 h0 _ hI'
        · exact typeA_kLevel hK hs'3 h0 (Pm_ne_one_of_ne_one hs'1) hI'
      obtain ⟨eI⟩ := pSimple_map_equiv' 3 e I
      rw [← kLevel_congr 3 eI]
      exact hk
  · exact hout α hα hin I hI

theorem kdLieRowSp4Eight_of_residuals (hF : KDLieRowSp4EightField)
    (hB : KDLieRowSp4EightFreeBlock) : KDLieRowSp4Eight := by
  intro q hv hq
  obtain ⟨e⟩ := bridge_B2 q hv hq
  have hS : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩).Group (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩, ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  exact downLe_of_parts e hB hS (hF q hv hq)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4E
