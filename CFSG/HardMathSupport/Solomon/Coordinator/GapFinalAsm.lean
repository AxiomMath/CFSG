module

public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalAsmCard
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BSL34Sylow
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Proof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance

section Orders

theorem not_isLThreeFour_of_isMJRType
    {G : Type} [Group G] [Finite G]
    {X I : Subgroup G} (hI : GLAPComponent 3 X I) (hL34 : IsLThreeFour (↥I ⧸ oPrimeP 3 ↥I))
    (hmjr : IsMJRType (barOf 3 I)) : False := by
  have h2 := card_of_isLThreeFour (Lemma510iiNs.isLThreeFour_barOf_center hI hL34)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (barOf 3 I))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Lemma510iiNs.isPGroup_center_barOf I).exists_card_eq
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨t, ht⟩ : ∃ t, t = 3 ^ k := ⟨_, rfl⟩
  rw [← ht] at hodd hk
  rw [h2, hk] at h3
  have h4 := card_of_isMJRType hmjr
  have h5 : t % 2 = 1 := Nat.odd_iff.1 hodd
  omega

theorem not_isHatON_of_isMJRType
    (hOG : UniquenessMaximal.InputONGroup) {X : Type*} [Group X] (hX : IsHatON X)
    (hmjr : IsMJRType X) : False := by
  have h1 := (UniquenessMaximal.isSimple_card_of_isHatON hOG hX).2
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  rw [h1, hX.2.1] at h3
  have h4 := card_of_isMJRType hmjr
  unfold orderON at h3
  omega

end Orders

theorem mem_centralizerQuot_of_mem_zpowers {G : Type} [Group G] [Finite G] {a b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hab : a ∈ Subgroup.zpowers b) (ha1 : a ≠ 1)
    {I : Subgroup G} (hI : I ≤ Subgroup.centralizer ({a} : Set G)) :
    b ∈ centralizerQuot I (GLAPPrimeCoreOf 3 I) := by
  have ha3 : a ^ 3 = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hab
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hab)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hbo])
  have hba : b ∈ Subgroup.zpowers a := heq ▸ Subgroup.mem_zpowers b
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hba
  refine Lemma59Ns.mem_cq_of_centralizes fun x hx => ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.1 (hI hx)).symm k).eq).symm

theorem not_isUpsilonComponent_of_isMJRType
    (hR3 : GapFinalBalance) (h31 : Lemma31) (h191 : Lemma59Ns.Input19_1_3)
    (hOG : UniquenessMaximal.InputONGroup) {G : Type} [Group G] [Finite G] {m : ℕ}
    (hSt : GLStanding G m 3) {B' : Subgroup G} (hB' : IsBOneMax 3 B') {a : G} (ha : a ∈ B')
    (ha1 : a ≠ 1) {I : Subgroup G} (hI : IsUpsilonComponent B' a I)
    (hmjr : IsMJRType (barOf 3 I)) : False := by
  have hIc := hI.1
  rcases hI.2 with ⟨hle, hnpsi⟩ | ⟨D, hD, hnc⟩
  · have hsc : IsSCp 3 ⊤ B' := lemma23_proved G m 3 hSt B' hB'
    have hnb := Lemma59Ns.not_balanced_of_le_lambdaOf hIc hle
    rcases h31 G m 3 hSt B' hB'.1 hsc a ha ha1 I hIc with h | h | h | h | h
    · exact hnb h
    · exact hnpsi (Lemma59Ns.le_psiStarGroup_of_inGOne ha ha1 hIc hnb h)
    · exact not_isLThreeFour_of_isMJRType hIc h.2.2.1 hmjr
    · exact not_isHatON_of_isMJRType hOG h.2.2.1 hmjr
    · exact absurd h.1 (by norm_num)
  · have := hSt.simple
    have hbal : IsCompLocallyBalanced 3 2 B' I := (hR3 _ hmjr).isLocallyBalanced _
    exact hnc (h191 G hSt.nonabelian hSt.kProper 3 Nat.prime_three B' hB'.1.1 2 (by norm_num) D hD
      a ha ha1 I hIc hbal)

theorem gapFinal_of_setup
    (hSetup : GapFinalSetup) (hR2 : GapFinalKType) (hR3 : GapFinalBalance) (h31 : Lemma31)
    (h191 : Lemma59Ns.Input19_1_3) (hOG : UniquenessMaximal.InputONGroup) :
    Lemma59Ns.Gap_Final := by
  intro G _ _ m hSt hC B' hB' b hb hb1 L hL hON hbL hBN a ha ha1 I hI
  have hb3 : b ^ 3 = 1 := hB'.1.1.2 b hb
  by_cases hab : a ∈ Subgroup.zpowers b
  · exact mem_centralizerQuot_of_mem_zpowers hb3 hb1 hab ha1 hI.1.1
  obtain ⟨J, hJ, hJty, hbJ, hK⟩ := hSetup G m hSt hC B' hB' b hb hb1 L hL hON hbL hBN a ha hab
  have hJK : J ≤ Lemma512Ns.conjHull a J := by
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) =>
      GLBConj g J) 1 (one_mem _)
    rwa [gLBConj_one] at this
  by_cases hIK : I = Lemma512Ns.conjHull a J
  · subst hIK
    rcases hR2 G m hSt hC B' hB' b hb hb1 L hL hON hbL hBN a ha hab J hJ hJty hbJ hK with h | h
    · exact Prop51Ns.oPrimePOf_le_centralizerQuot Nat.prime_three hK h
    · exact (not_isUpsilonComponent_of_isMJRType hR3 h31 h191 hOG hSt hB' ha ha1 hI h).elim
  · exact mem_centralizerQuot_of_ne Nat.prime_three hI.1 hK hIK (hJK hbJ)

end CFSG.HardMathSupport.Solomon.Coordinator
