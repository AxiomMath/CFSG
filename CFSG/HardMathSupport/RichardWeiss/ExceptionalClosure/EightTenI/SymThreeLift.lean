module

public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.SymThreeCommutator
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.EightTenI.A4Of
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.PerfectCommAbelian
public import CFSG.HardMathSupport.RichardWeiss.Proving.SymThreeCore
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Local
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KerThetaTwoCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Reduction
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock blockV barM Asc81bEightFour)
open CFSG.Open (pCoreOf)
open CFSG.HardMathSupport.Cooperstein
open CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.Quasithin.EmptyFaithfulMultiple.L1547
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (inf_centralizer_blockV_le_pCoreOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem asc81bHyp_of_sylow {X S Y : Subgroup G} (hA : Asc81bHyp X S) (hYX : Y ≤ X)
    (hSY : S ≤ Y) (hSyl : ¬ 2 ∣ (S.subgroupOf Y).index) : Asc81bHyp Y S := by
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  refine ⟨⟨hSY, hA.twoRadical.2.1, ?_⟩,
    CFSG.AGLEmbedding.charTwo_of_twoCore_le hA.charTwo (hA.twoCore_le.trans hSY) hYX,
    Coordinator.cgsIn_eq_of_le hA hYX⟩
  have hSn : S ≤ Y ⊓ Subgroup.normalizer (S : Set G) := le_inf hSY Subgroup.le_normalizer
  have hSP : S ≤ pCoreOf 2 (Y ⊓ Subgroup.normalizer (S : Set G)) :=
    le_pCoreOf_of_le_normalizer hSn inf_le_right hS2
  refine le_antisymm hSP ?_
  set P := pCoreOf 2 (Y ⊓ Subgroup.normalizer (S : Set G)) with hP
  have hPY : P ≤ Y := (pCoreOf_le_self _).trans inf_le_left
  have hP2 : IsPGroup 2 ↥P := isPGroup_pCoreOf _
  have hmul := Subgroup.relIndex_mul_relIndex S P Y hSP hPY
  obtain ⟨n, hn⟩ := hP2.index (S.subgroupOf P)
  have hrel : S.relIndex P = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    apply hSyl
    have h1 : 2 ∣ S.relIndex P := by rw [hrel]; exact dvd_pow_self 2 hne
    have h2 : 2 ∣ S.relIndex P * P.relIndex Y := Dvd.dvd.mul_right h1 _
    rw [hmul] at h2
    exact h2
  rw [hn0, pow_zero] at hrel
  exact Subgroup.relIndex_eq_one.mp hrel

theorem perm3_pow_six (g : Equiv.Perm (Fin 3)) : g ^ 6 = 1 := by revert g; decide

omit [Finite G] in
theorem exists_involution_barM {Y S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSyl : ¬ 2 ∣ (S.subgroupOf Y).index)
    (e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin 3)) :
    ∃ r ∈ barM Y S, r ≠ 1 ∧ r ^ 2 = 1 := by
  have hcard : (CFSG.pCore 2 ↥Y).index = 6 := by
    have : (CFSG.pCore 2 ↥Y).index = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := rfl
    rw [this, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  have hne : barM Y S ≠ ⊥ := by
    intro hbot
    have hle : S.subgroupOf Y ≤ CFSG.pCore 2 ↥Y := by
      intro s hs
      have hmem : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) s ∈ barM Y S := ⟨s, hs, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff s).mp hmem
    have := Subgroup.index_dvd_of_le hle
    rw [hcard] at this
    exact hSyl (Nat.dvd_trans (by norm_num : 2 ∣ 6) this)
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨r, hr, fun h => hr1 (Subtype.ext h), ?_⟩
  obtain ⟨s, hs, rfl⟩ := hr
  obtain ⟨k, hk⟩ := hS2 ⟨(s : G), hs⟩
  have hsk : s ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) s) ^ 2 ^ k = 1 := by
    rw [← map_pow, hsk, map_one]
  have h6 : (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) s) ^ 6 = 1 := by
    apply e.injective
    rw [map_pow, perm3_pow_six, map_one]
  have h2 := pow_gcd_eq_one.mpr ⟨h1, h6⟩
  have hg : Nat.gcd (2 ^ k) 6 ∣ 2 := by
    have hc : Nat.Coprime (Nat.gcd (2 ^ k) 6) 3 := by
      apply Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left _ _)
      exact Nat.Coprime.pow_left k (by norm_num)
    exact hc.dvd_of_dvd_mul_right (by simpa using Nat.gcd_dvd_right (2 ^ k) 6)
  exact (orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_trans (orderOf_dvd_of_pow_eq_one h2) hg))

omit [Finite G] in
theorem isSubnormal_subgroupOf' {A B : Subgroup G} (h : CFSG.Open.IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commutator_pCore_le_blockV_of_sym3_lift
    (h84 : Asc81bEightFour) {X S L Y : Subgroup G} (hX : CFSG.Open.IsKGroup ↥X)
    (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hcen : Subgroup.center ↥(barM X L) = ⊥)
    (hYM : Y ≤ L ⊔ S) (hSY : S ≤ Y) (hSyl : ¬ 2 ∣ (S.subgroupOf Y).index)
    (hS3 : Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* Equiv.Perm (Fin 3)))
    {y : G} (hyL : y ∈ L) (hyY : y ∈ Y) (hy : Odd (orderOf y))
    (hyQ : y ∉ pCoreOf 2 (L ⊔ S)) :
    ⁅pCoreOf 2 (L ⊔ S), L⁆ ≤ blockV S L := by
  obtain ⟨e⟩ := hS3
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have hLs : CFSG.AGLEmbedding.IsTwoPrimeComponent (L ⊔ S) L :=
    CFSG.HardMathSupport.Cooperstein.Proving.isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent
      hA.twoRadical.1 hA.twoRadical.isPGroup hSL
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hYX : Y ≤ X := hYM.trans (sup_le hL.le hA.twoRadical.1)
  have hAY : Asc81bHyp Y S := asc81bHyp_of_sylow hA hYX hSY hSyl
  have hKY : CFSG.Open.IsKGroup ↥Y := CFSG.AGLEmbedding.AscEightFour.isKGroup_mono hX hYX
  obtain ⟨r, hrR, hr1, hr2⟩ := exists_involution_barM hS2 hSyl e
  have hnot := CFSG.HardMathSupport.RichardWeiss.Proving.not_pPrimeCore_le_centralizer_of_sym3 e
    (R := barM Y S) hrR hr1 hr2
  rcases h84 G Y S hKY hAY with h | ⟨A, hAY', hAsub, ⟨e4⟩⟩
  · exact absurd h hnot
  have hsub : (A.subgroupOf Y).IsSubnormal := isSubnormal_subgroupOf' hAsub
  have hidx : ∃ k : ℕ, (A.subgroupOf Y).index = 2 ^ k := by
    have hpc : (CFSG.pCore 2 ↥Y).index = 6 := by
      have : (CFSG.pCore 2 ↥Y).index = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := rfl
      rw [this, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
      rfl
    obtain ⟨c, hc⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
    have h1 := Subgroup.card_mul_index (CFSG.pCore 2 ↥Y)
    rw [hc, hpc] at h1
    have hAc : Nat.card A = 12 := by
      rw [Nat.card_congr e4.toEquiv, Nat.card_eq_fintype_card]; decide +kernel
    have h2 := Subgroup.card_mul_index (A.subgroupOf Y)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY').toEquiv, hAc, ← h1] at h2
    have h3 : (A.subgroupOf Y).index ∣ 2 ^ c := ⟨2, by omega⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
    exact ⟨k, hk⟩
  have hyA : y ∈ A := by
    have hodd : Odd (orderOf (⟨y, hyY⟩ : ↥Y)) := by rw [Subgroup.orderOf_mk]; exact hy
    exact mem_of_isSubnormal_of_odd hsub hidx hodd
  obtain ⟨Q₄, hI, hQ₄⟩ := exists_isA4_of_mulEquiv e4
  have hZ : Subgroup.center ↥(barM (L ⊔ S) L) = ⊥ := by
    let eq := CFSG.HardMathSupport.Cooperstein.Proving.barMEquiv hL.le
      (le_sup_left : L ≤ L ⊔ S) (Coordinator.inf_pCoreOf_eq_inf_pCoreOf_sup hA hL hSL)
    have h1 := CFSG.HardMathSupport.Cooperstein.Proving.card_center_eq_of_mulEquiv eq
    rw [hcen, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1
  set M : Subgroup G := L ⊔ S with hMdef
  set V : Subgroup G := blockV S L with hVdef
  set Qm : Subgroup G := pCoreOf 2 M with hQmdef
  have hQS : Qm ≤ S := Coordinator.twoCore_sup_le hA hL hSL
  have hQ2 : IsPGroup 2 Qm := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hQY : Qm ≤ Y := hQS.trans hSY
  have hYQ : Y ≤ Subgroup.normalizer (Qm : Set G) :=
    hYM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
  have hyM : y ∈ M := (le_sup_left : L ≤ M) hyL
  have hAQ : ¬ A ≤ Subgroup.centralizer (Qm : Set G) := by
    intro h
    exact hyQ (hA'.charTwo ⟨hyM, h hyA⟩)
  have hcommQ : ⁅Qm, A⁆ = Q₄ :=
    commutator_eq_of_isSubnormal hI hQ₄ hAY' hsub hQY hYQ hQ2 hAQ
  have hVS : V ≤ S :=
    (CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _).trans hQS
  have hVY : V ≤ Y := hVS.trans hSY
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) :=
    hYM.trans (Coordinator.sup_le_normalizer_blockV S L)
  have hV2 : IsPGroup 2 V := hS2.to_le hVS
  have hAV : ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    exact hyQ (inf_centralizer_blockV_le_pCoreOf hA' hLs hSL
      (Coordinator.not_le_centralizer_blockV hA hL hSL) hZ ⟨hyM, h hyA⟩)
  have hcommV : ⁅V, A⁆ = Q₄ :=
    commutator_eq_of_isSubnormal hI hQ₄ hAY' hsub hVY hYV hV2 hAV
  have hQ₄V : Q₄ ≤ V := by
    rw [← hcommV]
    exact commutator_le_of_le_normalizer' (fun a ha => hYV (hAY' ha))
  refine commutator_pCore_le_blockV_of_elt hX hA hL hcen hyL (k := 0) (by simpa using hyQ) ?_
  intro q hq
  simp only [pow_zero, pow_one]
  exact hQ₄V (hcommQ ▸ Subgroup.commutator_mem_commutator hq hyA)

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

end
