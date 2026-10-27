module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511B
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftBasic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Oracles
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K3DvdL3
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.CharacterTheory.Wreathed.SmallerRecognitionOriginalFieldQuaternionConjugation
import CFSG.ClassicalGroups
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.Open.SplitBNPair
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.E3OffenderB
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.InternalSecData
import CFSG.Quasithin.Background.InternalSecIso
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch10SecD33
import CFSG.Quasithin.Vol2.Ch10SecDClA
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Main
import CFSG.Quasithin.Vol2.Ch11SecA14Conj
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts04
import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
import CFSG.Quasithin.Vol2.Ch11SecAViN13
import CFSG.Quasithin.Vol2.Ch11SecBDerived35
import CFSG.Quasithin.Vol2.Ch11SecBL2ODone
import CFSG.Quasithin.Vol2.Ch11SecBL2UOver
import CFSG.Quasithin.Vol2.Ch11SecBTCStar
import CFSG.Quasithin.Vol2.Ch11SecCFacts
import CFSG.Quasithin.Vol2.Ch11SecCFacts2
import CFSG.Quasithin.Vol2.Ch11SecSMain
import CFSG.Quasithin.Vol2.Ch11SecSShape2
import CFSG.Quasithin.Vol2.Ch11SecSSym2
import CFSG.Quasithin.Vol2.Ch11SecSSym4
import CFSG.Quasithin.Vol2.Ch11SecSSym5
import CFSG.Quasithin.Vol2.Ch11StatementsE
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
import CFSG.Quasithin.Vol2.KGNatCoord
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.M22

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open scoped commutatorElement

theorem exists_Y_O2form_aux_residual {G Z : Type} [Group G] [Finite G] [Group Z] (f : G →* Z)
    (H : Subgroup G) (hH : ⁅H.map f, H.map f⁆ = H.map f) :
    ∃ E : Subgroup G, E ≤ H ∧ ⁅E, E⁆ = E ∧ E.map f = H.map f ∧ (H.Normal → E.Normal) := by
  let c : Subgroup G → Subgroup G := fun K => ⁅K, K⁆
  let a : ℕ → Subgroup G := fun n => c^[n] H
  have hfle : ∀ K, c K ≤ K := fun K => Subgroup.commutator_le_of_le (le_refl K) (le_refl K)
  have hsucc : ∀ n, a (n + 1) = c (a n) := fun n => Function.iterate_succ_apply' c n _
  have hanti : ∀ n, a (n + 1) ≤ a n := fun n => by rw [hsucc]; exact hfle _
  have hle : ∀ n, a n ≤ H := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (hanti n).trans ih
  have hmap : ∀ n, (a n).map f = H.map f := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [hsucc]
      change (⁅a n, a n⁆).map f = H.map f
      rw [Subgroup.map_commutator, ih]
      exact hH
  have hnorm : H.Normal → ∀ n, (a n).Normal := by
    intro hHn n
    induction n with
    | zero => exact hHn
    | succ n ih =>
      rw [hsucc]
      haveI := ih
      exact Subgroup.commutator_normal _ _
  obtain ⟨m, k, hmk, hk⟩ := Finite.exists_ne_map_eq_of_infinite a
  have hanti' : Antitone a := antitone_nat_of_succ_le hanti
  have hstab : ∃ n, a (n + 1) = a n := by
    rcases lt_or_gt_of_ne hmk with h | h
    · exact ⟨m, le_antisymm (hanti m) (hk ▸ hanti' (Nat.succ_le_of_lt h))⟩
    · exact ⟨k, le_antisymm (hanti k) (hk.symm ▸ hanti' (Nat.succ_le_of_lt h))⟩
  obtain ⟨n, hn⟩ := hstab
  exact ⟨a n, hle n, (hsucc n).symm.trans hn, hmap n, fun hHn => hnorm hHn n⟩

theorem exists_Y_O2form_aux_comm_top {Y : Type*} [Group Y] {H : Subgroup Y} (h : ⁅H, H⁆ = H) :
    commutator ↥H = ⊤ :=
  Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 h)

theorem exists_Y_O2form_aux_perfect_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (h : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h' | h'
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h']
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · exact h'

open KFactsPair in
theorem exists_Y_O2form_aux_core {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    (h : HasLThreeCore A) :
    ∃ A₀ : Subgroup Y, A₀ ≤ A ∧ ⁅A₀, A₀⁆ = A₀ ∧
      IsLThreeOdd (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) ∧
      ∃ a b : ↥A₀ ⧸ CFSG.pCore 2 ↥A₀, a * b ≠ b * a := by
  classical
  set π : ↥A →* ↥A ⧸ CFSG.pCore 2 ↥A := QuotientGroup.mk' (CFSG.pCore 2 ↥A) with hπ
  set W : Subgroup (↥A ⧸ CFSG.pCore 2 ↥A) := pElementSubgroup 2 ⊤ with hW
  have hWn : W.Normal := R1511C.pElementSubgroup_top_normal 2
  have h2 : IsLThreeTwoPow ↥W := R1511C.isLThreeTwoPow_of_isLThreeOdd h
  haveI hWs : IsSimpleGroup ↥W := R1511C.isSimpleGroup_of_isLThreeTwoPow h2
  have hnc : ∃ a b : ↥W, a * b ≠ b * a :=
    R1511C.exists_noncomm_of_simple_of_dvd (K3DvdL3_holds _ h2) R1511C.closure_two_elements_eq_top
  have hWperf : ⁅W, W⁆ = W :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (exists_Y_O2form_aux_perfect_of_simple hnc))
  have hmapA : (W.comap π).map π = W :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) W
  obtain ⟨E, hEA, hEperf, hEmap, hEnorm⟩ :=
    exists_Y_O2form_aux_residual π (W.comap π) (by rw [hmapA]; exact hWperf)
  haveI hEn : E.Normal := hEnorm (Subgroup.Normal.comap hWn π)
  let ψ : ↥E →* ↥W := (π.comp E.subtype).codRestrict W (fun e => hEA e.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨w, hw⟩
    have hw' : w ∈ E.map π := by rw [hEmap, hmapA]; exact hw
    obtain ⟨e, he, rfl⟩ := hw'
    exact ⟨⟨e, he⟩, rfl⟩
  have hker : ψ.ker = CFSG.pCore 2 ↥E := by
    refine le_antisymm ?_ ?_
    · intro e he
      have h1 : π e = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 he)
      have h3 : (e : ↥A) ∈ CFSG.pCore 2 ↥A := (QuotientGroup.eq_one_iff (e : ↥A)).1 h1
      haveI : ((CFSG.pCore 2 ↥A).subgroupOf E).Normal :=
        Subgroup.Normal.subgroupOf CFSG.pCore_normal E
      have hN2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥A).subgroupOf E) :=
        (CFSG.pCore_isPGroup (p := 2) (G := ↥A)).comap_subtype
      exact isC2_normalizer_aux0 hN2 (Subgroup.mem_subgroupOf.2 h3)
    · intro e he
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h1 : (e : ↥A) ∈ CFSG.pCore 2 ↥A := pElement_quot_equiv_aux2 hEn ⟨e, he, rfl⟩
      exact (QuotientGroup.eq_one_iff (e : ↥A)).2 h1
  let eE : (↥E ⧸ CFSG.pCore 2 ↥E) ≃* ↥W :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hEL : IsLThreeOdd (↥E ⧸ CFSG.pCore 2 ↥E) := R1511C.isLThreeOdd_of_equiv eE h
  have hEnc : ∃ a b : ↥E ⧸ CFSG.pCore 2 ↥E, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨eE.symm a, eE.symm b, fun hh => hab (eE.symm.injective (by rw [map_mul, map_mul, hh]))⟩
  let eA : ↥E ≃* ↥(E.map A.subtype) := E.equivMapOfInjective A.subtype A.subtype_injective
  let eA' : (↥E ⧸ CFSG.pCore 2 ↥E) ≃*
      (↥(E.map A.subtype) ⧸ CFSG.pCore 2 ↥(E.map A.subtype)) :=
    QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA)
  refine ⟨E.map A.subtype, Subgroup.map_subtype_le E, ?_, R1511C.isLThreeOdd_of_equiv eA'.symm hEL,
    ?_⟩
  · rw [← Subgroup.map_commutator, hEperf]
  · obtain ⟨a, b, hab⟩ := hEnc
    exact ⟨eA' a, eA' b, fun hh => hab (eA'.injective (by rw [map_mul, map_mul, hh]))⟩

theorem exists_Y_O2form_aux_eq_top {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    (hS : IsSimpleGroup (G ⧸ CFSG.pCore 2 G)) (h3 : 3 ∣ Nat.card G) (M : Subgroup G) [M.Normal]
    (hM : ∀ g : G, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ M) : M = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect G := Group.isPerfect_def.2 hperf
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hgM : g ∈ M := hM g ⟨1, by simpa using hg⟩
  have hgR : g ∉ CFSG.pCore 2 G := by
    intro hgR
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)) ⟨g, hgR⟩
    have h1 : orderOf g ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    rw [hg] at h1
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
    omega
  have hMR : M ⊔ CFSG.pCore 2 G = ⊤ := by
    have hnorm : (M.map (QuotientGroup.mk' (CFSG.pCore 2 G))).Normal :=
      Subgroup.Normal.map ‹M.Normal› _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (M.map (QuotientGroup.mk' (CFSG.pCore 2 G))) with h | h
    · exfalso
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      exact hgR (h hgM)
    · have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 G)) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
      exact h2.symm
  by_contra hMtop
  obtain ⟨x, hx⟩ : ∃ x : G, x ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hMtop ((Subgroup.eq_top_iff' M).2 hcon)
  haveI : Nontrivial (G ⧸ M) :=
    ⟨⟨(x : G ⧸ M), 1, fun hh => hx ((QuotientGroup.eq_one_iff x).1 hh)⟩⟩
  let ρ : ↥(CFSG.pCore 2 G) →* G ⧸ M := (QuotientGroup.mk' M).comp (CFSG.pCore 2 G).subtype
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ M ⊔ CFSG.pCore 2 G := by rw [hMR]; exact Subgroup.mem_top z
    obtain ⟨m, hm, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hz
    refine ⟨⟨r, hr⟩, ?_⟩
    change ((r : G) : G ⧸ M) = ((m * r : G) : G ⧸ M)
    rw [QuotientGroup.eq]
    have h5 := Subgroup.Normal.conj_mem inferInstance m hm r⁻¹
    simpa [mul_assoc] using h5
  haveI hQ : IsPGroup 2 (G ⧸ M) := (CFSG.pCore_isPGroup (p := 2) (G := G)).of_surjective ρ hρ
  haveI : Group.IsNilpotent (G ⧸ M) := hQ.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (G ⧸ M) inferInstance

theorem exists_Y_O2form_aux_odd_two {P : Type*} [Group P] {K : Subgroup P}
    (hodd : Odd (Nat.card K)) {z : P} (hz : z ∈ K) {k : ℕ} (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf z ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk z hz]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf z = 1 := Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
  exact orderOf_eq_one_iff.1 h3

theorem exists_Y_O2form_aux_split {P A : Type} [Group P] [Finite P] [Group A] [Finite A]
    (f : P →* A) (hker : f.ker ≤ Subgroup.center P) (hodd : Odd (Nat.card f.ker))
    {O : Subgroup A} [O.Normal] (hO : IsPGroup 2 O) :
    ∃ R : Subgroup P, R.Normal ∧ IsPGroup 2 R ∧ R ≤ O.comap f ∧ O.comap f ≤ f.ker ⊔ R := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup P := O.comap f with hQ
  haveI hQn : Q.Normal := Subgroup.Normal.comap inferInstance f
  have hNle : f.ker ≤ Q := fun z hz => by
    show f z ∈ O
    rw [MonoidHom.mem_ker.1 hz]
    exact O.one_mem
  let fQ : ↥Q →* A := f.comp Q.subtype
  set N : Subgroup ↥Q := f.ker.subgroupOf Q with hN
  haveI hNn : N.Normal := (MonoidHom.normal_ker f).subgroupOf Q
  have hNk : N = fQ.ker := by
    ext z
    simp [hN, fQ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hNcard : Nat.card N = Nat.card f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNle).toEquiv
  obtain ⟨b, hb⟩ : ∃ b : ℕ, N.index = 2 ^ b := by
    have h1 : N.index = Nat.card fQ.range := hNk ▸ Subgroup.index_ker fQ
    have h2 : fQ.range ≤ O := by
      rintro _ ⟨z, rfl⟩
      exact z.2
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hO
    have h3 : Nat.card fQ.range ∣ 2 ^ n := hn ▸ Subgroup.card_dvd_of_le h2
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    exact ⟨b, h1.trans hb⟩
  have hcop : (Nat.card N).Coprime N.index := by
    rw [hb, hNcard]
    exact ((Nat.coprime_two_left.2 hodd).pow_left b).symm
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = 2 ^ b := hH.symm.index_eq_card.symm.trans hb
  have hH2 : IsPGroup 2 H := IsPGroup.iff_card.2 ⟨b, hHcard⟩
  have hdec : ∀ x : ↥Q, ∃ n ∈ N, ∃ h ∈ H, n * h = x := fun x =>
    Subgroup.mem_sup_of_normal_left.1 (by rw [hH.sup_eq_top]; exact Subgroup.mem_top x)
  have hHpow : ∀ z ∈ H, z ^ 2 ^ b = 1 := fun z hz => by
    have h1 := pow_card_eq_one' (x := (⟨z, hz⟩ : ↥H))
    rw [hHcard] at h1
    simpa using congrArg Subtype.val h1
  refine ⟨H.map Q.subtype, ⟨fun r hr g => ?_⟩, hH2.map _, Subgroup.map_subtype_le H, ?_⟩
  · obtain ⟨h₀, hh₀, rfl⟩ := hr
    have hy : g * (h₀ : P) * g⁻¹ ∈ Q := hQn.conj_mem _ h₀.2 g
    obtain ⟨n, hn, h', hh', hnh⟩ := hdec ⟨g * (h₀ : P) * g⁻¹, hy⟩
    have hnker : (n : P) ∈ f.ker := hn
    have hcomm : Commute (n : P) (h' : P) :=
      (Subgroup.mem_center_iff.1 (hker hnker) (h' : P)).symm
    have hyP : (n : P) * (h' : P) = g * (h₀ : P) * g⁻¹ := congrArg Subtype.val hnh
    have h1 : (n : P) ^ 2 ^ b = 1 := by
      have h2 : (g * (h₀ : P) * g⁻¹) ^ 2 ^ b = 1 := by
        rw [conj_pow]
        have h3 : (h₀ : P) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val (hHpow h₀ hh₀)
        rw [h3]
        simp
      rw [← hyP, hcomm.mul_pow] at h2
      have h4 : (h' : P) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val (hHpow h' hh')
      rwa [h4, mul_one] at h2
    have hn1 : (n : P) = 1 := exists_Y_O2form_aux_odd_two hodd hnker h1
    refine ⟨h', hh', ?_⟩
    rw [hn1, one_mul] at hyP
    exact hyP
  · intro x hx
    obtain ⟨n, hn, h, hh, hnh⟩ := hdec ⟨x, hx⟩
    have hxP : (n : P) * (h : P) = x := congrArg Subtype.val hnh
    rw [← hxP]
    exact Subgroup.mul_mem_sup (show (n : P) ∈ f.ker from hn) ⟨h, hh, rfl⟩

theorem exists_Y_O2form_aux_central {P A : Type} [Group P] [Finite P] [Group A] [Finite A]
    (f : P →* A) (hf : Function.Surjective f) (hP : commutator P = ⊤)
    (hker : f.ker ≤ Subgroup.center P) (hodd : Odd (Nat.card f.ker))
    (hS : IsSimpleGroup (A ⧸ CFSG.pCore 2 A))
    (hnc : ∃ a b : A ⧸ CFSG.pCore 2 A, a * b ≠ b * a)
    (hSM : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Odd (Nat.card (Subgroup.center K)) →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (A ⧸ CFSG.pCore 2 A)) →
      Nat.card (Subgroup.center K) = 1) :
    f.ker = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup A := CFSG.pCore 2 A with hO
  obtain ⟨R, hRn, hR2, hRQ, hQR⟩ :=
    exists_Y_O2form_aux_split f hker hodd (O := O) (CFSG.pCore_isPGroup (p := 2) (G := A))
  haveI := hRn
  let fb : P ⧸ R →* A ⧸ O := QuotientGroup.map R O f hRQ
  have hfb : Function.Surjective fb := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := hf a
    exact ⟨(x : P ⧸ R), rfl⟩
  have hdec : ∀ x : P, (x : P ⧸ R) ∈ fb.ker → ∃ z ∈ f.ker, (x : P ⧸ R) = (z : P ⧸ R) := by
    intro x hx
    have h1 : f x ∈ O := by
      have := MonoidHom.mem_ker.1 hx
      change ((f x : A) : A ⧸ O) = 1 at this
      exact (QuotientGroup.eq_one_iff _).1 this
    obtain ⟨z, hz, r, hr, hzr⟩ :=
      Subgroup.mem_sup_of_normal_right.1 (hQR (show x ∈ O.comap f from h1))
    refine ⟨z, hz, ?_⟩
    rw [← hzr, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff r).2 hr, mul_one]
  have hcen : fb.ker ≤ Subgroup.center (P ⧸ R) := by
    intro k hk
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
    obtain ⟨z, hz, hxz⟩ := hdec x hk
    rw [hxz, Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hker hz) y']
  have hZ : fb.ker = Subgroup.center (P ⧸ R) := by
    refine lift_inf_gnC_le_pCore_of_U4_aux1 fb hfb hcen ?_
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (A ⧸ O)) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)
  let eK : ((P ⧸ R) ⧸ Subgroup.center (P ⧸ R)) ≃* (A ⧸ O) :=
    (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective fb hfb)
  haveI : Group.IsPerfect P := Group.isPerfect_def.2 hP
  haveI := hS
  have hqs : CFSG.Open.IsQuasisimple (P ⧸ R) :=
    ⟨Group.isPerfect_def.1 inferInstance, eK.isSimpleGroup⟩
  have hoddK : Odd (Nat.card (Subgroup.center (P ⧸ R))) := by
    have hle : Subgroup.center (P ⧸ R) ≤ f.ker.map (QuotientGroup.mk' R) := by
      rw [← hZ]
      intro k hk
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective k
      obtain ⟨z, hz, hxz⟩ := hdec x hk
      exact ⟨z, hz, hxz.symm⟩
    exact Odd.of_dvd_nat hodd ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ _))
  have hcard1 : Nat.card (Subgroup.center (P ⧸ R)) = 1 := hSM (P ⧸ R) hqs hoddK ⟨eK⟩
  have hbot : Subgroup.center (P ⧸ R) = ⊥ := Subgroup.eq_bot_of_card_eq _ hcard1
  rw [eq_bot_iff]
  intro z hz
  have hzfb : (z : P ⧸ R) ∈ fb.ker := by
    rw [MonoidHom.mem_ker]
    change ((f z : A) : A ⧸ O) = 1
    rw [MonoidHom.mem_ker.1 hz]
    exact QuotientGroup.mk_one _
  have hzR : z ∈ R := by
    rw [hZ, hbot, Subgroup.mem_bot] at hzfb
    exact (QuotientGroup.eq_one_iff z).1 hzfb
  obtain ⟨k, hk⟩ := hR2 ⟨z, hzR⟩
  exact Subgroup.mem_bot.2
    (exists_Y_O2form_aux_odd_two hodd hz (by simpa using congrArg Subtype.val hk))

theorem exists_Y_O2form_aux_pCore_equiv {Y A : Type} [Group Y] [Finite Y] [Group A] [Finite A]
    (g : Y →* A) (hg : Function.Surjective g) (hk : IsPGroup 2 g.ker) :
    Nonempty ((Y ⧸ CFSG.pCore 2 Y) ≃* (A ⧸ CFSG.pCore 2 A)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomap : (CFSG.pCore 2 A).comap g = CFSG.pCore 2 Y := by
    refine le_antisymm ?_ ?_
    · haveI : ((CFSG.pCore 2 A).comap g).Normal := Subgroup.Normal.comap CFSG.pCore_normal g
      exact isC2_normalizer_aux0
        (IsPGroup.comap_of_ker_isPGroup (CFSG.pCore_isPGroup (p := 2) (G := A)) g hk)
    · rw [← Subgroup.map_le_iff_le_comap]
      haveI : ((CFSG.pCore 2 Y).map g).Normal := Subgroup.Normal.map CFSG.pCore_normal g hg
      exact isC2_normalizer_aux0 ((CFSG.pCore_isPGroup (p := 2) (G := Y)).map g)
  let ψ : Y →* A ⧸ CFSG.pCore 2 A := (QuotientGroup.mk' (CFSG.pCore 2 A)).comp g
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hg
  have hker : ψ.ker = CFSG.pCore 2 Y := by
    rw [← hcomap]
    ext y
    simp [ψ, MonoidHom.mem_ker, Subgroup.mem_comap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩

theorem exists_Y_O2form_aux_mem_normalizer {X : Type} [Group X] {L : Subgroup X} {x : X}
    (h : L.map (MulAut.conj x).toMonoidHom = L) : x ∈ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← h]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · intro hz
    rw [← h] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := by
      have h1 : x * w * x⁻¹ = x * z * x⁻¹ := by simpa [MulAut.conj_apply] using hwz
      simpa using h1
    exact this ▸ hw

theorem exists_Y_O2form_aux_pElement_mem {X : Type} [Group X] [Finite X] {L C : Subgroup X}
    [C.Normal]
    (hCL : ∀ c ∈ C, c ∈ Subgroup.normalizer (L : Set X)) (hC : ¬ 3 ∣ Nat.card C) {x : X}
    (hx : x ∈ L ⊔ C) {k : ℕ} (hk : orderOf x = 3 ^ k) : x ∈ L := by
  obtain ⟨l, hl, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx
  obtain ⟨l', hl', hpow⟩ := isC2_eq_of_barO2_eq_aux1 hl (hCL c hc) (Nat.card C)
  have hcn : c ^ Nat.card C = 1 := by
    have h1 := pow_card_eq_one' (x := (⟨c, hc⟩ : ↥C))
    have h2 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one] using h2
  rw [hcn, mul_one] at hpow
  have hxk : (l * c) ^ Nat.card C ∈ L := hpow ▸ hl'
  have hcop : Nat.Coprime (Nat.card C) (orderOf (l * c)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC).symm
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have huv' : (Nat.card C : ℤ) * u + (orderOf (l * c) : ℤ) * v = 1 := by
    rw [mul_comm (Nat.card C : ℤ) u, mul_comm (orderOf (l * c) : ℤ) v]
    exact huv
  have e : l * c = ((l * c) ^ Nat.card C) ^ u := by
    calc l * c = (l * c) ^ (1 : ℤ) := (zpow_one _).symm
      _ = (l * c) ^ ((Nat.card C : ℤ) * u + (orderOf (l * c) : ℤ) * v) := by rw [huv']
      _ = ((l * c) ^ (Nat.card C : ℤ)) ^ u * ((l * c) ^ (orderOf (l * c) : ℤ)) ^ v := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = ((l * c) ^ Nat.card C) ^ u := by
        rw [zpow_natCast, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
  rw [e]
  exact Subgroup.zpow_mem L hxk u

theorem exists_Y_O2form_aux_cover {X : Type} [Group X] [Finite X] {T L Ti : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (hC : ¬ 3 ∣ Nat.card (gnC T)) {A₀ : Subgroup (X ⧸ gnC T)}
    (hA₀ : A₀ ≤ gnA T Ti Ls) (hperf : ⁅A₀, A₀⁆ = A₀)
    (hS : IsSimpleGroup (↥A₀ ⧸ CFSG.pCore 2 ↥A₀)) (h3 : 3 ∣ Nat.card A₀) :
    ∃ Y : Subgroup X, Y ≤ Subgroup.normalizer (Ti : Set X) ⊓ L ∧ ⁅Y, Y⁆ = Y ∧
      Y.map (toStar T) = A₀ := by
  classical
  set N : Subgroup X := Subgroup.normalizer (Ti : Set X) with hN
  have hA₀Ls : A₀ ≤ Ls := hA₀.trans inf_le_right
  have hA₀N : A₀ ≤ N.map (toStar T) := hA₀.trans inf_le_left
  set B : Subgroup X := N ⊓ A₀.comap (toStar T) with hB
  have hBmap : B.map (toStar T) = A₀ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact hb.2
    · intro a ha
      obtain ⟨n, hn, rfl⟩ := hA₀N ha
      exact ⟨n, ⟨hn, ha⟩, rfl⟩
  have hcomap := (liftOf_central_ext hX hLs hL).2
  have hBLC : ∀ b ∈ B, b ∈ L ⊔ gnC T := fun b hb => by
    rw [← hcomap]
    exact hA₀Ls hb.2
  have hconj : ∀ x : X, toStar T x ∈ Ls → x ∈ Subgroup.normalizer (L : Set X) := fun x hx =>
    exists_Y_O2form_aux_mem_normalizer (liftOf_conj hX hLs hL x (Subgroup.le_normalizer hx))
  have hCnorm : ∀ c ∈ gnC T, c ∈ Subgroup.normalizer (L : Set X) := by
    intro c hc
    apply hconj
    have h1 : toStar T c = 1 := (QuotientGroup.eq_one_iff c).2 hc
    rw [h1]
    exact Ls.one_mem
  have hB3 : ∀ b ∈ B, (∃ k : ℕ, orderOf b = 3 ^ k) → b ∈ L := by
    rintro b hb ⟨k, hk⟩
    exact exists_Y_O2form_aux_pElement_mem hCnorm hC (hBLC b hb) hk
  set N₁ : Subgroup (X ⧸ gnC T) := (B ⊓ L).map (toStar T) with hN₁
  have hN₁A : N₁ ≤ A₀ := hBmap ▸ Subgroup.map_mono inf_le_left
  have hN₁norm : ∀ a ∈ A₀, ∀ m ∈ N₁, a * m * a⁻¹ ∈ N₁ := by
    intro a ha m hm
    obtain ⟨b, hb, rfl⟩ : a ∈ B.map (toStar T) := hBmap ▸ ha
    obtain ⟨x, ⟨hxB, hxL⟩, rfl⟩ := hm
    refine ⟨b * x * b⁻¹, ⟨B.mul_mem (B.mul_mem hb hxB) (B.inv_mem hb), ?_⟩, by simp⟩
    have hbL : b ∈ Subgroup.normalizer (L : Set X) := hconj b (hA₀Ls hb.2)
    exact (Subgroup.mem_normalizer_iff.1 hbL x).1 hxL
  haveI hMn : (N₁.subgroupOf A₀).Normal := ⟨fun m hm g => hN₁norm g g.2 m hm⟩
  have hM3 : ∀ g : ↥A₀, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ N₁.subgroupOf A₀ := by
    rintro ⟨a, ha⟩ ⟨k, hk⟩
    let ψ : ↥B →* ↥A₀ := ((toStar T).comp B.subtype).codRestrict A₀ (fun b => hBmap ▸ ⟨b, b.2, rfl⟩)
    have hψ : Function.Surjective ψ := by
      rintro ⟨a', ha'⟩
      obtain ⟨b, hb, rfl⟩ : a' ∈ B.map (toStar T) := hBmap ▸ ha'
      exact ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨b, hbψ, j, hj⟩ := exists_pPow_lift ψ hψ Nat.prime_three ⟨k, hk⟩
    have hbL : (b : X) ∈ L := hB3 b b.2 ⟨j, (Subgroup.orderOf_coe b).trans hj⟩
    have hba : toStar T (b : X) = a := congrArg Subtype.val hbψ
    exact ⟨b, ⟨b.2, hbL⟩, hba⟩
  have hMtop : N₁.subgroupOf A₀ = ⊤ :=
    exists_Y_O2form_aux_eq_top (exists_Y_O2form_aux_comm_top hperf) hS h3 _ hM3
  have hN₁eq : N₁ = A₀ := by
    refine le_antisymm hN₁A (fun a ha => ?_)
    have : (⟨a, ha⟩ : ↥A₀) ∈ N₁.subgroupOf A₀ := by
      rw [hMtop]
      exact Subgroup.mem_top _
    exact this
  obtain ⟨Y, hYle, hYperf, hYmap, -⟩ := exists_Y_O2form_aux_residual (toStar T) (B ⊓ L)
    (by change ⁅N₁, N₁⁆ = N₁; rw [hN₁eq]; exact hperf)
  exact ⟨Y, hYle.trans (inf_le_inf_right L inf_le_left), hYperf, hYmap.trans hN₁eq⟩

theorem exists_Y_O2form_aux_equiv {X : Type} [Group X] [Finite X] {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) {A₀ : Subgroup (X ⧸ gnC T)} {Y : Subgroup X} (hYL : Y ≤ L)
    (hYperf : ⁅Y, Y⁆ = Y) (hYmap : Y.map (toStar T) = A₀)
    (hS : IsSimpleGroup (↥A₀ ⧸ CFSG.pCore 2 ↥A₀))
    (hnc : ∃ a b : ↥A₀ ⧸ CFSG.pCore 2 ↥A₀, a * b ≠ b * a)
    (hSM : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Odd (Nat.card (Subgroup.center K)) →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (↥A₀ ⧸ CFSG.pCore 2 ↥A₀)) →
      Nat.card (Subgroup.center K) = 1) :
    Nonempty ((↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* (↥A₀ ⧸ CFSG.pCore 2 ↥A₀)) := by
  classical
  let πb : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X)
  let φb : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hX)
  have hφb : ∀ x : X, φb (πb x) = toStar T x := fun x => rfl
  set Yb : Subgroup (X ⧸ CFSG.pCore 2 X) := Y.map πb with hYb
  have hYbL : Yb ≤ barO2 L := Subgroup.map_mono hYL
  have hYbA : ∀ k ∈ Yb, φb k ∈ A₀ := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hφb, ← hYmap]
    exact ⟨y, hy, rfl⟩
  let f : ↥Yb →* ↥A₀ := (φb.comp Yb.subtype).codRestrict A₀ (fun k => hYbA k.1 k.2)
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [← hYmap] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨⟨πb y, y, hy, rfl⟩, rfl⟩
  have hP : commutator ↥Yb = ⊤ :=
    exists_Y_O2form_aux_comm_top (by rw [hYb, ← Subgroup.map_commutator, hYperf])
  have hcentral := (liftOf_central_ext hX hLs hL).1
  have hkerL : ∀ k ∈ f.ker, Subgroup.inclusion hYbL k ∈ Subgroup.center ↥(barO2 L) := by
    intro k hk
    obtain ⟨y, hy, hyk⟩ := k.2
    have h1 : toStar T y = 1 := by
      have h2 : φb (k : X ⧸ CFSG.pCore 2 X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hk)
      rw [← hyk] at h2
      exact h2
    have h2 : y ∈ gnC T := (QuotientGroup.eq_one_iff y).1 h1
    have h4 : (k : X ⧸ CFSG.pCore 2 X) ∈ (L ⊓ gnC T).map (QuotientGroup.mk' (CFSG.pCore 2 X)) :=
      ⟨y, ⟨hYL hy, h2⟩, hyk⟩
    obtain ⟨z, hz, hzk⟩ := hcentral h4
    have : Subgroup.inclusion hYbL k = z := Subtype.ext hzk.symm
    rw [this]
    exact hz
  have hkerc : f.ker ≤ Subgroup.center ↥Yb := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subgroup.inclusion_injective hYbL
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 (hkerL k hk) _
  have hodd : Odd (Nat.card f.ker) := by
    have hle : f.ker.map (Subgroup.inclusion hYbL) ≤ Subgroup.center ↥(barO2 L) := by
      rintro _ ⟨k, hk, rfl⟩
      exact hkerL k hk
    have hc : Nat.card (f.ker.map (Subgroup.inclusion hYbL)) = Nat.card f.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hYbL)
    rw [← hc]
    exact Odd.of_dvd_nat (centre_barO2_odd hL.1) (Subgroup.card_dvd_of_le hle)
  have hker0 : f.ker = ⊥ := exists_Y_O2form_aux_central f hf hP hkerc hodd hS hnc hSM
  let g : ↥Y →* ↥A₀ := ((toStar T).comp Y.subtype).codRestrict A₀ (fun y => hYmap ▸ ⟨y, y.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨a, ha⟩
    rw [← hYmap] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨⟨y, hy⟩, rfl⟩
  have hgk : IsPGroup 2 g.ker := by
    intro z
    have h1 : πb (z.1 : X) = 1 := by
      have h2 : (⟨πb z.1, z.1.1, z.1.2, rfl⟩ : ↥Yb) ∈ f.ker := by
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact congrArg Subtype.val (MonoidHom.mem_ker.1 z.2)
      rw [hker0, Subgroup.mem_bot] at h2
      exact congrArg Subtype.val h2
    have hz : (z.1 : X) ∈ CFSG.pCore 2 X := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨z.1.1, hz⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  exact exists_Y_O2form_aux_pCore_equiv g hg hgk

open KFactsPair in
theorem exists_Y_O2form (hKSML3 : KSML3) {X : Type} [Group X] [Finite X] {T L Ti : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) (hC : ¬ 3 ∣ Nat.card (gnC T)) (h : HasLThreeCore (gnA T Ti Ls)) :
    ∃ Y : Subgroup X, Y ≤ Subgroup.normalizer (Ti : Set X) ∧
      IsLThreeTwoPow (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  obtain ⟨A₀, hA₀A, hA₀perf, hA₀L, hA₀nc⟩ := exists_Y_O2form_aux_core h
  have h2 : IsLThreeTwoPow (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) :=
    R1511C.isLThreeTwoPow_of_isLThreeOdd hA₀L
  have hS : IsSimpleGroup (↥A₀ ⧸ CFSG.pCore 2 ↥A₀) := R1511C.isSimpleGroup_of_isLThreeTwoPow h2
  have h3 : 3 ∣ Nat.card A₀ :=
    (K3DvdL3_holds _ h2).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨Y, hYN, hYperf, hYmap⟩ := exists_Y_O2form_aux_cover hX hLs hL hC hA₀A hA₀perf hS h3
  have hSM : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
      Odd (Nat.card (Subgroup.center K)) →
      Nonempty ((K ⧸ Subgroup.center K) ≃* (↥A₀ ⧸ CFSG.pCore 2 ↥A₀)) →
      Nat.card (Subgroup.center K) = 1 := by
    intro K _ _ hq hodd ⟨eK⟩
    obtain ⟨n, hn, h1 | h1⟩ := hA₀L
    · obtain ⟨-, d, q, hq7, hd, ⟨e⟩⟩ := h1
      exact (hKSML3 K hq d ⟨eK.trans e⟩ hodd).1 (Or.inr ⟨q, hq7, hd⟩)
    · obtain ⟨-, d, Q, hQ, hQe, hd, ⟨e⟩⟩ := h1
      exact (hKSML3 K hq d ⟨eK.trans e⟩ hodd).1
        (Or.inl ⟨Q, hQ, by rw [hQe]; exact hn, hd⟩)
  obtain ⟨e⟩ := exists_Y_O2form_aux_equiv hX hLs hL (hYN.trans inf_le_right) hYperf hYmap hS
    hA₀nc hSM
  exact ⟨Y, hYN.trans inf_le_left,
    R1511C.isLThreeTwoPow_of_isLThreeOdd (R1511C.isLThreeOdd_of_equiv e hA₀L)⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
