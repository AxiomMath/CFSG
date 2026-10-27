module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.PlaneAlg
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.GroupTheory.Fitting.LayerTopBot
import CFSG.GroupTheory.PrimeCorefreeQuasisimple
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Comp212Diag
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Layer

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem layer_ne_bot_of_not_exists_selfCentralizing [Fact p.Prime]
    (hcore : primeComplementCore (G := X) p = ⊥)
    (hnc : ¬ ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup p Q ∧ centralizer (Q : Set X) ≤ Q) :
    CFSG.ComponentClassification.Layer.subgroup X ≠ ⊥ := by
  intro hlay
  apply hnc
  have hchar : CFSG.IsCharacteristicP p X :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p hcore
      (by rw [CFSG.layer_eq_componentClassification]; exact hlay)
  exact ⟨CFSG.pCore p X, CFSG.pCore_normal, CFSG.pCore_isPGroup, hchar⟩

omit [Finite X] in
theorem exists_isComponentOf_of_layer_ne_bot
    (h : CFSG.ComponentClassification.Layer.subgroup X ≠ ⊥) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ := by
  by_contra hno
  push Not at hno
  exact h (sSup_eq_bot.mpr fun K hK => absurd hK (hno K))

theorem exists_pElement_not_central (hp : p.Prime) (hcore : primeComplementCore (G := X) p = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    p ∣ Nat.card (K ⧸ center K) ∧
      ∃ x ∈ K, (∃ k : ℕ, x ^ p ^ k = 1) ∧ ∃ g ∈ K, g * x ≠ x * g := by
  have hKcore : CFSG.pPrimeCore p K = ⊥ :=
    cfsg_subnormal_primeComplementCore_eq_bot p K hK.2.1 hcore
  have hquasi : CFSG.IsQuasisimple K := ((CFSG.isComponent_iff_open K).2 hK).1
  obtain ⟨hdvd, hgen⟩ :=
    CFSG.GroupTheory.prime_corefree_quasisimple_prime_generation hquasi hp hKcore
  refine ⟨hdvd, ?_⟩
  by_contra hno
  push Not at hno
  have hcen : ∀ a : K, (∃ k : ℕ, orderOf a = p ^ k) → a ∈ center K := by
    rintro a ⟨k, hk⟩
    rw [mem_center_iff]
    intro g
    have h1 : (a : X) ^ p ^ k = 1 := by
      have := pow_orderOf_eq_one a
      rw [hk] at this
      exact congrArg Subtype.val this
    exact Subtype.ext (hno a a.2 ⟨k, h1⟩ g g.2)
  have htop : (⊤ : Subgroup K) ≤ center K := by
    rw [← hgen, closure_le]
    exact fun a ha => hcen a ha
  obtain ⟨-, -, a, b, hab⟩ := hquasi
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp (htop (mem_top b')) a']

omit [Finite X] in
theorem isPGroup_zpowers_of_pow_prime_pow_eq_one [Fact p.Prime] {x : X} {k : ℕ}
    (hx : x ^ p ^ k = 1) : IsPGroup p (zpowers x) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hx)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem commute_of_mem_pCore_of_mem_layer [Fact p.Prime] {w g : X} (hw : w ∈ CFSG.pCore p X)
    (hg : g ∈ CFSG.ComponentClassification.Layer.subgroup X) : g * w = w * g := by
  have hw' : w ∈ centralizer (CFSG.layer X : Set X) :=
    CFSG.WholeGroup.pCore_le_centralizer_layer p hw
  rw [CFSG.layer_eq_componentClassification] at hw'
  exact mem_centralizer_iff.mp hw' g hg

omit [Finite X] in
theorem center_eq_bot_iff_forall {K : Subgroup X} :
    center K = ⊥ ↔ ∀ g ∈ K, (∀ w ∈ K, w * g = g * w) → g = 1 := by
  constructor
  · intro h g hg hc
    have hmem : (⟨g, hg⟩ : K) ∈ center K :=
      mem_center_iff.2 fun w => Subtype.ext (hc w w.2)
    rw [h, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · intro h
    refine eq_bot_iff.2 fun c hc => ?_
    rw [mem_bot]
    exact Subtype.ext (h c c.2 fun w hw => congrArg Subtype.val (mem_center_iff.1 hc ⟨w, hw⟩))

end Layer

section Config

variable {X : Type*} [Group X] [Finite X] {n p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

namespace Lemma212ConfigGe

theorem z_pow_eq_one (h : Lemma212ConfigGe n p P z D) : z ^ p = 1 :=
  h.ord ▸ pow_orderOf_eq_one z

theorem mem_of_normal_of_dvd (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) {N : Subgroup X}
    [N.Normal] (hN : p ∣ Nat.card N) : z ∈ N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hR⟩ := CFSG.Glauberman.sylow_inf_normal P (N := N)
  have hRne : (R : Subgroup N) ≠ ⊥ := R.ne_bot_of_dvd_card hN
  have hPN : (P : Subgroup X) ⊓ N ≠ ⊥ := by
    intro hbot
    apply hRne
    rw [hR, hbot, bot_subgroupOf]
  have hHne : N.subgroupOf (P : Subgroup X) ≠ ⊥ := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPN
    intro hbot
    apply ht1
    have hmem : (⟨t, t.2.1⟩ : ↥(P : Subgroup X)) ∈ N.subgroupOf (P : Subgroup X) := t.2.2
    rw [hbot, mem_bot] at hmem
    have h2 : ((⟨t, t.2.1⟩ : ↥(P : Subgroup X)) : X) = ((1 : ↥(P : Subgroup X)) : X) :=
      congrArg Subtype.val hmem
    exact Subtype.ext h2
  haveI : Group.IsNilpotent (↥(P : Subgroup X)) := P.isPGroup'.isNilpotent
  have hW : N.subgroupOf (P : Subgroup X) ⊓ center (↥(P : Subgroup X)) ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set W : Subgroup (↥(P : Subgroup X)) :=
    N.subgroupOf (P : Subgroup X) ⊓ center (↥(P : Subgroup X))
  have hWp : IsPGroup p W := P.isPGroup'.to_subgroup W
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  obtain ⟨m, hm, hmcard⟩ := hWp.nontrivial_iff_card.mp inferInstance
  have hdvdW : p ∣ Nat.card W := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) p hdvdW
  set u : X := ((w : ↥(P : Subgroup X)) : X)
  have hu_ord : orderOf u = p :=
    (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hw)
  have hup : u ^ p = 1 := by
    rw [← hu_ord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu_ord
    exact hp.one_lt.ne hu_ord
  have huC : u ∈ centralizer ((P : Subgroup X) : Set X) := by
    refine mem_centralizer_iff.mpr fun g hg => ?_
    exact congrArg Subtype.val (mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hmem : u ∈ zpowers z := h.unique u (w : ↥(P : Subgroup X)).2 huC hup
  have heq : zpowers u = zpowers z :=
    zpowers_eq_of_mem_zpowers hup h.z_pow_eq_one hu1 (h.ne_one hp) hmem
  have hzu : z ∈ zpowers u := by
    rw [heq]
    exact mem_zpowers z
  have huN : u ∈ N := w.2.1
  exact zpowers_le.mpr huN hzu

theorem mem_pCore_of_pCore_ne_bot (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    (hpc : CFSG.pCore p X ≠ ⊥) : z ∈ CFSG.pCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  haveI : Nontrivial (CFSG.pCore p X) := (Subgroup.nontrivial_iff_ne_bot _).2 hpc
  obtain ⟨m, hm, hmcard⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)).nontrivial_iff_card.mp
    inferInstance
  exact h.mem_of_normal_of_dvd hp (hmcard ▸ dvd_pow_self p hm.ne')

theorem mem_of_pElement_mem_centralizer (hp : p.Prime) (h : Lemma212ConfigGe n p P z D) {x : X}
    (hx : x ∈ centralizer (D : Set X)) (hxp : ∃ k : ℕ, x ^ p ^ k = 1) : x ∈ D := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hxp
  have hxN : zpowers x ≤ normalizer (D : Set X) := by
    rw [zpowers_le]
    apply centralizer_le_normalizer
    exact hx
  have hR : IsPGroup p (↥(D ⊔ zpowers x)) :=
    h.isPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_prime_pow_eq_one hk) hxN
  have hxR : x ∈ (D ⊔ zpowers x) ⊓ centralizer (D : Set X) :=
    ⟨Subgroup.mem_sup_right (mem_zpowers x), hx⟩
  rw [h.inf_centralizer_eq_of_isPGroup hp hR le_sup_left] at hxR
  exact hxR

theorem center_ne_bot_of_isComponentOf (hp : p.Prime) (h : Lemma212ConfigGe n p P z D)
    (hcore : primeComplementCore (G := X) p = ⊥) (hz : z ∈ CFSG.pCore p X) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) : center K ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro hKz
  set F : Set (Subgroup X) := {K | IsComponentOf K ⊤ ∧ center K = ⊥}
  have hfin : F.Finite := Set.toFinite _
  set Y : Subgroup X := sSup F
  have hKF : K ∈ F := ⟨hK, hKz⟩
  have hFconj : ∀ g : X, ∀ K ∈ F, K.map (MulAut.conj g).toMonoidHom ∈ F := by
    rintro g K ⟨hKc, hKz⟩
    refine ⟨isComponentOf_map_conj g hKc, ?_⟩
    rw [center_eq_bot_iff_forall] at hKz ⊢
    rintro _ ⟨k, hk, rfl⟩ hc
    have hk1 : k = 1 := hKz k hk fun w hw => by
      have h1 := hc _ ⟨w, hw, rfl⟩
      apply (MulAut.conj g).injective
      rw [map_mul, map_mul]
      exact h1
    simp [hk1]
  have hYn : Y.Normal := by
    refine ⟨fun m hm g => ?_⟩
    have h1 : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
      rw [map_le_iff_le_comap]
      refine sSup_le fun K hK => ?_
      rw [← map_le_iff_le_comap]
      exact le_sSup (hFconj g K hK)
    simpa using h1 ⟨m, hm, rfl⟩
  have hKY : K ≤ Y := le_sSup hKF
  have hdvdY : p ∣ Nat.card Y :=
    ((exists_pElement_not_central hp hcore hK).1.trans (Subgroup.card_quotient_dvd_card _)).trans
      (card_dvd_of_le hKY)
  haveI := hYn
  have hzY : z ∈ Y := h.mem_of_normal_of_dvd hp hdvdY
  have hYfin : Y = ⨆ K ∈ hfin.toFinset, K :=
    le_antisymm (sSup_le fun K hK => le_iSup₂_of_le K (hfin.mem_toFinset.2 hK) le_rfl)
      (iSup₂_le fun K hK => le_sSup (hfin.mem_toFinset.1 hK))
  refine h.ne_one hp
    (CFSG.LocalAnalysis.RankThreeTheoremC.eq_one_of_mem_iSup_components hfin.toFinset
      (fun K hK => (hfin.mem_toFinset.1 hK).1) (fun K hK => (hfin.mem_toFinset.1 hK).2) z
      (hYfin ▸ hzY) fun K hK x hx => ?_)
  exact (commute_of_mem_pCore_of_mem_layer hz
    (CFSG.ComponentClassification.Layer.component_le (hfin.mem_toFinset.1 hK).1 hx)).symm

end Lemma212ConfigGe

end Config

end CFSG.LocalAnalysis.RankFourTheoremC
