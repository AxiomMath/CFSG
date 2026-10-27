module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma136c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116Design
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf innerAut IsLocallyBalanced IsWeaklyLocallyBalanced)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)
open scoped MatrixGroups

namespace Lemma123

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}

@[expose] def TD (p : ℕ) (M : Subgroup G) (a : G) (D : Subgroup G) : Subgroup G :=
  Tof p M a ⊓ Subgroup.centralizer (D : Set G)

theorem mem_normalizer_tof {x : G} (hxM : x ∈ M) (hxC : x ∈ Cg a) :
    x ∈ Subgroup.normalizer ((Tof p M a : Subgroup G) : Set G) := by
  have h1 : x ∈ Subgroup.normalizer ((alphaOf p M ⊓ Cg a : Subgroup G) : Set G) :=
    Sec12a.mem_normalizer_inf (le_normalizer_alphaOf p M hxM) (Subgroup.le_normalizer hxC)
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ h1

theorem tof_not_le_primeCore (h111 : Prop111Statement) (h : Cex121 G m p B M E A a) :
    ¬ Tof p M a ≤ GLAPPrimeCoreOf p (Cg a) := by
  intro hTN
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hNM : GLAPPrimeCoreOf p (Cg a) ≤ M := h111 h.toSec11 h.ha.1 h.ha.2
  have hNC : GLAPPrimeCoreOf p (Cg a) ≤ Cg a := sec11_glaPPrimeCoreOf_le _
  have hT2 : IsPGroup 2 ↥(Tof p M a) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have h1 : Tof p M a ≤ CFSG.Open.pCoreOf 2 (GLAPPrimeCoreOf p (Cg a)) :=
    Sec12a.le_pCoreOf_two_of_le_normalizer hTN (fun x hx => mem_normalizer_tof (hNM hx) (hNC hx)) hT2
  have h2 : CFSG.Open.pCoreOf 2 (GLAPPrimeCoreOf p (Cg a)) ≤ CFSG.Open.pCoreOf 2 (Cg a) := by
    refine Sec12a.le_pCoreOf_two_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hNC) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (sec11_le_normalizer_glaPPrimeCoreOf (Cg a)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  exact h.fails (h1.trans h2)

theorem card_eq_pow_pRank {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hP : IsElemAbelian p P) :
    Nat.card P = p ^ CFSG.Open.pRank p P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hP)
  have h1 : k ≤ CFSG.Open.pRank p P := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hP hk
  obtain ⟨E, hEP, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt P
  have h2 : p ^ CFSG.Open.pRank p P ≤ p ^ k := by
    rw [← hE, ← hk]
    exact Subgroup.card_le_of_le hEP
  have h3 : CFSG.Open.pRank p P ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
  rw [hk]
  congr 1
  omega

theorem le_iSup_inf_centralizer {p : ℕ} [Fact p.Prime] {P X : Subgroup G} (hP : IsElemAbelian p P)
    (hcard : p ^ 2 ≤ Nat.card P) (hX : ¬ p ∣ Nat.card X)
    (hn : P ≤ Subgroup.normalizer (X : Set G)) :
    X ≤ ⨆ (e : G) (_ : e ∈ P) (_ : e ≠ 1), X ⊓ Subgroup.centralizer ({e} : Set G) := by
  haveI : CFSG.IsElementaryAbelian p ↥P := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hP
  let α : ↥P →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hα : ∀ (k : ↥P) (x : ↥X), ((α k x : ↥X) : G) = (k : G) * x * (k : G)⁻¹ :=
    fun k x => Subgroup.normalizerMonoidHom_apply_apply_coe X (Subgroup.inclusion hn k) x
  letI : MulDistribMulAction ↥P ↥X := MulDistribMulAction.compHom X α
  have hsmul : ∀ (k : ↥P) (x : ↥X), k • x = α k x := fun _ _ => rfl
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥P) (H := ↥X) hcard hX
  have hall : (⊤ : Subgroup ↥X) ≤ (⨆ (e : G) (_ : e ∈ P) (_ : e ≠ 1),
      X ⊓ Subgroup.centralizer ({e} : Set G)).comap X.subtype := by
    rw [← hgen]
    refine iSup₂_le fun k hk => ?_
    intro x hx
    have hkx : k • x = x := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff k x).1 hx
    have h1 : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
      have h1' : ((k • x : ↥X) : G) = (x : G) := congrArg Subtype.val hkx
      rw [hsmul, hα] at h1'
      exact h1'
    have hxC : (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      calc (k : G) * (x : G) = (k : G) * (x : G) * (k : G)⁻¹ * (k : G) := by group
        _ = (x : G) * (k : G) := by rw [h1]
    have hk1 : (k : G) ≠ 1 := fun e => hk (Subtype.ext e)
    have hmem : (x : G) ∈ X ⊓ Subgroup.centralizer ({(k : G)} : Set G) := ⟨x.2, hxC⟩
    have hS : X ⊓ Subgroup.centralizer ({(k : G)} : Set G) ≤
        ⨆ (e : G) (_ : e ∈ P) (_ : e ≠ 1), X ⊓ Subgroup.centralizer ({e} : Set G) :=
      le_iSup₂_of_le (k : G) k.2
        (le_iSup (fun _ : (k : G) ≠ 1 => X ⊓ Subgroup.centralizer ({(k : G)} : Set G)) hk1)
    exact hS hmem
  intro x hx
  exact hall (Subgroup.mem_top (⟨x, hx⟩ : ↥X))

theorem isElemAbelian_inter (h : Sec11 G m p B M E A) : IsElemAbelian p (E ⊓ A) :=
  CFSG.Open.IsElemAbelian.mono h.pair.1.2.1.1.1.2.1 inf_le_right

theorem inter_le_cg (h : Cex121 G m p B M E A a) : E ⊓ A ≤ Cg a := by
  intro x hx
  have hAel : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff.1 hy]
  exact (CFSG.Open.IsElemAbelian.comm hAel (Subgroup.mem_inf.1 hx).2 h.ha.1).symm

theorem inter_le_M (h : Sec11 G m p B M E A) : E ⊓ A ≤ M :=
  inf_le_left.trans h.pair.1.1.1.1.1

theorem inter_le_normalizer_tof (h : Cex121 G m p B M E A a) :
    E ⊓ A ≤ Subgroup.normalizer ((Tof p M a : Subgroup G) : Set G) :=
  fun x hx => mem_normalizer_tof (inter_le_M h.toSec11 hx) (inter_le_cg h hx)

theorem sq_le_card_inter (h : Sec11 G m p B M E A) : p ^ 2 ≤ Nat.card (E ⊓ A : Subgroup G) := by
  have hp : p.Prime := h.standing.prime
  rw [card_eq_pow_pRank hp (isElemAbelian_inter h)]
  exact Nat.pow_le_pow_right hp.pos h.pair.1.2.2

theorem not_dvd_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup 2 X) : ¬ p ∣ Nat.card X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hX
  intro hdvd
  rw [hn] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem TD_zpowers (e : G) : TD p M a (Subgroup.zpowers e) = Tof p M a ⊓ Cg e := by
  ext x
  simp only [TD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
    forall_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2 e (Subgroup.mem_zpowers e)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g hg => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute e x from h2) n)).eq

theorem TD_bot : TD p M a (⊥ : Subgroup G) = Tof p M a := by
  ext x
  simp [TD, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]

theorem exists_maxD (h : Cex121 G m p B M E A a)
    (hTN : ¬ Tof p M a ≤ GLAPPrimeCoreOf p (Cg a)) :
    ∃ D : Subgroup G, D ≤ E ⊓ A ∧ ¬ TD p M a D ≤ GLAPPrimeCoreOf p (Cg a) ∧
      ∀ D' : Subgroup G, D' ≤ E ⊓ A → ¬ TD p M a D' ≤ GLAPPrimeCoreOf p (Cg a) →
        Nat.card D' ≤ Nat.card D := by
  classical
  let S : Set (Subgroup G) := {D | D ≤ E ⊓ A ∧ ¬ TD p M a D ≤ GLAPPrimeCoreOf p (Cg a)}
  have hfin : S.Finite := Set.toFinite S
  have hbot : (⊥ : Subgroup G) ∈ S := ⟨bot_le, by rw [TD_bot]; exact hTN⟩
  obtain ⟨D, hD, hmax⟩ := Set.exists_max_image S (fun D => Nat.card D) hfin ⟨⊥, hbot⟩
  exact ⟨D, hD.1, hD.2, fun D' h1 h2 => hmax D' ⟨h1, h2⟩⟩

theorem maxD_ne_bot (h : Cex121 G m p B M E A a)
    (hTN : ¬ Tof p M a ≤ GLAPPrimeCoreOf p (Cg a)) {D : Subgroup G}
    (hmax : ∀ D' : Subgroup G, D' ≤ E ⊓ A → ¬ TD p M a D' ≤ GLAPPrimeCoreOf p (Cg a) →
      Nat.card D' ≤ Nat.card D) : D ≠ ⊥ := by
  intro hD0
  subst hD0
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := h.standing.ne_two
  have hgen := le_iSup_inf_centralizer (p := p) (isElemAbelian_inter h.toSec11)
    (sq_le_card_inter h.toSec11)
    (not_dvd_card_of_isPGroup_two hp hp2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    (inter_le_normalizer_tof h)
  by_contra hcon
  apply hTN
  refine hgen.trans (iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_)
  by_contra hne
  have hmem : Subgroup.zpowers e ≤ E ⊓ A := by
    rw [Subgroup.zpowers_le]; exact he
  have hcardz : Nat.card (Subgroup.zpowers e) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((isElemAbelian_inter h.toSec11).2 e he) he1
  have := hmax (Subgroup.zpowers e) hmem (by rw [TD_zpowers]; exact hne)
  rw [hcardz, Subgroup.card_bot] at this
  exact hp.one_lt.not_ge this

theorem TD_inter_le {D : Subgroup G} (hDA : D ≤ E ⊓ A) (hne : D ≠ E ⊓ A)
    (hmax : ∀ D' : Subgroup G, D' ≤ E ⊓ A → ¬ TD p M a D' ≤ GLAPPrimeCoreOf p (Cg a) →
      Nat.card D' ≤ Nat.card D) :
    TD p M a (E ⊓ A) ≤ GLAPPrimeCoreOf p (Cg a) := by
  by_contra hcon
  have h1 := hmax (E ⊓ A) le_rfl hcon
  have h2 : Nat.card D < Nat.card (E ⊓ A : Subgroup G) :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hDA hne)
  omega

theorem TD_le_delta (h122 : Lemma122_i_iiStatement) (h : Cex121 G m p B M E A a) {D : Subgroup G}
    (hDA : D ≤ E ⊓ A) : TD p M a D ≤ localDeltaTwoIn (Cg a) D := by
  unfold localDeltaTwoIn
  refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
  have h1 := (h122 h).1 d (hDA hd) hd1
  rw [Sec12a.cg2_eq_inf] at h1
  intro x hx
  refine h1 ⟨hx.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff.1 hy]
  exact Subgroup.mem_centralizer_iff.1 hx.2 d hd

theorem mk_comm_of_commutator_mem {p : ℕ} {X : Subgroup G} {t y : G} (ht : t ∈ X) (hy : y ∈ X)
    (h : t * y * t⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨t, ht⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hy⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hy⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨t, ht⟩ := by
  obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.1 h
  have hz' : z = (⟨t, ht⟩ : ↥X) * ⟨y, hy⟩ * (⟨t, ht⟩ : ↥X)⁻¹ * (⟨y, hy⟩ : ↥X)⁻¹ :=
    Subtype.ext (by simpa using hzeq)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  rw [hz'] at h1
  simp only [map_mul, map_inv] at h1
  have h2 := mul_inv_eq_one.1 h1
  exact (mul_inv_eq_iff_eq_mul.1 h2)

theorem exists_comp_not_centralized {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X T' : Subgroup G}
    (hT2 : IsPGroup 2 T') (hTX : T' ≤ X)
    (hF : ∀ x ∈ T', ∀ y ∈ pPrimePCore p X, x * y * x⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p X)
    (hnot : ¬ T' ≤ GLAPPrimeCoreOf p X) :
    ∃ K : Subgroup G, GLAPComponent p X K ∧ ¬ ⁅K, T'⁆ ≤ GLAPPrimeCoreOf p X := by
  by_contra hcon
  push Not at hcon
  apply hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hQcore : GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hxfix : barX p X T' ≤ CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htT : (t : G) ∈ T' := Subgroup.mem_subgroupOf.1 ht
    apply mem_pCore_of_centralizes hp hQcore
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      have hy : (y : G) ∈ pPrimePCore p X := Subgroup.mem_map.2 ⟨y, hw, rfl⟩
      exact (mk_comm_of_commutator_mem t.2 y.2 (hF _ htT _ hy)).symm
    · intro K hK
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq X hK
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      obtain ⟨l, hl, rfl⟩ := hq
      have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
      have hc : (l : G) * t * (l : G)⁻¹ * (t : G)⁻¹ ∈ GLAPPrimeCoreOf p X :=
        hcon L hL (by simpa [commutatorElement_def] using Subgroup.commutator_mem_commutator hlL htT)
      exact mk_comm_of_commutator_mem l.2 t.2 hc
  have hT2' : IsPGroup 2 ↥(barX p X T') := by
    have hsub : IsPGroup 2 ↥(T'.subgroupOf X) := hT2.comap_of_injective X.subtype Subtype.val_injective
    exact hsub.map _
  have hbarT : barX p X T' = ⊥ := by
    have hpC : IsPGroup p ↥(CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup p
    have hI : barX p X T' ⊓ CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ := by
      have h2 : IsPGroup 2 ↥(barX p X T' ⊓ CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)) :=
        hT2'.to_le inf_le_left
      have hpp : IsPGroup p ↥(barX p X T' ⊓ CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X)) :=
        hpC.to_le inf_le_right
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 h2
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hpp
      have hb0 : b = 0 := by
        by_contra hb0
        have hdvd : p ∣ 2 ^ a := by
          rw [← ha, hb]
          exact dvd_pow_self p hb0
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hb, hb0, pow_zero])
    calc barX p X T' = barX p X T' ⊓ CFSG.Open.pCore p (↥X ⧸ GLAPPrimeCore p ↥X) :=
          (inf_eq_left.2 hxfix).symm
      _ = ⊥ := hI
  intro t ht
  have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) (⟨t, hTX ht⟩ : ↥X) ∈ barX p X T' :=
    ⟨⟨t, hTX ht⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩
  rw [hbarT, Subgroup.mem_bot] at h1
  have h2 := (QuotientGroup.eq_one_iff (⟨t, hTX ht⟩ : ↥X)).1 h1
  unfold GLAPPrimeCoreOf
  exact Subgroup.mem_map.2 ⟨⟨t, hTX ht⟩, h2, rfl⟩

theorem not_le_M_of_not_comm (hp : p.Prime) (hp2 : p ≠ 2) {D K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) (hTDnorm : TD p M a D ≤ Subgroup.normalizer (K : Set G))
    (hnot : ¬ ⁅K, TD p M a D⁆ ≤ GLAPPrimeCoreOf p (Cg a)) : ¬ K ≤ M := by
  intro hKM
  haveI : Fact p.Prime := ⟨hp⟩
  apply hnot
  have hKC : K ≤ Cg a := hK.1
  have hT2 : IsPGroup 2 ↥(Tof p M a) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hKT : K ⊓ Tof p M a ≤ CFSG.Open.pCoreOf 2 K := by
    refine Sec12a.le_pCoreOf_two_of_le_normalizer inf_le_left ?_ (hT2.to_le inf_le_right)
    intro k hk
    exact Sec12a.mem_normalizer_inf (Subgroup.le_normalizer hk)
      (mem_normalizer_tof (hKM hk) (hKC hk))
  have hKcore : CFSG.Open.pCoreOf 2 K ≤ GLAPPrimeCoreOf p K := by
    refine sec11_le_glaPPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) ?_ ?_
    · intro h hh n hn
      exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hh) n).1 hn
    · exact (Nat.Prime.coprime_iff_not_dvd hp).2
        (not_dvd_card_of_isPGroup_two hp hp2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K))
  have hKC' : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p (Cg a) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hK.2.1
  refine (Subgroup.commutator_le).2 fun k hk t ht => ?_
  refine hKC' (hKcore (hKT ⟨?_, ?_⟩))
  ·
    have h1 : t * k⁻¹ * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hTDnorm ht) k⁻¹).1 (K.inv_mem hk)
    simpa [commutatorElement_def, mul_assoc] using K.mul_mem hk h1
  ·
    have h1 : k * t * k⁻¹ ∈ Tof p M a :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_tof (hKM hk) (hKC hk)) t).1 ht.1
    simpa [commutatorElement_def, mul_assoc] using (Tof p M a).mul_mem h1 ((Tof p M a).inv_mem ht.1)

structure Prep123a (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K D : Subgroup G) (r : ℕ) : Prop where
  cex : Cex121 G m p B M E A a
  hK : GLAPComponent p (Cg a) K
  hDA : D ≤ E ⊓ A
  hDcard : Nat.card D = p ^ r
  hr : 1 ≤ r
  hDmax : ∀ D' : Subgroup G, D' ≤ E ⊓ A → ¬ TD p M a D' ≤ GLAPPrimeCoreOf p (Cg a) →
    Nat.card D' ≤ Nat.card D
  hTD : ¬ TD p M a D ≤ GLAPPrimeCoreOf p (Cg a)
  hTDK : ¬ ⁅K, TD p M a D⁆ ≤ GLAPPrimeCoreOf p (Cg a)
  hTDnorm : TD p M a D ≤ Subgroup.normalizer (K : Set G)
  hDnorm : D ≤ Subgroup.normalizer (K : Set G)
  hDfaith : centBar p D K = ⊥
  hbal : ¬ IsCompLocallyOTwoBalanced p r D K
  hKM : ¬ K ≤ M

theorem prep123a (h111 : Prop111Statement) (h122 : Lemma122_i_iiStatement)
    (hI191 : Lemma136c.Input19_1_O2) (h : Cex121 G m p B M E A a) :
    ∃ (K D : Subgroup G) (r : ℕ), Prep123a G m p B M E A a K D r := by
  have hp : p.Prime := h.standing.prime
  have hp2 : p ≠ 2 := h.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := h.standing.simple
  have hTN := tof_not_le_primeCore h111 h
  obtain ⟨D, hDA, hD, hmax⟩ := exists_maxD h hTN
  have hD0 : D ≠ ⊥ := maxD_ne_bot h hTN hmax
  have hDel : IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono (isElemAbelian_inter h.toSec11) hDA
  obtain ⟨r, hr⟩ := exists_card_eq_pow (CFSG.Open.IsElemAbelian.isPGroup hDel)
  have hr1 : 1 ≤ r := by
    by_contra hr0
    have : r = 0 := by omega
    subst this
    exact hD0 (Subgroup.eq_bot_of_card_eq D (by simpa using hr))
  have hXtop : Cg a ≠ ⊤ :=
    Lemma136c.l136c_centralizer_ne_top h.standing.nonabelian h.ha.2
  have hDX : IsEkIn p r (Cg a) D := ⟨hDA.trans (inter_le_cg h), hDel, hr⟩
  obtain ⟨hnormall, hcent, hclause⟩ := hI191 G h.standing.kProper p hp hp2 r hr1 (Cg a) D hXtop hDX
  have hTDle : TD p M a D ≤ localDeltaTwoIn (Cg a) D := TD_le_delta h122 h hDA
  have hT2 : IsPGroup 2 ↥(TD p M a D) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hTX : TD p M a D ≤ Cg a := inf_le_left.trans (Sec12a.tof_le_cg M a)
  obtain ⟨K, hK, hKT⟩ := exists_comp_not_centralized hp hp2 hT2 hTX
    (fun x hx y hy => hcent x (hTDle hx) y hy) hD
  have hKΔ : ¬ ⁅K, localDeltaTwoIn (Cg a) D⁆ ≤ GLAPPrimeCoreOf p (Cg a) :=
    fun hΔ => hKT (le_trans (Subgroup.commutator_mono le_rfl hTDle) hΔ)
  obtain ⟨hDK, hfaith, hbal⟩ := hclause K hK hKΔ
  have hTDnorm : TD p M a D ≤ Subgroup.normalizer (K : Set G) := fun x hx => hnormall K hK (hTDle hx)
  exact ⟨K, D, r, ⟨h, hK, hDA, hr, hr1, hmax, hD, hKT, hTDnorm, hDK, hfaith, hbal,
    not_le_M_of_not_comm hp hp2 hK hTDnorm hKT⟩⟩

theorem localDeltaTwoIn_anti {M' : Type*} [Group M'] {H D D' : Subgroup M'} (h : D ≤ D') :
    localDeltaTwoIn H D' ≤ localDeltaTwoIn H D := by
  unfold localDeltaTwoIn
  refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
  exact (iInf_le _ d).trans ((iInf_le _ (h hd)).trans (iInf_le _ hd1))

theorem isLocallyOTwoBalanced_mono {p k : ℕ} {K : Type*} [Group K] {A' A : Subgroup (MulAut K)}
    (h : A' ≤ A) (hA : IsLocallyOTwoBalanced p k A) : IsLocallyOTwoBalanced p k A' :=
  fun D hD H hH hN => hA D ⟨hD.1.trans h, hD.2.1, hD.2.2⟩ H hH hN

theorem isLocallyOTwoBalanced_of_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) {K : Type*} [Group K]
    {A : Subgroup (MulAut K)} (h : IsLocallyOTwoBalanced p 1 A) : IsLocallyOTwoBalanced p k A := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro D hD H hH hN
  obtain ⟨hDA, hDel, hDcard⟩ := hD
  have hnt : D ≠ ⊥ := by
    intro hD0
    rw [hD0, Subgroup.card_bot] at hDcard
    have : 1 < p ^ k := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  obtain ⟨d, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hnt
  have hdD : (d : MulAut K) ∈ D := d.2
  have hdp : (d : MulAut K) ^ p = 1 := hDel.2 d hdD
  have hzD : Subgroup.zpowers (d : MulAut K) ≤ D := by rw [Subgroup.zpowers_le]; exact hdD
  have hd1' : (d : MulAut K) ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hcard : Nat.card (Subgroup.zpowers (d : MulAut K)) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hdp hd1'
  have hE1 : IsEkIn p 1 A (Subgroup.zpowers (d : MulAut K)) :=
    ⟨hzD.trans hDA, CFSG.Open.isElemAbelian_zpowers hdp, hcard⟩
  have h0 := h _ hE1 H hH (hzD.trans hN)
  exact le_bot_iff.1 ((localDeltaTwoIn_anti hzD).trans h0.le)

theorem autBar_mono {p : ℕ} {B B' L : Subgroup G} (h : B ≤ B') : autBar p B L ≤ autBar p B' L := by
  unfold autBar
  refine Subgroup.map_mono fun x hx => ?_
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hx ⊢
  exact ⟨h hx.1, hx.2⟩

theorem not_isCompLocallyOTwoBalanced_one {p r : ℕ} (hp : p.Prime) (hr : 1 ≤ r) {D B' L : Subgroup G}
    (hDB : D ≤ B') (h : ¬ IsCompLocallyOTwoBalanced p r D L) : ¬ IsCompLocallyOTwoBalanced p 1 B' L := by
  intro h1
  apply h
  exact isLocallyOTwoBalanced_mono (autBar_mono hDB) (isLocallyOTwoBalanced_of_one hp hr h1)

theorem not_isCompLocallyOTwoBalanced_mono {p k : ℕ} {B B' L : Subgroup G} (hBB : B ≤ B')
    (h : ¬ IsCompLocallyOTwoBalanced p k B L) : ¬ IsCompLocallyOTwoBalanced p k B' L :=
  fun h' => h (isLocallyOTwoBalanced_mono (autBar_mono hBB) h')

theorem p_dvd_card_barOf {p : ℕ} (hp : p.Prime) {X K : Subgroup G} (hK : GLAPComponent p X K) :
    p ∣ Nat.card (barOf p K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hndvd
  have hcop : Nat.Coprime p (Nat.card (barOf p K)) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hnt : Nontrivial (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial
      (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK)
  have htop : GLAPPrimeCore p (barOf p K) = ⊤ :=
    eq_top_iff.2 (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have hbot : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  rw [hbot] at htop
  obtain ⟨x, hx⟩ := exists_ne (1 : barOf p K)
  have hx' : x ∈ (⊥ : Subgroup (barOf p K)) := by rw [htop]; trivial
  exact hx (Subgroup.mem_bot.1 hx')

theorem inter_le_cg' (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) : E ⊓ A ≤ Cg a := by
  intro x hx
  have hAel : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [Set.mem_singleton_iff.1 hy]
  exact (CFSG.Open.IsElemAbelian.comm hAel (Subgroup.mem_inf.1 hx).2 ha).symm

@[expose] def Fam123 (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :=
  {Z | ∃ z ∈ A0, Z = GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)}

theorem fam123_base (p : ℕ) (C K : Subgroup G) (A0 : Subgroup ↥C) :
    barX p C K ∈ Fam123 p C K A0 :=
  ⟨1, A0.one_mem, by rw [map_one, gLBConj_one]⟩

theorem fam123_comp {p : ℕ} {C K : Subgroup G} (hK : GLAPComponent p C K) (A0 : Subgroup ↥C) :
    ∀ Z ∈ Fam123 p C K A0, IsComponentOf Z ⊤ := by
  rintro Z ⟨z, -, rfl⟩
  exact l119_conj_component hK z

theorem bar_normalizes123 {p : ℕ} {C K : Subgroup G} (A0 : Subgroup ↥C) {y : ↥C} (hy : y ∈ A0) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) y ∈
      Subgroup.normalizer ((sSup (Fam123 p C K A0) : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) : Set _) := by
  set S : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) := sSup (Fam123 p C K A0) with hS
  have hstep : ∀ g : ↥C ⧸ GLAPPrimeCore p ↥C, (∃ w : ↥C, w ∈ A0 ∧ QuotientGroup.mk' (GLAPPrimeCore p ↥C) w = g) →
      S ≤ S.comap (MulAut.conj g).toMonoidHom := by
    rintro g ⟨w, hw, rfl⟩
    refine sSup_le fun Z hZ => ?_
    obtain ⟨z, hz, rfl⟩ := hZ
    intro x hx
    show (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹ ∈ S
    have hmem : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ∈ Fam123 p C K A0 :=
      ⟨z * w⁻¹, A0.mul_mem hz (A0.inv_mem hw), by
        rw [gLBConj_gLBConj, map_mul, map_inv]⟩
    have hsub : GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)
        (GLBConj (QuotientGroup.mk' (GLAPPrimeCore p ↥C) z) (barX p C K)) ≤ S :=
      le_sSup hmem
    apply hsub
    rw [mem_gLBConj]
    have hcancel : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) w) * x * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) w⁻¹)⁻¹ = x := by
      rw [map_inv]
      group
    rw [hcancel]
    exact hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hstep _ ⟨y, hy, rfl⟩ hh
  · intro hh
    have hh' := hstep (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) ⟨y⁻¹, A0.inv_mem hy, rfl⟩ hh
    have e : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ = h := by
      rw [map_inv]
      group
    have hh'' : (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹) *
        ((QuotientGroup.mk' (GLAPPrimeCore p ↥C) y) * h * (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y)⁻¹) *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥C) y⁻¹)⁻¹ ∈ S := hh'
    rw [e] at hh''
    exact hh''


@[expose] def InputDiagBalance : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (C K B : Subgroup G),
    GLAPComponent p C K → IsElemAbelian p B → B ≤ C → ¬ IsCompLocallyOTwoBalanced p 1 B K →
    ∀ b ∈ B, b ≠ 1 → ∀ hbC : b ∈ C,
      (b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p C K,
        QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨b, hbC⟩) →
      ∀ J : Subgroup G, GLAPComponent p (C ⊓ Subgroup.centralizer ({b} : Set G)) J →
        barX p C J ≤ barX p C (⨆ y ∈ B, GLBConj y K) →
          ¬ IsCompLocallyOTwoBalanced p 1 B J ∧ ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J)

theorem mk_mem_normalizer_barX {p : ℕ} {C K : Subgroup G} (hKC : K ≤ C) {z : ↥C}
    (hz : (z : G) ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥C) z ∈
      Subgroup.normalizer ((barX p C K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
        Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  classical
  rw [mem_normalizer_iff_gLBConj_eq]
  have h := l119_barX_gLBConj (p := p) (C := C) (g := (z : G)) z.2 hKC
  rw [gLBConj_eq_of_mem_normalizer hz] at h
  exact h.symm

theorem layer_le' {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hK : GLAPComponent p (Cg a) K) (hbal : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K)
    (hDiag : InputDiagBalance) (h115 : Prop115Statement)
    {b : G} (hbA0 : b ∈ E ⊓ A) (hb1 : b ≠ 1) (hbC : b ∈ Cg a)
    (hbp : IsPGroup p (Subgroup.zpowers b))
    (hbad : b ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p (Cg a) K,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩ * q =
        q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩)
    {L : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))} (hL : IsSubnormal L ⊤)
    (hLK : L ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K))
    {Q : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a))}
    (hQ : GLAPComponent p (L ⊓ Subgroup.centralizer
      ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨b, hbC⟩} :
        Set (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)))) Q) :
    Q ≤ barX p (Cg a) M := by
  obtain ⟨P, hP, hPQ, -⟩ := l119_layer_piece hp hbC hbp hL hQ
  have hQL : Q ≤ L := hQ.1.trans inf_le_left
  have hPK : barX p (Cg a) P ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K) := hPQ ▸ hQL.trans hLK
  obtain ⟨hb1', hb2'⟩ := hDiag G p hp hSec.standing.ne_two (Cg a) K (E ⊓ A) hK
    (isElemAbelian_inter hSec) (inter_le_cg' hSec ha) hbal b hbA0 hb1 hbC hbad P hP hPK
  have hJ : GLAPComponent p (Cg2 b a) P := by
    unfold Cg2
    rw [l119_cg2_eq]
    exact hP
  rcases h115 hSec ha ha1 hbA0 hb1 hJ hb2'
      (fun _ _ => not_isCompLocallyOTwoBalanced_mono (inf_le_right : E ⊓ A ≤ A) hb1') with hPM | ⟨A1, hA1, haA1⟩
  · rw [← hPQ]
    exact barX_mono p hPM
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD

theorem no_bad' {p : ℕ} {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (hp : p.Prime) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hK : GLAPComponent p (Cg a) K) (hKM : ¬ K ≤ M)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1)
    (hbal : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K)
    (h111 : Prop111Statement) (hI22 : Input22_3_2) (hDiag : InputDiagBalance)
    (h115 : Prop115Statement) :
    ¬ ∃ z : ↥(Cg a), (z : G) ∈ E ⊓ A ∧ (z : G) ≠ 1 ∧
      ((z : G) ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  rintro ⟨z₀, hz₀A, hz₀1, hbad⟩
  obtain ⟨hDDp, -⟩ := hSec.pair
  obtain ⟨-, hDp, hrA0⟩ := hDDp
  obtain ⟨hSCs, -⟩ := hDp
  obtain ⟨hSCp, -⟩ := hSCs
  obtain ⟨-, hAel, -⟩ := hSCp
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hApow : ∀ x ∈ A, x ^ p = 1 := fun x hx => hAel.2 x hx
  have hACg : A ≤ Cg a := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hAcomm a ha x hx
  set A0 : Subgroup G := E ⊓ A with hA0
  have hA0A : A0 ≤ A := inf_le_right
  have hA0C : A0 ≤ Cg a := hA0A.trans hACg
  have hA0el : IsElemAbelian p A0 := l119_isElemAbelian_of_le hA0A hAel
  have hrA0 : 2 ≤ CFSG.Open.pRank p A0 := hrA0
  set A0C : Subgroup ↥(Cg a) := A0.subgroupOf (Cg a) with hA0Cdef
  set Bbar : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) :=
    A0C.map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a))) with hBbar
  set Kb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := barX p (Cg a) K with hKb
  set 𝓛 := Fam123 p (Cg a) K A0C with h𝓛def
  set Yb : Subgroup (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) := sSup 𝓛 with hYb
  have hKbc : IsComponentOf Kb ⊤ := l119_isComponent_barX hK
  have hKbmem : Kb ∈ 𝓛 := fam123_base p (Cg a) K A0C
  have h𝓛c : ∀ X ∈ 𝓛, IsComponentOf X ⊤ := fam123_comp hK A0C
  have hcomm𝓛 : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, X ≠ X' → ∀ x ∈ X, ∀ y ∈ X', x * y = y * x := by
    rintro X ⟨w, -, rfl⟩ X' ⟨w', -, rfl⟩ hne x hx y hy
    exact l119_conj_comm hK hne hx hy
  have hYsub : IsSubnormal Yb ⊤ := l119_isSubnormal_sSup_components h𝓛c
  have hYcomp : ∀ X ∈ 𝓛, IsComponentOf X Yb := fun X hX => l119_isComponentOf_sSup h𝓛c hcomm𝓛 hX
  have hBcomm : ∀ z ∈ A0C, ∀ w ∈ A0C,
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w =
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) w * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z := by
    intro z hz w hw
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hAcomm _ (hA0A ((Subgroup.mem_subgroupOf).1 hz)) _ (hA0A ((Subgroup.mem_subgroupOf).1 hw))
  have hBnorm : Bbar ≤ Subgroup.normalizer ((Yb : Subgroup _) : Set _) := by
    rintro _ ⟨z, hz, rfl⟩
    exact bar_normalizes123 A0C hz
  have hA0Cel : IsElemAbelian p A0C := l119_isElemAbelian_subgroupOf hA0el (Cg a)
  have hBel : IsElemAbelian p Bbar :=
    CFSG.SectionRank.isElemAbelian_map hA0Cel _
  have hB_rank : 2 ≤ CFSG.Open.pRank p Bbar := le_trans hrA0 (l119_pRank_image_ge hp hA0C hA0el)
  have hKbe : (↥K ⧸ GLAPPrimeCore p ↥K) ≃* ↥Kb := quotEquivBarX hp hK.1 hK.2.1
  have hpY : p ∣ Nat.card ↥Yb :=
    dvd_trans (by rw [← Nat.card_congr hKbe.toEquiv]; exact p_dvd_card_barOf hp hK)
      (Subgroup.card_dvd_of_le (le_sSup hKbmem))
  have htrans : ∀ X ∈ 𝓛, ∀ X' ∈ 𝓛, ∃ b ∈ Bbar, GLBConj b X = X' := by
    rintro X ⟨w, hw, rfl⟩ X' ⟨w', hw', rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) (w⁻¹ * w'),
      Subgroup.mem_map_of_mem _ (A0C.mul_mem (A0C.inv_mem hw) hw'), l119_conj_trans w w'⟩
  have hz₀C : z₀ ∈ A0C := Subgroup.mem_subgroupOf.2 hz₀A
  have hb₀B : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Bbar :=
    Subgroup.mem_map_of_mem _ hz₀C
  have hz₀pow : z₀ ^ p = 1 := by
    apply Subtype.ext
    simpa using hApow _ hz₀A.2
  have hb₀1 : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ≠ 1 := by
    intro h
    apply hz₀1
    have h2 := l119_eq_one_of_pow_of_mem_core hp hz₀pow ((QuotientGroup.eq_one_iff _).1 h)
    simpa using congrArg Subtype.val h2
  have hJb₀ : QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∈ Subgroup.centralizer (Yb : Set _) ∨
      QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀ ∉ Subgroup.normalizer (Kb : Set _) := by
    rcases hbad with hN | hC
    · right
      intro hb
      exact hN (l119_mem_normalizer_of_bar hp hK z₀ hb)
    · left
      have hYc : Yb ≤ Subgroup.centralizer
          ({QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀} : Set _) := by
        refine sSup_le fun X hX => ?_
        obtain ⟨w, hw, rfl⟩ := hX
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact l119_centralizes_gLBConj (hBcomm z₀ hz₀C w hw) hC x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 := hYc hh
      rw [Subgroup.mem_centralizer_iff] at h2
      exact (h2 _ (Set.mem_singleton _)).symm
  have hLayer : ∀ b ∈ Bbar, b ≠ 1 → (b ∈ Subgroup.centralizer (Yb : Set _) ∨
      b ∉ Subgroup.normalizer (Kb : Set _)) →
      GLAPLayer p (Yb ⊓ Subgroup.centralizer ({b} : Set _)) ≤ barX p (Cg a) M := by
    intro b hb hb1 hJ
    have hbB := hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hzA : (z : G) ∈ A0 := Subgroup.mem_subgroupOf.1 hz
    have hz1 : (z : G) ≠ 1 := by
      intro h
      apply hb1
      have hzeq : z = 1 := Subtype.ext h
      rw [hzeq, map_one]
    have hzpow : (z : G) ^ p = 1 := hApow _ hzA.2
    have hzC : (z : G) ∈ Cg a := z.2
    have hzp : IsPGroup p (Subgroup.zpowers (z : G)) := l119_isPGroup_zpowers hzpow
    have hzpow' : z ^ p = 1 := by
      apply Subtype.ext
      simpa using hzpow
    have hbord : orderOf (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z) = p := by
      apply orderOf_eq_prime
      · rw [← map_pow, hzpow', map_one]
      · exact hb1
    have hbad : (z : G) ∉ Subgroup.normalizer (K : Set G) ∨ ∀ q ∈ barX p (Cg a) K,
        QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨(z : G), hzC⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨(z : G), hzC⟩ := by
      rcases hJ with hC | hN
      · right
        intro q hq
        exact ((Subgroup.mem_centralizer_iff.1 hC) q (le_sSup hKbmem hq)).symm
      · left
        intro hzN
        exact hN (mk_mem_normalizer_barX hK.1 hzN)
    have hYK : Yb ≤ barX p (Cg a) (⨆ y ∈ E ⊓ A, GLBConj y K) := by
      refine sSup_le fun X hX => ?_
      obtain ⟨w, hw, rfl⟩ := hX
      have hwA : (w : G) ∈ E ⊓ A := Subgroup.mem_subgroupOf.1 hw
      have h1 := l119_barX_gLBConj (p := p) (C := Cg a) (g := (w : G)) w.2 hK.1
      refine le_of_eq_of_le h1.symm (barX_mono p ?_)
      exact le_iSup₂_of_le (w : G) hwA le_rfl
    unfold GLAPLayer
    refine sSup_le fun Q hQ => ?_
    exact layer_le' hp hSec ha ha1 hnotD hK hbal hDiag h115 hzA hz1 hzC hzp hbad hYsub hYK hQ
  have hYM : Yb ≤ barX p (Cg a) M := by
    have hI22' := hI22 (↥(Cg a) ⧸ GLAPPrimeCore p ↥(Cg a)) p hp Bbar Yb Kb 𝓛 hBel hBnorm
      hKbmem hB_rank hpY rfl hYcomp hcomm𝓛 htrans
      ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) z₀, hb₀B, hb₀1, hJb₀⟩
    rw [hI22']
    refine sSup_le ?_
    rintro Z ⟨b, hb, hb1, hJ, rfl⟩
    exact hLayer b hb hb1 hJ
  have hKM' : barX p (Cg a) K ≤ barX p (Cg a) M := le_trans (le_sSup hKbmem) hYM
  apply hKM
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le hKM' hk (hK.1 hk)
  have hmM : m⁻¹ * k ∈ M := h111 hSec ha ha1 hmk
  have := M.mul_mem hm hmM
  simpa using this

structure Prep123 (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A : Subgroup G) (a : G)
    (K D : Subgroup G) (r : ℕ) : Prop extends Prep123a G m p B M E A a K D r where
  hA0norm : E ⊓ A ≤ Subgroup.normalizer (K : Set G)
  hA0faith : ∀ x ∈ E ⊓ A, x ∈ centBar p ⊤ K → x = 1

theorem prep123 (h111 : Prop111Statement) (h122 : Lemma122_i_iiStatement)
    (h115 : Prop115Statement) (hI191 : Lemma136c.Input19_1_O2) (hI22 : Input22_3_2)
    (hDiag : InputDiagBalance) (h : Cex121 G m p B M E A a) :
    ∃ (K D : Subgroup G) (r : ℕ), Prep123 G m p B M E A a K D r := by
  obtain ⟨K, D, r, P⟩ := prep123a h111 h122 hI191 h
  have hp : p.Prime := h.standing.prime
  have hSec : Sec11 G m p B M E A := h.toSec11
  have ha : a ∈ A := h.ha.1
  have ha1 : a ≠ 1 := h.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex h
  have hbal1 : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K :=
    not_isCompLocallyOTwoBalanced_one hp P.hr P.hDA P.hbal
  have hno := no_bad' hp hSec ha ha1 P.hK P.hKM hnotD hbal1 h111 hI22 hDiag h115
  have hACg : E ⊓ A ≤ Cg a := inter_le_cg h
  have hgood : ∀ x (hxA : x ∈ E ⊓ A), x ≠ 1 →
      x ∈ Subgroup.normalizer (K : Set G) ∧
        ¬ (∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩) := by
    intro x hxA hx1
    have h2 : ¬ (x ∉ Subgroup.normalizer (K : Set G) ∨
        ∀ q ∈ barX p (Cg a) K, QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩ * q =
          q * QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg a)) ⟨x, hACg hxA⟩) :=
      fun hc => hno ⟨⟨x, hACg hxA⟩, hxA, hx1, hc⟩
    refine ⟨?_, fun hall => h2 (Or.inr hall)⟩
    by_contra hN
    exact h2 (Or.inl hN)
  have hA0N : E ⊓ A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · exact (hgood x hx hx1).1
  refine ⟨K, D, r, ⟨P, hA0N, ?_⟩⟩
  intro x hx hc
  by_contra hx1
  obtain ⟨γ, hγ, hγx⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hc).1
  have hbar : barAut p K ⟨x, hA0N hx⟩ = 1 := by
    have hxγ : (⟨x, hA0N hx⟩ : ↥(Subgroup.normalizer (K : Set G))) = γ := Subtype.ext hγx.symm
    rw [hxγ]
    exact MonoidHom.mem_ker.1 hγ
  obtain ⟨_, hnc⟩ := hgood x hx hx1
  exact hnc (l119_centralizes_of_barAut hp P.hK (hACg hx) (hA0N hx) hbar)

theorem cov1 {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h112 : Prop112Statement) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) (hK : GLAPComponent p (Cg a) K) {e : G}
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1) : GLAPPrimeCoreOf p (K ⊓ Cg e) ≤ M := by
  have hsub : IsSubnormal (K ⊓ Cg e) (Cg a ⊓ Cg e) := isSubnormal_inf hK.2.1 _
  have hcore : GLAPPrimeCoreOf p (K ⊓ Cg e) ≤ GLAPPrimeCoreOf p (Cg a ⊓ Cg e) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp hsub
  have hM2 : GLAPPrimeCoreOf p (Cg2 e a) ≤ M := by
    rcases h112 hSec ha ha1 he he1 with h | h
    · exact h
    · exact absurd h hnotD
  rw [Sec12a.cg2_eq_inf] at hM2
  exact hcore.trans hM2

theorem cov2 {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h115 : Prop115Statement) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) (hK : GLAPComponent p (Cg a) K) {e : G}
    (he : e ∈ E ⊓ A) (he1 : e ≠ 1) {J : Subgroup G} (hJ : GLAPComponent p (K ⊓ Cg e) J)
    (h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J))
    (h2 : p = 3 → IsLTwoTwentySeven (barOf p J) → ¬ IsCompLocallyOTwoBalanced p 1 A J) : J ≤ M := by
  have hsub : IsSubnormal (K ⊓ Cg e) (Cg a ⊓ Cg e) := isSubnormal_inf hK.2.1 _
  have hJ' : GLAPComponent p (Cg2 e a) J := by
    rw [Sec12a.cg2_eq_inf]
    exact l119_glaPComponent_of_isSubnormal hp hsub hJ
  rcases h115 hSec ha ha1 he he1 hJ' h1 h2 with h | ⟨A1, hA1, haA1⟩
  · exact h
  · exact absurd ⟨A1, hA1, haA1⟩ hnotD

theorem type_trichotomy123 (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) :
    (∃ q : ℕ, q.Prime ∧ IsChevSimple q (barOf p K ⧸ Subgroup.center (barOf p K))) ∨
    (∃ n : ℕ, 5 ≤ n ∧ IsAltType n (barOf p K ⧸ Subgroup.center (barOf p K))) ∨
    (∃ s : TauCeti.SporadicName, IsSporType s (barOf p K ⧸ Subgroup.center (barOf p K))) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : IsSimpleGroup G := hS.simple
  have hCe : Cg a ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top hS.nonabelian h.ha.2
  have hKtop : K ≠ ⊤ := fun h' => hCe (top_le_iff.mp (h' ▸ hK.1))
  have hq1 : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hK
  haveI : IsSimpleGroup (barOf p K ⧸ Subgroup.center (barOf p K)) := hq1.2
  have hnonab := Prop1116Design.not_isCommutative_barQuot (barOf p K) hq1
  let φ : ↥K →* (barOf p K ⧸ Subgroup.center (barOf p K)) :=
    (QuotientGroup.mk' (Subgroup.center (barOf p K))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥K))
  have hφ : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  obtain ⟨i, ⟨f⟩⟩ := CFSG.KCore.KProperNonab.catalogue_of_surjective
    CFSG.Open.isCatalogGroup_isoInvariant hS.kProper K hKtop hnonab φ hφ
  rcases i with ⟨p', hp'⟩ | ⟨n, hn⟩ | idx | s
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnonab
    apply hxy
    apply f.injective
    rw [map_mul, map_mul]
    have : ∀ x y : Multiplicative (ZMod p'), x * y = y * x := fun x y => mul_comm x y
    exact this _ _
  · exact Or.inr (Or.inl ⟨n, hn, ⟨f⟩⟩)
  · exact Or.inl ⟨idx.1.characteristic, idx.1.characteristic_prime,
      Or.inl ⟨TauCeti.CFSGIndex.lie idx, rfl, ⟨f⟩⟩⟩
  · exact Or.inr (Or.inr ⟨s, ⟨f⟩⟩)

theorem le_M_of_barX_le {p : ℕ} {C K M : Subgroup G} (hKC : K ≤ C) (h : barX p C K ≤ barX p C M)
    (hcore : GLAPPrimeCoreOf p C ≤ M) : K ≤ M := by
  intro k hk
  obtain ⟨m, hm, hmk⟩ := exists_of_barX_le h hk (hKC hk)
  have := M.mul_mem hm (hcore hmk)
  simpa using this

theorem isElemAbelian_autBar {p : ℕ} {B' L : Subgroup G} (hB : IsElemAbelian p B') :
    IsElemAbelian p (autBar p B' L) :=
  CFSG.SectionRank.isElemAbelian_map
    (l119_isElemAbelian_subgroupOf (CFSG.Open.IsElemAbelian.mono hB inf_le_left) _) _

theorem iSup_le_of_cov1 {p : ℕ} (hp : p.Prime) {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
    (h112 : Prop112Statement) (hSec : Sec11 G m p B M E A) (ha : a ∈ A) (ha1 : a ≠ 1)
    (hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1) (hK : GLAPComponent p (Cg a) K) :
    (⨆ (b : G) (_ : b ∈ E ⊓ A) (_ : b ≠ 1), GLAPPrimeCoreOf p (K ⊓ Cg b)) ≤ M :=
  iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => cov1 hp h112 hSec ha ha1 hnotD hK hb hb1

@[expose] def Input19_6_4 : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → IsChevSimple p (Y ⧸ Subgroup.center Y) →
    ∀ B : Subgroup (MulAut Y), IsElemAbelian p B → ¬ IsLocallyOTwoBalanced p 1 B →
      p = 3 ∧ IsLTwoTwentySeven (Y ⧸ Subgroup.center Y) ∧ ¬ B ≤ innerAut Y

@[expose] def Input23_17 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K B : Subgroup G),
    GLAPComponent 3 X K → B ≤ X → IsElemAbelian 3 B → B ≤ Subgroup.normalizer (K : Set G) →
    (∀ x ∈ B, x ∈ centBar 3 ⊤ K → x = 1) → 2 ≤ CFSG.Open.pRank 3 B →
    IsLTwoTwentySeven (barOf 3 K ⧸ Subgroup.center (barOf 3 K)) → ¬ autBar 3 B K ≤ innerAut (barOf 3 K) →
      barX 3 X K ≤ barX 3 X (⨆ (b : G) (_ : b ∈ B) (_ : b ≠ 1),
        GLAPPrimeCoreOf 3 (K ⊓ Subgroup.centralizer ({b} : Set G)))

theorem case_chevp (h112 : Prop112Statement) (hI196 : Input19_6_4) (hI2317 : Input23_17)
    {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r)
    (hchev : IsChevSimple p (barOf p K ⧸ Subgroup.center (barOf p K))) : False := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have ha : a ∈ A := P.cex.ha.1
  have ha1 : a ≠ 1 := P.cex.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex P.cex
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hcore : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hbal1 : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K :=
    not_isCompLocallyOTwoBalanced_one hp P.hr P.hDA P.hbal
  obtain ⟨hp3, hL27, hout⟩ := hI196 p hp hp2 (barOf p K) hq hcore hchev (autBar p (E ⊓ A) K)
    (isElemAbelian_autBar (isElemAbelian_inter hSec)) hbal1
  subst hp3
  have hgen := hI2317 G (Cg a) K (E ⊓ A) P.hK (inter_le_cg P.cex) (isElemAbelian_inter hSec)
    P.hA0norm P.hA0faith hSec.pair.1.2.2 hL27 hout
  have hle : barX 3 (Cg a) K ≤ barX 3 (Cg a) M :=
    hgen.trans (barX_mono 3 (iSup_le_of_cov1 hp h112 hSec ha ha1 hnotD P.hK))
  exact P.hKM (le_M_of_barX_le P.hK.1 hle ((prop111_of_prop112 h112) hSec ha ha1))

@[expose] def Ke' (p : ℕ) (K : Subgroup G) (e : G) : Subgroup G :=
  GLAPPrimeCoreOf p (K ⊓ Cg e) ⊔ GLAPLayer p (K ⊓ Cg e)

@[expose] def Input19_17_1c : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → 5 ≤ n → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → IsAltType n (Y ⧸ Subgroup.center Y) →
      (¬ IsLocallyOTwoBalancedWrtP p 1 Y ↔ (n % p = 2 ∨ n % p = 4 % p ∨ (p = 5 ∧ n = 6)))

@[expose] def Input23_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ (X K B : Subgroup G),
    GLAPComponent p X K → B ≤ X → B ≤ Subgroup.normalizer (K : Set G) → IsElemAbelian p B → B ≠ ⊥ →
    (∀ x ∈ B, x ∈ centBar p ⊤ K → x = 1) →
    ∀ n : ℕ, 5 ≤ n → IsAltType n (barOf p K ⧸ Subgroup.center (barOf p K)) → ¬ p ∣ n →
      (barX p X K ≤ barX p X (⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Ke' p K e) ∨ Nat.card B < n) ∧
      (∀ e ∈ B, e ≠ 1 → ∀ J : Subgroup G, GLAPComponent p (K ⊓ Cg e) J →
        ∃ n' : ℕ, 5 ≤ n' ∧ n' < n ∧ n' % p = n % p ∧
          IsAltType n' (barOf p J ⧸ Subgroup.center (barOf p J)))

@[expose] def InputSchurAlt' : Prop :=
  ∀ (p n : ℕ), p.Prime → p ≠ 2 → ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y →
    GLAPPrimeCore p Y = ⊥ → IsAltType n (Y ⧸ Subgroup.center Y) →
      Subgroup.center Y = ⊥ ∨ (p = 3 ∧ (n = 6 ∨ n = 7))

theorem prop117_of_cex_false (h : Prop117_cex_falseStatement) (hs : Sec11 G m p B M E A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) {K : Subgroup G} (hK : GLAPComponent p (Cg a) K)
    (ht : Type117a p E A K ∨ Type117b p K ∨ Type117c p A K) :
    K ≤ M ∨ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := by
  by_contra hcon
  rw [not_or] at hcon
  by_cases hex : ∃ (E' A' : Subgroup G) (a' : G) (K' : Subgroup G),
      Cex117Base G m p B M E' A' a' K' ∧ ¬ NormalizesCyc M A' a'
  · obtain ⟨E', A', a', K', hb', hnn⟩ := hex
    exact h (⟨hb', fun _ => hnn⟩ : Cex117 G m p B M E' A' a' K')
  · exact h (⟨⟨hs, ⟨ha, ha1⟩, hK, ht, hcon.1, hcon.2⟩, fun hex' => absurd hex' hex⟩ :
      Cex117 G m p B M E A a K)

theorem not_dvd_of_congr {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : n % p = 2 ∨ n % p = 4 % p ∨ (p = 5 ∧ n = 6)) : ¬ p ∣ n := by
  intro hd
  have h0 : n % p = 0 := Nat.mod_eq_zero_of_dvd hd
  rcases h with h | h | ⟨rfl, rfl⟩
  · omega
  · rw [h0] at h
    have h4 : p ∣ 4 := Nat.dvd_of_mod_eq_zero h.symm
    have : p ∣ 2 ^ 2 := by simpa using h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this))
  · omega

theorem case_alt (h112 : Prop112Statement) (h115 : Prop115Statement) (h117 : Prop117_cex_falseStatement)
    (hI1917 : Input19_17_1c) (hI234 : Input23_4) (hSchur : InputSchurAlt')
    (hL27 : Prop1116.InputNotL27Pi) {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r)
    {n : ℕ} (hn5 : 5 ≤ n) (hn : IsAltType n (barOf p K ⧸ Subgroup.center (barOf p K))) : False := by
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have ha : a ∈ A := P.cex.ha.1
  have ha1 : a ≠ 1 := P.cex.ha.2
  have hnotD : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ a ∈ A1 := lemma122_ii_of_cex P.cex
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp P.hK
  have hcore : GLAPPrimeCore p (barOf p K) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hbal1 : ¬ IsCompLocallyOTwoBalanced p 1 (E ⊓ A) K :=
    not_isCompLocallyOTwoBalanced_one hp P.hr P.hDA P.hbal
  have hBel : IsElemAbelian p (autBar p (E ⊓ A) K) := isElemAbelian_autBar (isElemAbelian_inter hSec)
  have hbalP : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p K) := fun hb => hbal1 (hb _ hBel)
  have hcong := ((hI1917 p n hp hp2 hn5 (barOf p K) hq hcore hn).1 hbalP)
  have hpn : ¬ p ∣ n := not_dvd_of_congr hp hp2 hcong
  have hA0ne : E ⊓ A ≠ ⊥ := by
    intro h0
    have := sq_le_card_inter hSec
    rw [h0, Subgroup.card_bot] at this
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨hdich, hcomp⟩ := hI234 G p hp hp2 (Cg a) K (E ⊓ A) P.hK (inter_le_cg P.cex) P.hA0norm
    (isElemAbelian_inter hSec) hA0ne P.hA0faith n hn5 hn hpn
  rcases hdich with hgen | hbig
  ·
    have hKe : (⨆ (e : G) (_ : e ∈ E ⊓ A) (_ : e ≠ 1), Ke' p K e) ≤ M := by
      refine iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_
      refine sup_le (cov1 hp h112 hSec ha ha1 hnotD P.hK he he1) ?_
      unfold GLAPLayer
      refine sSup_le fun J hJ => ?_
      obtain ⟨n', hn'5, hn'n, hn'mod, hJA⟩ := hcomp e he he1 J hJ
      have hqJ : CFSG.Open.IsQuasisimple (barOf p J) :=
        CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
      have hcoreJ : GLAPPrimeCore p (barOf p J) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
      have hcong' : n' % p = 2 ∨ n' % p = 4 % p ∨ (p = 5 ∧ n' = 6) := by
        rcases hcong with h1 | h1 | ⟨rfl, rfl⟩
        · exact Or.inl (hn'mod.trans h1)
        · exact Or.inr (Or.inl (hn'mod.trans h1))
        · omega
      have h1 : ¬ IsLocallyOTwoBalancedWrtP p 1 (barOf p J) :=
        ((hI1917 p n' hp hp2 hn'5 (barOf p J) hqJ hcoreJ hJA).2 hcong')
      refine cov2 hp h115 hSec ha ha1 hnotD P.hK he he1 hJ h1 ?_
      intro hp3 hL
      exfalso
      subst hp3
      have hpn' : n' % 3 ≠ 0 := by
        rw [hn'mod]
        intro h0
        exact hpn (Nat.dvd_of_mod_eq_zero h0)
      exact hL27 (barOf 3 J) hL (Or.inl ⟨n', hn'5, hJA, Or.inr (Or.inr ⟨rfl, hpn'⟩)⟩)
    exact P.hKM (le_M_of_barX_le P.hK.1 (hgen.trans (barX_mono p hKe))
      ((prop111_of_prop112 h112) hSec ha ha1))
  ·
    have hn9 : p ^ 2 < n := lt_of_le_of_lt (sq_le_card_inter hSec) hbig
    have hz : Subgroup.center (barOf p K) = ⊥ := by
      rcases hSchur p n hp hp2 (barOf p K) hq hcore hn with h0 | ⟨hp3, hn67⟩
      · exact h0
      · exfalso
        subst hp3
        omega
    have hAlt : IsAltType n (barOf p K) :=
      l119_isAltType_congr n (Prop1116Design.mulEquivQuotCenterOfEqBot hz).symm hn
    have hcardpow : Nat.card (E ⊓ A : Subgroup G) = p ^ CFSG.Open.pRank p (E ⊓ A) :=
      card_eq_pow_pRank hp (isElemAbelian_inter hSec)
    have ht : Type117a p E A K := ⟨n, hAlt, hcardpow ▸ hbig, hpn⟩
    rcases prop117_of_cex_false h117 hSec ha ha1 P.hK (Or.inl ht) with hKM | hD
    · exact P.hKM hKM
    · exact hnotD hD

theorem barAut_eq_one_of_mem_core {p : ℕ} (hp : p.Prime) {a : G} {K : Subgroup G}
    (hK : GLAPComponent p (Cg a) K) {c : G} (hcN : c ∈ Subgroup.normalizer (K : Set G))
    (hc : c ∈ GLAPPrimeCoreOf p (Cg a)) : barAut p K ⟨c, hcN⟩ = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
  apply QuotientGroup.eq.2
  have hzG : ((((K.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x : ↥K)) : G) =
      (c * (x : G) * c⁻¹)⁻¹ * (x : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨c, hcN⟩ x]
  have hcN' : (((x⁻¹ : ↥K) : G)) * c⁻¹ * (((x⁻¹ : ↥K) : G))⁻¹ ∈ GLAPPrimeCoreOf p (Cg a) :=
    sec11_glaPPrimeCoreOf_conj_mem (hK.1 (x⁻¹ : ↥K).2) ((GLAPPrimeCoreOf p (Cg a)).inv_mem hc)
  have hmemN : ((((K.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x : ↥K)) : G) ∈
      GLAPPrimeCoreOf p (Cg a) := by
    rw [hzG]
    have : (c * (x : G) * c⁻¹)⁻¹ * (x : G) =
        c * ((((x⁻¹ : ↥K) : G)) * c⁻¹ * (((x⁻¹ : ↥K) : G))⁻¹) := by
      simp only [Subgroup.coe_inv]; group
    rw [this]
    exact (GLAPPrimeCoreOf p (Cg a)).mul_mem hc hcN'
  have hmem : ((((K.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x : ↥K)) : G) ∈
      K ⊓ GLAPPrimeCoreOf p (Cg a) := ⟨((K.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x : ↥K).2, hmemN⟩
  rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hK.2.1] at hmem
  obtain ⟨z', hz', hzz'⟩ := Subgroup.mem_map.1 hmem
  have : z' = (K.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x := Subtype.ext hzz'
  rw [← this]
  exact hz'

theorem exists_fixed_rep {P X N : Subgroup G} (hPX : P ≤ Subgroup.normalizer (X : Set G))
    (hNX : N ≤ X) (hXN : X ≤ Subgroup.normalizer (N : Set G))
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hNsolv : Group.IsSolvable N)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card N)) {g : G} (hgX : g ∈ X)
    (hg : ∀ x ∈ P, x * g * x⁻¹ * g⁻¹ ∈ N) :
    ∃ c ∈ X, (∀ x ∈ P, x * c * x⁻¹ = c) ∧ c⁻¹ * g ∈ N := by
  classical
  let α : ↥P →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion hPX)
  have hα : ∀ (k : ↥P) (x : ↥X), ((α k x : ↥X) : G) = (k : G) * x * (k : G)⁻¹ :=
    fun k x => Subgroup.normalizerMonoidHom_apply_apply_coe X (Subgroup.inclusion hPX k) x
  letI : MulDistribMulAction ↥P ↥X := MulDistribMulAction.compHom X α
  have hsmul : ∀ (k : ↥P) (x : ↥X), k • x = α k x := fun _ _ => rfl
  let N' : Subgroup ↥X := N.subgroupOf X
  haveI hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hinv : CFSG.IsInvariant ↥P ↥X N' := ⟨fun k x => by
    show (x : G) ∈ N ↔ ((k • x : ↥X) : G) ∈ N
    rw [hsmul, hα]
    exact Subgroup.mem_normalizer_iff.1 (hPN k.2) (x : G)⟩
  have hsolv' : Group.IsSolvable ↥N' := by
    haveI := hNsolv
    exact solvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hNX).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNX).symm.surjective
  have hcard : Nat.card ↥N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv
  have hg' : ∀ k : ↥P, (⟨g, hgX⟩ : ↥X)⁻¹ * (k • (⟨g, hgX⟩ : ↥X)) ∈ N' := by
    intro k
    show ((⟨g, hgX⟩ : ↥X)⁻¹ * (k • (⟨g, hgX⟩ : ↥X)) : ↥X).1 ∈ N
    rw [hsmul]
    have hk := hg (k : G) k.2
    have hcalc : (((⟨g, hgX⟩ : ↥X)⁻¹ * (α k ⟨g, hgX⟩) : ↥X) : G) =
        g⁻¹ * ((k : G) * g * (k : G)⁻¹ * g⁻¹) * g := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα]; group
    rw [hcalc]
    have := (Subgroup.mem_normalizer_iff.1 (hXN (X.inv_mem hgX)) _).1 hk
    simpa [mul_assoc] using this
  obtain ⟨c, hc, hcg⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed (B := ↥P) N' hinv hsolv'
    (by rw [hcard]; exact hcop) ⟨g, hgX⟩ hg'
  refine ⟨c, c.2, fun x hx => ?_, hcg⟩
  have h1 : (⟨x, hx⟩ : ↥P) • c = c := hc ⟨x, hx⟩
  have h2 := congrArg Subtype.val h1
  rw [hsmul, hα] at h2
  exact h2

theorem inter_comm_of_le (h : Sec11 G m p B M E A) {D : Subgroup G} (hDA : D ≤ E ⊓ A) {x d : G}
    (hx : x ∈ E ⊓ A) (hd : d ∈ D) : x * d = d * x :=
  CFSG.Open.IsElemAbelian.comm (isElemAbelian_inter h) hx (hDA hd)

theorem mem_normalizer_centralizer_of_comm {D : Subgroup G} {x : G} (hx : ∀ d ∈ D, x * d = d * x) :
    x ∈ Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  have hx' : ∀ d ∈ D, x⁻¹ * d = d * x⁻¹ := fun d hd => by
    calc x⁻¹ * d = x⁻¹ * (d * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * d) * x⁻¹ := by rw [hx d hd]
      _ = d * x⁻¹ := by group
  constructor
  · intro hy d hd
    have e1 : d * (x * y * x⁻¹) = x * (d * y) * x⁻¹ := by
      calc d * (x * y * x⁻¹) = (d * x) * y * x⁻¹ := by group
        _ = (x * d) * y * x⁻¹ := by rw [← hx d hd]
        _ = x * (d * y) * x⁻¹ := by group
    have e2 : (x * y * x⁻¹) * d = x * (y * d) * x⁻¹ := by
      calc (x * y * x⁻¹) * d = x * y * (x⁻¹ * d) := by group
        _ = x * y * (d * x⁻¹) := by rw [hx' d hd]
        _ = x * (y * d) * x⁻¹ := by group
    rw [e1, e2, hy d hd]
  · intro hy d hd
    have e1 : d * (x * y * x⁻¹) = x * (d * y) * x⁻¹ := by
      calc d * (x * y * x⁻¹) = (d * x) * y * x⁻¹ := by group
        _ = (x * d) * y * x⁻¹ := by rw [← hx d hd]
        _ = x * (d * y) * x⁻¹ := by group
    have e2 : (x * y * x⁻¹) * d = x * (y * d) * x⁻¹ := by
      calc (x * y * x⁻¹) * d = x * y * (x⁻¹ * d) := by group
        _ = x * y * (d * x⁻¹) := by rw [hx' d hd]
        _ = x * (y * d) * x⁻¹ := by group
    have h3 := hy d hd
    rw [e1, e2] at h3
    have h4 := mul_right_cancel h3
    exact mul_left_cancel h4

theorem inter_le_normalizer_TD (h : Cex121 G m p B M E A a) {D : Subgroup G} (hDA : D ≤ E ⊓ A) :
    E ⊓ A ≤ Subgroup.normalizer ((TD p M a D : Subgroup G) : Set G) := fun x hx =>
  Sec12a.mem_normalizer_inf (inter_le_normalizer_tof h hx)
    (mem_normalizer_centralizer_of_comm fun d hd => inter_comm_of_le h.toSec11 hDA hx hd)

theorem mem_centBar_iff {p : ℕ} {X L : Subgroup G} {r' : G} :
    r' ∈ centBar p X L ↔ r' ∈ X ∧ ∃ hN : r' ∈ Subgroup.normalizer (L : Set G),
      barAut p L ⟨r', hN⟩ = 1 := by
  constructor
  · intro hr'
    obtain ⟨γ, hγ, hγr⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hr').1
    refine ⟨(Subgroup.mem_inf.1 hr').2, by rw [← hγr]; exact γ.2, ?_⟩
    have : (⟨r', by rw [← hγr]; exact γ.2⟩ : ↥(Subgroup.normalizer (L : Set G))) = γ :=
      Subtype.ext hγr.symm
    rw [this]
    exact MonoidHom.mem_ker.1 hγ
  · rintro ⟨hrX, hN, hb⟩
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨r', hN⟩, MonoidHom.mem_ker.2 hb, rfl⟩, hrX⟩

theorem conj_mem_centBar {p : ℕ} {X L : Subgroup G} {y z : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyX : y ∈ Subgroup.normalizer (X : Set G))
    (hz : z ∈ centBar p X L) : y * z * y⁻¹ ∈ centBar p X L := by
  obtain ⟨hzX, hzN, hzb⟩ := mem_centBar_iff.1 hz
  have hN : y * z * y⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem ((Subgroup.normalizer (L : Set G)).mul_mem hyL hzN)
      ((Subgroup.normalizer (L : Set G)).inv_mem hyL)
  refine mem_centBar_iff.2 ⟨(Subgroup.mem_normalizer_iff.1 hyX z).1 hzX, hN, ?_⟩
  have hh : (⟨y * z * y⁻¹, hN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨z, hzN⟩ *
        (⟨y, hyL⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ := rfl
  rw [hh, map_mul, map_mul, hzb, mul_one, map_inv, mul_inv_cancel]

theorem exists_comm_nontriv {K D : Subgroup G} {r : ℕ} (P : Prep123 G m p B M E A a K D r)
    (hDne : D ≠ E ⊓ A) :
    ∃ t ∈ TD p M a D, ∃ x ∈ E ⊓ A, ∃ hN : t * x * t⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G),
      barAut p K ⟨t * x * t⁻¹ * x⁻¹, hN⟩ ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup G := TD p M a D with hX
  have hT2 : IsPGroup 2 ↥X := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left
  set R : Subgroup G := centBar p X K with hR
  have hRX : R ≤ X := inf_le_right
  have hA0X : E ⊓ A ≤ Subgroup.normalizer (X : Set G) := inter_le_normalizer_TD P.cex P.hDA
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := P.hTDnorm
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    Subgroup.mem_normalizer_iff.2 fun z => ⟨fun hz => conj_mem_centBar (hXK hy)
      (Subgroup.le_normalizer hy) hz, fun hz => by
        have h1 := conj_mem_centBar (hXK (X.inv_mem hy)) (Subgroup.le_normalizer (X.inv_mem hy)) hz
        simpa [mul_assoc] using h1⟩
  have hA0R : E ⊓ A ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    Subgroup.mem_normalizer_iff.2 fun z => ⟨fun hz => conj_mem_centBar (P.hA0norm hy) (hA0X hy) hz,
      fun hz => by
        have h1 := conj_mem_centBar (P.hA0norm ((E ⊓ A).inv_mem hy))
          (hA0X ((E ⊓ A).inv_mem hy)) hz
        simpa [mul_assoc] using h1⟩
  have hR2 : IsPGroup 2 ↥R :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (alphaOf p M ⊓ Cg a)).to_le (hRX.trans inf_le_left)
  have hRsolv : Group.IsSolvable ↥R := by
    haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card (E ⊓ A : Subgroup G)) (Nat.card R) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).1 hR2
    rw [card_eq_pow_pRank hp (isElemAbelian_inter P.cex.toSec11), hj]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hall : ∀ t ∈ X, ∀ x ∈ E ⊓ A, x * t * x⁻¹ * t⁻¹ ∈ R := by
    intro t ht x hx
    have hNK : Subgroup.normalizer (K : Set G) =
        Subgroup.normalizer (K : Set G) := rfl
    have hxK : x ∈ Subgroup.normalizer (K : Set G) := P.hA0norm hx
    have htK : t ∈ Subgroup.normalizer (K : Set G) := hXK ht
    have hN : t * x * t⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).mul_mem htK hxK)
          ((Subgroup.normalizer (K : Set G)).inv_mem htK))
        ((Subgroup.normalizer (K : Set G)).inv_mem hxK)
    have hN' : x * t * x⁻¹ * t⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).mul_mem hxK htK)
          ((Subgroup.normalizer (K : Set G)).inv_mem hxK))
        ((Subgroup.normalizer (K : Set G)).inv_mem htK)
    have h0 := hcon t ht x hx hN
    refine mem_centBar_iff.2 ⟨?_, hN', ?_⟩
    · have h1 : x * t * x⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hA0X hx) t).1 ht
      exact X.mul_mem h1 (X.inv_mem ht)
    · have hh : (⟨x * t * x⁻¹ * t⁻¹, hN'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
          (⟨t * x * t⁻¹ * x⁻¹, hN⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ :=
        Subtype.ext (by simp [mul_assoc])
      rw [hh, map_inv, h0, inv_one]
  have hbar1 : ∀ t ∈ X, ∀ hN : t ∈ Subgroup.normalizer (K : Set G), barAut p K ⟨t, hN⟩ = 1 := by
    intro t ht hN
    obtain ⟨c, hcX, hcfix, hcr⟩ := exists_fixed_rep hA0X hRX hXR hA0R hRsolv hcop ht (hall t ht)
    have hcT : c ∈ TD p M a (E ⊓ A) :=
      ⟨hcX.1, Subgroup.mem_centralizer_iff.2 fun x hx => by
        exact mul_inv_eq_iff_eq_mul.1 (hcfix x hx)⟩
    have hcN : c ∈ GLAPPrimeCoreOf p (Cg a) := TD_inter_le P.hDA hDne P.hDmax hcT
    have hcNK : c ∈ Subgroup.normalizer (K : Set G) := hXK hcX
    have hb_c : barAut p K ⟨c, hcNK⟩ = 1 := barAut_eq_one_of_mem_core hp P.hK hcNK hcN
    obtain ⟨-, hrN, hrb⟩ := mem_centBar_iff.1 hcr
    have : (⟨t, hN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨c, hcNK⟩ * ⟨c⁻¹ * t, hrN⟩ :=
      Subtype.ext (by simp)
    rw [this, map_mul, hb_c, hrb, one_mul]
  apply P.hTDK
  refine Subgroup.commutator_le.2 fun k hk t ht => ?_
  have hb := hbar1 t ht (P.hTDnorm ht)
  have hkinv : k⁻¹ ∈ K := K.inv_mem hk
  have hq : (barAut p K ⟨t, P.hTDnorm ht⟩) (QuotientGroup.mk (⟨k⁻¹, hkinv⟩ : ↥K)) =
      QuotientGroup.mk (⟨k⁻¹, hkinv⟩ : ↥K) := by
    rw [hb]; rfl
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at hq
  have hmem := QuotientGroup.eq.1 hq
  have hzval : ((((K.normalizerMonoidHom ⟨t, P.hTDnorm ht⟩ ⟨k⁻¹, hkinv⟩)⁻¹ * ⟨k⁻¹, hkinv⟩ : ↥K)) : G) =
      t * k * t⁻¹ * k⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨t, P.hTDnorm ht⟩ ⟨k⁻¹, hkinv⟩]
    simp [mul_assoc]
  have hmemG : t * k * t⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf p K := Subgroup.mem_map.2 ⟨_, hmem, hzval⟩
  have hmemG' : (t * k * t⁻¹ * k⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p (Cg a) :=
    (GLAPPrimeCoreOf p (Cg a)).inv_mem (glaPPrimeCoreOf_le_of_isSubnormal hp P.hK.2.1 hmemG)
  simpa [commutatorElement_def, mul_assoc] using hmemG'

theorem innerAut_normal (Y : Type*) [Group Y] : (innerAut Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply]

@[expose] noncomputable def DeltaImage (p : ℕ) (X D K : Subgroup G) : Subgroup (MulAut (barOf p K)) :=
  ((localDeltaTwoIn X D).subgroupOf (Subgroup.normalizer (K : Set G))).map (barAut p K)

@[expose] def Input19_1_O2_img : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], CFSG.Open.IsKProper G →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (k : ℕ), 1 ≤ k → ∀ (X D : Subgroup G), X ≠ ⊤ → IsEkIn p k X D →
      ∀ K : Subgroup G, GLAPComponent p X K → ¬ ⁅K, localDeltaTwoIn X D⁆ ≤ GLAPPrimeCoreOf p X →
        DeltaImage p X D K ≤
          localDeltaTwoIn (innerAut (barOf p K) ⊔ DeltaImage p X D K) (autBar p D K)

theorem inter_le_normalizer_delta (h : Sec11 G m p B M E A) {a : G} (ha : a ∈ A) {D : Subgroup G}
    (hDA : D ≤ E ⊓ A) :
    E ⊓ A ≤ Subgroup.normalizer ((localDeltaTwoIn (Cg a) D : Subgroup G) : Set G) := by
  have key : ∀ x ∈ E ⊓ A, ∀ y, y ∈ localDeltaTwoIn (Cg a) D →
      x * y * x⁻¹ ∈ localDeltaTwoIn (Cg a) D := by
    intro x hx y hy
    have hxC : x ∈ Cg a := inter_le_cg' h ha hx
    unfold localDeltaTwoIn at hy ⊢
    simp only [Subgroup.mem_iInf] at hy ⊢
    intro d hd hd1
    have hyd := hy d hd hd1
    have hxd : x ∈ Subgroup.normalizer ((Cg a ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      Sec12a.mem_normalizer_inf (Subgroup.le_normalizer hxC)
        (Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.2 fun z hz => by
          rw [Set.mem_singleton_iff.1 hz]
          exact (inter_comm_of_le h hDA hx hd).symm))
    exact (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxd) y).1 hyd
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key x hx y hy, fun hy => ?_⟩
  have := key x⁻¹ ((E ⊓ A).inv_mem hx) _ hy
  simpa [mul_assoc] using this

theorem mem_normalizer_sup' {Y : Type*} [Group Y] {A B : Subgroup Y} {g : Y}
    (hA : g ∈ Subgroup.normalizer (A : Set Y)) (hB : g ∈ Subgroup.normalizer (B : Set Y)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup Y) : Set Y) := by
  have key : ∀ g : Y, g ∈ Subgroup.normalizer (A : Set Y) → g ∈ Subgroup.normalizer (B : Set Y) →
      ∀ h ∈ A ⊔ B, g * h * g⁻¹ ∈ A ⊔ B := by
    intro g hA hB h hh
    have hle : (A ⊔ B).map (MulAut.conj g).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hA y).1 hy
      · rintro _ ⟨y, hy, rfl⟩
        exact (Subgroup.mem_normalizer_iff.1 hB y).1 hy
    exact hle ⟨h, hh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hA hB h, fun hh => ?_⟩
  have := key g⁻¹ ((Subgroup.normalizer (A : Set Y)).inv_mem hA)
    ((Subgroup.normalizer (B : Set Y)).inv_mem hB) _ hh
  simpa [mul_assoc] using this

theorem mem_normalizer_of_conj_mem {Y : Type*} [Group Y] {S : Subgroup Y} {v : Y}
    (h1 : ∀ w ∈ S, v * w * v⁻¹ ∈ S) (h2 : ∀ w ∈ S, v⁻¹ * w * v⁻¹⁻¹ ∈ S) :
    v ∈ Subgroup.normalizer (S : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  exact ⟨h1 h, fun hm => by simpa [mul_assoc] using h2 _ hm⟩

theorem weak_nonbal_gen (hI191img : Input19_1_O2_img) (h122 : Lemma122_i_iiStatement) {K D : Subgroup G}
    {r : ℕ} (P : Prep123 G m p B M E A a K D r) (hDne : D ≠ E ⊓ A) :
    ¬ IsWeaklyLocallyOTwoBalanced p r (autBar p (E ⊓ A) K) := by
  classical
  intro hweak
  have hp : p.Prime := P.cex.standing.prime
  have hp2 : p ≠ 2 := P.cex.standing.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup G := P.cex.standing.simple
  have hSec : Sec11 G m p B M E A := P.cex.toSec11
  have ha : a ∈ A := P.cex.ha.1
  have hDel : IsElemAbelian p D := CFSG.Open.IsElemAbelian.mono (isElemAbelian_inter hSec) P.hDA
  have hXtop : Cg a ≠ ⊤ := Lemma136c.l136c_centralizer_ne_top P.cex.standing.nonabelian P.cex.ha.2
  have hDX : IsEkIn p r (Cg a) D := ⟨P.hDA.trans (inter_le_cg P.cex), hDel, P.hDcard⟩
  have hTDle : TD p M a D ≤ localDeltaTwoIn (Cg a) D := TD_le_delta h122 P.cex P.hDA
  have hKΔ : ¬ ⁅K, localDeltaTwoIn (Cg a) D⁆ ≤ GLAPPrimeCoreOf p (Cg a) :=
    fun hΔ => P.hTDK (le_trans (Subgroup.commutator_mono le_rfl hTDle) hΔ)
  have himg := hI191img G P.cex.standing.kProper p hp hp2 r P.hr (Cg a) D hXtop hDX K P.hK hKΔ
  have hDt : IsEkIn p r (autBar p (E ⊓ A) K) (autBar p D K) := by
    have h1 := Lemma136c.l136c_isEkIn_autBar hDX P.hDnorm P.hDfaith
    exact ⟨autBar_mono P.hDA, h1.2.1, h1.2.2⟩
  set H : Subgroup (MulAut (barOf p K)) := innerAut (barOf p K) ⊔ DeltaImage p (Cg a) D K with hH
  have hHinn : innerAut (barOf p K) ≤ H := le_sup_left
  have hdelta_norm : ∀ x ∈ E ⊓ A, ∀ y ∈ localDeltaTwoIn (Cg a) D, x * y * x⁻¹ ∈ localDeltaTwoIn (Cg a) D :=
    fun x hx y hy => (Subgroup.mem_normalizer_iff.1 (inter_le_normalizer_delta hSec ha P.hDA hx) y).1 hy
  have hconj : ∀ x ∈ E ⊓ A, ∀ hxN : x ∈ Subgroup.normalizer (K : Set G),
      ∀ w ∈ DeltaImage p (Cg a) D K,
        barAut p K ⟨x, hxN⟩ * w * (barAut p K ⟨x, hxN⟩)⁻¹ ∈ DeltaImage p (Cg a) D K := by
    intro x hxA hxN w hw
    obtain ⟨⟨y, hyN⟩, hyΔ, rfl⟩ := hw
    have hyΔ' : y ∈ localDeltaTwoIn (Cg a) D := Subgroup.mem_subgroupOf.1 hyΔ
    have hxy : x * y * x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).mul_mem hxN hyN)
        ((Subgroup.normalizer (K : Set G)).inv_mem hxN)
    refine ⟨⟨x * y * x⁻¹, hxy⟩, Subgroup.mem_subgroupOf.2 (hdelta_norm x hxA y hyΔ'), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hnormH : autBar p (E ⊓ A) K ≤ Subgroup.normalizer (H : Set (MulAut (barOf p K))) := by
    rintro v ⟨⟨x, hxN⟩, hxm, rfl⟩
    have hxA : x ∈ E ⊓ A := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hxm)).1
    have hInn : (innerAut (barOf p K)).Normal := innerAut_normal (barOf p K)
    have hv0 : barAut p K ⟨x, hxN⟩ ∈ Subgroup.normalizer (innerAut (barOf p K) : Set _) :=
      Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hInn.conj_mem _ hh _, fun hh => by
        simpa [mul_assoc] using hInn.conj_mem _ hh (barAut p K ⟨x, hxN⟩)⁻¹⟩
    have hv1 : barAut p K ⟨x, hxN⟩ ∈ Subgroup.normalizer (DeltaImage p (Cg a) D K : Set _) := by
      refine mem_normalizer_of_conj_mem (hconj x hxA hxN) (fun w hw => ?_)
      have hx1 : x⁻¹ ∈ E ⊓ A := (E ⊓ A).inv_mem hxA
      have hxN' : x⁻¹ ∈ Subgroup.normalizer (K : Set G) := (Subgroup.normalizer (K : Set G)).inv_mem hxN
      have := hconj x⁻¹ hx1 hxN' w hw
      have e : barAut p K ⟨x⁻¹, hxN'⟩ = (barAut p K ⟨x, hxN⟩)⁻¹ := by
        rw [← map_inv]; rfl
      rw [e, inv_inv] at this
      exact this
    exact mem_normalizer_sup' hv0 hv1
  have hweak' := hweak (autBar p D K) hDt H hHinn hnormH
  obtain ⟨t, ht, x, hx, hN, hne⟩ := exists_comm_nontriv P hDne
  have htN : t ∈ Subgroup.normalizer (K : Set G) := P.hTDnorm ht
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := P.hA0norm hx
  have htΔ : barAut p K ⟨t, htN⟩ ∈ DeltaImage p (Cg a) D K :=
    ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.2 (hTDle ht), rfl⟩
  have htH : barAut p K ⟨t, htN⟩ ∈ localDeltaTwoIn H (autBar p D K) := himg htΔ
  have hxA : barAut p K ⟨x, hxN⟩ ∈ autBar p (E ⊓ A) K :=
    ⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨hx, hxN⟩), rfl⟩
  have hcm := Subgroup.commutator_mem_commutator htH hxA
  rw [hweak', commutatorElement_def] at hcm
  apply hne
  have e : barAut p K ⟨t * x * t⁻¹ * x⁻¹, hN⟩ = barAut p K ⟨t, htN⟩ * barAut p K ⟨x, hxN⟩ *
      (barAut p K ⟨t, htN⟩)⁻¹ * (barAut p K ⟨x, hxN⟩)⁻¹ := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e]
  exact Subgroup.mem_bot.1 hcm

theorem weak_nonbal (hI191img : Input19_1_O2_img) (h122 : Lemma122_i_iiStatement) {K D : Subgroup G}
    {r : ℕ} (P : Prep123 G m p B M E A a K D r) (hr1 : r = 1) :
    ¬ IsWeaklyLocallyOTwoBalanced p 1 (autBar p (E ⊓ A) K) := by
  have hp : p.Prime := P.cex.standing.prime
  have hDne : D ≠ E ⊓ A := by
    intro hDeq
    have h1 : p ^ 2 ≤ Nat.card (E ⊓ A : Subgroup G) := sq_le_card_inter P.cex.toSec11
    have h2 : Nat.card D = p := by rw [P.hDcard, hr1, pow_one]
    rw [hDeq] at h2
    rw [h2] at h1
    have : p ^ 2 ≤ p ^ 1 := by simpa using h1
    have := Nat.pow_le_pow_iff_right hp.one_lt |>.1 this
    omega
  subst hr1
  exact weak_nonbal_gen hI191img h122 P hDne

end Lemma123
