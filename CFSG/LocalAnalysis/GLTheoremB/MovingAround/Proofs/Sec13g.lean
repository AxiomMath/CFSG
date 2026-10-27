module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.WitnessTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec13g

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open scoped Pointwise

section Helpers

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_istar_eq {p : ℕ} {M D I : Subgroup G} (hI : I = Istar p M D) :
    M ≤ Subgroup.normalizer (I : Set G) := by
  intro g hg
  have h1 : GLBConj g I = I := by rw [hI]; exact istar_conj_eq p hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [← mem_gLBConj, h1]

noncomputable abbrev blkKer (p : ℕ) (M I : Subgroup G) : Subgroup G :=
  ((MonoidHom.ker (barAut p I)).map (Subgroup.normalizer (I : Set G)).subtype) ⊓ M

theorem mem_blkKer_iff {p : ℕ} {M I : Subgroup G} {x : G} :
    x ∈ blkKer p M I ↔ x ∈ M ∧ ∃ hx : x ∈ Subgroup.normalizer (I : Set G), barAut p I ⟨x, hx⟩ = 1 := by
  unfold blkKer
  rw [Subgroup.mem_inf, mem_centK_iff]
  exact and_comm

theorem centBar_eq_blkKer_inf {p : ℕ} {M I R : Subgroup G} (hRM : R ≤ M) :
    centBar p R I = blkKer p M I ⊓ R := by
  ext x
  unfold centBar blkKer
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hk, hR⟩
    exact ⟨⟨hk, hRM hR⟩, hR⟩
  · rintro ⟨⟨hk, -⟩, hR⟩
    exact ⟨hk, hR⟩

theorem blkKer_conj_mem {p : ℕ} {M I : Subgroup G} (hMN : M ≤ Subgroup.normalizer (I : Set G))
    {m k : G} (hm : m ∈ M) (hk : k ∈ blkKer p M I) : m * k * m⁻¹ ∈ blkKer p M I := by
  obtain ⟨hkM, hkN, hk1⟩ := mem_blkKer_iff.1 hk
  have hmN : m ∈ Subgroup.normalizer (I : Set G) := hMN hm
  have hmkN : m * k * m⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normalizer (I : Set G)).mul_mem ((Subgroup.normalizer (I : Set G)).mul_mem hmN hkN)
      ((Subgroup.normalizer (I : Set G)).inv_mem hmN)
  refine mem_blkKer_iff.2 ⟨M.mul_mem (M.mul_mem hm hkM) (M.inv_mem hm), hmkN, ?_⟩
  have e : (⟨m * k * m⁻¹, hmkN⟩ : ↥(Subgroup.normalizer (I : Set G))) =
      ⟨m, hmN⟩ * ⟨k, hkN⟩ * (⟨m, hmN⟩)⁻¹ := Subtype.ext (by simp)
  rw [e, map_mul, map_mul, map_inv, hk1]
  simp

theorem blkKer_inf_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M I : Subgroup G}
    (hcomp : GLAPComponent p M I) (hbl : IsGLBlock M I) :
    I ⊓ blkKer p M I ≤ GLAPPrimeCoreOf p I := by
  intro x hx
  obtain ⟨hxI, hxK⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨-, hxN, hx1⟩ := mem_blkKer_iff.1 hxK
  have h := mem_pPrimeCore_of_barAut_eq_one hp hp2 hcomp hbl hxI hxN hx1
  exact Subgroup.mem_map.2 ⟨⟨x, hxI⟩, h, rfl⟩

end Helpers

@[expose] def Lemma133_compStatement : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T : Subgroup G} (h : Sec13 G m p B M E A D T)
    {L : Subgroup G}, GLAPComponent p (Istar p M D) L → GLAPComponent p M L

section ConjPartI

variable {G : Type} [Group G] [Finite G]

theorem conj_part_i {m p : ℕ} {B M E A D T R : Subgroup G} (hI71 : Input7_1Inn)
    (hL133 : Lemma133Statement) (hcomp : Lemma133_compStatement) (h : Sec13 G m p B M E A D T)
    (hRM : IsSylowIn p M R)
    {I : Subgroup G} (hIstar : I = Istar p M D) (hIc : GLAPComponent p (Istar p M D) I)
    (hPiBar : IsPiTypeGroup p (barOf p I)) (hrk : CFSG.Open.pRank p I = 1) :
    R = (R ⊓ I) ⊔ centBar p R I ∧ (R ⊓ I) ⊓ centBar p R I = ⊥ ∧ CFSG.Open.pRank p (R ⊓ I) = 1 := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hbl : IsGLBlock M I := ((hL133 h).2 I hIc).1.1
  have hIM : I ≤ M := hbl.le
  have hsn : IsSubnormal I M := hbl.subnormal
  have hcompM : GLAPComponent p M I := hcomp h hIc
  have hMN : M ≤ Subgroup.normalizer (I : Set G) := le_normalizer_of_istar_eq hIstar
  have hZ : Subgroup.center (↥I ⧸ GLAPPrimeCore p ↥I) = ⊥ :=
    center_quotient_eq_bot_of_block hp hp2 hcompM hbl
  have hPi : IsPiTypeGroup p ↥(barX p M I) :=
    IsPiTypeGroup.of_mulEquiv' (quotEquivBarX hp hIM hsn) hPiBar
  obtain ⟨hRM', hRp, hRmax⟩ := hRM
  have hRN : R ≤ Subgroup.normalizer (I : Set G) := hRM'.trans hMN
  set K : Subgroup G := blkKer p M I with hKdef
  have hKN : K ≤ Subgroup.normalizer (I : Set G) := fun k hk => hMN (mem_blkKer_iff.1 hk).1
  have hKM : K ≤ M := inf_le_right
  set X : Subgroup G := I ⊔ K with hXdef
  have hXM : X ≤ M := sup_le hIM hKM
  have hIX : I ≤ X := le_sup_left
  have hKX : K ≤ X := le_sup_right
  have hXN : X ≤ Subgroup.normalizer (I : Set G) := sup_le Subgroup.le_normalizer hKN
  have hRX : R ≤ X := by
    intro x hx
    obtain ⟨l, hl, hbar⟩ := block_inner hp hp2 hRp hRN hIM hsn hPi hI71 hZ x hx
    have hlN : l ∈ Subgroup.normalizer (I : Set G) := hMN (hIM hl)
    have hxN : x ∈ Subgroup.normalizer (I : Set G) := hRN hx
    have hkN : l⁻¹ * x ∈ Subgroup.normalizer (I : Set G) :=
      (Subgroup.normalizer (I : Set G)).mul_mem ((Subgroup.normalizer (I : Set G)).inv_mem hlN) hxN
    have hk : l⁻¹ * x ∈ K := by
      refine mem_blkKer_iff.2 ⟨M.mul_mem (M.inv_mem (hIM hl)) (hRM' hx), hkN, ?_⟩
      have e : (⟨l⁻¹ * x, hkN⟩ : ↥(Subgroup.normalizer (I : Set G))) =
          (⟨l, hlN⟩)⁻¹ * ⟨x, hxN⟩ := Subtype.ext (by simp)
      rw [e, map_mul, map_inv]
      have hbar' : barAut p I ⟨x, hxN⟩ = barAut p I ⟨l, hlN⟩ := hbar
      rw [hbar']
      simp
    have hx' : x = l * (l⁻¹ * x) := by group
    show x ∈ I ⊔ K
    rw [hx']
    exact Subgroup.mul_mem_sup hl hk
  have hRsub : IsPGroup p ↥(R.subgroupOf X) := hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRX).symm
  let SX : Sylow p ↥X :=
    { toSubgroup := R.subgroupOf X
      isPGroup' := hRsub
      is_maximal' := by
        intro Q hQ hle
        have hQM : Q.map X.subtype ≤ M := by
          rintro _ ⟨y, -, rfl⟩
          exact hXM y.2
        have hQp : IsPGroup p ↥(Q.map X.subtype) :=
          hQ.of_equiv (Subgroup.equivMapOfInjective Q X.subtype Subtype.val_injective)
        have hRQ : R ≤ Q.map X.subtype := by
          intro x hx
          exact Subgroup.mem_map.2 ⟨⟨x, hRX hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have hEq : Q.map X.subtype = R := hRmax _ hQM hQp hRQ
        exact Subgroup.map_subtype_inj.1 (hEq.trans (Subgroup.map_subgroupOf_eq_of_le hRX).symm) }
  let L : Subgroup ↥X := I.subgroupOf X
  let C : Subgroup ↥X := K.subgroupOf X
  have hLC_top : L ⊔ C = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have hy : (y : G) ∈ (I : Set G) * (K : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left I K hKN]
      exact y.2
    obtain ⟨l, hl, k, hk, hlk⟩ := hy
    have hy' : y = (⟨l, hIX hl⟩ : ↥X) * ⟨k, hKX hk⟩ := Subtype.ext hlk.symm
    rw [hy']
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.2 hl) (Subgroup.mem_subgroupOf.2 hk)
  have hN0 : ¬ p ∣ Nat.card ↥(L ⊓ C) := by
    have hGI : GLAPPrimeCoreOf p I ≤ X := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
      exact hIX y.2
    have hle : L ⊓ C ≤ (GLAPPrimeCoreOf p I).subgroupOf X := by
      intro y hy
      obtain ⟨hyL, hyC⟩ := Subgroup.mem_inf.1 hy
      have hyI : (y : G) ∈ I := Subgroup.mem_subgroupOf.1 hyL
      have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.1 hyC
      exact Subgroup.mem_subgroupOf.2 (blkKer_inf_le hp hp2 hcompM hbl (Subgroup.mem_inf.2 ⟨hyI, hyK⟩))
    have hdvd := Subgroup.card_dvd_of_le hle
    have hcard : Nat.card ↥((GLAPPrimeCoreOf p I).subgroupOf X) = Nat.card ↥(GLAPPrimeCoreOf p I) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hGI).toEquiv
    intro hpd
    exact not_dvd_card_glaPPrimeCoreOf hp I (hcard ▸ (hpd.trans hdvd))
  have hcomm : ∀ l ∈ L, ∀ c ∈ C, c * l * c⁻¹ * l⁻¹ ∈ L ⊓ C := by
    intro l hl c hc
    have hlI : (l : G) ∈ I := Subgroup.mem_subgroupOf.1 hl
    have hcK : (c : G) ∈ K := Subgroup.mem_subgroupOf.1 hc
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 ?_, Subgroup.mem_subgroupOf.2 ?_⟩
    · have h1 : (c : G) * (l : G) * (c : G)⁻¹ ∈ I :=
        (Subgroup.mem_normalizer_iff.1 (hKN hcK) (l : G)).1 hlI
      have e : (c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹ =
          ((c : G) * (l : G) * (c : G)⁻¹) * (l : G)⁻¹ := rfl
      show (c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹ ∈ I
      rw [e]
      exact I.mul_mem h1 (I.inv_mem hlI)
    · have h2 : (l : G) * (c : G)⁻¹ * (l : G)⁻¹ ∈ K :=
        blkKer_conj_mem hMN (hIM hlI) (K.inv_mem hcK)
      show (c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹ ∈ K
      have e : (c : G) * (l : G) * (c : G)⁻¹ * (l : G)⁻¹ =
          (c : G) * ((l : G) * (c : G)⁻¹ * (l : G)⁻¹) := by group
      rw [e]
      exact K.mul_mem hcK h2
  have hCN : C ≤ Subgroup.normalizer (L : Set ↥X) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hcK : (c : G) ∈ K := Subgroup.mem_subgroupOf.1 hc
    show (h : G) ∈ I ↔ (c : G) * (h : G) * (c : G)⁻¹ ∈ I
    exact Subgroup.mem_normalizer_iff.1 (hKN hcK) (h : G)
  have hLN : L ≤ Subgroup.normalizer (C : Set ↥X) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hlM : (l : G) ∈ M := hIM (Subgroup.mem_subgroupOf.1 hl)
    show (k : G) ∈ K ↔ (l : G) * (k : G) * (l : G)⁻¹ ∈ K
    constructor
    · intro hk
      exact blkKer_conj_mem hMN hlM hk
    · intro hk
      have h3 := blkKer_conj_mem hMN (M.inv_mem hlM) hk
      have e : (l : G)⁻¹ * ((l : G) * (k : G) * (l : G)⁻¹) * (l : G)⁻¹⁻¹ = (k : G) := by group
      rw [e] at h3
      exact h3
  have hsplit := sylow_split hp hCN hLN hLC_top hN0 hcomm SX
  have hdec : R = (R ⊓ I) ⊔ (R ⊓ K) := by
    have h1 := congrArg (Subgroup.map X.subtype) hsplit
    rw [Subgroup.map_sup] at h1
    have e0 : (SX.toSubgroup).map X.subtype = R := Subgroup.map_subgroupOf_eq_of_le hRX
    have e1 : (SX.toSubgroup ⊓ L).map X.subtype = R ⊓ I := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨h1', h2'⟩ := Subgroup.mem_inf.1 hy
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h1', Subgroup.mem_subgroupOf.1 h2'⟩
      · intro hg
        obtain ⟨hgR, hgI⟩ := Subgroup.mem_inf.1 hg
        exact ⟨⟨g, hRX hgR⟩,
          Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hgR, Subgroup.mem_subgroupOf.2 hgI⟩, rfl⟩
    have e2 : (SX.toSubgroup ⊓ C).map X.subtype = R ⊓ K := by
      ext g
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨h1', h2'⟩ := Subgroup.mem_inf.1 hy
        exact Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h1', Subgroup.mem_subgroupOf.1 h2'⟩
      · intro hg
        obtain ⟨hgR, hgK⟩ := Subgroup.mem_inf.1 hg
        exact ⟨⟨g, hKX hgK⟩,
          Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.2 hgR, Subgroup.mem_subgroupOf.2 hgK⟩, rfl⟩
    rw [e0, e1, e2] at h1
    exact h1
  have hbot : R ⊓ GLAPPrimeCoreOf p I = ⊥ :=
    isPGroup_inf_eq_bot_of_not_dvd hp hRp (not_dvd_card_glaPPrimeCoreOf hp I)
  have hc1 : R = (R ⊓ I) ⊔ centBar p R I := by
    rw [centBar_eq_blkKer_inf hRM']
    rw [inf_comm R K] at hdec
    exact hdec
  have hc2 : (R ⊓ I) ⊓ centBar p R I = ⊥ := by
    rw [centBar_eq_blkKer_inf hRM', eq_bot_iff]
    intro x hx
    obtain ⟨hxRI, hxKR⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hxR, hxI⟩ := Subgroup.mem_inf.1 hxRI
    obtain ⟨hxK, -⟩ := Subgroup.mem_inf.1 hxKR
    have hxG : x ∈ GLAPPrimeCoreOf p I :=
      blkKer_inf_le hp hp2 hcompM hbl (Subgroup.mem_inf.2 ⟨hxI, hxK⟩)
    have h0 : x ∈ R ⊓ GLAPPrimeCoreOf p I := Subgroup.mem_inf.2 ⟨hxR, hxG⟩
    have h1 : x ∈ (⊥ : Subgroup G) := hbot ▸ h0
    exact h1
  refine ⟨hc1, hc2, ?_⟩
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_mono hp1 (inf_le_right : R ⊓ I ≤ I)
    rw [hrk] at h
    exact h
  ·
    have hpI : p ∣ Nat.card ↥I := by
      obtain ⟨E, hEI, -, hEc⟩ := CFSG.SectionRank.exists_pRank hp1 I
      rw [hrk, pow_one] at hEc
      exact hEc ▸ Subgroup.card_dvd_of_le hEI
    have hLnorm : L.Normal := by
      constructor
      intro n hn g
      have hgN : (g : G) ∈ Subgroup.normalizer (I : Set G) := hXN g.2
      have hn' : (n : G) ∈ I := Subgroup.mem_subgroupOf.1 hn
      show (g : G) * (n : G) * (g : G)⁻¹ ∈ I
      exact (Subgroup.mem_normalizer_iff.1 hgN (n : G)).1 hn'
    have hLcard : Nat.card ↥L = Nat.card ↥I :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIX).toEquiv
    obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal SX (N := L)
    have hPne : (P : Subgroup ↥L) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P (hLcard ▸ hpI)
    rw [hP] at hPne
    have hne : SX.toSubgroup ⊓ L ≠ ⊥ := by
      intro h0
      apply hPne
      rw [h0, Subgroup.bot_subgroupOf]
    obtain ⟨y, hy, hy1⟩ : ∃ y ∈ SX.toSubgroup ⊓ L, y ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hne (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hc y hy))
    obtain ⟨hyR', hyL'⟩ := Subgroup.mem_inf.1 hy
    have hyR : (y : G) ∈ R := Subgroup.mem_subgroupOf.1 hyR'
    have hyI : (y : G) ∈ I := Subgroup.mem_subgroupOf.1 hyL'
    have hyne : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hQp : IsPGroup p ↥(R ⊓ I) := hRp.to_inf_left
    have hyQ : (y : G) ∈ R ⊓ I := Subgroup.mem_inf.2 ⟨hyR, hyI⟩
    have hdvdQ : p ∣ Nat.card ↥(R ⊓ I) :=
      (hQp.dvd_orderOf (g := (⟨(y : G), hyQ⟩ : ↥(R ⊓ I))) (fun h => hyne (congrArg Subtype.val h))).trans
        (orderOf_dvd_natCard _)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvdQ
    have hzG : (z : G) ∈ R ⊓ I := z.2
    have hzp : (z : G) ^ p = 1 := by
      have hz' : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe]; exact hz
      rw [← hz']
      exact pow_orderOf_eq_one _
    have hEH : Subgroup.zpowers (z : G) ≤ R ⊓ I := Subgroup.zpowers_le.2 hzG
    have hE : CFSG.Open.IsElemAbelian p (Subgroup.zpowers (z : G)) := by
      apply isElemAbelian_of_comm_pow
      · intro x hx y hy'
        obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
        exact (Commute.zpow_zpow_self (z : G) a b).eq
      · intro x hx
        obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzp, one_zpow]
    have hcardE : Nat.card ↥(Subgroup.zpowers (z : G)) = p ^ 1 := by
      rw [pow_one, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
    have h1 := CFSG.SectionRank.le_pRank hp1 hEH hE hcardE
    exact h1

end ConjPartI

section Lemma1314i

variable {G : Type} [Group G] [Finite G]

theorem lemma1314_i_of_inputs {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (hI71 : Input7_1Inn) (hL133 : Lemma133Statement) (hcomp : Lemma133_compStatement)
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    (hPiI : IsPiTypeGroup p (barOf p (Iof p M D))) :
    R = (R ⊓ Iof p M D) ⊔ centBar p R (Iof p M D) ∧ (R ⊓ Iof p M D) ⊓ centBar p R (Iof p M D) = ⊥ ∧
      CFSG.Open.pRank p (R ⊓ Iof p M D) = 1 := by
  obtain ⟨-, hIstar, L, hLc, hIL, hrk, -⟩ := h139a
  rw [← hIL] at hLc hrk
  have hIc : GLAPComponent p (Istar p M D) (Iof p M D) := by
    rw [← hIstar]
    exact hLc
  exact conj_part_i hI71 hL133 hcomp h.toSec13 h.hR.1 hIstar hIc hPiI hrk

end Lemma1314i

section Lemma1312

variable {G : Type} [Group G] [Finite G]

theorem le_L1of {p : ℕ} {M D L0 : Subgroup G} : L0 ≤ L1of p M D L0 := by
  refine le_iSup₂_of_le (1 : G) (Istar p M D).one_mem ?_
  exact le_of_eq (gLBConj_eq_of_mem_normalizer (one_mem _)).symm

theorem piLayer_le_self (p : ℕ) (H : Subgroup G) : piLayer p H ≤ H := by
  unfold piLayer
  exact iSup₂_le fun L hL => hL.1.1

theorem le_centralizer_of_piComp {p : ℕ} {M D L0 : Subgroup G} {d : G}
    (hL0 : GLAPComponent p (piLayer p (Istar p M D ⊓ Cg d)) L0) : L0 ≤ Cg d :=
  hL0.1.trans ((piLayer_le_self p _).trans inf_le_right)

abbrev L2of (p : ℕ) (M D L0 : Subgroup G) : Subgroup G := ⨆ g ∈ M, GLBConj g (L1of p M D L0)

theorem L1_le_L2 {p : ℕ} {M D L0 : Subgroup G} : L1of p M D L0 ≤ L2of p M D L0 := by
  refine le_iSup₂_of_le (1 : G) (M.one_mem) ?_
  exact le_of_eq (gLBConj_eq_of_mem_normalizer (one_mem _)).symm

theorem normal_L2of {p : ℕ} {M D L0 : Subgroup G} :
    ∀ g ∈ M, ∀ x ∈ L2of p M D L0, g * x * g⁻¹ ∈ L2of p M D L0 := by
  intro g hg x hx
  have h1 : g * x * g⁻¹ ∈ GLBConj g⁻¹ (L2of p M D L0) := by
    apply mem_gLBConj.2
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  exact conj_iSup_mem_le (M.inv_mem hg) h1

theorem centralizer_L2of_normal {p : ℕ} {M D L0 : Subgroup G} :
    ∀ g ∈ M, ∀ c ∈ Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M,
      g * c * g⁻¹ ∈ Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M := by
  intro g hg c hc
  obtain ⟨hcC, hcM⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨?_, M.mul_mem (M.mul_mem hg hcM) (M.inv_mem hg)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ L2of p M D L0 := normal_L2of g⁻¹ (M.inv_mem hg) x hx
  have key := Subgroup.mem_centralizer_iff.1 hcC (g⁻¹ * x * g⁻¹⁻¹) hy
  have e1 : x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * c) * g⁻¹ := by group
  have e2 : (g * c * g⁻¹) * x = g * (c * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by group
  rw [e1, e2, key]

theorem inf_ne_bot_of_sylow_normal {p : ℕ} [Fact p.Prime] {M R N : Subgroup G}
    (hRM : IsSylowIn p M R) (hNM : N ≤ M) (hNn : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hdvd : p ∣ Nat.card ↥N) : R ⊓ N ≠ ⊥ := by
  obtain ⟨hRM', hRp, hRmax⟩ := hRM
  have hRsub : IsPGroup p ↥(R.subgroupOf M) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRM').symm
  let SM : Sylow p ↥M :=
    { toSubgroup := R.subgroupOf M
      isPGroup' := hRsub
      is_maximal' := by
        intro Q hQ hle
        have hQM : Q.map M.subtype ≤ M := by
          rintro _ ⟨y, -, rfl⟩
          exact y.2
        have hQp : IsPGroup p ↥(Q.map M.subtype) :=
          hQ.of_equiv (Subgroup.equivMapOfInjective Q M.subtype Subtype.val_injective)
        have hRQ : R ≤ Q.map M.subtype := by
          intro x hx
          exact Subgroup.mem_map.2 ⟨⟨x, hRM' hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        have hEq : Q.map M.subtype = R := hRmax _ hQM hQp hRQ
        exact Subgroup.map_subtype_inj.1 (hEq.trans (Subgroup.map_subgroupOf_eq_of_le hRM').symm) }
  haveI : (N.subgroupOf M).Normal := by
    constructor
    intro n hn g
    have := hNn (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.1 hn)
    exact this
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal SM (N := N.subgroupOf M)
  have hPne : (P : Subgroup ↥(N.subgroupOf M)) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card P (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
      exact hdvd)
  rw [hP] at hPne
  intro h0
  apply hPne
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hy
  have hyRN : (y : G) ∈ R ⊓ N :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h1, Subgroup.mem_subgroupOf.1 h2⟩
  rw [h0, Subgroup.mem_bot] at hyRN
  exact Subgroup.mem_bot.2 (Subtype.ext (Subtype.ext hyRN))


theorem caseA_central {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d)
    (hnot : ¬ (Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M) ≤ GLAPPrimeCoreOf p M) :
    ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ (Prop139a p M D → c ∈ centerOf R) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G,
      C = Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M := ⟨_, rfl⟩
  rw [← hCdef] at hnot
  have hCM : C ≤ M := by rw [hCdef]; exact inf_le_right
  have hCn : ∀ g ∈ M, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    rw [hCdef] at hc ⊢
    exact centralizer_L2of_normal g hg c hc
  have hCcent : ∀ g ∈ C, ∀ x ∈ L2of p M D L0, x * g = g * x := by
    intro g hg x hx
    rw [hCdef] at hg
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).1 x hx
  have hCL1 : ∀ g ∈ C, ∀ n ∈ L1of p M D L0, g * n * g⁻¹ = n := by
    intro g hg n hn
    have := hCcent g hg n (L1_le_L2 hn)
    rw [← this]
    group
  have hRM := h.hR.1
  have hRp : IsPGroup p ↥R := hRM.2.1
  have hRM' : R ≤ M := hRM.1
  have hpC : p ∣ Nat.card ↥C := by
    by_contra hpC
    apply hnot
    have hnorm : (C.subgroupOf M).Normal := by
      constructor
      intro n hn g
      exact hCn (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.1 hn)
    have hcop : Nat.Coprime p (Nat.card (C.subgroupOf M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpC
    have hle := le_pPrimeCore_of_normal_coprime hnorm hcop
    intro x hx
    have hxM : x ∈ M := hCM hx
    exact Subgroup.mem_map.2 ⟨⟨x, hxM⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hRC : R ⊓ C ≠ ⊥ :=
    inf_ne_bot_of_sylow_normal hRM hCM (fun g hg n hn => hCn g hg n hn) hpC
  haveI : Group.IsNilpotent ↥R := hRp.isNilpotent
  have hHn : ((R ⊓ C).subgroupOf R).Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ R ⊓ C := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨hnR, hnC⟩ := Subgroup.mem_inf.1 hn'
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact R.mul_mem (R.mul_mem g.2 hnR) (R.inv_mem g.2)
    · exact hCn (g : G) (hRM' g.2) (n : G) hnC
  have hHne : (R ⊓ C).subgroupOf R ≠ ⊥ := by
    intro h0
    apply hRC
    rw [eq_bot_iff]
    intro y hy
    have hyH : (⟨y, (Subgroup.mem_inf.1 hy).1⟩ : ↥R) ∈ (R ⊓ C).subgroupOf R :=
      Subgroup.mem_subgroupOf.2 hy
    rw [h0, Subgroup.mem_bot] at hyH
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hyH
  obtain ⟨w, hwH, hw1⟩ : ∃ w ∈ ((R ⊓ C).subgroupOf R ⊓ Subgroup.center ↥R), w ≠ 1 := by
    by_contra hc
    push_neg at hc
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
      (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hc y hy))
  obtain ⟨hwH', hwZ⟩ := Subgroup.mem_inf.1 hwH
  have hzRC : (w : G) ∈ R ⊓ C := Subgroup.mem_subgroupOf.1 hwH'
  have hzR : (w : G) ∈ R := (Subgroup.mem_inf.1 hzRC).1
  have hzcent : ∀ g ∈ R, g * (w : G) = (w : G) * g := by
    intro g hg
    have := Subgroup.mem_center_iff.1 hwZ ⟨g, hg⟩
    exact congrArg Subtype.val this
  have hz1 : (w : G) ≠ 1 := fun h' => hw1 (Subtype.ext h')
  obtain ⟨k0, hk0⟩ : ∃ k : ℕ, (w : G) ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hRp w
    exact ⟨k, congrArg Subtype.val hk⟩
  have hdvdz : p ∣ orderOf (w : G) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk0)
    have hj0 : j ≠ 0 := by
      intro hj0
      rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
      exact hz1 hj
    rw [hj]
    exact dvd_pow_self p hj0
  obtain ⟨c0, hc0⟩ := exists_prime_orderOf_dvd_card' p (by
    rw [Nat.card_zpowers]; exact hdvdz : p ∣ Nat.card ↥(Subgroup.zpowers (w : G)))
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (c0 : G) := ⟨_, rfl⟩
  have hcorder : orderOf c = p := by
    rw [hcdef, Subgroup.orderOf_coe]
    exact hc0
  have hcz : c ∈ Subgroup.zpowers (w : G) := by
    rw [hcdef]
    exact c0.2
  have hcR : c ∈ R := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hcz
    rw [← ha]
    exact R.zpow_mem hzR a
  have hwC : (w : G) ∈ C := (Subgroup.mem_inf.1 hzRC).2
  have hcC : c ∈ C := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hcz
    rw [← ha]
    exact C.zpow_mem hwC a
  have hcR : c ∈ R := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hcz
    rw [← ha]
    exact R.zpow_mem hzR a
  have hccent : ∀ g ∈ R, g * c = c * g := by
    intro g hg
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hcz
    rw [← ha]
    exact Commute.zpow_right (hzcent g hg : Commute g (w : G)) a
  have hcp : c ^ p = 1 := by
    rw [← hcorder]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hcorder
    exact hp.one_lt.ne hcorder
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hBR : B ≤ R := (le_sup_right : B ≤ A ⊔ B).trans h.hR.2
  have hcB : ∀ b ∈ B, b * c = c * b := fun b hb => hccent b (hBR hb)
  have hcomm_zc : ∀ g ∈ Subgroup.zpowers c, ∀ b ∈ B, g * b = b * g := by
    intro g hg b hb
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← ha]
    exact Commute.zpow_left (hcB b hb).symm a
  have hEwN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have e : g * b * g⁻¹ = b := by rw [hcomm_zc g hg b hb, mul_inv_cancel_right]
      rw [e]
      exact hb
    · intro hx
      have hgx : g⁻¹ * (g * b * g⁻¹) = (g * b * g⁻¹) * g⁻¹ :=
        hcomm_zc g⁻¹ (Subgroup.inv_mem _ hg) _ hx
      have e2 : g * b * g⁻¹ * g⁻¹ * g = g * b * g⁻¹ := by group
      have hb' : g⁻¹ * (g * b * g⁻¹) * g ∈ B := by
        rw [hgx, e2]
        exact hx
      have key : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rwa [key] at hb'
  obtain ⟨Ew, hEwdef⟩ : ∃ E : Subgroup G, E = B ⊔ Subgroup.zpowers c := ⟨_, rfl⟩
  have hEwprod : (Ew : Set G) = (B : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [hEwdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers c) hEwN
  have hEwcomm : ∀ x ∈ Ew, ∀ y ∈ Ew, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hx
    have hy' : y ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hy
    obtain ⟨b, hb, u, hu, rfl⟩ := hx'
    obtain ⟨b', hb', u', hu', rfl⟩ := hy'
    have hcb : Commute b b' := elemAbelian_comm hBel hb hb'
    have hub' : Commute u b' := hcomm_zc u hu b' hb'
    have hbu' : Commute b u' := (hcomm_zc u' hu' b hb).symm
    have huu' : Commute u u' := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨a', rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
      exact Commute.zpow_zpow_self c a a'
    have hcomm' : Commute (b * u) (b' * u') :=
      Commute.mul_right (Commute.mul_left hcb hub') (Commute.mul_left hbu' huu')
    exact hcomm'.eq
  have hEwpow : ∀ x ∈ Ew, x ^ p = 1 := by
    intro x hx
    have hx' : x ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hx
    obtain ⟨b, hb, u, hu, rfl⟩ := hx'
    have hbu : Commute b u := (hcomm_zc u hu b hb).symm
    rw [hbu.mul_pow p, hBel.2 b hb, one_mul]
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  have hEel : IsElemAbelian p Ew := isElemAbelian_of_comm_pow hEwcomm hEwpow
  have hsc := lemma23_proved G m p hS B h.bOne
  have hEqB : Ew = B := hsc.2.2 Ew le_top hEel (by rw [hEwdef]; exact le_sup_left)
  have hcB' : c ∈ B := by
    have hcEw : c ∈ Ew := by
      rw [hEwdef]
      exact (le_sup_right : Subgroup.zpowers c ≤ B ⊔ Subgroup.zpowers c) (Subgroup.mem_zpowers c)
    rw [hEqB] at hcEw
    exact hcEw
  have hcN : c ∈ Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hCL1 c hcC n hn]
      exact hn
    · intro hn
      have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
      have h2 := hCL1 c⁻¹ (C.inv_mem hcC) _ hn
      rw [e] at h2
      rw [h2]
      exact hn
  have hbar : barAut p (L1of p M D L0) ⟨c, hcN⟩ = 1 := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      show c * (x : G) * c⁻¹ = (x : G)
      exact hCL1 c hcC x x.2
  have hcmem : c ∈ centBar p B (L1of p M D L0) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨c, hcN⟩, MonoidHom.mem_ker.2 hbar, rfl⟩, hcB'⟩
  have hAR : A ≤ R := (le_sup_left : A ≤ A ⊔ B).trans h.hR.2
  have hdR : d ∈ R := hAR (h.hD.1 h.hd.1)
  have hcCg : c ∈ Cg d := Subgroup.mem_centralizer_iff.2 (fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact hccent d hdR)
  have hcZ : c ∈ centerOf R := by
    refine Subgroup.mem_map.2 ⟨⟨c, hcR⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_), rfl⟩
    exact hccent g.1 g.2
  exact ⟨c, Subgroup.mem_inf.2 ⟨hcmem, hcCg⟩, hc1, fun _ => hcZ⟩

theorem lemma1312_of_inputs {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d)
    (hint : (B ⊓ L1of p M D L0) ⊓ centBar p B (L1of p M D L0) = ⊥)
    (hx : ∃ x ∈ B ⊓ L0, x ≠ 1 ∧ (Prop139a p M D → x ∈ centerOf R))
    (hcB : Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M ≤ GLAPPrimeCoreOf p M →
      ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ (Prop139a p M D → c ∈ centerOf R)) :
    ∃ U : Subgroup G, IsU1312 p B M D L0 d U ∧ (Prop139a p M D → U ≤ centerOf R) := by
  have hc : ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ (Prop139a p M D → c ∈ centerOf R) := by
    by_cases hle : Subgroup.centralizer ((L2of p M D L0 : Subgroup G) : Set G) ⊓ M ≤ GLAPPrimeCoreOf p M
    · exact hcB hle
    · exact caseA_central h hle
  obtain ⟨x, hxBL, hx1, hxZ⟩ := hx
  obtain ⟨c, hcC, hc1, hcZ⟩ := hc
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := h.bOne.1.1
  have hxB : x ∈ B := (Subgroup.mem_inf.1 hxBL).1
  have hxL0 : x ∈ L0 := (Subgroup.mem_inf.1 hxBL).2
  have hcC' : c ∈ centBar p B (L1of p M D L0) := (Subgroup.mem_inf.1 hcC).1
  have hcCg : c ∈ Cg d := (Subgroup.mem_inf.1 hcC).2
  have hcB : c ∈ B := (Subgroup.mem_inf.1 hcC').2
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hcp : c ^ p = 1 := hBel.2 c hcB
  have hcomm : x * c = c * x := elemAbelian_comm hBel hxB hcB
  have hcnot : c ∉ Subgroup.zpowers x := by
    intro hcz
    have hcL0 : c ∈ L0 := (Subgroup.zpowers_le.2 hxL0) hcz
    have hmem : c ∈ (B ⊓ L1of p M D L0) ⊓ centBar p B (L1of p M D L0) :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcB, le_L1of hcL0⟩, hcC'⟩
    rw [hint, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  set U : Subgroup G := Subgroup.closure ({x, c} : Set G) with hUdef
  have hxU : x ∈ U := Subgroup.subset_closure (by simp)
  have hcU : c ∈ U := Subgroup.subset_closure (by simp)
  have hUB : U ≤ B := (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxB, Set.singleton_subset_iff.2 hcB⟩)
  have hUel : IsElemAbelian p U :=
    isElemAbelian_of_comm_pow (fun a ha b hb => elemAbelian_comm hBel (hUB ha) (hUB hb))
      (fun a ha => hBel.2 a (hUB ha))
  have hUcard : Nat.card U = p ^ 2 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.card_closure_pair_eq_sq
      hxp hcp hcomm hx1 hcnot
  have hUCg : U ≤ Cg d :=
    (Subgroup.closure_le _).2 (Set.insert_subset_iff.2
      ⟨le_centralizer_of_piComp h.hL0 hxL0, Set.singleton_subset_iff.2 hcCg⟩)
  have hUL0 : U ⊓ L0 ≠ ⊥ := by
    intro h0
    have hmem : x ∈ U ⊓ L0 := Subgroup.mem_inf.2 ⟨hxU, hxL0⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hUcb : centBar p U (L1of p M D L0) ≠ ⊥ := by
    intro h0
    have hmem : c ∈ centBar p U (L1of p M D L0) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hcC').1, hcU⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact hc1 hmem
  refine ⟨U, ⟨⟨hUB, hUel, hUcard⟩, hUCg, hUL0, hUcb⟩, fun hP => ?_⟩
  exact (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hxZ hP, Set.singleton_subset_iff.2 (hcZ hP)⟩)

end Lemma1312

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec13g

end
