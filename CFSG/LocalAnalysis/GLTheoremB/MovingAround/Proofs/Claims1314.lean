module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs71
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem mem_of_mem_centBar {p : ℕ} {U L : Subgroup G} {b : G} (hb : b ∈ centBar p U L) : b ∈ U :=
  (Subgroup.mem_inf.1 hb).2

theorem b_mem_normalizer_LOf {p : ℕ} {L0 : Subgroup G} {d b : G} (hbd : b ∈ Cg d) :
    b ∈ Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G) :=
  Lemma1314c.mem_normalizer_LOf hbd Lemma1314c.mem_normalizer_L0bOf_self

theorem fixSub_eq_fixedSub {K : Type} [Group K] (x : MulAut K) :
    Lemma1314.fixSub x = CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub x :=
  Subgroup.ext fun _ => Iff.rfl

end Basic

section Pumpup

variable {G : Type} [Group G] [Finite G]

theorem kHatBlock_of_lemma1313 (hL1313 : Lemma1313Statement) : Lemma1314.KHatBlock := by
  intro G _ _ m p B M E A D T R L0 d h U hU b hb hb1
  have hp : p.Prime := h.standing.prime
  obtain ⟨-, ⟨hLc, -, -⟩, -, -⟩ := hL1313 h hU hb hb1
  have hC : CFSG.Open.IsKGroup ↥(Cg d) :=
    Prop1310a5b.isKGroup_centralizer_of_standing h.standing h.hd.2
  exact CFSG.LocalAnalysis.GLTheoremA.IsKHat.of_mulEquiv (quotEquivBarX hp hLc.1 hLc.2.1).symm
    (isKHat_of_component (isKGroup_barX_quotient hC) hLc.2.2.1)

theorem barAut_ne_one_of_lemma1313 (hL1313 : Lemma1313Statement) {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0))
    (hb1 : b ≠ 1) (hbN : b ∈ Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G)) :
    barAut p (Lemma1314.LOf p L0 d b) ⟨b, hbN⟩ ≠ 1 := by
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, ⟨hLc, hL0bc, -⟩, -, hLpi⟩ := hL1313 h hU hb hb1
  set L : Subgroup G := Lemma1314.LOf p L0 d b with hLdef
  set L0b : Subgroup G := Lemma1314.L0bOf p L0 b with hL0bdef
  have hbp : b ^ p = 1 := hU.1.2.1.2 b (mem_of_mem_centBar hb)
  intro h1
  set Y : Subgroup G := L ⊓ Cg b with hY
  have hYL : Y ≤ L := inf_le_left
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp hbp hbN
  have htop : barX p L Y = ⊤ := by
    rw [← hfix, h1]
    ext y
    simp [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.fixedSub]
  have hcov : ∀ x ∈ L, ∃ y ∈ Y, ∃ n ∈ GLAPPrimeCoreOf p L, x = y * n := by
    intro x hx
    obtain ⟨k, hk, hkn⟩ :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff p hYL).1 htop x hx
    exact ⟨k, hk, k⁻¹ * x, hkn, by group⟩
  have hq : CFSG.Open.IsQuasisimple (barOf p L) := Lemma1313.isQuasisimple_barOf_of_pComp hLc
  obtain ⟨eY⟩ := Prop1310a5b.barOf_equiv_of_cover hYL hcov hq
  have hYq : CFSG.Open.IsQuasisimple (barOf p Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eY.symm hq
  have hbarTop : barX p Y L0b = ⊤ := Lemma1313.eq_top_of_isComponentOf_quasisimple hYq hL0bc.2.2.1
  have e1 : barOf p L0b ≃* ↥(barX p Y L0b) := quotEquivBarX hp hL0bc.1 hL0bc.2.1
  have e2 : ↥(barX p Y L0b) ≃* barOf p Y := (MulEquiv.subgroupCongr hbarTop).trans Subgroup.topEquiv
  obtain ⟨e0⟩ := Lemma1313.barOf_L0b_iso h hU hb hb1
  have hPi0 := Lemma1313.isPiGroup_barOf_L0 h
  have hPi : IsPiGroup p (barOf p L) :=
    IsPiGroup.of_mulEquiv (e0.symm.trans (e1.trans (e2.trans eY))) hPi0
  exact hLpi (Lemma1313.le_piOf_of_comp' hLc hPi)

theorem pumpupBlock_of_lemma1313 (hL1313 : Lemma1313Statement) : Lemma1314.PumpupBlock := by
  intro G _ _ m p B M E A D T R L0 d h U hU b hb hb1
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hbd : b ∈ Cg d := hU.2.1 (mem_of_mem_centBar hb)
  have hbN := b_mem_normalizer_LOf (p := p) (L0 := L0) hbd
  have hbp : b ^ p = 1 := hU.1.2.1.2 b (mem_of_mem_centBar hb)
  have hx1 := barAut_ne_one_of_lemma1313 hL1313 h hU hb hb1 hbN
  obtain ⟨-, ⟨-, hL0bc, -⟩, -, -⟩ := hL1313 h hU hb hb1
  have hL0bL : Lemma1314.L0bOf p L0 b ≤ Lemma1314.LOf p L0 d b := hL0bc.1.trans inf_le_left
  have hxp : (barAut p (Lemma1314.LOf p L0 d b) ⟨b, hbN⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (Lemma1314.LOf p L0 d b : Set G))) ^ p = 1 :=
      Subtype.ext hbp
    rw [this, map_one]
  refine ⟨barAut p (Lemma1314.LOf p L0 d b) ⟨b, hbN⟩, orderOf_eq_prime hxp hx1,
    barX p (Lemma1314.LOf p L0 d b) (Lemma1314.L0bOf p L0 b), ?_, ⟨(Prop115.barOfIso hL0bL).symm⟩⟩
  rw [fixSub_eq_fixedSub, AltFacts3.fixedSub_barAut_eq_p hp hbp hbN]
  exact Prop115b.barX_glaPComponent_of_le hp inf_le_left hL0bc

end Pumpup

section ChevOpM

variable {G : Type} [Group G] [Finite G]

theorem ddKey_le_of_le {p : ℕ} {E A E' A' : Subgroup G}
    (h1 : CFSG.Open.pRank p (E ⊓ A) ≤ CFSG.Open.pRank p (E' ⊓ A'))
    (h2 : min (CFSG.Open.pRank p E) (CFSG.Open.pRank p A) ≤
      min (CFSG.Open.pRank p E') (CFSG.Open.pRank p A'))
    (h3 : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p E')
    (h4 : CFSG.Open.pRank p A ≤ CFSG.Open.pRank p A')
    (h5 : IsPGroup p ↥(E' ⊔ A')) : ddKey p E A ≤ ddKey p E' A' := by
  classical
  unfold ddKey
  have h6 : (if IsPGroup p ↥(E ⊔ A) then 1 else 0) ≤ (if IsPGroup p ↥(E' ⊔ A') then 1 else 0) := by
    rw [if_pos h5]
    split_ifs <;> norm_num
  exact Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h1, Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h2,
    Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h3, Prod.Lex.toLex_mono (Prod.mk_le_mk.2 ⟨h4, h6⟩)⟩)⟩)⟩)

theorem U_le_A {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U)
    (hUR : U ≤ centerOf R) : U ≤ A := by
  have hAsc : IsSCp p M A := h.pair.1.2.1.1.1
  have hAR : A ≤ R := le_sup_left.trans h.hR.2
  have hBM : B ≤ M := (le_sup_right : B ≤ A ⊔ B).trans (h.hR.2.trans h.hR.1.1)
  have hUM : U ≤ M := hU.1.1.trans hBM
  have hAU : A ≤ Subgroup.centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Lemma1314b.mem_centerOf_iff_aux R u).1 (hUR hu)).2 a (hAR ha) |>.symm
  have hel : IsElemAbelian p (A ⊔ U) := isElemAbelian_sup_of_commute hAsc.2.1 hU.1.2.1 hAU
  have heq := hAsc.2.2 (A ⊔ U) (sup_le hAsc.1 hUM) hel le_sup_left
  exact le_sup_right.trans heq.le

theorem rank_inf_le_two_of_rank_eq_three {m p : ℕ} {B M E A : Subgroup G} (h : Sec11 G m p B M E A)
    (hA3 : CFSG.Open.pRank p A = 3) : CFSG.Open.pRank p (E ⊓ A) ≤ 2 := by
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hE : inD p M E := h.pair.1.1
  have hAp : inDp p M A := h.pair.1.2.1
  have hAsc : IsSCp p M A := hAp.1.1
  by_contra hc
  have h3 : 3 ≤ CFSG.Open.pRank p (E ⊓ A) := by omega
  obtain ⟨F, hF, hFel, hFc⟩ := CFSG.SectionRank.exists_pRank hp1 (E ⊓ A)
  obtain ⟨k, hk⟩ := exists_card_eq_pow (isPGroup_of_isElemAbelian' hAsc.2.1)
  have hk3 : k ≤ 3 := (CFSG.SectionRank.le_pRank hp1 le_rfl hAsc.2.1 hk).trans hA3.le
  have hFA : F = A := by
    refine Subgroup.eq_of_le_of_card_ge (hF.trans inf_le_right) ?_
    rw [hk, hFc]
    exact Nat.pow_le_pow_right hp.pos (hk3.trans h3)
  have hAE : A ≤ E := hFA ▸ (hF.trans inf_le_left)
  have hEA : E = A := hAsc.2.2 E hE.1.1.1 hE.1.1.2.1 hAE
  exact hAp.2 (hEA ▸ hE.2)

theorem isDDpStar_B_A {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (hA0 : CFSG.Open.pRank p (E ⊓ A) ≤ 2)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) : IsDDpStar p M B A := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp1 : 1 < p := hp.one_lt
  have hB : inD p M B := lemma101_ii_holds h.toSec13.toSec11.toSec10Fails
  have hAp : inDp p M A := h.pair.1.2.1
  have hUA : U ≤ A := U_le_A h hU hUR
  have h2 : 2 ≤ CFSG.Open.pRank p (B ⊓ A) :=
    CFSG.SectionRank.le_pRank hp1 (le_inf hU.1.1 hUA) hU.1.2.1 hU.1.2.2
  refine ⟨⟨hB, hAp, h2⟩, fun E' A' hE'A' => (h.pair.2 E' A' hE'A').trans ?_⟩
  have hEr : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p B := by
    have hEM : E ≤ M := h.pair.1.1.1.1.1
    have h1 : CFSG.Open.pRank p E ≤ CFSG.Open.pRank p M := CFSG.SectionRank.pRank_mono hp1 hEM
    have h2' : CFSG.Open.pRank p M ≤ m :=
      (pRank_le_glaTwoLocalRank hp1 h.pre.1.1).trans hS.rank_eq.le
    have h3 : m ≤ CFSG.Open.pRank p B :=
      CFSG.SectionRank.le_pRank hp1 le_rfl hB.1.1.2.1 (hS.card_eq h.bOne)
    omega
  have hpg : IsPGroup p ↥(B ⊔ A) := h.hR.1.2.1.to_le (sup_comm A B ▸ h.hR.2)
  exact ddKey_le_of_le (by omega) (min_le_min hEr le_rfl) hEr le_rfl hpg

theorem core_cg2_le_M (hP112 : Prop112Statement) {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (hA0 : CFSG.Open.pRank p (E ⊓ A) ≤ 2)
    {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R)
    (hii : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) :
    GLAPPrimeCoreOf p (Cg2 z d) ≤ M := by
  have h11 : Sec11 G m p B M B A := ⟨h.toSec13.toSec11.toSec10Fails, isDDpStar_B_A h hA0 hU hUR⟩
  have hdA : d ∈ A := h.hD.1 h.hd.1
  have hzBA : z ∈ B ⊓ A := ⟨hU.1.1 hz, U_le_A h hU hUR hz⟩
  rcases hP112 h11 hdA h.hd.2 hzBA hz1 with h1 | h2
  · exact h1
  · exact absurd h2 hii

theorem cg2_eq_inf' (d z : G) : Cg2 z d = Cg d ⊓ Cg z := by
  rw [← Lemma1314c.cg2_eq_inf d z, Cg2, Cg2, Set.pair_comm]

theorem core_inf_le_core_cg2 {p : ℕ} (hp : p.Prime) {X : Subgroup G} {d z : G}
    (hX : CFSG.Open.IsSubnormal X (Cg d)) :
    GLAPPrimeCoreOf p (X ⊓ Cg z) ≤ GLAPPrimeCoreOf p (Cg2 z d) := by
  rw [cg2_eq_inf']
  exact glaPPrimeCoreOf_le_of_isSubnormal hp (isSubnormal_inf hX (Cg z))

theorem uConjJoin_eq_of_le_normalizer {U L : Subgroup G}
    (hUN : U ≤ Subgroup.normalizer (L : Set G)) : Lemma1314c.uConjJoin U L = L := by
  unfold Lemma1314c.uConjJoin
  refine le_antisymm (iSup₂_le fun u hu => le_of_eq (gLBConj_eq_of_mem_normalizer (hUN hu))) ?_
  exact le_iSup₂_of_le (f := fun u (_ : u ∈ U) => GLBConj u L) 1 U.one_mem
    (le_of_eq (gLBConj_eq_of_mem_normalizer (Subgroup.one_mem _)).symm)

theorem chevOpM_of_rank (hP112 : Prop112Statement) (hL1313 : Lemma1313Statement)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement) {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    (h139a : Prop139a p M D) (hA3 : CFSG.Open.pRank p A = 3) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) (hUR : U ≤ centerOf R) {b : G}
    (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hii : ¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) :
    ∀ z ∈ U, z ≠ 1 →
      GLAPPrimeCoreOf p (Lemma1314c.uConjJoin U (Lemma1314.LOf p L0 d b) ⊓ Cg z) ≤ M := by
  intro z hz hz1
  have hp : p.Prime := h.standing.prime
  obtain ⟨-, ⟨hLc, -, -⟩, -, -⟩ := hL1313 h hU hb hb1
  have hA0 : CFSG.Open.pRank p (E ⊓ A) ≤ 2 :=
    rank_inf_le_two_of_rank_eq_three h.toSec13.toSec11 hA3
  rw [uConjJoin_eq_of_le_normalizer (Lemma1314c.U_le_normalizer_LOf h h139a hL133 hcomp hU hb hb1)]
  exact (core_inf_le_core_cg2 hp hLc.2.1).trans (core_cg2_le_M hP112 h hA0 hU hUR hii hz hz1)

end ChevOpM

section FiFaith

variable {G : Type} [Group G] [Finite G]

theorem barAut_inner_p {p : ℕ} {L : Subgroup G} {u : G} (huL : u ∈ L)
    (huN : u ∈ Subgroup.normalizer (L : Set G)) :
    barAut p L ⟨u, huN⟩ = MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨u, huL⟩) := by
  apply MulEquiv.ext
  intro z
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [barAut_mk, MulAut.conj_apply, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    all_goals (apply Subtype.ext; simp)

theorem mem_layer_of_p_element {p : ℕ} [Fact p.Prime] {L0 : Subgroup G} {b u0 : G}
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0))
    (hu0 : u0 ∈ L0 ⊓ Subgroup.centralizer ({b} : Set G)) (hu0p : u0 ^ p = 1) :
    u0 ∈ GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) := by
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hY
  set Z : Subgroup G := GLAPLayer p Y with hZ
  have hZY : Z ≤ Y := by
    rw [hZ]
    unfold GLAPLayer
    exact sSup_le fun K hK => hK.1
  obtain ⟨-, htop⟩ := Lemma1313.covering_data hbord hnorm hcomm hquasi
  obtain ⟨k, hkZ, hkn⟩ :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_top_iff p hZY).1 htop u0 hu0
  have hZn : ∀ y ∈ Y, GLBConj y Z = Z := by
    intro y hy
    rw [hZ, ← Prop1310a5b.glaPLayer_gLBConj', gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hy)]
  haveI hnormal : (Z.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (n : G) ∈ GLBConj (g : G) Z := by
      rw [hZn g g.2]
      exact hn
    have h2 := mem_gLBConj.1 h1
    simpa using h2
  set n : G := k⁻¹ * u0 with hn
  have hkY : k ∈ Y := hZY hkZ
  have hnO : n ∈ GLAPPrimeCoreOf p Y := hkn
  have hnY : n ∈ Y := Lemma1313.glaPPrimeCoreOf_le_self Y hnO
  have hcopm : Nat.Coprime p (orderOf n) := by
    have hd : orderOf (⟨n, hnO⟩ : ↥(GLAPPrimeCoreOf p Y)) ∣ Nat.card ↥(GLAPPrimeCoreOf p Y) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hd
    exact Nat.Coprime.coprime_dvd_right hd (Lemma1313.coprime_card_glaPPrimeCoreOf p Y)
  set π := QuotientGroup.mk' (Z.subgroupOf Y) with hπ
  have hu0Y : u0 ∈ Y := hu0
  have hk1 : π ⟨k, hkY⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hkZ)
  have hsplit : π ⟨u0, hu0Y⟩ = π ⟨n, hnY⟩ := by
    have : (⟨u0, hu0Y⟩ : ↥Y) = ⟨k, hkY⟩ * ⟨n, hnY⟩ := by
      apply Subtype.ext
      simp [hn]
    rw [this, map_mul, hk1, one_mul]
  have h3 : (π ⟨u0, hu0Y⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨u0, hu0Y⟩ : ↥Y) ^ p = 1 := Subtype.ext (by simpa using hu0p)
    rw [this, map_one]
  have hm : (π ⟨u0, hu0Y⟩) ^ (orderOf n) = 1 := by
    rw [hsplit, ← map_pow]
    have : (⟨n, hnY⟩ : ↥Y) ^ (orderOf n) = 1 := by
      apply Subtype.ext
      simpa using pow_orderOf_eq_one n
    rw [this, map_one]
  have hone : orderOf (π ⟨u0, hu0Y⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopm (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one hm)
  have hπ1 : π ⟨u0, hu0Y⟩ = 1 := orderOf_eq_one_iff.1 hone
  have hmem := (QuotientGroup.eq_one_iff _).1 hπ1
  exact Subgroup.mem_subgroupOf.1 hmem

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center X = ⊥) : Subgroup.center Y = ⊥ := by
  rw [← Subgroup.map_center_eq e, h, Subgroup.map_bot]

theorem eq_one_of_comm_barX {p : ℕ} [Fact p.Prime] {L K : Subgroup G} (hKL : K ≤ L)
    (hZ : Subgroup.center (barOf p K) = ⊥) {w : barOf p L} (hw : w ∈ barX p L K)
    (hwp : w ^ p = 1) (hcomm : ∀ y ∈ barX p L K, y * w = w * y) : w = 1 := by
  set J : Subgroup (barOf p L) := barX p L K with hJ
  set w' : ↥J := ⟨w, hw⟩ with hw'
  have hcen : (QuotientGroup.mk' (GLAPPrimeCore p ↥J) w') ∈ Subgroup.center (barOf p J) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥J) q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm y y.2)
  have hZJ : Subgroup.center (barOf p J) = ⊥ :=
    center_eq_bot_of_mulEquiv (Prop115.barOfIso (p := p) hKL) hZ
  rw [hZJ, Subgroup.mem_bot] at hcen
  have hcore : w' ∈ GLAPPrimeCore p ↥J := (QuotientGroup.eq_one_iff _).1 hcen
  have hord : orderOf (⟨w', hcore⟩ : ↥(GLAPPrimeCore p ↥J)) ∣ Nat.card ↥(GLAPPrimeCore p ↥J) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hord
  have hwp' : w' ^ p = 1 := Subtype.ext (by simpa [hw'] using hwp)
  have hcop : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
  have h1 : orderOf w' = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hwp') hord
  have h2 : w' = 1 := orderOf_eq_one_iff.1 h1
  exact congrArg Subtype.val h2

theorem eq_one_of_mem_coreOf_of_pow {p : ℕ} [Fact p.Prime] {L : Subgroup G} {y : G}
    (hy : y ∈ GLAPPrimeCoreOf p L) (hyp : y ^ p = 1) : y = 1 := by
  have hord : orderOf (⟨y, hy⟩ : ↥(GLAPPrimeCoreOf p L)) ∣ Nat.card ↥(GLAPPrimeCoreOf p L) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hord
  have h1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes (Lemma1313.coprime_card_glaPPrimeCoreOf p L)
    (orderOf_dvd_of_pow_eq_one hyp) hord
  exact orderOf_eq_one_iff.1 h1

theorem exists_zpow_mul_zpow_of_mem_closure_pair {a b c : G} (hab : a * b = b * a)
    (hc : c ∈ Subgroup.closure ({a, b} : Set G)) : ∃ i j : ℤ, c = a ^ i * b ^ j := by
  have hcomm : Commute a b := hab
  refine Prop1310a5b.closure_pair_induction (P := fun c => ∃ i j : ℤ, c = a ^ i * b ^ j)
    ⟨1, 0, by simp⟩ ⟨0, 1, by simp⟩ ⟨0, 0, by simp⟩ ?_ ?_ hc
  · rintro x y ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + k, j + l, ?_⟩
    have hjk : b ^ j * a ^ k = a ^ k * b ^ j := ((hcomm.zpow_zpow k j).eq).symm
    rw [zpow_add, zpow_add]
    calc a ^ i * b ^ j * (a ^ k * b ^ l) = a ^ i * (b ^ j * a ^ k) * b ^ l := by group
      _ = a ^ i * (a ^ k * b ^ j) * b ^ l := by rw [hjk]
      _ = a ^ i * a ^ k * (b ^ j * b ^ l) := by group
  · rintro x ⟨i, j, rfl⟩
    refine ⟨-i, -j, ?_⟩
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact ((hcomm.zpow_zpow i j).inv_inv).eq.symm

theorem zpow_apply_eq_of_apply_eq {K : Type*} [Group K] {x : MulAut K} {y : K} (hx : x y = y)
    (j : ℤ) : (x ^ j) y = y := by
  have hmem : x ∈ MulAction.stabilizer (MulAut K) y := by
    rw [MulAction.mem_stabilizer_iff]
    exact hx
  have hj := Subgroup.zpow_mem _ hmem j
  rw [MulAction.mem_stabilizer_iff] at hj
  exact hj

theorem centBar_U_LOf_eq_bot (hL1313 : Lemma1313Statement) (hL133 : Lemma133Statement)
    (hcomp : Sec13g.Lemma133_compStatement) {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) :
    centBar p U (Lemma1314.LOf p L0 d b) = ⊥ := by
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set L : Subgroup G := Lemma1314.LOf p L0 d b with hLdef
  set L0b : Subgroup G := Lemma1314.L0bOf p L0 b with hL0bdef
  have hbU : b ∈ U := mem_of_mem_centBar hb
  have hbd : b ∈ Cg d := hU.2.1 hbU
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := b_mem_normalizer_LOf hbd
  have hbp : b ^ p = 1 := hU.1.2.1.2 b hbU
  have hUN : U ≤ Subgroup.normalizer (L : Set G) :=
    Lemma1314c.U_le_normalizer_LOf h h139a hL133 hcomp hU hb hb1
  obtain ⟨-, ⟨-, hL0bc, -⟩, -, -⟩ := hL1313 h hU hb hb1
  have hL0bL : L0b ≤ L := hL0bc.1.trans inf_le_left
  obtain ⟨⟨x0, hx0mem⟩, hx01⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU.2.2.1
  have hx0U : x0 ∈ U := (Subgroup.mem_inf.1 hx0mem).1
  have hx0L0 : x0 ∈ L0 := (Subgroup.mem_inf.1 hx0mem).2
  have hx01' : x0 ≠ 1 := fun e => hx01 (Subtype.ext e)
  have hx0p : x0 ^ p = 1 := hU.1.2.1.2 x0 hx0U
  have hx0b : x0 * b = b * x0 := elemAbelian_comm hU.1.2.1 hx0U hbU
  obtain ⟨hbord, -, -, hnorm, hcomm, -, hquasi⟩ := Lemma1313.setting_facts h hU hb hb1
  have hx0Cb : x0 ∈ L0 ⊓ Subgroup.centralizer ({b} : Set G) :=
    ⟨hx0L0, Subgroup.mem_centralizer_singleton_iff.2 hx0b⟩
  have hx0L0b : x0 ∈ L0b := mem_layer_of_p_element hbord hnorm hcomm hquasi hx0Cb hx0p
  have hx0L : x0 ∈ L := hL0bL hx0L0b
  have hZ0 := Lemma1314c.center_barOf_L0_eq_bot h h139a hL133 hcomp
  have hbx : b ∉ Subgroup.zpowers x0 := by
    intro hbz
    exact hb1 (Lemma1314c.eq_one_of_mem_centBar_of_mem hp (Sec13g.le_L1of (p := p) (M := M) (D := D))
      hZ0 hb ((Subgroup.zpowers_le.2 hx0L0) hbz) hbp)
  have hUeq := Lemma1314c.closure_pair_eq_of_card hp hU.1 hx0U hbU hx01' hbx
  obtain ⟨e0⟩ := Lemma1313.barOf_L0b_iso h hU hb hb1
  have hZ0b : Subgroup.center (barOf p L0b) = ⊥ := center_eq_bot_of_mulEquiv e0.symm hZ0
  set x : MulAut (barOf p L) := barAut p L ⟨b, hbN⟩ with hxdef
  set y : barOf p L := QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨x0, hx0L⟩ with hydef
  have hx1 : x ≠ 1 := barAut_ne_one_of_lemma1313 hL1313 h hU hb hb1 hbN
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← map_pow]
    have : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 := Subtype.ext hbp
    rw [this, map_one]
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hyJ : y ∈ barX p L L0b := ⟨⟨x0, hx0L⟩, Subgroup.mem_subgroupOf.2 hx0L0b, rfl⟩
  have hyp : y ^ p = 1 := by
    rw [hydef, ← map_pow]
    have : (⟨x0, hx0L⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hx0p)
    rw [this, map_one]
  have hxJ : ∀ w ∈ barX p L L0b, x w = w := by
    rintro _ ⟨⟨l, hlL⟩, hl, rfl⟩
    have hl' : l ∈ L0b := Subgroup.mem_subgroupOf.1 hl
    have hlb : b * l = l * b :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hL0bc.1 hl')).2).symm
    rw [hxdef]
    show barAut p L ⟨b, hbN⟩ (QuotientGroup.mk ⟨l, hlL⟩) = QuotientGroup.mk ⟨l, hlL⟩
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    show b * l * b⁻¹ = l
    rw [hlb]
    group
  have hx0N : x0 ∈ Subgroup.normalizer (L : Set G) := hUN hx0U
  have hinner : barAut p L ⟨x0, hx0N⟩ = MulAut.conj y := barAut_inner_p hx0L hx0N
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  obtain ⟨hcK, hcU⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hcN, hcbar⟩ := mem_centK_iff.1 hcK
  rw [← hUeq] at hcU
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hx0b hcU
  have hsplit : (⟨x0 ^ i * b ^ j, hcN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      (⟨x0, hx0N⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ i * ⟨b, hbN⟩ ^ j := by
    apply Subtype.ext
    simp
  rw [hsplit, map_mul, map_zpow, map_zpow, hinner, ← hxdef] at hcbar
  have hxj : x ^ j = MulAut.conj (y ^ (-i)) := by
    rw [map_zpow, zpow_neg]
    exact (eq_inv_of_mul_eq_one_right hcbar)
  have hw : y ^ (-i) = 1 := by
    refine eq_one_of_comm_barX hL0bL hZ0b (Subgroup.zpow_mem _ hyJ (-i)) ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
    · intro w hwJ
      have h1 : (x ^ j) w = w := zpow_apply_eq_of_apply_eq (hxJ w hwJ) j
      rw [hxj, MulAut.conj_apply] at h1
      calc w * y ^ (-i) = y ^ (-i) * w * (y ^ (-i))⁻¹ * y ^ (-i) := by rw [h1]
        _ = y ^ (-i) * w := by group
  have hxj1 : x ^ j = 1 := by rw [hxj, hw, map_one]
  have hpj : (p : ℤ) ∣ j := by
    rw [← hxord]
    exact orderOf_dvd_iff_zpow_eq_one.2 hxj1
  have hbj : b ^ j = 1 := by
    obtain ⟨t, rfl⟩ := hpj
    rw [zpow_mul, zpow_natCast, hbp, one_zpow]
  rw [hxj1, mul_one, ← map_zpow] at hcbar
  have hyi : y ^ i = 1 := by
    refine eq_one_of_comm_barX hL0bL hZ0b (Subgroup.zpow_mem _ hyJ i) ?_ ?_
    · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]
    · intro w _
      have h1 : MulAut.conj (y ^ i) w = w := by rw [hcbar]; rfl
      rw [MulAut.conj_apply] at h1
      calc w * y ^ i = y ^ i * w * (y ^ i)⁻¹ * y ^ i := by rw [h1]
        _ = y ^ i * w := by group
  have hx0i : x0 ^ i ∈ GLAPPrimeCoreOf p L := by
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) ((⟨x0, hx0L⟩ : ↥L) ^ i) = 1 := by
      rw [map_zpow, ← hydef, hyi]
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : (⟨x0 ^ i, L.zpow_mem hx0L i⟩ : ↥L) = (⟨x0, hx0L⟩ : ↥L) ^ i := Subtype.ext (by simp)
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff p L _).2
      ⟨L.zpow_mem hx0L i, h3 ▸ h2⟩
  have hx0i1 : x0 ^ i = 1 := by
    refine eq_one_of_mem_coreOf_of_pow hx0i ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx0p, one_zpow]
  rw [hx0i1, hbj, one_mul]

theorem fiFaithBlock_of_inputs (hL1313 : Lemma1313Statement) (hL133 : Lemma133Statement)
    (hcomp : Sec13g.Lemma133_compStatement) : Lemma1314c.FiFaithBlock := by
  intro G _ _ m p B M E A D T R L0 d h h139a U hU _ b hb hb1 _ _
  exact centBar_U_LOf_eq_bot hL1313 hL133 hcomp h h139a hU hb hb1

end FiFaith

section Exc

@[expose] def Exc5Orders : Prop :=
  ∀ idx : TauCeti.ValidLieTypeIndex,
    (idx.1 = TauCeti.LieTypeIndex.tits → Nat.card (TauCeti.CFSGIndex.lie idx).Group = ordTits) ∧
    (idx.1 = TauCeti.LieTypeIndex.reeF4 2 →
      Nat.card (TauCeti.CFSGIndex.lie idx).Group = ordTwistedF4 (2 ^ 5)) ∧
    (idx.1 = TauCeti.LieTypeIndex.suzuki 2 →
      Nat.card (TauCeti.CFSGIndex.lie idx).Group = ordSuzuki (2 ^ 5))

theorem not_dvd_card_of_exc (hO : Exc5Orders) {X : Type} [Group X]
    (hX : Lemma1314.IsTitsGroup X ∨ Lemma1314.IsReeF4_32Group X ∨ Lemma1314.IsSz32Group X) :
    ¬ 3 ^ 4 ∣ Nat.card X := by
  rcases hX with ⟨idx, hidx, ⟨e⟩⟩ | ⟨idx, hidx, ⟨e⟩⟩ | ⟨idx, hidx, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, (hO idx).1 hidx]
    unfold ordTits
    norm_num
  · rw [Nat.card_congr e.toEquiv, (hO idx).2.1 hidx]
    unfold ordTwistedF4
    norm_num
  · rw [Nat.card_congr e.toEquiv, (hO idx).2.2 hidx]
    unfold ordSuzuki
    norm_num

theorem eighty_one_dvd_fourProd {k : ℕ} (hk : 3 ≤ k) :
    3 ^ 4 ∣ CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k _ ih =>
    rw [CFSG.HardMathSupport.Curtis.Coordinator.PLType.fourProd_succ]
    exact Dvd.dvd.mul_right ih _

theorem three_pow_four_dvd_card_omega {ε : Bool} {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X] [Finite X]
    (hX : IsOmegaTwo ε (n + 1) X) (h5 : HasFixedPointFreeOrder ε n 5) : 3 ^ 4 ∣ Nat.card X := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h3
  · exfalso
    cases ε
    · obtain ⟨A, -, hord, -⟩ := h5
      have h1 := orderOf_dvd_natCard A
      rw [hord, CatalogInputs.card_GL_zmod_two_eq _ 2 (by simp)] at h1
      revert h1
      decide
    · obtain ⟨A, hA, hord, -⟩ := h5
      rw [OmegaFacts.statedOmega_plus_one, Subgroup.mem_bot] at hA
      rw [hA, orderOf_one] at hord
      omega
  · cases ε
    · rcases OmegaFacts.omega_data hX with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, hc, -⟩
      all_goals try omega
      rw [hc, OmegaFacts.omegaOrd_three_minus]
      norm_num
    · exfalso
      obtain ⟨A, hA, hord, -⟩ := h5
      have h1 : orderOf (⟨A, hA⟩ : ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2)))) ∣
          Nat.card ↥(StatedOmega (StatedQuadPlus 2 (ZMod 2))) := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk, hord] at h1
      have h2 := h1.trans Inputs71.card_statedOmega_plus_two_dvd
      revert h2
      decide
  · rcases OmegaFacts.omega_data hX with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, hc, -⟩
    all_goals try omega
    rw [hc]
    unfold OmegaFacts.omegaOrd
    simp only [Nat.add_sub_cancel]
    exact Dvd.dvd.mul_left (eighty_one_dvd_fourProd h3) _

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_center {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) {Q : Type} [Group Q]
    [Finite Q] (hcore : GLAPPrimeCore p Q = ⊥) : ¬ q ∣ Nat.card (Subgroup.center Q) := by
  intro hdvd
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hdvd
  have hzc : (z : Q) ∈ Subgroup.center Q := z.2
  have hnorm : (Subgroup.zpowers (z : Q)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : g * (z : Q) ^ k = (z : Q) ^ k * g :=
      (Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hzc k) g)
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hcard : Nat.card (Subgroup.zpowers (z : Q)) = q := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z : Q))) := by
    rw [hcard]
    exact (Nat.coprime_primes hp hq).2 (Ne.symm hqp)
  have hle : Subgroup.zpowers (z : Q) ≤ GLAPPrimeCore p Q :=
    CFSG.le_pPrimeCore_of_normal_coprime hnorm hcop
  rw [hcore, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have : orderOf (z : Q) = 1 := by rw [hle, orderOf_one]
  rw [Subgroup.orderOf_coe, hz] at this
  exact hq.one_lt.ne' this

theorem dvd_card_quotient_center {q k : ℕ} (hq : q.Prime) {Q : Type} [Group Q] [Finite Q]
    (hdvd : q ^ k ∣ Nat.card Q) (hZ : ¬ q ∣ Nat.card (Subgroup.center Q)) :
    q ^ k ∣ Nat.card (Q ⧸ Subgroup.center Q) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)] at hdvd
  exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).2 hZ)).dvd_of_dvd_mul_right hdvd

theorem card_barOf_dvd {p : ℕ} [Fact p.Prime] {K L : Subgroup G} (hKL : K ≤ L) :
    Nat.card (barOf p K) ∣ Nat.card (barOf p L) := by
  rw [Nat.card_congr (Prop115.barOfIso (p := p) hKL).toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card _)

theorem L0bOf_le_LOf {p : ℕ} {L0 : Subgroup G} {d b : G} :
    Lemma1314.L0bOf p L0 b ≤ Lemma1314.LOf p L0 d b :=
  le_iSup₂_of_le (f := fun g (_ : g ∈ GLAPLayer p (Subgroup.centralizer ({d} : Set G))) =>
    GLBConj g (Lemma1314.L0bOf p L0 b)) 1 (Subgroup.one_mem _)
    (le_of_eq (gLBConj_eq_of_mem_normalizer (Subgroup.one_mem _)).symm)

theorem excBlock_of_orders (hL1313 : Lemma1313Statement) (hO : Exc5Orders) : Lemma1314.ExcBlock := by
  intro G _ _ m p B M E A D T R L0 d h _ U hU b hb hb1 hp5 hΩ _ hexc
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  subst hp5
  obtain ⟨ε, n, hn, hO2, hF⟩ := hΩ
  obtain ⟨-, ⟨hLc, -, -⟩, -, -⟩ := hL1313 h hU hb hb1
  set L : Subgroup G := Lemma1314.LOf 5 L0 d b with hLdef
  set Q : Type := barOf 5 L with hQ
  have h81 : 3 ^ 4 ∣ Nat.card Q :=
    (three_pow_four_dvd_card_omega hn hO2 hF).trans (card_barOf_dvd L0bOf_le_LOf)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center Q) :=
    not_dvd_card_center hp Nat.prime_three (by norm_num) (glaPPrimeCore_quotient_eq_bot hp)
  have h81' := dvd_card_quotient_center Nat.prime_three h81 hZ
  set e : Q ≃* ↥(barX 5 (Subgroup.centralizer ({d} : Set G)) L) := quotEquivBarX hp hLc.1 hLc.2.1
  have eZ : (Q ⧸ Subgroup.center Q) ≃*
      (↥(barX 5 (Subgroup.centralizer ({d} : Set G)) L) ⧸
        Subgroup.center ↥(barX 5 (Subgroup.centralizer ({d} : Set G)) L)) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  rw [Nat.card_congr eZ.toEquiv] at h81'
  exact not_dvd_card_of_exc hO hexc h81'

end Exc

section Chev3

@[expose] def Input14_19_3c : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ∀ (J : Type) [Group J] (ε : Bool) (n : ℕ), 1 ≤ n → IsOmegaTwo ε (n + 1) J →
      HasFixedPointFreeOrder ε n 5 → (∃ x : MulAut K, Lemma1314.PumpupVia 5 J K x) →
        IsLieChar (· = 3) K →
          ¬ ∃ Q : ℕ, (IsLpType 5 Q (K ⧸ Subgroup.center K) ∧ 5 ∣ Q - 1) ∨
            (IsUpType 5 Q (K ⧸ Subgroup.center K) ∧ 5 ∣ Q + 1)

@[expose] def InputFi23NotChev3 : Prop :=
  ∀ (K : Type) [Group K], IsSporType .Fi23 K → ¬ IsLieChar (· = 3) K

end Chev3

section ChevGen

variable {G : Type} [Group G] [Finite G]

@[expose] def ChevGenGenBlock : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139a p M D → ∀ {U : Subgroup G},
    IsU1312 p B M D L0 d U → U ≤ centerOf R → ∀ {b : G},
    b ∈ centBar p U (L1of p M D L0) → b ≠ 1 → CFSG.Open.pRank p A = 3 →
    (¬ ∃ A1 : Subgroup G, inD p M A1 ∧ d ∈ A1) →
    IsLieChar (· = 2) (barOf p (Lemma1314.LOf p L0 d b)) →
    (p = 5 → ¬ Lemma1314.I2310Exc5 (barX p (Cg d) (Lemma1314.LOf p L0 d b))) →
      barX p (Cg d) (Lemma1314.LOf p L0 d b) ≤ barX p (Cg d)
        (⨆ z ∈ U, ⨆ (_ : z ≠ 1),
          (GLAPPrimeCoreOf p (Lemma1314c.uConjJoin U (Lemma1314.LOf p L0 d b) ⊓ Cg z) ⊔
            ⨆ (H : Subgroup G) (_ : GLAPComponent p (Cg2 d z) H ∧
              H ≤ Lemma1314c.uConjJoin U (Lemma1314.LOf p L0 d b)), H))

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨hcomm, hsimple⟩ := h
  refine ⟨Group.isPerfect_def.mpr hcomm, hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk' (Subgroup.center Q)) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_def,
      hab ((QuotientGroup.mk' (Subgroup.center Q)) x), mul_inv_cancel_right, mul_inv_cancel]
  rw [hcomm] at hle
  haveI := hsimple
  obtain ⟨a, b, hne⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hne (QuotientGroup.eq.mpr (hle (Subgroup.mem_top _)))

theorem isChevSimple_of_isLieChar {X : Type} [Group X] (h : IsLieChar (· = 2) X) :
    CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 2 (X ⧸ Subgroup.center X) := by
  obtain ⟨idx, ⟨e⟩, hc⟩ := h
  exact Or.inl ⟨.lie idx, hc, ⟨e⟩⟩

theorem glaPComponent_inf_of_le {p : ℕ} (hp : p.Prime) {L H : Subgroup G} {d z : G}
    (hLd : L ≤ Cg d) (hH : GLAPComponent p (Cg2 d z) H) (hHL : H ≤ L) :
    GLAPComponent p (L ⊓ Cg z) H := by
  have hle : L ⊓ Cg z ≤ Cg2 d z := by
    rw [Lemma1314c.cg2_eq_inf]
    exact inf_le_inf_right _ hLd
  have hHz : H ≤ Cg z := hH.1.trans (by rw [Lemma1314c.cg2_eq_inf]; exact inf_le_right)
  exact glaPComponent_of_le hp hH (le_inf hHL hHz) hle

theorem inChevTwo_of_comp (hI144 : Lemma1315b.Input14_4_1) (hL1313 : Lemma1313Statement)
    (hL133 : Lemma133Statement) (hcomp : Sec13g.Lemma133_compStatement) {m p : ℕ}
    {B M E A D T R L0 : Subgroup G} {d : G} (h : Cex1310 G m p B M E A D T R L0 d)
    (h139a : Prop139a p M D) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G}
    (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hC2 : IsLieChar (· = 2) (barOf p (Lemma1314.LOf p L0 d b))) {z : G} (hz : z ∈ U) (hz1 : z ≠ 1)
    {H : Subgroup G} (hH : GLAPComponent p (Cg2 d z) H) (hHL : H ≤ Lemma1314.LOf p L0 d b) :
    Prop95Iv.InChevTwo (barOf p H) := by
  have hp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h139a.1
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    norm_num at hp
  obtain ⟨-, ⟨hLc, -, -⟩, -, -⟩ := hL1313 h hU hb hb1
  set L : Subgroup G := Lemma1314.LOf p L0 d b with hLdef
  have hUN : U ≤ Subgroup.normalizer (L : Set G) :=
    Lemma1314c.U_le_normalizer_LOf h h139a hL133 hcomp hU hb hb1
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := hUN hz
  have hzp : z ^ p = 1 := hU.1.2.1.2 z hz
  have hH' : GLAPComponent p (L ⊓ Cg z) H := glaPComponent_inf_of_le hp hLc.1 hH hHL
  have hHLz : GLAPComponent p (barX p L (L ⊓ Cg z)) (barX p L H) :=
    Prop115b.barX_glaPComponent_of_le hp inf_le_left hH'
  have hfix := AltFacts3.fixedSub_barAut_eq_p hp hzp hzN
  have hHq : CFSG.Open.IsQuasisimple (barOf p H) := Lemma1313.isQuasisimple_barOf_of_pComp hH
  refine ⟨isQuasisimple_of_open hHq, ?_⟩
  have hx : barAut p L ⟨z, hzN⟩ ≠ 1 := by
    intro hx1
    have hzc : z ∈ centBar p U L :=
      Subgroup.mem_inf.2 ⟨mem_centK_iff.2 ⟨hzN, hx1⟩, hz⟩
    rw [centBar_U_LOf_eq_bot hL1313 hL133 hcomp h h139a hU hb hb1, Subgroup.mem_bot] at hzc
    exact hz1 hzc
  have hxp : (barAut p L ⟨z, hzN⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨z, hzN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 := Subtype.ext hzp
    rw [this, map_one]
  have hpump : Lemma1314.PumpupVia p (barOf p H) (barOf p L) (barAut p L ⟨z, hzN⟩) := by
    refine ⟨orderOf_eq_prime hxp hx, barX p L H, ?_, ⟨(Prop115.barOfIso (hH'.1.trans inf_le_left)).symm⟩⟩
    rw [fixSub_eq_fixedSub, hfix]
    exact hHLz
  have hKH : CFSG.LocalAnalysis.GLTheoremA.IsKHat (barOf p L) := kHatBlock_of_lemma1313 hL1313 h hU hb hb1
  obtain ⟨hcs, -⟩ := hI144 p 2 hp hp5 Nat.prime_two (barOf p L) hKH (glaPPrimeCore_quotient_eq_bot hp)
    (isChevSimple_of_isLieChar hC2) (barOf p H) _ hpump
  exact Lemma123.isChevTwo_of_isChevSimple_two hcs

theorem chevGenBlock_of_inputs (hGen : ChevGenGenBlock) (hI144 : Lemma1315b.Input14_4_1)
    (hL1313 : Lemma1313Statement) (hL133 : Lemma133Statement)
    (hcomp : Sec13g.Lemma133_compStatement) : Lemma1314c.ChevGenBlock := by
  intro G _ _ m p B M E A D T R L0 d h h139a U hU hUR b hb hb1 hA3 hii hC2 hexc
  refine ⟨hGen h h139a hU hUR hb hb1 hA3 hii hC2 hexc, ?_⟩
  intro z hz hz1 H hH hHL
  rw [uConjJoin_eq_of_le_normalizer (Lemma1314c.U_le_normalizer_LOf h h139a hL133 hcomp hU hb hb1)]
    at hHL
  exact inChevTwo_of_comp hI144 hL1313 hL133 hcomp h h139a hU hb hb1 hC2 hz hz1 hH hHL

end ChevGen

section Orders

theorem exc5Orders_holds :
    Exc5Orders := by
  intro idx
  obtain ⟨x, hv⟩ := idx
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · obtain rfl : x = TauCeti.LieTypeIndex.tits := h
    exact CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits
      (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46.tits hv)
  · obtain rfl : x = TauCeti.LieTypeIndex.reeF4 2 := h
    exact CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4
      (CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46.reeF4 2 hv)
  · obtain rfl : x = TauCeti.LieTypeIndex.suzuki 2 := h
    obtain ⟨-, a, -, -, hcard⟩ := CFSG.GH74.card_of_suzukiModel
      (CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index 2 hv)
    exact hcard

end Orders

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1314

end
