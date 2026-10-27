module

public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.HardMathSupport.Timmesfeld.Proving.TwoLocalAttain
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

structure Cor112Indep (G : Type) [Group G] [Finite G] (m p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  direct : IsDirectZpowersInf B x L
  rank : GLATwoLocalRank p ↥L = m - 1
  noZ : ¬ p ∣ Nat.card (Subgroup.center ↥L)
  comm : (⁅B ⊓ L, nGen (B ⊓ L) L⁆ : Subgroup G) ≠ ⊥

namespace S11

variable {G : Type} [Group G] [Finite G] {m p q : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}

private theorem cor112_mem_zpowers_sup {K : Subgroup G} {x : G} (hK : ∀ c ∈ K, x * c = c * x)
    {b : G} (hb : b ∈ Subgroup.zpowers x ⊔ K) : ∃ k : ℤ, ∃ c ∈ K, b = x ^ k * c := by
  have hc : ∀ c ∈ K, ∀ l : ℤ, c * x ^ l = x ^ l * c := fun c hcK l =>
    ((show Commute c x from (hK c hcK).symm).zpow_right l).eq
  let S : Subgroup G :=
    { carrier := {g | ∃ k : ℤ, ∃ c ∈ K, g = x ^ k * c}
      mul_mem' := by
        rintro _ _ ⟨k, c, hcK, rfl⟩ ⟨l, d, hdK, rfl⟩
        refine ⟨k + l, c * d, K.mul_mem hcK hdK, ?_⟩
        calc x ^ k * c * (x ^ l * d) = x ^ k * (c * x ^ l) * d := by simp only [mul_assoc]
          _ = x ^ k * (x ^ l * c) * d := by rw [hc c hcK l]
          _ = x ^ (k + l) * (c * d) := by rw [zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 1, K.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, c, hcK, rfl⟩
        refine ⟨-k, c⁻¹, K.inv_mem hcK, ?_⟩
        rw [mul_inv_rev, ← zpow_neg, hc c⁻¹ (K.inv_mem hcK) (-k)] }
  have hle : Subgroup.zpowers x ⊔ K ≤ S := by
    refine sup_le (fun g hg => ?_) (fun c hcK => ⟨0, c, hcK, by simp⟩)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ⟨k, 1, K.one_mem, by simp⟩
  obtain ⟨k, c, hcK, hbk⟩ := hle hb
  exact ⟨k, c, hcK, hbk⟩

private theorem cor112_zpow_pow_eq_one {x : G} {p : ℕ} (hxp : x ^ p = 1) (k : ℤ) :
    (x ^ k) ^ p = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

private theorem cor112_mem_normalizer_of_comm {S : Subgroup G} {x : G}
    (hS : ∀ s ∈ S, x * s = s * x) : x ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have e : x * h * x⁻¹ = h := by rw [hS h hh, mul_inv_cancel_right]
    rw [e]
    exact hh
  · intro hh
    have e1 : x * (x * h * x⁻¹) = x * h := by
      rw [hS _ hh]
      simp [mul_assoc]
    have e2 : x * h * x⁻¹ = h := mul_left_cancel e1
    rw [e2] at hh
    exact hh

private theorem cor112_inf_zpowers_eq_bot {p : ℕ} (hp : p.Prime) {x : G} {E L : Subgroup G}
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxn : x ∉ L) (hEL : E ≤ L) :
    E ⊓ Subgroup.zpowers x = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  rintro y ⟨hyE, hyz⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyz
  rw [Subgroup.mem_bot]
  by_contra hne
  have hdvd : orderOf (x ^ k) ∣ p := orderOf_dvd_of_pow_eq_one (cor112_zpow_pow_eq_one hxp k)
  have hord : orderOf (x ^ k) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hne
    · exact h1
  have hle : Subgroup.zpowers (x ^ k) ≤ Subgroup.zpowers x :=
    Subgroup.zpowers_le.2 (Subgroup.zpow_mem_zpowers x k)
  have hcard : Nat.card (Subgroup.zpowers x) ≤ Nat.card (Subgroup.zpowers (x ^ k)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, orderOf_eq_prime hxp hx1]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hx : x ∈ Subgroup.zpowers (x ^ k) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hxn (Subgroup.zpowers_le.2 (hEL hyE) hx)

private theorem cor112_transport {p : ℕ} {L : Subgroup G} (T₀ E₀ : Subgroup ↥L) (hT₀ : T₀ ≠ ⊥)
    (hT₀2 : IsPGroup 2 T₀) (hE₀N : E₀ ≤ Subgroup.normalizer (T₀ : Set ↥L))
    (hE₀a : IsElemAbelian p E₀) :
    T₀.map L.subtype ≠ ⊥ ∧ IsPGroup 2 (T₀.map L.subtype) ∧ T₀.map L.subtype ≤ L ∧
      E₀.map L.subtype ≤ L ∧
      E₀.map L.subtype ≤ Subgroup.normalizer ((T₀.map L.subtype : Subgroup G) : Set G) ∧
      IsElemAbelian p (E₀.map L.subtype) ∧ Nat.card (E₀.map L.subtype) = Nat.card E₀ := by
  have hconj : ∀ (e : ↥L) (S : Subgroup ↥L),
      GLBConj (L.subtype e) (S.map L.subtype) = (GLBConj e S).map L.subtype := by
    intro e S
    unfold GLBConj
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨?_, hT₀2.map L.subtype, Subgroup.map_subtype_le T₀, Subgroup.map_subtype_le E₀, ?_, ?_,
    Subgroup.card_map_of_injective L.subtype_injective⟩
  · intro h
    apply hT₀
    exact Subgroup.map_injective L.subtype_injective (h.trans (Subgroup.map_bot _).symm)
  · rintro _ ⟨e, he, rfl⟩
    rw [mem_normalizer_iff_gLBConj_eq, hconj, mem_normalizer_iff_gLBConj_eq.1 (hE₀N he)]
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨b₀, hb₀, hb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← ha, ← hb, ← map_mul, ← map_mul, isElemAbelian_commute hE₀a ha₀ hb₀]
    · obtain ⟨a₀, ha₀, ha⟩ := Subgroup.mem_map.1 ha
      rw [← ha, ← map_pow, hE₀a.2 a₀ ha₀, map_one]

private theorem cor112_isElemAbelian_sup {p : ℕ} {K : Subgroup G} {x : G} (hK : IsElemAbelian p K)
    (hxK : ∀ c ∈ K, x * c = c * x) (hxp : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x ⊔ K) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨k, c, hc, hak⟩ := cor112_mem_zpowers_sup hxK a.2
    obtain ⟨l, d, hd, hbl⟩ := cor112_mem_zpowers_sup hxK b.2
    have hxl : Commute (x ^ k) (x ^ l) := (Commute.refl x).zpow_zpow k l
    have hcxl : Commute c (x ^ l) := ((show Commute x c from hxK c hc).symm).zpow_right l
    have h1 : Commute (x ^ k * c) (x ^ l) := Commute.mul_left hxl hcxl
    have hxkd : Commute (x ^ k) d := (((show Commute x d from hxK d hd).symm).zpow_right k).symm
    have hcd : Commute c d := isElemAbelian_commute hK hc hd
    have h2 : Commute (x ^ k * c) d := Commute.mul_left hxkd hcd
    have h3 : Commute (x ^ k * c) (x ^ l * d) := Commute.mul_right h1 h2
    apply Subtype.ext
    show (a : G) * (b : G) = (b : G) * (a : G)
    rw [hak, hbl]
    exact h3.eq
  · obtain ⟨k, c, hc, rfl⟩ := cor112_mem_zpowers_sup hxK ha
    rw [((show Commute x c from hxK c hc).zpow_left k).mul_pow p, cor112_zpow_pow_eq_one hxp k,
      hK.2 c hc, one_mul]

private theorem cor112_glaPLayer_gLBConj (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine CFSG.LocalAnalysis.GLTheoremB.gLBConj_eq_of_forall_ge (F := GLAPLayer p)
    (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g)

private theorem cor112_two_dvd_card_of_quasisimple {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) : 2 ∣ Nat.card K := by
  by_contra h
  have hodd : Odd (Nat.card K) := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have : Group.IsSolvable K := CFSG.Milestones.odd_order_solvable hodd
  have : Nontrivial K := isQuasisimple_nontrivial hK
  have : Group.IsPerfect K := ⟨hK.1⟩
  exact Group.IsPerfect.not_isSolvable K ‹_›

theorem mem_normalizer_glaPLayer {p : ℕ} {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, ← cor112_glaPLayer_gLBConj, gLBConj_eq_of_mem_normalizer hg]

theorem le_twoLocalRank_sub {q r : ℕ} (hq : q.Prime) {L S E : Subgroup G} (hSL : S ≤ L) (hS : IsPGroup 2 S)
    (hSne : S ≠ ⊥) (hEL : E ≤ L) (hES : E ≤ Subgroup.normalizer (S : Set G)) (hE : IsElemAbelian q E)
    (hEc : Nat.card E = q ^ r) : r ≤ GLATwoLocalRank q ↥L := by
  have hS' : IsPGroup 2 (S.subgroupOf L) :=
    hS.of_injective (Subgroup.subgroupOfEquivOfLe hSL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hSL).injective
  have hSne' : S.subgroupOf L ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hSL] at h
    exact hSne h
  have hES' : E.subgroupOf L ≤ Subgroup.normalizer ((S.subgroupOf L : Subgroup L) : Set L) := by
    intro e he
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.1 he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hn := Subgroup.mem_normalizer_iff.1 (hES heE) (h : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn
  have hE' : IsElemAbelian q (E.subgroupOf L) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext
      (isElemAbelian_commute hE (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)))⟩⟩,
      fun a ha => Subtype.ext ?_⟩
    simpa using hE.2 (a : G) (Subgroup.mem_subgroupOf.1 ha)
  have hcard : Nat.card (E.subgroupOf L) = q ^ r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv).trans hEc
  exact CFSG.HardMathSupport.Solomon.Coordinator.i1020_le_glaTwoLocalRank hq hS' hSne' hES' hE' hcard

theorem rank_add_one_le {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G} {X : Subgroup G} (hL : GLAPComponent p X L)
    (hxL : L ≤ Subgroup.centralizer ({x} : Set G)) (hxp : x ^ p = 1) (hx1 : x ≠ 1) (hxn : x ∉ L) :
    GLATwoLocalRank p ↥L + 1 ≤ GLATwoLocalRank p ↥(Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : 2 ∣ Nat.card ↥L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥L)]
    exact Dvd.dvd.mul_right (cor112_two_dvd_card_of_quasisimple
      (isQuasisimple_pQuot_of_glaPComponent hp hL)) _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hg
    exact absurd hg (by norm_num)
  obtain ⟨T₀, hT₀, hT₀2, E₀, hE₀N, hE₀a, hE₀c⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.exists_twoLocal_attaining_GLATwoLocalRank hp
      ⟨Subgroup.zpowers g, fun h => hg1 (Subgroup.zpowers_eq_bot.1 h),
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])⟩
  obtain ⟨hT0, hT2, hTL, hEL, hEN, hEa, hEc'⟩ := cor112_transport T₀ E₀ hT₀ hT₀2 hE₀N hE₀a
  have hinf := cor112_inf_zpowers_eq_bot hp hxp hx1 hxn hEL
  have hxcomm : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hxL hl)).symm
  have hxE : ∀ e ∈ E₀.map L.subtype, x * e = e * x := fun e he => hxcomm e (hEL he)
  have hxT : ∀ t ∈ T₀.map L.subtype, x * t = t * x := fun t ht => hxcomm t (hTL ht)
  have hxNE : x ∈ Subgroup.normalizer ((E₀.map L.subtype : Subgroup G) : Set G) :=
    cor112_mem_normalizer_of_comm hxE
  have hxNT : x ∈ Subgroup.normalizer ((T₀.map L.subtype : Subgroup G) : Set G) :=
    cor112_mem_normalizer_of_comm hxT
  have hcard : Nat.card ((E₀.map L.subtype ⊔ Subgroup.zpowers x : Subgroup G)) =
      p ^ (GLATwoLocalRank p ↥L + 1) := by
    have h := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer
      (Subgroup.zpowers_le.2 hxNE)
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, orderOf_eq_prime hxp hx1, hEc', hE₀c,
      mul_one] at h
    rw [pow_succ]
    exact h
  have hE'a : IsElemAbelian p (E₀.map L.subtype ⊔ Subgroup.zpowers x : Subgroup G) := by
    rw [sup_comm]
    exact cor112_isElemAbelian_sup hEa hxE hxp
  have hTC : T₀.map L.subtype ≤ Subgroup.centralizer ({x} : Set G) := hTL.trans hxL
  have hE'C : E₀.map L.subtype ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (hEL.trans hxL) (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hE'N : E₀.map L.subtype ⊔ Subgroup.zpowers x ≤
      Subgroup.normalizer ((T₀.map L.subtype : Subgroup G) : Set G) :=
    sup_le hEN (Subgroup.zpowers_le.2 hxNT)
  exact le_twoLocalRank_sub hp hTC hT2 hT0 hE'C hE'N hE'a hcard

theorem comm_ne_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B L : Subgroup G} {x : G} (hess : IsEssential p B x)
    (hB : IsElemAbelian p B) (hd : IsDirectZpowersInf B x L) (hLn : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLnorm : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G)) :
    (⁅B ⊓ L, nGen (B ⊓ L) L⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨T, hTC, hT2, hBT, hTcomm, hTne⟩ :=
    exists_two_group_comm_eq hp hp2 (isPGroup_of_isElemAbelian hB) hess
  have hxL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hLn hl)).symm
  have hBdec : ∀ b ∈ B, ∃ k : ℤ, ∃ c ∈ B ⊓ L, b = x ^ k * c := fun b hb => by
    have hb' : b ∈ Subgroup.zpowers x ⊔ (B ⊓ L) := by
      rw [← hd.1]
      exact hb
    exact cor112_mem_zpowers_sup (K := B ⊓ L) (fun c hc => hxL c hc.2) hb'
  have hcomm_mem : ∀ t ∈ T, ∀ c ∈ L, ⁅t, c⁆ ∈ L := fun t ht c hc => by
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.1 (hLnorm t (hTC ht)) c).1 hc) (L.inv_mem hc)
  have hkey : ∀ t ∈ T, ∀ b ∈ B, ∃ c ∈ B ⊓ L, ⁅t, b⁆ = ⁅t, c⁆ := by
    intro t ht b hb
    obtain ⟨k, c, hc, rfl⟩ := hBdec b hb
    refine ⟨c, hc, ?_⟩
    have htx : Commute t x := Subgroup.mem_centralizer_singleton_iff.1 (hTC ht)
    have h1 : ⁅t, x ^ k⁆ = 1 := commutatorElement_eq_one_iff_commute.2 (htx.zpow_right k)
    have h2 : Commute (x ^ k) ⁅t, c⁆ :=
      (show Commute x ⁅t, c⁆ from hxL _ (hcomm_mem t ht c hc.2)).zpow_left k
    rw [commutatorElement_mul_right, h1, one_mul, h2.eq]
    simp
  have hTL : T ≤ L := by
    have h : ⁅T, B⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro t ht b hb
      obtain ⟨c, hc, he⟩ := hkey t ht b hb
      rw [he]
      exact hcomm_mem t ht c hc.2
    rw [hTcomm] at h
    exact h
  have hTBL : T ≤ ⁅T, B ⊓ L⁆ := by
    have h : ⁅T, B⁆ ≤ ⁅T, B ⊓ L⁆ := by
      rw [Subgroup.commutator_le]
      intro t ht b hb
      obtain ⟨c, hc, he⟩ := hkey t ht b hb
      rw [he]
      exact Subgroup.commutator_mem_commutator ht hc
    rw [hTcomm] at h
    exact h
  have hTn : T ≤ nGen (B ⊓ L) L := by
    unfold nGen
    exact le_iSup₂_of_le T ⟨hTL, hT2, inf_le_left.trans hBT⟩ le_rfl
  intro hbot
  have h1 : T ≤ ⁅B ⊓ L, nGen (B ⊓ L) L⁆ := by
    calc T ≤ ⁅T, B ⊓ L⁆ := hTBL
      _ = ⁅B ⊓ L, T⁆ := Subgroup.commutator_comm _ _
      _ ≤ ⁅B ⊓ L, nGen (B ⊓ L) L⁆ := Subgroup.commutator_mono_right hTn
  rw [hbot] at h1
  exact hTne (le_bot_iff.1 h1)

theorem cor112_indep {m p : ℕ} (hctx : ThmACtx G m) (hsf : StageFacts G m) (h161 : I161aAt G) {B : Subgroup G}
    {x : G} {L : Subgroup G} (hR : RQuad G m p B x L) (hns : NoSplit16 p L) : Cor112Indep G m p B x L := by
  have hH := rquad_hyp hsf hR
  have hp : p.Prime := hH.prime
  have hp2 : p ≠ 2 := hH.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hnoZ, hinner⟩ := h161 p hp hp2 L hH.isChev2 hns
  have hin : ∀ b ∈ B, InducesInnerMod p L b := hinner B hH.elem hH.idiag
  have hcyc : CycModSylow p L := hR.2.1.2
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := hH.comp.1
  have hd : IsDirectZpowersInf B x L :=
    bdecomp_of_cyc hp hp2 hH.comp hnoZ hH.elem hH.mem hH.ne_one hxL hH.norm hH.cent hin hcyc
  have hxn : x ∉ L := not_mem_of_direct hp hH.ne_one hH.mem hd
  obtain ⟨h3, h4o, h4, h5, -, -, -, -, -⟩ := hsf p hR.1
  have hc6 : S6Ctx G p := S6Ctx.of_ctx hctx hR.1 h3 h4o h4 h5
  have hlayer : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := sstarMax_layer_eq hc6 hR.2.1
  have hLnorm : ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G) := by
    intro g hg
    rw [← hlayer]
    exact mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)
  have hcomm : (⁅B ⊓ L, nGen (B ⊓ L) L⁆ : Subgroup G) ≠ ⊥ :=
    comm_ne_bot hp hp2 hR.2.1.1.1.1.2.1 hH.elem hd hxL hLnorm
  refine ⟨hd, ?_, hnoZ, hcomm⟩
  have hle : GLATwoLocalRank p ↥L ≤ m - 1 := by
    have h1 := rank_add_one_le hp hH.comp hxL (hH.elem.2 x hH.mem) hH.ne_one hxn
    have h2 := twoLocalRank_le_top hp (Subgroup.centralizer ({x} : Set G))
    rw [hH.mu.2.1] at h2
    omega
  have hex : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ⊓ L ≤ Subgroup.normalizer (T : Set G) ∧ T ≠ ⊥ := by
    by_contra hno
    push_neg at hno
    apply hcomm
    have : nGen (B ⊓ L) L = ⊥ := by
      unfold nGen
      refine iSup₂_eq_bot.2 ?_
      intro T hT
      by_contra hne
      exact hne (hno T hT.1 hT.2.1 hT.2.2)
    rw [this]
    exact Subgroup.commutator_bot_right _
  obtain ⟨T, hTL, hT2, hTn, hTne⟩ := hex
  have hcard : Nat.card ↥(B ⊓ L) = p ^ (m - 1) := card_inf_eq hH hd
  have hge : m - 1 ≤ GLATwoLocalRank p ↥L :=
    le_twoLocalRank_sub hp hTL hT2 hTne inf_le_right hTn (isElemAbelian_mono hH.elem inf_le_left) hcard
  exact le_antisymm hle hge

end S11

end CFSG.LocalAnalysis.GLTheoremA
