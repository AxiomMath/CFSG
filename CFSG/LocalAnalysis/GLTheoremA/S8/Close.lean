module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma8910
public import CFSG.LocalAnalysis.GLTheoremA.S8.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S8.ExtraSpec
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Common
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

namespace S8

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem SporCfg.R_ne_bot {x : G} {L : Subgroup G} {row : Row} (c : SporCfg G p x L row) : c.R ≠ ⊥ := by
  intro h
  have h1 : Nat.card c.R = 1 := by rw [h]; exact Subgroup.card_bot
  have h2 := c.hR.2
  have h3 : 0 < row.rexp := by cases row <;> simp [Row.rexp]
  rw [h1] at h2
  have : (2 : ℕ) ^ row.rexp ≥ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem exists_M {x : G} {L : Subgroup G} {row : Row} (c : SporCfg G p x L row) :
    ∃ M : Subgroup G, GLAIsMaxTwoLocal M ∧ Subgroup.normalizer (c.R : Set G) ≤ M :=
  exists_maxTwoLocal_ge ⟨c.R, c.R_ne_bot, c.hR.1.1, rfl⟩

theorem SporCfg.Bs_le_normalizer {x : G} {L : Subgroup G} {row : Row} (c : SporCfg G p x L row) :
    c.Bs ≤ Subgroup.normalizer (c.R : Set G) := c.hBsN.trans inf_le_right

theorem cfg_three (hc : S8Ctx G 3) (hin : Inputs8910 G 3) {x : G} {L : Subgroup G} {row : Row}
    (hx : orderOf x = 3) (hL : GLAPComponent 3 (cx x) L) (hrow : RowL row 3 L)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 (cx x)))) (c : SporCfg G 3 x L row) : False := by
  obtain ⟨M, hM, hNM⟩ := exists_M c
  obtain ⟨-, hS, -⟩ := cfg_extraspecial hc hin hx hL hrow hodd c hM hNM
  have hBsM : c.Bs ≤ M := c.Bs_le_normalizer.trans hNM
  exact hc.ctx.noGF2 rfl ⟨M, hM, extraspec_symplectic hS, c.Bs, c.hBs, hBsM⟩

theorem inf_cx_eq_cfgN {M R : Subgroup G} {x : G} (hNM : Subgroup.normalizer (R : Set G) ≤ M)
    (hR : R = pCoreOf 2 M ⊓ cx x) : M ⊓ cx x = cfgN x R := by
  apply le_antisymm
  · intro g hg
    have h1 : M ⊓ cx x ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      inf_le_left.trans (le_normalizer_pCoreOf 2 M)
    have h2 : M ⊓ cx x ≤ Subgroup.normalizer (cx x : Set G) :=
      inf_le_right.trans Subgroup.le_normalizer
    have h3 := le_normalizer_inf h1 h2
    rw [← hR] at h3
    exact ⟨hg.2, h3 hg⟩
  · intro g hg
    exact ⟨hNM hg.2, hg.1⟩

theorem isTwoLocal_ne_top (hsimple : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a)
    {M : Subgroup G} (hM : IsTwoLocal M) : M ≠ ⊤ := by
  obtain ⟨P, hP, hP2, rfl⟩ := hM
  intro htop
  have hPn : (P : Subgroup G).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (P : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
  rcases hsimple.eq_bot_or_eq_top_of_normal P with h | h
  · exact hP h
  · subst h
    have hG2 : IsPGroup 2 G := by
      rw [IsPGroup.iff_orderOf]
      intro g
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨g, Subgroup.mem_top g⟩
      exact ⟨k, by simpa using hk⟩
    haveI : Nontrivial G := hsimple.toNontrivial
    haveI : Nontrivial (Subgroup.center G) := hG2.center_nontrivial
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
    · obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center G)
      apply hz
      have : (z : G) ∈ (⊥ : Subgroup G) := hc ▸ z.2
      exact Subtype.ext (by simpa using this)
    · obtain ⟨a, b, hab⟩ := hna
      apply hab
      have : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.1 this b).symm

theorem exists_noncomm_of_component {H : Type} [Group H] [Finite H] (hp : p.Prime) {X J : Subgroup H}
    (hJ : GLAPComponent p X J) : ∃ a b : ↥J, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hJ
  obtain ⟨a, b, hab⟩ := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hq
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨a'', rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hcomm a'' b'']

theorem five_transfer_component {M L N : Subgroup G} {x : G} (hxM : x ∈ M) (hx : orderOf x = 5)
    (hLn : cx x ≤ Subgroup.normalizer (L : Set G)) (hMN : M ⊓ cx x = N)
    (hNL : ∃ J₀ : Subgroup G, GLAPComponent 5 (L ⊓ N) J₀ ∧
      catalogIs (PSimple 5 J₀) (sporIs .Co1)) :
    orderOf (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : ↥M ⧸ GLAPPrimeCore 5 ↥M) = 5 ∧
    ∃ J' : Subgroup (↥M ⧸ GLAPPrimeCore 5 ↥M),
      GLAPComponent 5 (cx (QuotientGroup.mk (⟨x, hxM⟩ : ↥M) : ↥M ⧸ GLAPPrimeCore 5 ↥M)) J' ∧
        catalogIs (PSimple 5 J') (sporIs .Co1) := by
  have hp5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp5⟩
  set x' : ↥M := ⟨x, hxM⟩ with hx'
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx'5 : x' ^ 5 = 1 := Subtype.ext (by simpa using hx5)
  have hcop : ¬ 5 ∣ Nat.card (GLAPPrimeCore 5 ↥M) :=
    (Nat.Prime.coprime_iff_not_dvd hp5).1 CFSG.pPrimeCore_coprime_card
  have hker : ¬ 5 ∣ Nat.card (QuotientGroup.mk' (GLAPPrimeCore 5 ↥M)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hcop
  have hy : IsPGroup 5 (Subgroup.zpowers x') := isPGroup_zpowers_of_pow_eq_one hx'5
  refine ⟨?_, ?_⟩
  · apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hx'5, QuotientGroup.mk_one]
    · intro h
      rw [QuotientGroup.eq_one_iff] at h
      have h5 : orderOf (⟨x', h⟩ : ↥(GLAPPrimeCore 5 ↥M)) = 5 := by
        rw [Subgroup.orderOf_mk, hx', Subgroup.orderOf_mk, hx]
      have h6 := orderOf_dvd_natCard (⟨x', h⟩ : ↥(GLAPPrimeCore 5 ↥M))
      rw [h5] at h6
      exact hcop h6
  · obtain ⟨J₀, hJ₀, hco⟩ := hNL
    have hNM : N ≤ M := hMN ▸ inf_le_left
    have hNx : N ≤ cx x := hMN ▸ inf_le_right
    have hn : ((L ⊓ N).subgroupOf N).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      exact le_normalizer_inf (hNx.trans hLn) Subgroup.le_normalizer
    have h1 : GLAPComponent 5 N J₀ :=
      CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.glaPComponent_of_normal_sub hp5 inf_le_right hn hJ₀
    have h2 := glaPComponent_subgroupOf hp5 hNM h1
    have h3 : N.subgroupOf M = (⊤ : Subgroup ↥M) ⊓ Subgroup.centralizer ({x'} : Set ↥M) := by
      rw [← hMN]
      ext z
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, hx', Subtype.ext_iff]
    rw [h3] at h2
    have h4 := glaPComponent_map_of_ker_le hp5 hker (K := ⊤) (by simp) hy h2
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _), top_inf_eq] at h4
    refine ⟨(J₀.subgroupOf M).map (QuotientGroup.mk' (GLAPPrimeCore 5 ↥M)), h4, ?_⟩
    obtain ⟨i, hi, ⟨f⟩⟩ := hco
    have hJM : J₀ ≤ M := (hJ₀.1.trans inf_le_right).trans hNM
    obtain ⟨e1⟩ := nonempty_pQuot_equiv_subgroupOf 5 hJM
    obtain ⟨e2⟩ := nonempty_pQuot_equiv_map hp5 hker (J₀.subgroupOf M)
    exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ (e1.symm.trans e2) (Subgroup.map_center_eq _)).symm.trans f⟩⟩

theorem five_transfer_res {H : Type} [Group H] [Finite H] {y : H} (hy : orderOf y = 5)
    {J' : Subgroup H} (hJ' : GLAPComponent 5 (cx y) J') :
    ∃ (hyY : y ∈ oPrimeRes 5 H) (J'' : Subgroup ↥(oPrimeRes 5 H)),
      orderOf (⟨y, hyY⟩ : ↥(oPrimeRes 5 H)) = 5 ∧
      GLAPComponent 5 (cx (⟨y, hyY⟩ : ↥(oPrimeRes 5 H))) J'' ∧
      Nonempty (PSimple 5 J'' ≃* PSimple 5 J') := by
  have hp5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp5⟩
  set Y := oPrimeRes 5 H with hY
  have hYn : Y.Normal := Subgroup.normalClosure_normal
  have hy5 : y ^ 5 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hyY : y ∈ Y := Subgroup.subset_normalClosure ⟨1, by simpa using hy5⟩
  have hidx : Nat.Coprime 5 (Y.subgroupOf ⊤).index := by
    obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := H)
    have hPY : (P : Subgroup H) ≤ Y := by
      intro g hg
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 P.isPGroup') ⟨g, hg⟩
      refine Subgroup.subset_normalClosure ⟨k, ?_⟩
      have := pow_orderOf_eq_one (⟨g, hg⟩ : ↥(P : Subgroup H))
      rw [hk] at this
      simpa using congrArg Subtype.val this
    have h1 : Y.index ∣ (P : Subgroup H).index := Subgroup.index_dvd_of_le hPY
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact Nat.Coprime.coprime_dvd_right h1
      ((Nat.Prime.coprime_iff_not_dvd hp5).2 (Sylow.not_dvd_index P))
  haveI : (Y.subgroupOf ⊤).Normal := hYn.subgroupOf ⊤
  have hJY : J' ≤ Y := CFSG.HardMathSupport.Solomon.Coordinator.i183_le_of_coprime_index hp5 hJ' le_top hidx
  refine ⟨hyY, J'.subgroupOf Y, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hy
  · have h1 : GLAPComponent 5 (cx y ⊓ Y) J' :=
      glaPComponent_of_le hp5 hJ' (le_inf hJ'.1 hJY) inf_le_left
    have h2 := glaPComponent_subgroupOf hp5 (inf_le_right : cx y ⊓ Y ≤ Y) h1
    have h3 : (cx y ⊓ Y).subgroupOf Y = cx (⟨y, hyY⟩ : ↥Y) := by
      ext z
      simp [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
    rw [h3] at h2
    exact h2
  · obtain ⟨g⟩ := nonempty_pQuot_equiv_subgroupOf 5 hJY
    exact ⟨QuotientGroup.congr _ _ g (Subgroup.map_center_eq g)⟩

theorem cfg_five (hc : S8Ctx G 5) (hin : Inputs8910 G 5) (hTim : TimmesfeldAt) (hNo5 : No5PumpupAt)
    {x : G} {L : Subgroup G} (hx : orderOf x = 5) (hL : GLAPComponent 5 (cx x) L)
    (hLn : cx x ≤ Subgroup.normalizer (L : Set G))
    (hrow : RowL .m5 5 L) (hodd : Odd (Nat.card (GLAPPrimeCoreOf 5 (cx x))))
    (c : SporCfg G 5 x L .m5) : False := by
  obtain ⟨M, hM, hNM⟩ := exists_M c
  obtain ⟨hRS, hS, hRSx⟩ := cfg_extraspecial hc hin hx hL hrow hodd c hM hNM
  have hxM : x ∈ M := (c.Bs_le_normalizer.trans hNM) (c.hD.1 c.hD.2.2.2)
  have hcard : 2 ^ 25 ≤ Nat.card ↥(pCoreOf 2 M) := by
    have h1 : Nat.card c.R ≤ Nat.card ↥(pCoreOf 2 M) := Subgroup.card_le_of_le hRS
    have h2 := c.hR.2
    simp only [Row.rexp] at h2
    omega
  have hsimple := hTim G hc.ctx.simple hc.ctx.nonabelian hc.ctx.charTwo M hM hS hcard ⟨x, hxM, hx⟩
  have hMN : M ⊓ cx x = cfgN x c.R := inf_cx_eq_cfgN hNM hRSx
  obtain ⟨hy5, J', hJ', hJt⟩ := five_transfer_component hxM hx hLn hMN (c.hNL rfl)
  obtain ⟨hyY, J'', hy'', hJ'', ⟨e⟩⟩ := five_transfer_res hy5 hJ'
  have hMne : M ≠ ⊤ := isTwoLocal_ne_top hc.ctx.simple hc.ctx.nonabelian hM.1
  have hKM : CFSG.Open.IsKGroup ↥M := isKGroup_of_isKProper hc.ctx.kProper hMne
  have hKY : CFSG.Open.IsKGroup ↥(oPrimeRes 5 (↥M ⧸ GLAPPrimeCore 5 ↥M)) :=
    CFSG.Open.IsKGroup.subgroup (CFSG.Open.IsKGroup.quotient hKM _) _
  have hnonab : ∃ a b : ↥(oPrimeRes 5 (↥M ⧸ GLAPPrimeCore 5 ↥M)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_component (by norm_num : Nat.Prime 5) hJ''
    exact ⟨a, b, fun h => hab (Subtype.ext (by simpa using h))⟩
  obtain ⟨i, hi, ⟨f⟩⟩ := hJt
  exact hNo5 _ hsimple hnonab hKY _ hy'' J'' hJ'' ⟨i, hi, ⟨e.trans f⟩⟩

end S8

end CFSG.LocalAnalysis.GLTheoremA

