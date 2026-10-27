module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13a
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)

namespace Lemma135

@[expose] def cent {G : Type} [Group G] (M D L : Subgroup G) :
    Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M) :=
  Subgroup.centralizer ((barX 3 M (Lstarsub D L) : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
    Set (↥M ⧸ GLAPPrimeCore 3 ↥M))

@[expose] def CentThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L), cent M D L ≠ ⊥ → 3 ∣ Nat.card (cent M D L)

@[expose] def NineCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ) {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L), cent M D L = ⊥ →
    ∀ P : Subgroup G, IsSylowIn 3 M P → B ⊔ D ≤ P →
      ∀ X : Subgroup G, X ≤ P → 2 ≤ CFSG.Open.pRank 3 X →
        3 ≤ CFSG.Open.pRank 3 (X ⊔ (P ⊓ Subgroup.centralizer (X : Set G))) →
          Subgroup.normalizer (X : Set G) ≤ M

theorem cex134_p_eq_three (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement)
    {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m p B M E A D T L) : p = 3 := by
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hp2 : p ≠ 2 := hS.ne_two
  have hD : IsEkIn p 2 A D := h.hD
  have hDA : D ≤ A := hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hyp : Prop95Hyp p M D :=
    { twoLocal := h.pre.1.1
      le := hDM
      plane := ⟨hD.2.1, hD.2.2⟩
      clause_a := fun d hd hd1 =>
        (pCoreOf_two_le_glaPPrimeCoreOf hS.prime hp2 _).trans (h111 h.toSec11 (hDA hd) hd1)
      clause_b := fun d hd hd1 => by
        by_contra hc
        exact h121 (⟨h.toSec11, ⟨hDA hd, hd1⟩, hc⟩ : Cex121 G m p B M E A d)
      clause_c := h.hT1.trans (h.hT2.trans (gammaStar_le_gammaD p D)) }
  have hP := hP95 G m p hS M D hyp
  obtain ⟨hLc, hnc⟩ := hcomp h.toSec13 h.hL
  have hγ : Prop95Gamma p M D L := by
    rcases (hP.2.2 L hLc).2 with hc | ⟨-, ha | hb | hg⟩
    · exact absurd ((barX_mono_of_le p (gammaStar_le_gammaD p D)).trans hc) hnc
    · exact absurd ha (fun ha => h.notAB (Or.inl ha))
    · exact absurd hb (fun hb => h.notAB (Or.inr hb))
    · exact hg
  exact hγ.1

theorem gLBConj_lstar_le {G : Type} [Group G] [Finite G] {D L : Subgroup G} {y : G} (hy : y ∈ D) :
    GLBConj y (Lstarsub D L) ≤ Lstarsub D L := by
  unfold Lstarsub
  rw [gLBConj_iSup_eq]
  refine iSup_le fun d => ?_
  rw [gLBConj_iSup_eq]
  refine iSup_le fun hd => ?_
  rw [gLBConj_gLBConj]
  exact le_iSup₂_of_le (f := fun d' (_ : d' ∈ D) => GLBConj d' L) (d * y) (mul_mem hd hy) le_rfl

theorem gLBConj_lstar_le_of_normal {G : Type} [Group G] [Finite G] {D L B : Subgroup G}
    (hB : ∀ d ∈ D, B ≤ Subgroup.normalizer ((GLBConj d L : Subgroup G) : Set G)) {b : G}
    (hb : b ∈ B) : GLBConj b (Lstarsub D L) ≤ Lstarsub D L := by
  unfold Lstarsub
  rw [gLBConj_iSup_eq]
  refine iSup_le fun d => ?_
  rw [gLBConj_iSup_eq]
  refine iSup_le fun hd => ?_
  rw [gLBConj_eq_of_mem_normalizer (hB d hd hb)]
  exact le_iSup₂_of_le (f := fun d' (_ : d' ∈ D) => GLBConj d' L) d hd le_rfl

theorem mem_normalizer_of_gLBConj_le {G : Type} [Group G] [Finite G] {S : Subgroup G} {y : G}
    (h1 : GLBConj y S ≤ S) (h2 : GLBConj y⁻¹ S ≤ S) :
    y ∈ Subgroup.normalizer (S : Set G) := by
  have heq : GLBConj y S = S := by
    refine le_antisymm h1 ?_
    have := gLBConj_mono y h2
    rwa [gLBConj_gLBConj_inv] at this
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← mem_gLBConj, heq]

theorem le_normalizer_lstar {G : Type} [Group G] [Finite G] {D L : Subgroup G} :
    D ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) := fun d hd =>
  mem_normalizer_of_gLBConj_le (gLBConj_lstar_le hd) (gLBConj_lstar_le (D.inv_mem hd))

theorem le_normalizer_lstar_of_normal {G : Type} [Group G] [Finite G] {D L B : Subgroup G}
    (hB : ∀ d ∈ D, B ≤ Subgroup.normalizer ((GLBConj d L : Subgroup G) : Set G)) :
    B ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) := fun b hb =>
  mem_normalizer_of_gLBConj_le (gLBConj_lstar_le_of_normal hB hb)
    (gLBConj_lstar_le_of_normal hB (B.inv_mem hb))

theorem barX_lstar_normalizers {G : Type} [Group G] {M D L B : Subgroup G}
    (hBn : B ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G))
    (hDn : D ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G)) :
    barX 3 M B ≤ Subgroup.normalizer ((barX 3 M (Lstarsub D L) :
        Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ∧
      barX 3 M D ≤ Subgroup.normalizer ((barX 3 M (Lstarsub D L) :
        Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
  ⟨barX_le_normalizer hBn, barX_le_normalizer hDn⟩

theorem iof_le_istar' {G : Type} [Group G] [Finite G] (p : ℕ) (M D : Subgroup G) :
    Iof p M D ≤ Istar p M D := by
  unfold Istar
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) 1 M.one_mem
    (le_of_eq (gLBConj_one _).symm)

theorem glaPComponent_istar_conj {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M D L : Subgroup G} (hLc : GLAPComponent p M L) (hLI : L ≤ Istar p M D) {d : G} (hd : d ∈ M) :
    GLAPComponent p (Istar p M D) (GLBConj d L) := by
  have h1 : GLAPComponent p (Istar p M D) L := glaPComponent_of_le hp hLc hLI (istar_le_M p M D)
  have h2 := glaPComponent_gLBConj h1 d
  rwa [istar_conj_eq p hd] at h2

theorem gLBConj_normalizer_eq {G : Type} [Group G] (g : G) (O : Subgroup G) :
    GLBConj g (Subgroup.normalizer (O : Set G)) =
      Subgroup.normalizer ((GLBConj g O : Subgroup G) : Set G) := by
  ext x
  rw [mem_gLBConj, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx y
    rw [mem_gLBConj, mem_gLBConj, hx (g * y * g⁻¹)]
    have e : g * x * g⁻¹ * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * (x * y * x⁻¹) * g⁻¹ := by
      group
    rw [e]
  · intro hx y
    have h1 := hx (g⁻¹ * y * g)
    rw [mem_gLBConj, mem_gLBConj] at h1
    have e1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have e2 : g * (x * (g⁻¹ * y * g) * x⁻¹) * g⁻¹ = g * x * g⁻¹ * y * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1

theorem isTwoLocal_gLBConj {G : Type} [Group G] {H : Subgroup G} (hH : CFSG.Open.IsTwoLocal H)
    (g : G) : CFSG.Open.IsTwoLocal (GLBConj g H) := by
  obtain ⟨O, hO1, hO2, rfl⟩ := hH
  refine ⟨GLBConj g O, ?_, ?_, ?_⟩
  · intro h
    apply hO1
    have h' : GLBConj g⁻¹ (GLBConj g O) = GLBConj g⁻¹ ⊥ := by rw [h]
    rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h'
    rw [h']
    unfold GLBConj
    simp
  · have e := Subgroup.equivMapOfInjective O (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective
    exact hO2.of_equiv e
  · rw [gLBConj_normalizer_eq]

theorem sylow_of_normalizer_le {G : Type} [Group G] [Finite G] {M P : Subgroup G}
    (hPM : IsSylowIn 3 M P) (hN : Subgroup.normalizer (P : Set G) ≤ M) :
    ∀ S : Subgroup G, IsPGroup 3 S → P ≤ S → S = P := by
  intro S hS hPS
  have hPN : P ≤ Subgroup.normalizer (P : Set G) := Subgroup.le_normalizer
  have hSN : S ⊓ Subgroup.normalizer (P : Set G) = P :=
    hPM.2.2 (S ⊓ Subgroup.normalizer (P : Set G)) (inf_le_right.trans hN)
      (hS.to_le (inf_le_left : S ⊓ Subgroup.normalizer (P : Set G) ≤ S)) (le_inf hPS hPN)
  by_contra hne
  have hlt : P.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hne (le_antisymm h hPS)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := S) (P.subgroupOf S)
    (by exact hlt)
  obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hnc
  have hfwd : ∀ y ∈ P, (x : G) * y * (x : G)⁻¹ ∈ P := by
    intro y hy
    have hyS : y ∈ S := hPS hy
    have hy' : (⟨y, hyS⟩ : S) ∈ P.subgroupOf S := Subgroup.mem_subgroupOf.2 hy
    have := (Subgroup.mem_normalizer_iff.1 hx1 ⟨y, hyS⟩).1 hy'
    exact Subgroup.mem_subgroupOf.1 this
  have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hfwd y hy
    · intro hy
      have hzS : (x : G) * y * (x : G)⁻¹ ∈ S := hPS hy
      have hw' : (⟨(x : G) * y * (x : G)⁻¹, hzS⟩ : S) ∈ P.subgroupOf S :=
        Subgroup.mem_subgroupOf.2 hy
      have hx'1 : (x⁻¹ : S) ∈ Subgroup.normalizer ((P.subgroupOf S : Subgroup S) : Set S) :=
        inv_mem hx1
      have key := Subgroup.mem_subgroupOf.1
        ((Subgroup.mem_normalizer_iff.1 hx'1 ⟨(x : G) * y * (x : G)⁻¹, hzS⟩).1 hw')
      have e : (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) = y := by group
      simpa [e] using key
  have hxS : (x : G) ∈ S ⊓ Subgroup.normalizer (P : Set G) := ⟨x.2, hxN⟩
  rw [hSN] at hxS
  exact hx2 (Subgroup.mem_subgroupOf.2 hxS)

theorem glaWeakCoreLocal_of_core {G : Type} [Group G] [Finite G] {m : ℕ} {B M P : Subgroup G}
    (hS : GLStanding G m 3) (hB : IsBOneMax 3 B) (hM2 : CFSG.Open.IsTwoLocal M)
    (hBP : B ≤ P) (hPM : IsSylowIn 3 M P)
    (hcore : ∀ X : Subgroup G, X ≤ P → 2 ≤ CFSG.Open.pRank 3 X →
      3 ≤ CFSG.Open.pRank 3 (X ⊔ (P ⊓ Subgroup.centralizer (X : Set G))) →
        Subgroup.normalizer (X : Set G) ≤ M) :
    GLAWeakCoreLocal G 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBcard : Nat.card B = 3 ^ m := by
    have h := hB.1.2.1
    rw [hS.rank_eq] at h
    exact h
  have hBEA : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hm4 : 4 ≤ m := hS.four_le
  have hTop : m ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hBEA hBcard
  have hNP : Subgroup.normalizer (P : Set G) ≤ M := by
    refine hcore P le_rfl ?_ ?_
    · have := CFSG.SectionRank.le_pRank (by norm_num) hBP hBEA hBcard
      omega
    · rw [sup_eq_left.2 inf_le_left]
      have := CFSG.SectionRank.le_pRank (by norm_num) hBP hBEA hBcard
      omega
  have hWM : GLAWeakCore 3 P ≤ M := by
    show CFSG.Open.rankThreeAschCore 2 3 P ≤ M
    unfold CFSG.Open.rankThreeAschCore
    apply sSup_le
    rintro N ⟨X, hXP, h2, h3, rfl⟩
    exact hcore X hXP h2 h3
  have hPG := sylow_of_normalizer_le hPM hNP
  let PS : Sylow 3 G := ⟨P, hPM.2.1, fun {Q} hQ hPQ => hPG Q hQ hPQ⟩
  show 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) ∧
    ∀ S : Sylow 3 G, ∃ H : Subgroup G, CFSG.Open.IsTwoLocal H ∧ GLAWeakCore 3 (S : Subgroup G) ≤ H
  refine ⟨by omega, fun S => ?_⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G PS S
  have hSP : (S : Subgroup G) = GLBConj g⁻¹ P := by
    rw [← hg]
    unfold GLBConj
    rw [inv_inv]
    rfl
  refine ⟨GLBConj g⁻¹ M, isTwoLocal_gLBConj hM2 g⁻¹, ?_⟩
  rw [hSP, CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs.glaWeakCore_gLBConj
    Nat.prime_three P g⁻¹]
  exact gLBConj_mono g⁻¹ hWM

theorem sylow_above3 {G : Type} [Group G] [Finite G] {M P : Subgroup G} (hPM : P ≤ M)
    (hP : IsPGroup 3 ↥P) : ∃ R : Subgroup G, IsSylowIn 3 M R ∧ P ≤ R := by
  obtain ⟨R, hPR, hRmax⟩ :=
    (Set.toFinite {R : Subgroup G | R ≤ M ∧ IsPGroup 3 ↥R}).exists_le_maximal ⟨hPM, hP⟩
  exact ⟨R, ⟨hRmax.1.1, hRmax.1.2, fun R' hR'M hR'p hRR' =>
    le_antisymm (hRmax.2 ⟨hR'M, hR'p⟩ hRR') hRR'⟩, hPR⟩

theorem exists_fixed_three_part {Y : Type} [Group Y] [Finite Y] (K Hh : Subgroup Y) [K.Normal]
    (hK : K ⊔ Hh = ⊤) (hH : IsPGroup 3 ↥Hh) (h3 : 3 ∣ Nat.card K) :
    ∃ x ∈ K, x ≠ 1 ∧ x ^ 3 = 1 ∧ ∀ h ∈ Hh, h * x = x * h := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  have hHQ' : Hh ≤ (Q : Subgroup Y) := hHQ
  have hQK : (Q : Subgroup Y) ⊓ K ≠ ⊥ := by
    intro hbot
    have hsup : (Q : Subgroup Y) ⊔ K = ⊤ := by
      rw [eq_top_iff, ← hK]
      exact sup_le le_sup_right (hHQ'.trans le_sup_left)
    have hcardQ : Nat.card (Q : Subgroup Y) = K.index := by
      let f : (Q : Subgroup Y) →* Y ⧸ K := (QuotientGroup.mk' K).comp (Q : Subgroup Y).subtype
      have hinj : Function.Injective f := by
        rw [injective_iff_map_eq_one]
        intro q hq
        have hq' : (q : Y) ∈ K := (QuotientGroup.eq_one_iff _).1 hq
        have hmem : (q : Y) ∈ (Q : Subgroup Y) ⊓ K := ⟨q.2, hq'⟩
        rw [hbot] at hmem
        exact Subtype.ext (by simpa using hmem)
      have hsurj : Function.Surjective f := by
        intro y
        obtain ⟨y0, rfl⟩ := QuotientGroup.mk'_surjective K y
        have hy0 : y0 ∈ (Q : Subgroup Y) ⊔ K := by rw [hsup]; exact Subgroup.mem_top y0
        obtain ⟨q, hq, z, hz, hzq⟩ := Subgroup.mem_sup_of_normal_right.1 hy0
        refine ⟨⟨q, hq⟩, ?_⟩
        simp only [f, MonoidHom.comp_apply, MonoidHom.coe_comp, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply]
        rw [← hzq, QuotientGroup.eq]
        have e : q⁻¹ * (q * z) = z := by group
        rw [e]
        exact hz
      have e := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
      rw [e]
      rfl
    have h1 : (Q : Subgroup Y).index * Nat.card (Q : Subgroup Y) = Nat.card Y :=
      Subgroup.index_mul_card _
    have h2 : Nat.card K * K.index = Nat.card Y := Subgroup.card_mul_index K
    have hnd : ¬ 3 ∣ (Q : Subgroup Y).index := Sylow.not_dvd_index Q
    have hidx : (Q : Subgroup Y).index = Nat.card K := by
      have hpos : 0 < K.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
      rw [hcardQ] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    exact hnd (hidx ▸ h3)
  have hRp : IsPGroup 3 ↥((Q : Subgroup Y) ⊓ K) := Q.isPGroup'.to_le inf_le_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hRp
  have hRcard : 3 ∣ Nat.card ↥((Q : Subgroup Y) ⊓ K) := by
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact hQK ((Subgroup.eq_bot_iff_card _).2 hn)
    rw [hn]
    exact dvd_pow_self 3 hn0
  have hHnorm : ∀ (h : ↥Hh) (r : ↥((Q : Subgroup Y) ⊓ K)),
      (h : Y) * (r : Y) * (h : Y)⁻¹ ∈ (Q : Subgroup Y) ⊓ K := by
    intro h r
    refine ⟨Q.mul_mem (Q.mul_mem (hHQ' h.2) r.2.1) (Q.inv_mem (hHQ' h.2)), ?_⟩
    exact Subgroup.Normal.conj_mem inferInstance (r : Y) r.2.2 (h : Y)
  letI : MulAction ↥Hh ↥((Q : Subgroup Y) ⊓ K) :=
    { smul := fun h r => ⟨(h : Y) * (r : Y) * (h : Y)⁻¹, hHnorm h r⟩
      one_smul := fun r => Subtype.ext (by
        show ((1 : ↥Hh) : Y) * (r : Y) * ((1 : ↥Hh) : Y)⁻¹ = r
        simp)
      mul_smul := fun h₁ h₂ r => Subtype.ext (by
        show ((h₁ * h₂ : ↥Hh) : Y) * (r : Y) * ((h₁ * h₂ : ↥Hh) : Y)⁻¹ =
          (h₁ : Y) * ((h₂ : Y) * (r : Y) * (h₂ : Y)⁻¹) * (h₁ : Y)⁻¹
        simp [mul_assoc, mul_inv_rev]) }
  have hmod := hH.card_modEq_card_fixedPoints ↥((Q : Subgroup Y) ⊓ K)
  have hfix3 : 3 ∣ Nat.card (MulAction.fixedPoints ↥Hh ↥((Q : Subgroup Y) ⊓ K)) :=
    (Nat.modEq_zero_iff_dvd).1 (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).2 hRcard))
  let oneFix : (MulAction.fixedPoints ↥Hh ↥((Q : Subgroup Y) ⊓ K)) :=
    ⟨1, fun h => Subtype.ext (by
      show (h : Y) * 1 * (h : Y)⁻¹ = 1
      simp)⟩
  haveI : Nonempty (MulAction.fixedPoints ↥Hh ↥((Q : Subgroup Y) ⊓ K)) := ⟨oneFix⟩
  have hFpos : 0 < Nat.card (MulAction.fixedPoints ↥Hh ↥((Q : Subgroup Y) ⊓ K)) :=
    Nat.card_pos
  have hFnt : 1 < Nat.card (MulAction.fixedPoints ↥Hh ↥((Q : Subgroup Y) ⊓ K)) := by
    have := Nat.le_of_dvd hFpos hfix3
    omega
  haveI := (Finite.one_lt_card_iff_nontrivial).1 hFnt
  obtain ⟨x, hx1⟩ := exists_ne oneFix
  have hxK : (x.1 : Y) ∈ K := x.1.2.2
  have hxc : ∀ h ∈ Hh, h * (x.1 : Y) = (x.1 : Y) * h := by
    intro h hh
    have key := MulAction.mem_fixedPoints.1 x.2 ⟨h, hh⟩
    have key' := congrArg (fun r : ↥((Q : Subgroup Y) ⊓ K) => (r : Y)) key
    change (h : Y) * (x.1 : Y) * (h : Y)⁻¹ = (x.1 : Y) at key'
    exact mul_inv_eq_iff_eq_mul.1 key'
  have hxne : (x.1 : Y) ≠ 1 := by
    intro h0
    apply hx1
    exact Subtype.ext (Subtype.ext h0)
  have hord : orderOf (x.1 : Y) ∣ 3 ^ n := by
    rw [← hn, Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord
  have hj1 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hxne hj
  have h3ord : 3 ∣ orderOf (x.1 : Y) := by
    rw [hj]
    exact dvd_pow_self 3 hj1
  have hxpos : orderOf (x.1 : Y) ≠ 0 := by
    rw [hj]
    exact pow_ne_zero _ (by norm_num)
  have hyord : orderOf ((x.1 : Y) ^ (orderOf (x.1 : Y) / 3)) = 3 :=
    orderOf_pow_orderOf_div hxpos h3ord
  refine ⟨(x.1 : Y) ^ (orderOf (x.1 : Y) / 3), K.pow_mem hxK _, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  · have hp := pow_orderOf_eq_one ((x.1 : Y) ^ (orderOf (x.1 : Y) / 3))
    rwa [hyord] at hp
  · intro h hh
    exact (Commute.pow_right (show Commute h (x.1 : Y) from hxc h hh) _).eq

theorem mem_of_centralizes_rank {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y} {m : ℕ}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ m)
    (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ m) {z : Y} (hz3 : z ^ 3 = 1)
    (hzE : ∀ e ∈ E, e * z = z * e) : z ∈ E := by
  by_contra hzE'
  have hzk : ∀ k : ℕ, z ^ k ∈ E → k % 3 = 0 := by
    intro k hk
    rw [pow_eq_pow_mod k hz3] at hk
    have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k % 3
    · rfl
    · exfalso
      apply hzE'
      simpa using hk
    · exfalso
      apply hzE'
      have e4 : (z ^ 2) ^ 2 = z := by
        rw [← pow_mul, pow_eq_pow_mod (2 * 2) hz3]
        norm_num
      have h4 : z ^ 2 * z ^ 2 ∈ E := E.mul_mem hk hk
      rwa [← pow_two, e4] at h4
  let A := E × Multiplicative (ZMod 3)
  let f : A →* Y :=
    { toFun := fun a => (a.1 : Y) * z ^ (Multiplicative.toAdd a.2).val
      map_one' := by simp
      map_mul' := by
        intro a b
        have hb : ∀ n : ℕ, (b.1 : Y) * z ^ n = z ^ n * (b.1 : Y) :=
          fun n => (Commute.pow_right (hzE _ b.1.2) n).eq
        show ((a.1 * b.1 : E) : Y) * z ^ (Multiplicative.toAdd (a.2 * b.2)).val =
          ((a.1 : Y) * z ^ (Multiplicative.toAdd a.2).val) *
            ((b.1 : Y) * z ^ (Multiplicative.toAdd b.2).val)
        rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod ((Multiplicative.toAdd a.2).val +
          (Multiplicative.toAdd b.2).val) hz3, Subgroup.coe_mul, pow_add]
        have key : (b.1 : Y) * (z ^ (Multiplicative.toAdd a.2).val *
            z ^ (Multiplicative.toAdd b.2).val) =
            z ^ (Multiplicative.toAdd a.2).val * ((b.1 : Y) * z ^ (Multiplicative.toAdd b.2).val) := by
          rw [← mul_assoc, hb, mul_assoc]
        simp only [mul_assoc]
        rw [key]
      }
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : (a.1 : Y) * z ^ (Multiplicative.toAdd a.2).val = 1 := ha
    have hzx : z ^ (Multiplicative.toAdd a.2).val = (a.1 : Y)⁻¹ :=
      eq_inv_of_mul_eq_one_right ha'
    have hmem : z ^ (Multiplicative.toAdd a.2).val ∈ E := by
      rw [hzx]
      exact E.inv_mem a.1.2
    have h0 := hzk _ hmem
    have hlt : (Multiplicative.toAdd a.2).val < 3 := ZMod.val_lt _
    have hval : (Multiplicative.toAdd a.2).val = 0 := by omega
    rw [hval, pow_zero, mul_one] at ha'
    have ha1 : a.1 = 1 := Subtype.ext ha'
    have ha2 : a.2 = 1 := by
      rw [ZMod.val_eq_zero] at hval
      exact (toAdd_eq_zero).1 hval
    exact Prod.ext ha1 ha2
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    Prod.ext (Subtype.ext (elemAbelian_comm hE a.1.2 b.1.2)) (mul_comm _ _)
  have hpow : ∀ a : A, a ^ 3 = 1 := by
    intro a
    have h6 : ∀ x : Multiplicative (ZMod 3), x ^ 3 = 1 := by decide
    refine Prod.ext (Subtype.ext ?_) (h6 a.2)
    exact hE.2 _ a.1.2
  have hA : Nat.card A = 3 ^ (m + 1) := by
    have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
      rw [Nat.card_congr (Multiplicative.ofAdd.symm)]
      simp
    rw [Nat.card_prod, hcard, h3, pow_succ]
  have hle : m + 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hcomm hpow hA f hfinj le_top
  omega


theorem le_normalizer_centralizer_of_le {Y : Type} [Group Y] {S H : Subgroup Y}
    (hH : H ≤ Subgroup.normalizer (S : Set Y)) :
    H ≤ Subgroup.normalizer ((Subgroup.centralizer (S : Set Y) : Subgroup Y) : Set Y) := by
  have fwd : ∀ g ∈ H, ∀ x ∈ Subgroup.centralizer (S : Set Y),
      g * x * g⁻¹ ∈ Subgroup.centralizer (S : Set Y) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro l hl
    have hl' : g⁻¹ * l * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 (hH hg) (g⁻¹ * l * g)).2 (by
        have e : g * (g⁻¹ * l * g) * g⁻¹ = l := by group
        rw [e]
        exact hl)
      exact this
    have hx' := hx _ hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hx']
      _ = (g * x * g⁻¹) * l := by group
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => fwd h hh x hx
  · intro hx
    have := fwd h⁻¹ (Subgroup.inv_mem _ hh) _ hx
    simpa [mul_assoc] using this

theorem barX_eq_range {G : Type} [Group G] [Finite G] {M K : Subgroup G} :
    barX 3 M K = ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (K.subgroupOf M).subtype).range := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem isPGroup_barX {G : Type} [Group G] [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsPGroup 3 ↥K) : IsPGroup 3 ↥(barX 3 M K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [barX_eq_range]
  let φ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (K.subgroupOf M).subtype
  exact (hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKM).symm).of_surjective
    φ.rangeRestrict φ.rangeRestrict_surjective

theorem card_barX_of_isPGroup {G : Type} [Group G] [Finite G] {M K : Subgroup G} (hKM : K ≤ M)
    (hK : IsPGroup 3 ↥K) : Nat.card (barX 3 M K) = Nat.card K := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)).comp (K.subgroupOf M).subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : ↥M) ∈ GLAPPrimeCore 3 ↥M := (QuotientGroup.eq_one_iff _).1 hx
    have hS : IsPGroup 3 ↥(K.subgroupOf M) := hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKM).symm
    have hbot := isPGroup_inf_eq_bot_of_not_dvd Nat.prime_three hS
      (not_dvd_card_pPrimeCore Nat.prime_three M)
    have hmem : (x : ↥M) ∈ K.subgroupOf M ⊓ GLAPPrimeCore 3 ↥M := ⟨x.2, hxN⟩
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.1 hmem)
  rw [barX_eq_range, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv

theorem pRank_quotient_le {G : Type} [Group G] [Finite G] {m : ℕ} {M : Subgroup G}
    (hM2 : CFSG.Open.IsTwoLocal M) (hTLR : CFSG.Open.twoLocalPrimeRank 3 G = m) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≤ m := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_quotient_eq (GLAPPrimeCore 3 ↥M)
    (not_dvd_card_pPrimeCore Nat.prime_three M)]
  apply CFSG.SectionRank.pRank_le (by norm_num)
  intro E _ hE
  have hE' : CFSG.Open.IsElemAbelian 3 (E.map M.subtype) :=
    CFSG.SectionRank.isElemAbelian_map hE M.subtype
  have hVM : E.map M.subtype ≤ M := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2
  have hle := card_le_of_isTwoLocal Nat.prime_three hTLR hM2 hVM hE'
  have hcard : Nat.card (E.map M.subtype) = Nat.card E :=
    Subgroup.card_map_of_injective Subtype.val_injective
  rw [hcard] at hle
  exact hle

theorem case_one_of_three_dvd {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A D T L : Subgroup G}
    (h : Cex134 G m 3 B M E A D T L) (h3 : 3 ∣ Nat.card (cent M D L))
    (hBn : barX 3 M B ≤ Subgroup.normalizer ((barX 3 M (Lstarsub D L) :
        Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)))
    (hDn : barX 3 M D ≤ Subgroup.normalizer ((barX 3 M (Lstarsub D L) :
        Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M))) :
    barX 3 M B ⊓ Subgroup.centralizer ((barX 3 M D ⊔ barX 3 M (Lstarsub D L) :
      Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : GLStanding G m 3 := h.standing
  have hB : IsBOneMax 3 B := h.bOne
  have hM2 : CFSG.Open.IsTwoLocal M := h.pre.1.1
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hTLR : CFSG.Open.twoLocalPrimeRank 3 G = m := hS.rank_eq
  have hBcard : Nat.card B = 3 ^ m := by
    have := hB.1.2.1
    rw [hS.rank_eq] at this
    exact this
  have hBEA : CFSG.Open.IsElemAbelian 3 B := hB.1.1
  have hBp : IsPGroup 3 ↥B := IsPGroup.iff_card.2 ⟨m, hBcard⟩
  have hDA : D ≤ A := h.hD.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDM : D ≤ M := hDA.trans hAM
  have hBDp : IsPGroup 3 ↥(B ⊔ D) :=
    IsPGroup.to_le h.hAB (sup_le le_sup_right (hDA.trans le_sup_left))
  have hBD_M : B ⊔ D ≤ M := sup_le hBM hDM
  have hBbEA : CFSG.Open.IsElemAbelian 3 (barX 3 M B) :=
    isElemAbelian_map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥M)) (isElemAbelian_subgroupOf hBM hBEA)
  have hBbCard : Nat.card (barX 3 M B) = 3 ^ m := by
    rw [card_barX_of_isPGroup hBM hBp, hBcard]
  have hrk := pRank_quotient_le hM2 hTLR
  set Db := barX 3 M D with hDb
  set Bb := barX 3 M B with hBb
  set Lb := barX 3 M (Lstarsub D L) with hLb
  set C := cent M D L with hCdef
  have hC' : C = Subgroup.centralizer (Lb : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := rfl
  have hHb : Bb ⊔ Db ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    sup_le hBn hDn
  have hHC : Bb ⊔ Db ≤ Subgroup.normalizer (C : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rw [hC']
    exact le_normalizer_centralizer_of_le hHb
  have hCX : C ≤ C ⊔ (Bb ⊔ Db) := le_sup_left
  have hHX : Bb ⊔ Db ≤ C ⊔ (Bb ⊔ Db) := le_sup_right
  have hXn : C ⊔ (Bb ⊔ Db) ≤ Subgroup.normalizer (C : Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) :=
    sup_le Subgroup.le_normalizer hHC
  haveI hKn : (C.subgroupOf (C ⊔ (Bb ⊔ Db))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCX).2 hXn
  have hK : C.subgroupOf (C ⊔ (Bb ⊔ Db)) ⊔ (Bb ⊔ Db).subgroupOf (C ⊔ (Bb ⊔ Db)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCX hHX, Subgroup.subgroupOf_self]
  have hHp : IsPGroup 3 ↥((Bb ⊔ Db).subgroupOf (C ⊔ (Bb ⊔ Db))) := by
    have hHbp : IsPGroup 3 ↥(Bb ⊔ Db) :=
      IsPGroup.to_le (isPGroup_barX hBD_M hBDp)
        (sup_le (barX_mono_of_le 3 le_sup_left) (barX_mono_of_le 3 le_sup_right))
    exact hHbp.of_equiv (Subgroup.subgroupOfEquivOfLe hHX).symm
  have h3K : 3 ∣ Nat.card (C.subgroupOf (C ⊔ (Bb ⊔ Db))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv]
    exact h3
  obtain ⟨y, hyK, hy1, hy3, hyc⟩ :=
    exists_fixed_three_part (C.subgroupOf (C ⊔ (Bb ⊔ Db)))
      ((Bb ⊔ Db).subgroupOf (C ⊔ (Bb ⊔ Db))) hK hHp h3K
  have hzC : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ∈ C := Subgroup.mem_subgroupOf.1 hyK
  have hz1 : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ≠ 1 := fun h0 => hy1 (Subtype.ext h0)
  have hz3 : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3
    simpa using this
  have hcomm_sub : ∀ e ∈ Bb ⊔ Db, e * (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) =
      (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) * e := by
    intro e he
    have heX : e ∈ C ⊔ (Bb ⊔ Db) := hHX he
    have := hyc ⟨e, heX⟩ (Subgroup.mem_subgroupOf.2 he)
    have := congrArg Subtype.val this
    simpa using this
  have hzB : ∀ e ∈ Bb, e * (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) =
      (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) * e :=
    fun e he => hcomm_sub e (Subgroup.mem_sup_left he)
  have hzBb : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ∈ Bb :=
    mem_of_centralizes_rank hBbEA hBbCard hrk hz3 hzB
  intro hbot
  have hzcent : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ∈
      Subgroup.centralizer ((Db ⊔ Lb : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hT : Db ⊔ Lb ≤ Subgroup.centralizer ({(y : ↥M ⧸ GLAPPrimeCore 3 ↥M)} :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := by
      apply sup_le
      · intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (hcomm_sub d (Subgroup.mem_sup_right hd)).symm
      · intro l hl
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (Subgroup.mem_centralizer_iff.1 hzC l hl).symm
    have := Subgroup.mem_centralizer_iff.1 (hT hw) _ (Set.mem_singleton _)
    exact this.symm
  have hmem : (y : ↥M ⧸ GLAPPrimeCore 3 ↥M) ∈
      Bb ⊓ Subgroup.centralizer ((Db ⊔ Lb : Subgroup (↥M ⧸ GLAPPrimeCore 3 ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore 3 ↥M)) := ⟨hzBb, hzcent⟩
  rw [hbot] at hmem
  exact hz1 (Subgroup.mem_bot.1 hmem)

end Lemma135

open Lemma135 in
theorem lemma135_i_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    (hC3 : Lemma135.CentThreeInput) (hN : Lemma135.NineCoreInput) : Lemma135_iStatement := by
  intro G _ _ m p B M E A D T L h
  have hp3 : p = 3 := cex134_p_eq_three hP95 h111 h121 hcomp h
  subst hp3
  have hS : GLStanding G m 3 := h.standing
  have hB : IsBOneMax 3 B := h.bOne
  have hM2 : CFSG.Open.IsTwoLocal M := h.pre.1.1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hDA : D ≤ A := h.hD.1
  have hDM : D ≤ M := hDA.trans hAM
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  have hLc : GLAPComponent 3 M L := (hcomp h.toSec13 h.hL).1
  have hLI : L ≤ Istar 3 M D := (h.hL.1).trans (iof_le_istar' 3 M D)
  have hBnorm : B ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) :=
    le_normalizer_lstar_of_normal fun d hd =>
      (((h133 h.toSec13).2 (GLBConj d L)
        (glaPComponent_istar_conj Nat.prime_three hLc hLI (hDM hd))).2).1
  have hDnorm : D ≤ Subgroup.normalizer ((Lstarsub D L : Subgroup G) : Set G) :=
    le_normalizer_lstar
  obtain ⟨hBn, hDn⟩ := barX_lstar_normalizers hBnorm hDnorm
  by_cases hC : cent M D L = ⊥
  ·
    exfalso
    have hBD : B ⊔ D ≤ A ⊔ B := sup_le le_sup_right (hDA.trans le_sup_left)
    have hBD3 : IsPGroup 3 ↥(B ⊔ D) := IsPGroup.to_le h.hAB hBD
    obtain ⟨P, hPM, hBDP⟩ := sylow_above3 (sup_le hBM hDM) hBD3
    have hcore := hN G m h hC P hPM hBDP
    exact h.notB (glaWeakCoreLocal_of_core hS hB hM2 (le_trans le_sup_left hBDP) hPM hcore)
  · exact case_one_of_three_dvd h (hC3 G m h hC) hBn hDn

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
