module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13Comp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1112b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop127
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.SylowTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

namespace AltFacts

theorem input23_2Aut_holds : Input23_2AutStatement := by
  intro K _ _ D _ _ ψ hψ hAlt hD hcard
  obtain ⟨e⟩ := hAlt
  obtain ⟨W, hW, hgen⟩ := S7.exists_pCores_of_aut e ψ hψ hcard
  refine hgen.trans (iSup_mono fun d => iSup_mono' fun hd => ⟨hd, ?_⟩)
  obtain ⟨h2, hfix, hnorm⟩ := hW d hd
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun y hy => hfix y hy) ?_ h2
  intro c hc
  exact hnorm c hc

section Block

variable {G : Type} [Group G] [Finite G]

theorem glaPPrimeCoreOf_le_pCoreOf_of_simple {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G}
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) (hdvd : p ∣ Nat.card ↥L) :
    GLAPPrimeCoreOf p L ≤ pCoreOf 2 L := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Subgroup ↥L := CFSG.pCore 2 ↥L with hS
  set Q : Subgroup ↥L := GLAPPrimeCore p ↥L with hQ
  have hcop2 : Nat.Coprime p (Nat.card ↥S) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hSQ : S ≤ Q := CFSG.le_pPrimeCore_of_normal_coprime (CFSG.pCore_normal (p := 2) (G := ↥L)) hcop2
  haveI : (Q.map (QuotientGroup.mk' S)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Q.map (QuotientGroup.mk' S)) with hbot | htop
  · have hQS : Q ≤ S := by
      intro x hx
      have h1 : QuotientGroup.mk' S x ∈ (⊥ : Subgroup (↥L ⧸ S)) :=
        hbot ▸ Subgroup.mem_map_of_mem _ hx
      rw [Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff x).1 h1
    exact Subgroup.map_mono hQS
  · exfalso
    have hQtop : Q = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      have h1 : QuotientGroup.mk' S x ∈ Q.map (QuotientGroup.mk' S) := htop ▸ Subgroup.mem_top _
      obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 h1
      have h2 : q⁻¹ * x ∈ S := QuotientGroup.eq.1 hqx
      have h3 : x = q * (q⁻¹ * x) := by group
      rw [h3]
      exact Q.mul_mem hq (hSQ h2)
    have hnd : ¬ p ∣ Nat.card ↥Q := (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
    apply hnd
    rw [hQtop, Subgroup.card_top]
    exact hdvd

end Block

theorem cex134_O2_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) : Cex134_O2Statement := by
  intro G _ _ m p B M E A D T L h hp3
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
  have hLM : L ≤ M := hLc.1
  have key : IsGLBlock M L ∧ Prop95Gamma p M D L := by
    rcases (hP.2.2 L hLc).2 with hc | ⟨hb, ha | hb' | hg⟩
    · exact absurd ((barX_mono_of_le p (gammaStar_le_gammaD p D)).trans hc) hnc
    · exact absurd ha (fun ha => h.notAB (Or.inl ha))
    · exact absurd hb' (fun hb' => h.notAB (Or.inr hb'))
    · exact ⟨hb, hg⟩
  obtain ⟨hblock, hγ⟩ := key
  obtain ⟨-, e, -⟩ := hγ
  have h3 : 3 ∣ Nat.card ↥L := by
    have h1 : Nat.card ↥(barX p M L) ∣ Nat.card ↥(L.subgroupOf M) :=
      Subgroup.card_map_dvd (L.subgroupOf M) (QuotientGroup.mk' (GLAPPrimeCore p ↥M))
    have h2 : Nat.card ↥(L.subgroupOf M) = Nat.card ↥L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv
    have h4 : Nat.card ↥(barX p M L) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    rw [← h2]
    exact (show 3 ∣ 2520 by norm_num).trans (h4 ▸ h1)
  subst hp3
  exact glaPPrimeCoreOf_le_pCoreOf_of_simple Nat.prime_three (by norm_num) hblock.simple h3

section L34

theorem finite_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) : Finite X := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hX
  exact Finite.of_equiv _ e.symm.toEquiv

theorem inputAutL34Order9_holds : Lemma1112b.InputAutL34Order9 := by
  intro X _ hX E hE
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite X := finite_of_isLThreeFour hX
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (Lemma1112b.isPGroup_of_isElemAbelian hE)
  have hn2 : n ≤ 2 :=
    (Lemma1112b.le_pRank_of_card (le_top : E ≤ ⊤) hE hn).trans (pRank_mulAut_le_two_of_isLThreeFour hX)
  rw [hn]
  calc (3 : ℕ) ^ n ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 9 := by norm_num

theorem exists_conj_of_mk_eq_three {Γ : Type} [Group Γ] [Finite Γ] (Q : Subgroup Γ) [Q.Normal]
    (hQ : ¬ 3 ∣ Nat.card Q) {y w : Γ} (hy : orderOf y = 3) (hw : orderOf w = 3)
    (hyw : y⁻¹ * w ∈ Q) : ∃ h ∈ Q ⊔ Subgroup.zpowers y, h * w * h⁻¹ = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card Q) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ
  set W : Subgroup Γ := Q ⊔ Subgroup.zpowers y with hW
  have hyW : y ∈ W := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hwW : w ∈ W := by
    have : w = y * (y⁻¹ * w) := by group
    rw [this]
    exact W.mul_mem hyW (Subgroup.mem_sup_left hyw)
  have hY3 : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy]
  have hZ3 : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hw]
  have hYp : IsPGroup 3 (Subgroup.zpowers y) := IsPGroup.of_card (n := 1) (by rw [hY3]; rfl)
  have hZp : IsPGroup 3 (Subgroup.zpowers w) := IsPGroup.of_card (n := 1) (by rw [hZ3]; rfl)
  have hYleW : Subgroup.zpowers y ≤ W := le_sup_right
  have hZleW : Subgroup.zpowers w ≤ W := Subgroup.zpowers_le.2 hwW
  have hbot : Subgroup.zpowers y ⊓ Q = ⊥ := Lemma1210.inf_eq_bot_of_coprime hcop hYp
  have hWcard : Nat.card W = Nat.card (Subgroup.zpowers y) * Nat.card Q := by
    rw [hW, sup_comm]
    exact Lemma1210.card_sup_of_inf_bot hbot
  have hidx : ∀ H : Subgroup W, Nat.card H = 3 → ¬ 3 ∣ H.index := by
    intro H hH
    have h1 := Subgroup.card_mul_index H
    rw [hH, hWcard, hY3] at h1
    have h2 : H.index = Nat.card Q := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h1
    rw [h2]
    exact hQ
  have hYc : Nat.card ((Subgroup.zpowers y).subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleW).toEquiv, hY3]
  have hZc : Nat.card ((Subgroup.zpowers w).subgroupOf W) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZleW).toEquiv, hZ3]
  have hYp' : IsPGroup 3 ((Subgroup.zpowers y).subgroupOf W) :=
    hYp.comap_of_injective W.subtype Subtype.val_injective
  have hZp' : IsPGroup 3 ((Subgroup.zpowers w).subgroupOf W) :=
    hZp.comap_of_injective W.subtype Subtype.val_injective
  let S₁ : Sylow 3 ↥W := IsPGroup.toSylow hZp' (hidx _ hZc)
  let S₂ : Sylow 3 ↥W := IsPGroup.toSylow hYp' (hidx _ hYc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥W) S₁ S₂
  have hS₁coe : (S₁ : Subgroup ↥W) = (Subgroup.zpowers w).subgroupOf W := rfl
  have hS₂coe : (S₂ : Subgroup ↥W) = (Subgroup.zpowers y).subgroupOf W := rfl
  obtain ⟨j, hj⟩ : ∃ j : ℤ, g.1 * w ^ j * g.1⁻¹ = y := by
    have h1 : (⟨y, hyW⟩ : ↥W) ∈ (S₂ : Subgroup ↥W) := by
      rw [hS₂coe]
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers y)
    rw [← hg, Sylow.coe_subgroup_smul] at h1
    obtain ⟨t, ht, hgt⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 h1
    rw [hS₁coe] at ht
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 ht)
    refine ⟨j, ?_⟩
    have := congrArg Subtype.val hgt
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [hj]
    exact this
  obtain ⟨q₀, hq₀, s, hs, hqs⟩ := Subgroup.mem_sup_of_normal_left.1 g.2
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  set π : Γ →* Γ ⧸ Q := QuotientGroup.mk' Q with hπ
  have hπq₀ : π q₀ = 1 := (QuotientGroup.eq_one_iff _).2 hq₀
  have hπg : π g.1 = π y ^ i := by
    rw [← hqs, map_mul, hπq₀, one_mul, map_zpow]
  have hπw : π w = π y := by
    have h1 : π (y⁻¹ * w) = 1 := (QuotientGroup.eq_one_iff _).2 hyw
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.1 h1).symm
  have hy1 : π y ≠ 1 := by
    intro h1
    have hyQ : y ∈ Q := (QuotientGroup.eq_one_iff y).1 h1
    have h2 : orderOf y ∣ Nat.card Q := by
      have := Subgroup.orderOf_dvd_natCard Q hyQ
      simpa using this
    rw [hy] at h2
    exact hQ h2
  have hπy3 : orderOf (π y) = 3 := by
    refine orderOf_eq_prime ?_ hy1
    rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  have hkey : π y = π y ^ j := by
    have h1 : π (g.1 * w ^ j * g.1⁻¹) = π y := by rw [hj]
    rw [map_mul, map_mul, map_inv, hπg, map_zpow, hπw] at h1
    have h2 : π y ^ i * π y ^ j * (π y ^ i)⁻¹ = π y ^ j := by
      rw [← zpow_neg, ← zpow_add, ← zpow_add]
      congr 1
      ring
    exact h1.symm.trans h2
  have hdvd : (3 : ℤ) ∣ j - 1 := by
    have h1 : π y ^ (j - 1) = 1 := by
      rw [zpow_sub, zpow_one, ← hkey, mul_inv_cancel]
    have := orderOf_dvd_iff_zpow_eq_one.2 h1
    rwa [hπy3] at this
  have hwj : w ^ j = w := by
    have h1 : w ^ (j - 1) = 1 := by
      refine orderOf_dvd_iff_zpow_eq_one.1 ?_
      rw [hw]
      exact hdvd
    rw [zpow_sub, zpow_one, mul_inv_eq_one] at h1
    exact h1
  refine ⟨g.1, g.2, ?_⟩
  rw [← hj, hwj]

theorem isRankThreeL34_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) :
    CFSG.LocalAnalysis.RankThreeTheoremC.IsRankThreeL34 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let q : TauCeti.PrimePower := ⟨2, 2, Nat.prime_two, by norm_num⟩
  have hv : (TauCeti.LieTypeIndex.A 2 q).Valid := by
    norm_num [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, q]
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 2 q hv
  rcases hm.2 with ⟨-, F', _, _, hF', ⟨f⟩⟩ | ⟨hn, -⟩
  · refine ⟨q, rfl, rfl, hv, ⟨?_⟩⟩
    have hF2 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
    exact ((e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 3 2 2 (by norm_num)
      hF2)).trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F' 3 2 2 (by norm_num)
      hF').symm).trans f.symm
  · omega

theorem inputL34FusionK_holds : Lemma1112b.InputL34FusionK := by
  intro X _ _ K hL x y hx hy
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup ↥K := GLAPPrimeCore 3 ↥K with hQdef
  haveI : Q.Normal := inferInstance
  have hQ : ¬ 3 ∣ Nat.card Q :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  set π : ↥K →* ↥K ⧸ Q := QuotientGroup.mk' Q with hπ
  have hord : ∀ u : ↥K, orderOf u = 3 → orderOf (π u) = 3 := by
    intro u hu
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hu, pow_orderOf_eq_one, map_one]
    · intro h1
      have huQ : u ∈ Q := (QuotientGroup.eq_one_iff u).1 h1
      have h2 : orderOf u ∣ Nat.card Q := by
        have := Subgroup.orderOf_dvd_natCard Q huQ
        simpa using this
      rw [hu] at h2
      exact hQ h2
  haveI : Finite (↥K ⧸ Q) := inferInstance
  obtain ⟨cb, hcb⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34Borel.exists_conj_of_orderOf_eq_three
    (K := ↥K ⧸ Q) (isRankThreeL34_of_isLThreeFour hL) (hord x hx) (hord y hy)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Q cb
  have hw : orderOf (c * x * c⁻¹) = 3 := by
    rw [← hx]
    exact (MulAut.conj c).orderOf_eq x
  have hyw : y⁻¹ * (c * x * c⁻¹) ∈ Q := by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    show π (y⁻¹ * (c * x * c⁻¹)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, map_inv]
    have : π c * π x * (π c)⁻¹ = π y := hcb
    rw [this, inv_mul_cancel]
  obtain ⟨h, -, hh⟩ := exists_conj_of_mk_eq_three Q hQ hy hw hyw
  refine ⟨(h * c)⁻¹, ?_⟩
  calc (h * c)⁻¹⁻¹ * x * (h * c)⁻¹ = h * (c * x * c⁻¹) * h⁻¹ := by group
    _ = y := hh

theorem p1rank_of_inputs_alt (h1111 : Lemma1111Statement) (hKn : Lemma1112b.InputCgNormalizesK)
    (hC1 : Lemma1112b.InputCentBarRankOne) :
    ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a : G} {K : Subgroup G}
      (h : Cex117 G m 3 B M E A a K), CFSG.Open.pRank 3 (Cg a) = 3 :=
  Lemma1112b.p1rank_of_inputs h1111 hKn hC1 inputAutL34Order9_holds

theorem p1Claim_of_inputs_alt (hsyl : Lemma1112b.P1SylowClaim) (h1111 : Lemma1111Statement)
    (hKn : Lemma1112b.InputCgNormalizesK) (hC1 : Lemma1112b.InputCentBarRankOne) :
    Lemma1112.P1Claim :=
  Lemma1112b.p1Claim_of_inputs hsyl h1111 hKn hC1 inputAutL34Order9_holds

theorem p2Claim_of_inputs_alt (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h113 : Lemma113_iStatement) (hsyl : Lemma1112b.P1SylowClaim) : Lemma1112.P2Claim :=
  Lemma1112b.p2Claim_of_inputs h1111 h119 h113 inputL34FusionK_holds hsyl

theorem lemma1112_of_inputs_alt (h1111 : Lemma1111Statement) (h119 : Lemma119Statement)
    (h113 : Lemma113_iStatement) (h104ii : Lemma104_iiStatement)
    (hsyl : Lemma1112b.P1SylowClaim) (hKn : Lemma1112b.InputCgNormalizesK)
    (hC1 : Lemma1112b.InputCentBarRankOne) (hP3 : Lemma1112.P3Claim) : Lemma1112Statement :=
  lemma1112_of_inputs h1111 h119 h104ii (p1Claim_of_inputs_alt hsyl h1111 hKn hC1)
    (p2Claim_of_inputs_alt h1111 h119 h113 hsyl) hP3

end L34

theorem cex134_O2_of_siblings (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) : Cex134_O2Statement :=
  cex134_O2_of_inputs hP95 h111 h121 sec13_comp_holds

theorem prop134_of_cex_of_siblings (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (h136 : Lemma136Statement) : Prop134_of_cexStatement :=
  prop134_of_cex_of_inputs' hP95 h111 h121 h136 input23_2Aut_holds
    (cex134_O2_of_siblings hP95 h111 h121)

theorem lemma136_of_inputs_alt (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hP1 : Lemma136.P1BarInput)
    (h121c : Prop121_corStatement) (hII : Lemma136.IIHardInput) : Lemma136Statement :=
  lemma136_of_inputs'' hP95 h111 h121 hP1 (cex134_O2_of_siblings hP95 h111 h121) h121c hII

section A13

open Equiv Equiv.Perm

abbrev S13 : Type := Perm (Fin 13)

@[expose] def b1 : S13 := c[0, 1, 2]

@[expose] def b2 : S13 := c[3, 4, 5]

@[expose] def b3 : S13 := c[6, 7, 8]

@[expose] def b4 : S13 := c[9, 10, 11]

theorem b1_pow : b1 ^ 3 = 1 := by decide
theorem b2_pow : b2 ^ 3 = 1 := by decide
theorem b3_pow : b3 ^ 3 = 1 := by decide
theorem b4_pow : b4 ^ 3 = 1 := by decide
theorem b1_ne : b1 ≠ 1 := by decide
theorem b2_ne : b2 ≠ 1 := by decide
theorem b3_ne : b3 ≠ 1 := by decide
theorem b4_ne : b4 ≠ 1 := by decide
theorem b12_comm : b1 * b2 = b2 * b1 := by decide
theorem b13_comm : b1 * b3 = b3 * b1 := by decide
theorem b14_comm : b1 * b4 = b4 * b1 := by decide
theorem b23_comm : b2 * b3 = b3 * b2 := by decide
theorem b24_comm : b2 * b4 = b4 * b2 := by decide
theorem b34_comm : b3 * b4 = b4 * b3 := by decide
theorem b1_alt : b1 ∈ alternatingGroup (Fin 13) := by rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem b2_alt : b2 ∈ alternatingGroup (Fin 13) := by rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem b3_alt : b3 ∈ alternatingGroup (Fin 13) := by rw [Equiv.Perm.mem_alternatingGroup]; decide
theorem b4_alt : b4 ∈ alternatingGroup (Fin 13) := by rw [Equiv.Perm.mem_alternatingGroup]; decide

theorem card_sup_mul_card_inf {Γ : Type} [Group Γ] [Finite Γ] (L R : Subgroup Γ)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup Γ) * Nat.card (L ⊓ R : Subgroup Γ) = Nat.card L * Nat.card R := by
  let μ : L × R →* Γ := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : Γ) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup Γ) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : Γ), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : Γ)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [Subgroup.coe_inv]
        rw [h, inv_inv]
  have h1 := Subgroup.card_ker_mul_card_range μ
  rw [hker, hrange, Nat.card_prod] at h1
  rw [mul_comm]
  exact h1

theorem comm_sup_of_comm {Γ : Type} [Group Γ] {A B : Subgroup Γ} {c : Γ}
    (hA : ∀ a ∈ A, a * c = c * a) (hB : ∀ b ∈ B, b * c = c * b) :
    ∀ x ∈ A ⊔ B, x * c = c * x := by
  have h : A ⊔ B ≤ Subgroup.centralizer ({c} : Set Γ) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (hA a ha))
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hB b hb))
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 (h hx)

theorem comm_zpowers {Γ : Type} [Group Γ] {x y : Γ} (h : x * y = y * x) :
    ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers y, a * b = b * a := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  exact (Commute.zpow_zpow (show Commute x y from h) i j).eq

@[expose] def fixSet (T : Set (Fin 13)) : Subgroup S13 where
  carrier := {σ | ∀ i ∈ T, σ i = i}
  mul_mem' := by
    intro a b ha hb i hi
    simp only [Equiv.Perm.mul_apply]
    rw [hb i hi, ha i hi]
  one_mem' := fun i _ => rfl
  inv_mem' := by
    intro a ha i hi
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

theorem mem_fixSet {T : Set (Fin 13)} {σ : S13} : σ ∈ fixSet T ↔ ∀ i ∈ T, σ i = i := Iff.rfl

theorem zpowers_le_fixSet {x : S13} {T : Set (Fin 13)} (hx : ∀ i ∈ T, x i = i) :
    Subgroup.zpowers x ≤ fixSet T :=
  Subgroup.zpowers_le.2 (mem_fixSet.2 hx)

theorem inf_eq_bot_of_fixSet {A B : Subgroup S13} {T U : Set (Fin 13)} (hA : A ≤ fixSet T)
    (hB : B ≤ fixSet U) (h : ∀ i : Fin 13, i ∈ T ∨ i ∈ U) : A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  refine Equiv.ext fun i => ?_
  rcases h i with hi | hi
  · exact mem_fixSet.1 (hA hσ.1) i hi
  · exact mem_fixSet.1 (hB hσ.2) i hi

@[expose] def Z1 : Subgroup S13 := Subgroup.zpowers b1
@[expose] def Z2 : Subgroup S13 := Subgroup.zpowers b2
@[expose] def Z3 : Subgroup S13 := Subgroup.zpowers b3
@[expose] def Z4 : Subgroup S13 := Subgroup.zpowers b4

@[expose] def R12 : Subgroup S13 := Z1 ⊔ Z2

@[expose] def R34 : Subgroup S13 := Z3 ⊔ Z4

@[expose] def H0 : Subgroup S13 := R12 ⊔ R34

theorem Z1_fix : Z1 ≤ fixSet {i : Fin 13 | 3 ≤ i.val} :=
  zpowers_le_fixSet (by decide)
theorem Z2_fix : Z2 ≤ fixSet {i : Fin 13 | i.val < 3 ∨ 6 ≤ i.val} :=
  zpowers_le_fixSet (by decide)
theorem Z3_fix : Z3 ≤ fixSet {i : Fin 13 | i.val < 6 ∨ 9 ≤ i.val} :=
  zpowers_le_fixSet (by decide)
theorem Z4_fix : Z4 ≤ fixSet {i : Fin 13 | i.val < 9 ∨ i.val = 12} :=
  zpowers_le_fixSet (by decide)

theorem R12_fix : R12 ≤ fixSet {i : Fin 13 | 6 ≤ i.val} :=
  sup_le (Z1_fix.trans (fun σ hσ => mem_fixSet.2 fun i hi => mem_fixSet.1 hσ i (by
      simp only [Set.mem_setOf_eq] at hi ⊢; omega)))
    (Z2_fix.trans (fun σ hσ => mem_fixSet.2 fun i hi => mem_fixSet.1 hσ i (by
      simp only [Set.mem_setOf_eq] at hi ⊢; omega)))

theorem R34_fix : R34 ≤ fixSet {i : Fin 13 | i.val < 6 ∨ i.val = 12} :=
  sup_le (Z3_fix.trans (fun σ hσ => mem_fixSet.2 fun i hi => mem_fixSet.1 hσ i (by
      simp only [Set.mem_setOf_eq] at hi ⊢; omega)))
    (Z4_fix.trans (fun σ hσ => mem_fixSet.2 fun i hi => mem_fixSet.1 hσ i (by
      simp only [Set.mem_setOf_eq] at hi ⊢; omega)))

theorem Z12_inf : Z1 ⊓ Z2 = ⊥ :=
  inf_eq_bot_of_fixSet Z1_fix Z2_fix (by intro i; simp only [Set.mem_setOf_eq]; omega)

theorem Z34_inf : Z3 ⊓ Z4 = ⊥ :=
  inf_eq_bot_of_fixSet Z3_fix Z4_fix (by intro i; simp only [Set.mem_setOf_eq]; omega)

theorem R_inf : R12 ⊓ R34 = ⊥ :=
  inf_eq_bot_of_fixSet R12_fix R34_fix (by intro i; simp only [Set.mem_setOf_eq]; omega)

theorem Z1_card : Nat.card Z1 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Z1
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime b1_pow b1_ne
theorem Z2_card : Nat.card Z2 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Z2
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime b2_pow b2_ne
theorem Z3_card : Nat.card Z3 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Z3
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime b3_pow b3_ne
theorem Z4_card : Nat.card Z4 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Z4
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime b4_pow b4_ne

theorem Z12_comm : ∀ a ∈ Z1, ∀ b ∈ Z2, a * b = b * a := comm_zpowers b12_comm
theorem Z34_comm : ∀ a ∈ Z3, ∀ b ∈ Z4, a * b = b * a := comm_zpowers b34_comm

theorem Z13_comm : ∀ a ∈ Z1, ∀ b ∈ Z3, a * b = b * a := comm_zpowers b13_comm
theorem Z14_comm : ∀ a ∈ Z1, ∀ b ∈ Z4, a * b = b * a := comm_zpowers b14_comm
theorem Z23_comm : ∀ a ∈ Z2, ∀ b ∈ Z3, a * b = b * a := comm_zpowers b23_comm
theorem Z24_comm : ∀ a ∈ Z2, ∀ b ∈ Z4, a * b = b * a := comm_zpowers b24_comm

theorem R_comm : ∀ a ∈ R12, ∀ b ∈ R34, a * b = b * a := by
  intro a ha b hb
  have h3 : ∀ x ∈ R12, ∀ c ∈ Z3, x * c = c * x := fun x hx c hc =>
    comm_sup_of_comm (A := Z1) (B := Z2) (c := c) (fun a ha => Z13_comm a ha c hc)
      (fun a ha => Z23_comm a ha c hc) x hx
  have h4 : ∀ x ∈ R12, ∀ c ∈ Z4, x * c = c * x := fun x hx c hc =>
    comm_sup_of_comm (A := Z1) (B := Z2) (c := c) (fun a ha => Z14_comm a ha c hc)
      (fun a ha => Z24_comm a ha c hc) x hx
  have := comm_sup_of_comm (A := Z3) (B := Z4) (c := a) (fun x hx => (h3 a ha x hx).symm)
    (fun x hx => (h4 a ha x hx).symm) b hb
  exact this.symm

theorem R12_card : Nat.card R12 = 9 := by
  have h := card_sup_mul_card_inf Z1 Z2 Z12_comm
  rw [Z12_inf, Subgroup.card_bot, Z1_card, Z2_card] at h
  simpa [R12] using h

theorem R34_card : Nat.card R34 = 9 := by
  have h := card_sup_mul_card_inf Z3 Z4 Z34_comm
  rw [Z34_inf, Subgroup.card_bot, Z3_card, Z4_card] at h
  simpa [R34] using h

theorem H0_card : Nat.card H0 = 3 ^ 4 := by
  have h := card_sup_mul_card_inf R12 R34 R_comm
  rw [R_inf, Subgroup.card_bot, R12_card, R34_card] at h
  simpa [H0] using h

theorem isElemAbelian_Z (x : S13) (h3 : x ^ 3 = 1) : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) := by
  rw [Subgroup.zpowers_eq_closure]
  refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
  · intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  · intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact h3

theorem R12_elem : CFSG.Open.IsElemAbelian 3 R12 :=
  CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_Z b1 b1_pow) (isElemAbelian_Z b2 b2_pow)
    Z12_comm

theorem R34_elem : CFSG.Open.IsElemAbelian 3 R34 :=
  CFSG.Open.IsElemAbelian.sup_of_commute (isElemAbelian_Z b3 b3_pow) (isElemAbelian_Z b4 b4_pow)
    Z34_comm

theorem H0_elem : CFSG.Open.IsElemAbelian 3 H0 :=
  CFSG.Open.IsElemAbelian.sup_of_commute R12_elem R34_elem R_comm

theorem Z_le_alt {x : S13} (hx : x ∈ alternatingGroup (Fin 13)) :
    Subgroup.zpowers x ≤ alternatingGroup (Fin 13) := Subgroup.zpowers_le.2 hx

theorem R12_alt : R12 ≤ alternatingGroup (Fin 13) :=
  sup_le (Z_le_alt b1_alt) (Z_le_alt b2_alt)

theorem R34_alt : R34 ≤ alternatingGroup (Fin 13) :=
  sup_le (Z_le_alt b3_alt) (Z_le_alt b4_alt)

theorem H0_alt : H0 ≤ alternatingGroup (Fin 13) := sup_le R12_alt R34_alt

theorem mem_normalizer_of_comm {Γ : Type} [Group Γ] (S : Subgroup Γ) {y : Γ}
    (h : ∀ r ∈ S, r * y = y * r) : y ∈ Subgroup.normalizer (S : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have : y * g * y⁻¹ = g := by rw [← h g hg]; group
    rw [this]
    exact hg
  · intro hg
    have h1 := h _ hg
    have h2 : g = y * g * y⁻¹ := by
      have : y * g = y * (y * g * y⁻¹) := by
        calc y * g = (y * g * y⁻¹) * y := by group
          _ = y * (y * g * y⁻¹) := h1
      exact mul_left_cancel this
    exact h2 ▸ hg

@[expose] def J1 : Subgroup S13 :=
  Subgroup.centralizer ({b1, b2} : Set S13) ⊓ alternatingGroup (Fin 13)

@[expose] def J2 : Subgroup S13 :=
  Subgroup.centralizer ({b3, b4} : Set S13) ⊓ alternatingGroup (Fin 13)

theorem mem_J1 {σ : S13} (h1 : σ * b1 = b1 * σ) (h2 : σ * b2 = b2 * σ)
    (h : σ ∈ alternatingGroup (Fin 13)) : σ ∈ J1 := by
  refine Subgroup.mem_inf.2 ⟨?_, h⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rcases hg with rfl | rfl
  · exact h1.symm
  · exact h2.symm

theorem mem_J2 {σ : S13} (h1 : σ * b3 = b3 * σ) (h2 : σ * b4 = b4 * σ)
    (h : σ ∈ alternatingGroup (Fin 13)) : σ ∈ J2 := by
  refine Subgroup.mem_inf.2 ⟨?_, h⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rcases hg with rfl | rfl
  · exact h1.symm
  · exact h2.symm

theorem J1_le_alt : J1 ≤ alternatingGroup (Fin 13) := inf_le_right
theorem J2_le_alt : J2 ≤ alternatingGroup (Fin 13) := inf_le_right

theorem threeCycle_b3 : b3.IsThreeCycle := card_support_eq_three_iff.1 (by decide)

theorem b3_mem_J1 : b3 ∈ J1 := mem_J1 b13_comm.symm b23_comm.symm b3_alt

theorem orbit12 (i : Fin 13) : ∃ h ∈ J1 ⊔ J2, h 12 = i := by
  have k1 : ∀ σ : S13, σ * b1 = b1 * σ → σ * b2 = b2 * σ → σ ∈ alternatingGroup (Fin 13) →
      σ ∈ J1 ⊔ J2 := fun σ h1 h2 h => Subgroup.mem_sup_left (mem_J1 h1 h2 h)
  have k2 : ∀ σ : S13, σ * b3 = b3 * σ → σ * b4 = b4 * σ → σ ∈ alternatingGroup (Fin 13) →
      σ ∈ J1 ⊔ J2 := fun σ h1 h2 h => Subgroup.mem_sup_right (mem_J2 h1 h2 h)
  fin_cases i
  · exact ⟨c[12, 0, 1], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 1, 2], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 2, 0], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 3, 4], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 4, 5], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 5, 3], k2 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 6, 7], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 7, 8], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 8, 6], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 9, 10], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 10, 11], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨c[12, 11, 9], k1 _ (by decide) (by decide) (by rw [Equiv.Perm.mem_alternatingGroup]; decide), by decide⟩
  · exact ⟨1, (J1 ⊔ J2).one_mem, by decide⟩

theorem alt_le_J12 : alternatingGroup (Fin 13) ≤ J1 ⊔ J2 := by
  have hpre : MulAction.IsPretransitive ↥(J1 ⊔ J2) (Fin 13) := by
    rw [MulAction.isPretransitive_iff_base (12 : Fin 13)]
    intro i
    obtain ⟨h, hh, hi⟩ := orbit12 i
    exact ⟨⟨h, hh⟩, hi⟩
  have hprim : MulAction.IsPreprimitive ↥(J1 ⊔ J2) (Fin 13) := by
    refine MulAction.IsPreprimitive.of_prime_card ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim (g := b3)
    threeCycle_b3 (Subgroup.mem_sup_left b3_mem_J1)

theorem J1_le_normalizer :
    J1.subgroupOf (alternatingGroup (Fin 13)) ≤
      Subgroup.normalizer (((R12.subgroupOf (alternatingGroup (Fin 13))) :
        Subgroup (alternatingGroup (Fin 13))) : Set (alternatingGroup (Fin 13))) := by
  intro y hy
  have hy' : (y : S13) ∈ J1 := hy
  have hc1 : (y : S13) * b1 = b1 * y := (Subgroup.mem_centralizer_iff.1 hy'.1 b1 (by simp)).symm
  have hc2 : (y : S13) * b2 = b2 * y := (Subgroup.mem_centralizer_iff.1 hy'.1 b2 (by simp)).symm
  apply mem_normalizer_of_comm
  intro r hr
  have hr' : (r : S13) ∈ R12 := hr
  have h := comm_sup_of_comm (A := Z1) (B := Z2) (c := (y : S13))
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact (Commute.zpow_left (show Commute b1 (y : S13) from hc1.symm) i).eq)
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact (Commute.zpow_left (show Commute b2 (y : S13) from hc2.symm) i).eq) r hr'
  exact Subtype.ext h

theorem J2_le_normalizer :
    J2.subgroupOf (alternatingGroup (Fin 13)) ≤
      Subgroup.normalizer (((R34.subgroupOf (alternatingGroup (Fin 13))) :
        Subgroup (alternatingGroup (Fin 13))) : Set (alternatingGroup (Fin 13))) := by
  intro y hy
  have hy' : (y : S13) ∈ J2 := hy
  have hc1 : (y : S13) * b3 = b3 * y := (Subgroup.mem_centralizer_iff.1 hy'.1 b3 (by simp)).symm
  have hc2 : (y : S13) * b4 = b4 * y := (Subgroup.mem_centralizer_iff.1 hy'.1 b4 (by simp)).symm
  apply mem_normalizer_of_comm
  intro r hr
  have hr' : (r : S13) ∈ R34 := hr
  have h := comm_sup_of_comm (A := Z3) (B := Z4) (c := (y : S13))
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact (Commute.zpow_left (show Commute b3 (y : S13) from hc1.symm) i).eq)
    (fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact (Commute.zpow_left (show Commute b4 (y : S13) from hc2.symm) i).eq) r hr'
  exact Subtype.ext h

theorem H0_GLBCore :
    CFSG.Open.GLBCore 3 2 (H0.subgroupOf (alternatingGroup (Fin 13))) = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_top_iff]
  set A : Subgroup S13 := alternatingGroup (Fin 13) with hA
  have hR12 : R12.subgroupOf A ≤ H0.subgroupOf A := fun x hx =>
    Subgroup.mem_subgroupOf.2 ((le_sup_left : R12 ≤ H0) (Subgroup.mem_subgroupOf.1 hx))
  have hR34 : R34.subgroupOf A ≤ H0.subgroupOf A := fun x hx =>
    Subgroup.mem_subgroupOf.2 ((le_sup_right : R34 ≤ H0) (Subgroup.mem_subgroupOf.1 hx))
  have hrk : ∀ R : Subgroup S13, CFSG.Open.IsElemAbelian 3 R → Nat.card R = 9 → R ≤ A →
      2 ≤ CFSG.Open.pRank 3 (R.subgroupOf A) := by
    intro R hRe hRc hRA
    have hE : CFSG.Open.IsElemAbelian 3 (R.subgroupOf A) := Lemma1112b.isElemAbelian_subgroupOf hRe A
    have hc : Nat.card (R.subgroupOf A) = 3 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRA).toEquiv, hRc]
      norm_num
    exact Lemma1112b.le_pRank_of_card le_rfl hE hc
  have hN1 : Subgroup.normalizer (((R12.subgroupOf A : Subgroup A)) : Set A) ≤
      CFSG.Open.GLBCore 3 2 (H0.subgroupOf A) :=
    le_sSup ⟨R12.subgroupOf A, hR12, hrk R12 R12_elem R12_card R12_alt, rfl⟩
  have hN2 : Subgroup.normalizer (((R34.subgroupOf A : Subgroup A)) : Set A) ≤
      CFSG.Open.GLBCore 3 2 (H0.subgroupOf A) :=
    le_sSup ⟨R34.subgroupOf A, hR34, hrk R34 R34_elem R34_card R34_alt, rfl⟩
  intro x _
  have hx : (x : S13) ∈ J1 ⊔ J2 := alt_le_J12 x.2
  have hx' : x ∈ (J1 ⊔ J2).subgroupOf A := hx
  rw [Subgroup.subgroupOf_sup J1_le_alt J2_le_alt] at hx'
  exact sup_le (J1_le_normalizer.trans hN1) (J2_le_normalizer.trans hN2) hx'

theorem H0A_card : Nat.card (H0.subgroupOf (alternatingGroup (Fin 13))) = 3 ^ 4 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe H0_alt).toEquiv, H0_card]

theorem H0A_elem : CFSG.Open.IsElemAbelian 3 (H0.subgroupOf (alternatingGroup (Fin 13))) :=
  Lemma1112b.isElemAbelian_subgroupOf H0_elem _

open CFSG.AGLEmbedding.Norton.OrdinaryProofs in
theorem input1210_P2_holds : Lemma1210.Input1210_P2 := by
  intro Y _ _ ⟨e⟩ Q hQ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup S13 := alternatingGroup (Fin 13) with hA
  have hH0p : IsPGroup 3 (H0.subgroupOf A) :=
    IsPGroup.of_card (n := 4) H0A_card
  obtain ⟨P0, hP0⟩ := hH0p.exists_le_sylow
  have hQp : IsPGroup 3 Q := hQ.2.1
  obtain ⟨SQ, hSQ⟩ := hQp.exists_le_sylow
  have hSQQ : (SQ : Subgroup Y) = Q := hQ.2.2 _ le_top SQ.isPGroup' hSQ
  let SA : Sylow 3 ↥A := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective SQ
  obtain ⟨g, hg⟩ := sylow_eq_map_conj P0 SA
  have hSA : (SA : Subgroup ↥A) = Q.map e.toMonoidHom := by
    rw [← hSQQ]
    rfl
  set H1 : Subgroup ↥A := (H0.subgroupOf A).map (MulAut.conj g : ↥A ≃* ↥A).toMonoidHom with hH1
  refine ⟨H1.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : H1 ≤ Q.map e.toMonoidHom := by
      rw [← hSA, hg]
      exact Subgroup.map_mono hP0
    calc H1.map e.symm.toMonoidHom ≤ (Q.map e.toMonoidHom).map e.symm.toMonoidHom :=
          Subgroup.map_mono h1
      _ = Q := map_map_symm_equiv e Q
  · exact CFSG.AGLEmbedding.Norton.OrdinaryProofs.isElemAbelian_map e.symm
      (CFSG.AGLEmbedding.Norton.OrdinaryProofs.isElemAbelian_map (MulAut.conj g : ↥A ≃* ↥A)
        H0A_elem)
  · rw [Subgroup.card_map_of_injective e.symm.injective, hH1,
      Subgroup.card_map_of_injective (MulAut.conj g : ↥A ≃* ↥A).injective]
    exact H0A_card
  · rw [GLBCore_map_equiv e.symm, hH1, GLBCore_map_conj, H0_GLBCore]
    simp

end A13

section Cfg

open Equiv Equiv.Perm
open scoped Classical

@[expose] def moved (Fh : Subgroup (Perm (Fin 13))) : Set (Fin 13) := {j | ∃ g ∈ Fh, g j ≠ j}

theorem mem_moved {Fh : Subgroup (Perm (Fin 13))} {j : Fin 13} :
    j ∈ moved Fh ↔ ∃ g ∈ Fh, g j ≠ j := Iff.rfl

theorem not_moved_fix' {Fh : Subgroup (Perm (Fin 13))} {g : Perm (Fin 13)} (hg : g ∈ Fh)
    {j : Fin 13} (hj : j ∉ moved Fh) : g j = j := by
  by_contra h
  exact hj ⟨g, hg, h⟩

structure Cfg13 (Fh Bh : Subgroup (Perm (Fin 13))) (c₀ : Perm (Fin 13)) : Prop where
  comm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x
  three : ∀ x ∈ Fh, x ^ 3 = 1
  fix4 : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4
  reg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
    ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k
  hB : Bh = Subgroup.zpowers c₀
  hc₀ : c₀ ≠ 1 → c₀.IsThreeCycle ∧ ∀ j ∈ moved Fh, c₀ j = j

variable {Fh Bh : Subgroup (Perm (Fin 13))} {c₀ : Perm (Fin 13)}

theorem commute_of_fix' {x y : Perm (Fin 13)} (hx : ∀ j ∈ moved Fh, x j = j)
    (hy : ∀ j, j ∉ moved Fh → y j = j) : x * y = y * x := by
  ext j
  by_cases hj : j ∈ moved Fh
  · have hyj : y j ∈ moved Fh := by
      by_contra hn
      have hyy : y j = j := y.injective (hy _ hn)
      rw [hyy] at hn
      exact hn hj
    rw [Perm.mul_apply, Perm.mul_apply, hx j hj, hx _ hyj]
  · have hxj : x j ∉ moved Fh := by
      intro hm
      apply hj
      have := hx _ hm
      rw [← x.injective this]
      exact hm
    rw [Perm.mul_apply, Perm.mul_apply, hy j hj, hy _ hxj]

theorem Cfg13.card_moved (h : Cfg13 Fh Bh c₀) : Set.ncard (moved Fh) = 9 := by
  have hc : moved Fh = {j : Fin 13 | ∀ g ∈ Fh, g j = j}ᶜ := by
    ext j
    simp [moved]
  have := Set.ncard_add_ncard_compl {j : Fin 13 | ∀ g ∈ Fh, g j = j}
  have h13 : Nat.card (Fin 13) = 13 := by simp
  rw [h.fix4, ← hc, h13] at this
  omega

theorem Cfg13.bfix (h : Cfg13 Fh Bh c₀) : ∀ x ∈ Bh, ∀ j ∈ moved Fh, x j = j := by
  intro x hx j hj
  rw [h.hB] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  by_cases h1 : c₀ = 1
  · subst h1
    simp
  · exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ((h.hc₀ h1).2 j hj) k

theorem Cfg13.fb_comm (h : Cfg13 Fh Bh c₀) : ∀ f ∈ Fh, ∀ c ∈ Bh, f * c = c * f := by
  intro f hf c hc
  exact (commute_of_fix' (Fh := Fh) (h.bfix c hc) (fun j hj => not_moved_fix' hf hj)).symm

theorem Cfg13.supp_F (h : Cfg13 Fh Bh c₀) {f : Perm (Fin 13)} (hf : f ∈ Fh) (hf1 : f ≠ 1) :
    f.support.card = 9 := by
  have hset : (f.support : Set (Fin 13)) = moved Fh := by
    ext j
    simp only [Finset.mem_coe, Equiv.Perm.mem_support]
    constructor
    · intro hj
      exact ⟨f, hf, hj⟩
    · intro hj hfj
      obtain ⟨g, hg, hgj⟩ := hj
      obtain ⟨u, -, hu⟩ := h.reg j j ⟨g, hg, hgj⟩ ⟨g, hg, hgj⟩
      have h1 : (1 : Perm (Fin 13)) = u := hu 1 ⟨Fh.one_mem, rfl⟩
      have h2 : f = u := hu f ⟨hf, hfj⟩
      exact hf1 (h2.trans h1.symm)
  rw [← Set.ncard_coe_finset, hset]
  exact h.card_moved

theorem Cfg13.pow_three_B (h : Cfg13 Fh Bh c₀) {c : Perm (Fin 13)} (hc : c ∈ Bh) : c ^ 3 = 1 := by
  rw [h.hB] at hc
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  by_cases h1 : c₀ = 1
  · subst h1
    simp
  · have h3 : c₀ ^ 3 = 1 := by
      have := (h.hc₀ h1).1.orderOf
      rw [← this]
      exact pow_orderOf_eq_one c₀
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h3, one_zpow]

theorem Cfg13.threeCycle_B (h : Cfg13 Fh Bh c₀) {c : Perm (Fin 13)} (hc : c ∈ Bh) (hc1 : c ≠ 1) :
    c.IsThreeCycle := by
  rw [h.hB] at hc
  have h1 : c₀ ≠ 1 := by
    rintro rfl
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hc
    exact hc1 hc
  have h3cyc := (h.hc₀ h1).1
  have hord := h3cyc.orderOf
  rw [mem_zpowers_iff_mem_range_orderOf] at hc
  simp only [Finset.mem_image, Finset.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  rw [hord] at hi
  interval_cases i
  · exact absurd (pow_zero c₀) hc1
  · rw [pow_one]; exact h3cyc
  · have h3 : c₀ ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one c₀
    have : c₀ ^ 2 = c₀⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ]; exact h3
    rw [this]
    exact h3cyc.inv

theorem Cfg13.exists_mul (h : Cfg13 Fh Bh c₀) {x : Perm (Fin 13)} (hx : x ∈ Fh ⊔ Bh) :
    ∃ f ∈ Fh, ∃ c ∈ Bh, f * c = x :=
  Lemma1112b.exists_mul_of_mem_sup_of_commute h.fb_comm hx

theorem Cfg13.pow_three_sup (h : Cfg13 Fh Bh c₀) {x : Perm (Fin 13)} (hx : x ∈ Fh ⊔ Bh) :
    x ^ 3 = 1 := by
  obtain ⟨f, hf, c, hc, rfl⟩ := h.exists_mul hx
  rw [Commute.mul_pow (h.fb_comm f hf c hc), h.three f hf, h.pow_three_B hc, one_mul]

theorem Cfg13.supp_card (h : Cfg13 Fh Bh c₀) {x : Perm (Fin 13)} (hx : x ∈ Fh ⊔ Bh) (hx1 : x ≠ 1) :
    x.support.card = 3 ∨ x.support.card = 9 ∨ x.support.card = 12 := by
  obtain ⟨f, hf, c, hc, rfl⟩ := h.exists_mul hx
  have hdisj : f.Disjoint c := by
    intro j
    by_cases hj : j ∈ moved Fh
    · exact Or.inr (h.bfix c hc j hj)
    · exact Or.inl (not_moved_fix' hf hj)
  by_cases hf1 : f = 1
  · subst hf1
    have hc1 : c ≠ 1 := by simpa using hx1
    left
    rw [one_mul]
    exact (card_support_eq_three_iff.2 (h.threeCycle_B hc hc1))
  · by_cases hc1 : c = 1
    · subst hc1
      right; left
      rw [mul_one]
      exact h.supp_F hf hf1
    · right; right
      rw [hdisj.support_mul, Finset.card_union_of_disjoint hdisj.disjoint_support,
        h.supp_F hf hf1, card_support_eq_three_iff.2 (h.threeCycle_B hc hc1)]

theorem three_pow_five_dvd_centralizer {σ : Perm (Fin 13)} (h3 : σ ^ 3 = 1)
    (hs : σ.support.card = 3 ∨ σ.support.card = 9 ∨ σ.support.card = 12) :
    3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({σ} : Set (Perm (Fin 13)))) := by
  have hct : ∀ n ∈ σ.cycleType, n = 3 := by
    intro n hn
    have h1 : n ∣ orderOf σ := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have h3' : n ∣ 3 := h1.trans h2
    have h4 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime Nat.prime_three).1 h3' with h | h
    · omega
    · exact h
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
    Multiset.eq_replicate.2 ⟨rfl, hct⟩
  set k := Multiset.card σ.cycleType with hk
  have hsum : σ.cycleType.sum = σ.support.card := Equiv.Perm.sum_cycleType σ
  have hsum' : σ.cycleType.sum = 3 * k := by
    rw [hrep, Multiset.sum_replicate]
    simp [mul_comm]
  have hk' : k = 1 ∨ k = 3 ∨ k = 4 := by omega
  rw [nat_card_centralizer σ]
  have hprod : σ.cycleType.prod = 3 ^ k := by
    rw [hrep, Multiset.prod_replicate]
  have hcount : σ.cycleType.count 3 = k := by
    rw [hrep, Multiset.count_replicate_self]
  have hfin : σ.cycleType.toFinset = {3} := by
    ext n
    simp only [Multiset.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact hct n
    · rintro rfl
      rw [hrep]
      apply Multiset.mem_replicate.2
      refine ⟨?_, rfl⟩
      omega
  rw [hsum', hprod, hfin, Finset.prod_singleton, hcount, Fintype.card_fin]
  rcases hk' with h | h | h <;> rw [h] <;> decide

theorem exists_threeGroup_cent {σ : Perm (Fin 13)} (h3 : σ ^ 3 = 1)
    (hs : σ.support.card = 3 ∨ σ.support.card = 9 ∨ σ.support.card = 12)
    {X : Subgroup (Perm (Fin 13))} (hX : IsPGroup 3 X) (hXc : ∀ x ∈ X, x * σ = σ * x) :
    ∃ P : Subgroup (Perm (Fin 13)), IsPGroup 3 P ∧ X ≤ P ∧ (∀ p ∈ P, p * σ = σ * p) ∧
      3 ^ 5 ≤ Nat.card P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup (Perm (Fin 13)) := Subgroup.centralizer ({σ} : Set (Perm (Fin 13))) with hC
  have hXC : X ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hXc x hx)
  have hT : IsPGroup 3 (X.subgroupOf C) := hX.comap_of_injective C.subtype Subtype.val_injective
  obtain ⟨S, hS⟩ := hT.exists_le_sylow
  refine ⟨(S : Subgroup ↥C).map C.subtype, S.isPGroup'.map C.subtype, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hXC hx⟩, hS (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 p.2
  · rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity]
    have hdvd := three_pow_five_dvd_centralizer h3 hs
    have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have h5 : 5 ≤ (Nat.card C).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 hdvd
    exact Nat.pow_le_pow_right (by norm_num) h5

end Cfg

section Unpack

variable {G : Type} [Group G] [Finite G]

theorem config_unpack {N K A F : Subgroup G} {a : G}
    (ι : ↥(barX 3 N K) →* Equiv.Perm (Fin 13)) (hιinj : Function.Injective ι)
    (Fh Bh : Subgroup (Equiv.Perm (Fin 13)))
    (hFh : Fh = ((barX 3 N F).subgroupOf (barX 3 N K)).map ι)
    (hBh : Bh = ((barX 3 N (Subgroup.zpowers a)).subgroupOf (barX 3 N K)).map ι)
    (hAN : A ≤ N) (hAK : barX 3 N A ≤ barX 3 N K) (hEk : IsEkIn 3 2 A F) (haA : a ∈ A)
    (hAeq : A = F ⊔ Subgroup.zpowers a)
    (hFix : Set.ncard {j : Fin 13 | ∀ g ∈ Fh, g j = j} = 4)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Equiv.Perm (Fin 13), g ∈ Fh ∧ g j = k)
    (hBth : ∀ g ∈ Bh, g ≠ 1 → g.IsThreeCycle ∧ ∀ j : Fin 13, (∃ h ∈ Fh, h j ≠ j) → g j = j) :
    ∃ c₀ : Equiv.Perm (Fin 13), Cfg13 Fh Bh c₀ ∧
      ((barX 3 N A).subgroupOf (barX 3 N K)).map ι = Fh ⊔ Bh := by
  have hFA : F ≤ A := hEk.1
  have hFN : F ≤ N := hFA.trans hAN
  have haN : a ∈ N := hAN haA
  have hzN : Subgroup.zpowers a ≤ N := Subgroup.zpowers_le.2 haN
  have hFel : CFSG.Open.IsElemAbelian 3 F := hEk.2.1
  have hFhmem : ∀ x ∈ Fh, ∃ (y : ↥(barX 3 N K)), ∃ u : ↥N, (u : G) ∈ F ∧
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) u = (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) ∧ ι y = x := by
    intro x hx
    rw [hFh] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨u, hu, hπu⟩ := Prop127.mem_barX.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨y, u, hu, hπu, rfl⟩
  have hFcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x := by
    intro x hx x' hx'
    obtain ⟨y, u, hu, hπu, rfl⟩ := hFhmem x hx
    obtain ⟨y', u', hu', hπu', rfl⟩ := hFhmem x' hx'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (y' : ↥N ⧸ GLAPPrimeCore 3 ↥N) =
      (y' : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (y : ↥N ⧸ GLAPPrimeCore 3 ↥N)
    rw [← hπu, ← hπu', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Lemma1210.elemAb_comm hFel hu hu'
  have hF3 : ∀ x ∈ Fh, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, u, hu, hπu, rfl⟩ := hFhmem x hx
    rw [← map_pow]
    have h1 : y ^ 3 = 1 := by
      apply Subtype.ext
      show (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) ^ 3 = 1
      rw [← hπu, ← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (hFel.2 _ hu)
      rw [this, map_one]
    rw [h1, map_one]
  have hπaK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩ ∈ barX 3 N K :=
    hAK (Prop127.mem_barX.2 ⟨⟨a, haN⟩, haA, rfl⟩)
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : Equiv.Perm (Fin 13),
      c₀ = ι ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩, hπaK⟩ := ⟨_, rfl⟩
  have hBeq : Bh = Subgroup.zpowers c₀ := by
    apply le_antisymm
    · intro x hx
      rw [hBh] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      obtain ⟨u, hu, hπu⟩ := Prop127.mem_barX.1 (Subgroup.mem_subgroupOf.1 hy)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hu
      have huk : u = (⟨a, haN⟩ : ↥N) ^ k := Subtype.ext (by simpa using hk.symm)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [hc₀def, ← map_zpow]
      congr 1
      apply Subtype.ext
      show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩) ^ k =
        (y : ↥N ⧸ GLAPPrimeCore 3 ↥N)
      rw [← map_zpow, ← huk, hπu]
    · rw [Subgroup.zpowers_le, hBh, hc₀def]
      exact Subgroup.mem_map.2 ⟨⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨a, haN⟩, hπaK⟩,
        Subgroup.mem_subgroupOf.2
          (Prop127.mem_barX.2 ⟨⟨a, haN⟩, Subgroup.mem_zpowers a, rfl⟩), rfl⟩
  have hc₀mem : c₀ ∈ Bh := hBeq ▸ Subgroup.mem_zpowers c₀
  have hbarA : barX 3 N A = barX 3 N F ⊔ barX 3 N (Subgroup.zpowers a) := by
    have h := congrArg (barX 3 N) hAeq
    rw [h, Prop127.barX_sup hFN hzN]
  have hbarFY : barX 3 N F ≤ barX 3 N K := (Lemma1210.barX_mono_left hFA).trans hAK
  have hbarBY : barX 3 N (Subgroup.zpowers a) ≤ barX 3 N K :=
    (Lemma1210.barX_mono_left (Subgroup.zpowers_le.2 haA)).trans hAK
  have hAmap : ((barX 3 N A).subgroupOf (barX 3 N K)).map ι = Fh ⊔ Bh := by
    rw [hbarA, Subgroup.subgroupOf_sup hbarFY hbarBY, Subgroup.map_sup, hFh, hBh]
  exact ⟨c₀, ⟨hFcomm, hF3, hFix, hreg, hBeq, fun hne => hBth c₀ hc₀mem hne⟩, hAmap⟩

end Unpack

section CenProof

open Equiv Equiv.Perm

theorem isPGroup_three_of_pow_three {Γ : Type} [Group Γ] {X : Subgroup Γ} (h : ∀ x ∈ X, x ^ 3 = 1) :
    IsPGroup 3 X := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h g hg)
  rw [Subgroup.orderOf_mk]
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact ⟨0, by rw [h1, pow_zero]⟩
  · exact ⟨1, by rw [h1, pow_one]⟩

theorem mem_alt_of_isPGroup_three {n : ℕ} {P : Subgroup (Perm (Fin n))} (hP : IsPGroup 3 P) :
    P ≤ alternatingGroup (Fin n) := by
  intro p hp
  rw [Equiv.Perm.mem_alternatingGroup]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) ⟨p, hp⟩
  rw [Subgroup.orderOf_mk] at hk
  have h1 : Equiv.Perm.sign p ^ (3 ^ k) = 1 := by
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h2 | h2
  · exact h2
  · rw [h2] at h1
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    rw [hodd.neg_one_pow] at h1
    exact absurd h1 (by decide)

variable {Fh Bh : Subgroup (Perm (Fin 13))} {c₀ : Perm (Fin 13)}

theorem Cfg13.comm_sup (h : Cfg13 Fh Bh c₀) :
    ∀ x ∈ Fh ⊔ Bh, ∀ y ∈ Fh ⊔ Bh, x * y = y * x := by
  have hFe : CFSG.Open.IsElemAbelian 3 Fh :=
    ⟨⟨⟨fun a b => Subtype.ext (h.comm a a.2 b b.2)⟩⟩, fun x hx => h.three x hx⟩
  have hBe : CFSG.Open.IsElemAbelian 3 Bh := by
    rw [h.hB]
    exact isElemAbelian_Z c₀ (by
      by_cases h1 : c₀ = 1
      · rw [h1]; simp
      · have := (h.hc₀ h1).1.orderOf
        rw [← this]
        exact pow_orderOf_eq_one c₀)
  exact fun x hx y hy => (CFSG.Open.IsElemAbelian.sup_of_commute hFe hBe h.fb_comm).comm hx hy

theorem cen_assemble {Y : Type} [Group Y] [Finite Y] (φ : Y ≃* alternatingGroup (Fin 13))
    {Abar : Subgroup Y} {Fh Bh : Subgroup (Perm (Fin 13))} {c₀ : Perm (Fin 13)}
    (hcfg : Cfg13 Fh Bh c₀)
    (hAmap : Abar.map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom) = Fh ⊔ Bh)
    {x : Y} (hx : x ∈ Abar) (hx1 : x ≠ 1) :
    ∃ Q : Subgroup Y, IsSylowIn 3 ⊤ Q ∧ Abar ≤ Q ∧ x ∈ centerOf Q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ι : Y →* Perm (Fin 13) := (alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιsurj : ∀ σ ∈ alternatingGroup (Fin 13), ∃ y : Y, ι y = σ := fun σ hσ =>
    ⟨φ.symm ⟨σ, hσ⟩, by
      show ((φ (φ.symm ⟨σ, hσ⟩) : alternatingGroup (Fin 13)) : Perm (Fin 13)) = σ
      rw [MulEquiv.apply_symm_apply]⟩
  have hιx : ι x ∈ Fh ⊔ Bh := hAmap ▸ Subgroup.mem_map_of_mem ι hx
  have hιx1 : ι x ≠ 1 := fun h => hx1 (hιinj (h.trans (map_one ι).symm))
  have hX3 : ∀ y ∈ Fh ⊔ Bh, y ^ 3 = 1 := fun y hy => hcfg.pow_three_sup hy
  have hXp : IsPGroup 3 ↥(Fh ⊔ Bh) := isPGroup_three_of_pow_three hX3
  obtain ⟨P, hPp, hXP, hPc, hP5⟩ := exists_threeGroup_cent (hX3 _ hιx)
    (hcfg.supp_card hιx hιx1) hXp (fun y hy => hcfg.comm_sup y hy _ hιx)
  have hPalt : P ≤ alternatingGroup (Fin 13) := mem_alt_of_isPGroup_three hPp
  set Q : Subgroup Y := P.comap ι with hQ
  have hQP : Q.map ι = P := by
    rw [hQ, Subgroup.map_comap_eq]
    refine inf_eq_right.2 (show P ≤ ι.range from fun p hp => ?_)
    obtain ⟨y, hy⟩ := hιsurj p (hPalt hp)
    exact ⟨y, hy⟩
  have hQcard : Nat.card Q = Nat.card P := by
    rw [← hQP, Subgroup.card_map_of_injective hιinj]
  have hQp : IsPGroup 3 Q := hPp.comap_of_injective ι hιinj
  have hfac : (Nat.card Y).factorization 3 = 5 := by
    rw [Nat.card_congr φ.toEquiv]
    exact Prop127.card_alt13_factorization
  have hQ5 : Nat.card Q = 3 ^ 5 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQp
    have hn5 : 5 ≤ n := by
      have h1 : 3 ^ 5 ≤ 3 ^ n := by rw [← hn, hQcard]; exact hP5
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    have hdvd : 3 ^ n ∣ Nat.card Y := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card Q
    have hne : Nat.card Y ≠ 0 := Nat.card_pos.ne'
    have hn5' : n ≤ 5 := by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).1 hdvd
      omega
    rw [hn, show n = 5 by omega]
  have hQsyl : IsSylowIn 3 ⊤ Q := by
    refine ⟨le_top, hQp, Lemma1210.isMax_of_card_threePart le_top ?_⟩
    rw [Subgroup.card_top, hfac]
    exact hQ5
  have hAbarQ : Abar ≤ Q := by
    intro y hy
    have : ι y ∈ P := hXP (hAmap ▸ Subgroup.mem_map_of_mem ι hy)
    exact this
  refine ⟨Q, hQsyl, hAbarQ, ?_⟩
  refine Subgroup.mem_map.2 ⟨⟨x, hAbarQ hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  show (q : Y) * x = x * (q : Y)
  apply hιinj
  have h1 : ι (q : Y) * ι x = ι x * ι (q : Y) := hPc _ q.2
  rw [map_mul, map_mul]
  exact h1

theorem input1210_cen'_holds :
    ∀ (G : Type) [Group G] [Finite G] (N K E A F : Subgroup G) (a : G)
      (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))),
      A ≤ N → barX 3 N A ≤ barX 3 N K → Lemma129IvAOrbit φ E A → Lemma129IvAComplement φ A F a →
      ∀ x ∈ (barX 3 N A).subgroupOf (barX 3 N K), x ≠ 1 →
        ∃ Q : Subgroup ↥(barX 3 N K), IsSylowIn 3 ⊤ Q ∧
          (barX 3 N A).subgroupOf (barX 3 N K) ≤ Q ∧ x ∈ centerOf Q := by
  intro G _ _ N K E A F a φ hAN hAK hOrb hF x hx hx1
  obtain ⟨hEk, hFix, hreg, haA, hAeq, -, hBth⟩ := hF
  obtain ⟨c₀, hcfg, hAmap⟩ := config_unpack ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)
    (Subtype.val_injective.comp φ.injective) _ _ rfl rfl hAN hAK hEk haA hAeq hFix hreg hBth
  exact cen_assemble φ hcfg hAmap hx hx1

end CenProof

section Sigma13

open Equiv Equiv.Perm
open scoped Classical

variable {Fh : Subgroup (Perm (Fin 13))}

theorem orb_mem' (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x) {ω : Fin 13} (hω : ω ∈ moved Fh)
    (g : ↥Fh) : (g : Perm (Fin 13)) ω ∈ moved Fh := by
  obtain ⟨h, hh, hne⟩ := hω
  refine ⟨h, hh, ?_⟩
  have hc : h ((g : Perm (Fin 13)) ω) = (g : Perm (Fin 13)) (h ω) := by
    have := congrArg (fun x : Perm (Fin 13) => x ω) (hcomm h hh g g.2)
    simpa using this
  rw [hc]
  intro heq
  exact hne ((g : Perm (Fin 13)).injective heq)

@[expose] def orbMap' (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x) {ω : Fin 13}
    (hω : ω ∈ moved Fh) : ↥Fh → {j // j ∈ moved Fh} :=
  fun g => ⟨(g : Perm (Fin 13)) ω, orb_mem' hcomm hω g⟩

theorem orbMap'_bijective (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
    {ω : Fin 13} (hω : ω ∈ moved Fh) : Function.Bijective (orbMap' hcomm hω) := by
  constructor
  · intro g g' hgg'
    have hk : ((g : Perm (Fin 13)) ω) ∈ moved Fh := orb_mem' hcomm hω g
    obtain ⟨x, -, hx⟩ := hreg ω ((g : Perm (Fin 13)) ω) hω hk
    have h1 := hx g ⟨g.2, rfl⟩
    have h2 := hx g' ⟨g'.2, (congrArg Subtype.val hgg').symm⟩
    exact Subtype.ext (h1.trans h2.symm)
  · rintro ⟨k, hk⟩
    obtain ⟨x, ⟨hxF, hxk⟩, -⟩ := hreg ω k hω hk
    exact ⟨⟨x, hxF⟩, Subtype.ext hxk⟩

@[expose] noncomputable def sigmaOf' (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
    (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
      ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
    {ω : Fin 13} (hω : ω ∈ moved Fh) (α : MulAut ↥Fh) : Perm (Fin 13) :=
  Equiv.Perm.extendDomain (α.toEquiv : Perm ↥Fh)
    (Equiv.ofBijective (orbMap' hcomm hω) (orbMap'_bijective hcomm hreg hω))

section SigmaProps

variable (hcomm : ∀ x ∈ Fh, ∀ y ∈ Fh, x * y = y * x)
  (hreg : ∀ j k : Fin 13, (∃ g ∈ Fh, g j ≠ j) → (∃ g ∈ Fh, g k ≠ k) →
    ∃! g : Perm (Fin 13), g ∈ Fh ∧ g j = k)
  {ω : Fin 13} (hω : ω ∈ moved Fh) (α : MulAut ↥Fh)

theorem sigma'_apply_orb (g : ↥Fh) :
    sigmaOf' hcomm hreg hω α ((g : Perm (Fin 13)) ω) = ((α g : ↥Fh) : Perm (Fin 13)) ω := by
  unfold sigmaOf'
  exact Equiv.Perm.extendDomain_apply_image (α.toEquiv : Perm ↥Fh)
    (Equiv.ofBijective (orbMap' hcomm hω) (orbMap'_bijective hcomm hreg hω)) g

theorem sigma'_apply_of_not_moved {j : Fin 13} (hj : j ∉ moved Fh) :
    sigmaOf' hcomm hreg hω α j = j := by
  unfold sigmaOf'
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hj

theorem sigma'_mul_comm (g : ↥Fh) :
    sigmaOf' hcomm hreg hω α * (g : Perm (Fin 13)) =
      ((α g : ↥Fh) : Perm (Fin 13)) * sigmaOf' hcomm hreg hω α := by
  ext j
  by_cases hj : j ∈ moved Fh
  · obtain ⟨h, hh⟩ := (orbMap'_bijective hcomm hreg hω).2 ⟨j, hj⟩
    have hhj : (h : Perm (Fin 13)) ω = j := congrArg Subtype.val hh
    subst hhj
    have h1 := sigma'_apply_orb hcomm hreg hω α (g * h)
    have h2 := sigma'_apply_orb hcomm hreg hω α h
    simp only [Subgroup.coe_mul, map_mul, Perm.coe_mul, Function.comp_apply] at h1 ⊢
    rw [h1, h2]
  · rw [Perm.mul_apply, Perm.mul_apply, not_moved_fix' g.2 hj,
      sigma'_apply_of_not_moved hcomm hreg hω α hj, not_moved_fix' (α g).2 hj]

theorem sigma'_conj (g : ↥Fh) :
    sigmaOf' hcomm hreg hω α * (g : Perm (Fin 13)) * (sigmaOf' hcomm hreg hω α)⁻¹ =
      ((α g : ↥Fh) : Perm (Fin 13)) := by
  rw [sigma'_mul_comm hcomm hreg hω α g]
  group

theorem sigma'_mem_moved {j : Fin 13} (hj : j ∈ moved Fh) :
    sigmaOf' hcomm hreg hω α j ∈ moved Fh := by
  obtain ⟨h, hh⟩ := (orbMap'_bijective hcomm hreg hω).2 ⟨j, hj⟩
  have hhj : (h : Perm (Fin 13)) ω = j := congrArg Subtype.val hh
  rw [← hhj, sigma'_apply_orb]
  exact orb_mem' hcomm hω _

theorem sigma'_commute_of_fix {x : Perm (Fin 13)} (hx : ∀ j ∈ moved Fh, x j = j) :
    sigmaOf' hcomm hreg hω α * x = x * sigmaOf' hcomm hreg hω α := by
  ext j
  by_cases hj : j ∈ moved Fh
  · rw [Perm.mul_apply, Perm.mul_apply, hx j hj, hx _ (sigma'_mem_moved hcomm hreg hω α hj)]
  · have hxj : x j ∉ moved Fh := by
      intro hm
      apply hj
      have := hx _ hm
      rw [← x.injective this]
      exact hm
    rw [Perm.mul_apply, Perm.mul_apply, sigma'_apply_of_not_moved hcomm hreg hω α hj,
      sigma'_apply_of_not_moved hcomm hreg hω α hxj]

theorem sigma'_pow_three (hα : α ^ 3 = 1) : sigmaOf' hcomm hreg hω α ^ 3 = 1 := by
  ext j
  by_cases hj : j ∈ moved Fh
  · obtain ⟨h, hh⟩ := (orbMap'_bijective hcomm hreg hω).2 ⟨j, hj⟩
    have hhj : (h : Perm (Fin 13)) ω = j := congrArg Subtype.val hh
    subst hhj
    have e1 := sigma'_apply_orb hcomm hreg hω α h
    have e2 := sigma'_apply_orb hcomm hreg hω α (α h)
    have e3 := sigma'_apply_orb hcomm hreg hω α (α (α h))
    have hα3 : α (α (α h)) = h := by
      have := congrArg (fun β : MulAut ↥Fh => β h) hα
      simpa [pow_succ, MulAut.mul_apply] using this
    rw [pow_succ, pow_two, Perm.mul_apply, Perm.mul_apply, e1, e2, e3, hα3]
    rfl
  · have : ∀ n : ℕ, (sigmaOf' hcomm hreg hω α ^ n) j = j := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ, Perm.mul_apply, sigma'_apply_of_not_moved hcomm hreg hω α hj, ih]
    rw [this 3]
    rfl

end SigmaProps

end Sigma13

section Transvection

theorem zmod3_triple : ∀ a : ZMod 3, a + a + a = 0 := by decide

theorem exists_coord_functional {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (hfr : Module.finrank (ZMod 3) V = 2) {f w : V} (hw : w ≠ 0)
    (hfw : ∀ a : ZMod 3, a • w ≠ f) :
    ∃ c : V →ₗ[ZMod 3] ZMod 3, c w = 0 ∧ c f = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hli : LinearIndependent (ZMod 3) ![w, f] := (LinearIndependent.pair_iff' hw).2 hfw
  let b : Module.Basis (Fin 2) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp [hfr])
  have hb0 : b 0 = w := by simp [b]
  have hb1 : b 1 = f := by simp [b]
  refine ⟨b.coord 1, ?_, ?_⟩
  · rw [← hb0, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  · rw [← hb1, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp

theorem exists_transvection {H : Type} [CommGroup H] [Finite H] (h3 : ∀ x : H, x ^ 3 = 1)
    (hc : Nat.card H = 9) {f w : H} (hw : w ≠ 1) (hfw : f ∉ Subgroup.zpowers w) :
    ∃ α : MulAut H, α f = f * w ∧ α ^ 3 = 1 ∧ ∀ g : H, g⁻¹ * α g ∈ Subgroup.zpowers w := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Module (ZMod 3) (Additive H) := AddCommGroup.zmodModule (fun x => by
    have : x = Additive.ofMul (Additive.toMul x) := rfl
    rw [this, ← ofMul_pow, h3, ofMul_one])
  haveI : Finite (Additive H) := inferInstanceAs (Finite H)
  haveI : Module.Finite (ZMod 3) (Additive H) := Module.Finite.of_finite
  have hcard : Nat.card (Additive H) = 9 := hc
  have hfr : Module.finrank (ZMod 3) (Additive H) = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive H)
    rw [hcard, Nat.card_zmod] at h
    have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
    rw [h9] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h).symm
  have hsmul : ∀ a : ZMod 3, a • Additive.ofMul w = Additive.ofMul (w ^ a.val) := by
    intro a
    have : a • Additive.ofMul w = a.val • Additive.ofMul w := by
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      exact Nat.cast_smul_eq_nsmul (ZMod 3) a.val _
    rw [this, ofMul_pow]
  have hw0 : Additive.ofMul w ≠ 0 := fun h => hw (Additive.ofMul.injective (h.trans ofMul_one.symm))
  have hnot : ∀ a : ZMod 3, a • Additive.ofMul w ≠ Additive.ofMul f := by
    intro a ha
    apply hfw
    rw [hsmul] at ha
    have : w ^ a.val = f := Additive.ofMul.injective ha
    rw [← this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _
  obtain ⟨c, hcw, hcf⟩ := exists_coord_functional hfr hw0 hnot
  let T : Additive H ≃ₗ[ZMod 3] Additive H :=
    LinearEquiv.ofLinear (LinearMap.id + c.smulRight (Additive.ofMul w))
      (LinearMap.id - c.smulRight (Additive.ofMul w))
      (by
        ext v
        simp [hcw])
      (by
        ext v
        simp [hcw])
  have hTv : ∀ v : Additive H, T v = v + c v • Additive.ofMul w := fun v => by
    simp [T]
  have hcT : ∀ v : Additive H, c (T v) = c v := fun v => by
    rw [hTv, map_add, map_smul, hcw]
    simp
  refine ⟨{ toFun := fun x => Additive.toMul (T (Additive.ofMul x))
            invFun := fun x => Additive.toMul (T.symm (Additive.ofMul x))
            left_inv := fun x => by simp
            right_inv := fun x => by simp
            map_mul' := fun x y => by
              simp [ofMul_mul, map_add, toMul_add] }, ?_, ?_, ?_⟩
  · show Additive.toMul (T (Additive.ofMul f)) = f * w
    rw [hTv, hcf, one_smul]
    rfl
  · have hT3 : ∀ v : Additive H, T (T (T v)) = v := by
      intro v
      rw [hTv (T (T v)), hcT, hcT, hTv (T v), hcT, hTv v]
      have h3' : ∀ a : ZMod 3, a + a + a = 0 := zmod3_triple
      have : c v • Additive.ofMul w + c v • Additive.ofMul w + c v • Additive.ofMul w = 0 := by
        rw [← add_smul, ← add_smul, h3', zero_smul]
      calc v + c v • Additive.ofMul w + c v • Additive.ofMul w + c v • Additive.ofMul w
          = v + (c v • Additive.ofMul w + c v • Additive.ofMul w + c v • Additive.ofMul w) := by abel
        _ = v := by rw [this, add_zero]
    ext x
    show Additive.toMul (T (Additive.ofMul (Additive.toMul (T (Additive.ofMul (Additive.toMul
      (T (Additive.ofMul x)))))))) = x
    simp [hT3]
  · intro g
    show g⁻¹ * Additive.toMul (T (Additive.ofMul g)) ∈ Subgroup.zpowers w
    rw [hTv, toMul_add, hsmul]
    simp only [toMul_ofMul]
    rw [← mul_assoc, inv_mul_cancel, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers w) _

end Transvection

section PermShear

open Equiv Equiv.Perm
open scoped Classical

variable {Fh Bh : Subgroup (Perm (Fin 13))} {c₀ : Perm (Fin 13)}

theorem Cfg13.exists_moved (h : Cfg13 Fh Bh c₀) : ∃ ω : Fin 13, ω ∈ moved Fh := by
  by_contra hcon
  push Not at hcon
  have : {j : Fin 13 | ∀ g ∈ Fh, g j = j} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro j g hg
    by_contra hne
    exact hcon j ⟨g, hg, hne⟩
  have h4 := h.fix4
  rw [this, Set.ncard_univ] at h4
  simp at h4

theorem Cfg13.card_Fh (h : Cfg13 Fh Bh c₀) : Nat.card Fh = 9 := by
  obtain ⟨ω, hω⟩ := h.exists_moved
  have hbij := orbMap'_bijective h.comm h.reg hω
  have h1 : Nat.card ↥Fh = Nat.card {j // j ∈ moved Fh} :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [h1, Nat.card_coe_set_eq]
  exact h.card_moved

theorem Cfg13.moved_pres (h : Cfg13 Fh Bh c₀) {x : Perm (Fin 13)} (hx : x ∈ Fh ⊔ Bh) {j : Fin 13} :
    j ∈ moved Fh ↔ x j ∈ moved Fh := by
  obtain ⟨f, hf, c, hc, rfl⟩ := h.exists_mul hx
  rw [Perm.mul_apply]
  constructor
  · intro hj
    rw [h.bfix c hc j hj]
    exact orb_mem' h.comm hj ⟨f, hf⟩
  · intro hj
    by_contra hnj
    have hcjn : c j ∉ moved Fh := by
      intro hcm
      have h1 := h.bfix c hc (c j) hcm
      have h2 : c j = j := c.injective h1
      exact hnj (h2 ▸ hcm)
    have := not_moved_fix' hf hcjn
    rw [this] at hj
    exact hcjn hj

theorem card_eq_orbit_mul_stab (Z : Subgroup (Perm (Fin 13))) (i : Fin 13) :
    Nat.card Z = Set.ncard (MulAction.orbit Z i) * Nat.card (MulAction.stabilizer Z i) := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer Z i)
  rw [MulAction.index_stabilizer] at h
  rw [← h, mul_comm]

theorem Cfg13.zh_regular (h : Cfg13 Fh Bh c₀) {Zh : Subgroup (Perm (Fin 13))} (hZle : Zh ≤ Fh ⊔ Bh)
    (hZcard : Nat.card Zh ≤ 9) (hZorb : ∃ i : Fin 13, Set.ncard (MulAction.orbit Zh i) = 9) :
    Nat.card Zh = 9 ∧ ∀ c ∈ Bh, c ∈ Zh → c = 1 := by
  obtain ⟨i, hi⟩ := hZorb
  have hsub : ∀ k ∈ MulAction.orbit Zh i, (i ∈ moved Fh ↔ k ∈ moved Fh) := by
    rintro _ ⟨x, rfl⟩
    exact h.moved_pres (hZle x.2)
  have himoved : i ∈ moved Fh := by
    by_contra hni
    have hsubc : MulAction.orbit Zh i ⊆ {j : Fin 13 | ∀ g ∈ Fh, g j = j} := by
      intro k hk g hg
      have : k ∉ moved Fh := fun hkm => hni ((hsub k hk).2 hkm)
      exact not_moved_fix' hg this
    have := Set.ncard_le_ncard hsubc (Set.toFinite _)
    rw [hi, h.fix4] at this
    omega
  have hcardmoved : Set.ncard (moved Fh) = 9 := h.card_moved
  have horbeq : MulAction.orbit Zh i = moved Fh := by
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [hi, hcardmoved]) (Set.toFinite _)
    intro k hk
    exact (hsub k hk).1 himoved
  have hos := card_eq_orbit_mul_stab Zh i
  rw [hi] at hos
  have hpos : 0 < Nat.card (MulAction.stabilizer Zh i) := Nat.card_pos
  have hstab1 : Nat.card (MulAction.stabilizer Zh i) = 1 := by omega
  refine ⟨by omega, ?_⟩
  intro c hcB hcZ
  have hci : c i = i := h.bfix c hcB i himoved
  have hmem : (⟨c, hcZ⟩ : Zh) ∈ MulAction.stabilizer Zh i := by
    rw [MulAction.mem_stabilizer_iff]
    exact hci
  have hsub1 : Subsingleton (MulAction.stabilizer Zh i) := (Nat.card_eq_one_iff_unique.1 hstab1).1
  have : (⟨⟨c, hcZ⟩, hmem⟩ : MulAction.stabilizer Zh i) = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun t : MulAction.stabilizer Zh i => ((t : Zh) : Perm (Fin 13))) this
  simpa using h2

theorem Cfg13.card_Bh_le (h : Cfg13 Fh Bh c₀) : Nat.card Bh ≤ 3 := by
  rw [h.hB, Nat.card_zpowers]
  by_cases h1 : c₀ = 1
  · rw [h1, orderOf_one]; norm_num
  · rw [(h.hc₀ h1).1.orderOf]

theorem Cfg13.card_sup_le (h : Cfg13 Fh Bh c₀) : Nat.card ↥(Fh ⊔ Bh) ≤ 27 := by
  have h1 := card_sup_mul_card_inf Fh Bh h.fb_comm
  rw [h.card_Fh] at h1
  have h2 : 0 < Nat.card ↥(Fh ⊓ Bh) := Nat.card_pos
  have h3 := h.card_Bh_le
  have h4 : Nat.card ↥(Fh ⊔ Bh) ≤ Nat.card ↥(Fh ⊔ Bh) * Nat.card ↥(Fh ⊓ Bh) :=
    Nat.le_mul_of_pos_right _ h2
  omega

theorem Cfg13.exists_w (h : Cfg13 Fh Bh c₀) {Zh : Subgroup (Perm (Fin 13))} (hZle : Zh ≤ Fh ⊔ Bh)
    (hZc9 : Nat.card Zh = 9) : ∃ w ∈ Zh ⊓ Fh, w ≠ 1 := by
  have hc : ∀ x ∈ Zh, ∀ y ∈ Fh, x * y = y * x := fun x hx y hy =>
    h.comm_sup x (hZle hx) y (Subgroup.mem_sup_left hy)
  have h1 := card_sup_mul_card_inf Zh Fh hc
  rw [hZc9, h.card_Fh] at h1
  have h2 : Nat.card ↥(Zh ⊔ Fh) ≤ 27 :=
    (Subgroup.card_le_of_le (sup_le hZle le_sup_left)).trans h.card_sup_le
  by_contra hcon
  push Not at hcon
  have hbot : Zh ⊓ Fh = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    exact hcon
  rw [hbot, Subgroup.card_bot] at h1
  omega

theorem perm_shear (h : Cfg13 Fh Bh c₀) {Zh : Subgroup (Perm (Fin 13))} (hZle : Zh ≤ Fh ⊔ Bh)
    (hZcard : Nat.card Zh ≤ 9) (hZorb : ∃ i : Fin 13, Set.ncard (MulAction.orbit Zh i) = 9)
    {z : Perm (Fin 13)} (hz : z ∈ Zh) (hzF : z ∉ Fh) :
    ∃ σ ∈ alternatingGroup (Fin 13), (∀ x ∈ Fh ⊔ Bh, σ * x * σ⁻¹ ∈ Fh ⊔ Bh) ∧
      (∀ x ∈ Zh, σ * x * σ⁻¹ ∈ Zh) ∧ ∃ f ∈ Fh, f ≠ 1 ∧ σ⁻¹ * z * σ = z * f := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ9, hZB⟩ := h.zh_regular hZle hZcard hZorb
  obtain ⟨f₀, hf₀, c, hc, hzfc⟩ := h.exists_mul (hZle hz)
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hzfc
    exact hzF (hzfc ▸ hf₀)
  have hf₀1 : f₀ ≠ 1 := by
    rintro rfl
    rw [one_mul] at hzfc
    exact hc1 (hZB c hc (hzfc ▸ hz))
  obtain ⟨w, hwZF, hw1⟩ := h.exists_w hZle hZ9
  have hwZ : w ∈ Zh := hwZF.1
  have hwF : w ∈ Fh := hwZF.2
  have hfw : f₀ ∉ Subgroup.zpowers w := by
    intro hmem
    have hf₀Z : f₀ ∈ Zh := (Subgroup.zpowers_le.2 hwZ) hmem
    have hcZ : c ∈ Zh := by
      have : c = f₀⁻¹ * z := by rw [← hzfc]; group
      rw [this]
      exact Zh.mul_mem (Zh.inv_mem hf₀Z) hz
    exact hc1 (hZB c hc hcZ)
  letI : CommGroup ↥Fh :=
    { (inferInstance : Group ↥Fh) with mul_comm := fun x y => Subtype.ext (h.comm x x.2 y y.2) }
  have hF3 : ∀ x : ↥Fh, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using h.three x x.2)
  obtain ⟨α, hαf, hα3, hαg⟩ := exists_transvection (H := ↥Fh) hF3 h.card_Fh
    (f := ⟨f₀, hf₀⟩) (w := ⟨w, hwF⟩) (fun h1 => hw1 (congrArg Subtype.val h1)) (by
      intro hmem
      apply hfw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩)
  obtain ⟨ω, hω⟩ := h.exists_moved
  set σ := sigmaOf' h.comm h.reg hω α with hσ
  have hσconj : ∀ g : ↥Fh, σ * (g : Perm (Fin 13)) * σ⁻¹ = ((α g : ↥Fh) : Perm (Fin 13)) :=
    fun g => sigma'_conj h.comm h.reg hω α g
  have hσc : ∀ c' ∈ Bh, σ * c' = c' * σ := fun c' hc' =>
    sigma'_commute_of_fix h.comm h.reg hω α (h.bfix c' hc')
  have hσ3 : σ ^ 3 = 1 := sigma'_pow_three h.comm h.reg hω α hα3
  have hσalt : σ ∈ alternatingGroup (Fin 13) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 := congrArg Equiv.Perm.sign hσ3
    rw [map_pow, map_one] at h1
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hconjFB : ∀ (g : ↥Fh), ∀ c' ∈ Bh, σ * ((g : Perm (Fin 13)) * c') * σ⁻¹ =
      ((α g : ↥Fh) : Perm (Fin 13)) * c' := by
    intro g c' hc'
    have e : σ * ((g : Perm (Fin 13)) * c') * σ⁻¹ = (σ * g * σ⁻¹) * (σ * c' * σ⁻¹) := by group
    rw [e, hσconj g, hσc c' hc']
    group
  refine ⟨σ, hσalt, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, c', hc', rfl⟩ := h.exists_mul hx
    have := hconjFB ⟨f, hf⟩ c' hc'
    simp only at this
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (α ⟨f, hf⟩).2) (Subgroup.mem_sup_right hc')
  · intro x hx
    obtain ⟨f, hf, c', hc', rfl⟩ := h.exists_mul (hZle hx)
    have h1 := hconjFB ⟨f, hf⟩ c' hc'
    simp only at h1
    rw [h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hαg ⟨f, hf⟩)
    have hk' : (f : Perm (Fin 13))⁻¹ * ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) = w ^ k := by
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at this
      exact this.symm
    have hαf' : ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) = f * w ^ k := by
      rw [← hk']
      group
    have hwk : w ^ k ∈ Fh := Fh.zpow_mem hwF k
    have hcomm : c' * w ^ k = w ^ k * c' := (h.fb_comm _ hwk c' hc').symm
    have e : ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) * c' = (f * c') * w ^ k := by
      rw [hαf', mul_assoc, mul_assoc, hcomm]
    rw [e]
    exact Zh.mul_mem hx (Zh.zpow_mem hwZ k)
  ·
    set g₀ : ↥Fh := ⟨f₀, hf₀⟩ with hg₀
    set g₁ : ↥Fh := α⁻¹ g₀ with hg₁
    have hσg₁ : σ * (g₁ : Perm (Fin 13)) * σ⁻¹ = f₀ := by
      rw [hσconj g₁, hg₁]
      simp [hg₀]
    have hσinvf : σ⁻¹ * f₀ * σ = (g₁ : Perm (Fin 13)) := by
      rw [← hσg₁]
      group
    have hσinvc : σ⁻¹ * c * σ = c := by
      have := hσc c hc
      calc σ⁻¹ * c * σ = σ⁻¹ * (c * σ) := by group
        _ = σ⁻¹ * (σ * c) := by rw [this]
        _ = c := by group
    refine ⟨f₀⁻¹ * (g₁ : Perm (Fin 13)), Fh.mul_mem (Fh.inv_mem hf₀) g₁.2, ?_, ?_⟩
    · intro h1
      have h2 : (g₁ : Perm (Fin 13)) = f₀ := by
        have := congrArg (fun t => f₀ * t) h1
        simpa using this
      have h3 : g₁ = g₀ := Subtype.ext h2
      have h4 : α g₀ = g₀ := by
        have := congrArg α h3
        rw [hg₁] at this
        simpa using this.symm
      rw [hαf] at h4
      have h5 : (⟨w, hwF⟩ : ↥Fh) = 1 :=
        mul_left_cancel (a := g₀) (h4.trans (mul_one g₀).symm)
      exact hw1 (congrArg Subtype.val h5)
    · have hcg : c * (g₁ : Perm (Fin 13)) = (g₁ : Perm (Fin 13)) * c := (h.fb_comm _ g₁.2 c hc).symm
      have hcf : c * f₀⁻¹ = f₀⁻¹ * c := (h.fb_comm _ (Fh.inv_mem hf₀) c hc).symm
      calc σ⁻¹ * z * σ = σ⁻¹ * (f₀ * c) * σ := by rw [hzfc]
        _ = (σ⁻¹ * f₀ * σ) * (σ⁻¹ * c * σ) := by group
        _ = (g₁ : Perm (Fin 13)) * c := by rw [hσinvf, hσinvc]
        _ = z * (f₀⁻¹ * (g₁ : Perm (Fin 13))) := by
          rw [← hzfc]
          calc (g₁ : Perm (Fin 13)) * c = f₀ * (f₀⁻¹ * (g₁ : Perm (Fin 13))) * c := by group
            _ = f₀ * ((f₀⁻¹ * (g₁ : Perm (Fin 13))) * c) := by group
            _ = f₀ * (c * (f₀⁻¹ * (g₁ : Perm (Fin 13)))) := by
              rw [(h.fb_comm _ (Fh.mul_mem (Fh.inv_mem hf₀) g₁.2) c hc)]
            _ = f₀ * c * (f₀⁻¹ * (g₁ : Perm (Fin 13))) := by group

end PermShear

section ShearProof

theorem shear_assemble {Y : Type} [Group Y] [Finite Y] (φ : Y ≃* alternatingGroup (Fin 13))
    {Abar Zbar Fbar : Subgroup Y} {Fh Bh : Subgroup (Equiv.Perm (Fin 13))} {c₀ : Equiv.Perm (Fin 13)}
    (hcfg : Cfg13 Fh Bh c₀)
    (hAmap : Abar.map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom) = Fh ⊔ Bh)
    (hFmap : Fbar.map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom) = Fh)
    (hZA : Zbar ≤ Abar)
    (hZcard : Nat.card ↥(Zbar.map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)) ≤ 9)
    (hZorb : ∃ i : Fin 13, Set.ncard (MulAction.orbit
      ↥(Zbar.map ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)) i) = 9)
    {z : Y} (hz : z ∈ Zbar) (hzF : z ∉ Fbar) :
    ∃ y : Y, (∀ x ∈ Abar, y * x * y⁻¹ ∈ Abar) ∧ (∀ x ∈ Zbar, y * x * y⁻¹ ∈ Zbar) ∧
      ∃ f ∈ Fbar, f ≠ 1 ∧ y⁻¹ * z * y = z * f := by
  set ι : Y →* Equiv.Perm (Fin 13) := (alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hZle : Zbar.map ι ≤ Fh ⊔ Bh := by
    rw [← hAmap]
    exact Subgroup.map_mono hZA
  have hzι : ι z ∈ Zbar.map ι := Subgroup.mem_map_of_mem ι hz
  have hzFι : ι z ∉ Fh := by
    intro hmem
    rw [← hFmap] at hmem
    obtain ⟨z', hz', hz'eq⟩ := Subgroup.mem_map.1 hmem
    exact hzF (hιinj hz'eq ▸ hz')
  obtain ⟨σ, hσalt, hσ1, hσ2, f, hfF, hf1, hrel⟩ :=
    perm_shear hcfg hZle hZcard hZorb hzι hzFι
  obtain ⟨y, hy⟩ : ∃ y : Y, ι y = σ := ⟨φ.symm ⟨σ, hσalt⟩, by
    show ((φ (φ.symm ⟨σ, hσalt⟩) : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = σ
    rw [MulEquiv.apply_symm_apply]⟩
  refine ⟨y, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · have h1 : ι x ∈ Fh ⊔ Bh := hAmap ▸ Subgroup.mem_map_of_mem ι hx
    have h2 := hσ1 _ h1
    rw [← hAmap] at h2
    obtain ⟨x'', hx'', hx''eq⟩ := Subgroup.mem_map.1 h2
    have : x'' = y * x * y⁻¹ := by
      apply hιinj
      rw [hx''eq, map_mul, map_mul, map_inv, hy]
    rw [← this]
    exact hx''
  · have h1 := Subgroup.mem_map_of_mem ι hx
    have h2 := hσ2 _ h1
    obtain ⟨x'', hx'', hx''eq⟩ := Subgroup.mem_map.1 h2
    have : x'' = y * x * y⁻¹ := by
      apply hιinj
      rw [hx''eq, map_mul, map_mul, map_inv, hy]
    rw [← this]
    exact hx''
  · rw [← hFmap] at hfF
    obtain ⟨f', hf', hf'eq⟩ := Subgroup.mem_map.1 hfF
    refine ⟨f', hf', ?_, ?_⟩
    · rintro rfl
      exact hf1 (hf'eq ▸ map_one ι)
    · apply hιinj
      rw [map_mul, map_mul, map_mul, map_inv, hy, hf'eq]
      exact hrel

theorem input1210_shear'_holds :
    ∀ (G : Type) [Group G] [Finite G] (N K E A F : Subgroup G) (a : G)
      (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))),
      A ≤ N → CFSG.Open.IsElemAbelian 3 A → CFSG.Open.pRank 3 (E ⊓ A) = 2 →
      barX 3 N A ≤ barX 3 N K → Lemma129IvAOrbit φ E A → Lemma129IvAComplement φ A F a →
      ∀ z ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K),
        z ∉ (barX 3 N F).subgroupOf (barX 3 N K) →
        ∃ y : ↥(barX 3 N K),
          (∀ x ∈ (barX 3 N A).subgroupOf (barX 3 N K),
            y * x * y⁻¹ ∈ (barX 3 N A).subgroupOf (barX 3 N K)) ∧
          (∀ x ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K),
            y * x * y⁻¹ ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K)) ∧
          ∃ f ∈ (barX 3 N F).subgroupOf (barX 3 N K), f ≠ 1 ∧ y⁻¹ * z * y = z * f := by
  intro G _ _ N K E A F a φ hAN hAe hE2 hAK hOrb hF z hz hzF
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEk, hFix, hreg, haA, hAeq, -, hBth⟩ := hF
  obtain ⟨c₀, hcfg, hAmap⟩ := config_unpack ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)
    (Subtype.val_injective.comp φ.injective) _ _ rfl rfl hAN hAK hEk haA hAeq hFix hreg hBth
  have hUN : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hbarU : barX 3 N (E ⊓ A) ≤ barX 3 N K :=
    (Lemma1210.barX_mono_left (inf_le_right : E ⊓ A ≤ A)).trans hAK
  have hUA : (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K) ≤ (barX 3 N A).subgroupOf (barX 3 N K) :=
    fun x hx => Subgroup.mem_subgroupOf.2
      (Lemma1210.barX_mono_left (inf_le_right : E ⊓ A ≤ A) (Subgroup.mem_subgroupOf.1 hx))
  have hUe : CFSG.Open.IsElemAbelian 3 (E ⊓ A) := Lemma1112.isElemAbelian_of_le hAe inf_le_right
  have hUcard : Nat.card ↥(E ⊓ A) = 9 := by
    rw [Lemma1112.card_eq_pow_pRank hUe, hE2]
    norm_num
  have hZcard : Nat.card ↥(((barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K)).map
      ((alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom)) ≤ 9 := by
    rw [Subgroup.card_map_of_injective (Subtype.val_injective.comp φ.injective),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarU).toEquiv, Lemma1210.barX_eq_map]
    have h1 : Nat.card ↥(((E ⊓ A).subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))) ∣
        Nat.card ↥((E ⊓ A).subgroupOf N) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥((E ⊓ A).subgroupOf N) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv, hUcard]
    rw [h2] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  exact shear_assemble φ hcfg hAmap rfl hUA hZcard hOrb hz hzF

end ShearProof

section Consumers

open Lemma1210

variable {G : Type} [Group G] [Finite G]

theorem sylow_central_of_cen' {m : ℕ} {B M E A N K F : Subgroup G} {a : G}
    (h : Sec11 G m 3 B M E A) (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A)
    (hAN : A ≤ N) (hKN : K ≤ N)
    (hAK : barX 3 N A ≤ barX 3 N K) (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13)))
    (hOrb : Lemma129IvAOrbit φ E A) (hF : Lemma129IvAComplement φ A F a)
    (hOut : Lemma1210.Input1210_Out13) {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) :
    ∃ Q : Subgroup G, IsSylowIn 3 N Q ∧ A ≤ Q ∧ x ∈ centerOf Q := by
  have hcen := input1210_cen'_holds
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYn : (barX 3 N K).Normal := Lemma1210.barX_normal_of_layer N K A hKN hAN hAK hL
  set O : Subgroup ↥N := GLAPPrimeCore 3 ↥N with hOdef
  have hAΓ : IsPGroup 3 ↥(A.subgroupOf N) := Lemma1210.isPGroup_subgroupOf_of_elemAb hAe hAN
  set xN : ↥N := ⟨x, hAN hx⟩ with hxN
  have hxA : xN ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 hx
  have hπx : QuotientGroup.mk' O xN ∈ barX 3 N A := by
    rw [Lemma1210.barX_eq_map]
    exact Subgroup.mem_map.2 ⟨xN, hxA, rfl⟩
  have hπx1 : QuotientGroup.mk' O xN ≠ 1 := by
    intro h1
    have hxO : xN ∈ O := (QuotientGroup.eq_one_iff xN).1 h1
    have hm : xN ∈ (A.subgroupOf N) ⊓ O := ⟨hxA, hxO⟩
    rw [Lemma1210.inf_eq_bot_of_coprime (Lemma1210.coprime_three_card_O N) hAΓ, Subgroup.mem_bot] at hm
    apply hx1
    have := congrArg Subtype.val hm
    simpa [hxN] using this
  obtain ⟨Qb0', hQb0'syl, hAQb0', hxQb0'⟩ := hcen G N K E A F a φ hAN hAK hOrb hF
    ⟨QuotientGroup.mk' O xN, hAK hπx⟩ (by
      show (⟨QuotientGroup.mk' O xN, hAK hπx⟩ : ↥(barX 3 N K)) ∈ (barX 3 N A).subgroupOf (barX 3 N K)
      exact Subgroup.mem_subgroupOf.2 hπx) (by
      intro h1
      apply hπx1
      exact congrArg Subtype.val h1)
  set Qb0 : Subgroup (↥N ⧸ O) := Qb0'.map (barX 3 N K).subtype with hQb0
  have hQb0p : IsPGroup 3 ↥Qb0 := Lemma1210.isPGroup_map_of_isPGroup (barX 3 N K).subtype hQb0'syl.2.1
  have hcardQb0 : Nat.card ↥Qb0 = 3 ^ (Nat.card ↥(barX 3 N K)).factorization 3 := by
    rw [hQb0, Subgroup.card_map_of_injective (barX 3 N K).subtype_injective]
    exact Lemma1210.card_of_isSylowIn_top hQb0'syl
  have hAT : A.subgroupOf N ≤ Qb0.comap (QuotientGroup.mk' O) := by
    intro a ha
    show QuotientGroup.mk' O a ∈ Qb0
    have hπa : QuotientGroup.mk' O a ∈ barX 3 N A := by
      rw [Lemma1210.barX_eq_map]
      exact Subgroup.mem_map.2 ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.2 ⟨⟨QuotientGroup.mk' O a, hAK hπa⟩, hAQb0' (Subgroup.mem_subgroupOf.2 hπa), rfl⟩
  obtain ⟨Q₀, hQ₀T, hQ₀p, hAQ₀, hQ₀map⟩ :=
    Lemma1210.exists_lift_sylow O (Lemma1210.coprime_three_card_O N) Qb0 hQb0p hAT hAΓ
  have hcardQ₀ : Nat.card ↥Q₀ = 3 ^ (Nat.card ↥N).factorization 3 := by
    have hcop : Nat.Coprime 3 (barX 3 N K).index :=
      Lemma1210.barX_index_coprime N K A hKN hAN hAK hL hAe hAmax φ hOut
    rw [← Lemma1210.card_map_mk_of_inf_eq_bot O Q₀ (Lemma1210.inf_eq_bot_of_coprime (Lemma1210.coprime_three_card_O N) hQ₀p),
      hQ₀map, hcardQb0, Lemma1210.factor_three_quotient O (Lemma1210.coprime_three_card_O N),
      Lemma1210.factor_three_eq_of_coprime (barX 3 N K) hcop]
  have hmaxN : ∀ R : Subgroup ↥N, R ≤ ⊤ → IsPGroup 3 ↥R → Q₀ ≤ R → R = Q₀ :=
    Lemma1210.isMax_of_card_threePart le_top (by rw [Subgroup.card_top]; exact hcardQ₀)
  have hcentQ₀ : ∀ q ∈ Q₀, xN * q = q * xN := by
    intro q hq
    have hxQ₀ : xN ∈ Q₀ := hAQ₀ hxA
    have hqb : QuotientGroup.mk' O q ∈ Qb0 := by
      rw [← hQ₀map]
      exact Subgroup.mem_map_of_mem _ hq
    have hcomm : ∀ y ∈ Qb0, QuotientGroup.mk' O xN * y = y * QuotientGroup.mk' O xN := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hxQb0'
      have hzx1 : ((z : ↥(Qb0')) : ↥(barX 3 N K)).1 = QuotientGroup.mk' O xN :=
        congrArg Subtype.val hzx
      have hz' := congrArg (fun t : ↥(barX 3 N K) => t.1)
        (congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩))
      simp only [Subgroup.coe_mul] at hz'
      rw [hzx1] at hz'
      exact hz'.symm
    have hqb' := hcomm _ hqb
    have hc1 : QuotientGroup.mk' O (xN * q * xN⁻¹ * q⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hqb']
      group
    have hc2 : xN * q * xN⁻¹ * q⁻¹ ∈ Q₀ :=
      Q₀.mul_mem (Q₀.mul_mem (Q₀.mul_mem hxQ₀ hq) (Q₀.inv_mem hxQ₀)) (Q₀.inv_mem hq)
    have hc3 : xN * q * xN⁻¹ * q⁻¹ = 1 := by
      have hm : xN * q * xN⁻¹ * q⁻¹ ∈ Q₀ ⊓ O := ⟨hc2, (QuotientGroup.eq_one_iff _).1 hc1⟩
      rw [Lemma1210.inf_eq_bot_of_coprime (Lemma1210.coprime_three_card_O N) hQ₀p, Subgroup.mem_bot] at hm
      exact hm
    calc xN * q = (xN * q * xN⁻¹ * q⁻¹) * (q * xN) := by group
      _ = q * xN := by rw [hc3, one_mul]
  refine ⟨Q₀.map N.subtype, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le Q₀, hQ₀p.map N.subtype, fun R' hR'N hR'p hQR' => ?_⟩
    have hR''p : IsPGroup 3 ↥(R'.subgroupOf N) :=
      hR'p.comap_of_injective N.subtype Subtype.val_injective
    have hQle : Q₀ ≤ R'.subgroupOf N := by
      intro q hq
      exact Subgroup.mem_subgroupOf.2 (hQR' (Subgroup.mem_map.2 ⟨q, hq, rfl⟩))
    have hEq := hmaxN (R'.subgroupOf N) le_top hR''p hQle
    rw [← hEq, Subgroup.subgroupOf_map_subtype, inf_of_le_left hR'N]
  · intro a ha
    exact Subgroup.mem_map.2 ⟨⟨a, hAN ha⟩, hAQ₀ (Subgroup.mem_subgroupOf.2 ha), rfl⟩
  · have hxQ : x ∈ Q₀.map N.subtype := Subgroup.mem_map.2 ⟨xN, hAQ₀ hxA, rfl⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    rintro ⟨g, hg⟩
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hg
    apply Subtype.ext
    exact (congrArg Subtype.val (hcentQ₀ q hq)).symm

theorem shear_lift' {m : ℕ} {B M E A N K F : Subgroup G} {a : G}
    (h : Sec11 G m 3 B M E A) (hAe : CFSG.Open.IsElemAbelian 3 A)
    (hA3 : CFSG.Open.pRank 3 A = 3) (hE2 : CFSG.Open.pRank 3 (E ⊓ A) = 2)
    (hAN : A ≤ N) (hKN : K ≤ N) (hAK : barX 3 N A ≤ barX 3 N K)
    (hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K)
    (φ : ↥(barX 3 N K) ≃* ↥(alternatingGroup (Fin 13))) (hOrb : Lemma129IvAOrbit φ E A)
    (hF : Lemma129IvAComplement φ A F a)
    {z : G} (hzA0 : z ∈ E ⊓ A) (hzF : z ∉ F) :
    ∃ y ∈ N ⊓ M ⊓ Subgroup.normalizer (A : Set G), ∃ f ∈ F, f ≠ 1 ∧ y⁻¹ * z * y = z * f := by
  have hShear := input1210_shear'_holds
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O : Subgroup ↥N := GLAPPrimeCore 3 ↥N with hOdef
  have hO : Nat.Coprime 3 (Nat.card O) := Lemma1210.coprime_three_card_O N
  have hAΓp : IsPGroup 3 ↥(A.subgroupOf N) := Lemma1210.isPGroup_subgroupOf_of_elemAb hAe hAN
  have hAΓe : CFSG.Open.IsElemAbelian 3 (A.subgroupOf N) := Lemma1210.isElemAbelian_subgroupOf hAe hAN
  have hAOΓ : (A.subgroupOf N) ⊓ O = ⊥ := Lemma1210.inf_eq_bot_of_coprime hO hAΓp
  have hFA : F ≤ A := hF.1.1
  have hFAΓ : F.subgroupOf N ≤ A.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hFA (Subgroup.mem_subgroupOf.1 hx))
  have hA0AΓ : (E ⊓ A).subgroupOf N ≤ A.subgroupOf N := fun x hx =>
    Subgroup.mem_subgroupOf.2 ((inf_le_right : E ⊓ A ≤ A) (Subgroup.mem_subgroupOf.1 hx))
  have hzA : z ∈ A := hzA0.2
  set zN : ↥N := ⟨z, hAN hzA⟩ with hzN
  have hzΓ : zN ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 hzA
  have hπz : QuotientGroup.mk' O zN ∈ barX 3 N A := by
    rw [Lemma1210.barX_eq_map]
    exact Subgroup.mem_map.2 ⟨zN, hzΓ, rfl⟩
  have hπzK : QuotientGroup.mk' O zN ∈ barX 3 N K := hAK hπz
  set zY : ↥(barX 3 N K) := ⟨QuotientGroup.mk' O zN, hπzK⟩ with hzY
  have hzY1 : zY ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K) := by
    apply Subgroup.mem_subgroupOf.2
    rw [Lemma1210.barX_eq_map]
    exact Subgroup.mem_map.2 ⟨zN, Subgroup.mem_subgroupOf.2 hzA0, rfl⟩
  have hzY2 : zY ∉ (barX 3 N F).subgroupOf (barX 3 N K) := by
    intro hmem
    apply hzF
    have hmem' : QuotientGroup.mk' O zN ∈ barX 3 N F := Subgroup.mem_subgroupOf.1 hmem
    rw [Lemma1210.barX_eq_map] at hmem'
    exact Subgroup.mem_subgroupOf.1 (Lemma1210.mem_of_mk_mem_map O hAOΓ hFAΓ hzΓ hmem')
  obtain ⟨yb, hyA, hyA0, fb, hfbF, hfb1, hrel⟩ :=
    hShear G N K E A F a φ hAN hAe hE2 hAK hOrb hF zY hzY1 hzY2
  set nb : ↥N ⧸ O := (yb : ↥N ⧸ O) with hnb
  have hnbA : ∀ xb ∈ (A.subgroupOf N).map (QuotientGroup.mk' O),
      nb * xb * nb⁻¹ ∈ (A.subgroupOf N).map (QuotientGroup.mk' O) := by
    intro xb hxb
    have hxbA : xb ∈ barX 3 N A := by rw [Lemma1210.barX_eq_map]; exact hxb
    have hxbK : xb ∈ barX 3 N K := hAK hxbA
    have h1 := hyA ⟨xb, hxbK⟩ (Subgroup.mem_subgroupOf.2 hxbA)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    rw [Lemma1210.barX_eq_map] at h2
    exact h2
  obtain ⟨mΓ, hmN, xb, hxb, hnbeq⟩ := Lemma1210.normalizer_lift O hO (A.subgroupOf N) hAΓp nb hnbA
  have hmiff : ∀ x : ↥N, x ∈ A.subgroupOf N ↔ mΓ⁻¹ * x * mΓ ∈ A.subgroupOf N :=
    fun x => Subgroup.mem_normalizer_iff''.1 hmN x
  have hmk : QuotientGroup.mk' O mΓ = xb⁻¹ * nb := by
    rw [hnbeq]
    group
  have hcommA : ∀ u ∈ (A.subgroupOf N).map (QuotientGroup.mk' O),
      ∀ v ∈ (A.subgroupOf N).map (QuotientGroup.mk' O), u * v = v * u := by
    intro u hu v hv
    obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.1 hu
    obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul, ← map_mul]
    exact congrArg (QuotientGroup.mk' O) (Lemma1210.elemAb_comm hAΓe hu' hv')
  have hkey : ∀ x : ↥N, x ∈ A.subgroupOf N →
      QuotientGroup.mk' O (mΓ⁻¹ * x * mΓ) = nb⁻¹ * QuotientGroup.mk' O x * nb := by
    intro x hx
    have hcx : xb * QuotientGroup.mk' O x = QuotientGroup.mk' O x * xb :=
      hcommA xb hxb _ (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    rw [map_mul, map_mul, map_inv, hmk]
    calc (xb⁻¹ * nb)⁻¹ * QuotientGroup.mk' O x * (xb⁻¹ * nb)
        = nb⁻¹ * xb * QuotientGroup.mk' O x * xb⁻¹ * nb := by group
      _ = nb⁻¹ * (xb * QuotientGroup.mk' O x) * xb⁻¹ * nb := by group
      _ = nb⁻¹ * (QuotientGroup.mk' O x * xb) * xb⁻¹ * nb := by rw [hcx]
      _ = nb⁻¹ * QuotientGroup.mk' O x * nb := by group
  have hB0conj : ∀ y ∈ barX 3 N (E ⊓ A), nb * y * nb⁻¹ ∈ barX 3 N (E ⊓ A) := by
    intro y hy
    have hyK : y ∈ barX 3 N K := hAK (Lemma1210.barX_mono_left inf_le_right hy)
    have h1 := hyA0 ⟨y, hyK⟩ (Subgroup.mem_subgroupOf.2 hy)
    have h2 := Subgroup.mem_subgroupOf.1 h1
    exact h2
  have hB0inv : ∀ y ∈ barX 3 N (E ⊓ A), nb⁻¹ * y * nb ∈ barX 3 N (E ⊓ A) :=
    Lemma1210.mem_conj_inv_of_conj_mem (barX 3 N (E ⊓ A)) nb hB0conj
  have hA0 : ∀ x ∈ (E ⊓ A).subgroupOf N, mΓ⁻¹ * x * mΓ ∈ (E ⊓ A).subgroupOf N := by
    intro x hx
    have hxA : x ∈ A.subgroupOf N := hA0AΓ hx
    have hconjA : mΓ⁻¹ * x * mΓ ∈ A.subgroupOf N := (hmiff x).1 hxA
    have himg : QuotientGroup.mk' O (mΓ⁻¹ * x * mΓ) ∈ barX 3 N (E ⊓ A) := by
      rw [hkey x hxA]
      exact hB0inv _ (by rw [Lemma1210.barX_eq_map]; exact Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    have himg' : QuotientGroup.mk' O (mΓ⁻¹ * x * mΓ) ∈ ((E ⊓ A).subgroupOf N).map
        (QuotientGroup.mk' O) := by
      rw [← Lemma1210.barX_eq_map]
      exact himg
    exact Lemma1210.mem_of_mk_mem_map O hAOΓ hA0AΓ hconjA himg'
  set mG : G := (mΓ : G) with hmG
  have hmG_N : mG ∈ N := mΓ.2
  have hmG_A : mG ∈ Subgroup.normalizer (A : Set G) := by
    apply Lemma1210.mem_normalizer_of_conj_inv_mem A mG
    intro x hx
    have hxN : x ∈ N := hAN hx
    have hxΓ : (⟨x, hxN⟩ : ↥N) ∈ A.subgroupOf N := Subgroup.mem_subgroupOf.2 hx
    have := Subgroup.mem_subgroupOf.1 ((hmiff ⟨x, hxN⟩).1 hxΓ)
    simpa [hmG] using this
  have hmG_A0 : mG ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    apply Lemma1210.mem_normalizer_of_conj_inv_mem (E ⊓ A) mG
    intro x hx
    have hxN : x ∈ N := hAN ((inf_le_right : E ⊓ A ≤ A) hx)
    have hxΓ : (⟨x, hxN⟩ : ↥N) ∈ (E ⊓ A).subgroupOf N := Subgroup.mem_subgroupOf.2 hx
    have := Subgroup.mem_subgroupOf.1 (hA0 _ hxΓ)
    simpa [hmG] using this
  have hmG_M : mG ∈ M := Lemma1210.normalizer_E_inf_le_M h hE2 hmG_A0
  set zp : ↥N := zN⁻¹ * (mΓ⁻¹ * zN * mΓ) with hzp
  have hzpA : zp ∈ A.subgroupOf N :=
    (A.subgroupOf N).mul_mem ((A.subgroupOf N).inv_mem hzΓ) ((hmiff zN).1 hzΓ)
  have hrelN : nb⁻¹ * QuotientGroup.mk' O zN * nb = QuotientGroup.mk' O zN * (fb : ↥N ⧸ O) :=
    congrArg Subtype.val hrel
  have hpi_zp : QuotientGroup.mk' O zp = (fb : ↥N ⧸ O) := by
    rw [hzp, map_mul, map_inv, hkey zN hzΓ, hrelN]
    group
  have hzpF : zp ∈ F.subgroupOf N := by
    apply Lemma1210.mem_of_mk_mem_map O hAOΓ hFAΓ hzpA
    rw [hpi_zp]
    have hf' : (fb : ↥N ⧸ O) ∈ barX 3 N F := Subgroup.mem_subgroupOf.1 hfbF
    rw [Lemma1210.barX_eq_map] at hf'
    exact hf'
  have hzp1 : (zp : G) ≠ 1 := by
    intro h1
    apply hfb1
    apply Subtype.ext
    have hzp0 : zp = 1 := Subtype.ext h1
    show (fb : ↥N ⧸ O) = 1
    rw [← hpi_zp, hzp0, map_one]
  refine ⟨mG, ⟨⟨hmG_N, hmG_M⟩, hmG_A⟩, (zp : G), Subgroup.mem_subgroupOf.1 hzpF, hzp1, ?_⟩
  have hz' : (zp : G) = z⁻¹ * (mG⁻¹ * z * mG) := by
    simp [hzp, hmG, hzN]
  rw [hz']
  group

end Consumers

end AltFacts

theorem lemma1210_holds : Lemma1210Statement := by
  have hOut := Prop127.input1210_out13_holds
  have hP2 := AltFacts.input1210_P2_holds
  have hCen := AltFacts.input1210_cen'_holds
  have hShear := AltFacts.input1210_shear'_holds
  intro G _ _ m p B M E A N D h K F a hK h3 φ hOrb hF
  obtain ⟨rfl, -, -, hbar⟩ := h3
  have h11 : Sec11 G m 3 B M E A := h.toSec11
  have hEA := lemma104_ii_holds h11.toSec10Fails h11.pair
  have hAe : CFSG.Open.IsElemAbelian 3 A := hEA.2.2.1
  have hAmax : ∀ S : Subgroup G, CFSG.Open.IsElemAbelian 3 S → A ≤ S → S = A :=
    fun S hS hAS => hEA.2.2.2 S le_top hS hAS
  have hA3 : CFSG.Open.pRank 3 A = 3 := hK.2.1.1
  have hE2 : CFSG.Open.pRank 3 (E ⊓ A) = 2 := hK.2.1.2
  have hcovK : ¬ Covers 3 N M K := hK.2.2.1
  have hKN : K ≤ N := hK.1.1
  have hL : GLAPLayer 3 N = ⨆ g ∈ A, GLBConj g K := hK.2.2.2.1
  have hAK : barX 3 N A ≤ barX 3 N K := hbar
  have hAN : A ≤ N := by
    intro x hx
    apply h.hD
    apply Lemma1210.mem_normalizer_of_conj_inv_mem D x
    intro d hd
    have hdA : d ∈ A := h.plane.1 hd
    have hc : x * d = d * x := Lemma1210.elemAb_comm hAe hx hdA
    have hx' : x⁻¹ * d * x = d := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hx']
    exact hd
  have hAnt : ∃ x ∈ A, x ≠ 1 := by
    obtain ⟨E0, hE0A, -, hcard⟩ := Lemma1210.exists_elemAb_pRank (p := 3) (by norm_num) A
    rw [hA3] at hcard
    by_contra hcon
    push Not at hcon
    have hbot : E0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact Subgroup.mem_bot.2 (hcon x (hE0A hx))
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨R, hRM, hER⟩ := Sec12c.prop126_exists_sylow h11
  have hAR : A ≤ R := le_trans le_sup_right hER
  have hne : ∃ x ∈ R, x ≠ 1 := by
    obtain ⟨x, hxA, hx1⟩ := hAnt
    exact ⟨x, hAR hxA, hx1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hzR, hz3⟩ := Lemma1210.exists_central_prime hRM.2.1 hne
  have hzEA : z ∈ E ⊓ A := Sec12c.prop126_central_mem h11 hER hzR hz3
  have hzA : z ∈ A := hzEA.2
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz3
    norm_num at hz3
  have hzPC : IsPCentralIn 3 M z := ⟨R, hRM, hzR⟩
  have hsyl : ∀ x ∈ A, x ≠ 1 →
      ∃ Q : Subgroup G, IsSylowIn 3 N Q ∧ x ∈ centerOf Q ∧ A ≤ Q ∧ ¬ Q ≤ M := by
    intro x hxA hx1
    obtain ⟨Q, hQN, hAQ, hxQ⟩ :=
      AltFacts.sylow_central_of_cen' h11 hAe hAmax hAN hKN hAK hL φ hOrb hF hOut hxA hx1
    exact ⟨Q, hQN, hxQ, hAQ,
      Lemma1210.not_le_of_sylow_contains_A h11 hA3 hAe hAmax hAN hKN hAK hL hcovK φ hP2 hOut hQN hAQ⟩
  have hnotCg : ¬ Cg z ≤ M := by
    obtain ⟨Q, -, hzQ, -, hQM⟩ := hsyl z hzA hz1
    intro hCM
    exact hQM ((Lemma1210.le_cg_of_mem_centerOf hzQ).trans hCM)
  have hshear : z ∈ F ∨ ∃ z' ∈ F, z' ≠ 1 ∧
      Shears (N ⊓ M ⊓ Subgroup.normalizer (A : Set G)) z z' := by
    by_cases hzF : z ∈ F
    · exact Or.inl hzF
    · obtain ⟨y, hy, f, hfF, hf1, hyf⟩ :=
        AltFacts.shear_lift' h11 hAe hA3 hE2 hAN hKN hAK hL φ hOrb hF hzEA hzF
      exact Or.inr ⟨f, hfF, hf1, y, hy, hyf⟩
  exact ⟨z, hzA, hz1, hzPC, hnotCg, hsyl, hshear⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
