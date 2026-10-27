module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Defs
public import CFSG.LocalAnalysis.GLTheoremA.S12.Common
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B : Subgroup G} {x : G} {L D K : Subgroup G}

theorem maxG_of_isBmax (hp : p.Prime) (hB : GLAIsBmax p B) : MaxG p B := fun E U hE hU2 hU hEU => by
  have h1 := card_le_pow_glaTwoLocalRank hp hE hU hU2 hEU
  rw [hB.2.1]
  exact h1

theorem rank_of_two_group (hB : IsElemAbelian p B) {T : Subgroup G} (hMax : MaxG p B) (hT : T ≠ ⊥)
    (hT2 : IsPGroup 2 T) (hTc : T ≤ Subgroup.centralizer (L : Set G))
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) : Rank p B L := by
  intro E hEL hE
  have hC : IsElemAbelian p (B ⊓ Subgroup.centralizer (L : Set G)) := isElemAbelian_mono hB inf_le_left
  have hcomm : ∀ a ∈ E, ∀ b ∈ B ⊓ Subgroup.centralizer (L : Set G), a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.1 hb.2 a (hEL ha)
  refine hMax _ T (IsElemAbelian.sup_of_commute hE hC hcomm) hT2 hT ?_
  refine sup_le (fun e he => ?_) (fun c hc => hBT hc.1)
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun t ht =>
    (Subgroup.mem_centralizer_iff.1 (hTc ht) e (hEL he)).symm)

theorem B_norm_K (hB : IsElemAbelian p B) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hpre : GLAStdSubPre p B x L D K) : B ≤ Subgroup.normalizer (K : Set G) := by
  have hbcs : ∀ b ∈ B, b ∈ Subgroup.centralizer (D : Set G) := fun b hb => by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact isElemAbelian_commute hB (hpre.1 hd) hb
  intro b hb
  rw [hpre.2.2.2.2.1]
  exact S12.mem_normalizer_glaLayer' (S12.mem_normalizer_inf' (hBL hb)
    (Subgroup.le_normalizer (hbcs b hb)))

theorem exists_y (hp : p.Prime) (hx1 : x ≠ 1) (hpre : GLAStdSubPre p B x L D K) :
    ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
  by_contra hcon
  push Not at hcon
  have hD : D ≤ Subgroup.zpowers x := hcon
  have hcard := Subgroup.card_le_of_le hD
  rw [hpre.2.2.1, Nat.card_zpowers] at hcard
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf x = p := orderOf_eq_prime (hpre.2.1.2 x hpre.2.2.2.1) hx1
  rw [hord] at hcard
  have := hp.two_le
  nlinarith

theorem cs_eq (hp : p.Prime) (hx1 : x ≠ 1) (hpre : GLAStdSubPre p B x L D K) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.centralizer (D : Set G) = Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) :=
  S8.L89.centralizer_eq_inf hp hpre.2.1 hpre.2.2.1 hpre.2.2.2.1 hx1 hy hyx

theorem L_cs_eq (hp : p.Prime) (hx1 : x ≠ 1) (hpre : GLAStdSubPre p B x L D K) {y : G} (hy : y ∈ D)
    (hyx : y ∉ Subgroup.zpowers x) (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
  rw [cs_eq hp hx1 hpre hy hyx, ← inf_assoc, inf_eq_left.2 hLx]

theorem faithful_quot (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hKq : CFSG.Open.IsQuasisimple ↥K)
    (hpre : GLAStdSubPre p B x L D K) {b : G} (hb : b ∈ B)
    (hc : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ Subgroup.centralizer (K : Set G)) : b ∈ D := by
  have h1 : (⁅(⁅K, Subgroup.zpowers b⁆ : Subgroup G), K⁆ : Subgroup G) = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 hc
  have h2 : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
    CFSG.LocalCores.perfect_double_commutator ⟨hKq.1⟩ h1
  have h3 : K ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  rw [hpre.2.2.2.2.2.2]
  refine ⟨hb, ?_⟩
  show b ∈ Subgroup.centralizer (K : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact ((Subgroup.mem_centralizer_iff.1 (h3 hk)) b (Subgroup.mem_zpowers b)).symm

theorem dvd_of_faithful (i713 : CFSG.HardMathSupport.Solomon.Coordinator.I_7_13_1_pPrime)
    (hp : p.Prime) (hp2 : p ≠ 2) {Y Q A : Subgroup G} (hY : CFSG.Open.IsKGroup ↥Y) (hQY : Q ≤ Y)
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hA : IsElemAbelian p A)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set G))
    (hrank : p ^ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) ≤ Nat.card A) :
    p ∣ Nat.card (↥Q ⧸ Subgroup.center ↥Q) := by
  by_contra hnd
  haveI : Fact p.Prime := ⟨hp⟩
  have hKG : CFSG.Open.IsKGroup ↥Q := CFSG.Open.IsKGroup.of_le hY hQY
  have hs : IsSimpleGroup (↥Q ⧸ Subgroup.center ↥Q) := hQ.2
  have hna : ∃ a b : ↥Q ⧸ Subgroup.center ↥Q, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥Q hQ
  have hcat : CFSG.Open.IsCatalogGroup (↥Q ⧸ Subgroup.center ↥Q) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.isCatalogGroup_center_quotient_of_isKGroup hKG hQ
  have h1 := i713 p hp hp2 (↥Q ⧸ Subgroup.center ↥Q) hs hna hcat hnd
  haveI : Group.IsPerfect ↥Q := ⟨hQ.1⟩
  let φ : ↥A →* MulAut (↥Q ⧸ Subgroup.center ↥Q) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q).comp
      (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  have hker : φ.ker ≤ (A ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf A := by
    intro b hb
    have h0 : (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Q)
        (Q.normalizerMonoidHom (Subgroup.inclusion hAQ b)) = 1 := hb
    have h1 : Q.normalizerMonoidHom (Subgroup.inclusion hAQ b) = 1 := by
      apply CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥Q
      rw [h0, map_one]
    have h2 : Subgroup.inclusion hAQ b ∈ Q.normalizerMonoidHom.ker := h1
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at h2
    rw [Subgroup.mem_subgroupOf]
    exact ⟨b.2, h2⟩
  have hkcard : Nat.card φ.ker ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) := by
    have := Subgroup.card_le_of_le hker
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ Subgroup.centralizer (Q : Set G) ≤ A)).toEquiv] at this
  have hmul := Subgroup.card_ker_mul_card_range φ
  have hcpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) := Nat.card_pos
  have hrange : p ^ 2 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have h3 : Nat.card ↥A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) * Nat.card φ.range := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hkcard
    have h4 : Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) * Nat.card φ.range <
        Nat.card ↥(A ⊓ Subgroup.centralizer (Q : Set G)) * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hcpos
    nlinarith
  have hrange_el : IsElemAbelian p φ.range := by
    have := CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf hA A) φ
    rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at this
  obtain ⟨e, he⟩ := exists_card_eq_pow_of_isElemAbelian hp hrange_el
  have he2 : 2 ≤ e := by
    rw [he] at hrange
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hrange
  obtain ⟨E, -, hEel, hEcard⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hrange_el
    (n := 2) (by rw [he]; exact pow_dvd_pow p he2)
  have h5 := CFSG.SectionRank.le_pRank hp.one_lt le_top hEel hEcard
  omega

theorem cent_of_cyc (hp : p.Prime) (hB : IsElemAbelian p B) (hx : x ∈ B) (hx1 : x ≠ 1)
    (hxc : x ∈ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S) :
    ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set G) ↔ b ∈ Subgroup.zpowers x := by
  intro b hb
  constructor
  · intro hbc
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer (L : Set G) :=
      sup_le (Subgroup.zpowers_le.2 hxc) (Subgroup.zpowers_le.2 hbc)
    have hSB : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ B :=
      sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hb)
    have hSel : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers b) := isElemAbelian_mono hB hSB
    have hcyc' := hcyc _ hle (isPGroup_of_isElemAbelian hSel)
    have hcard := card_le_of_isCyclic_of_pow hp hcyc' (fun d hd => hB.2 d (hSB hd))
    exact mem_zpowers_of_card_sup_le hp (hB.2 x hx) hx1 hcard
  · intro hbx
    exact (Subgroup.zpowers_le.2 hxc) hbx

theorem cfg_mk (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElemAbelian p B) (h4 : p ^ 4 ≤ Nat.card B) (hx : x ∈ B)
    (hx1 : x ≠ 1) (hBL : B ≤ Subgroup.normalizer (L : Set G)) (hq : CFSG.Open.IsQuasisimple ↥L)
    (hchev : IsChevSimple 2 (PSimple p L)) (hxc : x ∈ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hid : InnerDiagMarking B L) : Cfg G p B x L :=
  ⟨hp, hp2, hB, h4, hx, hx1, hBL, hq, hchev, cent_of_cyc hp hB hx hx1 hxc hcyc, hcyc, hid⟩

theorem sstarMax_layer_eq' (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSStarMax p B x L) :
    GLAPLayer p (Subgroup.centralizer ({x} : Set G)) = L := by
  have hxB : x ∈ B := (IsSStarMax.essential h).1
  have hx1 : x ≠ 1 := (IsSStarMax.essential h).2.1
  have hLc : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L := IsSStarMax.component h
  have hxp : x ^ p = 1 := (IsSStarMax.bmax h).1.2 x hxB
  have hxL : x ∈ centModSubgroup p L := by
    refine centMod_iff.1 (centMod_of_mem_centralizer ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc.1 hl)
  apply le_antisymm
  · refine sSup_le fun J hJ => ?_
    by_cases hJL : J = L
    · exact hJL ▸ le_rfl
    exfalso
    have hJCm : J ≤ centModSubgroup p L := le_centModSubgroup_of_ne hp hJ hLc hJL
    obtain ⟨w, hwJ, hwp, k, hkJ, hkw⟩ := exists_pow_eq_one_noncomm_of_component hp hp2 hJ
    have hkx : Commute k x := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hkJ)
    have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hwJ)
    have hwnx : w ∉ Subgroup.zpowers x := by
      intro hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
      exact hkw (hkx.zpow_right n).eq
    obtain ⟨hE, hcard⟩ := Prop53.isElemAbelian_card_sup_zpowers hp hwx hwp hxp hx1 hwnx
    have hle : Subgroup.zpowers w ⊔ Subgroup.zpowers x ≤ centModSubgroup p L :=
      sup_le (Subgroup.zpowers_le.2 (hJCm hwJ)) (Subgroup.zpowers_le.2 hxL)
    have hcycS : IsCyclic (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) :=
      IsSStarMax.cycMod h (Subgroup.zpowers w ⊔ Subgroup.zpowers x)
        (fun g hg => centMod_iff.2 (hle hg)) (isPGroup_of_isElemAbelian hE)
    have hdiv : Nat.card (Subgroup.zpowers w ⊔ Subgroup.zpowers x : Subgroup G) ≤ p :=
      card_le_of_isCyclic_of_pow hp hcycS (fun d hd => hE.2 d hd)
    rw [hcard] at hdiv
    have h2 := hp.two_le
    nlinarith
  · exact le_sSup hLc

theorem cx_le_normalizer (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSStarMax p B x L) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro t ht
  have hle : ∀ (g : G) (X : Subgroup G), GLBConj g (GLAPLayer p X) ≤ GLAPLayer p (GLBConj g X) := by
    intro g X
    refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun M hM => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (glaPComponent_gLBConj hM g)
  have h1 := gLBConj_eq_of_forall_ge (F := GLAPLayer p) hle t (Subgroup.centralizer ({x} : Set G))
  rw [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer ht), sstarMax_layer_eq' hp hp2 h] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1.symm

theorem cfg_of_sstarMax (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSStarMax p B x L) (h4 : p ^ 4 ≤ Nat.card B)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hchev : IsChevSimple 2 (PSimple p L)) (hid : InnerDiagMarking B L) :
    Cfg G p B x L := by
  have hxc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 ((IsSStarMax.component h).1 hl)
  refine cfg_mk hp hp2 (IsSStarMax.bmax h).1 h4 (IsSStarMax.essential h).1 (IsSStarMax.essential h).2.1
    (IsSStarMax.normalizes h) hq hchev hxc (fun S hS hSp => ?_) hid
  exact IsSStarMax.cycMod h S (fun g hg => centMod_of_mem_centralizer (hS hg)) hSp

theorem exists_T_of_sstarMax (hp : p.Prime) (hp2 : p ≠ 2) (h : IsSStarMax p B x L) :
    ∃ T : Subgroup G, T ≤ Subgroup.normalizer (L : Set G) ∧ T ≤ Subgroup.centralizer ({x} : Set G) ∧
      IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨-, -, T, hTC, hT2, hBT, hne, -⟩ := IsSStarMax.essential h
  exact ⟨T, (hTC.trans (cx_le_normalizer hp hp2 h)), hTC, hT2, hBT, hne⟩

theorem normalizer_of_innerDiagMarking (h : InnerDiagMarking B L) : B ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, -, -, R, _, I, F, θ, -, -, hB1⟩ := CFSG.StandardType.Canonical.largeEvenMarking_exists h
  exact hB1.1

theorem innerDiagMarking_mono {A : Subgroup G} (h : InnerDiagMarking B L) (hAB : A ≤ B) :
    InnerDiagMarking A L :=
  CFSG.StandardType.Canonical.largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨hn, hall⟩ => ⟨hAB.trans hn, fun b hb => hall b (hAB hb)⟩) h

theorem cfg_of_sStar (hS : GLASStar 3 B x L) (h4 : 3 ^ 4 ≤ Nat.card B) (hchev : IsChevSimple 2 (PSimple 3 L))
    (hid : InnerDiagMarking B L) : Cfg G 3 B x L := by
  obtain ⟨hBmax, hxB, hx1, hcomp, hcyc⟩ := hS
  have hxc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 hl)
  exact cfg_mk Nat.prime_three (by norm_num) hBmax.1 h4 hxB hx1 (normalizer_of_innerDiagMarking hid) hcomp.2.2
    hchev hxc hcyc hid

theorem ker_chevQuotHom_eq_center' (hp : p.Prime) {X : Subgroup G} (hL : GLAPComponent p X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) : (chevQuotHom p L).ker = Subgroup.center ↥L := by
  apply le_antisymm
  · refine le_center_of_normal_of_isQuasisimple hLq inferInstance ?_
    intro htop
    have hsimple := (isQuasisimple_pQuot_of_glaPComponent hp hL).2
    haveI := hsimple.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : PSimple p L)
    obtain ⟨y, rfl⟩ := chevQuotHom_surjective p L x
    have hy : y ∈ (chevQuotHom p L).ker := htop ▸ Subgroup.mem_top y
    exact hx (MonoidHom.mem_ker.1 hy)
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hc : (QuotientGroup.mk' (GLAPPrimeCore p ↥L) z : PQuot p L) ∈ Subgroup.center (PQuot p L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥L) y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz l]
    show QuotientGroup.mk' (Subgroup.center (PQuot p L)) (QuotientGroup.mk' (GLAPPrimeCore p ↥L) z) = 1
    exact (QuotientGroup.eq_one_iff _).2 hc

noncomputable def chevIso' (hp : p.Prime) {X : Subgroup G} (hL : GLAPComponent p X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) : ↥L ⧸ Subgroup.center ↥L ≃* PSimple p L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_chevQuotHom_eq_center' hp hL hLq).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (chevQuotHom p L) (chevQuotHom_surjective p L))

theorem catalogIs_pSimple_iff (hp : p.Prime) {X : Subgroup G} (hL : GLAPComponent p X L)
    (hLq : CFSG.Open.IsQuasisimple ↥L) {Q : TauCeti.CFSGIndex → Prop} :
    catalogIs (↥L ⧸ Subgroup.center ↥L) Q ↔ catalogIs (PSimple p L) Q :=
  ⟨fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨(chevIso' hp hL hLq).symm.trans f⟩⟩,
   fun ⟨i, hi, ⟨f⟩⟩ => ⟨i, hi, ⟨(chevIso' hp hL hLq).trans f⟩⟩⟩

theorem catalogIs_three {S : Type} [Group S] {P Q R : TauCeti.CFSGIndex → Prop}
    (h : catalogIs S (fun i => P i ∨ Q i ∨ R i)) : catalogIs S P ∨ catalogIs S Q ∨ catalogIs S R := by
  obtain ⟨i, hi, e⟩ := h
  rcases hi with h | h | h
  · exact Or.inl ⟨i, h, e⟩
  · exact Or.inr (Or.inl ⟨i, h, e⟩)
  · exact Or.inr (Or.inr ⟨i, h, e⟩)

theorem card_cenB (hcfg : Cfg G p B x L) : Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) = p := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have heq : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
    ext g
    constructor
    · rintro ⟨hgB, hgc⟩
      exact (hcfg.cent g hgB).1 hgc
    · intro hg
      have hgB : g ∈ B := (Subgroup.zpowers_le.2 hcfg.mem) hg
      exact ⟨hgB, (hcfg.cent g hgB).2 hg⟩
  rw [heq, Nat.card_zpowers]
  exact orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one

theorem not_rank_of_big_elem (hcfg : Cfg G p B x L) {E : Subgroup G} (hEL : E ≤ L)
    {k : ℕ} (hEc : p ^ k * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card E)
    (hE : IsElemAbelian p E) (hB : Nat.card B < p ^ (k + 1)) : ¬ Rank p B L := by
  intro hR
  have hp := hcfg.prime
  have h1 := hR E hEL hE
  set C : Subgroup G := B ⊓ Subgroup.centralizer (L : Set G) with hC
  have hCN : C ≤ Subgroup.normalizer (E : Set G) := fun c hc =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun e he =>
      (Subgroup.mem_centralizer_iff.1 hc.2 e (hEL he)))
  have h2 := card_sup_mul_card_inf_of_le_normalizer hCN
  rw [card_cenB hcfg] at h2
  have h3 : Nat.card ↥(E ⊓ C) ≤ Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_left E inf_le_right)
  have hz : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have h4 : p ^ (k + 1) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) ≤
      Nat.card ↥(E ⊔ C) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) := by
    calc p ^ (k + 1) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G))
        = p * (p ^ k * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G))) := by ring
      _ ≤ p * Nat.card E := Nat.mul_le_mul_left _ hEc
      _ = Nat.card ↥(E ⊔ C) * Nat.card ↥(E ⊓ C) := by rw [h2, mul_comm]
      _ ≤ Nat.card ↥(E ⊔ C) * Nat.card ↥(E ⊓ Subgroup.centralizer (L : Set G)) :=
        Nat.mul_le_mul_left _ h3
  have h5 : p ^ (k + 1) ≤ Nat.card ↥(E ⊔ C) := Nat.le_of_mul_le_mul_right h4 hz
  omega

end CFSG.LocalAnalysis.GLTheoremA.S171

end
