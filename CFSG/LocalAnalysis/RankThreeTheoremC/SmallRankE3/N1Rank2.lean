module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65Basic
import CFSG.GroupTheory.SteinbergBSNormalPlane
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.RankThree.PartOne.K1214.CycAlg

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (KFactP65RankTwo KFactP65RankTwoAt
  IsMaxFInvariantIn
  IsFInvariantIn p65_le_of_plane_centralizers_le p65_normalizer_le_of_enlarged)

section General

variable {G : Type} [Group G] [Finite G]

private theorem p65r2_le_pRank {p : ℕ} (hp : p.Prime) {H E : Subgroup G} (hEH : E ≤ H)
    (hE : IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk

private theorem p65r2_exists_isElemAbelian {p : ℕ} (hp : p.Prime) {H : Subgroup G} {k : ℕ}
    (hk : k ≤ Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k :=
  CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hp hk

private theorem p65r2_exists_sylow {p : ℕ} (hp : p.Prime) {H T : Subgroup G} (hTH : T ≤ H)
    (hT : IsPGroup p T) :
    ∃ Q : Subgroup G, T ≤ Q ∧ Q ≤ H ∧ IsPGroup p Q ∧ ¬ p ∣ (Q.subgroupOf H).index :=
  CFSG.LocalAnalysis.RankThreeTheoremC.exists_sylow_le_of_isPGroup hp hTH hT

private theorem p65r2_pRank_centralizer_conj {p : ℕ} (hp : p.Prime) (g y : G) :
    Open.pRank p (centralizer ({g * y * g⁻¹} : Set G)) =
      Open.pRank p (centralizer ({y} : Set G)) := by
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  have hz : zpowers (g * y * g⁻¹) = (zpowers y).map (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hC : centralizer ({g * y * g⁻¹} : Set G) =
      (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom := by
    rw [hcz (g * y * g⁻¹), hcz y, hz, centralizer_map_automorphism]
  rw [hC]
  exact pRank_map_automorphism p hp.one_lt _ _

private theorem p65r2_sup_zpowers {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E)
    {w : G} (hw : w ^ p = 1) (hwE : w ∉ E) (hc : ∀ e ∈ E, e * w = w * e) :
    IsElemAbelian p (E ⊔ zpowers w) ∧ Nat.card (E ⊔ zpowers w : Subgroup G) = Nat.card E * p := by
  refine ⟨?_, CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp E hw hwE hc⟩
  have : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
  have : CFSG.IsElementaryAbelian p (zpowers w) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hw
  exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
    (CFSG.IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.2 (mem_centralizer_iff.2 hc)))

private theorem p65r2_isCyclic_center {p : ℕ} (hp : p.Prime) {Q B U : Subgroup G}
    (hQ : IsPGroup p Q) (hBQ : B ≤ Q) (hUQ : U ≤ Q) (hB9 : Nat.card B = p ^ 2)
    (hU : IsElemAbelian p U) (hU9 : Nat.card U = p ^ 2)
    (hmem : ∀ y ∈ centralizer (B : Set G), y ^ p = 1 → y ∈ B) (hBU : B ≠ U) :
    IsCyclic (center Q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hnc
  set Y : Subgroup G := (center Q).map Q.subtype with hY
  have hYQ : Y ≤ Q := map_subtype_le _
  have hYc : ∀ y ∈ Y, ∀ q ∈ Q, q * y = y * q := by
    rintro _ ⟨c, hc, rfl⟩ q hq
    exact congrArg Subtype.val (mem_center_iff.1 hc ⟨q, hq⟩)
  have hYp : IsPGroup p ↥Y := hQ.to_le hYQ
  have hYcomm : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := fun a ha b hb => (hYc a ha b (hYQ hb)).symm
  have hYnc : ¬ IsCyclic ↥Y := fun hc =>
    hnc ((Subgroup.equivMapOfInjective (center Q) Q.subtype Q.subtype_injective).isCyclic.2 hc)
  have key : ∀ B' : Subgroup G, Nat.card B' ≤ p → ∃ y ∈ Y, y ^ p = 1 ∧ y ∉ B' := by
    intro B' hB'
    by_contra hcon
    push Not at hcon
    exact hYnc (CFSG.RankThree.PartOne.K1214.isCyclic_of_torsion_le hp hYp hYcomm hB' hcon)
  obtain ⟨y₁, hy₁Y, hy₁3, hy₁⟩ := key ⊥ (by rw [Subgroup.card_bot]; exact hp.one_lt.le)
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁ (Subgroup.mem_bot.2 h1)
  have hy₁c : Nat.card (zpowers y₁) = p := by rw [Nat.card_zpowers, orderOf_eq_prime hy₁3 hy₁1]
  obtain ⟨y₂, hy₂Y, hy₂3, hy₂⟩ := key (zpowers y₁) hy₁c.le
  have hyB : ∀ y ∈ Y, y ^ p = 1 → y ∈ B := fun y hy hy3 =>
    hmem y (mem_centralizer_iff.2 fun b hb => hYc y hy b (hBQ hb)) hy3
  have hcomm : ∀ e ∈ zpowers y₁, e * y₂ = y₂ * e := fun e he =>
    mem_centralizer_singleton_iff.1
      ((zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYcomm y₁ hy₁Y y₂ hy₂Y))) he)
  have hV9 : Nat.card (zpowers y₁ ⊔ zpowers y₂ : Subgroup G) = p ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers y₁) hy₂3 hy₂ hcomm, hy₁c,
      pow_two]
  have hVB : zpowers y₁ ⊔ zpowers y₂ ≤ B :=
    sup_le (zpowers_le.2 (hyB y₁ hy₁Y hy₁3)) (zpowers_le.2 (hyB y₂ hy₂Y hy₂3))
  have hVeq : zpowers y₁ ⊔ zpowers y₂ = B :=
    Subgroup.eq_of_le_of_card_ge hVB (hB9.trans hV9.symm).le
  have hUB : U ≤ B := by
    intro u hu
    refine hmem u (mem_centralizer_iff.2 fun b hb => ?_) (hU.2 u hu)
    rw [← hVeq] at hb
    have hle : zpowers y₁ ⊔ zpowers y₂ ≤ centralizer ({u} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYc y₁ hy₁Y u (hUQ hu)).symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 (hYc y₂ hy₂Y u (hUQ hu)).symm))
    exact mem_centralizer_singleton_iff.1 (hle hb)
  exact hBU (Subgroup.eq_of_le_of_card_ge hUB (hU9.trans hB9.symm).ge).symm

private theorem p65r2_relIndex_centralizer_le {p : ℕ} (hp : p.Prime) {R U : Subgroup G}
    (hR : IsPGroup p R) (hUR : U ≤ R) (hRU : R ≤ normalizer (U : Set G)) (hU : IsElemAbelian p U)
    (hUc : Nat.card U = p ^ 2) : (centralizer (U : Set G)).relIndex R ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hUn : (U.subgroupOf R).Normal := (normal_subgroupOf_iff_le_normalizer hUR).mpr hRU
  haveI : CFSG.IsElementaryAbelian p U :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).2 hU
  haveI : CFSG.IsElementaryAbelian p (U.subgroupOf R) := CFSG.IsElementaryAbelian.subgroupOf hUR
  have hcard : Nat.card (U.subgroupOf R) = p ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUR).toEquiv).trans hUc
  have h := CFSG.GroupTheory.SteinbergBS.index_centralizer_le hR (U.subgroupOf R) hcard
  have heq : (centralizer (U : Set G)).subgroupOf R =
      centralizer ((U.subgroupOf R : Subgroup R) : Set R) := by
    ext g
    simp only [mem_subgroupOf, mem_centralizer_iff, SetLike.mem_coe]
    constructor
    · intro hg h hh
      exact Subtype.ext (hg h hh)
    · intro hg h hh
      exact congrArg Subtype.val (hg ⟨h, hUR hh⟩ hh)
  rw [Subgroup.relIndex, heq]
  exact h

private theorem p65r2_pRank_centralizer_ge {p : ℕ} (hp : p.Prime) {R U : Subgroup G}
    (hR : IsPGroup p R) (hUR : U ≤ R) (hRU : R ≤ normalizer (U : Set G)) (hU : IsElemAbelian p U)
    (hUc : Nat.card U = p ^ 2) (hR3 : 3 ≤ Open.pRank p R) :
    3 ≤ Open.pRank p (R ⊓ centralizer (U : Set G)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAR, hA, hAc⟩ := p65r2_exists_isElemAbelian hp hR3
  by_cases hUA : U ≤ A
  ·
    have hAC : A ≤ R ⊓ centralizer (U : Set G) := by
      refine le_inf hAR fun a ha => Subgroup.mem_centralizer_iff.2 fun u hu => ?_
      exact hA.comm (hUA hu) ha
    exact p65r2_le_pRank hp hAC hA hAc
  ·
    obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = centralizer (U : Set G) ⊓ A := ⟨_, rfl⟩
    have hC_le_cent : C ≤ centralizer (U : Set G) := by rw [hCdef]; exact inf_le_left
    have hC_le_A : C ≤ A := by rw [hCdef]; exact inf_le_right
    have hCel : IsElemAbelian p C := by rw [hCdef]; exact IsElemAbelian.mono hA inf_le_right
    have hidx := p65r2_relIndex_centralizer_le hp hR hUR hRU hU hUc
    have hrel : (centralizer (U : Set G)).relIndex A ≤ p :=
      (relIndex_le_of_le_right hAR (by
        rw [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite)).trans hidx
    have h1 := relIndex_mul_card (centralizer (U : Set G)) A
    rw [hAc, ← hCdef] at h1
    have hCcard : p ^ 2 ≤ Nat.card ↥C := by
      have h3 : p * p ^ 2 ≤ p * Nat.card ↥C := by
        calc p * p ^ 2 = p ^ 3 := by ring
          _ = (centralizer (U : Set G)).relIndex A * Nat.card ↥C := h1.symm
          _ ≤ p * Nat.card ↥C := Nat.mul_le_mul hrel le_rfl
      exact Nat.le_of_mul_le_mul_left h3 hp.pos
    have hUAc : Nat.card ↥(U ⊓ A) ≤ p := by
      have hdvd : Nat.card ↥(U ⊓ A) ∣ Nat.card ↥U := Subgroup.card_dvd_of_le inf_le_left
      rw [hUc] at hdvd
      obtain ⟨i, hi, hiU⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      rcases Nat.lt_or_ge i 2 with hi2 | hi2
      · rw [hiU]
        calc p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
          _ = p := pow_one p
      · exfalso
        have hi2' : i = 2 := by omega
        have heq : U ⊓ A = U :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq (by rw [hUc, hiU, hi2']))
        exact hUA ((le_of_eq heq.symm).trans inf_le_right)
    have hCU : Nat.card ↥(C ⊓ U) ≤ p := by
      refine le_trans (Subgroup.card_le_of_le ?_) hUAc
      exact le_inf inf_le_right (inf_le_left.trans hC_le_A)
    have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C U
      (fun x hx y hy => (Subgroup.mem_centralizer_iff.1 (hC_le_cent hx) y hy).symm)).1
    have hEel : IsElemAbelian p (C ⊔ U) :=
      IsElemAbelian.sup_of_commute hCel hU fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.1 (hC_le_cent ha) b hb).symm
    have hEsub : C ⊔ U ≤ R ⊓ centralizer (U : Set G) := by
      refine sup_le (le_inf (hC_le_A.trans hAR) hC_le_cent) (le_inf hUR fun u hu => ?_)
      exact Subgroup.mem_centralizer_iff.2 fun v hv => hU.comm hv hu
    have hE3 : p ^ 3 ≤ Nat.card ↥(C ⊔ U) := by
      have h7 : p ^ 3 * p ≤ Nat.card ↥(C ⊔ U) * p := by
        calc p ^ 3 * p = p ^ 2 * p ^ 2 := by ring
          _ ≤ Nat.card ↥C * Nat.card ↥U := Nat.mul_le_mul hCcard hUc.symm.le
          _ = Nat.card ↥(C ⊔ U) * Nat.card ↥(C ⊓ U) := hprod.symm
          _ ≤ Nat.card ↥(C ⊔ U) * p := Nat.mul_le_mul le_rfl hCU
      exact Nat.le_of_mul_le_mul_right h7 hp.pos
    obtain ⟨k, hk⟩ := (elementary_isPGroup p _ hEel).exists_card_eq
    have hk3 : 3 ≤ k := by
      rw [hk] at hE3
      exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hE3
    exact hk3.trans (p65r2_le_pRank hp hEsub hEel hk)

private theorem p65r2_exists_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {Q R : Subgroup G}
    (hR : IsPGroup p R) (hQR : Q < R) : ∃ y ∈ R, y ∈ normalizer (Q : Set G) ∧ y ∉ Q := by
  have : Group.IsNilpotent R := hR.isNilpotent
  have hlt : Q.subgroupOf R < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hQR.ne ?_
    exact le_antisymm hQR.le (Subgroup.subgroupOf_eq_top.mp h)
  have hgrow := Group.normalizerCondition_of_isNilpotent (G := R) _ hlt
  obtain ⟨y, hyN, hyQ⟩ := IsConcreteLE.exists_of_lt hgrow
  rw [← Subgroup.subgroupOf_normalizer_eq hQR.le, Subgroup.mem_subgroupOf] at hyN
  exact ⟨y, y.2, hyN, fun h => hyQ (Subgroup.mem_subgroupOf.mpr h)⟩

omit [Finite G] in
private theorem p65r2_normalizer_ne_top [IsSimpleGroup G] {F Fs : Subgroup G} (hF1 : F ≠ ⊥)
    (hFFs : F < Fs) : normalizer (F : Set G) ≠ ⊤ := by
  intro htop
  have : F.Normal := normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal F with hb | ht
  · exact hF1 hb
  · rw [ht] at hFFs
    exact not_top_lt hFFs

omit [Finite G] in
private theorem p65r2_normalizer_le_normalizer_centralizer (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer ((centralizer (S : Set G) : Subgroup G) : Set G) := by
  intro n hn
  have hn' : S.map (MulAut.conj n).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (centralizer (S : Set G)).map (MulAut.conj n).toMonoidHom = centralizer (S : Set G)
  rw [centralizer_map_automorphism, hn']

end General

section Situation

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

private theorem p65r2_conj_not_mem (hS : Sit G p P M) (hx : SmallRankPoint P M x) {U : Subgroup G}
    (hU3 : ∀ u ∈ U, 3 ≤ Open.pRank p (centralizer ({u} : Set G))) (g : G) : g * x * g⁻¹ ∉ U := by
  intro hxU
  have h3 := hU3 _ hxU
  have h2 := hS.pRank_centralizer_le hx
  rw [p65r2_pRank_centralizer_conj hS.prime] at h3
  omega

private theorem p65r2_not_conj (hS : Sit G p P M) (hx : SmallRankPoint P M x) {U : Subgroup G}
    (hU3 : ∀ u ∈ U, 3 ≤ Open.pRank p (centralizer ({u} : Set G))) (g : G) :
    (zpowers x ⊔ zpowers z).map (MulAut.conj g).toMonoidHom ≠ U := by
  intro hgU
  refine p65r2_conj_not_mem hS hx hU3 g ?_
  rw [← hgU]
  exact ⟨x, mem_sup_left (mem_zpowers x), rfl⟩

private theorem p65r2_central_mem_zpowers (hS : Sit G p P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {Q U : Subgroup G} (hBQ : zpowers x ⊔ zpowers z ≤ Q) (hUQ : U ≤ Q)
    (hU : IsElemAbelian p U) (hU9 : Nat.card U = p ^ 2)
    (hU3 : ∀ u ∈ U, 3 ≤ Open.pRank p (centralizer ({u} : Set G))) {w : G}
    (hw3 : orderOf w = p) (hwc : ∀ q ∈ Q, q * w = w * q) : w ∈ zpowers z := by
  by_contra hwz
  have hprime := hS.prime
  have hpl := hS.plane hx hz
  have hwp : w ^ p = 1 := by rw [← hw3]; exact pow_orderOf_eq_one w
  have hwB : w ∈ zpowers x ⊔ zpowers z := hpl.mem_of_mem_centralizer w
    (mem_centralizer_iff.2 fun b hb => hwc b (hBQ hb)) hwp
  have h2 := hS.pRank_centralizer_le_of_mem_plane hx hz hwB hwz
  have h3 : 3 ≤ Open.pRank p (centralizer ({w} : Set G)) := by
    by_cases hwU : w ∈ U
    · exact hU3 w hwU
    · have hc : ∀ u ∈ U, u * w = w * u := fun u hu => hwc u (hUQ hu)
      obtain ⟨hel, hcard⟩ := p65r2_sup_zpowers hprime hU hwp hwU hc
      refine p65r2_le_pRank hprime ?_ hel (k := 3) (by rw [hcard, hU9]; ring)
      exact sup_le (fun u hu => mem_centralizer_singleton_iff.2 (hc u hu))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  omega

private theorem p65r2_weakly_closed (hS : Sit G p P M) (hx : SmallRankPoint P M x)
    (hz : SmallRankCentral P z) {Q U : Subgroup G} (hBQ : zpowers x ⊔ zpowers z ≤ Q) (hUQ : U ≤ Q)
    (hU : IsElemAbelian p U) (hU9 : Nat.card U = p ^ 2)
    (hU3 : ∀ u ∈ U, 3 ≤ Open.pRank p (centralizer ({u} : Set G))) {w : G}
    (hw3 : orderOf w = p) (hwc : ∀ q ∈ Q, q * w = w * q) {g : G}
    (hg : g * w * g⁻¹ ∈ zpowers x ⊔ zpowers z) : g * w * g⁻¹ ∈ zpowers w := by
  have hwz : w ∈ zpowers z := p65r2_central_mem_zpowers hS hx hz hBQ hUQ hU hU9 hU3 hw3 hwc
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hz3 : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have heq : zpowers w = zpowers z := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hwz)
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hz3, hw3])
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (show z ∈ zpowers w by rw [heq]; exact mem_zpowers z)
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hwz
  have hgz : g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z := by
    have : g * z * g⁻¹ = (g * w * g⁻¹) ^ j := by rw [conj_zpow, hj]
    rw [this]
    exact zpow_mem hg j
  have hgz' := hS.mem_zpowers_of_conj_mem_plane hx hz hgz
  have : g * w * g⁻¹ = (g * z * g⁻¹) ^ k := by rw [conj_zpow, hk]
  rw [heq, this]
  exact zpow_mem hgz' k

private theorem p65r2_centralizer_le (hS : Sit G p P M) {E : Subgroup G} (hEM : E ≤ M)
    (hE : IsElemAbelian p E) (hE3 : Nat.card E = p ^ 3) {y : G} (hyM : y ∈ M)
    (hy : orderOf y = p) (hEy : E ≤ centralizer ({y} : Set G)) :
    centralizer ({y} : Set G) ≤ M :=
  hS.centralizer_le_of_pRank hyM hy
    (p65r2_le_pRank hS.prime (le_inf hEM hEy) hE hE3)

private theorem p65r2_normalizer_zpowers_le (hS : Sit G p P M) {E : Subgroup G}
    (hEM : E ≤ M) (hE : IsElemAbelian p E) (hE3 : Nat.card E = p ^ 3) {y : G} (hyM : y ∈ M)
    (hy : orderOf y = p) (hEy : E ≤ centralizer ({y} : Set G)) :
    normalizer ((zpowers y : Subgroup G) : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hCM := p65r2_centralizer_le hS hEM hE hE3 hyM hy hEy
  obtain ⟨S, hES, hSC, hS3, hSidx⟩ :=
    p65r2_exists_sylow hprime hEy (elementary_isPGroup p E hE)
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer ({y} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hSC, hS3, hSidx⟩
  have hS2 : 2 ≤ Open.pRank p S := by
    have := p65r2_le_pRank hprime hES hE hE3
    omega
  have hSM : normalizer (S : Set G) ≤ M := hS.normalizer_le hS3 (hSC.trans hCM) hS2
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
    (CFSG.LocalAnalysis.RankThreeTheoremC.normalizer_zpowers_le_normalizer_centralizer y)
    hSsyl).trans (sup_le hCM hSM)

private theorem p65r2_normalizer_le_of_le_U (hS : Sit G p P M) {E U S : Subgroup G}
    (hEM : E ≤ M) (hE : IsElemAbelian p E) (hE3 : Nat.card E = p ^ 3)
    (hEU : E ≤ centralizer (U : Set G)) (hUM : U ≤ M) (hU : IsElemAbelian p U)
    (hU9 : Nat.card U = p ^ 2) (hSU : S ≤ U) (hS1 : 1 ≤ Open.pRank p S) :
    normalizer (S : Set G) ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨E₁, hE₁S, -, hE₁c⟩ := p65r2_exists_isElemAbelian hprime (k := 1) hS1
  have hS3 : p ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hE₁S
    rw [hE₁c] at this
    simpa using this
  obtain ⟨i, hi, hSi⟩ := (Nat.dvd_prime_pow hprime).1
    (show Nat.card S ∣ p ^ 2 by simpa [hU9] using Subgroup.card_dvd_of_le hSU)
  have hp1 := hprime.one_lt
  have hS : Nat.card S = p ∨ Nat.card S = p ^ 2 := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rw [pow_zero] at hSi
      omega
    · exact Or.inl (by rw [hSi, pow_one])
    · exact Or.inr hSi
  rcases hS with hSc | hSc
  · have hSne : S ≠ ⊥ := fun hb => by
      rw [hb, Subgroup.card_bot] at hSc
      omega
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hSne
    have hu1' : (u : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    have huS : (u : G) ∈ S := u.2
    have hup : (u : G) ^ p = 1 := hU.2 u (hSU huS)
    have hord : orderOf (u : G) = p := orderOf_eq_prime hup hu1'
    have heq : zpowers (u : G) = S := Subgroup.eq_of_le_of_card_ge (zpowers_le.2 huS)
      (by rw [Nat.card_zpowers, hord, hSc])
    rw [← heq]
    exact p65r2_normalizer_zpowers_le hS hEM hE hE3 (hUM (hSU huS)) hord
      (hEU.trans (centralizer_le (Set.singleton_subset_iff.2 (hSU huS))))
  · have hSeq : S = U := Subgroup.eq_of_le_of_card_ge hSU (by rw [hSc, hU9])
    subst hSeq
    refine hS.normalizer_le (IsPGroup.of_card (n := 2) hU9) hUM ?_
    exact p65r2_le_pRank hprime le_rfl hU hU9

set_option linter.unusedVariables false in
theorem p65_centralizer_cyclicAt (hK : KFactP65RankTwoAt G) (hS : Sit G p P M)
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (hfp : f ≠ p)
    {F Fs R : Subgroup G} (hF : IsPGroup f F) (hF1 : F ≠ ⊥)
    (hBF : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G))
    (hHM : ¬ normalizer (F : Set G) ≤ M) (hFs : IsPGroup f Fs) (hFsM : Fs ≤ M)
    (hBFs : zpowers x ⊔ zpowers z ≤ normalizer (Fs : Set G)) (hFFs : F < Fs)
    (hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ →
      zpowers x ⊔ zpowers z ≤ normalizer (F' : Set G) → Nat.card F < Nat.card F' →
      normalizer (F' : Set G) ≤ M)
    (hrankH : Open.pRank p (normalizer (F : Set G)) ≤ 2)
    (hR : IsPGroup p R) (hRM : R ≤ M) (hBR : zpowers x ⊔ zpowers z ≤ R)
    (hRFs : R ≤ normalizer (Fs : Set G)) (hR3 : 3 ≤ Open.pRank p R) :
    IsCyclic (R ⊓ centralizer (Fs : Set G) : Subgroup G) := by
  classical
  by_contra hnc
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : IsSimpleGroup G := hS.simple
  have hpl := hS.plane hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hRn : R ≤ normalizer ((R ⊓ centralizer (Fs : Set G) : Subgroup G) : Set G) :=
    (le_inf le_normalizer (hRFs.trans (p65r2_normalizer_le_normalizer_centralizer Fs))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨U, hUC, hRU, hUc, hUp, hUcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hprime hS.ne_two hR inf_le_left hRn hnc
  have hU : IsElemAbelian p U :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p U).1
      (CFSG.IsElementaryAbelian.of_forall hUcomm hUp)
  have hUR : U ≤ R := hUC.trans inf_le_left
  have hUFs : U ≤ centralizer (Fs : Set G) := hUC.trans inf_le_right
  have hUM : U ≤ M := hUR.trans hRM
  obtain ⟨E, hEC, hE, hEc⟩ := p65r2_exists_isElemAbelian hprime
    (p65r2_pRank_centralizer_ge hprime hR hUR hRU hU hUc hR3)
  have hEM : E ≤ M := (hEC.trans inf_le_left).trans hRM
  have hEU : E ≤ centralizer (U : Set G) := hEC.trans inf_le_right
  have hU3 : ∀ u ∈ U, 3 ≤ Open.pRank p (centralizer ({u} : Set G)) := fun u hu =>
    p65r2_le_pRank hprime (hEU.trans (centralizer_le (Set.singleton_subset_iff.2 hu))) hE hEc
  have hBU : zpowers x ⊔ zpowers z ≠ U := by
    intro hBU
    have := p65r2_conj_not_mem hS hx hU3 1
    rw [one_mul, inv_one, mul_one] at this
    exact this (hBU ▸ mem_sup_left (mem_zpowers x))
  obtain ⟨y, hyFs, hyN, hyF⟩ := p65r2_exists_mem_normalizer_not_mem hFs hFFs
  have hEF : F < Fs ⊓ normalizer (F : Set G) := by
    rw [IsConcreteLE.lt_iff_le_and_exists]
    exact ⟨le_inf hFFs.le le_normalizer, y, ⟨hyFs, hyN⟩, hyF⟩
  have hE'p : IsPGroup f ↥(Fs ⊓ normalizer (F : Set G)) := hFs.to_le inf_le_left
  have hBN : zpowers x ⊔ zpowers z ≤
      normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) : Set G) :=
    (le_inf hBFs (hBF.trans le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hUN : U ≤ normalizer ((Fs ⊓ normalizer (F : Set G) : Subgroup G) : Set G) :=
    hUFs.trans ((centralizer_le (SetLike.coe_subset_coe.2 inf_le_left)).trans
      (centralizer_le_normalizer _))
  have hUH : U ≤ normalizer (F : Set G) :=
    hUFs.trans ((centralizer_le (SetLike.coe_subset_coe.2 hFFs.le)).trans
      (centralizer_le_normalizer _))
  have hHK : CatalogSimpleSections ↥(normalizer (F : Set G)) :=
    catalogSimpleSections_of_isKProper hS.setting.kProper _
      (p65r2_normalizer_ne_top hF1 hFFs)
  have hrank2 : Open.pRank p (normalizer (F : Set G)) = 2 :=
    le_antisymm hrankH (p65r2_le_pRank hprime hBF hpl.isElemAbelian hpl.card_eq)
  have hQ₀ : IsPGroup p ↥(zpowers x ⊔ zpowers z ⊔ U) := hR.to_le (sup_le hBR hUR)
  obtain ⟨Q, hQ₀Q, hQH, hQ3, hQidx⟩ := p65r2_exists_sylow hprime (sup_le hBF hUH) hQ₀
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := le_sup_left.trans hQ₀Q
  have hUQ : U ≤ Q := le_sup_right.trans hQ₀Q
  have hQM : Q ≤ M := hS.le_of_plane_le hBP (hS.centralizer_plane_le hx hz) hQ3 hBQ
  have hcyc : IsCyclic (center Q) :=
    p65r2_isCyclic_center hprime hQ3 hBQ hUQ hpl.card_eq hU hUc hpl.mem_of_mem_centralizer hBU
  have hcop : Nat.Coprime (Nat.card ↥(Fs ⊓ normalizer (F : Set G))) (2 * p) := by
    obtain ⟨n, hn⟩ := hE'p.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.Coprime.mul_right
      ((Nat.coprime_primes hf Nat.prime_two).2 hf2) ((Nat.coprime_primes hf hprime).2 hfp))
  have hW := hK p (normalizer (F : Set G)) Q (zpowers x ⊔ zpowers z) U hprime hS.p_ge hHK hrank2
    hQH hQ3 hQidx hcyc hBQ hpl.isElemAbelian hpl.card_eq hUQ hU hUc
    (fun g _ => p65r2_not_conj hS hx hU3 g)
    (fun w _ hw3 hwc g _ hg => p65r2_weakly_closed hS hx hz hBQ hUQ hU hUc hU3 hw3 hwc hg)
    ⟨normalizer (F : Set G) ⊓ M, inf_le_left, fun heq => hHM (inf_eq_left.1 heq),
      fun S hSU hS1 g hg => ⟨hg.2,
        p65r2_normalizer_le_of_le_U hS hEM hE hEc hEU hUM hU hUc hSU hS1 hg.1⟩,
      fun S hSQ hS2 g hg => ⟨hg.2, hS.normalizer_le (hQ3.to_le hSQ) (hSQ.trans hQM) hS2 hg.1⟩⟩
    (Fs ⊓ normalizer (F : Set G)) inf_le_right (sup_le hBN hUN) hcop
  obtain ⟨-, hHO, hOc⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (normalizer (F : Set G))
  have hOM : rankThreePrimeCore p (normalizer (F : Set G)) ≤ M :=
    p65_le_of_plane_centralizers_le hprime hU hUc (hUH.trans hHO)
      ((Nat.Prime.coprime_iff_not_dvd hprime).1 hOc) fun u hu hu1 =>
        p65r2_centralizer_le hS hEM hE hEc (hUM hu) (orderOf_eq_prime (hUp u hu) hu1)
          (hEU.trans (centralizer_le (Set.singleton_subset_iff.2 hu)))
  exact hHM (p65_normalizer_le_of_enlarged hprime hf (hR.to_le hBR) hmax hBF hOM hEF hE'p hBN hW)

end Situation

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N1
