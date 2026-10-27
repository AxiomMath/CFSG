module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5L511Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Fusion
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BModel
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BAab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem csl_tz_mem (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (h58d : Asc82Lemma58d) (h510 : Asc82Lemma510)
    {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) :
    t * z ∈ conjClassIn ⊤ t ∩ (A : Set G) := by
  obtain ⟨φ, hm⟩ := sec5b_model58_of h58d c
  obtain ⟨ht, -, hz⟩ := hm.mem_A
  have hc := (h510 G t L S z r B A c).1
  have hnt := sec5_t_not_conj_z h37 c.toSec5Ctx
  have hntz := sec5_tz_not_conj_z h36 h37 h52b h53 tab c.toSec5Ctx
  rw [hc]
  refine ⟨⟨A.mul_mem ht hz, ?_⟩, ?_⟩
  · intro h1
    have h1' : t * z = 1 := h1
    have hzt : z = t⁻¹ := eq_inv_of_mul_eq_one_right h1'
    have hti : t⁻¹ = t := by
      have := c.involution
      rw [inv_eq_iff_mul_eq_one, ← pow_two, ← this, pow_orderOf_eq_one]
    exact hnt 1 (by rw [inv_one, one_mul, mul_one, hzt, hti])
  · rintro ⟨m, -, hmz⟩
    exact hntz m⁻¹ (by rw [inv_inv, hmz])

theorem csl_tz_conj (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (h52b : Asc82Lemma52b)
    (h53 : Asc82Lemma53) (tab : Asc82Tab5) (h58d : Asc82Lemma58d) (h510 : Asc82Lemma510)
    {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) :
    ∃ h : G, h⁻¹ * t * h = t * z := by
  obtain ⟨⟨h, -, hh⟩, -⟩ := csl_tz_mem h36 h37 h52b h53 tab h58d h510 c
  exact ⟨h⁻¹, by rw [inv_inv, hh]⟩

theorem csl_z_not_central (h37 : Asc82Lemma37) {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) {h : G} (hh : h⁻¹ * t * h = t * z) :
    ¬ z ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
  intro hzc
  have hS := c.toSec3SettingLB.conjugate h
  rw [hh] at hS
  have hzL : z ∈ L := c.pocket.mem
  have hzt : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp (c.component.1 hzL)
  have e : h⁻¹⁻¹ * (h⁻¹ * z * h) * h⁻¹ = z := by group
  have hmem : h⁻¹⁻¹ * (h⁻¹ * z * h) * h⁻¹ ∈ centralizer ({t * z} : Set G) := by
    rw [e, Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, hzt]
  have key := h37 G (t * z) (CFSG.conjugate L h) hS (h⁻¹ * z * h) h⁻¹
    (c.pocket.conjugate h) hmem
  rw [e] at key
  have hinf : CFSG.conjugate L h ⊓ centralizer ({z} : Set G) = CFSG.conjugate L h :=
    inf_eq_left.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzc x hx)
  rw [hinf] at key
  have hQ := hS.component.isQuasisimple
  have htop : CFSG.layer ↥(CFSG.conjugate L h) = ⊤ :=
    eq_top_iff.mpr (CFSG.LocalCores.component_le_layer (K := ⊤)
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ,
        Subgroup.IsSubnormal.top⟩)
  apply hS.component.ne_bot
  rw [eq_bot_iff]
  intro x hx
  rw [← key]
  exact ⟨⟨x, hx⟩, by rw [htop]; exact Subgroup.mem_top _, rfl⟩

theorem csl_twoCore_le (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    {t : G} {L S : Subgroup G}
    {z r : G} {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) {h : G}
    (hh : h⁻¹ * t * h = t * z) {K : Subgroup G} (hK : Sl23PocketIn L z K) :
    twoCoreIn K ≤ CFSG.conjugate L h := by
  have hS := c.toSec3SettingLB
  have hD : Sec3PocketData t L z K :=
    sec3PocketData_of_sl23PocketIn hS.involution hS.component (Or.inl hS.inF)
      (conjugate_eq_self_of_lemma36 h36 hS) c.pocket.1 hK
  have hS' : Sec3SettingLB G (t * z) (CFSG.conjugate L h) := by
    rw [← hh]
    exact hS.conjugate h
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have htc : t ∈ centralizer ((L ⊔ zpowers t : Subgroup G) : Set G) := by
    have hle : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
      sup_le hLt (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  rcases h34a G t L hS t L z K (t * z) (CFSG.conjugate L h) hD hS'.involution ⟨t, htc, rfl⟩
      hS'.component (Or.inl hS'.inF) with hcomm | hle
  · exfalso
    have hKc : K ≤ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact csl_z_not_central h37 c hh (hKc hK.1)
  · exact hle

theorem csl_t_mem_zpowers (h52a : Asc82Lemma52a) {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) {y : G}
    (hy : y ∈ S ⊓ centralizer (L : Set G)) (hy1 : y ≠ 1) : t ∈ zpowers y := by
  obtain ⟨hyS, hyC⟩ := hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp c.sylow.2.1 ⟨y, hyS⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hy1 (orderOf_eq_one_iff.mp (by rw [hk, pow_zero]))
  have hdvd : 2 ∣ orderOf y := by rw [hk]; exact dvd_pow_self 2 hk0
  have hy0 : orderOf y ≠ 0 := by rw [hk]; positivity
  set w := y ^ (orderOf y / 2) with hw
  have hw2 : orderOf w = 2 := orderOf_pow_orderOf_div hy0 hdvd
  have hwz : w ∈ zpowers y := Subgroup.npow_mem_zpowers y _
  have hwC : w ∈ centralizer (L : Set G) := (centralizer (L : Set G)).pow_mem hyC _
  have hwt : w * t = t * w :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (c.sylow.1 (S.pow_mem hyS _))
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hww : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
  rcases sec4_eq_of_commute (h52a G t L c.toSec5Setting) hwC htC hww c.involution hwt with h1 | h1
  · exact absurd hw2 (by rw [h1, orderOf_one]; decide)
  · exact h1 ▸ hwz

theorem csl_pow_four (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5)
    (h58d : Asc82Lemma58d) (h510 : Asc82Lemma510) (hF0 : Asc82FactPockets6)
    (hE : Asc82FactQCentExp6) {t : G} {L S : Subgroup G} {z r : G} {B A : Subgroup G}
    (c : Sec5RCtx G t L S z r B A) :
    ∀ x ∈ S ⊓ centralizer (L : Set G), x ^ 4 = 1 := by
  intro x hx
  obtain ⟨h, hh⟩ := csl_tz_conj h36 h37 h52b h53 tab h58d h510 c
  have hS := c.toSec3SettingLB
  have hS' : Sec3SettingLB G (t * z) (CFSG.conjugate L h) := by
    rw [← hh]
    exact hS.conjugate h
  have hzL : z ∈ L := c.pocket.mem
  have hxC : x ∈ centralizer ({t * z} : Set G) := by
    have hxt := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
    have hxz : z * x = x * z := Subgroup.mem_centralizer_iff.mp hx.2 z hzL
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (t * z) = t * (x * z) := by rw [← mul_assoc, hxt, mul_assoc]
      _ = t * z * x := by rw [← hxz, mul_assoc]
  have hxN : x ∈ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 hS' x hxC)
  obtain ⟨K₁, K₂, hK₁, hK₂, -, hq1, hq2, hcomm, hcard, hcent, -⟩ :=
    hF0 G L z c.toSec5Setting.isOm6Z2 c.pocket
  have hle : ∀ {K}, Sl23PocketIn L z K → twoCoreIn K ≤ L := fun hK =>
    (Subgroup.map_subtype_le _).trans (hK.2.1.trans inf_le_left)
  have hxQ : x ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (show ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) ⊆ L from
      sup_le (hle hK₁) (hle hK₂)) hx.2
  have hzc : z ∉ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    csl_z_not_central h37 c hh
  have hznot : z ∉ centerIn (CFSG.conjugate L h) := by
    rintro ⟨w, hw, rfl⟩
    apply hzc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨y, hy⟩)
  have hx4 := hE G (CFSG.conjugate L h) z (isOm6Z2_conjugate c.toSec5Setting.isOm6Z2 h)
    (twoCoreIn K₁) (twoCoreIn K₂) (csl_twoCore_le h34a h36 h37 c hh hK₁)
    (csl_twoCore_le h34a h36 h37 c hh hK₂) hq1 hq2 hcomm hcard hcent hznot x hxN hxQ
  by_contra hne
  have ht := csl_t_mem_zpowers h52a c ((S ⊓ centralizer (L : Set G)).pow_mem hx 4) hne
  have htI : t ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx4) ht
  have htzI : t * z ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hS'.component.le hy))
  apply hzc
  have : z = t⁻¹ * (t * z) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htI) htzI


theorem csl_z_mem_B (h58d : Asc82Lemma58d) {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) : z ∈ B := by
  obtain ⟨φ, hm⟩ := sec5b_model58_of h58d c
  obtain ⟨-, -, hzA⟩ := hm.mem_A
  have hrL : r ∉ L := hm.r_not_mem_L
  have hrN : zpowers r ≤ normalizer (B : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (B : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (c.B_le hb).2
  rw [c.A_eq] at hzA
  have hzA' : z ∈ ((zpowers r : Set G) * (B : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (zpowers r) B hrN]
    exact hzA
  obtain ⟨a, ha, b, hb, hab⟩ := hzA'
  beta_reduce at hab
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hr2 : orderOf r = 2 := sec5b_orderOf_r c
  have hbL : b ∈ L := (c.B_le hb).1
  have hzL : z ∈ L := c.pocket.mem
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · have hr1 : r ^ n = 1 := by
      rw [← zpow_mod_orderOf, hr2]
      simp [h0]
    rw [hr1, one_mul] at hab
    rw [← hab]
    exact hb
  · exfalso
    have hr1 : r ^ n = r := by
      rw [← zpow_mod_orderOf, hr2]
      simp [h1]
    rw [hr1] at hab
    apply hrL
    have : r = z * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact L.mul_mem hzL (L.inv_mem hbL)

theorem csl_B_center (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) {t : G} {L S : Subgroup G}
    {z r : G} {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) :
    Nat.card ↥(B ⊓ centerIn L) = 2 := by
  have htB : t ∈ B := c.B_split.1
  have htZ : t ∈ centerIn L := sec5_t_mem_centerIn h52b c.toSec5Setting
  have hBA : B ≤ A := c.A_eq ▸ le_sup_right
  have hsq := (sec5b_A_elemAb c).2
  have heq : B ⊓ centerIn L = zpowers t := by
    apply le_antisymm
    · rintro b ⟨hb, hbZ⟩
      obtain ⟨-, hbc⟩ := sec5_mem_centerIn_iff.mp hbZ
      have hbC : b ∈ centralizer (L : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => (hbc y hy).symm
      have htC := sec4_t_mem_centralizer c.toSec3Setting
      have hbt : b * t = t * b := (sec5b_A_elemAb c).1 b (hBA hb) t (hBA htB)
      rcases sec4_eq_of_commute (h52a G t L c.toSec5Setting) hbC htC (hsq b (hBA hb))
          c.involution hbt with h1 | h1
      · rw [h1]
        exact one_mem _
      · rw [h1]
        exact mem_zpowers t
    · rw [Subgroup.zpowers_le]
      exact ⟨htB, htZ⟩
  rw [heq, Nat.card_zpowers, c.involution]

theorem csl_centralizer_A (h34a : Asc82Lemma34a) (h36 : Asc82Lemma36) (h37 : Asc82Lemma37)
    (h52a : Asc82Lemma52a) (h52b : Asc82Lemma52b) (h53 : Asc82Lemma53) (tab : Asc82Tab5)
    (h58d : Asc82Lemma58d) (h510 : Asc82Lemma510) (hF0 : Asc82FactPockets6)
    (hE : Asc82FactQCentExp6) (hB : Asc82FactQBCent6) {t : G} {L S : Subgroup G} {z r : G}
    {B A : Subgroup G} (c : Sec5RCtx G t L S z r B A) :
    ∀ x ∈ S ⊓ centralizer (L : Set G), x ∈ centralizer (A : Set G) → x ∈ zpowers t := by
  intro x hx hxA
  by_contra hxt
  have htC : t ∈ centralizer (L : Set G) := sec4_t_mem_centralizer c.toSec3Setting
  have hcyc := h52a G t L c.toSec5Setting
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (c.sylow.1 hx.1)
  have hx4 := csl_pow_four h34a h36 h37 h52a h52b h53 tab h58d h510 hF0 hE c x hx
  have hx2t : x * x = t := by
    have hxx_t : x * x * t = t * (x * x) := by
      calc x * x * t = x * (x * t) := by group
        _ = x * (t * x) := by rw [hxt']
        _ = (x * t) * x := by group
        _ = (t * x) * x := by rw [hxt']
        _ = t * (x * x) := by group
    have hxxC : x * x ∈ centralizer (L : Set G) := Subgroup.mul_mem _ hx.2 hx.2
    have hxx2 : x * x * (x * x) = 1 := by
      rw [← hx4]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rcases sec4_eq_of_commute hcyc hxxC htC hxx2 c.involution hxx_t with h1 | h1
    · exfalso
      rcases sec4_eq_of_commute hcyc hx.2 htC h1 c.involution hxt' with h2 | h2
      · exact hxt (by rw [h2]; exact one_mem _)
      · exact hxt (by rw [h2]; exact mem_zpowers t)
    · exact h1
  obtain ⟨φ, hmod⟩ := sec5b_model58_of h58d c
  obtain ⟨htA, -, hzA⟩ := hmod.mem_A
  have hBA : B ≤ A := c.A_eq ▸ le_sup_right
  have hab := sec5b_A_elemAb c
  have hmem := csl_tz_mem h36 h37 h52b h53 tab h58d h510 c
  rw [(h510 G t L S z r B A c).2.1] at hmem
  obtain ⟨m, hmN, hm⟩ := hmem
  have hn : m⁻¹⁻¹ * t * m⁻¹ = t * z := by rw [inv_inv, hm]
  have conj_comm : ∀ a : G, a * x = x * a → (m * a * m⁻¹) * (m * x * m⁻¹) =
      (m * x * m⁻¹) * (m * a * m⁻¹) := by
    intro a ha
    calc (m * a * m⁻¹) * (m * x * m⁻¹) = m * (a * x) * m⁻¹ := by group
      _ = m * (x * a) * m⁻¹ := by rw [ha]
      _ = (m * x * m⁻¹) * (m * a * m⁻¹) := by group
  have hyA : m * x * m⁻¹ ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : m⁻¹ * a * m ∈ A := by
      refine (Subgroup.mem_normalizer_iff.mp hmN (m⁻¹ * a * m)).mpr ?_
      have : m * (m⁻¹ * a * m) * m⁻¹ = a := by group
      rw [this]
      exact ha
    have ea : a = m * (m⁻¹ * a * m) * m⁻¹ := by group
    rw [ea]
    exact conj_comm _ (Subgroup.mem_centralizer_iff.mp hxA _ ha')
  have hyy : (m * x * m⁻¹) * (m * x * m⁻¹) = t * z := by
    calc (m * x * m⁻¹) * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = t * z := by rw [hx2t, hm]
  have hyt : m * x * m⁻¹ ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hyA t htA).symm
  have hyN : m * x * m⁻¹ ∈ normalizer (L : Set G) :=
    mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 c.toSec3SettingLB _ hyt)
  have hyB : m * x * m⁻¹ ∈ centralizer (B : Set G) :=
    Subgroup.centralizer_le (show (B : Set G) ⊆ A from hBA) hyA
  have hyLn : m * x * m⁻¹ ∈ centralizer ((CFSG.conjugate L m⁻¹ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hl := (mem_conjugate_iff L m⁻¹ w).mp hw
    rw [inv_inv] at hl
    have ew : w = m * (m⁻¹ * w * m) * m⁻¹ := by group
    rw [ew]
    exact conj_comm _ (Subgroup.mem_centralizer_iff.mp hx.2 _ hl)
  obtain ⟨K₁, K₂, hK₁, hK₂, -, hq1, hq2, hcomm, hcard, hcent, hint⟩ :=
    hF0 G L z c.toSec5Setting.isOm6Z2 c.pocket
  have hle : ∀ {K}, Sl23PocketIn L z K → twoCoreIn K ≤ L := fun hK =>
    (Subgroup.map_subtype_le _).trans (hK.2.1.trans inf_le_left)
  have hyQ : m * x * m⁻¹ ∈ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le
      (show ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) ⊆ CFSG.conjugate L m⁻¹ from
        sup_le (csl_twoCore_le h34a h36 h37 c hn hK₁) (csl_twoCore_le h34a h36 h37 c hn hK₂))
      hyLn
  have hBle : B ≤ L ⊓ centralizer ({z} : Set G) := fun b hb =>
    ⟨(c.B_le hb).1, Subgroup.mem_centralizer_singleton_iff.mpr (hab.1 b (hBA hb) z hzA)⟩
  apply hB G L z c.toSec5Setting.isOm6Z2 (twoCoreIn K₁) (twoCoreIn K₂) (hle hK₁) (hle hK₂)
    hq1 hq2 hcomm hcard hcent hint B hBle c.B_E32 (csl_z_mem_B h58d c) (csl_B_center h52a h52b c)
    _ hyN hyQ hyB
  rw [hyy, mul_assoc, hab.2 z hzA, mul_one]
  exact htC

end CFSG.OddStandard.SmallF3.Omega
