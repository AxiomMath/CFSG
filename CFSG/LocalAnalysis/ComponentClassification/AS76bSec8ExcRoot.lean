module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcLift
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalLevi
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8Swap

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.Exc

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

@[expose] def qLift {G : Type} [Group G] {A : Subgroup G} {C : Type} [Group C]
    (ψ : normalizer (A : Set G) →* MulAut C) (T : Subgroup G) (Ql : Subgroup C) : Subgroup G :=
  CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) ⊓ liftIn ψ (inn Ql)

structure LeviClassData {G : Type} [Group G] {A : Subgroup G} (D : ExcModel A) {C : Type}
    [Group C] (Z Dl Ql Hl Ll : Subgroup C) : Prop where
  levi : LeviData Z Dl Ql Hl Ll
  autFix : AutFix Ql Ll
  type : ∀ L₀ : Subgroup G, Nonempty (rankTwoQuot L₀ ≃* rankTwoQuot Ll) → D.LeviType L₀
  diag : D.IsTrialityFour → StatedClassicalModel (rankTwoQuot Ll) .PSL 3 2 2 →
    ∃ y ∈ centralizer (Ql : Set C), (∃ k : ℕ, y ^ 3 ^ k = 1) ∧ ¬ InducesInner y Ll

section Root

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {C : Type} [Group C]
  {ψ : normalizer (A : Set G) →* MulAut C}
  (hZC : center C = ⊥) (hψ : IsActionHom A (MulAut.conj : C →* MulAut C).range ψ)
include hZC hψ

omit [Finite G] hZC hψ in
theorem charTwo_of_reps {reps : List C} (hcover : ClassesCover reps)
    (hchar : ∀ y ∈ reps, CharTwo y) {x : C} (hx2 : x * x = 1) (hx1 : x ≠ 1) : CharTwo x := by
  obtain ⟨y, hy, hyx⟩ := hcover x hx2 hx1
  obtain ⟨c, hc⟩ := isConj_iff.1 hyx
  rw [← hc]
  exact charTwo_conj (hchar y hy) c

theorem actsIn_zx_of_reps (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y) (hchar : ∀ y ∈ reps, CharTwo y)
    {t₀ : G} (ht₀ : t₀ ∈ T) (ht₀1 : t₀ ≠ 1) (ht₀N : t₀ ∈ normalizer (A : Set G)) {x₀ : C}
    (hx₀ : ψ ⟨t₀, ht₀N⟩ = MulAut.conj x₀) : ActsIn ψ T (zx x₀) := by
  refine actsIn_zx hZC hψ h4 h32 h34 hc hZA
    (inf_eq_bot_of_reps hZC hψ h4 h32 h34 hc hOut hZA hcover hres) (fun t ht ht1 htN x hx => ?_)
    ht₀ ht₀1 ht₀N hx₀
  obtain ⟨hx2, hx1⟩ := involution_of_conj hZC hψ hc h32 ht htN hx
  exact charTwo_of_reps hcover hchar hx2 (hx1 ht1)

omit hZC in
theorem leviLift_le_perfectCore (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {Zl Dl : Subgroup C} (hT : ActsIn ψ T Zl)
    (hDZ : Dl ≤ centralizer (Zl : Set C)) (hDp : ⁅Dl, Dl⁆ = Dl) :
    leviLift ψ (inn Dl) ≤ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := by
  have hTP : ∀ u ∈ T, ∀ huN : u ∈ normalizer (A : Set G), ∀ s ∈ inn Dl,
      ψ ⟨u, huN⟩ * s = s * ψ ⟨u, huN⟩ := by
    intro u hu huN s hs
    obtain ⟨y, hy⟩ := exists_conj_of_mem hψ hc h32 h4 h34 hu huN
    have hyZ := (actsIn_iff.1 hT) u hu huN y hy
    obtain ⟨d, hd, rfl⟩ := hs
    rw [hy, ← map_mul, ← map_mul]
    congr 1
    exact (mem_centralizer_iff.1 (hDZ hd) y hyZ)
  exact CFSG.Quasithin.le_perfectCore_of_perfect
    (le_inf leviLift_le fun l hl => mem_centralizer_iff.2 fun u hu =>
      (mem_centralizer_singleton_iff.1 (leviLift_le_centralizer hψ (hc.le_normalizer hu)
        (hTP u hu _) hl)).symm)
    (commutator_leviLift hψ (inn_le_range _) (commutator_inn hDp))

omit hZC hψ [Finite G] in
theorem qLift_le {Ql : Subgroup C} : qLift ψ T Ql ≤ A :=
  fun _ hw => (mem_liftIn.1 (mem_inf.1 hw).2).1

omit hZC hψ [Finite G] in
theorem exists_of_mem_qLift {Ql : Subgroup C} {w : G} (hw : w ∈ qLift ψ T Ql) :
    ∃ q ∈ Ql, ψ ⟨w, le_normalizer (qLift_le hw)⟩ = MulAut.conj q := by
  obtain ⟨q, hq, hqw⟩ := (mem_liftIn.1 (mem_inf.1 hw).2).2
  exact ⟨q, hq, hqw.symm⟩

omit hZC in
theorem exists_mem_qLift (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {Zl Dl Ql : Subgroup C} (hT : ActsIn ψ T Zl)
    (hDZ : Dl ≤ centralizer (Zl : Set C)) (hDp : ⁅Dl, Dl⁆ = Dl) (hQD : Ql ≤ Dl) {q : C}
    (hq : q ∈ Ql) :
    ∃ w, ∃ hw : w ∈ qLift ψ T Ql, ψ ⟨w, le_normalizer (qLift_le hw)⟩ = MulAut.conj q := by
  obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (inn_le_range _) (commutator_inn hDp)
    (conj_mem_inn (hQD hq))
  refine ⟨l, mem_inf.2 ⟨leviLift_le_perfectCore hψ h4 h32 h34 hc hT hDZ hDp hl,
    mem_liftIn.2 ⟨leviLift_le hl, ?_⟩⟩, hlψ⟩
  rw [hlψ]
  exact conj_mem_inn hq

omit hZC [Finite G] in
theorem odd_orderOf_of_psi (hZA : Odd (Nat.card (center A))) {S : Subgroup C}
    (hS : Odd (Nat.card S)) {w : G} (hwA : w ∈ A) {s : C} (hs : s ∈ S)
    (hw : ψ ⟨w, le_normalizer hwA⟩ = MulAut.conj s) : Odd (orderOf w) := by
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hso : Odd (orderOf s) := RankTwoL3Even.odd_orderOf_of_mem hS hs
  set n := orderOf s
  have hwn : w ^ n ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨pow_mem hwA n, (hψ.eq_one_iff ⟨w ^ n, le_normalizer (pow_mem hwA n)⟩).1 ?_⟩
    rw [psi_pow (le_normalizer hwA), hw, ← map_pow, pow_orderOf_eq_one, map_one]
  have hz := RankTwoL3Even.odd_orderOf_of_mem hZA' hwn
  have h1 : w ^ (n * orderOf (w ^ n)) = 1 := by rw [pow_mul, pow_orderOf_eq_one]
  exact (hso.mul hz).of_dvd_nat (orderOf_dvd_of_pow_eq_one h1)

omit hZC [Finite G] in
theorem odd_orderOf_of_mem_qLift (hZA : Odd (Nat.card (center A))) {Ql : Subgroup C}
    (hQodd : Odd (Nat.card Ql)) {w : G} (hw : w ∈ qLift ψ T Ql) : Odd (orderOf w) := by
  obtain ⟨q, hq, hqw⟩ := exists_of_mem_qLift hw
  exact odd_orderOf_of_psi hψ hZA hQodd (qLift_le hw) hq hqw

theorem mem_centralizer_of_mem_qLift (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {Zl Dl Ql : Subgroup C} (hT : ActsIn ψ T Zl)
    (hDZ : Dl ≤ centralizer (Zl : Set C)) (hDp : ⁅Dl, Dl⁆ = Dl) (hQD : Ql ≤ Dl) {x : G}
    (hx : x ∈ A ⊓ centralizer (qLift ψ T Ql : Set G)) {c : C}
    (hxc : ψ ⟨x, le_normalizer (mem_inf.1 hx).1⟩ = MulAut.conj c) :
    c ∈ centralizer (Ql : Set C) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  rw [mem_centralizer_iff]
  intro q hq
  obtain ⟨w, hw, hwψ⟩ := exists_mem_qLift hψ h4 h32 h34 hc hT hDZ hDp hQD hq
  have hwx : w * x = x * w := mem_centralizer_iff.1 (mem_inf.1 hx).2 w hw
  have hwN := le_normalizer (qLift_le hw)
  have hxN := le_normalizer (mem_inf.1 hx).1
  have h1 := congrArg ψ (Subtype.ext hwx :
    (⟨w * x, mul_mem hwN hxN⟩ : normalizer (A : Set G)) = ⟨x * w, mul_mem hxN hwN⟩)
  rw [psi_mul hwN hxN, psi_mul hxN hwN, hwψ, hxc, ← map_mul, ← map_mul] at h1
  exact hinj h1

omit [Finite G] hZC hψ in
theorem commutatorElement_mem_of_normalizer {Hl Ll : Subgroup C}
    (hHc : ∀ a ∈ Hl, ∀ b ∈ Hl, a * b = b * a) (hHN : Hl ≤ normalizer (Ll : Set C))
    {h₁ h₂ l₁ l₂ : C} (hh₁ : h₁ ∈ Hl) (hh₂ : h₂ ∈ Hl) (hl₁ : l₁ ∈ Ll) (hl₂ : l₂ ∈ Ll) :
    ⁅h₁ * l₁, h₂ * l₂⁆ ∈ Ll := by
  have hcomm : h₂⁻¹ * h₁⁻¹ * h₂ = h₁⁻¹ := by
    rw [← mul_inv_rev, hHc h₁ hh₁ h₂ hh₂, mul_inv_rev, inv_mul_cancel_right]
  have e : ⁅h₁ * l₁, h₂ * l₂⁆ = (h₁ * l₁ * h₁⁻¹) * ((h₁ * h₂) * (l₂ * l₁⁻¹) * (h₁ * h₂)⁻¹) *
      (h₂ * l₂⁻¹ * h₂⁻¹) := by
    calc ⁅h₁ * l₁, h₂ * l₂⁆ = h₁ * l₁ * h₂ * l₂ * l₁⁻¹ * h₁⁻¹ * l₂⁻¹ * h₂⁻¹ := by
          rw [commutatorElement_def]; group
      _ = h₁ * l₁ * h₂ * l₂ * l₁⁻¹ * (h₂⁻¹ * h₁⁻¹ * h₂) * l₂⁻¹ * h₂⁻¹ := by rw [hcomm]
      _ = _ := by group
  rw [e]
  have hN₁ := hHN hh₁
  have hN₂ := hHN hh₂
  have hN₁₂ := hHN (mul_mem hh₁ hh₂)
  refine mul_mem (mul_mem ((mem_normalizer_iff.1 hN₁ l₁).1 hl₁) ?_)
    ((mem_normalizer_iff.1 hN₂ _).1 (inv_mem hl₂))
  exact (mem_normalizer_iff.1 hN₁₂ _).1 (mul_mem hl₂ (inv_mem hl₁))

omit [Finite G] hZC hψ in
theorem psi_commutatorElement' {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    ψ ⟨⁅x, y⁆, le_normalizer (RankTwoL3Even.commutatorElement_mem' hx hy)⟩ =
      ⁅ψ ⟨x, le_normalizer hx⟩, ψ ⟨y, le_normalizer hy⟩⁆ :=
  map_commutatorElement ψ ⟨x, le_normalizer hx⟩ ⟨y, le_normalizer hy⟩

omit [Finite G] hZC hψ in
theorem commutator_eq_of_isQuasisimple {L : Subgroup C} (h : CFSG.Open.IsQuasisimple ↥L) :
    ⁅L, L⁆ = L := by
  have h2 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
    rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  rw [← h2, h.1, ← MonoidHom.range_eq_map, range_subtype]

theorem layerCentralizer_qLift (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) {Zl Dl Ql Hl Ll : Subgroup C} (hT : ActsIn ψ T Zl)
    (hlevi : LeviData Zl Dl Ql Hl Ll) :
    layerCentralizer A (qLift ψ T Ql) = leviLift ψ (inn Ll) := by
  have hLlp := commutator_eq_of_isQuasisimple hlevi.quasisimple
  have hcent : ∀ {x : G} (hx : x ∈ A ⊓ centralizer (qLift ψ T Ql : Set G)) {c : C},
      ψ ⟨x, le_normalizer (mem_inf.1 hx).1⟩ = MulAut.conj c → c ∈ centralizer (Ql : Set C) :=
    fun hx _ hxc => mem_centralizer_of_mem_qLift hZC hψ h4 h32 h34 hc hT hlevi.D_le
      hlevi.D_perfect hlevi.Q_le hx hxc
  refine layerCentralizer_eq_leviLift' hψ qLift_le ?_ ?_ ?_
    (isQuasisimple_leviLift_inn hZC hψ hLlp hlevi.quasisimple)
  · intro w hw s hs
    obtain ⟨q, hq, hqw⟩ := exists_of_mem_qLift hw
    obtain ⟨l, hl, rfl⟩ := hs
    rw [hqw, ← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_iff.1 (hlevi.L_le hl) q hq
  · intro x hx
    obtain ⟨c, hc'⟩ := hψ.map_mem x (mem_inf.1 hx).1
    rw [← hc']
    refine conj_mem_normalizer_inn ?_
    obtain ⟨h, hh, hhl⟩ := hlevi.cent_eq c (hcent hx hc'.symm)
    have e : c = h * (h⁻¹ * c) := by group
    rw [e]
    exact mul_mem (hlevi.H_le hh) (le_normalizer hhl)
  · intro x hx y hy
    obtain ⟨c, hc'⟩ := hψ.map_mem x (mem_inf.1 hx).1
    obtain ⟨d, hd'⟩ := hψ.map_mem y (mem_inf.1 hy).1
    rw [psi_commutatorElement' (ψ := ψ) (mem_inf.1 hx).1 (mem_inf.1 hy).1, ← hc', ← hd',
      ← map_commutatorElement]
    refine conj_mem_inn ?_
    obtain ⟨h₁, hh₁, hl₁⟩ := hlevi.cent_eq c (hcent hx hc'.symm)
    obtain ⟨h₂, hh₂, hl₂⟩ := hlevi.cent_eq d (hcent hy hd'.symm)
    have e₁ : c = h₁ * (h₁⁻¹ * c) := by group
    have e₂ : d = h₂ * (h₂⁻¹ * d) := by group
    rw [e₁, e₂]
    exact commutatorElement_mem_of_normalizer hlevi.H_comm hlevi.H_le hh₁ hh₂ hl₁ hl₂

omit [Finite G] hψ in
theorem psi_apply_eq_of_commute {s : G} (hsN : s ∈ normalizer (A : Set G)) {w : G}
    (hwN : w ∈ normalizer (A : Set G)) {y : C} (hsw : w * s = s * w)
    (hwψ : ψ ⟨w, hwN⟩ = MulAut.conj y) : ψ ⟨s, hsN⟩ y = y := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have h1 := congrArg ψ (Subtype.ext hsw :
    (⟨w * s, mul_mem hwN hsN⟩ : normalizer (A : Set G)) = ⟨s * w, mul_mem hsN hwN⟩)
  rw [psi_mul hwN hsN, psi_mul hsN hwN, hwψ] at h1
  apply hinj
  rw [RankTwoHypIIY.conj_apply_eq_mul_conj_mul_inv, ← h1, mul_inv_cancel_right]

theorem isSylowOf_of_autFix (hA : Hyp31 A) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    {Ql Ll : Subgroup C} (hfix : AutFix Ql Ll) {Q L₀ : Subgroup G} (hQA : Q ≤ A) (hL₀A : L₀ ≤ A)
    (hQ : ∀ y ∈ Ql, ∃ w ∈ Q, ∃ hwN : w ∈ normalizer (A : Set G), ψ ⟨w, hwN⟩ = MulAut.conj y)
    (hL₀ : ∀ y ∈ Ll, ∃ l ∈ L₀, ∃ hlN : l ∈ normalizer (A : Set G), ψ ⟨l, hlN⟩ = MulAut.conj y) :
    IsSylowOf 2 R (centralizer (Q : Set G) ⊓ centralizer (L₀ : Set G) ⊓
      normalizer (R : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAR : A ≤ centralizer (R : Set G) := le_centralizer_iff.1 hR.le
  have hRH : R ≤ centralizer (Q : Set G) ⊓ centralizer (L₀ : Set G) ⊓ normalizer (R : Set G) :=
    le_inf (le_inf (le_centralizer_iff.2 (hQA.trans hAR)) (le_centralizer_iff.2 (hL₀A.trans hAR)))
      Subgroup.le_normalizer
  obtain ⟨S, hS, hRS⟩ := AS76b.exists_isSylowOf_le hRH hR.isPGroup
  have hNA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    have h := Lemma36.normalizer_le hA hR 1
    rwa [rightConjugate_one, rightConjugate_one] at h
  have hSK : S ≤ centralizer (A : Set G) := by
    intro s hs
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
    have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hsH := hS.le hs
    have hsQ := (mem_inf.1 (mem_inf.1 hsH).1).1
    have hsL := (mem_inf.1 (mem_inf.1 hsH).1).2
    have hsN := hNA (mem_inf.1 hsH).2
    refine (hψ.eq_one_iff ⟨s, hsN⟩).1 (hfix _ ⟨k, ?_⟩ (fun y hy => ?_) (fun y hy => ?_))
    · rw [← psi_pow hsN]
      have h1 : (⟨s ^ 2 ^ k, pow_mem hsN _⟩ : normalizer (A : Set G)) = 1 := Subtype.ext hk'
      rw [h1, map_one]
    · obtain ⟨w, hw, hwN, hwψ⟩ := hQ y hy
      exact psi_apply_eq_of_commute hZC hsN hwN (mem_centralizer_iff.1 hsQ w hw) hwψ
    · obtain ⟨l, hl, hlN, hlψ⟩ := hL₀ y hy
      exact psi_apply_eq_of_commute hZC hsN hlN (mem_centralizer_iff.1 hsL l hl) hlψ
  have hSR := hR.eq_of_le hRS hSK hS.isPGroup
  subst hSR
  exact hS

omit hZC in
theorem le_sup_leviLift_inn (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A))) {Zl Ll : Subgroup C}
    (hT : ActsIn ψ T Zl) (hLp : ⁅Ll, Ll⁆ = Ll) (hZL : Zl ≤ Ll) :
    T ≤ R ⊔ leviLift ψ (inn Ll) := by
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  intro t ht
  have htN := hc.le_normalizer ht
  obtain ⟨p, hpA, hpR⟩ := hc.exists_aPart h32 h4 h34 ht
  obtain ⟨x, hx⟩ := exists_conj_of_mem hψ hc h32 h4 h34 ht htN
  have hψp : ψ ⟨p, le_normalizer hpA⟩ = MulAut.conj x := by
    have h1 : ψ ⟨t⁻¹ * p, mul_mem (inv_mem htN) (le_normalizer hpA)⟩ = 1 :=
      (hψ.eq_one_iff _).2 (hc.sylowR.le hpR)
    rw [psi_mul (inv_mem htN) (le_normalizer hpA), psi_inv htN, inv_mul_eq_one] at h1
    rw [← h1, hx]
  have hp2 : p ^ 2 ^ 1 = 1 := by
    have hcomm : Commute t (t⁻¹ * p) := hc.commute_T_R ht hpR
    calc p ^ 2 ^ 1 = (t * (t⁻¹ * p)) ^ 2 := by rw [mul_inv_cancel_left, pow_one]
      _ = t ^ 2 * (t⁻¹ * p) ^ 2 := hcomm.mul_pow 2
      _ = 1 := by rw [(hc.elemT h32).2 t ht, (hc.elemR h32).2 _ hpR, one_mul]
  have hpL : p ∈ leviLift ψ (inn Ll) := by
    refine mem_leviLift_of_pow hψ (inn_le_range Ll) (commutator_inn hLp) hZA'
      (mem_liftIn.2 ⟨hpA, ?_⟩) hp2
    rw [hψp]
    exact conj_mem_inn (hZL ((actsIn_iff.1 hT) t ht htN x hx))
  have h1 : t = p * (t⁻¹ * p)⁻¹ := by group
  rw [h1]
  exact mul_mem (mem_sup_right hpL) (mem_sup_left (inv_mem hpR))

theorem not_conj_le (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y) (c : G) :
    ¬ R.map (MulAut.conj c).toMonoidHom ≤ A := by
  intro hle
  have hZA' : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rwa [RankTwoL3Even.card_inf_centralizer_eq]
  have hRc : R.map (MulAut.conj c).toMonoidHom = rightConjugate R c⁻¹ := by
    rw [rightConjugate, inv_inv]
  rw [hRc] at hle
  have hsec : Sec3 A R (rightConjugate R c⁻¹) c⁻¹ := by
    refine ⟨hc.hyp, hc.sylowR, fun hcN => ?_,
      AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR c⁻¹,
      hle.trans (le_centralizer_iff.1 hc.sylowR.le)⟩
    have hKc : rightConjugate (centralizer (A : Set G)) c⁻¹ = centralizer (A : Set G) :=
      (rightConjugate_eq_self_iff _ _).2 (by
        rw [normalizer_centralizer_eq hc.hyp.standard]
        exact hcN)
    obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
      (isSylowOf_ne_bot_of_even (AschbacherTheorem3.isSylowOf_rightConjugate hc.sylowR c⁻¹)
        (by rw [rightConjugate_card]; exact (tightlyEmbedded_centralizer hc.hyp.standard).1))
    have hrK : r ∈ centralizer (A : Set G) := by
      have := map_mono (f := (MulAut.conj c⁻¹⁻¹).toMonoidHom) hc.sylowR.le hr
      rwa [← rightConjugate, hKc] at this
    have hr2 : r ^ 2 ^ 1 = 1 := by
      have h1 := (mem_rightConjugate_iff R c⁻¹ r).1 hr
      have h2 := (hc.elemR h32).2 _ h1
      rw [pow_one]
      calc r ^ 2 = c * (c⁻¹ * r * c⁻¹⁻¹) ^ 2 * c⁻¹ := by rw [inv_inv, sq, sq]; group
        _ = 1 := by rw [h2, mul_one, mul_inv_cancel]
    exact hr1 (Subtype.ext (RankTwoL3Even.eq_one_of_odd_of_pow_two
      (RankTwoL3Even.odd_orderOf_of_mem hZA' (mem_inf.2 ⟨hle hr, hrK⟩)) hr2))
  have hbot := inf_eq_bot_of_reps hZC hψ h4 h32 h34 hsec hOut hZA hcover hres
  rw [inf_of_le_left hle] at hbot
  exact hsec.T_ne_bot hbot

theorem not_le_normalizer_qLift [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (hc : Sec3 A R T g) (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A))))
    (hZA : Odd (Nat.card (center A))) {reps : List C} (hcover : ClassesCover reps)
    (hres : ∀ y ∈ reps, ResidualMem y) (hchar : ∀ y ∈ reps, CharTwo y)
    (hD0 : ∀ y ∈ reps, D0Data y (zx y)) {Ql : Subgroup C} (hQodd : Odd (Nat.card Ql)) :
    ¬ centralizer (qLift ψ T Ql : Set G) ⊓ centralizer (T : Set G) ≤ normalizer (R : Set G) := by
  intro hle
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hsw := hc.swap
  set R₁ := rightConjugate R g⁻¹ with hR₁
  have hX : CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) = rightConjugate
      (CFSG.Quasithin.perfectCore (A ⊓ centralizer (R₁ : Set G))) g := by
    rw [hc.perfectCore_eq h32 h4 h34 hOut, RankTwoClassical.rightConjugate_perfectCore,
      RankTwoClassical.rightConjugate_inf, ← AS76b.centralizer_rightConjugate,
      RankTwoClassical.rightConjugate_inv_rightConjugate]
  have hM₁ : ∀ w ∈ qLift ψ T Ql, g * w * g⁻¹ ∈ A ⊓ centralizer (R₁ : Set G) := by
    intro w hw
    have h1 : w ∈ CFSG.Quasithin.perfectCore (A ⊓ centralizer (T : Set G)) := (mem_inf.1 hw).1
    rw [hX, mem_rightConjugate_iff] at h1
    exact CFSG.Quasithin.perfectCore_le _ h1
  obtain ⟨⟨r₀, hr₀⟩, hr₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hsw.T_ne_bot
  have hr₀1' : r₀ ≠ 1 := fun h => hr₀1 (Subtype.ext h)
  have hr₀N := hsw.le_normalizer hr₀
  obtain ⟨x', hx'⟩ := exists_conj_of_mem hψ hsw h32 h4 h34 hr₀ hr₀N
  obtain ⟨hx'2, hx'1⟩ := involution_of_conj hZC hψ hsw h32 hr₀ hr₀N hx'
  have hr₀2 : r₀ ^ 2 = 1 := (hsw.elemT h32).2 r₀ hr₀
  have hD0' : D0Data x' (zx x') := by
    obtain ⟨y, hy, hyx⟩ := hcover x' hx'2 (hx'1 hr₀1')
    obtain ⟨c, rfl⟩ := isConj_iff.1 hyx
    rw [zx_conj]
    exact (hD0 y hy).conj c
  set Q₁ := rightConjugate (qLift ψ T Ql) g⁻¹ with hQ₁
  have hQ₁mem : ∀ v, v ∈ Q₁ ↔ g⁻¹ * v * g ∈ qLift ψ T Ql := by
    intro v
    rw [hQ₁, mem_rightConjugate_iff, inv_inv]
  have hQ₁le : Q₁ ≤ A ⊓ centralizer ({r₀} : Set G) := by
    intro v hv
    have h1 := hM₁ _ ((hQ₁mem v).1 hv)
    rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h1
    exact mem_inf.2 ⟨(mem_inf.1 h1).1, mem_centralizer_singleton_iff.2
      (mem_centralizer_iff.1 (mem_inf.1 h1).2 r₀ hr₀).symm⟩
  have hSle : img ψ Q₁ ≤ cent x' := by
    rw [← img_centralizer_eq hZC hψ hZA hr₀N hr₀2 hx']
    exact img_mono hQ₁le
  have hSodd : Odd (Nat.card (img ψ Q₁)) := by
    refine AS76b.Lemma22.odd_card_of_forall_orderOf_ne_two fun c hc' h2 => ?_
    obtain ⟨v, hv, hvN, hvc⟩ := mem_img.1 hc'
    have hvo : Odd (orderOf v) := by
      have h1 := odd_orderOf_of_mem_qLift hψ hZA hQodd ((hQ₁mem v).1 hv)
      have e : g⁻¹ * v * g = MulAut.conj g⁻¹ v := by simp
      rwa [e, MulEquiv.orderOf_eq] at h1
    have h3 : orderOf c ∣ orderOf v := by
      have h4 := orderOf_map_dvd ψ ⟨v, hvN⟩
      rwa [hvc, orderOf_injective _ hinj, Subgroup.orderOf_mk] at h4
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 hvo) (even_iff_two_dvd.2 h3)
  obtain ⟨Dl₀, hDp, hDS, -, hDW⟩ := hD0' (img ψ Q₁) hSle hSodd
  have hD₀Q : ∀ v ∈ Q₁, ∀ d ∈ leviLift ψ (inn Dl₀), d * v = v * d := by
    intro v hv d hd
    have hvA : v ∈ A := (mem_inf.1 (hQ₁le hv)).1
    refine mem_centralizer_singleton_iff.1
      (leviLift_le_centralizer hψ (le_normalizer hvA) (fun s hs => ?_) hd)
    obtain ⟨c, hc'⟩ := hψ.map_mem v hvA
    have hcS : c ∈ img ψ Q₁ := mem_img.2 ⟨v, hv, le_normalizer hvA, hc'.symm⟩
    obtain ⟨e, he, rfl⟩ := hs
    rw [← hc', ← map_mul, ← map_mul]
    congr 1
    exact mem_centralizer_iff.1 (hDS he) c hcS
  have hD₀N : ∀ d ∈ leviLift ψ (inn Dl₀), d ∈ normalizer (R₁ : Set G) := by
    intro d hd
    have hdA : d ∈ A := leviLift_le hd
    have h1 : g⁻¹ * d * g ∈ centralizer (qLift ψ T Ql : Set G) ⊓ centralizer (T : Set G) := by
      refine mem_inf.2 ⟨mem_centralizer_iff.2 fun w hw => ?_, mem_centralizer_iff.2 fun t ht => ?_⟩
      · have hv : g * w * g⁻¹ ∈ Q₁ := by
          rw [hQ₁mem]
          simpa [mul_assoc] using hw
        have h2 := (hD₀Q _ hv d hd).symm
        calc w * (g⁻¹ * d * g) = g⁻¹ * (g * w * g⁻¹ * d) * g := by group
          _ = g⁻¹ * (d * (g * w * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * d * g * w := by group
      · have hgt : g * t * g⁻¹ ∈ centralizer (A : Set G) :=
          hsw.sylowR.le (conj_mem_rightConjugate_inv ht g)
        have h2 : g * t * g⁻¹ * d = d * (g * t * g⁻¹) := (mem_centralizer_iff.1 hgt d hdA).symm
        calc t * (g⁻¹ * d * g) = g⁻¹ * (g * t * g⁻¹ * d) * g := by group
          _ = g⁻¹ * (d * (g * t * g⁻¹)) * g := by rw [h2]
          _ = g⁻¹ * d * g * t := by group
    rw [hR₁, AS76b.mem_normalizer_rightConjugate_iff, inv_inv]
    exact hle h1
  have hR₁A := inf_eq_bot_of_reps hZC hψ h4 h32 h34 hsw hOut hZA hcover hres
  have hD₀R : ∀ d ∈ leviLift ψ (inn Dl₀), ∀ r ∈ R₁, d * r = r * d := by
    intro d hd r hr
    have hdA : d ∈ A := leviLift_le hd
    have h1 : d * r * d⁻¹ * r⁻¹ ∈ R₁ :=
      mul_mem ((mem_normalizer_iff.1 (hD₀N d hd) r).1 hr) (inv_mem hr)
    have h2 : d * r * d⁻¹ * r⁻¹ ∈ A := by
      have h3 : r * d⁻¹ * r⁻¹ ∈ A :=
        (mem_normalizer_iff.1 (hsw.le_normalizer hr) _).1 (inv_mem hdA)
      have he : d * r * d⁻¹ * r⁻¹ = d * (r * d⁻¹ * r⁻¹) := by group
      rw [he]
      exact mul_mem hdA h3
    have h5 : d * r * d⁻¹ * r⁻¹ ∈ R₁ ⊓ A := mem_inf.2 ⟨h1, h2⟩
    rw [hR₁A, mem_bot] at h5
    calc d * r = d * r * d⁻¹ * r⁻¹ * (r * d) := by group
      _ = r * d := by rw [h5, one_mul]
  have hW : img ψ R₁ ≤ zx x' :=
    actsIn_zx_of_reps hZC hψ h4 h32 h34 hsw hOut hZA hcover hres hchar hr₀ hr₀1' hr₀N hx'
  have hWbot : img ψ R₁ ≠ ⊥ := by
    intro h
    have h1 : x' ∈ img ψ R₁ := mem_img.2 ⟨r₀, hr₀, hr₀N, hx'⟩
    rw [h, mem_bot] at h1
    exact hx'1 hr₀1' h1
  refine hDW (img ψ R₁) hW hWbot fun e he => centralizer_le_normalizer _
    (mem_centralizer_iff.2 fun c hc' => ?_)
  obtain ⟨r, hr, hrN, hrc⟩ := mem_img.1 hc'
  obtain ⟨d, hd, hdψ⟩ := exists_mem_leviLift hψ (inn_le_range _) (commutator_inn hDp)
    (conj_mem_inn he)
  have hdN := le_normalizer (leviLift_le hd)
  have h1 := congrArg ψ (Subtype.ext (hD₀R d hd r hr) :
    (⟨d * r, mul_mem hdN hrN⟩ : normalizer (A : Set G)) = ⟨r * d, mul_mem hrN hdN⟩)
  rw [psi_mul hdN hrN, psi_mul hrN hdN, hdψ, hrc, ← map_mul, ← map_mul] at h1
  exact (hinj h1).symm

omit [Finite G] in
theorem exists_diag (h3 : Nat.Coprime 3 (Nat.card (center ↥A))) {Q : Subgroup G} (hQA : Q ≤ A)
    {Ql Ll : Subgroup C}
    (hQψ : ∀ w (hw : w ∈ Q), ∃ q ∈ Ql, ψ ⟨w, le_normalizer (hQA hw)⟩ = MulAut.conj q)
    (hLl : ⁅Ll, Ll⁆ = Ll) {y : C} (hy : y ∈ centralizer (Ql : Set C))
    (hy3 : ∃ k : ℕ, y ^ 3 ^ k = 1) (hyL : ¬ InducesInner y Ll) :
    ∃ y' ∈ A ⊓ centralizer (Q : Set G), (∃ k : ℕ, y' ^ 3 ^ k = 1) ∧
      ¬ InducesInner y' (leviLift ψ (inn Ll)) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  obtain ⟨k, hk⟩ := hy3
  set m := 3 ^ k with hm
  set n := Nat.card (center ↥A) with hn
  have hcop : Nat.Coprime n m := Nat.Coprime.pow_right k h3.symm
  obtain ⟨a, ha, haψ⟩ := hψ.exists_eq (MulAut.conj y) ⟨y, rfl⟩
  have haN := le_normalizer ha
  set e := n ^ Nat.totient m with he
  have he1 : e ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  have hm0 : 0 < m := by positivity
  have htot : Nat.totient m = Nat.totient m - 1 + 1 :=
    (Nat.sub_add_cancel (Nat.totient_pos.2 hm0)).symm
  have hye : y ^ e = y := by
    have h1 : orderOf y ∣ m := orderOf_dvd_of_pow_eq_one hk
    exact (pow_eq_pow_iff_modEq.2 (Nat.ModEq.of_dvd h1 he1)).trans (pow_one y)
  set b := a ^ e with hb
  have hbA : b ∈ A := pow_mem ha e
  have hbN := le_normalizer hbA
  have hbψ : ψ ⟨b, hbN⟩ = MulAut.conj y := by
    rw [show (⟨b, hbN⟩ : normalizer (A : Set G)) = ⟨a, haN⟩ ^ e from rfl, map_pow, haψ,
      ← map_pow, hye]
  have hZn : ∀ z ∈ A ⊓ centralizer (A : Set G), z ^ n = 1 := by
    intro z hz
    have h1 := orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard _ hz)
    rwa [RankTwoL3Even.card_inf_centralizer_eq] at h1
  have ham : a ^ m ∈ A ⊓ centralizer (A : Set G) := by
    refine mem_inf.2 ⟨pow_mem ha m, (hψ.eq_one_iff ⟨_, pow_mem haN m⟩).1 ?_⟩
    rw [show (⟨a ^ m, pow_mem haN m⟩ : normalizer (A : Set G)) = ⟨a, haN⟩ ^ m from rfl,
      map_pow, haψ, ← map_pow, hk, map_one]
  have hbm : b ^ m = 1 := by
    rw [hb, ← pow_mul, mul_comm e m, pow_mul, he, htot, pow_succ', pow_mul, hZn _ ham, one_pow]
  refine ⟨b, mem_inf.2 ⟨hbA, mem_centralizer_iff.2 fun w hw => ?_⟩, ⟨k, hbm⟩, ?_⟩
  ·
    obtain ⟨q, hq, hqw⟩ := hQψ w hw
    have hwA := hQA hw
    have hwN := le_normalizer hwA
    set z := b * w * b⁻¹ * w⁻¹ with hz
    have hzA : z ∈ A := mul_mem (mul_mem (mul_mem hbA hwA) (inv_mem hbA)) (inv_mem hwA)
    have hzC : z ∈ centralizer (A : Set G) := by
      refine (hψ.eq_one_iff ⟨z, le_normalizer hzA⟩).1 ?_
      have e1 : (⟨z, le_normalizer hzA⟩ : normalizer (A : Set G)) =
          ⟨b, hbN⟩ * ⟨w, hwN⟩ * ⟨b, hbN⟩⁻¹ * ⟨w, hwN⟩⁻¹ := rfl
      have hyq : y * q = q * y := (mem_centralizer_iff.1 hy q hq).symm
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hbψ, hqw,
        show MulAut.conj y * MulAut.conj q * (MulAut.conj y)⁻¹ * (MulAut.conj q)⁻¹ =
          MulAut.conj (y * q * y⁻¹ * q⁻¹) by simp only [map_mul, map_inv],
        show y * q * y⁻¹ * q⁻¹ = 1 by rw [hyq]; group, map_one]
    have hzb : Commute z b := (mem_centralizer_iff.1 hzC b hbA).symm
    have hbw : b * w * b⁻¹ = z * w := by rw [hz]; group
    have key : ∀ j : ℕ, b ^ j * w * (b ^ j)⁻¹ = z ^ j * w := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hzjb : z ^ j * b = b * z ^ j := (hzb.pow_left j).eq
        calc b ^ (j + 1) * w * (b ^ (j + 1))⁻¹ = b * (b ^ j * w * (b ^ j)⁻¹) * b⁻¹ := by group
          _ = b * (z ^ j * w) * b⁻¹ := by rw [ih]
          _ = z ^ j * (b * w * b⁻¹) := by rw [← mul_assoc b, ← hzjb]; group
          _ = z ^ (j + 1) * w := by rw [hbw]; group
    have hzm : z ^ m = 1 := by
      have h1 := key m
      rw [hbm, one_mul, inv_one, mul_one] at h1
      exact (mul_eq_right.1 h1.symm)
    have hzn : z ^ n = 1 := hZn z (mem_inf.2 ⟨hzA, hzC⟩)
    have hz1 : z = 1 := by
      have h1 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hzm
      have h2 : orderOf z ∣ n := orderOf_dvd_of_pow_eq_one hzn
      have h5 : orderOf z ∣ Nat.gcd n m := Nat.dvd_gcd h2 h1
      rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one] at h5
      exact orderOf_eq_one_iff.1 h5
    have h6 : b * w * b⁻¹ * w⁻¹ = 1 := hz1
    calc w * b = (b * w * b⁻¹ * w⁻¹)⁻¹ * (b * w) := by group
      _ = b * w := by rw [h6, inv_one, one_mul]
  ·
    rintro ⟨l, hl, hlx⟩
    apply hyL
    obtain ⟨lb, hlb, hlbψ⟩ := exists_mem_of_mem_leviLift hl
    refine ⟨lb, hlb, fun xb hxb => ?_⟩
    obtain ⟨x, hx, hxψ⟩ := exists_mem_leviLift hψ (inn_le_range Ll) (commutator_inn hLl)
      (conj_mem_inn hxb)
    obtain ⟨u, huZ, hueq⟩ := hlx x hx
    have hueq' : (u : G) = b * x * b⁻¹ * (l * x * l⁻¹)⁻¹ := hueq
    have hlN := le_normalizer (leviLift_le hl)
    have hxN := le_normalizer (leviLift_le hx)
    have huN : (u : G) ∈ normalizer (A : Set G) := le_normalizer (leviLift_le u.2)
    have hψu : ψ ⟨u, huN⟩ = MulAut.conj (y * xb * y⁻¹ * (lb * xb * lb⁻¹)⁻¹) := by
      have e1 : (⟨u, huN⟩ : normalizer (A : Set G)) =
          ⟨b, hbN⟩ * ⟨x, hxN⟩ * ⟨b, hbN⟩⁻¹ * (⟨l, hlN⟩ * ⟨x, hxN⟩ * ⟨l, hlN⟩⁻¹)⁻¹ :=
        Subtype.ext hueq'
      rw [e1]
      simp only [map_mul, map_inv, hbψ, hxψ, hlbψ]
    obtain ⟨ub, hub, hubψ⟩ := exists_mem_of_mem_leviLift u.2
    have hueq2 : ub = y * xb * y⁻¹ * (lb * xb * lb⁻¹)⁻¹ := hinj (hubψ.symm.trans hψu)
    rw [← hueq2]
    refine ⟨⟨ub, hub⟩, mem_center_iff.2 fun v => Subtype.ext ?_, rfl⟩
    obtain ⟨v', hv', hv'ψ⟩ := exists_mem_leviLift hψ (inn_le_range Ll) (commutator_inn hLl)
      (conj_mem_inn v.2)
    have hv'N := le_normalizer (leviLift_le hv')
    have h1 : (v' : G) * u = u * v' :=
      congrArg Subtype.val (mem_center_iff.1 huZ ⟨v', hv'⟩)
    have h2 := congrArg ψ (Subtype.ext h1 :
      (⟨v' * u, mul_mem hv'N huN⟩ : normalizer (A : Set G)) = ⟨u * v', mul_mem huN hv'N⟩)
    rw [psi_mul hv'N huN, psi_mul huN hv'N, hv'ψ, hubψ, ← map_mul, ← map_mul] at h2
    exact hinj h2

theorem config814_of_pinned [Finite C] (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    (D : ExcModel A) (hc : Sec3 A R T g) (hZA : Odd (Nat.card (center A)))
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (hq2 : 2 < D.q)
    {reps : List C} (hcover : ClassesCover reps) (hres : ∀ y ∈ reps, ResidualMem y)
    (hchar : ∀ y ∈ reps, CharTwo y) (hD0 : ∀ y ∈ reps, D0Data y (zx y)) {y₀ : C}
    (hT : ActsIn ψ T (zx y₀)) {Dl Ql Hl Ll : Subgroup C}
    (hLC : LeviClassData D (zx y₀) Dl Ql Hl Ll)
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A))) :
    Config814 D g R T (qLift ψ T Ql) := by
  have hinj := RankTwoHypIIY.conj_injective_of_center_eq_bot hZC
  have hTA := inf_eq_bot_of_reps hZC hψ h4 h32 h34 hc hOut hZA hcover hres
  have hlevi' := hLC.levi
  have hLlp := commutator_eq_of_isQuasisimple hlevi'.quasisimple
  have hQodd := hlevi'.odd_Q
  have hlay := layerCentralizer_qLift hZC hψ h4 h32 h34 hc hT hlevi'
  refine
    { not_mem := hc.not_mem
      sylowR := hc.sylowR
      sylowT := hc.sylowT
      le_normalizer := hc.le_normalizer
      commute := commutator_eq_bot_iff_le_centralizer.2 hc.le_centralizer
      two_lt_q := hq2
      le := qLift_le
      ne_bot := ?_
      quasisimple := ?_
      odd_center := ?_
      levi := ?_
      sylow_inf := ?_
      le_sup := ?_
      inf_eq_bot := ?_
      not_le := not_le_normalizer_qLift hZC hψ h4 h32 h34 hc hOut hZA hcover hres hchar hD0 hQodd
      noConj := ?_
      diag := ?_ }
  ·
    obtain ⟨⟨q₁, hq₁⟩, hq₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hlevi'.Q_ne_bot
    obtain ⟨w, hw, hwψ⟩ := exists_mem_qLift hψ h4 h32 h34 hc hT hlevi'.D_le hlevi'.D_perfect
      hlevi'.Q_le hq₁
    intro hbot
    have hw1 : w = 1 := by
      have := hw
      rw [hbot, mem_bot] at this
      exact this
    subst hw1
    apply hq₁1
    refine Subtype.ext (hinj ?_)
    rw [← hwψ]
    show ψ 1 = MulAut.conj (1 : C)
    rw [map_one, map_one]
  · rw [hlay]
    exact isQuasisimple_leviLift_inn hZC hψ hLlp hlevi'.quasisimple
  · rw [hlay]
    exact odd_card_center_leviLift hZC hψ hZA hLlp hlevi'.odd_center
  · rw [hlay]
    exact hLC.type _ ⟨quotEquiv_leviLift hZC hψ hLlp⟩
  · rw [hlay]
    refine isSylowOf_of_autFix hZC hψ hc.hyp hc.sylowR hLC.autFix qLift_le leviLift_le
      (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨w, hw, hwψ⟩ := exists_mem_qLift hψ h4 h32 h34 hc hT hlevi'.D_le hlevi'.D_perfect
        hlevi'.Q_le hy
      exact ⟨w, hw, _, hwψ⟩
    · obtain ⟨l, hl, hlψ⟩ := exists_mem_leviLift hψ (inn_le_range Ll) (commutator_inn hLlp)
        (conj_mem_inn hy)
      exact ⟨l, hl, _, hlψ⟩
  · rw [hlay]
    exact le_sup_leviLift_inn hψ h4 h32 h34 hc hZA hT hLlp hlevi'.Z_le
  · rw [hlay, eq_bot_iff, ← hTA]
    exact inf_le_inf_left T leviLift_le
  · intro n _ _ c hle
    rw [hlay] at hle
    exact not_conj_le hZC hψ h4 h32 h34 hc hOut hZA hcover hres c (hle.trans leviLift_le)
  · intro hD hL3
    rw [hlay] at hL3 ⊢
    obtain ⟨y, hy, hy3, hyL⟩ :=
      hLC.diag hD (statedPSL_of_mulEquiv (quotEquiv_leviLift hZC hψ hLlp).symm hL3)
    exact exists_diag hZC hψ (h3 hD) qLift_le (fun w hw => exists_of_mem_qLift hw) hLlp hy hy3
      hyL

theorem exists_pinned (h4 : Asc75Theorem4) (h32 : Lemma32) (h34 : Asc08Lemma34)
    {T₀ : Subgroup G} {g₀ : G} (hc₀ : Sec3 A R T₀ g₀) {reps : List C}
    (hcover : ClassesCover reps) :
    ∃ (T : Subgroup G) (g : G), Sec3 A R T g ∧ ∃ y ∈ reps, ∃ t ∈ T, t ≠ 1 ∧
      ∃ htN : t ∈ normalizer (A : Set G), ψ ⟨t, htN⟩ = MulAut.conj y := by
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hc₀.T_ne_bot
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have ht₀N := hc₀.le_normalizer ht₀
  obtain ⟨x₀, hx₀⟩ := exists_conj_of_mem hψ hc₀ h32 h4 h34 ht₀ ht₀N
  obtain ⟨hx₀2, hx₀1⟩ := involution_of_conj hZC hψ hc₀ h32 ht₀ ht₀N hx₀
  obtain ⟨y₀, hy₀, hy₀x⟩ := hcover x₀ hx₀2 (hx₀1 ht₀1')
  obtain ⟨a, ha, hc, ht₁T, ht₁N, hψt₁⟩ := exists_pin hψ hc₀ ht₀ ht₀N hx₀ hy₀x
  refine ⟨_, _, hc, y₀, hy₀, _, ht₁T, fun h => ht₀1' ?_, ht₁N, hψt₁⟩
  calc t₀ = a⁻¹ * (a * t₀ * a⁻¹) * a := by group
    _ = 1 := by rw [h]; group

end Root

section Assembly

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem exists_config814_of_classes (h32 : Lemma32) (h33 : Lemma33Three) (h4 : Asc75Theorem4)
    (h34 : Asc08Lemma34) (D : ExcModel A) (hA : Hyp31 A) (hZA : Odd (Nat.card (center A)))
    {C : Type} [Group C] [Finite C] (hZC : center C = ⊥) (e : rankTwoQuot A ≃* C)
    (hOut : Odd (Nat.card (commutator (outerAutomorphismGroup ↥A)))) (q : ℕ) (hq : D.q = q)
    {reps : List C} (hcover : ClassesCover reps)
    (hcls : ∀ x ∈ reps, ∃ Z, ClassData q x Z ∧ ResidualMem x)
    (hlevi : 2 < q → ∀ x ∈ reps, ∃ Z Dl Ql Hl Ll : Subgroup C,
      CentreData x Z ∧ LeviClassData D Z Dl Ql Hl Ll ∧ D0Data x Z)
    (h3 : D.IsTrialityFour → Nat.Coprime 3 (Nat.card (center ↥A))) :
    ∃ (g : G) (R T Q : Subgroup G), Config814 D g R T Q := by
  classical
  have hAp : commutator ↥A = ⊤ := hA.standard.1.1
  obtain ⟨ψ, hψ⟩ := exists_isActionHom (RankTwoHypIIY.autModel_mulAut hZC) hAp e
  have hres : ∀ y ∈ reps, ResidualMem y := fun y hy => (hcls y hy).choose_spec.2
  have hchar : ∀ y ∈ reps, CharTwo y := fun y hy => (hcls y hy).choose_spec.1.charTwo
  have hcard : ∀ y ∈ reps, Nat.card (zx y) = q := fun y hy => by
    obtain ⟨Z, hZ, -⟩ := hcls y hy
    rw [zx_eq_of_centreData hZ.centre, hZ.card]
  obtain ⟨g₀, hg₀, R, T₀, hR, hT₀, -, -, hTR, -, -⟩ := section3Config_of h32 h33 h4 h34 G A hA
  have hc₀ : Sec3 A R T₀ g₀ := ⟨hA, hR, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨T, g, hc, y₀, hy₀, t₁, ht₁T, ht₁1, ht₁N, hψt₁⟩ :=
    exists_pinned hZC hψ h4 h32 h34 hc₀ hcover
  have hT : ActsIn ψ T (zx y₀) :=
    actsIn_zx_of_reps hZC hψ h4 h32 h34 hc hOut hZA hcover hres hchar ht₁T ht₁1 ht₁N hψt₁
  have hq2 : 2 < q := by
    have h1 := card_le_of_actsIn hZC hψ h4 h32 h34 hc hT
    rw [hcard y₀ hy₀] at h1
    have h2 : 4 ≤ Nat.card T := by rw [hc.card_eq]; exact hc.four_le
    omega
  obtain ⟨Z, Dl, Ql, Hl, Ll, hZ, hLC, -⟩ := hlevi hq2 y₀ hy₀
  rw [← zx_eq_of_centreData hZ] at hLC
  have hD0 : ∀ y ∈ reps, D0Data y (zx y) := by
    intro y hy
    obtain ⟨Z', -, -, -, -, hZ', -, hD0'⟩ := hlevi hq2 y hy
    rw [zx_eq_of_centreData hZ']
    exact hD0'
  exact ⟨g, R, T, _, config814_of_pinned hZC hψ h4 h32 h34 D hc hZA hOut (by rw [hq]; exact hq2)
    hcover hres hchar hD0 hT hLC h3⟩

end Assembly

end CFSG.ComponentClassification.RankTwoExceptional.Exc
