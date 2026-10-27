module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma85Aux

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_normalizer_le_normalizer_inf (A B : Subgroup G) :
    Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) ≤
      Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := (Subgroup.mem_normalizer_iff.1 hg.1) y
  have h2 := (Subgroup.mem_normalizer_iff.1 hg.2) y
  simp only [Subgroup.mem_inf]
  rw [h1, h2]

omit [Finite G] in
theorem glaPPrimeCoreOf_le_self' (p : ℕ) (X : Subgroup G) : GLAPPrimeCoreOf p X ≤ X :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem barX_eq_bot_of_le {p : ℕ} {X K : Subgroup G} (h : K ≤ GLAPPrimeCoreOf p X) :
    barX p X K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (k : G) ∈ GLAPPrimeCoreOf p X := h ((Subgroup.mem_subgroupOf).1 hk)
  obtain ⟨k', hk', hkk⟩ := hk'
  have : k' = k := Subtype.ext hkk
  subst this
  exact (QuotientGroup.eq_one_iff k').2 hk'

omit [Finite G] in
theorem le_glaPPrimeCoreOf_of_barX_eq_bot {p : ℕ} {X K : Subgroup G} (hKX : K ≤ X)
    (h : barX p X K = ⊥) : K ≤ GLAPPrimeCoreOf p X := by
  intro k hk
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨k, hKX hk⟩ ∈ barX p X K :=
    ⟨⟨k, hKX hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
  rw [h, Subgroup.mem_bot] at h1
  exact ⟨⟨k, hKX hk⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩

theorem glaPPrimeCoreOf_inf_eq {K N : Subgroup G} (hcov : Covers3 N K) :
    GLAPPrimeCoreOf 3 (K ⊓ N) = (K ⊓ N) ⊓ GLAPPrimeCoreOf 3 K := by
  set H := K ⊓ N with hH
  set O := GLAPPrimeCoreOf 3 K with hO
  have hHK : H ≤ K := inf_le_left
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 K
  have hcov' : K ≤ H ⊔ O := by rwa [hH, inf_comm]
  have hQH : GLAPPrimeCoreOf 3 H ≤ H := glaPPrimeCoreOf_le_self' 3 H
  have hQO : GLAPPrimeCoreOf 3 H ≤ O := by
    set Q := GLAPPrimeCoreOf 3 H with hQ
    have hQN : Q ≤ Subgroup.normalizer (O : Set G) := (hQH.trans hHK).trans hKO
    have hS3 : ¬ 3 ∣ Nat.card (Q ⊔ O : Subgroup G) := by
      have h := Lemma85Aux.card_sup_mul_card_inf' hQN
      intro hd
      have h1 : 3 ∣ Nat.card Q * Nat.card O := h ▸ Dvd.dvd.mul_right hd _
      rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h1 with h2 | h2
      · exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three H h2
      · exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K h2
    have hSN : K ≤ Subgroup.normalizer ((Q ⊔ O : Subgroup G) : Set G) := by
      refine hcov'.trans (sup_le ?_ ?_)
      · exact fun h hh => Subgroup.inf_normalizer_le_normalizer_sup Q O
          ⟨le_normalizer_glaPPrimeCoreOf 3 H hh, hKO (hHK hh)⟩
      · exact (le_sup_right : O ≤ Q ⊔ O).trans Subgroup.le_normalizer
    have := Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three
      (sup_le (hQH.trans hHK) (glaPPrimeCoreOf_le_self' 3 K)) hSN hS3
    exact le_sup_left.trans this
  refine le_antisymm (le_inf hQH hQO) ?_
  refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three inf_le_left ?_ ?_
  · exact fun h hh => inf_normalizer_le_normalizer_inf H O
      ⟨Subgroup.le_normalizer hh, hKO (hHK hh)⟩
  · intro hd
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      (hd.trans (Subgroup.card_dvd_of_le inf_le_right))


omit [Finite G] in
theorem glaPLayer_gLBConj (p : ℕ) (g : G) (X : Subgroup G) :
    GLAPLayer p (GLBConj g X) = GLBConj g (GLAPLayer p X) := by
  refine gLBConj_eq_of_forall_ge (F := GLAPLayer p) (fun g X => ?_) g X
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (glaPComponent_gLBConj hL g)

omit [Finite G] in
theorem mem_normalizer_glaPLayer {p : ℕ} {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer p X : Set G) := by
  rw [mem_normalizer_iff_gLBConj_eq, ← glaPLayer_gLBConj, gLBConj_eq_of_mem_normalizer hg]

omit [Finite G] in
theorem le_normalizer_glaPLayer (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (GLAPLayer p X : Set G) :=
  fun _ hg => mem_normalizer_glaPLayer (Subgroup.le_normalizer hg)

omit [Finite G] in
theorem mem_of_pow_mem_of_coprime {J : Subgroup G} {q : G} {n : ℕ}
    (hcop : Nat.Coprime n (orderOf q)) (h : q ^ n ∈ J) : q ∈ J := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hq : q = (q ^ n) ^ a := by
    calc q = q ^ ((n : ℤ) * a + (orderOf q : ℤ) * b) := by
          rw [show ((n : ℤ) * a + (orderOf q : ℤ) * b) = 1 by linarith, zpow_one]
      _ = (q ^ n) ^ a := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, pow_orderOf_eq_one, one_zpow,
            mul_one]
  rw [hq]
  exact zpow_mem h a

omit [Finite G] in
theorem commutatorElement_mul_mul_of_commute' {z₁ z₂ l₁ l₂ : G} (h₁₁ : Commute z₁ l₁)
    (h₁₂ : Commute z₁ l₂) (h₂₁ : Commute z₂ l₁) (h₂₂ : Commute z₂ l₂) (hz : Commute z₁ z₂) :
    ⁅z₁ * l₁, z₂ * l₂⁆ = ⁅l₁, l₂⁆ := by
  have e₁ : z₁ * l₁ = l₁ * z₁ := h₁₁.eq
  have e₂ : z₂ * l₂ = l₂ * z₂ := h₂₂.eq
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_inv_rev]
  have c1 : Commute z₁ (l₁ * (z₂ * l₂) * l₁⁻¹) :=
    (h₁₁.mul_right (hz.mul_right h₁₂)).mul_right h₁₁.inv_right
  have c2 : Commute z₂ (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
    ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  calc z₁ * l₁ * (z₂ * l₂) * (l₁⁻¹ * z₁⁻¹) * (l₂⁻¹ * z₂⁻¹)
      = (z₁ * (l₁ * (z₂ * l₂) * l₁⁻¹) * z₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by group
    _ = l₁ * (z₂ * l₂) * l₁⁻¹ * l₂⁻¹ * z₂⁻¹ := by rw [c1.eq, mul_inv_cancel_right]
    _ = z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂⁻¹ := by
        rw [show l₁ * (z₂ * l₂) = z₂ * (l₁ * l₂) by
          rw [← mul_assoc, ← h₂₁.eq, mul_assoc]]
        group
    _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]

omit [Finite G] in
theorem le_commutator_of_isQuasisimple {J : Subgroup G} (hJ : CFSG.Open.IsQuasisimple ↥J) :
    J ≤ ⁅J, J⁆ := by
  have h := congrArg (Subgroup.map J.subtype) hJ.1
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  intro x hx
  rw [h]
  exact hx

omit [Finite G] in
theorem centralizes_of_commutator_le_proper {J P : Subgroup G} {c : G}
    (hJ : CFSG.Open.IsQuasisimple ↥J)
    (hPJ : P ≤ J) (hJP : J ≤ Subgroup.normalizer (P : Set G)) (hne : ¬ J ≤ P)
    (hcomm : ∀ z ∈ J, c * z * c⁻¹ * z⁻¹ ∈ P) : ∀ z ∈ J, c * z = z * c := by
  have hPn : (P.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPJ).2 hJP
  have hPc : P.subgroupOf J ≤ Subgroup.center ↥J :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hJ _
      (fun htop => hne (Subgroup.subgroupOf_eq_top.1 htop))
  have hcen : ∀ w ∈ P, ∀ y ∈ J, Commute w y := fun w hw y hy => by
    have := Subgroup.mem_center_iff.1 (hPc (show (⟨w, hPJ hw⟩ : J) ∈ P.subgroupOf J from hw)) ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  have hcc : ⁅J, J⁆ ≤ Subgroup.centralizer ({c} : Set G) := by
    refine Subgroup.commutator_le.2 fun x hx y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    set wx := c * x * c⁻¹ * x⁻¹ with hwx
    set wy := c * y * c⁻¹ * y⁻¹ with hwy
    have hwxP : wx ∈ P := hcomm x hx
    have hwyP : wy ∈ P := hcomm y hy
    have ex : c * x * c⁻¹ = wx * x := by rw [hwx]; group
    have ey : c * y * c⁻¹ = wy * y := by rw [hwy]; group
    have key : c * ⁅x, y⁆ * c⁻¹ = ⁅x, y⁆ := by
      have e1 : c * ⁅x, y⁆ * c⁻¹ = ⁅c * x * c⁻¹, c * y * c⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e1, ex, ey]
      exact commutatorElement_mul_mul_of_commute' (hcen _ hwxP x hx) (hcen _ hwxP y hy)
        (hcen _ hwyP x hx) (hcen _ hwyP y hy) (hcen _ hwxP _ (hPJ hwyP))
    calc ⁅x, y⁆ * c = c * ⁅x, y⁆ * c⁻¹ * c := by rw [key]
      _ = c * ⁅x, y⁆ := by group
  intro z hz
  have := hcc (le_commutator_of_isQuasisimple hJ hz)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm


omit [Finite G] in
theorem layer_le_normalizerO (K N : Subgroup G) : GLAPLayer 3 (K ⊓ N) ≤
    Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) :=
  (glaPLayer_le 3 _).trans (inf_le_left.trans (le_normalizer_glaPPrimeCoreOf 3 K))

structure LayerSetup (B N K : Subgroup G) : Prop where
  bN : B ≤ N
  bK : B ≤ Subgroup.normalizer (K : Set G)
  cov : Covers3 N K
  quasi : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore 3 ↥K)
  comp : IsComponentOf (barX 3 N (GLAPLayer 3 (K ⊓ N))) ⊤

namespace LayerSetup

variable {B N K : Subgroup G} (h : LayerSetup B N K)
include h

omit [Finite G] in
theorem layer_ne_bot : GLAPLayer 3 (K ⊓ N) ≠ ⊥ := by
  intro hJ
  have h1 : barX 3 N (GLAPLayer 3 (K ⊓ N)) = ⊥ := by
    rw [hJ]; exact barX_eq_bot_of_le bot_le
  have hq := h.comp.2.2
  rw [h1] at hq
  exact (Subgroup.nontrivial_iff_ne_bot _).1
    (CFSG.ComponentClassification.Quasisimple.nontrivial hq) rfl

omit [Finite G] in
theorem not_le_glaPPrimeCoreOf : ¬ K ≤ GLAPPrimeCoreOf 3 K := by
  intro hK
  have := CFSG.ComponentClassification.Quasisimple.nontrivial h.quasi
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥K ⧸ GLAPPrimeCore 3 ↥K)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  apply hz
  obtain ⟨k', hk', hkk⟩ := hK k.2
  have : k' = k := Subtype.ext hkk
  subst this
  exact (QuotientGroup.eq_one_iff _).2 hk'

omit [Finite G] in
theorem bNormalizesInf : B ≤ Subgroup.normalizer ((K ⊓ N : Subgroup G) : Set G) :=
  fun _ hb => inf_normalizer_le_normalizer_inf K N ⟨h.bK hb, Subgroup.le_normalizer (h.bN hb)⟩

omit [Finite G] in
theorem bNormalizesO : B ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 K : Set G) :=
  le_normalizer_glaPPrimeCoreOf_of_le' h.bK

omit [Finite G] in
theorem bNormalizesLayer : B ≤ Subgroup.normalizer (GLAPLayer 3 (K ⊓ N) : Set G) :=
  fun _ hb => mem_normalizer_glaPLayer (h.bNormalizesInf hb)

theorem le_layer_sup : K ≤ GLAPLayer 3 (K ⊓ N) ⊔ GLAPPrimeCoreOf 3 K := by
  set H := K ⊓ N with hH
  set O := GLAPPrimeCoreOf 3 K with hO
  have hHK : H ≤ K := inf_le_left
  obtain ⟨L, hL⟩ : ∃ L, GLAPComponent 3 H L := by
    by_contra hne
    push Not at hne
    exact h.layer_ne_bot (sSup_eq_bot.2 fun L hL => (hne L hL).elim)
  have hLJ : L ≤ GLAPLayer 3 H := le_sSup hL
  suffices hKL : K ≤ L ⊔ O from hKL.trans (sup_le_sup_right hLJ O)
  have hcov' : K ≤ H ⊔ O := by have := h.cov; rwa [Covers3, inf_comm] at this
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := hHK.trans (le_normalizer_glaPPrimeCoreOf 3 K)
  have hLK : L ≤ K := hL.1.trans hHK
  have hKbar : barX 3 K K ≤ barX 3 K H := by
    refine barX_le_of_forall hHK fun k hk => ?_
    have hk' : k ∈ ((H ⊔ O : Subgroup G) : Set G) := hcov' hk
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H O hHO] at hk'
    obtain ⟨j, hj, o, ho, rfl⟩ := hk'
    exact ⟨j, hj, by simpa using ho⟩
  have hH_top : barX 3 K H = ⊤ := by
    rw [eq_top_iff, ← barX_self 3 K]; exact hKbar
  have hsn : IsSubnormal (barX 3 K L) ⊤ := by
    have := isSubnormal_barX (C := K) 3 hL.2.1
    rwa [hH_top] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top h.quasi _ hsn with
    hcen | htop
  · exfalso
    have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
    have hLbot : barX 3 K L = ⊥ := by
      have h1 : barX 3 K ⁅L, L⁆ = ⁅barX 3 K L, barX 3 K L⁆ := barX_commutator 3 hLK hLK
      rw [hperf] at h1
      rw [h1]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hcen.trans (Subgroup.center_le_centralizer _))
    have hLO : L ≤ O := le_glaPPrimeCoreOf_of_barX_eq_bot hLK hLbot
    have hbot : barX 3 H L = ⊥ := barX_eq_bot_of_le (by
      rw [glaPPrimeCoreOf_inf_eq h.cov]; exact le_inf hL.1 hLO)
    have hq := hL.2.2.1.2.2
    change CFSG.Open.IsQuasisimple ↥(barX 3 H L) at hq
    rw [hbot] at hq
    exact (Subgroup.nontrivial_iff_ne_bot _).1
      (CFSG.ComponentClassification.Quasisimple.nontrivial hq) rfl
  · intro k hk
    have hle : barX 3 K K ≤ barX 3 K L := by rw [barX_self 3 K]; exact htop.ge
    obtain ⟨l, hl, hlk⟩ := exists_of_barX_le hle hk hk
    have := Subgroup.mul_mem_sup hl hlk
    simpa using this

theorem layer_inf_le : GLAPLayer 3 (K ⊓ N) ⊓ GLAPPrimeCoreOf 3 N ≤ GLAPPrimeCoreOf 3 K := by
  set H := K ⊓ N with hH
  have hJH : GLAPLayer 3 H ≤ H := glaPLayer_le 3 H
  have hQ : GLAPLayer 3 H ⊓ GLAPPrimeCoreOf 3 N ≤ GLAPPrimeCoreOf 3 H := by
    refine Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three (inf_le_left.trans hJH) ?_ ?_
    · intro x hx
      exact inf_normalizer_le_normalizer_inf _ _
        ⟨le_normalizer_glaPLayer 3 H hx,
          le_normalizer_glaPPrimeCoreOf 3 N (Subgroup.mem_inf.1 hx).2⟩
    · intro hd
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three N
        (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  rw [hH, glaPPrimeCoreOf_inf_eq h.cov] at hQ
  exact hQ.trans inf_le_right

theorem le_layer_of_pow_eq_one {x : G} (hx : x ∈ K ⊓ N) (hx3 : x ^ 3 = 1) :
    x ∈ GLAPLayer 3 (K ⊓ N) := by
  set H := K ⊓ N with hH
  set J := GLAPLayer 3 H with hJ
  set O := GLAPPrimeCoreOf 3 K with hO
  have hk : x ∈ ((J ⊔ O : Subgroup G) : Set G) := h.le_layer_sup hx.1
  rw [Subgroup.coe_mul_of_left_le_normalizer_right J O (layer_le_normalizerO K N)] at hk
  obtain ⟨j, hj, q, hq, hxe⟩ := hk
  have hxe : j * q = x := hxe
  subst hxe
  have hjH : j ∈ H := glaPLayer_le 3 H hj
  have hqH : q ∈ H := by
    have := H.mul_mem (H.inv_mem hjH) hx
    simpa using this
  have hqN : q ∈ Subgroup.normalizer (J : Set G) := le_normalizer_glaPLayer 3 H hqH
  have hq3 : q ^ 3 ∈ J := by
    have e : (j * q) ^ 3 = (j * (q * j * q⁻¹) * (q ^ 2 * j * (q ^ 2)⁻¹)) * q ^ 3 := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      group
    rw [hx3] at e
    have e' : q ^ 3 = (j * (q * j * q⁻¹) * (q ^ 2 * j * (q ^ 2)⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right e.symm
    rw [e']
    refine J.inv_mem (J.mul_mem (J.mul_mem hj ?_) ?_)
    · exact (Subgroup.mem_normalizer_iff.1 hqN j).1 hj
    · exact (Subgroup.mem_normalizer_iff.1 (pow_mem hqN 2) j).1 hj
  have hcop : Nat.Coprime 3 (orderOf q) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
    exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
      (hd.trans (Subgroup.orderOf_dvd_natCard O hq))
  exact J.mul_mem hj (mem_of_pow_mem_of_coprime hcop hq3)

theorem inf_le_layer (hF : IsElemAbelian 3 (B ⊓ K)) : B ⊓ K ≤ GLAPLayer 3 (K ⊓ N) := by
  intro x hx
  exact h.le_layer_of_pow_eq_one ⟨hx.2, h.bN hx.1⟩ (hF.2 x hx)


theorem mem_centralizerQuot_of_comm {b : G} (hb : b ∈ B)
    (hcomm : ∀ j ∈ GLAPLayer 3 (K ⊓ N), b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N) :
    b ∈ centralizerQuot B K := by
  refine Subgroup.subset_closure ⟨hb, fun k hk => ?_⟩
  set J := GLAPLayer 3 (K ⊓ N) with hJ
  set O := GLAPPrimeCoreOf 3 K with hO
  have hk' : k ∈ ((O ⊔ J : Subgroup G) : Set G) := by
    rw [sup_comm]; exact h.le_layer_sup hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left O J (layer_le_normalizerO K N)] at hk'
  obtain ⟨o, ho, j, hj, hkoj⟩ := hk'
  have hkoj : o * j = k := hkoj
  subst hkoj
  have hbO : b * o * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (h.bNormalizesO hb) o).1 ho
  have hbJ : b * j * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (h.bNormalizesLayer hb) j).1 hj
  have hc : b * j * b⁻¹ * j⁻¹ ∈ O :=
    h.layer_inf_le ⟨J.mul_mem hbJ (J.inv_mem hj), hcomm j hj⟩
  have e : b * (o * j) * b⁻¹ * (o * j)⁻¹ = (b * o * b⁻¹) * (b * j * b⁻¹ * j⁻¹) * o⁻¹ := by group
  rw [e]
  exact O.mul_mem (O.mul_mem hbO hc) (O.inv_mem ho)

theorem comm_of_mem_centralizerQuot {b : G} (hb : b ∈ centralizerQuot B K) :
    b ∈ B ∧ ∀ j ∈ GLAPLayer 3 (K ⊓ N), b * j * b⁻¹ * j⁻¹ ∈ GLAPPrimeCoreOf 3 N := by
  set J := GLAPLayer 3 (K ⊓ N) with hJ
  set O := GLAPPrimeCoreOf 3 K with hO
  set S : Set G := {b | b ∈ B ∧ ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ O} with hS
  have hJK : J ≤ K := (glaPLayer_le 3 _).trans inf_le_left
  have hJN : J ≤ N := (glaPLayer_le 3 _).trans inf_le_right
  have hSB : Subgroup.closure S ≤ B := (Subgroup.closure_le B).2 fun b hb => hb.1
  let T : Subgroup G := ((Subgroup.centralizer (barX 3 N J : Set (↥N ⧸ GLAPPrimeCore 3 ↥N))).comap
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))).map N.subtype
  have hST : Subgroup.closure S ≤ T := by
    refine (Subgroup.closure_le T).2 fun b hbS => ?_
    have hbB : b ∈ B := hbS.1
    refine ⟨⟨b, h.bN hbB⟩, ?_, rfl⟩
    set c : ↥N ⧸ GLAPPrimeCore 3 ↥N := QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨b, h.bN hbB⟩ with hc
    have hJP : J ≤ Subgroup.normalizer ((J ⊓ O : Subgroup G) : Set G) := fun x hx =>
      inf_normalizer_le_normalizer_inf J O ⟨le_normalizer_glaPLayer 3 _ ((glaPLayer_le 3 _) hx),
        layer_le_normalizerO K N hx⟩
    have hcomm : ∀ z ∈ barX 3 N J, c * z * c⁻¹ * z⁻¹ ∈ barX 3 N (J ⊓ O) := by
      rintro _ ⟨z, hz, rfl⟩
      have hzJ : (z : G) ∈ J := (Subgroup.mem_subgroupOf).1 hz
      have hzK : (z : G) ∈ K := hJK hzJ
      have hbJ : b * z * b⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 (h.bNormalizesLayer hbB) z).1 hzJ
      have hcz : b * (z : G) * b⁻¹ * (z : G)⁻¹ ∈ J ⊓ O :=
        ⟨J.mul_mem hbJ (J.inv_mem hzJ), hbS.2 z hzK⟩
      refine ⟨⟨b, h.bN hbB⟩ * z * ⟨b, h.bN hbB⟩⁻¹ * z⁻¹, (Subgroup.mem_subgroupOf).2 hcz, ?_⟩
      simp [hc]
    have hne : ¬ barX 3 N J ≤ barX 3 N (J ⊓ O) := by
      intro hle
      have hJO : J ≤ O := by
        intro j hj
        obtain ⟨p, hp, hpj⟩ := exists_of_barX_le hle hj (hJN hj)
        have hpjJ : p⁻¹ * j ∈ J ⊓ GLAPPrimeCoreOf 3 N := ⟨J.mul_mem (J.inv_mem hp.1) hj, hpj⟩
        have := O.mul_mem hp.2 (h.layer_inf_le hpjJ)
        simpa using this
      exact h.not_le_glaPPrimeCoreOf ((h.le_layer_sup).trans (sup_le hJO le_rfl))
    have hbn : (barX 3 N J) ≤ Subgroup.normalizer ((barX 3 N (J ⊓ O) : Subgroup _) :
        Set (↥N ⧸ GLAPPrimeCore 3 ↥N)) := barX_le_normalizer hJP
    have hcen := centralizes_of_commutator_le_proper (J := barX 3 N J) (P := barX 3 N (J ⊓ O))
      (c := c) h.comp.2.2 (barX_mono 3 inf_le_left) hbn hne hcomm
    refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
    exact (hcen z hz).symm
  refine ⟨hSB hb, fun j hj => ?_⟩
  obtain ⟨b', hb', hbb⟩ := hST hb
  have hjN : j ∈ N := hJN hj
  have h1 := Subgroup.mem_centralizer_iff.1 hb' (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) ⟨j, hjN⟩)
    ⟨⟨j, hjN⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩
  have h2 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥N) (b' * ⟨j, hjN⟩ * b'⁻¹ * ⟨j, hjN⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  have h3 := (QuotientGroup.eq_one_iff _).1 h2
  refine ⟨_, h3, ?_⟩
  simp [← hbb]

end LayerSetup

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7
