module

public import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.PrimeCentralizerSpecialFixedLine
import CFSG.FeitThompson.Local.CentralRankThreeConstrainedTransitivity
import CFSG.FeitThompson.Local.CyclicCommonFixedFrobeniusKernelDerived
import CFSG.FeitThompson.Local.FrattiniQuotientPPowerElementaryAbelian
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
import CFSG.FeitThompson.Local.PrimeSubgroupFixesFittingLine
import CFSG.FeitThompson.Local.FittingModuleFaithfulAction
import CFSG.FeitThompson.OddOrder.SemidirectReassociation

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise Subgroup
open scoped commutatorElement

universe u

section Aux

variable {G : Type u} [Group G]

theorem mem_conj_pointwise_smul_iff {g y : G} {D : Subgroup G} :
    y ∈ (MulAut.conj g • D : Subgroup G) ↔ g⁻¹ * y * g ∈ D := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.conj]

theorem coe_conj_inv_pointwise_smul (x : G) (D : Subgroup G) :
    ((MulAut.conj x⁻¹ • D : Subgroup G) : Set G) = (fun d => x⁻¹ * d * x) '' (D : Set G) := by
  ext y
  simp only [SetLike.mem_coe, mem_conj_pointwise_smul_iff, Set.mem_image]
  refine ⟨fun h => ⟨x * y * x⁻¹, by simpa [mul_assoc] using h, by group⟩, ?_⟩
  rintro ⟨d, hd, rfl⟩
  simpa [mul_assoc] using hd

theorem mem_normalizer_of_conj_pointwise_smul_eq {g : G} {D : Subgroup G}
    (h : (MulAut.conj g • D : Subgroup G) = D) : g ∈ normalizer (D : Set G) := by
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  have h2 : g * y * g⁻¹ ∈ (MulAut.conj g • D : Subgroup G) ↔ y ∈ D := by
    rw [mem_conj_pointwise_smul_iff]
    exact iff_of_eq (congrArg _ (by group))
  rw [h] at h2
  exact h2.symm

theorem conj_pointwise_smul_le {g : G} {D E : Subgroup G} (hg : g ∈ normalizer (E : Set G))
    (hDE : D ≤ E) : (MulAut.conj g • D : Subgroup G) ≤ E := by
  intro y hy
  have h2 := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * y * g)).1
    (hDE (mem_conj_pointwise_smul_iff.1 hy))
  simpa [mul_assoc] using h2

theorem natCard_conj_pointwise_smul (g : G) (D : Subgroup G) [Finite ↥D] :
    Nat.card ↥(MulAut.conj g • D : Subgroup G) = Nat.card ↥D := by
  rw [Subgroup.pointwise_smul_def]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem index_conj_pointwise_smul [Finite G] (g : G) (D : Subgroup G) :
    (MulAut.conj g • D : Subgroup G).index = D.index := by
  have h1 := Subgroup.card_mul_index (MulAut.conj g • D : Subgroup G)
  have h2 := Subgroup.card_mul_index D
  rw [natCard_conj_pointwise_smul] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem isMulCommutative_conj_pointwise_smul (g : G) (D : Subgroup G)
    [hD : IsMulCommutative ↥D] : IsMulCommutative ↥(MulAut.conj g • D : Subgroup G) := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  set u : G := g⁻¹ * (a : G) * g with hu
  set v : G := g⁻¹ * (b : G) * g with hv
  have hcomm : u * v = v * u := congrArg Subtype.val
    (hD.is_comm.comm ⟨u, mem_conj_pointwise_smul_iff.1 a.2⟩
      ⟨v, mem_conj_pointwise_smul_iff.1 b.2⟩)
  have ha : (a : G) = g * u * g⁻¹ := by rw [hu]; group
  have hb : (b : G) = g * v * g⁻¹ := by rw [hv]; group
  push_cast [ha, hb]
  calc g * u * g⁻¹ * (g * v * g⁻¹) = g * (u * v) * g⁻¹ := by group
    _ = g * (v * u) * g⁻¹ := by rw [hcomm]
    _ = g * v * g⁻¹ * (g * u * g⁻¹) := by group

theorem isMulCommutative_of_commutator_eq_bot {D : Subgroup G} (h : ⁅D, D⁆ = (⊥ : Subgroup G)) :
    IsMulCommutative ↥D :=
  ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h a.2) b b.2).symm⟩⟩

theorem le_centralizer_of_isMulCommutative {D : Subgroup G} [hD : IsMulCommutative ↥D] :
    D ≤ centralizer (D : Set G) := fun a ha =>
  Subgroup.mem_centralizer_iff.2 fun b hb =>
    congrArg Subtype.val (hD.is_comm.comm (⟨b, hb⟩ : ↥D) ⟨a, ha⟩)

theorem mem_centralizer_sup {A B : Subgroup G} {z : G} (hA : z ∈ centralizer (A : Set G))
    (hB : z ∈ centralizer (B : Set G)) : z ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [show A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) by rw [Subgroup.closure_union]; simp,
    Subgroup.centralizer_closure]
  refine Subgroup.mem_centralizer_iff.2 ?_
  rintro y (hy | hy)
  · exact Subgroup.mem_centralizer_iff.1 hA y hy
  · exact Subgroup.mem_centralizer_iff.1 hB y hy

theorem derived_le_self (D : Subgroup G) : ⁅D, D⁆ ≤ D :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem eq_bot_of_subgroupOf_eq_bot {A B : Subgroup G} (hAB : A ≤ B)
    (h : A.subgroupOf B = ⊥) : A = ⊥ := by
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at h
  exact le_bot_iff.1 ((le_inf le_rfl hAB).trans h.le)

theorem zpowers_eq_of_prime_natCard {R : Subgroup G} (hR : (Nat.card ↥R).Prime)
    {k : G} (hk : k ∈ R) (hk1 : k ≠ 1) : Subgroup.zpowers k = R := by
  have : Finite ↥R := Nat.finite_of_card_ne_zero hR.pos.ne'
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hk) ?_
  have hdvd : orderOf k ∣ Nat.card ↥R := by
    rw [← Nat.card_zpowers k]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hk)
  rcases (Nat.dvd_prime hR).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hk1
  · rw [Nat.card_zpowers, h]

theorem centralizer_eq_centralizer_singleton_of_prime_natCard {R : Subgroup G}
    (hR : (Nat.card ↥R).Prime) {k : G} (hk : k ∈ R) (hk1 : k ≠ 1) :
    Subgroup.centralizer (R : Set G) = Subgroup.centralizer {k} := by
  rw [← zpowers_eq_of_prime_natCard hR hk hk1, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]

theorem le_normalizer_conj_pointwise_smul {g : G} {D E : Subgroup G}
    (hg : g ∈ normalizer (E : Set G)) (hED : E ≤ normalizer (D : Set G)) :
    E ≤ normalizer ((MulAut.conj g • D : Subgroup G) : Set G) := by
  intro e he
  refine Subgroup.mem_normalizer_iff.2 fun y => ?_
  have hconj : g⁻¹ * e * g ∈ E := by
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) e).1 he
    simpa [mul_assoc] using h
  rw [mem_conj_pointwise_smul_iff, mem_conj_pointwise_smul_iff,
    show g⁻¹ * (e * y * e⁻¹) * g = (g⁻¹ * e * g) * (g⁻¹ * y * g) * (g⁻¹ * e * g)⁻¹ by group]
  exact Subgroup.mem_normalizer_iff.1 (hED hconj) (g⁻¹ * y * g)

theorem map_subtype_top' (K : Subgroup G) : (⊤ : Subgroup ↥K).map K.subtype = K := by
  rw [← Subgroup.top_subgroupOf (H := K), Subgroup.subgroupOf_map_subtype, top_inf_eq]

theorem eq_of_subgroupOf_eq_of_le {A B K : Subgroup G} (hA : A ≤ K) (hB : B ≤ K)
    (h : A.subgroupOf K = B.subgroupOf K) : A = B := by
  have h2 := congrArg (Subgroup.map K.subtype) h
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hA,
    inf_eq_left.2 hB] at h2

theorem map_subtype_fixedPoints_conjOnNormalized_subgroupOf {V E B : Subgroup G}
    (hEN : E ≤ normalizer (V : Set G)) (hBE : B ≤ E) :
    (FixedPoints.subgroup
        ↥(((conjOnNormalized V hEN).comp (B.subgroupOf E).subtype).range) ↥V).map V.subtype
      = V ⊓ centralizer (B : Set G) := by
  rw [map_subtype_fixedPoints_conjOnNormalized hEN (B.subgroupOf E),
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hBE]

theorem index_subgroupOf_eq_of_natCard_eq [Finite G] {A B K : Subgroup G} (hA : A ≤ K)
    (hB : B ≤ K) (h : Nat.card ↥A = Nat.card ↥B) :
    (A.subgroupOf K).index = (B.subgroupOf K).index := by
  have h1 := Subgroup.card_mul_index (A.subgroupOf K)
  have h2 := Subgroup.card_mul_index (B.subgroupOf K)
  rw [natCard_subgroupOf_of_le hA, h] at h1
  rw [natCard_subgroupOf_of_le hB] at h2
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem sup_eq_top_of_ne_of_index_eq_prime {q : ℕ} (hq : q.Prime) {D E : Subgroup G}
    (hD : D.index = q) (hE : E.index = q) (hne : D ≠ E) : D ⊔ E = ⊤ := by
  have hcD := isCoatom_of_index_eq_prime hq hD
  have hcE := isCoatom_of_index_eq_prime hq hE
  rcases eq_or_lt_of_le (le_sup_left : D ≤ D ⊔ E) with h | h
  · exfalso
    rcases eq_or_lt_of_le (h ▸ le_sup_right : E ≤ D) with h2 | h2
    · exact hne h2.symm
    · exact hcD.1 (hcE.2 _ h2)
  · exact hcD.2 _ h

theorem index_inf_eq_of_sup_eq_top_of_index_eq [Finite G] {q : ℕ} {D E : Subgroup G}
    (hD : D.index = q) (hE : E.index = q) (hcard : Nat.card ↥(D ⊓ E) * Nat.card G
      = Nat.card ↥D * Nat.card ↥E) : (D ⊓ E).index = q ^ 2 := by
  have h1 := Subgroup.card_mul_index (D ⊓ E)
  have h2 := Subgroup.card_mul_index D
  have h3 := Subgroup.card_mul_index E
  rw [hD] at h2
  rw [hE] at h3
  have key : Nat.card ↥(D ⊓ E) * (q * q) * Nat.card G = Nat.card G * Nat.card G :=
    calc Nat.card ↥(D ⊓ E) * (q * q) * Nat.card G
        = (Nat.card ↥(D ⊓ E) * Nat.card G) * (q * q) := by ring
      _ = (Nat.card ↥D * Nat.card ↥E) * (q * q) := by rw [hcard]
      _ = (Nat.card ↥D * q) * (Nat.card ↥E * q) := by ring
      _ = Nat.card G * Nat.card G := by rw [h2, h3]
  have key2 : Nat.card ↥(D ⊓ E) * (q * q) = Nat.card G :=
    Nat.eq_of_mul_eq_mul_right Nat.card_pos key
  refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥(D ⊓ E))) ?_
  rw [h1, ← key2, sq]

end Aux

variable {G : Type u} [Group G] [Finite G]

namespace IsReducedPrimeCentralizerKernel

variable {p q : ℕ} {H R R0 V K U N P : Subgroup G}
  (hc : IsReducedPrimeCentralizerKernel p q H R R0 V K U N P)

include hc

theorem commutator_K_R_ne_bot : (⁅K, R⁆ : Subgroup G) ≠ ⊥ := by
  rw [hc.R_eq]; exact hc.isPrimeCentralizerKernelSetup.commutator_R0_ne_bot

theorem R_le_normalizer_commutator : R ≤ normalizer ((⁅K, R⁆ : Subgroup G) : Set G) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    mem_normalizer_iff_map_conj_eq.1 (hc.R_le_normalizer_K hr),
    mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hr)]

theorem inf_commutator_inf_centralizer_R_eq_bot :
    (⁅K, R⁆ : Subgroup G) ⊓ (K ⊓ centralizer (R : Set G)) = ⊥ := by
  have h := congrArg (Subgroup.map K.subtype) hc.inf_commutator_centralizer_R_eq_bot
  rw [Subgroup.map_inf _ _ _ K.subtype_injective, hc.map_subtype_actionCentralizer_R,
    hc.map_subtype_actionCommutator_R, Subgroup.map_bot, inf_comm] at h
  exact h

theorem prime_natCard_R : (Nat.card ↥R).Prime := by
  rw [hc.R_eq]; exact hc.admissible.prime_card

theorem R_ne_bot : R ≠ ⊥ := by
  intro h
  have hr := hc.prime_natCard_R
  rw [h, Subgroup.card_bot] at hr
  exact hr.one_lt.ne rfl

theorem disjoint_commutator_R : Disjoint (⁅K, R⁆ : Subgroup G) R :=
  disjoint_iff.2 (le_bot_iff.1
    ((inf_le_inf_right R (hc.commutator_K_R_le.trans hc.K_le_H)).trans
      hc.admissible.inf_eq_bot.le))

theorem not_dvd_natCard_sup_commutator_R : ¬ p ∣ Nat.card ↥((⁅K, R⁆ : Subgroup G) ⊔ R) := by
  intro hdvd
  refine hc.isPrimeCentralizerKernelSetup.not_dvd_natCard_sup_K_R0 (hdvd.trans ?_)
  refine Subgroup.card_dvd_of_le (sup_le (hc.commutator_K_R_le.trans le_sup_left) ?_)
  rw [hc.R_eq]; exact le_sup_right

theorem sup_commutator_R_le_normalizer_V :
    (⁅K, R⁆ : Subgroup G) ⊔ R ≤ normalizer (V : Set G) :=
  have := hc.isPrimeCentralizerKernelSetup.normal_V
  fun _ _ => le_normalizer_of_normal (by trivial)

theorem coprime_natCard_R_K : (Nat.card ↥R).Coprime (Nat.card ↥K) := by
  have h := hc.coprime_natCard_R_subgroupOf_K
  rwa [natCard_subgroupOf_of_le (le_sup_right : R ≤ P ⊔ R)] at h

theorem commutator_commutator_K_R_eq_bot :
    (⁅(⁅K, R⁆ : Subgroup G), (⁅K, R⁆ : Subgroup G)⁆ : Subgroup G) = ⊥ := by
  set D : Subgroup G := ⁅K, R⁆ with hDdef
  have hRD : R ≤ normalizer (D : Set G) := hc.R_le_normalizer_commutator
  have hVN : D ⊔ R ≤ normalizer (V : Set G) := hc.sup_commutator_R_le_normalizer_V
  set ρ : ↥(D ⊔ R) →* MulAut ↥V := conjOnNormalized V hVN with hρ
  have hDA : D ≤ D ⊔ R := le_sup_left
  have hRA : R ≤ D ⊔ R := le_sup_right
  set D' : Subgroup ↥(D ⊔ R) := D.subgroupOf (D ⊔ R) with hD'
  set R' : Subgroup ↥(D ⊔ R) := R.subgroupOf (D ⊔ R) with hR'
  have hD'n : D'.Normal := normal_subgroupOf_sup hRD
  have hcompl : D'.IsComplement' R' := isComplement'_subgroupOf_sup hRD hc.disjoint_commutator_R
  have hD1 : D' ≠ ⊥ := fun h => hc.commutator_K_R_ne_bot (eq_bot_of_subgroupOf_eq_bot hDA h)
  have hR1 : R' ≠ ⊥ := fun h => hc.R_ne_bot (eq_bot_of_subgroupOf_eq_bot hRA h)
  have hRprime : (Nat.card ↥R').Prime := by
    rw [hR', natCard_subgroupOf_of_le hRA]; exact hc.prime_natCard_R
  have _isolvG : Group.IsSolvable G := hc.admissible.isSolvable
  have _isolvD' : Group.IsSolvable ↥D' := isSolvable_of_le (le_top : D' ≤ ⊤)
  have hfrob : ∀ k ∈ R', k ≠ 1 → D' ⊓ Subgroup.centralizer {k} = ⊥ := by
    intro k hk hk1
    refine le_bot_iff.1 fun z hz => ?_
    have hzD : (z : G) ∈ D := Subgroup.mem_subgroupOf.1 hz.1
    have hkR : (k : G) ∈ R := Subgroup.mem_subgroupOf.1 hk
    have hk1' : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hcomm : (k : G) * (z : G) = (z : G) * (k : G) :=
      congrArg (fun w : ↥(D ⊔ R) => (w : G)) (Subgroup.mem_centralizer_iff.1 hz.2 k rfl)
    have hzC : (z : G) ∈ Subgroup.centralizer (R : Set G) := by
      rw [centralizer_eq_centralizer_singleton_of_prime_natCard hc.prime_natCard_R hkR hk1']
      exact Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hcomm
    have hmem : (z : G) ∈ D ⊓ (K ⊓ Subgroup.centralizer (R : Set G)) :=
      ⟨hzD, hc.commutator_K_R_le hzD, hzC⟩
    rw [hc.inf_commutator_inf_centralizer_R_eq_bot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact Subtype.ext hmem
  obtain ⟨d, -, -, ⟨e⟩⟩ := hc.isPrimeCentralizerKernelSetup.exists_mulEquiv_V
  have hCK : Nat.card ↥(FixedPoints.subgroup ↥((ρ.comp R'.subtype).range) ↥V) = p := by
    rw [← Subgroup.card_map_of_injective (f := V.subtype) V.subtype_injective, hρ, hR',
      map_subtype_fixedPoints_conjOnNormalized_subgroupOf hVN hRA, hc.R_eq]
    exact hc.isPrimeCentralizerKernelSetup.natCard_inf_V_centralizer_R0
  have hker : ⁅D', D'⁆ ≤ ρ.ker := fun x hx =>
    eq_one_of_mem_commutator_of_natCard_fixedPoints_eq_prime hc.prime_p e hD'n hcompl hD1 hR1
      hfrob hRprime hc.not_dvd_natCard_sup_commutator_R ρ hCK hx
  rw [hρ, ker_conjOnNormalized] at hker
  have himg := Subgroup.map_mono (f := (D ⊔ R).subtype) hker
  rw [Subgroup.map_commutator, hD', Subgroup.map_subgroupOf_eq_of_le hDA,
    Subgroup.subgroupOf_map_subtype] at himg
  refine le_bot_iff.1 (le_trans (le_inf ?_ (himg.trans inf_le_left))
    hc.isPrimeCentralizerKernelSetup.inf_K_centralizer_V.le)
  exact (derived_le_self D).trans hc.commutator_K_R_le

theorem isMulCommutative_commutator_K_R : IsMulCommutative ↥(⁅K, R⁆ : Subgroup G) :=
  isMulCommutative_of_commutator_eq_bot hc.commutator_commutator_K_R_eq_bot

theorem normal_commutator_K_R_subgroupOf_K :
    ((⁅K, R⁆ : Subgroup G).subgroupOf K).Normal := by
  have he : (⁅K, R⁆ : Subgroup G).subgroupOf K
      = actionCommutator hc.action (R.subgroupOf (P ⊔ R)) := by
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, hc.map_subtype_actionCommutator_R,
      inf_eq_left.2 hc.commutator_K_R_le]
  rw [he]
  exact hc.normal_actionCommutator_R

theorem index_commutator_K_R_subgroupOf_K :
    ((⁅K, R⁆ : Subgroup G).subgroupOf K).index = q := hc.index_commutator_K_R

theorem K_le_normalizer_commutator : K ≤ normalizer ((⁅K, R⁆ : Subgroup G) : Set G) :=
  le_normalizer_of_normal_subgroupOf hc.commutator_K_R_le hc.normal_commutator_K_R_subgroupOf_K

theorem commutator_ne_K : (⁅K, R⁆ : Subgroup G) ≠ K := by
  intro h
  have hidx := hc.index_commutator_K_R
  rw [h, Subgroup.subgroupOf_self, Subgroup.index_top] at hidx
  exact hc.prime_q.one_lt.ne hidx

theorem exists_conj_ne :
    ∃ x ∈ P, (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≠ ⁅K, R⁆ := by
  set D : Subgroup G := ⁅K, R⁆ with hDdef
  by_contra hcon
  simp only [not_exists, not_and, ne_eq, not_not] at hcon
  have hPD : P ≤ normalizer (D : Set G) := fun x hx => by
    have h := mem_normalizer_of_conj_pointwise_smul_eq (hcon x hx)
    simpa using Subgroup.inv_mem _ h
  have hPC : P ≤ centralizer (D : Set G) :=
    hc.centralizes_of_lt D hc.commutator_K_R_le hc.commutator_ne_K hPD
      hc.R_le_normalizer_commutator
  have hDPhi : ∀ x : ↥K, (x : G) ∈ D → x ∈ frattini ↥K := by
    intro x hxD
    refine hc.mem_frattini_of_forall_conj_mk_eq x fun dd hdd => ?_
    have hdP : (dd : G) ∈ P := Subgroup.mem_subgroupOf.1 hdd
    have hfix : hc.action dd x = x := by
      refine Subtype.ext ?_
      rw [hc.coe_action_apply]
      have hcomm := Subgroup.mem_centralizer_iff.1 (hPC hdP) (x : G) hxD
      calc (dd : G) * (x : G) * (dd : G)⁻¹ = (x : G) * (dd : G) * (dd : G)⁻¹ := by rw [← hcomm]
        _ = (x : G) := by group
    rw [hfix]
  set φ : ↥R →* MulAut ↥K := conjOnNormalized K hc.R_le_normalizer_K with hφ
  have hmemker : ∀ r : ↥R, φ r ∈ autKerFrattini ↥K := by
    intro r
    refine mem_autKerFrattini_iff_inv_mul_mem.2 fun x => hDPhi _ ?_
    have hval : (((φ r x)⁻¹ * x : ↥K) : G) = ⁅(r : G), (x : G)⁻¹⁆ := by
      rw [Subgroup.coe_mul, InvMemClass.coe_inv, hφ, conjOnNormalized_apply_coe,
        commutatorElement_def]
      group
    rw [hval, hDdef, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator r.2 (K.inv_mem x.2)
  have _isolvK : Group.IsSolvable ↥K := hc.isSolvable_K
  have hone : ∀ r : ↥R, φ r = 1 := fun r =>
    eq_one_of_mem_autKerFrattini_of_coprime (hmemker r)
      (Nat.Coprime.coprime_dvd_left ((orderOf_map_dvd φ r).trans (_root_.orderOf_dvd_natCard r))
        hc.coprime_natCard_R_K)
  refine hc.isPrimeCentralizerKernelSetup.not_le_centralizer_K ?_
  rw [← hc.R_eq]
  intro r hr
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨y, hy⟩ : ↥K) : G)) (hone ⟨r, hr⟩)
  simp only [hφ, conjOnNormalized_apply_coe] at h2
  have h3 : r * y * r⁻¹ = y := by simpa using h2
  calc y * r = (r * y * r⁻¹) * r := by rw [h3]
    _ = r * y := by group

variable {x : G}

theorem conj_le_K (hx : x ∈ P) :
    (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≤ K :=
  conj_pointwise_smul_le (Subgroup.inv_mem _ (hc.P_le_normalizer_K hx)) hc.commutator_K_R_le

theorem isMulCommutative_conj :
    IsMulCommutative ↥(MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) :=
  haveI := hc.isMulCommutative_commutator_K_R
  isMulCommutative_conj_pointwise_smul _ _

theorem normal_conj_subgroupOf_K (hx : x ∈ P) :
    ((MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G).subgroupOf K).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (le_normalizer_conj_pointwise_smul (Subgroup.inv_mem _ (hc.P_le_normalizer_K hx))
      hc.K_le_normalizer_commutator)

theorem index_conj_subgroupOf_K (hx : x ∈ P) :
    ((MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G).subgroupOf K).index = q := by
  rw [index_subgroupOf_eq_of_natCard_eq (hc.conj_le_K hx) hc.commutator_K_R_le
    (natCard_conj_pointwise_smul _ _)]
  exact hc.index_commutator_K_R_subgroupOf_K

theorem sup_conj_eq_K (hx : x ∈ P)
    (hne : (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≠ ⁅K, R⁆) :
    (⁅K, R⁆ : Subgroup G) ⊔ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) = K := by
  set D : Subgroup G := ⁅K, R⁆ with hDdef
  set E : Subgroup G := MulAut.conj x⁻¹ • D with hEdef
  have hDK : D ≤ K := hc.commutator_K_R_le
  have hEK : E ≤ K := hc.conj_le_K hx
  have hsup : D.subgroupOf K ⊔ E.subgroupOf K = ⊤ :=
    sup_eq_top_of_ne_of_index_eq_prime hc.prime_q hc.index_commutator_K_R_subgroupOf_K
      (hc.index_conj_subgroupOf_K hx)
      (fun h => hne (eq_of_subgroupOf_eq_of_le hEK hDK h.symm))
  have h := congrArg (Subgroup.map K.subtype) hsup
  rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hEK, inf_eq_left.2 hDK, map_subtype_top'] at h

theorem inf_conj_le_center (hx : x ∈ P)
    (hne : (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≠ ⁅K, R⁆) :
    (⁅K, R⁆ : Subgroup G) ⊓ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G)
      ≤ K ⊓ centralizer (K : Set G) := by
  set D : Subgroup G := ⁅K, R⁆ with hDdef
  have := hc.isMulCommutative_commutator_K_R
  have : IsMulCommutative ↥(MulAut.conj x⁻¹ • D : Subgroup G) := hc.isMulCommutative_conj
  intro z hz
  refine ⟨hc.commutator_K_R_le hz.1, ?_⟩
  rw [← hc.sup_conj_eq_K hx hne]
  exact mem_centralizer_sup (le_centralizer_of_isMulCommutative hz.1)
    (le_centralizer_of_isMulCommutative hz.2)

theorem index_inf_conj (hx : x ∈ P)
    (hne : (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≠ ⁅K, R⁆) :
    (((⁅K, R⁆ : Subgroup G) ⊓ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G)
      : Subgroup G).subgroupOf K).index = q ^ 2 := by
  set D : Subgroup G := ⁅K, R⁆ with hDdef
  set E : Subgroup G := MulAut.conj x⁻¹ • D with hEdef
  have hDK : D ≤ K := hc.commutator_K_R_le
  have hEK : E ≤ K := hc.conj_le_K hx
  have hEn : (E.subgroupOf K).Normal := hc.normal_conj_subgroupOf_K hx
  have hcount := natCard_sup_mul_natCard_inf_of_le_normalizer
    (S := E.subgroupOf K) (T := D.subgroupOf K) le_normalizer_of_normal
  have hsupK : E.subgroupOf K ⊔ D.subgroupOf K = ⊤ := by
    have h := congrArg (fun S : Subgroup G => S.subgroupOf K) (hc.sup_conj_eq_K hx hne)
    rwa [Subgroup.subgroupOf_sup hDK hEK, Subgroup.subgroupOf_self, sup_comm] at h
  rw [hsupK] at hcount
  simp only [Subgroup.card_top] at hcount
  have hinfeq : (D ⊓ E : Subgroup G).subgroupOf K = D.subgroupOf K ⊓ E.subgroupOf K := rfl
  rw [hinfeq]
  refine index_inf_eq_of_sup_eq_top_of_index_eq hc.index_commutator_K_R_subgroupOf_K
    (hc.index_conj_subgroupOf_K hx) ?_
  rw [inf_comm]
  linarith [hcount]

theorem primeCentralizerAbelianCommutatorConjugates :
    IsMulCommutative ↥(⁅K, R⁆ : Subgroup G) ∧
      ((⁅K, R⁆ : Subgroup G).subgroupOf K).Normal ∧
      ((⁅K, R⁆ : Subgroup G).subgroupOf K).index = q ∧
      ∃ x ∈ P, (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) ≠ ⁅K, R⁆ ∧
        (⁅K, R⁆ : Subgroup G) ⊔ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G) = K ∧
        (⁅K, R⁆ : Subgroup G) ⊓ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G)
          ≤ K ⊓ centralizer (K : Set G) ∧
        (((⁅K, R⁆ : Subgroup G) ⊓ (MulAut.conj x⁻¹ • (⁅K, R⁆ : Subgroup G) : Subgroup G)
          : Subgroup G).subgroupOf K).index = q ^ 2 := by
  obtain ⟨x, hxP, hne⟩ := hc.exists_conj_ne
  exact ⟨hc.isMulCommutative_commutator_K_R, hc.normal_commutator_K_R_subgroupOf_K,
    hc.index_commutator_K_R_subgroupOf_K,
    x, hxP, hne, hc.sup_conj_eq_K hxP hne, hc.inf_conj_le_center hxP hne,
    hc.index_inf_conj hxP hne⟩

end IsReducedPrimeCentralizerKernel

end CFSG.FeitThompson

end
