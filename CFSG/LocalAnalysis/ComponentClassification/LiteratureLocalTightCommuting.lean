module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.LiteratureLocal.TightCommuting

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped Pointwise

variable {G : Type*} [Group G]

theorem rightConjugate_mono {A B : Subgroup G} (g : G) (h : A ≤ B) :
    rightConjugate A g ≤ rightConjugate B g := fun x hx => by
  rw [mem_rightConjugate_iff] at hx ⊢
  exact h hx

theorem rightConjugate_inf (A B : Subgroup G) (g : G) :
    rightConjugate (A ⊓ B) g = rightConjugate A g ⊓ rightConjugate B g := by
  ext x
  simp only [mem_rightConjugate_iff, mem_inf]

theorem rightConjugate_rightConjugate_inv (A : Subgroup G) (g : G) :
    rightConjugate (rightConjugate A g) g⁻¹ = A := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem conj_mem_rightConjugate {A : Subgroup G} {a : G} (ha : a ∈ A) (g : G) :
    g⁻¹ * a * g ∈ rightConjugate A g := by
  rw [mem_rightConjugate_iff]
  simpa [mul_assoc] using ha

theorem rightConjugate_ne_bot {A : Subgroup G} (hA : A ≠ ⊥) (g : G) :
    rightConjugate A g ≠ ⊥ := by
  intro h
  apply hA
  rw [eq_bot_iff]
  intro a ha
  have hmem := conj_mem_rightConjugate ha g
  rw [h, mem_bot] at hmem
  rw [mem_bot]
  calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [hmem]; group

theorem rightConjugate_eq_of_mem {A : Subgroup G} {g : G} (hg : g ∈ A) :
    rightConjugate A g = A :=
  (rightConjugate_eq_self_iff A g).mpr (le_normalizer hg)

@[expose] def Commutes (A B : Subgroup G) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, a * b = b * a

theorem Commutes.symm {A B : Subgroup G} (h : Commutes A B) : Commutes B A :=
  fun b hb a ha => (h a ha b hb).symm

theorem Commutes.le_normalizer {A B : Subgroup G} (h : Commutes A B) :
    A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    rw [h a ha b hb, mul_inv_cancel_right]
    exact hb
  · intro hb
    have hc := h a ha _ hb
    have h2 : a * (a * b * a⁻¹) * a⁻¹ = a * b * a⁻¹ := by rw [hc]; group
    have h3 : a * b * a⁻¹ = b := by
      calc a * b * a⁻¹ = a⁻¹ * (a * (a * b * a⁻¹) * a⁻¹) * a := by group
        _ = a⁻¹ * (a * b * a⁻¹) * a := by rw [h2]
        _ = b := by group
    rwa [h3] at hb

variable [Finite G]

omit [Finite G] in
theorem tightlyEmbedded_rightConjugate {K : Subgroup G} (hK : TightlyEmbedded K) (g : G) :
    TightlyEmbedded (rightConjugate K g) :=
  StandardSubgroupAPI.tightlyEmbedded_rightConjugate hK g

structure Setup (K H Q S : Subgroup G) : Prop where
  tight : TightlyEmbedded K
  le_inf : Q ≤ H ⊓ K
  sylow : ∀ R : Subgroup G, R ≤ H ⊓ K → IsPGroup 2 R → Q ≤ R → R = Q
  pGroup : IsPGroup 2 Q
  ne_bot : Q ≠ ⊥
  S_le : S ≤ H
  S_pGroup : IsPGroup 2 S
  le_S : Q ≤ S

variable {K H Q S : Subgroup G}

omit [Finite G] in
theorem Setup.le_H (hs : Setup K H Q S) : Q ≤ H := hs.le_inf.trans inf_le_left

omit [Finite G] in
theorem Setup.le_K (hs : Setup K H Q S) : Q ≤ K := hs.le_inf.trans inf_le_right

omit [Finite G] in
theorem Setup.conj (hs : Setup K H Q S) {g : G} (hg : g ∈ H) {S' : Subgroup G}
    (hS'H : S' ≤ H) (hS'2 : IsPGroup 2 S') (hQS' : rightConjugate Q g ≤ S') :
    Setup (rightConjugate K g) H (rightConjugate Q g) S' where
  tight := tightlyEmbedded_rightConjugate hs.tight g
  le_inf := _root_.le_inf ((rightConjugate_mono g hs.le_H).trans (rightConjugate_eq_of_mem hg).le)
    (rightConjugate_mono g hs.le_K)
  sylow := by
    intro R hR hR2 hQR
    have hR' : rightConjugate R g⁻¹ ≤ H ⊓ K := by
      have h1 := rightConjugate_mono g⁻¹ hR
      rw [rightConjugate_inf, rightConjugate_rightConjugate_inv,
        rightConjugate_eq_of_mem (inv_mem hg)] at h1
      exact h1
    have hQR' : Q ≤ rightConjugate R g⁻¹ := by
      have h1 := rightConjugate_mono g⁻¹ hQR
      rwa [rightConjugate_rightConjugate_inv] at h1
    have heq := hs.sylow _ hR' (hR2.map _) hQR'
    have := congrArg (fun B => rightConjugate B g) heq
    rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
  pGroup := hs.pGroup.map _
  ne_bot := rightConjugate_ne_bot hs.ne_bot g
  S_le := hS'H
  S_pGroup := hS'2
  le_S := hQS'

omit [Finite G] in
theorem Setup.inf_eq (hs : Setup K H Q S) : S ⊓ K = Q :=
  hs.sylow _ (inf_le_inf_right K hs.S_le) (hs.S_pGroup.to_le inf_le_left)
    (_root_.le_inf hs.le_S hs.le_K)

theorem Setup.inf_conj_eq_bot (hs : Setup K H Q S) {g : G}
    (hne : rightConjugate Q g ≠ Q) (hle : rightConjugate Q g ≤ S) :
    Q ⊓ rightConjugate Q g = ⊥ := by
  by_contra hbot
  have hgN : g ∈ normalizer (K : Set G) := by
    by_contra hgN
    exact hbot (two_subgroup_of_odd_eq_bot _ _ (hs.pGroup.to_le inf_le_left) (hs.tight.2 g hgN)
      (inf_le_inf hs.le_K (rightConjugate_mono g hs.le_K)))
  have hKg : rightConjugate K g = K := (rightConjugate_eq_self_iff K g).mpr hgN
  have hQgK : rightConjugate Q g ≤ K := hKg ▸ rightConjugate_mono g hs.le_K
  have hQgQ : rightConjugate Q g ≤ Q := by
    have h1 : rightConjugate Q g ≤ S ⊓ K := _root_.le_inf hle hQgK
    rwa [hs.inf_eq] at h1
  exact hne (Subgroup.eq_of_le_of_card_ge hQgQ (by rw [rightConjugate_card]))

theorem Setup.mem_normalizer (hs : Setup K H Q S) {X : Subgroup G} (hXQ : X ≤ Q) (hX : X ≠ ⊥)
    {s : G} (hsS : s ∈ S) (hsX : s ∈ normalizer (X : Set G)) :
    s ∈ normalizer (Q : Set G) := by
  have hsK : s ∈ normalizer (K : Set G) :=
    normalizer_two_subgroup_le K X hs.tight (hs.pGroup.to_le hXQ) (hXQ.trans hs.le_K) hX hsX
  rw [← hs.inf_eq, mem_normalizer_iff]
  intro y
  rw [mem_inf, mem_inf, ← mem_normalizer_iff.mp (le_normalizer hsS) y,
    ← mem_normalizer_iff.mp hsK y]

theorem card_mul_le_card_sup {Q R N : Subgroup G} (hinf : Q ⊓ R = ⊥) (hQN : Q ≤ N)
    (hRN : R ≤ N) : Nat.card Q * Nat.card R ≤ Nat.card N := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun p : Q × R => (⟨(p.1 : G) * p.2, mul_mem (hQN p.1.2) (hRN p.2.2)⟩ : N)) ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : (a : G) * b = a' * b' := congrArg Subtype.val h
  have hab : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [h']
      _ = b' * (b : G)⁻¹ := by group
  have hmem : (a' : G)⁻¹ * a ∈ Q ⊓ R :=
    ⟨Q.mul_mem (Q.inv_mem a'.2) a.2, hab ▸ R.mul_mem b'.2 (R.inv_mem b.2)⟩
  rw [hinf, mem_bot] at hmem
  have ha : (a : G) = a' := by
    calc (a : G) = a' * ((a' : G)⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one]
  have hb : (b : G) = b' := by
    rw [ha] at h'
    exact mul_left_cancel h'
  rw [Subtype.ext ha, Subtype.ext hb]

theorem card_sup_le_of_le_normalizer {Q R : Subgroup G} (hRN : R ≤ normalizer (Q : Set G)) :
    Nat.card (Q ⊔ R : Subgroup G) ≤ Nat.card Q * Nat.card R := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : Q × R => (⟨(p.1 : G) * p.2, mul_mem_sup p.1.2 p.2.2⟩ : (Q ⊔ R : Subgroup G))) ?_
  rintro ⟨x, hx⟩
  have hx' : x ∈ ((Q : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q R hRN]
    exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx'
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem exists_mem_normalizer_not_mem {S N : Subgroup G} (hS : IsPGroup 2 S) (hNS : N < S) :
    ∃ s ∈ S, s ∉ N ∧ s ∈ normalizer (N : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := (hS.isNilpotent)
  set N' := N.subgroupOf S
  have hN' : N' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    apply hNS.ne
    apply le_antisymm hNS.le
    intro s hs
    have : (⟨s, hs⟩ : S) ∈ N' := h ▸ mem_top _
    exact this
  obtain ⟨s, hs, hsN⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent N' hN')
  have hsS : (s : G) ∈ S := s.2
  refine ⟨s, hsS, hsN, ?_⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hyS : y ∈ S := hNS.le hy
    have := (mem_normalizer_iff.mp hs ⟨y, hyS⟩).mp hy
    exact this
  · intro hy
    have hyS : y ∈ S := by
      have h1 : (s : G) * y * (s : G)⁻¹ ∈ S := hNS.le hy
      have h2 : y = (s : G)⁻¹ * ((s : G) * y * (s : G)⁻¹) * s := by group
      rw [h2]
      exact mul_mem (mul_mem (inv_mem hsS) h1) hsS
    exact (mem_normalizer_iff.mp hs ⟨y, hyS⟩).mpr hy

theorem Setup.le_normalizer_of_card (hs : Setup K H Q S) (hcard : Nat.card S ≤ Nat.card Q ^ 2) :
    S ≤ normalizer (Q : Set G) := by
  set N := S ⊓ normalizer (Q : Set G) with hN
  have hQN : Q ≤ N := _root_.le_inf hs.le_S le_normalizer
  by_cases hw : ∃ s ∈ S, rightConjugate Q s ≤ N ∧ rightConjugate Q s ≠ Q
  · obtain ⟨s, hsS, hsN, hsne⟩ := hw
    have hinf := hs.inf_conj_eq_bot hsne (hsN.trans inf_le_left)
    have hle := card_mul_le_card_sup hinf hQN hsN
    rw [rightConjugate_card, ← pow_two] at hle
    have hNS : N = S := Subgroup.eq_of_le_of_card_ge inf_le_left (hcard.trans hle)
    rw [← hNS]
    exact inf_le_right
  · push Not at hw
    by_contra hSN
    have hlt : N < S := lt_of_le_of_ne inf_le_left (fun h => hSN (h ▸ inf_le_right))
    obtain ⟨s, hsS, hsN, hsNN⟩ := exists_mem_normalizer_not_mem hs.S_pGroup hlt
    apply hsN
    refine ⟨hsS, ?_⟩
    have hQs : rightConjugate Q s ≤ N := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have h1 : s * x * s⁻¹ ∈ N := hQN hx
      have h2 := (mem_normalizer_iff.mp (inv_mem hsNN) (s * x * s⁻¹)).mp h1
      simpa [mul_assoc] using h2
    have := hw s hsS hQs
    exact (rightConjugate_eq_self_iff Q s).mp this

theorem Setup.commutes_of_le_normalizer (hs : Setup K H Q S) {g : G} (hg : g ∈ H)
    (hne : rightConjugate Q g ≠ Q) (hle : rightConjugate Q g ≤ S)
    (hN : rightConjugate Q g ≤ normalizer (Q : Set G)) :
    Commutes Q (rightConjugate Q g) ∧ Q ⊓ rightConjugate Q g = ⊥ := by
  have hinf := hs.inf_conj_eq_bot hne hle
  set R := rightConjugate Q g with hR
  have hS'2 : IsPGroup 2 (Q ⊔ R : Subgroup G) := by
    rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' (hs.S_pGroup.to_le hle) hs.pGroup hN
  have hS'H : Q ⊔ R ≤ H := sup_le hs.le_H (hle.trans hs.S_le)
  have hsR := hs.conj hg hS'H hS'2 le_sup_right
  have hcard : Nat.card (Q ⊔ R : Subgroup G) ≤ Nat.card R ^ 2 := by
    have h1 := card_sup_le_of_le_normalizer hN
    have h2 : Nat.card Q = Nat.card R := (rightConjugate_card Q g).symm
    rw [h2, ← pow_two] at h1
    exact h1
  have hQN : Q ⊔ R ≤ normalizer (R : Set G) := hsR.le_normalizer_of_card hcard
  refine ⟨fun a ha b hb => ?_, hinf⟩
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ Q := by
    have := (mem_normalizer_iff.mp (hN hb) a⁻¹).mp (inv_mem ha)
    simpa [mul_assoc] using mul_mem ha this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ R := by
    have := (mem_normalizer_iff.mp (hQN (mem_sup_left ha)) b).mp hb
    exact mul_mem this (inv_mem hb)
  have h3 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ Q ⊓ R := ⟨h1, h2⟩
    rw [hinf, mem_bot] at hmem
    exact hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

omit [Finite G] in
theorem frattini_eq_bot_of_sq_eq_one {E : Type*} [Group E] [Finite E]
    (h : ∀ e : E, e ^ 2 = 1) : frattini E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexp : Monoid.exponent E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one h
  have hcomm : ∀ a b : E, a * b = b * a := by
    intro a b
    have h1 := h (a * b)
    have ha : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h a]
    have hb : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h b]
    have hab : (a * b)⁻¹ = a * b := by rw [inv_eq_iff_mul_eq_one, ← pow_two, h1]
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha, hb]
  have hel : IsElementaryAbelian 2 E :=
    { toIsMulCommutative := isMulCommutative_iff.mpr hcomm
      exponent_dvd_p := hexp }
  rw [eq_bot_iff]
  intro e he
  rw [mem_bot]
  by_contra he1
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 E (zpowers e)
  have heo : orderOf e = 2 := orderOf_eq_prime (h e) he1
  have hsup : (zpowers e ⊔ C : Subgroup E) = ⊤ := hC.sup_eq_top
  have hinf : zpowers e ⊓ C = ⊥ := hC.inf_eq_bot
  have hle1 : Nat.card E ≤ Nat.card (zpowers e) * Nat.card C := by
    rw [← Subgroup.card_top (G := E), ← hsup]
    refine card_sup_le_of_le_normalizer ?_
    intro c _
    rw [mem_normalizer_iff]
    intro y
    rw [hcomm c y, mul_inv_cancel_right]
  have hle2 : Nat.card (zpowers e) * Nat.card C ≤ Nat.card E := by
    have := card_mul_le_card_sup hinf (le_top : zpowers e ≤ ⊤) (le_top : C ≤ ⊤)
    rwa [Subgroup.card_top] at this
  have hidx : C.index = 2 := by
    have h2 := C.card_mul_index
    rw [Nat.card_zpowers, heo] at hle1 hle2
    have hpos : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hcoatom := Subgroup.isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_two)
  have heC : e ∈ C := frattini_le_coatom hcoatom he
  have : e ∈ zpowers e ⊓ C := ⟨mem_zpowers e, heC⟩
  rw [hinf, mem_bot] at this
  exact he1 this

theorem exists_orderOf_eq_four {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hΦ : frattini Q ≠ ⊥) :
    ∃ x ∈ Q, orderOf x = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : ∃ q : Q, q ^ 2 ≠ 1 := by
    by_contra h
    push Not at h
    exact hΦ (frattini_eq_bot_of_sq_eq_one h)
  obtain ⟨q, hq⟩ := hq
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) q
  have hk2 : 2 ≤ k := by
    by_contra hk2
    apply hq
    rw [← orderOf_dvd_iff_pow_eq_one, hk]
    exact (Nat.pow_dvd_pow 2 (by omega : k ≤ 1)).trans (by norm_num)
  refine ⟨((q : G) ^ (2 ^ (k - 2))), ?_, ?_⟩
  · exact pow_mem q.2 _
  · have hqG : orderOf (q : G) = 2 ^ k := by rw [Subgroup.orderOf_coe]; exact hk
    have h4 : 2 ^ k = 2 ^ (k - 2) * 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hk2]
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero)
      (by rw [hqG]; exact Nat.pow_dvd_pow 2 (Nat.sub_le k 2)), hqG, h4,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]

@[expose] def conjugatesIn (H Q S : Subgroup G) : Set (Subgroup G) :=
  {R | ∃ h ∈ H, R = rightConjugate Q h ∧ R ≤ S}

omit [Finite G] in
theorem Setup.setup_of_mem (hs : Setup K H Q S) {R : Subgroup G}
    (hR : R ∈ conjugatesIn H Q S) : ∃ h ∈ H, R = rightConjugate Q h ∧
      Setup (rightConjugate K h) H R S := by
  obtain ⟨h, hh, rfl, hRS⟩ := hR
  exact ⟨h, hh, rfl, hs.conj hh hs.S_le hs.S_pGroup hRS⟩

omit [Finite G] in
theorem Setup.conj_mem (hs : Setup K H Q S) {R : Subgroup G} (hR : R ∈ conjugatesIn H Q S)
    {s : G} (hsS : s ∈ S) : rightConjugate R s ∈ conjugatesIn H Q S := by
  obtain ⟨h, hh, rfl, hRS⟩ := hR
  refine ⟨h * s, mul_mem hh (hs.S_le hsS), (rightConjugate_mul Q h s), ?_⟩
  exact (rightConjugate_mono s hRS).trans (rightConjugate_eq_of_mem hsS).le

theorem Setup.inf_eq_bot_of_mem (hs : Setup K H Q S) {R₁ R₂ : Subgroup G}
    (h₁ : R₁ ∈ conjugatesIn H Q S) (h₂ : R₂ ∈ conjugatesIn H Q S) (hne : R₁ ≠ R₂) :
    R₁ ⊓ R₂ = ⊥ := by
  obtain ⟨a, ha, rfl, hs₁⟩ := hs.setup_of_mem h₁
  obtain ⟨b, hb, rfl, hbS⟩ := h₂
  have hR₂ : rightConjugate Q b = rightConjugate (rightConjugate Q a) (a⁻¹ * b) := by
    rw [rightConjugate_mul, show a * (a⁻¹ * b) = b by group]
  rw [hR₂] at hne hbS ⊢
  exact hs₁.inf_conj_eq_bot (Ne.symm hne) hbS

theorem Setup.commutes_of_mem (hs : Setup K H Q S) {R₁ R₂ : Subgroup G}
    (h₁ : R₁ ∈ conjugatesIn H Q S) (h₂ : R₂ ∈ conjugatesIn H Q S) (hne : R₁ ≠ R₂)
    (hN : R₂ ≤ normalizer (R₁ : Set G)) : Commutes R₁ R₂ := by
  obtain ⟨a, ha, rfl, hs₁⟩ := hs.setup_of_mem h₁
  obtain ⟨b, hb, rfl, hbS⟩ := h₂
  have hR₂ : rightConjugate Q b = rightConjugate (rightConjugate Q a) (a⁻¹ * b) := by
    rw [rightConjugate_mul, show a * (a⁻¹ * b) = b by group]
  rw [hR₂] at hne hbS hN ⊢
  exact (hs₁.commutes_of_le_normalizer (mul_mem (inv_mem ha) hb) (Ne.symm hne) hbS hN).1

theorem Setup.mem_normalizer_of_mem (hs : Setup K H Q S) {R : Subgroup G}
    (hR : R ∈ conjugatesIn H Q S) {X : Subgroup G} (hXR : X ≤ R) (hX : X ≠ ⊥) {s : G}
    (hsS : s ∈ S) (hsX : s ∈ normalizer (X : Set G)) : s ∈ normalizer (R : Set G) := by
  obtain ⟨a, ha, rfl, hs₁⟩ := hs.setup_of_mem hR
  exact hs₁.mem_normalizer hXR hX hsS hsX

omit [Finite G] in
theorem le_S_of_mem {R : Subgroup G} (hR : R ∈ conjugatesIn H Q S) : R ≤ S := by
  obtain ⟨h, -, -, hRS⟩ := hR
  exact hRS

omit [Finite G] in
theorem Setup.isPGroup_of_mem (hs : Setup K H Q S) {R : Subgroup G}
    (hR : R ∈ conjugatesIn H Q S) : IsPGroup 2 R :=
  hs.S_pGroup.to_le (le_S_of_mem hR)

omit [Finite G] in
theorem Setup.ne_bot_of_mem (hs : Setup K H Q S) {R : Subgroup G}
    (hR : R ∈ conjugatesIn H Q S) : R ≠ ⊥ := by
  obtain ⟨h, -, rfl, -⟩ := hR
  exact rightConjugate_ne_bot hs.ne_bot h

theorem exists_center_commute {R : Subgroup G} (hR : IsPGroup 2 R) (hR1 : R ≠ ⊥) {y : G}
    (hy : y ∈ normalizer (R : Set G)) (hy2 : IsPGroup 2 (zpowers y)) :
    ∃ z ∈ R, z ≠ 1 ∧ (∀ r ∈ R, z * r = r * z) ∧ z * y = y * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := (center R).map R.subtype with hZ
  have hZR : Z ≤ R := map_subtype_le _
  have hmemZ : ∀ z, z ∈ Z ↔ z ∈ R ∧ ∀ r ∈ R, z * r = r * z := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, fun r hr => ?_⟩
      exact congrArg Subtype.val ((mem_center_iff.mp hw ⟨r, hr⟩).symm)
    · rintro ⟨hz, hzc⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_center_iff]
      intro r
      exact Subtype.ext (hzc r r.2).symm
  have hZne : Z ≠ ⊥ := by
    have : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR1
    have hc := hR.center_nontrivial
    obtain ⟨⟨c, hc⟩, hc1⟩ := exists_ne (1 : center R)
    intro h
    apply hc1
    have : (c : G) ∈ Z := ⟨c, hc, rfl⟩
    rw [h, mem_bot] at this
    exact Subtype.ext (Subtype.ext this)
  have hZ2 : IsPGroup 2 Z := hR.to_le hZR
  have hyZ : zpowers y ≤ normalizer (Z : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro z
    rw [hmemZ, hmemZ]
    constructor
    · rintro ⟨hz, hzc⟩
      refine ⟨(mem_normalizer_iff.mp hy z).mp hz, fun r hr => ?_⟩
      have hr' : y⁻¹ * r * y ∈ R := by
        have := (mem_normalizer_iff.mp (inv_mem hy) r).mp hr
        simpa using this
      have := hzc _ hr'
      calc y * z * y⁻¹ * r = y * (z * (y⁻¹ * r * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * r * y) * z) * y⁻¹ := by rw [this]
        _ = r * (y * z * y⁻¹) := by group
    · rintro ⟨hz, hzc⟩
      have hz' : z ∈ R := (mem_normalizer_iff.mp hy z).mpr hz
      refine ⟨hz', fun r hr => ?_⟩
      have hr' : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.mp hy r).mp hr
      have := hzc _ hr'
      calc z * r = y⁻¹ * ((y * z * y⁻¹) * (y * r * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * r * y⁻¹) * (y * z * y⁻¹)) * y := by rw [this]
        _ = r * z := by group
  set P : Subgroup G := zpowers y ⊔ Z with hP
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_right' hy2 hZ2 hyZ
  have hPN : P ≤ normalizer (Z : Set G) := sup_le hyZ le_normalizer
  have hZP : Z ≤ P := le_sup_right
  have : Group.IsNilpotent P := hP2.isNilpotent
  have hnorm : (Z.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hZP).mpr hPN
  have hne : Z.subgroupOf P ≠ ⊥ := by
    intro h
    apply hZne
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hZP hz⟩ : P) ∈ Z.subgroupOf P := hz
    rw [h, mem_bot] at this
    exact (mem_bot).mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨⟨⟨z, hzP⟩, hzZ, hzC⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hcen)
  refine ⟨z, hZR hzZ, fun h => hz1 (Subtype.ext (Subtype.ext h)), ((hmemZ z).mp hzZ).2, ?_⟩
  have hyP : y ∈ P := mem_sup_left (mem_zpowers y)
  exact congrArg Subtype.val ((mem_center_iff.mp hzC ⟨y, hyP⟩).symm)

omit [Finite G] in
theorem mem_normalizer_zpowers_of_commute {c g : G} (h : c * g = g * c) :
    c ∈ normalizer ((zpowers g : Subgroup G) : Set G) := by
  have hc : c ∈ centralizer ({g} : Set G) := mem_centralizer_singleton_iff.mpr h
  have hle : centralizer ({g} : Set G) ≤ normalizer ((zpowers g : Subgroup G) : Set G) := by
    rw [zpowers_eq_closure, ← centralizer_closure]
    exact centralizer_le_normalizer _
  exact hle hc

omit [Finite G] in
theorem zpowers_ne_bot_of_ne_one {g : G} (hg : g ≠ 1) : zpowers g ≠ ⊥ := by
  intro h
  apply hg
  have : g ∈ zpowers g := mem_zpowers g
  rw [h, mem_bot] at this
  exact this

theorem Setup.commutes_of_permutes (hs : Setup K H Q S) {x : G} (hxQ : x ∈ Q)
    (hx4 : orderOf x = 4) {Γ : Set (Subgroup G)} (hΓ : Γ ⊆ conjugatesIn H Q S)
    (hcomm : ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → Commutes R₁ R₂) {T : Subgroup G}
    (hT : T ∈ conjugatesIn H Q S) (hTΓ : T ∉ Γ)
    (hperm : ∀ t ∈ T, ∀ R ∈ Γ, rightConjugate R t ∈ Γ) :
    ∀ R ∈ Γ, Commutes T R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := ⨆ R : Γ, (R : Subgroup G) with hW
  have hRW : ∀ R ∈ Γ, R ≤ W := fun R hR => le_iSup (fun R : Γ => (R : Subgroup G)) ⟨R, hR⟩
  have hWN : ∀ R ∈ Γ, W ≤ normalizer (R : Set G) := by
    intro R hR
    refine iSup_le fun R' => ?_
    by_cases hR' : (R' : Subgroup G) = R
    · rw [hR']
      exact le_normalizer
    · exact (hcomm R' R'.2 R hR hR').le_normalizer
  have hTW : ∀ t ∈ T, t ∈ normalizer (W : Set G) := by
    intro t ht
    rw [← rightConjugate_eq_self_iff]
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [rightConjugate_card])
    change W.map (MulAut.conj t⁻¹).toMonoidHom ≤ W
    rw [hW, Subgroup.map_iSup]
    exact iSup_le fun R => hRW _ (hperm t ht R R.2)
  have hTS : T ≤ S := le_S_of_mem hT
  have hT2 : IsPGroup 2 T := hs.isPGroup_of_mem hT
  intro R hRΓ
  have hRΔ := hΓ hRΓ
  have hRS : R ≤ S := le_S_of_mem hRΔ
  have hTR : T ≠ R := fun h => hTΓ (h ▸ hRΓ)
  by_contra hTRc
  have hstar : T ⊓ normalizer (R : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyT, hyN⟩
    rw [mem_bot]
    by_contra hy1
    obtain ⟨z, hzR, hz1, hzc, hzy⟩ := exists_center_commute (hs.isPGroup_of_mem hRΔ)
      (hs.ne_bot_of_mem hRΔ) hyN (hT2.to_le ((zpowers_le).mpr hyT))
    have hzW : ∀ w ∈ W, w * z = z * w := by
      have hle : W ≤ centralizer ({z} : Set G) := by
        refine iSup_le fun R' => ?_
        intro w hw
        rw [mem_centralizer_singleton_iff]
        by_cases hR' : (R' : Subgroup G) = R
        · rw [hR'] at hw
          exact (hzc w hw).symm
        · exact hcomm R' R'.2 R hRΓ hR' w hw z hzR
      intro w hw
      exact mem_centralizer_singleton_iff.mp (hle hw)
    have hzNT : z ∈ normalizer (T : Set G) :=
      hs.mem_normalizer_of_mem hT ((zpowers_le).mpr hyT) (zpowers_ne_bot_of_ne_one hy1)
        (hRS hzR) (mem_normalizer_zpowers_of_commute hzy)
    by_cases hcase : ∀ t' ∈ T, z * t' * z⁻¹ * t'⁻¹ = 1
    · have hTN : T ≤ normalizer (R : Set G) := by
        intro t' ht'
        have htz : t' * z = z * t' := by
          have h1 := hcase t' ht'
          calc t' * z = (z * t' * z⁻¹ * t'⁻¹)⁻¹ * (z * t') := by group
            _ = z * t' := by rw [h1, inv_one, one_mul]
        exact hs.mem_normalizer_of_mem hRΔ ((zpowers_le).mpr hzR) (zpowers_ne_bot_of_ne_one hz1)
          (hTS ht') (mem_normalizer_zpowers_of_commute htz)
      exact hTRc (hs.commutes_of_mem hRΔ hT (Ne.symm hTR) hTN).symm
    · push Not at hcase
      obtain ⟨t', ht', hc1⟩ := hcase
      set c := z * t' * z⁻¹ * t'⁻¹ with hc
      have hcT : c ∈ T := by
        have := (mem_normalizer_iff.mp hzNT t').mp ht'
        exact mul_mem this (inv_mem ht')
      have hcW : ∀ w ∈ W, w * c = c * w := by
        intro w hw
        have hw' : t'⁻¹ * w * t' ∈ W := by
          have := (mem_normalizer_iff.mp (inv_mem (hTW t' ht')) w).mp hw
          simpa using this
        have h1 := hzW w hw
        have h2 := hzW _ hw'
        have h3 : w * (t' * z⁻¹ * t'⁻¹) = (t' * z⁻¹ * t'⁻¹) * w := by
          have h2' : (t'⁻¹ * w * t') * z⁻¹ = z⁻¹ * (t'⁻¹ * w * t') := by
            calc (t'⁻¹ * w * t') * z⁻¹ = z⁻¹ * (z * (t'⁻¹ * w * t')) * z⁻¹ := by group
              _ = z⁻¹ * ((t'⁻¹ * w * t') * z) * z⁻¹ := by rw [h2]
              _ = z⁻¹ * (t'⁻¹ * w * t') := by group
          calc w * (t' * z⁻¹ * t'⁻¹) = t' * ((t'⁻¹ * w * t') * z⁻¹) * t'⁻¹ := by group
            _ = t' * (z⁻¹ * (t'⁻¹ * w * t')) * t'⁻¹ := by rw [h2']
            _ = (t' * z⁻¹ * t'⁻¹) * w := by group
        calc w * c = (w * z) * (t' * z⁻¹ * t'⁻¹) := by rw [hc]; group
          _ = (z * w) * (t' * z⁻¹ * t'⁻¹) := by rw [h1]
          _ = z * (w * (t' * z⁻¹ * t'⁻¹)) := by group
          _ = z * ((t' * z⁻¹ * t'⁻¹) * w) := by rw [h3]
          _ = c * w := by rw [hc]; group
      have hRN : R ≤ normalizer (T : Set G) := by
        intro r hr
        exact hs.mem_normalizer_of_mem hT ((zpowers_le).mpr hcT) (zpowers_ne_bot_of_ne_one hc1)
          (hRS hr) (mem_normalizer_zpowers_of_commute (hcW r (hRW R hRΓ hr)))
      exact hTRc (hs.commutes_of_mem hT hRΔ hTR hRN)
  have hTW1 : ∀ w ∈ T, w ∈ W → w = 1 := by
    intro w hwT hwW
    have : w ∈ T ⊓ normalizer (R : Set G) := ⟨hwT, hWN R hRΓ hwW⟩
    rw [hstar, mem_bot] at this
    exact this
  have hWS : W ≤ S := iSup_le fun R' => le_S_of_mem (hΓ R'.2)
  obtain ⟨b, hb, hTb, -⟩ := id hT
  set y := b⁻¹ * x * b with hy
  have hyT : y ∈ T := by
    rw [hTb]
    exact conj_mem_rightConjugate hxQ b
  have hy4 : orderOf y = 4 := by
    have hsc : SemiconjBy b y x := by
      simp only [SemiconjBy, hy]
      group
    rw [SemiconjBy.orderOf_eq b hsc, hx4]
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy4
    norm_num at hy4
  have hnorm : ∀ g ∈ T, g ∈ normalizer (R : Set G) → g = 1 := fun g hg hgN => by
    have : g ∈ T ⊓ normalizer (R : Set G) := ⟨hg, hgN⟩
    rw [hstar, mem_bot] at this
    exact this
  set t := y * y with ht
  have htT : t ∈ T := mul_mem hyT hyT
  have htt : t * t = 1 := by
    calc t * t = y ^ 4 := by rw [ht]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hy4'
  have ht1 : t ≠ 1 := by
    intro h
    have : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hy4] at this
    norm_num at this
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, htt]
  have hy3 : y * y * y = y⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc y * y * y * y = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := hy4'
  have hy3' : y⁻¹ * y⁻¹ * y⁻¹ = y := by
    calc y⁻¹ * y⁻¹ * y⁻¹ = (y * y * y)⁻¹ := by group
      _ = y⁻¹⁻¹ := by rw [hy3]
      _ = y := inv_inv y
  set R1 := rightConjugate R y with hR1
  set R2 := rightConjugate R t with hR2
  have hR1Γ : R1 ∈ Γ := hperm y hyT R hRΓ
  have hR2Γ : R2 ∈ Γ := hperm t htT R hRΓ
  have hR01 : R ≠ R1 :=
    fun h => hy1 (hnorm y hyT ((rightConjugate_eq_self_iff R y).mp h.symm))
  have hR02 : R ≠ R2 :=
    fun h => ht1 (hnorm t htT ((rightConjugate_eq_self_iff R t).mp h.symm))
  have hR12 : R1 ≠ R2 := by
    intro h
    apply hR01
    have h' := congrArg (fun B => rightConjugate B y⁻¹) h
    simp only [hR1, hR2, ht, rightConjugate_mul] at h'
    rw [show y * y⁻¹ = 1 by group, show y * y * y⁻¹ = y by group, rightConjugate_one] at h'
    exact h'
  have h2R : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hs.isPGroup_of_mem hRΔ)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hs.ne_bot_of_mem hRΔ (Subgroup.card_eq_one.mp (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2R
  set u : G := (u' : G) with hu
  have huR : u ∈ R := u'.2
  have huo : orderOf u = 2 := by rw [hu, Subgroup.orderOf_coe]; exact hu'
  have huu : u * u = 1 := by rw [← pow_two, ← huo]; exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    norm_num at huo
  set a1 := y⁻¹ * u * y with ha1
  set a2 := t⁻¹ * u * t with ha2
  have ha1R : a1 ∈ R1 := conj_mem_rightConjugate huR y
  have ha2R : a2 ∈ R2 := conj_mem_rightConjugate huR t
  have c01 : u * a1 = a1 * u := hcomm R hRΓ R1 hR1Γ hR01 u huR a1 ha1R
  have c02 : u * a2 = a2 * u := hcomm R hRΓ R2 hR2Γ hR02 u huR a2 ha2R
  have c12 : a1 * a2 = a2 * a1 := hcomm R1 hR1Γ R2 hR2Γ hR12 a1 ha1R a2 ha2R
  have ha11 : a1 * a1 = 1 := by
    calc a1 * a1 = y⁻¹ * (u * u) * y := by rw [ha1]; group
      _ = 1 := by rw [huu]; group
  have ha22 : a2 * a2 = 1 := by
    calc a2 * a2 = t⁻¹ * (u * u) * t := by rw [ha2]; group
      _ = 1 := by rw [huu]; group
  have ha2' : a2 = t * u * t := by rw [ha2, htinv]
  have hC : ∀ c ∈ W, t * c = c * t → y * c = c * y := by
    intro c hcW hct
    have hcNT : c ∈ normalizer (T : Set G) :=
      hs.mem_normalizer_of_mem hT ((zpowers_le).mpr htT) (zpowers_ne_bot_of_ne_one ht1)
        (hWS hcW) (mem_normalizer_zpowers_of_commute hct.symm)
    have hkT : y * c * y⁻¹ * c⁻¹ ∈ T := by
      have h1 := (mem_normalizer_iff.mp hcNT y⁻¹).mp (inv_mem hyT)
      have h2 := mul_mem hyT h1
      simpa [mul_assoc] using h2
    have hkW : y * c * y⁻¹ * c⁻¹ ∈ W := by
      have h1 := (mem_normalizer_iff.mp (hTW y hyT) c).mp hcW
      exact mul_mem h1 (inv_mem hcW)
    have hk := hTW1 _ hkT hkW
    calc y * c = (y * c * y⁻¹ * c⁻¹) * (c * y) := by group
      _ = c * y := by rw [hk, one_mul]
  have hRW' : u ∈ W := hRW R hRΓ huR
  have ha1W : a1 ∈ W := hRW R1 hR1Γ ha1R
  have ha2W : a2 ∈ W := hRW R2 hR2Γ ha2R
  have hc1t : t * (u * a2) = (u * a2) * t := by
    have c02' : t * u * t * u = u * (t * u * t) := by
      rw [← ha2']
      exact c02.symm
    rw [ha2']
    calc t * (u * (t * u * t)) = (t * u * t * u) * t := by group
      _ = (u * (t * u * t)) * t := by rw [c02']
  have hyc1 := hC _ (mul_mem hRW' ha2W) hc1t
  set a3 := y⁻¹ * a2 * y with ha3
  have h13 : a1 * a3 = u * a2 := by
    calc a1 * a3 = y⁻¹ * (u * a2) * y := by rw [ha1, ha3]; group
      _ = y⁻¹ * ((u * a2) * y) := by group
      _ = y⁻¹ * (y * (u * a2)) := by rw [hyc1]
      _ = u * a2 := by group
  have hta1 : t * a1 * t⁻¹ = a3 := by
    rw [ha3, ha2, ha1, ht]
    calc y * y * (y⁻¹ * u * y) * (y * y)⁻¹ = y * u * y⁻¹ := by group
      _ = (y⁻¹ * y⁻¹ * y⁻¹) * u * (y * y * y) := by rw [hy3, hy3']
      _ = y⁻¹ * ((y * y)⁻¹ * u * (y * y)) * y := by group
  have htu : t * u * t⁻¹ = a2 := by rw [ha2', htinv]
  have ha3' : a3 = a1 * u * a2 := by
    calc a3 = (a1 * a1) * a3 := by rw [ha11, one_mul]
      _ = a1 * (a1 * a3) := by group
      _ = a1 * (u * a2) := by rw [h13]
      _ = a1 * u * a2 := by group
  have h23 : a2 * a3 = u * a1 := by
    rw [ha3']
    calc a2 * (a1 * u * a2) = (a2 * a1) * u * a2 := by group
      _ = (a1 * a2) * u * a2 := by rw [c12]
      _ = a1 * (a2 * u) * a2 := by group
      _ = a1 * (u * a2) * a2 := by rw [c02]
      _ = a1 * u * (a2 * a2) := by group
      _ = u * a1 := by rw [ha22, mul_one, c01]
  have hc2t : t * (u * a1) = (u * a1) * t := by
    have h : t * (u * a1) * t⁻¹ = u * a1 := by
      calc t * (u * a1) * t⁻¹ = (t * u * t⁻¹) * (t * a1 * t⁻¹) := by group
        _ = a2 * a3 := by rw [htu, hta1]
        _ = u * a1 := h23
    calc t * (u * a1) = (t * (u * a1) * t⁻¹) * t := by group
      _ = (u * a1) * t := by rw [h]
  have hyc2 := hC _ (mul_mem hRW' ha1W) hc2t
  have hya1 : y⁻¹ * a1 * y = a2 := by rw [ha1, ha2, ht]; group
  have h12 : a1 * a2 = a1 * u := by
    calc a1 * a2 = (y⁻¹ * u * y) * (y⁻¹ * a1 * y) := by rw [hya1, ha1]
      _ = y⁻¹ * (u * a1) * y := by rw [ha1]; group
      _ = y⁻¹ * ((u * a1) * y) := by group
      _ = y⁻¹ * (y * (u * a1)) := by rw [hyc2]
      _ = u * a1 := by group
      _ = a1 * u := c01
  have ha2u : a2 = u := mul_left_cancel h12
  have hmem : u ∈ R ⊓ R2 := ⟨huR, ha2u ▸ ha2R⟩
  rw [hs.inf_eq_bot_of_mem hRΔ (hΓ hR2Γ) hR02, mem_bot] at hmem
  exact hu1 hmem

omit [Finite G] in
theorem iSup_le_normalizer_of_commutes {Γ : Set (Subgroup G)}
    (hcomm : ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → Commutes R₁ R₂) {R : Subgroup G} (hR : R ∈ Γ) :
    (⨆ R' : Γ, (R' : Subgroup G)) ≤ normalizer (R : Set G) := by
  refine iSup_le fun R' => ?_
  by_cases hR' : (R' : Subgroup G) = R
  · rw [hR']
    exact le_normalizer
  · exact (hcomm R' R'.2 R hR hR').le_normalizer

theorem mem_normalizer_iSup {Γ : Set (Subgroup G)} {g : G}
    (h : ∀ R ∈ Γ, rightConjugate R g ≤ ⨆ R' : Γ, (R' : Subgroup G)) :
    g ∈ normalizer (((⨆ R' : Γ, (R' : Subgroup G)) : Subgroup G) : Set G) := by
  rw [← rightConjugate_eq_self_iff]
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [rightConjugate_card])
  change (⨆ R' : Γ, (R' : Subgroup G)).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [Subgroup.map_iSup]
  exact iSup_le fun R => h R R.2

theorem Setup.commutes_conjugatesIn (hs : Setup K H Q S) (hΦ : frattini Q ≠ ⊥) :
    ∀ R₁ ∈ conjugatesIn H Q S, ∀ R₂ ∈ conjugatesIn H Q S, R₁ ≠ R₂ → Commutes R₁ R₂ := by
  classical
  obtain ⟨x, hxQ, hx4⟩ := exists_orderOf_eq_four hs.pGroup hΦ
  set Δ := conjugatesIn H Q S with hΔ
  have hΔfin : Δ.Finite := Set.toFinite Δ
  let P : Finset (Subgroup G) → Prop := fun Γ =>
    (↑Γ : Set (Subgroup G)) ⊆ Δ ∧ ∀ R₁ ∈ Γ, ∀ R₂ ∈ Γ, R₁ ≠ R₂ → Commutes R₁ R₂
  have hne : ((hΔfin.toFinset.powerset).filter P).Nonempty :=
    ⟨∅, by simp [P]⟩
  obtain ⟨Γ, hΓmem, hΓmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter] at hΓmem
  obtain ⟨-, hΓΔ, hΓc⟩ := hΓmem
  set Γs : Set (Subgroup G) := (Γ : Set (Subgroup G)) with hΓs
  have hΓc' : ∀ R₁ ∈ Γs, ∀ R₂ ∈ Γs, R₁ ≠ R₂ → Commutes R₁ R₂ := hΓc
  have hself : ∀ T ∈ Δ, (∀ t ∈ T, ∀ R ∈ Γs, rightConjugate R t ∈ Γs) → T ∈ Γ := by
    intro T hT hperm
    by_contra hTΓ
    have hcT := hs.commutes_of_permutes hxQ hx4 hΓΔ hΓc' hT hTΓ hperm
    have hP : P (insert T Γ) := by
      refine ⟨?_, ?_⟩
      · rw [Finset.coe_insert]
        exact Set.insert_subset hT hΓΔ
      · intro R₁ h₁ R₂ h₂ h12
        rw [Finset.mem_insert] at h₁ h₂
        rcases h₁ with rfl | h₁ <;> rcases h₂ with rfl | h₂
        · exact absurd rfl h12
        · exact hcT R₂ h₂
        · exact (hcT R₁ h₁).symm
        · exact hΓc R₁ h₁ R₂ h₂ h12
    have hmem : insert T Γ ∈ (hΔfin.toFinset.powerset).filter P := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, hP⟩
      intro R hR
      rw [Set.Finite.mem_toFinset]
      exact hP.1 hR
    have := hΓmax _ hmem
    rw [Finset.card_insert_of_notMem hTΓ] at this
    omega
  set W : Subgroup G := ⨆ R : Γs, (R : Subgroup G) with hW
  have hRW : ∀ R ∈ Γs, R ≤ W := fun R hR => le_iSup (fun R : Γs => (R : Subgroup G)) ⟨R, hR⟩
  have hWN : ∀ R ∈ Γs, W ≤ normalizer (R : Set G) :=
    fun R hR => iSup_le_normalizer_of_commutes hΓc' hR
  have hWS : W ≤ S := iSup_le fun R => le_S_of_mem (hΓΔ R.2)
  have hm1 : ∀ T ∈ Δ, T ≤ W → T ∈ Γ := by
    intro T hT hTW
    refine hself T hT fun t ht R hR => ?_
    rw [(rightConjugate_eq_self_iff R t).mpr (hWN R hR (hTW ht))]
    exact hR
  have hm2 : ∀ s ∈ S, s ∈ normalizer (W : Set G) → ∀ R ∈ Γs, rightConjugate R s ∈ Γs := by
    intro s hsS hsN R hR
    refine hm1 _ (hs.conj_mem (hΓΔ hR) hsS) ?_
    exact (rightConjugate_mono s (hRW R hR)).trans
      ((rightConjugate_eq_self_iff W s).mpr hsN).le
  have hm3 : ∀ T ∈ Δ, T ≤ S ⊓ normalizer (W : Set G) → T ∈ Γ := by
    intro T hT hTM
    exact hself T hT fun t ht R hR => hm2 t (hTM ht).1 (hTM ht).2 R hR
  set M := S ⊓ normalizer (W : Set G) with hM
  have hm4 : ∀ s ∈ S, s ∈ normalizer (M : Set G) → s ∈ M := by
    intro s hsS hsN
    refine ⟨hsS, mem_normalizer_iSup fun R hR => ?_⟩
    have hRM : R ≤ M := _root_.le_inf (le_S_of_mem (hΓΔ hR)) ((hRW R hR).trans le_normalizer)
    have hRs : rightConjugate R s ∈ Γs := by
      refine hm3 _ (hs.conj_mem (hΓΔ hR) hsS) ?_
      exact (rightConjugate_mono s hRM).trans ((rightConjugate_eq_self_iff M s).mpr hsN).le
    exact hRW _ hRs
  have hm5 : M = S := by
    by_contra hMS
    have hlt : M < S := lt_of_le_of_ne inf_le_left hMS
    obtain ⟨s, hsS, hsM, hsN⟩ := exists_mem_normalizer_not_mem hs.S_pGroup hlt
    exact hsM (hm4 s hsS hsN)
  have hm6 : ∀ T ∈ Δ, T ∈ Γ := fun T hT => hm3 T hT (hm5 ▸ le_S_of_mem hT)
  intro R₁ h₁ R₂ h₂ h12
  exact hΓc R₁ (hm6 R₁ h₁) R₂ (hm6 R₂ h₂) h12

theorem tightly_embedded_conjugates_commute {K H : Subgroup G} (htight : TightlyEmbedded K)
    (Q : Sylow 2 ↥(H ⊓ K)) (hQ : (Q : Subgroup ↥(H ⊓ K)) ≠ ⊥) {S : Subgroup G} (hSH : S ≤ H)
    (hS2 : IsPGroup 2 S) (hQS : sylowImage _ Q ≤ S) (hΦ : frattini (sylowImage _ Q) ≠ ⊥)
    {h k : G} (hh : h ∈ H) (hk : k ∈ H) (hhS : rightConjugate (sylowImage _ Q) h ≤ S)
    (hkS : rightConjugate (sylowImage _ Q) k ≤ S)
    (hne : rightConjugate (sylowImage _ Q) h ≠ rightConjugate (sylowImage _ Q) k) :
    Commutes (rightConjugate (sylowImage _ Q) h) (rightConjugate (sylowImage _ Q) k) ∧
      rightConjugate (sylowImage _ Q) h ⊓ rightConjugate (sylowImage _ Q) k = ⊥ ∧
      ∃ e : (rightConjugate (sylowImage _ Q) h) × (rightConjugate (sylowImage _ Q) k) ≃*
          ↥(rightConjugate (sylowImage _ Q) h ⊔ rightConjugate (sylowImage _ Q) k),
        ∀ p, (e p : G) = (p.1 : G) * p.2 := by
  set Q' := sylowImage _ Q with hQ'
  have hs : Setup K H Q' S :=
    { tight := htight
      le_inf := sylowImage_le _ Q
      sylow := by
        intro R hR hR2 hQR
        have hR' : IsPGroup 2 (R.subgroupOf (H ⊓ K)) :=
          hR2.comap_of_injective _ Subtype.val_injective
        have hle : (Q : Subgroup ↥(H ⊓ K)) ≤ R.subgroupOf (H ⊓ K) := by
          intro q hq
          exact hQR ⟨q, hq, rfl⟩
        have heq := Q.is_maximal' hR' hle
        rw [hQ', sylowImage, ← heq, Subgroup.subgroupOf_map_subtype, inf_of_le_left hR]
      pGroup := sylowImage_isPGroup _ Q
      ne_bot := (sylowImage_eq_bot_iff _ Q).not.mpr hQ
      S_le := hSH
      S_pGroup := hS2
      le_S := hQS }
  have hcomm := hs.commutes_conjugatesIn hΦ _ ⟨h, hh, rfl, hhS⟩ _ ⟨k, hk, rfl, hkS⟩ hne
  have hinf := hs.inf_eq_bot_of_mem ⟨h, hh, rfl, hhS⟩ ⟨k, hk, rfl, hkS⟩ hne
  refine ⟨hcomm, hinf, ?_⟩
  set A := rightConjugate Q' h
  set B := rightConjugate Q' k
  let f : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => hcomm a a.2 b b.2)
  have hrange : f.range = A ⊔ B := by
    simpa only [Subgroup.subtype_range] using
      MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => hcomm a a.2 b b.2)
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.mem_ker] at hab
    have hab' : (a : G) * b = 1 := hab
    have ha : (a : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left hab'
    have hmem : (a : G) ∈ A ⊓ B := ⟨a.2, ha ▸ B.inv_mem b.2⟩
    rw [hinf, mem_bot] at hmem
    have hb : (b : G) = 1 := by rw [hmem, one_mul] at hab'; exact hab'
    rw [mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hmem, Subtype.ext hb⟩
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun p => ?_⟩
  rfl

end CFSG.ComponentClassification.LiteratureLocal.TightCommuting
