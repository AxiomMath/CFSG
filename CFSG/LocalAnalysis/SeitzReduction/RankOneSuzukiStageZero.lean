module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGoldschmidt
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SuzukiOuterOdd
public import CFSG.LocalAnalysis.SeitzReduction.SeitzFamilies
public import CFSG.RankThree.SteinbergR3ESuzukiInvolutionCentralizers

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.LieType.Ree
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974 goldschmidt1974_of_milestone)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

section General

variable {G : Type*} [Group G]

theorem inf_centralizer_eq_bot_of_center_eq_bot {L : Subgroup G} (hZ : center L = ⊥) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxL, hxC⟩ := mem_inf.1 hx
  have hmem : (⟨x, hxL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro l
    exact Subtype.ext (mem_centralizer_iff.1 hxC l l.2)
  rw [hZ, mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem le_normalizer_centralizer_of_le_normalizer {L S : Subgroup G}
    (hSN : S ≤ normalizer (L : Set G)) : S ≤ normalizer (centralizer (L : Set G) : Set G) := by
  intro g hg
  have hgN := hSN hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [mem_centralizer_iff] at hh ⊢
    intro z hz
    have hz' : g⁻¹ * z * g ∈ L := (mem_normalizer_iff''.1 hgN z).1 hz
    have e := hh _ hz'
    calc z * (g * h * g⁻¹) = g * ((g⁻¹ * z * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * z * g)) * g⁻¹ := by rw [e]
      _ = g * h * g⁻¹ * z := by group
  · intro hh
    rw [mem_centralizer_iff] at hh ⊢
    intro z hz
    have hz' : g * z * g⁻¹ ∈ L := (mem_normalizer_iff.1 hgN z).1 hz
    have e := hh _ hz'
    have e' : g * (z * h) * g⁻¹ = g * (h * z) * g⁻¹ := by
      calc g * (z * h) * g⁻¹ = (g * z * g⁻¹) * (g * h * g⁻¹) := by group
        _ = (g * h * g⁻¹) * (g * z * g⁻¹) := e
        _ = g * (h * z) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e')

theorem isPGroup_inf_sup_of_commute {p : ℕ} {A B S : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hdisj : A ⊓ B = ⊥) (hS : IsPGroup p S)
    (hSB : S ≤ normalizer (B : Set G)) : IsPGroup p (A ⊓ (S ⊔ B) : Subgroup G) := by
  rintro ⟨z, hz⟩
  obtain ⟨hzA, hzSB⟩ := mem_inf.1 hz
  have hzSB' : z ∈ ((S ⊔ B : Subgroup G) : Set G) := hzSB
  rw [coe_mul_of_left_le_normalizer_right S B hSB] at hzSB'
  obtain ⟨s, hs, b, hb, hsb⟩ := hzSB'
  have hzb : Commute z b⁻¹ := hAB z hzA b⁻¹ (inv_mem hb)
  have hs' : s = z * b⁻¹ := by rw [← hsb, mul_inv_cancel_right]
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  have hn' : s ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  rw [hs', hzb.mul_pow, inv_pow, mul_inv_eq_one] at hn'
  have hmem : z ^ p ^ n ∈ A ⊓ B := mem_inf.2 ⟨pow_mem hzA _, by rw [hn']; exact pow_mem hb _⟩
  rw [hdisj, mem_bot] at hmem
  exact ⟨n, Subtype.ext (by simpa using hmem)⟩

theorem exists_inv_mul_mem_centralizer_of_odd_card_outer {L : Subgroup G}
    (hOut : Odd (Nat.card (Outer L))) {x : G} (hxN : x ∈ normalizer (L : Set G)) {k : ℕ}
    (hxk : x ^ 2 ^ k = 1) : ∃ l ∈ L, l⁻¹ * x ∈ centralizer (L : Set G) := by
  have hαk : L.normalizerMonoidHom ⟨x, hxN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hxN⟩ : normalizer (L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hxk)
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer L)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hOut)
  have h1 : orderOf ((L.normalizerMonoidHom ⟨x, hxN⟩ : MulAut L) : Outer L) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hαk, QuotientGroup.mk_one]))
      (_root_.orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, y.2, ?_⟩
  rw [mem_centralizer_iff]
  intro z hz
  have h2 := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : G)) hy
  simp only [MulAut.conj_apply, coe_mul, coe_inv, normalizerMonoidHom_apply_apply_coe] at h2
  calc z * ((y : G)⁻¹ * x) = (y : G)⁻¹ * (y * z * (y : G)⁻¹) * x := by group
    _ = (y : G)⁻¹ * (x * z * x⁻¹) * x := by rw [h2]
    _ = (y : G)⁻¹ * x * z := by group

theorem commute_of_sq_eq_one_of_le_normalizer {L : Subgroup G} (hZ : center L = ⊥)
    (hOut : Odd (Nat.card (Outer L)))
    (hL : ∀ Q : Subgroup G, Q ≤ L → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q, x ^ 2 = 1 → y ^ 2 = 1 →
      x * y = y * x)
    (hC : ∀ Q : Subgroup G, Q ≤ centralizer (L : Set G) → IsPGroup 2 Q → ∀ x ∈ Q, ∀ y ∈ Q,
      x ^ 2 = 1 → y ^ 2 = 1 → x * y = y * x)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (L : Set G)) {x y : G}
    (hx : x ∈ S) (hy : y ∈ S) (hx2 : x ^ 2 = 1) (hy2 : y ^ 2 = 1) : x * y = y * x := by
  set C := centralizer (L : Set G)
  have hLC : L ⊓ C = ⊥ := inf_centralizer_eq_bot_of_center_eq_bot hZ
  have hcomm : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l := fun l hl c hc => mem_centralizer_iff.1 hc l hl
  have decomp : ∀ w ∈ S, w ^ 2 = 1 → ∃ l ∈ L, ∃ k ∈ C, w = l * k ∧ l ^ 2 = 1 ∧ k ^ 2 = 1 ∧
      l ∈ S ⊔ C ∧ k ∈ S ⊔ L := by
    intro w hw hw2
    obtain ⟨n, hn⟩ := hS ⟨w, hw⟩
    have hn' : w ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨l, hl, hk⟩ := exists_inv_mul_mem_centralizer_of_odd_card_outer hOut (hSN hw) hn'
    have hw' : w ^ 2 = l ^ 2 * (l⁻¹ * w) ^ 2 := by
      calc w ^ 2 = (l * (l⁻¹ * w)) ^ 2 := by rw [mul_inv_cancel_left]
        _ = l ^ 2 * (l⁻¹ * w) ^ 2 := Commute.mul_pow (hcomm l hl _ hk) 2
    have hl2 : l ^ 2 = 1 := by
      have h1 : l ^ 2 = ((l⁻¹ * w) ^ 2)⁻¹ := by
        rw [hw2] at hw'
        exact eq_inv_of_mul_eq_one_left hw'.symm
      have hmem : l ^ 2 ∈ L ⊓ C :=
        mem_inf.2 ⟨pow_mem hl 2, by rw [h1]; exact inv_mem (pow_mem hk 2)⟩
      rw [hLC, mem_bot] at hmem
      exact hmem
    refine ⟨l, hl, l⁻¹ * w, hk, by rw [mul_inv_cancel_left], hl2, ?_, ?_, ?_⟩
    · rw [hl2, one_mul] at hw'
      rw [← hw', hw2]
    · have hmem := mul_mem_sup hw (inv_mem hk)
      rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    · have hmem := mul_mem_sup (inv_mem hl) hw
      rwa [sup_comm] at hmem
  obtain ⟨l₁, hl₁, k₁, hk₁, rfl, hl₁2, hk₁2, hl₁S, hk₁S⟩ := decomp x hx hx2
  obtain ⟨l₂, hl₂, k₂, hk₂, rfl, hl₂2, hk₂2, hl₂S, hk₂S⟩ := decomp y hy hy2
  have hSC : S ≤ normalizer (C : Set G) := le_normalizer_centralizer_of_le_normalizer hSN
  have hQL : IsPGroup 2 (L ⊓ (S ⊔ C) : Subgroup G) :=
    isPGroup_inf_sup_of_commute hcomm hLC hS hSC
  have hQC : IsPGroup 2 (C ⊓ (S ⊔ L) : Subgroup G) :=
    isPGroup_inf_sup_of_commute (fun c hc l hl => (hcomm l hl c hc).symm)
      (by rw [inf_comm]; exact hLC) hS hSN
  have h12 : l₁ * l₂ = l₂ * l₁ :=
    hL _ inf_le_left hQL l₁ (mem_inf.2 ⟨hl₁, hl₁S⟩) l₂ (mem_inf.2 ⟨hl₂, hl₂S⟩) hl₁2 hl₂2
  have k12 : k₁ * k₂ = k₂ * k₁ :=
    hC _ inf_le_left hQC k₁ (mem_inf.2 ⟨hk₁, hk₁S⟩) k₂ (mem_inf.2 ⟨hk₂, hk₂S⟩) hk₁2 hk₂2
  have c12 : k₁ * l₂ = l₂ * k₁ := (hcomm l₂ hl₂ k₁ hk₁).symm
  have c21 : k₂ * l₁ = l₁ * k₂ := (hcomm l₁ hl₁ k₂ hk₂).symm
  calc l₁ * k₁ * (l₂ * k₂) = l₁ * (k₁ * l₂) * k₂ := by group
    _ = l₁ * (l₂ * k₁) * k₂ := by rw [c12]
    _ = (l₁ * l₂) * (k₁ * k₂) := by group
    _ = (l₂ * l₁) * (k₂ * k₁) := by rw [h12, k12]
    _ = l₂ * (l₁ * k₂) * k₁ := by group
    _ = l₂ * (k₂ * l₁) * k₁ := by rw [c21]
    _ = l₂ * k₂ * (l₁ * k₁) := by group

theorem commute_of_isPGroup_of_isCyclic_sylow [Finite G] {C : Subgroup G}
    (hcyc : ∃ P : Sylow 2 C, IsCyclic (P : Subgroup C)) {Q : Subgroup G} (hQC : Q ≤ C)
    (hQ : IsPGroup 2 Q) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) : x * y = y * x := by
  obtain ⟨P, hP⟩ := hcyc
  obtain ⟨P', hP'⟩ := (hQ.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq C P P'
  set x' : C := ⟨x, hQC hx⟩
  set y' : C := ⟨y, hQC hy⟩
  have hx' : g⁻¹ * x' * g ∈ (P : Subgroup C) :=
    (CFSG.RankThree.mem_smul_sylow_iff P g x').1 (hP' (mem_subgroupOf.2 hx))
  have hy' : g⁻¹ * y' * g ∈ (P : Subgroup C) :=
    (CFSG.RankThree.mem_smul_sylow_iff P g y').1 (hP' (mem_subgroupOf.2 hy))
  have key : (g⁻¹ * x' * g) * (g⁻¹ * y' * g) = (g⁻¹ * y' * g) * (g⁻¹ * x' * g) :=
    congrArg Subtype.val (mul_comm' (⟨_, hx'⟩ : (P : Subgroup C)) ⟨_, hy'⟩)
  have e1 : (g⁻¹ * x' * g) * (g⁻¹ * y' * g) = g⁻¹ * (x' * y') * g := by group
  have e2 : (g⁻¹ * y' * g) * (g⁻¹ * x' * g) = g⁻¹ * (y' * x') * g := by group
  rw [e1, e2] at key
  exact congrArg Subtype.val (mul_left_cancel (mul_right_cancel key))

theorem normalizer_zpowers_le_centralizer_of_orderOf_eq_two [Finite G] {t : G}
    (ht : orderOf t = 2) : normalizer (zpowers t : Set G) ≤ centralizer {t} := by
  classical
  intro g hg
  rw [mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have h1 : g * z * g⁻¹ ∈ zpowers z := (mem_normalizer_iff.1 hg z).1 (mem_zpowers z)
  rw [mem_zpowers_iff_mem_range_orderOf, ht, Finset.mem_image] at h1
  obtain ⟨k, hk, hkeq⟩ := h1
  rw [Finset.mem_range] at hk
  interval_cases k
  · exfalso
    rw [pow_zero, eq_comm, mul_inv_eq_one, mul_eq_left] at hkeq
    rw [hkeq, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rw [pow_one, eq_comm, mul_inv_eq_iff_eq_mul] at hkeq
    exact hkeq.symm

end General

theorem false_of_sylow_of_commute_sq_eq_one (hGold : Goldschmidt1974) {G : Type} [Group G]
    [Finite G] {L : Subgroup G} (h : SeitzSetting G L) (h1 : SeitzRankOne L) (S : Sylow 2 G)
    (hS : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x ^ 2 = 1 → y ^ 2 = 1 →
      x * y = y * x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup G :=
    { carrier := {x | x ∈ (S : Subgroup G) ∧ x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy =>
        ⟨(S : Subgroup G).mul_mem hx.1 hy.1, by
          rw [Commute.mul_pow (hS x hx.1 y hy.1 hx.2 hy.2), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨(S : Subgroup G).one_mem, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨(S : Subgroup G).inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hmemA : ∀ x, x ∈ A ↔ x ∈ (S : Subgroup G) ∧ x ^ 2 = 1 := fun x => Iff.rfl
  have hAS : A ≤ (S : Subgroup G) := fun x hx => ((hmemA x).1 hx).1
  have hAab : IsMulCommutative A := IsMulCommutative.of_comm fun a b =>
    Subtype.ext (hS a ((hmemA a).1 a.2).1 b ((hmemA b).1 b.2).1 ((hmemA a).1 a.2).2
      ((hmemA b).1 b.2).2)
  have hA1 : A ≠ ⊥ := by
    obtain ⟨t, ht, -, -⟩ := exists_involution_centralizer_of_seitzSetting h
    have h2G : 2 ^ 1 ∣ Nat.card G := by
      rw [pow_one, ← ht]
      exact _root_.orderOf_dvd_natCard t
    have h2S : 2 ∣ Nat.card (S : Subgroup G) := by
      simpa using S.pow_dvd_card_of_pow_dvd_card h2G
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup G)) 2 h2S
    have hs' : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe, hs]
    intro hbot
    have hsA : (s : G) ∈ A := (hmemA _).2 ⟨s.2, by
      have e := pow_orderOf_eq_one (s : G)
      rwa [hs'] at e⟩
    rw [hbot, mem_bot] at hsA
    rw [hsA, orderOf_one] at hs'
    exact absurd hs' (by norm_num)
  have hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ (S : Subgroup G) → g⁻¹ * a * g ∈ A := by
    intro a ha g hg
    refine (hmemA _).2 ⟨hg, ?_⟩
    have e : (g⁻¹ * a * g) ^ 2 = g⁻¹ * a ^ 2 * g := by rw [sq, sq]; group
    rw [e, ((hmemA a).1 ha).2, mul_one, inv_mul_cancel]
  exact false_of_stronglyClosed_abelian_of_goldschmidt hGold h h1 S hAS hAab hA1 hcl

section Suzuki

variable {a : ℕ} {K : Type} [Field K]

theorem commute_of_mem_suzukiU_of_sq_eq_one [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {x y : suzukiGroup a K} (hx : x ∈ suzukiU a K)
    (hy : y ∈ suzukiU a K) (hx2 : x ^ 2 = 1) : x * y = y * x := by
  obtain ⟨h2, -, -⟩ := suzuki_frob_data a hK
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
  have hsq : suzukiSElt a K u v ^ 2 = suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
    rw [sq, suzukiSElt_mul hK, suzukiSElt_inj]
    constructor
    · linear_combination u * h2
    · rw [pow_succ]
      linear_combination v * h2
  rw [hsq, ← suzukiSElt_zero_zero hK, suzukiSElt_inj] at hx2
  have hu : u = 0 := (pow_eq_zero_iff (Nat.succ_ne_zero _)).1 hx2.2
  subst hu
  exact suzukiSElt_zero_commute hK v c d

theorem commute_of_isPGroup_suzukiGroup_of_sq_eq_one [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Q : Subgroup (suzukiGroup a K)} (hQ : IsPGroup 2 Q)
    {x y : suzukiGroup a K} (hx : x ∈ Q) (hy : y ∈ Q) (hx2 : x ^ 2 = 1) : x * y = y * x := by
  have := finite_suzukiGroup hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P₀ := Sylow.ofCard (suzukiU a K) (CFSG.RankThree.card_suzukiU_eq hK)
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P₀ P
  have hx₀ : g⁻¹ * x * g ∈ suzukiU a K := (CFSG.RankThree.mem_smul_sylow_iff P₀ g x).1 (hP hx)
  have hy₀ : g⁻¹ * y * g ∈ suzukiU a K := (CFSG.RankThree.mem_smul_sylow_iff P₀ g y).1 (hP hy)
  have hx₀2 : (g⁻¹ * x * g) ^ 2 = 1 := by
    have e : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by rw [sq, sq]; group
    rw [e, hx2, mul_one, inv_mul_cancel]
  have key := commute_of_mem_suzukiU_of_sq_eq_one hK hx₀ hy₀ hx₀2
  have e1 : g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
  have e2 : g⁻¹ * y * g * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
  rw [e1, e2] at key
  exact mul_left_cancel (mul_right_cancel key)

end Suzuki

theorem suzukiModel_of_lieModel_twistedB2 {Y : Type} [Group Y] {p f : ℕ}
    (h : LieModel Y .twistedB2 0 p f) : SuzukiModel Y p f :=
  (CFSG.Blueprint.LieModel.suzukiModel h).2

theorem odd_card_outer_of_lieModel_twistedB2 {Y : Type} [Group Y]
    {f : ℕ} (h : LieModel Y .twistedB2 0 2 f) : Odd (Nat.card (Outer Y)) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  rw [Nat.card_congr (equivalence e).toEquiv]
  exact CFSG.ProperTwoGeneratedCore.HighRankPair.odd_card_outer_suzukiGroup ha hK

theorem commute_of_isPGroup_of_lieModel_twistedB2 {Y : Type}
    [Group Y] {f : ℕ} (h : LieModel Y .twistedB2 0 2 f) {Q : Subgroup Y} (hQ : IsPGroup 2 Q)
    {x y : Y} (hx : x ∈ Q) (hy : y ∈ Q) (hx2 : x ^ 2 = 1) : x * y = y * x := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := suzukiModel_of_lieModel_twistedB2 h
  have key := commute_of_isPGroup_suzukiGroup_of_sq_eq_one hK (hQ.map e.toMonoidHom)
    (mem_map_of_mem e.toMonoidHom hx) (mem_map_of_mem e.toMonoidHom hy)
    (by rw [MulEquiv.coe_toMonoidHom, ← map_pow, hx2, map_one])
  simp only [MulEquiv.coe_toMonoidHom, ← map_mul] at key
  exact e.injective key

theorem sylow_not_le_normalizer_suzuki_of_goldschmidt
    (hGold : Goldschmidt1974) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hL : LieModel L .twistedB2 0 2 f) (S : Sylow 2 G) :
    ¬ (S : Subgroup G) ≤ normalizer (L : Set G) := by
  intro hSN
  have hcyc : ∃ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))) := h.2.2.2.2.2.1
  refine false_of_sylow_of_commute_sq_eq_one hGold h (Or.inr (Or.inr ⟨f, hL⟩)) S ?_
  intro x hx y hy hx2 hy2
  refine commute_of_sq_eq_one_of_le_normalizer h.center_eq_bot
    (odd_card_outer_of_lieModel_twistedB2 hL) ?_ ?_ S.isPGroup' hSN hx hy hx2 hy2
  · intro Q hQL hQ x hx y hy hx2 _
    have key := commute_of_isPGroup_of_lieModel_twistedB2 hL (hQ.comap_subtype (K := L))
      (x := ⟨x, hQL hx⟩) (y := ⟨y, hQL hy⟩) (mem_subgroupOf.2 hx) (mem_subgroupOf.2 hy)
      (Subtype.ext (by simpa using hx2))
    exact congrArg Subtype.val key
  · intro Q hQC hQ x hx y hy _ _
    exact commute_of_isPGroup_of_isCyclic_sylow hcyc hQC hQ hx hy

theorem not_exists_sylow_eq_suzuki_of_goldschmidt
    (hGold : Goldschmidt1974) {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : SeitzSetting G L) {f : ℕ} (hL : LieModel L .twistedB2 0 2 f) {T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G)) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T := by
  rintro ⟨S, rfl⟩
  exact sylow_not_le_normalizer_suzuki_of_goldschmidt hGold h hL S hT

theorem not_exists_sylow_eq_suzuki_of_le_normalizer_zpowers_of_goldschmidt
    (hGold : Goldschmidt1974) {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : SeitzSetting G L) {f : ℕ} (hL : LieModel L .twistedB2 0 2 f) {t : G}
    (ht : orderOf t = 2) (hN : centralizer {t} ≤ normalizer (L : Set G)) {T : Subgroup G}
    (hT : T ≤ normalizer (zpowers t : Set G)) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
  not_exists_sylow_eq_suzuki_of_goldschmidt hGold h hL
    ((hT.trans (normalizer_zpowers_le_centralizer_of_orderOf_eq_two ht)).trans hN)

theorem not_exists_sylow_eq_suzuki_of_le_normalizer_zpowers
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : SeitzSetting G L) {f : ℕ}
    (hL : LieModel L .twistedB2 0 2 f) {t : G} (ht : orderOf t = 2)
    (hN : centralizer {t} ≤ normalizer (L : Set G)) {T : Subgroup G}
    (hT : T ≤ normalizer (zpowers t : Set G)) : ¬ ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
  not_exists_sylow_eq_suzuki_of_le_normalizer_zpowers_of_goldschmidt goldschmidt1974_of_milestone
    h hL ht hN hT

end CFSG.SeitzReduction.RankOne
