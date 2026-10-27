module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4SL2
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Bridge
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Linked

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem5
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix

variable {G : Type} [Group G] [Finite G]

@[expose] def CentMod (K O : Subgroup G) (g : G) : Prop :=
  ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ O

namespace CentMod

variable {K O : Subgroup G}

omit [Finite G] in
theorem one : CentMod K O 1 := fun k _ => by
  rw [one_mul, inv_one, mul_one, mul_inv_cancel]
  exact one_mem O

omit [Finite G] in
theorem mul {g h : G} (hg : CentMod K O g) (hh : CentMod K O h)
    (hgO : g ∈ normalizer (O : Set G)) : CentMod K O (g * h) := fun k hk => by
  have h1 := (mem_normalizer_iff.mp hgO _).mp (hh k hk)
  have : g * h * k * (g * h)⁻¹ * k⁻¹ =
      g * (h * k * h⁻¹ * k⁻¹) * g⁻¹ * (g * k * g⁻¹ * k⁻¹) := by group
  rw [this]
  exact mul_mem h1 (hg k hk)

omit [Finite G] in
theorem inv {g : G} (hg : CentMod K O g) (hgO : g ∈ normalizer (O : Set G)) :
    CentMod K O g⁻¹ := fun k hk => by
  have h1 := (mem_normalizer_iff.mp (inv_mem hgO) _).mp (inv_mem (hg k hk))
  have : g⁻¹ * k * g⁻¹⁻¹ * k⁻¹ = g⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ * g⁻¹⁻¹ := by group
  rw [this]
  exact h1

omit [Finite G] in
theorem conj {g q : G} (hg : CentMod K O g) (hqK : q ∈ normalizer (K : Set G))
    (hqO : q ∈ normalizer (O : Set G)) : CentMod K O (q * g * q⁻¹) := fun k hk => by
  have hk' : q⁻¹ * k * q⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (inv_mem hqK) k).mp hk
  have h1 := (mem_normalizer_iff.mp hqO _).mp (hg _ hk')
  have : q * g * q⁻¹ * k * (q * g * q⁻¹)⁻¹ * k⁻¹ =
      q * (g * (q⁻¹ * k * q⁻¹⁻¹) * g⁻¹ * (q⁻¹ * k * q⁻¹⁻¹)⁻¹) * q⁻¹ := by group
  rw [this]
  exact h1

omit [Finite G] in
theorem mono {g : G} {L : Subgroup G} (hg : CentMod K O g) (hLK : L ≤ K) : CentMod L O g :=
  fun k hk => hg k (hLK hk)

end CentMod

omit [Finite G] in
theorem eq_one_of_mem_of_odd {O : Subgroup G} (hO : Odd (Nat.card O)) {x : G} (hx : x ∈ O)
    {j : ℕ} (hj : x ^ (2 ^ j) = 1) : x = 1 := by
  have hj' : (⟨x, hx⟩ : O) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hj)
  have h := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hO))
    (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_natCard (⟨x, hx⟩ : O))
  rw [orderOf_eq_one_iff] at h
  exact congrArg Subtype.val h

theorem inf_oddCoreIn_le {Q C : Subgroup G} (hCQ : C ≤ Q) : C ⊓ oddCoreIn Q ≤ oddCoreIn C := by
  refine le_oddCoreIn (normalIn_of_le_normalizer inf_le_left fun c hc => ?_)
    ((odd_card_oddCoreIn Q).of_dvd_nat (card_dvd_of_le inf_le_right))
  exact inf_normalizer_le_normalizer_inf C (oddCoreIn Q)
    (mem_inf.mpr ⟨le_normalizer hc, normalIn_le_normalizer (oddCoreIn_normalIn Q) (hCQ hc)⟩)

theorem oddCoreIn_le_oddCoreIn {Q C : Subgroup G} (hCK : C ≤ twoPrimeLayerIn Q)
    (hKC : twoPrimeLayerIn Q ≤ C ⊔ oddCoreIn Q) : oddCoreIn C ≤ oddCoreIn Q := by
  set K := twoPrimeLayerIn Q
  set O := oddCoreIn Q
  set N := oddCoreIn C ⊔ O
  have hCQ : C ≤ Q := hCK.trans (twoPrimeLayerIn_le Q)
  have hQO : Q ≤ normalizer (O : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  have hOC : oddCoreIn C ≤ normalizer (O : Set G) := (oddCoreIn_le C).trans (hCQ.trans hQO)
  have hNodd : Odd (Nat.card N) := by
    have hodd := (odd_card_oddCoreIn C).mul (odd_card_oddCoreIn Q)
    rw [← card_sup_mul_card_inf hOC] at hodd
    exact (Nat.odd_mul.mp hodd).1
  have hCN : C ≤ normalizer (N : Set G) := fun c hc => by
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_oddCoreIn C (le_normalizer hc)),
      mem_normalizer_iff_map_conj_eq.mp (hQO (hCQ hc))]
  have hON : O ≤ normalizer (N : Set G) := fun o ho => by
    rw [mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (MulAut.conj o).injective).ge
    rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (le_normalizer ho)]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨c, hc, rfl⟩
    have hcQ := hCQ (oddCoreIn_le C hc)
    have h1 : c⁻¹ * o * c⁻¹⁻¹ ∈ O := (mem_normalizer_iff.mp (hQO (inv_mem hcQ)) o).mp ho
    have h2 : o * c * o⁻¹ = c * ((c⁻¹ * o * c⁻¹⁻¹) * o⁻¹) := by group
    show o * c * o⁻¹ ∈ N
    rw [h2]
    exact mul_mem (mem_sup_left hc) (mem_sup_right (mul_mem h1 (inv_mem ho)))
  have hKN : K ≤ normalizer (N : Set G) := hKC.trans (sup_le hCN hON)
  have hNK : N ≤ K := sup_le ((oddCoreIn_le C).trans hCK) (oddCoreIn_le_twoPrimeLayerIn Q)
  have h := le_oddCoreIn (normalIn_of_le_normalizer hNK hKN) hNodd
  rw [oddCoreIn_twoPrimeLayerIn] at h
  exact le_sup_left.trans h

theorem isSemisimpleQ_of_le_twoPrimeLayerIn {Q C : Subgroup G} (hCK : C ≤ twoPrimeLayerIn Q)
    (hKC : twoPrimeLayerIn Q ≤ C ⊔ oddCoreIn Q) : IsSemisimpleQ C :=
  isSemisimpleQ_of_le_sup hCK (by rw [oddCoreIn_twoPrimeLayerIn]; exact hKC)
    (isSemisimpleQ_twoPrimeLayerIn Q)

theorem twoPrimeLayerIn_le_oUpperTwoPrime_sup {Q C : Subgroup G} (hCK : C ≤ twoPrimeLayerIn Q)
    (hKC : twoPrimeLayerIn Q ≤ C ⊔ oddCoreIn Q) :
    twoPrimeLayerIn Q ≤ oUpperTwoPrime C ⊔ oddCoreIn Q :=
  hKC.trans (sup_le ((le_oUpperTwoPrime_sup_oddCoreIn
    (isSemisimpleQ_of_le_twoPrimeLayerIn hCK hKC)).trans
    (sup_le le_sup_left ((oddCoreIn_le_oddCoreIn hCK hKC).trans le_sup_right))) le_sup_right)

section Faithful

variable {Q C : Subgroup G} {n : ℕ}
  {ψ : oUpperTwoPrime C →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}

theorem mem_oddCoreIn_of_centMod_self (hCQ : C ≤ Q) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C)) {l : G}
    (hl : l ∈ oUpperTwoPrime C) (hc : CentMod (oUpperTwoPrime C) (oddCoreIn Q) l) :
    l ∈ oddCoreIn C := by
  have hLC : oUpperTwoPrime C ≤ C := oUpperTwoPrime_le C
  have hmem : ∀ x : oUpperTwoPrime C, (x : G) ∈ oddCoreIn C ↔ x ∈ ψ.ker := fun x => by
    rw [hker, mem_subgroupOf]
  have hz : ψ ⟨l, hl⟩ ∈ center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [mem_center_iff]
    intro s
    obtain ⟨k, rfl⟩ := hψ s
    have h1 : (⟨l, hl⟩ * k * (⟨l, hl⟩ : oUpperTwoPrime C)⁻¹ * k⁻¹ : oUpperTwoPrime C) ∈
        ψ.ker := by
      rw [← hmem]
      exact inf_oddCoreIn_le hCQ (mem_inf.mpr ⟨hLC (Subtype.prop _), hc k k.2⟩)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 := mul_inv_eq_one.mp h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, mem_bot] at hz
  exact (hmem ⟨l, hl⟩).mpr hz

theorem factorization_card_eq (hn : n ≠ 0) (hψ : Function.Surjective ψ)
    (hker : ψ.ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C)) :
    (Nat.card C).factorization 2 = n := by
  have hLC : oUpperTwoPrime C ≤ C := oUpperTwoPrime_le C
  have hkerodd : Odd (Nat.card ψ.ker) := hker ▸ odd_card_oddCoreIn_subgroupOf C _
  have hL : Nat.card (oUpperTwoPrime C) = 2 ^ n * (((2 ^ n) ^ 2 - 1) * Nat.card ψ.ker) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, card_sl2 hn]
    ring
  have : ((oUpperTwoPrime C).subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLC).mpr
      (le_normalizer.trans (normalizer_le_normalizer_oUpperTwoPrime C))
  have hodd := odd_card_quotient_of_oUpperTwoPrime_le (X := C) (N := oUpperTwoPrime C) le_rfl
  have hC : Nat.card C = 2 ^ n * ((((2 ^ n) ^ 2 - 1) * Nat.card ψ.ker) *
      Nat.card (C ⧸ (oUpperTwoPrime C).subgroupOf C)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((oUpperTwoPrime C).subgroupOf C),
      Nat.card_congr (subgroupOfEquivOfLe hLC).toEquiv, hL]
    ring
  rw [hC]
  exact factorization_two_pow_mul_odd n (((odd_four_pow_sub_one hn).mul hkerodd).mul hodd)

end Faithful

section Centralizer

variable {Q C U : Subgroup G}

theorem mem_of_two_element_of_isSylowOf {K : Subgroup G} (hU : IsSylowOf 2 U Q) (hUK : U ≤ K)
    (hQK : Q ≤ normalizer (K : Set G)) {u : G} (hu : u ∈ Q) {j : ℕ} (hj : u ^ (2 ^ j) = 1) :
    u ∈ K := by
  obtain ⟨c, hcQ, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hU
    (isPGroup_zpowers_of_pow_eq_one hj) ((zpowers_le).mpr hu)
  have hx : c⁻¹ * u * c ∈ U := hle ((mem_rightConjugate_iff _ c _).mpr
    (by rw [show c * (c⁻¹ * u * c) * c⁻¹ = u by group]; exact mem_zpowers u))
  have h1 := (mem_normalizer_iff.mp (hQK hcQ) _).mp (hUK hx)
  rwa [show c * (c⁻¹ * u * c) * c⁻¹ = u by group] at h1

variable (hCK : C ≤ twoPrimeLayerIn Q) (hU : IsSylowOf 2 U Q) (hUL : U ≤ oUpperTwoPrime C)
  (hF : ∀ l ∈ oUpperTwoPrime C, CentMod (oUpperTwoPrime C) (oddCoreIn Q) l → l ∈ oddCoreIn C)
include hCK hU hUL hF

theorem eq_one_of_centMod {u : G} (huQ : u ∈ Q) {j : ℕ} (hu : u ^ (2 ^ j) = 1)
    (hc : CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) u) : u = 1 := by
  obtain ⟨c, hcQ, hle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hU
    (isPGroup_zpowers_of_pow_eq_one hu) ((zpowers_le).mpr huQ)
  have hx : c⁻¹ * u * c ∈ U := hle ((mem_rightConjugate_iff _ c _).mpr
    (by rw [show c * (c⁻¹ * u * c) * c⁻¹ = u by group]; exact mem_zpowers u))
  have hKn : Q ≤ normalizer (twoPrimeLayerIn Q : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q)
  have hOn : Q ≤ normalizer (oddCoreIn Q : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  have hc' := hc.conj (hKn (inv_mem hcQ)) (hOn (inv_mem hcQ))
  rw [inv_inv] at hc'
  have hO := hF _ (hUL hx) (hc'.mono ((oUpperTwoPrime_le C).trans hCK))
  have hx2 : (c⁻¹ * u * c) ^ (2 ^ j) = 1 := by
    rw [show c⁻¹ * u * c = c⁻¹ * u * c⁻¹⁻¹ by rw [inv_inv], conj_pow, hu, mul_one,
      mul_inv_cancel]
  have h1 := eq_one_of_mem_of_odd (odd_card_oddCoreIn C) hO hx2
  rw [show u = c * (c⁻¹ * u * c) * c⁻¹ by group, h1, mul_one, mul_inv_cancel]

theorem mem_oddCoreIn_of_centMod {q : G} (hq : q ∈ Q)
    (hc : CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) q) : q ∈ oddCoreIn Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := twoPrimeLayerIn Q
  set O := oddCoreIn Q
  have hKn : Q ≤ normalizer (K : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q)
  have hOn : Q ≤ normalizer (O : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  let Z : Subgroup G :=
    { carrier := {g | g ∈ Q ∧ CentMod K O g}
      mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, ha.2.mul hb.2 (hOn ha.1)⟩
      one_mem' := ⟨one_mem _, CentMod.one⟩
      inv_mem' := fun ha => ⟨inv_mem ha.1, ha.2.inv (hOn ha.1)⟩ }
  have hZQ : Z ≤ Q := fun g hg => hg.1
  have hZn : NormalIn Z Q := normalIn_of_le_normalizer hZQ fun g hg => by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact ⟨mul_mem (mul_mem hg hz.1) (inv_mem hg), hz.2.conj (hKn hg) (hOn hg)⟩
    · intro hz
      have h1 : z = g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ := by group
      rw [h1]
      exact ⟨mul_mem (mul_mem (inv_mem hg) hz.1) (inv_mem (inv_mem hg)),
        hz.2.conj (hKn (inv_mem hg)) (hOn (inv_mem hg))⟩
  have hZodd : Odd (Nat.card Z) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨⟨z, hz⟩, hz2⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (even_iff_two_dvd.mp hev)
    rw [Subgroup.orderOf_mk] at hz2
    have hz1 : z = 1 := eq_one_of_centMod hCK hU hUL hF hz.1 (j := 1)
      (by rw [pow_one, ← hz2, pow_orderOf_eq_one]) hz.2
    rw [hz1, orderOf_one] at hz2
    norm_num at hz2
  exact le_oddCoreIn hZn hZodd ⟨hq, hc⟩

theorem commutator_mem_oddCoreIn_of_centMod {t : G} (htN : t ∈ normalizer (Q : Set G))
    (ht : CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) t) {q : G} (hq : q ∈ Q) :
    q * t * q⁻¹ * t⁻¹ ∈ oddCoreIn Q := by
  have hKn : Q ≤ normalizer (twoPrimeLayerIn Q : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q)
  have hOn : Q ≤ normalizer (oddCoreIn Q : Set G) := normalIn_le_normalizer (oddCoreIn_normalIn Q)
  have htO : t ∈ normalizer (oddCoreIn Q : Set G) := normalizer_le_normalizer_oddCoreIn Q htN
  refine mem_oddCoreIn_of_centMod hCK hU hUL hF ?_ ?_
  · have : q * t * q⁻¹ * t⁻¹ = q * (t * q⁻¹ * t⁻¹) := by group
    rw [this]
    exact mul_mem hq ((mem_normalizer_iff.mp htN _).mp (inv_mem hq))
  · exact (ht.conj (hKn hq) (hOn hq)).mul (ht.inv htO)
      (mul_mem (mul_mem (hOn hq) htO) (inv_mem (hOn hq)))

end Centralizer

omit [Finite G] in
theorem bar_oUpperTwoPrime_le {Q X : Subgroup G} (hX : X ≤ normalizer (Q : Set G)) :
    bar Q (oUpperTwoPrime X) ≤ AschbacherTheorem3.oTwoPrime (bar Q X) := by
  set W : Subgroup G := ((AschbacherTheorem3.oTwoPrime (bar Q X)).comap (toBar Q)).map
    (normalizer (Q : Set G)).subtype
  have hle : oUpperTwoPrime X ≤ W := by
    rw [oUpperTwoPrime, closure_le]
    rintro x ⟨hx, k, hk⟩
    refine ⟨⟨x, hX hx⟩, ?_, rfl⟩
    refine subset_closure ⟨toBar_mem_bar Q (h := ⟨x, hX hx⟩) hx, k, ?_⟩
    rw [← map_pow]
    have : (⟨x, hX hx⟩ : normalizer (Q : Set G)) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  intro z hz
  obtain ⟨y, hy, rfl⟩ := (mem_bar_iff Q _ z).mp hz
  obtain ⟨w, hw, hwy⟩ := hle hy
  rw [show y = w from Subtype.ext hwy.symm]
  exact hw

omit [Finite G] in
theorem bar_oddCoreIn_eq_bot (Q : Subgroup G) : bar Q (oddCoreIn Q) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨x, hx, rfl⟩ := (mem_bar_iff Q _ z).mp hz
  rw [mem_bot, toBar_eq_one_iff]
  exact hx

theorem thm4Case3_of_sl2 {Q C U T : Subgroup G} (htight : TightlyEmbedded Q)
    (hCK : C ≤ twoPrimeLayerIn Q) (hKC : twoPrimeLayerIn Q ≤ C ⊔ oddCoreIn Q) {n : ℕ}
    (hn : 2 ≤ n) {ψ : oUpperTwoPrime C →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)}
    (hψ : Function.Surjective ψ) (hψker : ψ.ker = (oddCoreIn C).subgroupOf (oUpperTwoPrime C))
    (hU : IsSylowOf 2 U Q) (hUL : U ≤ oUpperTwoPrime C) {g : G}
    (hg : g ∉ normalizer (Q : Set G)) (hT : IsSylowOf 2 T (rightConjugate Q g))
    (hTN : T ≤ normalizer (Q : Set G))
    (hTc : ∀ t ∈ T, CentMod (twoPrimeLayerIn Q) (oddCoreIn Q) t)
    (hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTsq : ∀ t ∈ T, t ^ 2 = 1)
    (hTcard : Nat.card T = 2 ^ n) : Thm4Case3 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCQ : C ≤ Q := hCK.trans (twoPrimeLayerIn_le Q)
  have hLC : oUpperTwoPrime C ≤ C := oUpperTwoPrime_le C
  have hLN : oUpperTwoPrime C ≤ normalizer (Q : Set G) := (hLC.trans hCQ).trans le_normalizer
  have hF : ∀ l ∈ oUpperTwoPrime C, CentMod (oUpperTwoPrime C) (oddCoreIn Q) l →
      l ∈ oddCoreIn C := fun l hl hc => mem_oddCoreIn_of_centMod_self hCQ hψ hψker hl hc
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hTQ : T ⊓ Q = ⊥ := two_subgroup_inf_conjugate_eq_bot Q T htight hT2 g hg hT.le
  have hOQ : oddCoreIn Q ≤ normalizer (Q : Set G) := (oddCoreIn_le Q).trans le_normalizer
  set A := bar Q T
  set B := bar Q (oUpperTwoPrime C)
  have hAQ : A ⊓ bar Q Q = ⊥ := by
    have h1 := bar_inf_of_core_le (D := Q) (Y := T) (Z := Q) (core_le Q)
    rw [hTQ] at h1
    rw [← h1, bar, bot_subgroupOf, Subgroup.map_bot]
  have hBQ : B ≤ bar Q Q := bar_mono Q (hLC.trans hCQ)
  have hinf : A ⊓ B = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hBQ).trans hAQ.le)
  have hcommQ : ∀ a ∈ A, ∀ b ∈ bar Q Q, a * b = b * a := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := (mem_bar_iff Q T a).mp ha
    obtain ⟨q, hq, rfl⟩ := (mem_bar_iff Q Q b).mp hb
    refine (commutator_mem_core_iff Q t q).mp ?_
    have h1 := commutator_mem_oddCoreIn_of_centMod hCK hU hUL hF t.2 (hTc t ht) (inv_mem hq)
    have htO : ((t : G))⁻¹ ∈ normalizer (oddCoreIn Q : Set G) :=
      normalizer_le_normalizer_oddCoreIn Q (inv_mem t.2)
    have h2 := (mem_normalizer_iff.mp htO _).mp h1
    have h3 : ((t : G))⁻¹ * ((q : G)⁻¹ * t * (q : G)⁻¹⁻¹ * (t : G)⁻¹) * ((t : G))⁻¹⁻¹ =
        ((t : G))⁻¹ * ((q : G))⁻¹ * t * q := by group
    rw [h3] at h2
    exact h2
  have hAcomm : ∀ a b : A, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨s, hs, rfl⟩ := (mem_bar_iff Q T a).mp ha
    obtain ⟨t, ht, rfl⟩ := (mem_bar_iff Q T b).mp hb
    apply Subtype.ext
    show toBar Q s * toBar Q t = toBar Q t * toBar Q s
    rw [← map_mul, ← map_mul, show s * t = t * s from Subtype.ext (hTcomm s hs t ht)]
  have hAsq : ∀ x : A, x ^ 2 = 1 := by
    rintro ⟨a, ha⟩
    obtain ⟨t, ht, rfl⟩ := (mem_bar_iff Q T a).mp ha
    apply Subtype.ext
    show toBar Q t ^ 2 = 1
    rw [← map_pow, show t ^ 2 = 1 from Subtype.ext (by simpa using hTsq t ht), map_one]
  obtain ⟨eA⟩ := nonempty_mulEquiv_fin_zmod_two (E := A) hAcomm hAsq
    ((card_bar_of_isPGroup hT2 hTN).trans hTcard)
  let ι : oUpperTwoPrime C →* Bar Q := (toBar Q).comp (inclusion hLN)
  have hιrange : ι.range = B := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hιker : ι.ker = ψ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, toBar_eq_one_iff, hψker, mem_subgroupOf]
    show (x : G) ∈ oddCoreIn Q ↔ (x : G) ∈ oddCoreIn C
    exact ⟨fun h => inf_oddCoreIn_le hCQ (mem_inf.mpr ⟨hLC x.2, h⟩),
      fun h => oddCoreIn_le_oddCoreIn hCK hKC h⟩
  let eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (MulEquiv.subgroupCongr hιrange).symm.trans ((QuotientGroup.quotientKerEquivRange ι).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hιker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)))
  have hsup : A ⊔ B = AschbacherTheorem3.oTwoPrime (bar Q Q ⊔ bar Q T) := by
    apply le_antisymm
    · refine sup_le (fun z hz => ?_) ((bar_oUpperTwoPrime_le (hCQ.trans le_normalizer)).trans
        (closure_mono fun x hx => ⟨mem_sup_left (bar_mono Q hCQ hx.1), hx.2⟩))
      obtain ⟨k, hk⟩ := isPGroup_bar hT2 ⟨z, hz⟩
      exact subset_closure ⟨mem_sup_right hz, k, by simpa using congrArg Subtype.val hk⟩
    · rw [AschbacherTheorem3.oTwoPrime, closure_le]
      rintro z ⟨hz, k, hk⟩
      have hTbN : bar Q T ≤ normalizer (bar Q Q : Set (Bar Q)) :=
        bar_le_normalizer hTN le_normalizer
      rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hTbN] at hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hz
      have hab : Commute a b := hcommQ a ha b hb
      rw [hab.mul_pow] at hk
      have hb2 : b ^ (2 ^ k) = 1 := by
        have h1 : b ^ (2 ^ k) = (a ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hk
        have hmem : b ^ (2 ^ k) ∈ A ⊓ bar Q Q :=
          mem_inf.mpr ⟨h1 ▸ inv_mem (pow_mem ha _), pow_mem hb _⟩
        rwa [hAQ, mem_bot] at hmem
      refine mul_mem (mem_sup_left ha) (mem_sup_right ?_)
      obtain ⟨x, hxQ, rfl⟩ := (mem_bar_iff Q Q b).mp hb
      obtain ⟨y, hy, ⟨j, hj⟩, hyx⟩ := exists_two_element_pow (toBar Q) hb2
      have hyQ : (y : G) ∈ Q := by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
        simp only [SubgroupClass.coe_zpow]
        exact zpow_mem hxQ m
      have hy2 : (y : G) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
      have hyK : (y : G) ∈ twoPrimeLayerIn Q := mem_of_two_element_of_isSylowOf hU
        (hUL.trans (hLC.trans hCK))
        (le_normalizer.trans (normalizer_le_normalizer_twoPrimeLayerIn Q)) hyQ hy2
      have h1 : toBar Q y ∈ bar Q (oUpperTwoPrime C ⊔ oddCoreIn Q) :=
        toBar_mem_bar Q (twoPrimeLayerIn_le_oUpperTwoPrime_sup hCK hKC hyK)
      rw [bar_sup hLN hOQ, bar_oddCoreIn_eq_bot, sup_bot_eq] at h1
      rw [← hyx]
      exact h1
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_of_prod hTN hsup hinf
    (fun a ha b hb => hcommQ a ha b (hBQ hb)) eA eB
  exact ⟨g, hg, T, hT, hTN, n, hn, φ, hφ, hker⟩

end CFSG.ComponentClassification.Asc75T4
