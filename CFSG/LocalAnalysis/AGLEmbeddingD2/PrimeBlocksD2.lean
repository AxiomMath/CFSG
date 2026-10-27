module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairBlocks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BlocksD2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairTools
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.AGLEmbedding.PrimeBlockClose
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorusFacts
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.ConjPowInjective

public section

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

namespace CFSG.AGLEmbeddingD2

theorem AGLPair.blockInnerNormalizer {G : Type} [Group G] [Finite G] {p : ℕ} {M H R L : Subgroup G}
    (h : AGLPair p M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (l : ↥M ⧸ CFSG.pCore 2 ↥M) (hl : l ∈ barM M L)
    (hlS : ∀ s ∈ barM M (pCoreOf 2 H), ∃ s' ∈ barM M (pCoreOf 2 H), ∀ y ∈ barM M L,
        (l * s * l⁻¹) * y * (l * s * l⁻¹)⁻¹ = s' * y * s'⁻¹) :
    l ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) :=
  h.toTwoLocalPhaseThree.blockInnerNormalizer h.isKGroup.1 h84 h86 hD2 hL l hl hlS

theorem AGLPair.mem_centralizer_of_mem_sup {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R L : Subgroup G} (h : AGLPair p M H R)
    (h84 : Asc81bEightFour) (h86 : Asc81bEightSix) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hPL : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))))
    {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hx : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hxS : x ∈ Subgroup.normalizer (barM M (pCoreOf 2 H) : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {k : ℕ} (hxq : x ^ q ^ k = 1) :
    x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.toTwoLocalPhaseThree.mem_centralizer_of_mem_sup h.isKGroup.1 h84 h86 hD2 hL hPL hx hxS hxq

theorem AGLPair.coprime_card_barM_normalizer_inf {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R L : Subgroup G} (h : AGLPair p M H R)
    (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G)
    (hKP : KFactParabolicPrime) (hC3 : CitedBlockTransvectionPrime)
    (hK5 : KFactBlockAltSevenPrime) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) → ⁅V, V⁆ = V →
        q.Coprime (Nat.card V)) :
    q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L))) :=
  h.toTwoLocalPhaseThree.coprime_card_barM_normalizer_inf h.isKGroup.1 h85 h93 hD2 hKP hC3 hK5 hL hq
    hq5 hPq

theorem AGLPair.twoGenInner_hyp {G : Type} [Group G] [Finite G] {p : ℕ}
    {M H R L : Subgroup G} (h : AGLPair p M H R) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G)
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) {q : ℕ}
    (hP : q.Coprime (Nat.card (barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L)))) :
    ¬ q ∣ Nat.card (barM M L) ∨ IsOrthogonalTwo ↥(barM M L) ∨
      (∃ m : ℕ, Nonempty (↥(barM M L) ≃* alternatingGroup (Fin m)) ∨
        Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
      (IsClassicalTwoOrG2 (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∧
        ∃ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsSylowTwoOf T (barM M L) ∧
          q.Coprime (Nat.card ↥(barM M L ⊓ Subgroup.normalizer (T : Set _)))) :=
  h.toTwoLocalPhaseThree.twoGenInner_hyp h.isKGroup.1 h85 h93 hD2 hL hP

theorem six_dvd_sq_sub_one_div_four {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    4 ∣ p ^ 2 - 1 ∧ 6 ∣ (p ^ 2 - 1) / 4 := by
  have h2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h3 : p % 3 ≠ 0 := by
    intro h
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this
    omega
  have h24 : p % 24 = 1 ∨ p % 24 = 5 ∨ p % 24 = 7 ∨ p % 24 = 11 ∨ p % 24 = 13 ∨ p % 24 = 17 ∨
      p % 24 = 19 ∨ p % 24 = 23 := by omega
  have hsq : p ^ 2 % 24 = 1 := by
    rw [pow_two, Nat.mul_mod]
    rcases h24 with h | h | h | h | h | h | h | h <;> rw [h]
  have h1 : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (by omega)
  constructor <;> omega

theorem exists_inverting_torus_element {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {B X : Subgroup G}
    (htorus : ∃ φ : Multiplicative (GaloisField p 2) ≃* X, ∀ μ : (GaloisField p 2)ˣ,
      ∃ t ∈ B, ∀ a, t * (φ a : G) * t⁻¹ =
        φ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * Multiplicative.toAdd a))) :
    ∃ t : G, t ∈ B ∧ t ∈ Subgroup.normalizer (X : Set G) ∧
      ∀ x ∈ X, t ^ ((p ^ 2 - 1) / 4) * x * (t ^ ((p ^ 2 - 1) / 4))⁻¹ = x⁻¹ := by
  have hp : p.Prime := Fact.out
  obtain ⟨h4, -⟩ := six_dvd_sq_sub_one_div_four hp hp5
  obtain ⟨φ, htor⟩ := htorus
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hord : orderOf μ = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hμ, Nat.card_units,
      GaloisField.card p 2 (by norm_num)]
  obtain ⟨t, htB, ht⟩ := htor μ
  have hc0 : (μ : GaloisField p 2) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero μ)
  have hu : 2 * ((p ^ 2 - 1) / 4) + 2 * ((p ^ 2 - 1) / 4) = p ^ 2 - 1 := by omega
  have hpos : 0 < (p ^ 2 - 1) / 4 := by
    have : 24 ≤ p ^ 2 - 1 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      omega
    omega
  have hneg : ((μ : GaloisField p 2) ^ 2) ^ ((p ^ 2 - 1) / 4) = -1 := by
    have hcc : (((μ : GaloisField p 2) ^ 2) ^ ((p ^ 2 - 1) / 4)) *
        (((μ : GaloisField p 2) ^ 2) ^ ((p ^ 2 - 1) / 4)) = 1 := by
      rw [← pow_mul, ← pow_add, hu, ← Units.val_pow_eq_pow_val, ← hord, pow_orderOf_eq_one,
        Units.val_one]
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · exfalso
      rw [← pow_mul, ← Units.val_pow_eq_pow_val, Units.val_eq_one,
        ← orderOf_dvd_iff_pow_eq_one, hord] at h
      have := Nat.le_of_dvd (by omega) h
      omega
    · exact h
  refine ⟨t, htB, mem_normalizer_of_torus_conj φ hc0 ht, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := φ.surjective ⟨x, hx⟩
  have hxa : (φ a : G) = x := congrArg Subtype.val ha
  rw [← hxa, conj_pow_of_torus_conj φ ht, hneg, neg_one_mul, ofAdd_neg, ofAdd_toAdd, map_inv,
    Subgroup.coe_inv]

section TwoPart

variable {G : Type*} [Group G]

theorem sq_conj_eq_of_inverts {X : Subgroup G} {ι : G} (hι : ∀ x ∈ X, ι * x * ι⁻¹ = x⁻¹)
    {x : G} (hx : x ∈ X) : ι ^ 2 * x * (ι ^ 2)⁻¹ = x := by
  have h1 := hι x hx
  have h2 := hι x⁻¹ (X.inv_mem hx)
  calc ι ^ 2 * x * (ι ^ 2)⁻¹ = ι * (ι * x * ι⁻¹) * ι⁻¹ := by
        rw [pow_two]; simp [mul_assoc]
    _ = ι * x⁻¹ * ι⁻¹ := by rw [h1]
    _ = x := by rw [h2, inv_inv]

theorem pow_two_mul_conj_eq {X : Subgroup G} {ι : G} (hι : ∀ x ∈ X, ι * x * ι⁻¹ = x⁻¹)
    {x : G} (hx : x ∈ X) (c : ℕ) : ι ^ (2 * c) * x * (ι ^ (2 * c))⁻¹ = x := by
  induction c with
  | zero => simp
  | succ c ih =>
    have e : ι ^ (2 * (c + 1)) = ι ^ (2 * c) * ι ^ 2 := by rw [← pow_add]; congr 1
    rw [e]
    calc ι ^ (2 * c) * ι ^ 2 * x * (ι ^ (2 * c) * ι ^ 2)⁻¹
        = ι ^ (2 * c) * (ι ^ 2 * x * (ι ^ 2)⁻¹) * (ι ^ (2 * c))⁻¹ := by group
      _ = x := by rw [sq_conj_eq_of_inverts hι hx, ih]

theorem odd_pow_inverts {X : Subgroup G} {ι : G} (hι : ∀ x ∈ X, ι * x * ι⁻¹ = x⁻¹) {j : ℕ}
    (hj : Odd j) {x : G} (hx : x ∈ X) : ι ^ j * x * (ι ^ j)⁻¹ = x⁻¹ := by
  obtain ⟨c, rfl⟩ := hj
  have e : ι ^ (2 * c + 1) = ι ^ (2 * c) * ι := by rw [pow_succ]
  rw [e]
  calc ι ^ (2 * c) * ι * x * (ι ^ (2 * c) * ι)⁻¹
      = ι ^ (2 * c) * (ι * x * ι⁻¹) * (ι ^ (2 * c))⁻¹ := by group
    _ = ι ^ (2 * c) * x⁻¹ * (ι ^ (2 * c))⁻¹ := by rw [hι x hx]
    _ = x⁻¹ := pow_two_mul_conj_eq hι (X.inv_mem hx) c

theorem exists_two_element_inverting [Finite G] {X : Subgroup G} {ι : G}
    (hι : ∀ x ∈ X, ι * x * ι⁻¹ = x⁻¹) :
    ∃ j : ℕ, Odd j ∧ (∃ k : ℕ, (ι ^ j) ^ 2 ^ k = 1) ∧
      ∀ x ∈ X, ι ^ j * x * (ι ^ j)⁻¹ = x⁻¹ := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf ι)
    (orderOf_pos ι).ne'
  refine ⟨m, hm, ⟨k, ?_⟩, fun x hx => odd_pow_inverts hι hm hx⟩
  rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]

end TwoPart

section Closure

variable {Y : Type*} [Group Y]

theorem mem_closure_two_elements_of_inverted {N : Subgroup Y} {x y : Y} {p : ℕ} (hp : Odd p)
    (hx : x ∈ N) (hy : y ∈ N) (hy2 : ∃ k : ℕ, y ^ 2 ^ k = 1) (hxp : x ^ p = 1)
    (hinv : y * x * y⁻¹ = x⁻¹) :
    x ∈ Subgroup.closure {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
  obtain ⟨k, hk⟩ := hy2
  have h1 : x * y * x⁻¹ ∈ {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    refine ⟨N.mul_mem (N.mul_mem hx hy) (N.inv_mem hx), k, ?_⟩
    rw [conj_pow, hk]; simp
  have h2 : y⁻¹ ∈ {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    refine ⟨N.inv_mem hy, k, ?_⟩
    rw [inv_pow, hk, inv_one]
  have hsq : x * x = (x * y * x⁻¹) * y⁻¹ := by
    have : y * x⁻¹ * y⁻¹ = x := by
      have h3 : y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ := by group
      rw [h3, hinv, inv_inv]
    calc x * x = x * (y * x⁻¹ * y⁻¹) := by rw [this]
      _ = (x * y * x⁻¹) * y⁻¹ := by group
  have hsq' : x ^ 2 ∈ Subgroup.closure {a : Y | a ∈ N ∧ ∃ k : ℕ, a ^ 2 ^ k = 1} := by
    rw [pow_two, hsq]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)
  obtain ⟨c, hc⟩ := hp
  have : x = (x ^ 2) ^ (c + 1) := by
    rw [← pow_mul]
    have : x ^ (2 * (c + 1)) = x ^ (2 * c + 1) * x := by
      rw [show 2 * (c + 1) = (2 * c + 1) + 1 by ring, pow_succ]
    rw [this, ← hc, hxp, one_mul]
  rw [this]
  exact Subgroup.pow_mem _ hsq' _

end Closure

section Orbit

variable {G : Type*} [Group G] [Finite G]

theorem pow_six_mem_normalizer_of_bound {t : G} {L : Subgroup G}
    (hbound : ∀ m : ℕ, (∀ a : ℕ, 0 < a → a < m → t ^ a ∉ Subgroup.normalizer (L : Set G)) →
      m ≤ 3) : t ^ 6 ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have hex : ∃ s : ℕ, 0 < s ∧ t ^ s ∈ Subgroup.normalizer (L : Set G) :=
    ⟨orderOf t, orderOf_pos t, by rw [pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩
  let s := Nat.find hex
  have hs : 0 < s ∧ t ^ s ∈ Subgroup.normalizer (L : Set G) := Nat.find_spec hex
  have hmin : ∀ a : ℕ, 0 < a → a < s → t ^ a ∉ Subgroup.normalizer (L : Set G) := by
    intro a ha has hmem
    exact Nat.find_min hex has ⟨ha, hmem⟩
  have h3 : s ≤ 3 := hbound s hmin
  have hs6 : s ∣ 6 := by
    obtain ⟨hs0, -⟩ := hs
    interval_cases s <;> norm_num
  obtain ⟨c, hc⟩ := hs6
  rw [hc, pow_mul]
  exact Subgroup.pow_mem _ hs.2 c

end Orbit

section Assembly

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem injective_map_conj_pow_aux' {L : Subgroup G} {t : G} {m : ℕ}
    (hmove : ∀ a : ℕ, 0 < a → a < m → t ^ a ∉ Subgroup.normalizer (L : Set G)) :
    Function.Injective fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom :=
  injective_map_conj_pow_of_forall_lt hmove

theorem D2L2Data.pow_six_mem_normalizer_weakSBlock {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}
    (hD1 : D1For G)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (h : D2L2Data p M H R X) {t : G} (ht : t ∈ H ⊓ M) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) : t ^ 6 ∈ Subgroup.normalizer (L : Set G) := by
  have htM : t ∈ M := ht.2
  have htS : t ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    (h.pair.inf_eq_inf_normalizer_twoCore ▸ ht).2
  refine pow_six_mem_normalizer_of_bound fun m hmove => ?_
  have hinj := injective_map_conj_pow_aux' (L := L) (t := t) (m := m) hmove
  have h1 := h.pair.card_le_pRank_three_of_blocks hB3
    (fun i : Fin m => L.map (MulAut.conj (t ^ (i : ℕ))).toMonoidHom)
    (fun i => hL.map_conj (M.pow_mem htM _) (Subgroup.pow_mem _ htS _)) hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (h.pair.pRank_inf_le_three hD1 Nat.prime_three (by decide))

theorem D2L2Data.barM_le_centralizer_of_weakSBlock {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}
    (hD1 : D1For G) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : NoXBlockFor G) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime)
    (h : D2L2Data p M H R X) (hp5 : 5 ≤ p) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) :
    barM M X ≤ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  have hp : p.Prime := Fact.out
  set S := pCoreOf 2 H with hSdef
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M S L → BlockHasThree M S L := fun L hL =>
    h.pair.blockHasThree h85 h86 h93 hD2 hK2 hC3 hK5 hL
  have hXL : X ≤ Subgroup.normalizer (L : Set G) := h.le_normalizer_weakSBlock hD1 hp5 hB3 hL
  obtain ⟨t, htK, htX, hinv⟩ := exists_inverting_torus_element hp5 h.torus
  obtain ⟨h4, h6⟩ := six_dvd_sq_sub_one_div_four hp hp5
  obtain ⟨c, hc⟩ := h6
  have hιL : t ^ ((p ^ 2 - 1) / 4) ∈ Subgroup.normalizer (L : Set G) := by
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (h.pow_six_mem_normalizer_weakSBlock hD1 hB3 htK hL) c
  obtain ⟨j, hj, ⟨k, hjk⟩, hinv2⟩ := exists_two_element_inverting hinv
  have hιM : t ^ ((p ^ 2 - 1) / 4) ∈ M := M.pow_mem htK.2 _
  have hι2M : (t ^ ((p ^ 2 - 1) / 4)) ^ j ∈ M := M.pow_mem hιM j
  have hι2L : (t ^ ((p ^ 2 - 1) / 4)) ^ j ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.pow_mem _ hιL j
  have hPq : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → ⁅V, V⁆ = V →
        p.Coprime (Nat.card V) :=
    fun V hV hVp => coprime_card_of_le_barM_of_perfect (inf_le_right.trans hL.le)
      (fun W hW hWp => h.coprime_of_perfect W
        (le_inf (hW.trans (inf_le_right.trans hL.le)) (hW.trans inf_le_left)) hWp) hV hVp
  have hP := h.pair.coprime_card_barM_normalizer_inf h85 h93 hD2 hKP hC3p hK5p hL hp hp5 hPq
  have hMtop : M ≠ ⊤ := fun hM => h.pair.not_le (hM ▸ le_top)
  have hcat : IsCatalogGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
    ((catalogSimpleSections_of_isKProper h.pair.glob.kProper M hMtop).quotient
      _).isCatalogGroup_center_quotient hL.component
  rintro _ ⟨⟨x, hxM⟩, hx, rfl⟩
  have hxX : x ∈ X := Subgroup.mem_subgroupOf.mp hx
  have hxS : x ∈ Subgroup.normalizer (S : Set G) := (h.le_inf_normalizer hxX).2
  have hxp : x ^ p = 1 := h.isElemAbelian.2 x hxX
  set xb := mk ⟨x, hxM⟩ with hxb
  set yb := mk ⟨(t ^ ((p ^ 2 - 1) / 4)) ^ j, hι2M⟩ with hyb
  have hxbN : xb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hxM (hXL hxX)
  have hybN : yb ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    mem_normalizer_barM hι2M hι2L
  have hyb2 : ∃ k : ℕ, yb ^ 2 ^ k = 1 := by
    refine ⟨k, ?_⟩
    have : (⟨(t ^ ((p ^ 2 - 1) / 4)) ^ j, hι2M⟩ : M) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hjk)
    rw [hyb, ← map_pow, this, map_one]
  have hxbp : xb ^ p = 1 := by
    have : (⟨x, hxM⟩ : M) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [hxb, ← map_pow, this, map_one]
  have hinvb : yb * xb * yb⁻¹ = xb⁻¹ := by
    have h1 : (⟨(t ^ ((p ^ 2 - 1) / 4)) ^ j, hι2M⟩ : M) * ⟨x, hxM⟩ *
        (⟨(t ^ ((p ^ 2 - 1) / 4)) ^ j, hι2M⟩ : M)⁻¹ = (⟨x, hxM⟩ : M)⁻¹ :=
      Subtype.ext (by simpa using hinv2 x hxX)
    have h2 := congrArg mk h1
    simpa only [hyb, hxb, map_mul, map_inv] using h2
  have hclos := mem_closure_two_elements_of_inverted (N := Subgroup.normalizer
      (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) (hp.odd_of_ne_two (by omega)) hxbN hybN hyb2 hxbp
    hinvb
  have hsup := hKin (↥M ⧸ CFSG.pCore 2 ↥M) (barM M L) hL.component hcat p hp hp5
    (h.pair.twoGenInner_hyp h85 h93 hD2 hL hP) xb hclos ⟨1, by simpa using hxbp⟩
  exact h.pair.mem_centralizer_of_mem_sup h84 h86 hD2 hL hP hsup
    (mem_normalizer_barM hxM hxS) (k := 1) (by simpa using hxbp)

theorem d2BlocksCentralized_of_primeBlocks (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hKin : KFactTwoGenInner) (hKP : KFactParabolicPrime)
    (hC3p : CitedBlockTransvectionPrime) (hK5p : KFactBlockAltSevenPrime) :
    D2BlocksCentralized := by
  intro G _ _ hglob hD1 p _ M H R X h hp5 L hL
  exact h.barM_le_centralizer_of_weakSBlock hD1 h84 h85 h86 h93 (hD2.noXBlockFor hglob.toD1Global)
    hK2 hC3 hK5 hKin hKP hC3p hK5p hp5 hL

end Assembly

end CFSG.AGLEmbeddingD2

