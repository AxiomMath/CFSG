module

public import CFSG.ClassicalInvolution.SolvableCase.Tight
public import CFSG.ClassicalInvolution.PerfectCase
import CFSG.ClassicalInvolution.SubnormalClosure
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12
public import Certificates.Certificate2193
public import Certificates.Certificate2200
public import CFSG.ClassicalInvolution.SolvableCase.M12Inputs
public import Certificates.Certificate9315
public import Certificates.Certificate2194
public import Certificates.Certificate9311
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12
public import CFSG.ClassicalInvolution.SolvableCase.Structure
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.ClassicalInvolution

open CFSG CFSG.Open
open scoped MatrixGroups

theorem sl2Three_eq_mul_of_pow_three :
    ∀ g : SL(2, ZMod 3), ∃ a b c : SL(2, ZMod 3), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ c ^ 3 = 1 ∧
      g = a * b * c := by
  decide +kernel

theorem mem_of_odd_orderOf {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hL : Nat.card G ≤ 2 * Nat.card L) {g : G} (hg : Odd (orderOf g)) : g ∈ L := by
  have hQ : Nat.card (G ⧸ L) ≤ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    have hpos : 0 < Nat.card L := Nat.card_pos
    by_contra hcon
    push Not at hcon
    nlinarith
  have hsq : ∀ q : G ⧸ L, q * q = 1 := by
    intro q
    have hpos : 0 < Nat.card (G ⧸ L) := Nat.card_pos
    interval_cases h : Nat.card (G ⧸ L)
    · have : Subsingleton (G ⧸ L) := Nat.card_eq_one_iff_unique.mp h |>.1
      exact Subsingleton.elim _ _
    · have := pow_card_eq_one' (G := G ⧸ L) (x := q)
      rwa [h, pow_two] at this
  have hg2 : g * g ∈ L := by
    have := hsq (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at this
    exact this
  obtain ⟨k, hk⟩ := hg
  have h1 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have : g = (g * g) ^ (k + 1) := by
    calc g = g ^ (orderOf g) * g := by rw [h1, one_mul]
      _ = g ^ (2 * k + 1) * g := by rw [hk]
      _ = (g * g) ^ (k + 1) := by
        rw [← pow_two, ← pow_mul, ← pow_succ]
        congr 1
  rw [this]
  exact L.pow_mem hg2 _

theorem odd_orderOf_of_pow_three_mem_oddCore {J : Type*} [Group J] [Finite J] {a : J}
    (ha : a ^ 3 ∈ oddCore J) : Odd (orderOf a) := by
  have hodd := QuaternionStructure.odd_natCard_oddCore J
  have h1 : Odd (orderOf (⟨a ^ 3, ha⟩ : oddCore J)) :=
    hodd.of_dvd_nat (orderOf_dvd_natCard _)
  have h2 : orderOf (a ^ 3) = orderOf (⟨a ^ 3, ha⟩ : oddCore J) := by
    rw [← Subgroup.orderOf_coe]
  rw [← h2] at h1
  have h3 : orderOf a ∣ 3 * orderOf (a ^ 3) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, pow_orderOf_eq_one]
  exact (Odd.mul (by decide) h1).of_dvd_nat h3

theorem le_of_witness_of_card {G : Type*} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hL : Nat.card G ≤ 2 * Nat.card L) {J : Subgroup G}
    (eJ : J ⧸ oddCore J ≃* SL(2, ZMod 3)) : J ≤ L := by
  intro x hx
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := sl2Three_eq_mul_of_pow_three (eJ (QuotientGroup.mk ⟨x, hx⟩))
  have key : ∀ s : SL(2, ZMod 3), s ^ 3 = 1 → ∃ s' : J, eJ (QuotientGroup.mk s') = s ∧
      (s' : G) ∈ L := by
    intro s hs
    obtain ⟨s', hs'⟩ := QuotientGroup.mk_surjective (eJ.symm s)
    refine ⟨s', by rw [hs']; simp, ?_⟩
    have h3 : s' ^ 3 ∈ oddCore J := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hs', ← map_pow, hs, map_one]
    refine mem_of_odd_orderOf L hL ?_
    have := odd_orderOf_of_pow_three_mem_oddCore h3
    rwa [← Subgroup.orderOf_coe] at this
  obtain ⟨a', ha', haL⟩ := key a ha
  obtain ⟨b', hb', hbL⟩ := key b hb
  obtain ⟨c', hc', hcL⟩ := key c hc
  have hx' : eJ (QuotientGroup.mk (⟨x, hx⟩ : J)) = eJ (QuotientGroup.mk (a' * b' * c')) := by
    rw [habc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul, ha', hb', hc']
  have hx'' := eJ.injective hx'
  rw [QuotientGroup.eq] at hx''
  have hodd : Odd (orderOf (((⟨x, hx⟩ : J)⁻¹ * (a' * b' * c'))⁻¹ : J)) := by
    have h1 := QuaternionStructure.odd_natCard_oddCore J
    have h2 : Odd (orderOf (⟨((⟨x, hx⟩ : J)⁻¹ * (a' * b' * c'))⁻¹,
        (oddCore J).inv_mem hx''⟩ : oddCore J)) := h1.of_dvd_nat (orderOf_dvd_natCard _)
    rwa [← Subgroup.orderOf_coe] at h2
  have hoL : ((((⟨x, hx⟩ : J)⁻¹ * (a' * b' * c'))⁻¹ : J) : G) ∈ L := by
    refine mem_of_odd_orderOf L hL ?_
    rw [Subgroup.orderOf_coe]
    exact hodd
  have habcL : ((a' * b' * c' : J) : G) ∈ L := by
    simp only [Subgroup.coe_mul]
    exact L.mul_mem (L.mul_mem haL hbL) hcL
  have hJ : (⟨x, hx⟩ : J) = (a' * b' * c') * ((⟨x, hx⟩ : J)⁻¹ * (a' * b' * c'))⁻¹ := by group
  have hxe : x = ((a' * b' * c' : J) : G) *
      ((((⟨x, hx⟩ : J)⁻¹ * (a' * b' * c'))⁻¹ : J) : G) := congrArg Subtype.val hJ
  rw [hxe]
  exact L.mul_mem habcL hoL

private theorem natCard_sylow_eight_of_natCard_eq_24 {Y : Type*} [Group Y] [Finite Y]
    (h : Nat.card Y = 24) (P : Sylow 2 Y) : Nat.card (P : Subgroup Y) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := P.isPGroup'.exists_card_eq
  have hidx := Subgroup.card_mul_index (P : Subgroup Y)
  have hodd : ¬ 2 ∣ (P : Subgroup Y).index := P.not_dvd_index
  rw [ha, h] at hidx
  have ha4 : a < 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hcon
    have : 0 < (P : Subgroup Y).index := Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hidx)
    nlinarith
  rw [ha]
  interval_cases a <;> simp at hidx ⊢ <;> omega

theorem natCard_sylow_eq_eight {J : Type*} [Group J] [Finite J]
    (eJ : J ⧸ oddCore J ≃* SL(2, ZMod 3)) (S : Sylow 2 J) : Nat.card (S : Subgroup J) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : Nat.card (J ⧸ oddCore J) = 24 := by
    rw [Nat.card_congr eJ.toEquiv, natCard_sl2Three]
  obtain ⟨P⟩ : Nonempty (Sylow 2 (J ⧸ oddCore J)) := inferInstance
  obtain ⟨f⟩ := QuaternionStructure.sylow_oddCore_quotient_equiv S P
  rw [← Nat.card_congr f.toEquiv]
  exact natCard_sylow_eight_of_natCard_eq_24 hY P

theorem solvable_witness_facts {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    {J : Subgroup G} (hzJ : z ∈ J) (hcent : J ≤ Subgroup.centralizer ({z} : Set G))
    (S : Sylow 2 J)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))))
    (eJ : J ⧸ oddCore J ≃* SL(2, ZMod 3)) :
    (∃ g ∈ J, orderOf g = 3) ∧ (∃ i ∈ J, i * i = z) ∧
      ∀ W : Subgroup G, W ≤ J → IsPGroup 2 W → Nat.card W ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 := natCard_sylow_eq_eight eJ S
  refine ⟨?_, ?_, ?_⟩
  · have h3 : 3 ∣ Nat.card J := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore J)
      rw [Nat.card_congr eJ.toEquiv, natCard_sl2Three] at h1
      rw [h1]
      exact Dvd.dvd.mul_right (by norm_num) _
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 h3
    exact ⟨g, g.2, by rw [Subgroup.orderOf_coe]; exact hg⟩
  ·
    have hzc : (⟨z, hzJ⟩ : J) ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent g.2) z rfl).symm
    have hord : orderOf (⟨z, hzJ⟩ : J) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hz
    have hP2 : IsPGroup 2 (Subgroup.zpowers (⟨z, hzJ⟩ : J)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
    obtain ⟨P, hP⟩ := hP2.exists_le_sylow
    have hzS : (⟨z, hzJ⟩ : J) ∈ (S : Subgroup J) :=
      QuaternionStructure.mem_sylow_of_mem_center P S hzc (hP (Subgroup.mem_zpowers _))
    obtain ⟨r, hr3, ⟨e⟩⟩ := hS
    have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    have hzS2 : orderOf (⟨⟨z, hzJ⟩, hzS⟩ : (S : Subgroup J)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    have h1 : e ⟨⟨z, hzJ⟩, hzS⟩ =
        QuaternionGroup.a (((2 ^ (r - 2) : ℕ)) : ZMod (2 * 2 ^ (r - 2))) :=
      (quaternionGroup_orderOf_eq_two_iff _ _).mp (by rw [MulEquiv.orderOf_eq]; exact hzS2)
    let i : (S : Subgroup J) := e.symm (QuaternionGroup.xa 0)
    have hii : i * i = ⟨⟨z, hzJ⟩, hzS⟩ := by
      apply e.injective
      rw [map_mul, h1]
      simp [i, QuaternionGroup.xa_mul_xa]
    refine ⟨((i : J) : G), ((i : J)).2, ?_⟩
    have := congrArg (fun q : (S : Subgroup J) => ((q : J) : G)) hii
    simpa using this
  · intro W hWJ hW
    have hW' : IsPGroup 2 (W.subgroupOf J) := hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWJ).symm
    obtain ⟨P, hP⟩ := hW'.exists_le_sylow
    have h1 : Nat.card (W.subgroupOf J) ≤ Nat.card (P : Subgroup J) := Subgroup.card_le_of_le hP
    have h2 : Nat.card (P : Subgroup J) = 8 := by
      rw [← h8]
      exact Nat.card_congr (Sylow.equiv P S).toEquiv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWJ).toEquiv] at h1
    omega

structure SolvableTightData {X : Type*} [Group X] (z : X) (J : Subgroup X) : Prop where
  mem : z ∈ J
  le_centralizer : J ≤ Subgroup.centralizer ({z} : Set X)
  centralizer_le_normalizer : Subgroup.centralizer ({z} : Set X) ≤ Subgroup.normalizer (J : Set X)
  exists_orderOf_eq_three : ∃ g ∈ J, orderOf g = 3
  exists_mul_self_eq : ∃ i ∈ J, i * i = z
  card_le_eight : ∀ W : Subgroup X, W ≤ J → IsPGroup 2 W → Nat.card W ≤ 8

theorem SolvableTightData.subgroupOf {X : Type*} [Group X] {z : X} {J : Subgroup X}
    (d : SolvableTightData z J) {F : Subgroup X} (hJF : J ≤ F) :
    SolvableTightData (⟨z, hJF d.mem⟩ : F) (J.subgroupOf F) where
  mem := d.mem
  le_centralizer x hx := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (d.le_centralizer hx) z rfl)
  centralizer_le_normalizer x hx := by
    have hxz : (x : X) ∈ Subgroup.centralizer ({z} : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx ⟨z, hJF d.mem⟩ rfl)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.mp (d.centralizer_le_normalizer hxz) (h : X)
    simpa [Subgroup.mem_subgroupOf] using this
  exists_orderOf_eq_three := by
    obtain ⟨g, hg, h3⟩ := d.exists_orderOf_eq_three
    refine ⟨⟨g, hJF hg⟩, hg, ?_⟩
    rw [← h3, ← Subgroup.orderOf_coe]
  exists_mul_self_eq := by
    obtain ⟨i, hi, hii⟩ := d.exists_mul_self_eq
    exact ⟨⟨i, hJF hi⟩, hi, Subtype.ext hii⟩
  card_le_eight W hW hW2 := by
    have h1 : W.map F.subtype ≤ J := by
      rintro _ ⟨w, hw, rfl⟩
      exact hW hw
    have := d.card_le_eight _ h1 (hW2.map F.subtype)
    rwa [Subgroup.card_map_of_injective F.subtype_injective] at this

open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)

variable {M : Type*} [Group M]

@[expose] def TightCentralizerGood (H : Subgroup M) (r : M) : Prop :=
  (∃ U : Subgroup M, U ≤ centralizerIn H r ∧ centralizerIn H r ≤ Subgroup.normalizer (U : Set M) ∧
      IsPGroup 2 U ∧ ∀ g ∈ centralizerIn H r, g ^ 3 = 1 → g ≠ 1 → ∀ W : Subgroup M,
        (∀ u ∈ U, u * g * u⁻¹ * g⁻¹ ∈ W) → 8 < Nat.card W) ∨
    ∃ N : Subgroup M, N ≤ centralizerIn H r ∧
      Nat.card (centralizerIn H r) = 2 * Nat.card N ∧ r ∉ N

theorem SolvableTightData.false_of_tightCentralizerGood {X : Type*} [Group X] [Finite M] {z : X}
    {J : Subgroup X} (d : SolvableTightData z J) (H : Subgroup M) (ι : X →* M)
    (hι : Function.Injective ι) (hle : ∀ x, ι x ∈ H) (hrange : ∀ h ∈ H, ∃ x, ι x = h)
    (hgood : TightCentralizerGood H (ι z)) : False := by
  have hcomm : ∀ x ∈ J, x * z = z * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (d.le_centralizer hx) z rfl).symm
  have hK : ∀ x ∈ J, ι x ∈ centralizerIn H (ι z) := fun x hx =>
    mem_centralizerIn.2 ⟨hle x, by rw [← map_mul, ← map_mul, hcomm x hx]⟩
  rcases hgood with ⟨U, hUK, hUn, hU2, hU3⟩ | ⟨N, hNK, hcard, hrN⟩
  · obtain ⟨g, hgJ, hg3⟩ := d.exists_orderOf_eq_three
    have hg1 : g ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hg3
      exact absurd hg3 (by norm_num)
    have hgpow : (ι g) ^ 3 = 1 := by rw [← map_pow, ← hg3, pow_orderOf_eq_one, map_one]
    have hne : ι g ≠ 1 := fun h => hg1 (hι (by rw [h, map_one]))
    have hgK := hK g hgJ
    have hbig : 8 < Nat.card (J.map ι ⊓ U : Subgroup M) := by
      refine hU3 (ι g) hgK hgpow hne _ fun u hu => ⟨?_, ?_⟩
      · obtain ⟨x, rfl⟩ := hrange u (mem_centralizerIn.1 (hUK hu)).1
        have hxz : x ∈ Subgroup.centralizer ({z} : Set X) := by
          rw [Subgroup.mem_centralizer_iff]
          intro h hh
          rw [Set.mem_singleton_iff] at hh
          rw [hh]
          exact hι (by rw [map_mul, map_mul]; exact ((mem_centralizerIn.1 (hUK hu)).2).symm)
        have hx : x * g * x⁻¹ ∈ J :=
          (Subgroup.mem_normalizer_iff.mp (d.centralizer_le_normalizer hxz) g).mp hgJ
        exact ⟨x * g * x⁻¹ * g⁻¹, J.mul_mem hx (J.inv_mem hgJ), by simp [map_mul, map_inv]⟩
      · have h1 : ι g * u⁻¹ * (ι g)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hUn hgK) u⁻¹).mp (U.inv_mem hu)
        have e : u * ι g * u⁻¹ * (ι g)⁻¹ = u * (ι g * u⁻¹ * (ι g)⁻¹) := by group
        rw [e]
        exact U.mul_mem hu h1
    have hsmall : Nat.card (J.map ι ⊓ U : Subgroup M) ≤ 8 := by
      set W : Subgroup M := J.map ι ⊓ U with hW
      have hWJ : W.comap ι ≤ J := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hx.1
        rw [← hι hyx]
        exact hy
      have hW2 : IsPGroup 2 (W.comap ι) :=
        (hU2.to_le (inf_le_right : W ≤ U)).comap_of_injective ι hι
      have hWr : W ≤ ι.range := inf_le_left.trans (Subgroup.map_le_range ι J)
      have h8 := d.card_le_eight _ hWJ hW2
      rwa [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self hWr] at h8
    omega
  · obtain ⟨i, hiJ, hii⟩ := d.exists_mul_self_eq
    have hiK := hK i hiJ
    have hpos : 0 < Nat.card N := Nat.card_pos
    have hidx : (N.subgroupOf (centralizerIn H (ι z))).index = 2 := by
      have h := Subgroup.card_mul_index (N.subgroupOf (centralizerIn H (ι z)))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv, hcard] at h
      exact Nat.eq_of_mul_eq_mul_left hpos (h.trans (mul_comm _ _))
    have hsq := Subgroup.mul_self_mem_of_index_two hidx ⟨ι i, hiK⟩
    rw [Subgroup.mem_subgroupOf] at hsq
    apply hrN
    rw [← hii, map_mul]
    exact hsq

section Lists

variable [DecidableEq M]

theorem exists_commutator_subgroup_of_check [Finite M] (K : Subgroup M) (KL UL : List M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (k : ℕ) (h : commutatorCheck KL UL k = true) :
    ∃ U : Subgroup M, U ≤ K ∧ K ≤ Subgroup.normalizer (U : Set M) ∧ IsPGroup 2 U ∧
      ∀ g ∈ K, g ^ 3 = 1 → g ≠ 1 → ∀ W : Subgroup M,
        (∀ u ∈ U, u * g * u⁻¹ * g⁻¹ ∈ W) → 8 < Nat.card W := by
  simp only [commutatorCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hUK⟩, hpow⟩, hnorm⟩, hcomm⟩ := h
  have hmul' : ∀ x ∈ UL, ∀ y ∈ UL, x * y ∈ UL := fun x hx y hy => by
    simpa using hmul x hx y hy
  have hinv' : ∀ x ∈ UL, x⁻¹ ∈ UL := hinv
  let U := subgroupOfList UL h1 hmul' hinv'
  have hmemU : ∀ x, x ∈ U ↔ x ∈ UL := fun x => Iff.rfl
  refine ⟨U, fun u hu => (hK u).1 (hUK u hu), ?_, ?_, ?_⟩
  · intro g hg
    have hgL : g ∈ KL := (hK g).2 hg
    rw [Subgroup.mem_normalizer_iff]
    have hconj : ∀ g ∈ KL, ∀ x, x ∈ UL → g * x * g⁻¹ ∈ UL := fun g hg x hx => by
      simpa using hnorm g hg x hx
    intro x
    rw [hmemU, hmemU]
    refine ⟨fun hx => hconj g hgL x hx, fun hx => ?_⟩
    have hgi : g⁻¹ ∈ KL := (hK _).2 (inv_mem hg)
    have := hconj g⁻¹ hgi _ hx
    simpa [mul_assoc] using this
  · intro u
    have hu : u.1 ∈ UL := u.2
    exact ⟨k, Subtype.ext (by simpa using hpow u.1 hu)⟩
  · intro g hg hg3 hg1 W hW
    have hgL : g ∈ KL := (hK g).2 hg
    rcases hcomm g hgL with (hne | hone) | hbig
    · exact absurd hg3 (by simpa using hne)
    · exact absurd (by simpa using hone) hg1
    · set l := (UL.map fun u => u * g * u⁻¹ * g⁻¹).dedup with hl
      have hsub : (l.toFinset : Set M) ⊆ (W : Set M) := by
        intro x hx
        simp only [Finset.mem_coe, List.mem_toFinset, hl, List.mem_dedup, List.mem_map] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        exact hW u ((hmemU u).2 hu)
      calc 8 < l.length := hbig
        _ = l.toFinset.card := (List.toFinset_card_of_nodup (List.nodup_dedup _)).symm
        _ = (l.toFinset : Set M).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ (W : Set M).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = Nat.card W := (Nat.card_coe_set_eq _).symm

end Lists

section Model

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

theorem m12_commutator_check :
    commutatorCheck (enumerationTab m12CentQ1) (permClosureList m12UGens1 20) 5 = true := by
  exact Certificates.certificate9315

theorem m12_exists_conj_tightGood :
    ∀ u ∈ NativeSporadic.M12, orderOf u = 2 →
    ∃ c ∈ NativeSporadic.M12, ∃ r : Equiv.Perm (Fin 12),
      TightCentralizerGood NativeSporadic.M12 r ∧ u = c * r * c⁻¹ := by
  obtain ⟨hcov, hcent⟩ := m12_cover_and_centralizers
  have hQ1 : ValidSchreier m12CentQ1 := (m12_oddcore_cent1).1
  have hQ2 : ValidSchreier m12CentQ2 := (m12_oddcore_cent2).1
  rw [m12Certificate_originalSubgroup] at hcov hcent
  intro u hu ho
  obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
  refine ⟨c, hc, d.1, ?_, hud⟩
  have h := hcent d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · have h1 : centralizerIn NativeSporadic.M12 m12Rep1 = m12CentQ1.originalSubgroup := h
    unfold TightCentralizerGood
    rw [h1]
    left
    exact exists_commutator_subgroup_of_check _ (enumerationTab m12CentQ1) _
      (mem_enumerationTab_iff m12CentQ1 hQ1) 5 m12_commutator_check
  · have h2 : centralizerIn NativeSporadic.M12 m12Rep2 = m12CentQ2.originalSubgroup := h
    unfold TightCentralizerGood
    rw [h2]
    right
    exact exists_index_two_of_check m12Rep2 _ (enumerationTab m12CentQ2) _
      (mem_enumerationTab_iff m12CentQ2 hQ2) (enumerationTab_nodup m12CentQ2 hQ2) m12_N2_check

end Model

open CFSG.Blueprint

theorem m12NoSolvableTightClassical :
    M12NoSolvableTightClassical := by
  intro G _ _ _ hF z hz J hzJ hJ S hS hw hs hTE
  have hFn : (genFittingFStar G).Normal := genFittingFStar_normal G
  have hcent : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ
  have hCN : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    (tightlyEmbedded_iff_centralizer_le_normalizer hzJ hz hcent S hS).mp hTE
  obtain ⟨eJ⟩ := nonempty_mulEquiv_sl2Three_of_witness hw hs
  obtain ⟨hg3, hsq, h2⟩ := solvable_witness_facts hz hzJ hcent S hS eJ
  have d : SolvableTightData z J := ⟨hzJ, hcent, hCN, hg3, hsq, h2⟩
  obtain ⟨e⟩ := hF
  have e' : genFittingFStar G ≃* NativeSporadic.M12 := e
  have hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a := by
    refine ⟨e'.symm CFSG.Sporadic.Mathieu.m12a, e'.symm CFSG.Sporadic.Mathieu.m12b,
      fun h => CFSG.Sporadic.Schreier.m12_gens_not_comm ?_⟩
    apply e'.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hCen := centralizer_genFittingFStar_eq_bot hnab
  have hL : Nat.card G ≤ 2 * Nat.card (genFittingFStar G) := by
    have hinj : Function.Injective (MulAut.conjNormal : G →* MulAut (genFittingFStar G)) := by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hgc : g ∈ Subgroup.centralizer (genFittingFStar G : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        have := congrArg (fun φ : MulAut (genFittingFStar G) => (φ ⟨h, hh⟩ : G)) hg
        simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
        calc h * g = (g * h * g⁻¹) * g := by rw [this]
          _ = g * h := by group
      rw [hCen] at hgc
      exact Subgroup.mem_bot.mp hgc
    have hAut : Nat.card (MulAut (genFittingFStar G)) ≤ 2 * Nat.card (genFittingFStar G) := by
      rw [Nat.card_congr (MulAut.congr e').toEquiv, Nat.card_congr e'.toEquiv]
      exact CFSG.Sporadic.Schreier.m12_mulAut_card
    exact (Nat.card_le_card_of_injective _ hinj).trans hAut
  have hJF : J ≤ genFittingFStar G := le_of_witness_of_card _ hL eJ
  have dF := d.subgroupOf hJF
  let ι₀ : genFittingFStar G →* Equiv.Perm (Fin 12) :=
    NativeSporadic.M12.subtype.comp e'.toMonoidHom
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp e'.injective
  have hz'o : orderOf (ι₀ (⟨z, hJF hzJ⟩ : genFittingFStar G)) = 2 := by
    rw [orderOf_injective ι₀ hι₀, Subgroup.orderOf_mk]
    exact hz
  obtain ⟨c, hc, r, hr, hcr⟩ :=
    m12_exists_conj_tightGood (ι₀ (⟨z, hJF hzJ⟩ : genFittingFStar G))
      (e' (⟨z, hJF hzJ⟩ : genFittingFStar G)).2 hz'o
  let ι : genFittingFStar G →* Equiv.Perm (Fin 12) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp ι₀
  have hι : Function.Injective ι := (MulAut.conj c⁻¹).injective.comp hι₀
  have hιz : ι (⟨z, hJF hzJ⟩ : genFittingFStar G) = r := by
    simp only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hcr]
    group
  refine dF.false_of_tightCentralizerGood NativeSporadic.M12 ι hι (fun x => ?_) (fun h hh => ?_)
    (hιz ▸ hr)
  · simp only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem (NativeSporadic.M12.inv_mem hc)
      (e' x).2) hc
  · have hmem : c * h * c⁻¹ ∈ NativeSporadic.M12 :=
      NativeSporadic.M12.mul_mem (NativeSporadic.M12.mul_mem hc hh) (NativeSporadic.M12.inv_mem hc)
    obtain ⟨x, hx⟩ := e'.surjective ⟨c * h * c⁻¹, hmem⟩
    refine ⟨x, ?_⟩
    have hx' : ι₀ x = c * h * c⁻¹ := congrArg Subtype.val hx
    simp only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hx']
    group

end CFSG.ClassicalInvolution
