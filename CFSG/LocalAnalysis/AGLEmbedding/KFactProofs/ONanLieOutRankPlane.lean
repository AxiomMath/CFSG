module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutFiveLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOutElemRankAut
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.RankThree.PartOne.OutStructure

@[expose] def IsOuterPlane (p : ℕ) {X : Type*} [Group X] (R : Subgroup (MulAut X)) : Prop :=
  CFSG.IsElementaryAbelian p R ∧ Nat.card R = p ^ 2 ∧ R ⊓ Inn X = ⊥

theorem exists_outerPlane {Y : Type} [Group Y] {p : ℕ} {L E : Subgroup Y}
    [Group.IsPerfect L] (hEN : E ≤ Subgroup.normalizer (L : Set Y))
    (hE : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hdisj : E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) = ⊥) :
    ∃ R : Subgroup (MulAut (L ⧸ Subgroup.center L)), IsOuterPlane p R := by
  have hEel := CFSG.AGLEmbedding.OutElemRank.isElementaryAbelian_of_open hE
  obtain ⟨α, hα⟩ : ∃ α : E →* MulAut (L ⧸ Subgroup.center L),
      α = (actionOnQuot L).comp (Subgroup.inclusion hEN) := ⟨_, rfl⟩
  have hαe : ∀ e : E, α e = actionOnQuot L ⟨e, hEN e.2⟩ := fun e => by rw [hα]; rfl
  have hαinn : ∀ e : E, α e ∈ Inn (L ⧸ Subgroup.center L) → e = 1 := by
    intro e he
    rw [hαe] at he
    have h1 : (e : Y) ∈ L ⊔ Subgroup.centralizer (L : Set Y) :=
      (actionOnQuot_mem_inner_iff L (hEN e.2)).mp he
    have h2 : (e : Y) ∈ E ⊓ (L ⊔ Subgroup.centralizer (L : Set Y)) := ⟨e.2, h1⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    exact hαinn e (by rw [MonoidHom.mem_ker.mp he]; exact Subgroup.one_mem _)
  refine ⟨α.range, CFSG.RankThree.PartOne.isElementaryAbelian_range_of_hom α, ?_, ?_⟩
  · rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · rw [eq_bot_iff]
    rintro x ⟨⟨e, he⟩, hI⟩
    rw [← he] at hI ⊢
    rw [hαinn e hI, map_one]
    exact Subgroup.one_mem _

section Linear

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.AGLEmbedding.OutFive

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem IsOuterPlane.psl {p ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hn : 3 ≤ n)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) [CharP K ℓ] (hK : Nat.card K = ℓ ^ f)
    {R : Subgroup (MulAut (projectiveSL n K))} (hR : IsOuterPlane p R) :
    p ∣ Nat.gcd n (Nat.card K - 1) ∧ p ∣ f := by
  obtain ⟨hRel, hcard, hRI⟩ := hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn
  obtain ⟨-, -, hDn, -, -, ⟨g, hgE, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hpE : ∀ α : MulAut (projectiveSL n K), (∃ k : ℕ, α ^ (p ^ k) ∈ linearAutGroup n K) →
      α ∈ semilinearAutGroup n K := by
    rintro α ⟨k, hk⟩
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    have hpodd : Odd (p ^ k) := (Nat.Prime.odd_of_ne_two hp hp2).pow
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (linearAutGroup_le_semilinearAutGroup hk)
  have hRE : R ≤ semilinearAutGroup n K := fun x hx =>
    hpE x ⟨1, by rw [pow_one, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx]; exact one_mem _⟩
  have hnotD : ¬ R ≤ linearAutGroup n K := fun hRD => by
    obtain ⟨g₀, hg₀D, hg₀⟩ := linearAutGroup_quotient_cyclic (K := K) (n := n) (by omega)
    have : IsCyclic (↥(linearAutGroup n K) ⧸
        (Inn (projectiveSL n K)).subgroupOf (linearAutGroup n K)) :=
      isCyclic_quotient_of_forall _ ⟨g₀, hg₀D⟩ fun α => hg₀ α α.2
    exact false_of_plane_in_cyclic_quotient hp hRD hRel hcard hRI
  have hmeet : R ⊓ linearAutGroup n K ≠ ⊥ := fun hRD => by
    have : IsCyclic (↥(semilinearAutGroup n K) ⧸
        (linearAutGroup n K).subgroupOf (semilinearAutGroup n K)) :=
      isCyclic_quotient_of_forall _ ⟨g, hgE⟩ fun α => hg α α.2
    exact false_of_plane_in_cyclic_quotient hp hRE hRel hcard hRD
  refine ⟨?_, ?_⟩
  · by_contra hdiag
    apply hmeet
    rw [eq_bot_iff]
    rintro β ⟨hβR, hβD⟩
    have hβp : β ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian β hβR
    have hβI : β ∈ Inn (projectiveSL n K) :=
      linear_D2 hp hn hdiag β hβD 1 (by rw [pow_one, hβp]; exact one_mem _)
    have : β ∈ R ⊓ Inn (projectiveSL n K) := ⟨hβR, hβI⟩
    rw [hRI] at this
    exact this
  · obtain ⟨α, hαR, hαD⟩ := Set.not_subset.1 hnotD
    have hαp : α ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαR
    have hα1 : α ≠ 1 := fun h => hαD (h ▸ one_mem _)
    have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
    obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
      CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent hℓ hf hn hK
    exact (hdesc p hp hpℓ α (hRE hαR) hαD hαord).1

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.AGLEmbedding.OutFive

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem IsOuterPlane.psu {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ ℓ ^ f = 2))
    {R : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))}
    (hR : IsOuterPlane p R) : p ∣ Nat.gcd n (ℓ ^ f + 1) ∧ p ∣ f := by
  obtain ⟨hRel, hcard, hRI⟩ := hR
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := h.finite
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨-, -, -, -, -, -, -, hFker, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn hq
  obtain ⟨-, hcyc, hcardD, -⟩ := unitary_full_diagonal_outer_order h hn hq
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic h.prime K h.card).2
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  have hnotD : ¬ R ≤ D := fun hRD => by
    have := hcyc
    exact false_of_plane_in_cyclic_quotient hp hRD hRel hcard hRI
  have hmeet : R ⊓ D ≠ ⊥ := fun hRD =>
    false_of_plane_meets_kernel_trivially hp (primeFormFieldFactor h hC hn hq) hRel hcard
      (hFker ▸ hRD)
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨β, hβR, hβD⟩, hβ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hmeet
    have hβp : (β : MulAut _) ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian _ hβR
    have hβI : (β : MulAut _) ∉
        Inn (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      fun hI => hβ1 (Subtype.ext (by
        have : (β : MulAut _) ∈ R ⊓
            Inn (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
          ⟨hβR, hI⟩
        rw [hRI] at this
        exact this))
    set x : ↥D ⧸ (Inn (primeFormP h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K))).subgroupOf D := QuotientGroup.mk (⟨β, hβD⟩ : D) with hx
    have hxp : x ^ p = 1 := by
      rw [hx, ← QuotientGroup.mk_pow]
      have : (⟨β, hβD⟩ : D) ^ p = 1 := Subtype.ext (by simpa using hβp)
      rw [this]
      rfl
    have hx1 : x ≠ 1 := fun h1 =>
      hβI (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨β, hβD⟩ : D)).mp h1))
    have hord : orderOf x = p := orderOf_eq_prime hxp hx1
    rw [← hcardD, ← hord]
    exact orderOf_dvd_natCard x
  · obtain ⟨α, hαR, hαD⟩ := Set.not_subset.1 hnotD
    have hαp : α ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαR
    have hα1 : α ≠ 1 := fun h1 => hαD (h1 ▸ one_mem _)
    have hαord : orderOf α = p := orderOf_eq_prime hαp hα1
    set σ := primeFormFieldFactor h hC hn hq α with hσ
    have hσ1 : σ ≠ 1 := fun h1 => hαD (hFker ▸ MonoidHom.mem_ker.2 h1)
    have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hαp, map_one]
    exact (CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn hq hp hp2
      hpℓ α hαord σ rfl (orderOf_eq_prime hσp hσ1)).1

end Unitary

section Transport

theorem IsOuterPlane.map_congr {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {R : Subgroup (MulAut X)} (hR : IsOuterPlane p R) :
    IsOuterPlane p (R.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨hel, hcard, hRI⟩ := hR
  set φ : MulAut X ≃* MulAut Y := MulAut.congr e with hφ
  have hinner : (Inn X).map φ.toMonoidHom = Inn Y :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  refine ⟨?_, ?_, ?_⟩
  · have := hel
    have h3 := CFSG.RankThree.PartOne.isElementaryAbelian_range_of_hom (p := p)
      (φ.toMonoidHom.comp R.subtype)
    rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h3
  · rw [Subgroup.card_map_of_injective φ.injective, hcard]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨r, hr, rfl⟩, hI⟩
    have hr1 : r ∈ R ⊓ Inn X := by
      refine ⟨hr, ?_⟩
      rw [← hinner] at hI
      obtain ⟨β, hβ, hβr⟩ := hI
      have : β = r := φ.injective hβr
      exact this ▸ hβ
    rw [hRI, Subgroup.mem_bot] at hr1
    rw [hr1, map_one]
    exact Subgroup.one_mem _

end Transport

section Arith

theorem pow_prime_modEq {p x : ℕ} (hp : p.Prime) : x ^ p ≡ x [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simp)

theorem dvd_sub_one_of_dvd_pow_sub_one {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x)
    (h : p ∣ x ^ p - 1) : p ∣ x - 1 := by
  have hle : x ≤ x ^ p := Nat.le_self_pow hp.ne_zero x
  have h1 : p ∣ x ^ p - x := (Nat.modEq_iff_dvd' hle).1 (pow_prime_modEq hp).symm
  have h2 : x ^ p - 1 = (x ^ p - x) + (x - 1) := by omega
  rw [h2] at h
  exact (Nat.dvd_add_right h1).1 h

theorem dvd_add_one_of_dvd_pow_add_one {p x : ℕ} (hp : p.Prime)
    (h : p ∣ x ^ p + 1) : p ∣ x + 1 := by
  have hle : x ≤ x ^ p := Nat.le_self_pow hp.ne_zero x
  have h1 : p ∣ x ^ p - x := (Nat.modEq_iff_dvd' hle).1 (pow_prime_modEq hp).symm
  have h2 : x ^ p + 1 = (x ^ p - x) + (x + 1) := by omega
  rw [h2] at h
  exact (Nat.dvd_add_right h1).1 h

theorem sq_dvd_pow_sub_one {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : 2 ≤ x)
    (h : p ∣ x - 1) : p ^ 2 ∣ x ^ p - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpx : ¬ p ∣ x := by
    intro hpx
    have h1 : p ∣ x - (x - 1) := Nat.dvd_sub hpx h
    have h2 : x - (x - 1) = 1 := by omega
    rw [h2] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hv := padicValNat.pow_sub_pow (p := p) (x := x) (y := 1) hodd (by omega)
    (by simpa using h) hpx (n := p) hp.ne_zero
  have hne : x ^ p - 1 ≠ 0 := by
    have : 1 < x ^ p := Nat.one_lt_pow hp.ne_zero (by omega)
    omega
  rw [one_pow] at hv
  have h1 : 1 ≤ padicValNat p (x - 1) := one_le_padicValNat_of_dvd (by omega) h
  have h2 : padicValNat p p = 1 := padicValNat_self
  exact (padicValNat_dvd_iff_le hne).2 (by omega)

theorem sq_dvd_pow_add_one {p x : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : 1 ≤ x)
    (h : p ∣ x + 1) : p ^ 2 ∣ x ^ p + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hpx : ¬ p ∣ x := by
    intro hpx
    have h1 : p ∣ 1 := (Nat.dvd_add_right hpx).1 h
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have hv := padicValNat.pow_add_pow (p := p) (x := x) (y := 1) hodd (by simpa using h) hpx
    (n := p) hodd
  have hne : x ^ p + 1 ≠ 0 := by omega
  rw [one_pow] at hv
  have h1 : 1 ≤ padicValNat p (x + 1) := one_le_padicValNat_of_dvd (by omega) h
  have h2 : padicValNat p p = 1 := padicValNat_self
  exact (padicValNat_dvd_iff_le hne).2 (by omega)

end Arith

section Models

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag

theorem IsOuterPlane.sq_dvd_psl {T : Type} [Group T] {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hn : 3 ≤ n) (hC : StatedClassicalModel T .PSL n 2 f) {R : Subgroup (MulAut T)}
    (hR : IsOuterPlane p R) : p ^ 2 ∣ 2 ^ f - 1 := by
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  let e : T ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  obtain ⟨hd, hpf⟩ := IsOuterPlane.psl hp hp2 (by omega) hn Nat.prime_two hf hK (hR.map_congr e)
  have h1 : p ∣ 2 ^ f - 1 := by
    rw [← hK]
    exact hd.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨g, rfl⟩ := hpf
  have hg : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · simp [h0] at hf
    · exact h0
  have h2 : 2 ^ (p * g) = (2 ^ g) ^ p := pow_mul' 2 p g
  rw [h2] at h1 ⊢
  have hx : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  exact sq_dvd_pow_sub_one hp hp2 hx
    (dvd_sub_one_of_dvd_pow_sub_one hp (by omega) h1)

theorem IsOuterPlane.dvd_psu {T : Type} [Group T] {p n ℓ f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hC : StatedClassicalModel T .PSU n ℓ f) {R : Subgroup (MulAut T)}
    (hR : IsOuterPlane p R) : p ∣ Nat.gcd n (ℓ ^ f + 1) ∧ p ∣ f := by
  obtain ⟨⟨hℓ, hm, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have hU : UnitaryFieldData ℓ f K := ⟨hℓ, hm, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  exact IsOuterPlane.psu hp hp2 hpℓ hU hn3 hq
    (hR.map_congr ((e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm))

theorem IsOuterPlane.sq_dvd_psu {T : Type} [Group T] {p n f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hC : StatedClassicalModel T .PSU n 2 f) {R : Subgroup (MulAut T)} (hR : IsOuterPlane p R) :
    p ^ 2 ∣ 2 ^ f + 1 := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hd, hpf⟩ := IsOuterPlane.dvd_psu hp hp2 (by omega) hC hR
  have h1 : p ∣ 2 ^ f + 1 := hd.trans (Nat.gcd_dvd_right _ _)
  have hf : 1 ≤ f := hC.1.2.1
  obtain ⟨g, rfl⟩ := hpf
  have h2 : 2 ^ (p * g) = (2 ^ g) ^ p := pow_mul' 2 p g
  rw [h2] at h1 ⊢
  exact sq_dvd_pow_add_one hp hp2 (Nat.one_le_two_pow)
    (dvd_add_one_of_dvd_pow_add_one hp h1)

end Models

end CFSG.AGLEmbedding.LieOut
