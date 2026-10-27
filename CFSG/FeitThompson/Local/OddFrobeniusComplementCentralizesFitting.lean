module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FreeComplementNoFrobeniusSubgroup
import CFSG.FeitThompson.Local.OddFrobeniusComplementCyclicSylows
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.CoprimeActionDetectedOnPrimeTorsion
import CFSG.FeitThompson.Local.PrimeOrderFixedFreeKernelCoprime

open Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {L : Type*} [Group L]

private theorem ne_bot_of_natCard_eq_prime {G : Type*} [Group G] {r : ℕ} (hr : r.Prime)
    {T : Subgroup G} (h : Nat.card T = r) : T ≠ ⊥ := by
  intro hb
  rw [hb, Subgroup.card_bot] at h
  exact hr.one_lt.ne h

theorem exists_orderOf_eq_prime_of_isCyclic_of_isPGroup {G : Type*} [Group G] [Finite G]
    {r : ℕ} (hr : r.Prime) {Q : Subgroup G} (hQcyc : IsCyclic Q) (hQp : IsPGroup r Q)
    (hQbot : Q ≠ ⊥) :
    ∃ t ∈ Q, orderOf t = r ∧ ∀ x ∈ Q, x ^ r = 1 → x ∈ Subgroup.zpowers t := by
  have := Fact.mk hr
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Q).1 hQcyc
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hord : orderOf g = r ^ n := by rw [← Nat.card_zpowers, hg, hn]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    refine ⟨n - 1, ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [pow_zero, orderOf_eq_one_iff] at hord
      rw [hord] at hg
      simp only [zpowers_one_eq_bot] at hg
      exact absurd hg.symm hQbot
    · omega
  refine ⟨g ^ r ^ m, hg ▸ (Subgroup.zpowers g).pow_mem (mem_zpowers g) _, ?_, ?_⟩
  · rw [orderOf_pow, hord, Nat.gcd_eq_right (pow_dvd_pow r (by omega)), pow_succ,
      Nat.mul_div_cancel_left _ (Nat.pow_pos hr.pos)]
  · intro x hx hxr
    rw [← hg, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have h1 : g ^ (k * r) = 1 := by rw [zpow_mul, hk]; exact_mod_cast hxr
    rw [← orderOf_dvd_iff_zpow_eq_one, hord] at h1
    have h2 : ((r ^ m : ℕ) : ℤ) ∣ k := by
      have h3 : ((r ^ m : ℕ) : ℤ) * (r : ℤ) ∣ k * (r : ℤ) := by
        push_cast at h1 ⊢
        calc ((r : ℤ) ^ m) * (r : ℤ) = (r : ℤ) ^ (m + 1) := by rw [← pow_succ]
          _ ∣ k * r := h1
      exact (mul_dvd_mul_iff_right (by exact_mod_cast hr.ne_zero : (r : ℤ) ≠ 0)).1 h3
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [← hk, hc, zpow_mul, zpow_natCast]⟩

theorem false_of_frobenius_pair_subgroup_free_complement [Finite L] [Group.IsSolvable L]
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {U V : Subgroup E} (hU : U ≠ ⊥) (hV : V ≠ ⊥)
    (hnorm : V ≤ Subgroup.normalizer (U : Set E)) (hUV : U ⊓ V = ⊥)
    (hUfree : ∀ v ∈ V, v ≠ 1 → U ⊓ Subgroup.centralizer {v} = ⊥) : False := by
  have hinj := E.subtype_injective
  refine false_of_frobenius_pair_le_free_complement (E := E) hH hfree
    (U := U.map E.subtype) (V := V.map E.subtype) (Subgroup.map_subtype_le U)
    (Subgroup.map_subtype_le V) ((Subgroup.map_eq_bot_iff_of_injective _ hinj).not.2 hU)
    ((Subgroup.map_eq_bot_iff_of_injective _ hinj).not.2 hV) ?_ ?_ ?_
  · exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map _)
  · rw [← Subgroup.map_inf _ _ _ hinj, hUV, Subgroup.map_bot]
  · rintro v ⟨v₀, hv₀, rfl⟩ hv1
    have hv1' : v₀ ≠ 1 := fun h => hv1 (by rw [h]; simp)
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨⟨y, hy, rfl⟩, hxc⟩
    have hy' : (y : E) ∈ U ⊓ Subgroup.centralizer {v₀} :=
      ⟨hy, Subgroup.mem_centralizer_singleton_iff.2
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hxc))⟩
    rw [hUfree v₀ hv₀ hv1', Subgroup.mem_bot] at hy'
    simp [hy']

theorem commutator_pCore_eq_bot_of_natCard_eq_prime [Finite L] [Group.IsSolvable L]
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥)
    (hnil : Group.IsNilpotent H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {p : ℕ} (hp : p.Prime) {P : Subgroup E} (hP : Nat.card P = p)
    {r : ℕ} (hr : r.Prime) : ⁅P, pCore r E⁆ = ⊥ := by
  have _ : Group.IsSolvable H := by have := hnil; infer_instance
  have hZ : IsZGroup E := isZGroup_of_free_complement hodd hH hfree
  set Q : Subgroup E := pCore r E with hQdef
  have hQn : Q.Normal := pCore_normal r E
  have hQp : IsPGroup r Q := isPGroup_pCore hr E
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  have : IsCyclic (S : Subgroup E) := IsZGroup.isZGroup r hr S
  have hQcyc : IsCyclic Q := Subgroup.isCyclic_of_le hS
  have hPp : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [hP, pow_one])
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  suffices hkey : ∀ x ∈ P, ∀ y ∈ Q, x * y * x⁻¹ = y by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hkey x hx y hy
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rcases eq_or_ne Q ⊥ with hQb | hQb
  · intro x _ y hy
    rw [hQb, Subgroup.mem_bot] at hy
    simp [hy]
  rcases eq_or_ne r p with rfl | hrp
  ·
    have hsup : IsPGroup r (Q ⊔ P : Subgroup E) := hQp.to_sup_of_normal_left hPp
    obtain ⟨S', hS'⟩ := hsup.exists_le_sylow
    have : IsCyclic (S' : Subgroup E) := IsZGroup.isZGroup r hr S'
    have hcyc : IsCyclic (Q ⊔ P : Subgroup E) := Subgroup.isCyclic_of_le hS'
    let _inst : CommGroup (Q ⊔ P : Subgroup E) := IsCyclic.commGroup
    intro x hx y hy
    have hxs : x ∈ (Q ⊔ P : Subgroup E) := (le_sup_right : P ≤ Q ⊔ P) hx
    have hys : y ∈ (Q ⊔ P : Subgroup E) := (le_sup_left : Q ≤ Q ⊔ P) hy
    have h1 : (⟨x, hxs⟩ : (Q ⊔ P : Subgroup E)) * ⟨y, hys⟩ = ⟨y, hys⟩ * ⟨x, hxs⟩ := mul_comm' _ _
    have h2 : x * y = y * x := congrArg Subtype.val h1
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  ·
    obtain ⟨t, htQ, htord, htuniq⟩ :=
      exists_orderOf_eq_prime_of_isCyclic_of_isPGroup hr hQcyc hQp hQb
    have := Fact.mk hr
    have htr : t ^ r = 1 := by rw [← htord]; exact pow_orderOf_eq_one t
    set T : Subgroup E := Subgroup.zpowers t with hTdef
    have hTcard : Nat.card T = r := by rw [hTdef, Nat.card_zpowers, htord]
    have hTb : T ≠ ⊥ := ne_bot_of_natCard_eq_prime hr hTcard
    have hTconj : ∀ x : E, x * t * x⁻¹ ∈ T := by
      intro x
      refine htuniq _ (hQn.conj_mem t htQ x) ?_
      rw [conj_pow, htr, mul_one, mul_inv_cancel]
    have hTN : T.Normal := by
      constructor
      intro n hn g
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      rw [show g * t ^ k * g⁻¹ = (g * t * g⁻¹) ^ k from conj_zpow.symm]
      exact Subgroup.zpow_mem T (hTconj g) k
    have hPt : ∀ x ∈ P, x * t * x⁻¹ = t := by
      by_contra hnt
      push Not at hnt
      obtain ⟨x₀, hx₀P, hx₀⟩ := hnt
      refine false_of_frobenius_pair_subgroup_free_complement (E := E) hH hfree
        (U := T) (V := P) hTb (ne_bot_of_natCard_eq_prime hp hP)
        Subgroup.le_normalizer_of_normal ?_ ?_
      · refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
        rw [hTcard, hP]
        exact (Nat.coprime_primes hr hp).2 hrp
      · intro v hvP hv1
        rw [Subgroup.eq_bot_iff_forall]
        intro z hz
        by_contra hz1
        have hTz : Subgroup.zpowers z = T := zpowers_eq_of_natCard_eq_prime hr hTcard hz.1 hz1
        have hzv : Commute z v := Subgroup.mem_centralizer_singleton_iff.1 hz.2
        have htz : t ∈ Subgroup.zpowers z := by rw [hTz]; exact mem_zpowers t
        have hvt : Commute v t := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 htz
          have h := (hzv.symm).zpow_right k
          rwa [hk] at h
        have hPv : Subgroup.zpowers v = P := zpowers_eq_of_natCard_eq_prime hp hP hvP hv1
        rw [← hPv] at hx₀P
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx₀P
        exact hx₀ (by rw [(hvt.zpow_left m).eq]; group)
    let _inst : CommGroup Q := IsCyclic.commGroup
    let ρ : P →* MulAut Q := (MulAut.conjNormal (H := Q)).comp P.subtype
    have hcop : (Nat.card P).Coprime r := by
      rw [hP]; exact (Nat.coprime_primes hp hr).2 (Ne.symm hrp)
    have key : ∀ (b : P) (y : Q), y ^ r = 1 → ρ b y = y := by
      intro b y hy
      apply Subtype.ext
      change (b : E) * (y : E) * (b : E)⁻¹ = (y : E)
      have hyt : (y : E) ∈ T := htuniq _ y.2 (by exact_mod_cast congrArg Subtype.val hy)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyt
      rw [← hk, show (b : E) * t ^ k * (b : E)⁻¹ = ((b : E) * t * (b : E)⁻¹) ^ k from
        conj_zpow.symm, hPt _ b.2]
    have hρ := eq_one_of_forall_pow_eq_one hr hQp hcop ρ key
    intro x hx y hy
    have h3 : ρ ⟨x, hx⟩ ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hρ]; rfl
    exact congrArg Subtype.val h3

theorem le_centralizer_fittingRaw_of_natCard_eq_prime [Finite L] [Group.IsSolvable L]
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥)
    (hnil : Group.IsNilpotent H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {p : ℕ} (hp : p.Prime) {P : Subgroup E} (hP : Nat.card P = p) :
    P ≤ Subgroup.centralizer (fittingRaw E : Set E) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm,
    Subgroup.commutator_eq_bot_iff_le_centralizer, fittingRaw_eq_iSup_pCore]
  refine iSup₂_le fun r hr => ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact commutator_pCore_eq_bot_of_natCard_eq_prime hodd hH hnil hfree hp hP hr

theorem commutator_pCore_eq_bot_and_le_centralizer_fittingRaw_of_frobenius_decomposition
    [Finite L] [Group.IsSolvable L] (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) (_hE : E ≠ ⊥) (_hmul : (H : Set L) * (E : Set L) = Set.univ)
    (_hdisj : H ⊓ E = ⊥) (hnil : Group.IsNilpotent H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {p : ℕ} (hp : p.Prime) {P : Subgroup E} (hP : Nat.card P = p) :
    (∀ r : ℕ, r.Prime → ⁅P, pCore r E⁆ = ⊥) ∧
      P ≤ Subgroup.centralizer (fittingRaw E : Set E) :=
  ⟨fun _r hr => commutator_pCore_eq_bot_of_natCard_eq_prime hodd hH hnil hfree hp hP hr,
    le_centralizer_fittingRaw_of_natCard_eq_prime hodd hH hnil hfree hp hP⟩

theorem commutator_pCoreIn_eq_bot_and_le_centralizer_fittingRaw_of_frobenius_decomposition
    [Finite L] [Group.IsSolvable L] (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal]
    (hH : H ≠ ⊥) (_hE : E ≠ ⊥) (_hmul : (H : Set L) * (E : Set L) = Set.univ)
    (_hdisj : H ⊓ E = ⊥) (hnil : Group.IsNilpotent H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ Subgroup.centralizer {e} = ⊥)
    {p : ℕ} (hp : p.Prime) {P : Subgroup L} (hPE : P ≤ E) (hP : Nat.card P = p) :
    (∀ r : ℕ, r.Prime → ⁅P, pCoreIn r E⁆ = ⊥) ∧
      P ≤ Subgroup.centralizer (Subgroup.map E.subtype (fittingRaw E) : Set L) := by
  have hcard : Nat.card (P.subgroupOf E) = p := by
    rw [← hP, ← Subgroup.card_map_of_injective E.subtype_injective (K := P.subgroupOf E),
      Subgroup.map_subgroupOf_eq_of_le hPE]
  have hcent := le_centralizer_fittingRaw_of_natCard_eq_prime hodd hH hnil hfree hp hcard
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at hcent
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [pCoreIn_eq, ← Subgroup.map_subgroupOf_eq_of_le hPE, ← Subgroup.map_commutator,
      commutator_pCore_eq_bot_of_natCard_eq_prime hodd hH hnil hfree hp hcard hr,
      Subgroup.map_bot]
  · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      ← Subgroup.map_subgroupOf_eq_of_le hPE, ← Subgroup.map_commutator, hcent, Subgroup.map_bot]

end CFSG.FeitThompson

end
