module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG

variable {G : Type} [Group G]

@[expose] def TwoElt (x : G) : Prop := ∃ k : ℕ, x ^ (2 ^ k) = 1

theorem TwoElt.conj {x : G} (hx : TwoElt x) (g : G) : TwoElt (g * x * g⁻¹) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [conj_pow, hk]; group⟩

theorem TwoElt.map {G' : Type} [Group G'] {x : G} (hx : TwoElt x) (f : G →* G') :
    TwoElt (f x) := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem TwoElt.of_injective {G' : Type} [Group G'] {x : G} {f : G →* G'}
    (hf : Function.Injective f) (hx : TwoElt (f x)) : TwoElt x := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, hf (by rw [map_pow, hk, map_one])⟩

theorem oTwoPrimeOf_le_iff {A R : Subgroup G} :
    oTwoPrimeOf A ≤ R ↔ ∀ x ∈ A, TwoElt x → x ∈ R := by
  constructor
  · intro h x hx h2
    exact h (mem_oTwoPrimeOf hx h2.choose h2.choose_spec)
  · intro h
    exact (Subgroup.closure_le R).mpr fun x hx => h x hx.1 hx.2

theorem mem_oTwoPrimeOf_of_twoElt {A : Subgroup G} {x : G} (hx : x ∈ A) (h2 : TwoElt x) :
    x ∈ oTwoPrimeOf A :=
  mem_oTwoPrimeOf hx h2.choose h2.choose_spec

theorem mem_of_twoElt_of_odd_pow {R : Subgroup G} {x : G} (hx : TwoElt x) {m : ℕ} (hm : Odd m)
    (h : x ^ m ∈ R) : x ∈ R := by
  obtain ⟨k, hk⟩ := hx
  have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime m (orderOf x) :=
    Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm))
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact R.pow_mem h n

theorem exists_odd_pow_twoElt (x : G) [Finite G] : ∃ m : ℕ, Odd m ∧ TwoElt (x ^ m) := by
  have hpos : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  refine ⟨m, hm, k, ?_⟩
  rw [← pow_mul, mul_comm, ← hkm]
  exact pow_orderOf_eq_one x

theorem pow_mul_mem_coset {N : Subgroup G} {a : G} (ha : a ∈ normalizer (N : Set G)) {n : G}
    (hn : n ∈ N) (k : ℕ) : ∃ n' ∈ N, (n * a) ^ k = n' * a ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', h⟩ := ih
    have hak : a ^ k ∈ normalizer (N : Set G) := (normalizer (N : Set G)).pow_mem ha k
    have hconj : a ^ k * n * (a ^ k)⁻¹ ∈ N := (mem_normalizer_iff.mp hak n).mp hn
    refine ⟨n' * (a ^ k * n * (a ^ k)⁻¹), N.mul_mem hn' hconj, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem oTwoPrimeOf_normalizes {A H : Subgroup G} (hAH : A ≤ normalizer (H : Set G)) :
    A ≤ normalizer (oTwoPrimeOf H : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro a ha x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact Subgroup.subset_closure ⟨(mem_normalizer_iff.mp (hAH ha) y).mp hy.1, hy.2.elim
      fun k hk => ⟨k, by rw [conj_pow, hk]; group⟩⟩
  | one => simp
  | mul y z _ _ hy hz =>
    have : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
    rw [this]
    exact (oTwoPrimeOf H).mul_mem hy hz
  | inv y _ hy =>
    have : a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ := by group
    rw [this]
    exact (oTwoPrimeOf H).inv_mem hy

theorem twoElt_mem_sup_of_normalizes [Finite G] {U V : Subgroup G}
    (hVU : V ≤ normalizer (U : Set G)) (hUV : U ≤ normalizer (V : Set G)) {x : G}
    (hx : x ∈ U ⊔ V) (h2 : TwoElt x) : x ∈ oTwoPrimeOf U ⊔ oTwoPrimeOf V := by
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing U V hVU _).mp hx
  set W := oTwoPrimeOf U ⊔ oTwoPrimeOf V with hW
  have hUW : U ≤ normalizer (W : Set G) := fun x hx =>
    mem_normalizer_sup (oTwoPrimeOf_normalizes (A := U) (H := U) Subgroup.le_normalizer hx)
      (oTwoPrimeOf_normalizes hUV hx)
  obtain ⟨mv, hmv, hmv2⟩ := exists_odd_pow_twoElt v
  have hvW : v ^ mv ∈ W :=
    mem_sup_right (mem_oTwoPrimeOf_of_twoElt (V.pow_mem hv mv) hmv2)
  have hVN : v ∈ normalizer (U : Set G) := hVU hv
  obtain ⟨u', hu', hy⟩ := pow_mul_mem_coset hVN hu mv
  obtain ⟨mu, hmu, hmu2⟩ := exists_odd_pow_twoElt u'
  have huW : u' ^ mu ∈ W :=
    mem_sup_left (mem_oTwoPrimeOf_of_twoElt (U.pow_mem hu' mu) hmu2)
  have hu'N : u' ∈ normalizer (W : Set G) := hUW hu'
  have hwc : u' * v ^ mv * u'⁻¹ ∈ W := (mem_normalizer_iff.mp hu'N _).mp hvW
  obtain ⟨n', hn', hz⟩ := pow_mul_mem_coset hu'N hwc mu
  have hxm : (u * v) ^ (mv * mu) ∈ W := by
    rw [pow_mul, hy]
    have : u' * v ^ mv = (u' * v ^ mv * u'⁻¹) * u' := by group
    rw [this, hz]
    exact W.mul_mem hn' huW
  exact mem_of_twoElt_of_odd_pow h2 (hmv.mul hmu) hxm

theorem twoElt_mem_sup_odd [Finite G] {D O M : Subgroup G} [M.Normal]
    (hDO : D ≤ normalizer (O : Set G)) (hOodd : Odd (Nat.card O))
    (hD : ∀ d ∈ D, TwoElt d → d ∈ M) {y : G} (hy : y ∈ O ⊔ D) (h2 : TwoElt y) : y ∈ M := by
  obtain ⟨o, ho, d, hd, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing O D hDO _).mp hy
  obtain ⟨m, hm, hm2⟩ := exists_odd_pow_twoElt d
  have hdM : d ^ m ∈ M := hD _ (D.pow_mem hd m) hm2
  obtain ⟨o', ho', hym⟩ := pow_mul_mem_coset (hDO hd) ho m
  set c' := o' * d ^ m * o'⁻¹ with hc'
  have hc'M : c' ∈ M := (inferInstance : M.Normal).conj_mem _ hdM o'
  have hMn : o' ∈ normalizer (M : Set G) := Subgroup.le_normalizer_of_normal (Subgroup.mem_top o')
  obtain ⟨c'', hc'', hpow⟩ := pow_mul_mem_coset hMn hc'M (Nat.card O)
  have ho'1 : o' ^ Nat.card O = 1 := by
    have h := congrArg (fun z : O => (z : G)) (pow_card_eq_one' (x := (⟨o', ho'⟩ : O)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h
  have hyM : (o * d) ^ (m * Nat.card O) ∈ M := by
    rw [pow_mul, hym]
    have : o' * d ^ m = c' * o' := by rw [hc']; group
    rw [this, hpow, ho'1, mul_one]
    exact hc''
  exact mem_of_twoElt_of_odd_pow h2 (hm.mul hOodd) hyM

end CFSG.OddStandard.Solomon75
