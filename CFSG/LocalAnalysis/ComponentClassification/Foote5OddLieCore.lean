module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized
import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open CFSG Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

@[expose] def oddFixed (i : MulAut S) : Subgroup S := closure {s | i s = s ∧ Odd (orderOf s)}

@[expose] def innerPart (i : MulAut S) (R : Subgroup (MulAut S)) : Subgroup S :=
  oddFixed i ⊓ R.comap MulAut.conj

theorem conj_apply_eq (σ : MulAut S) (s : S) :
    MulAut.conj (σ s) = σ * MulAut.conj s * σ⁻¹ := by
  ext x
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem conj_injective (hZ : center S = ⊥) : Function.Injective (MulAut.conj : S →* MulAut S) := by
  intro a b hab
  have hc : a⁻¹ * b ∈ center S := by
    rw [mem_center_iff]
    intro g
    have h := congrArg (fun τ : MulAut S => τ g) hab
    simp only [MulAut.conj_apply] at h
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h]
      _ = a⁻¹ * b * g := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at hc
  exact hc

variable {i : MulAut S} {R : Subgroup (MulAut S)}
  (hRi : ∀ r ∈ R, r * i = i * r)
  (hRconj : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
    MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)

include hRconj in
theorem conj_mem_normalizer {t : S} (ht : t ∈ oddFixed i) :
    MulAut.conj t ∈ normalizer (R : Set (MulAut S)) := by
  have hle : (oddFixed i).map MulAut.conj ≤ normalizer (R : Set (MulAut S)) := by
    rw [oddFixed, MonoidHom.map_closure, closure_le]
    rintro _ ⟨s, ⟨hs, hso⟩, rfl⟩
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro r
    refine ⟨fun hr => hRconj s hs hso r hr, fun hr => ?_⟩
    have hs' : i s⁻¹ = s⁻¹ := by rw [map_inv, hs]
    have := hRconj s⁻¹ hs' (by rwa [orderOf_inv]) _ hr
    rwa [map_inv, inv_inv, show (MulAut.conj s)⁻¹ * (MulAut.conj s * r * (MulAut.conj s)⁻¹) *
      MulAut.conj s = r by group] at this
  exact hle ⟨t, ht, rfl⟩

include hRi in
theorem map_mem_oddFixed {r : MulAut S} (hr : r ∈ R) {t : S} (ht : t ∈ oddFixed i) :
    r t ∈ oddFixed i := by
  have hle : oddFixed i ≤ (oddFixed i).comap r.toMonoidHom := by
    rw [oddFixed, closure_le]
    rintro s ⟨hs, hso⟩
    refine subset_closure ⟨?_, ?_⟩
    · have := congrArg (fun τ : MulAut S => τ s) (hRi r hr)
      simp only [MulAut.mul_apply] at this
      change i (r s) = r s
      rw [← this, hs]
    · change Odd (orderOf (r s))
      rw [MulEquiv.orderOf_eq]
      exact hso
  exact hle ht

include hRi hRconj in
theorem mul_inv_mem_innerPart {r : MulAut S} (hr : r ∈ R) {t : S} (ht : t ∈ oddFixed i) :
    r t * t⁻¹ ∈ innerPart i R := by
  refine mem_inf.mpr ⟨mul_mem (map_mem_oddFixed hRi hr ht) (inv_mem ht), ?_⟩
  rw [mem_comap, map_mul, map_inv, conj_apply_eq]
  have h1 : MulAut.conj t * r⁻¹ * (MulAut.conj t)⁻¹ ∈ R :=
    (mem_normalizer_iff.mp (conj_mem_normalizer hRconj ht) _).mp (inv_mem hr)
  have e : r * MulAut.conj t * r⁻¹ * (MulAut.conj t)⁻¹ =
      r * (MulAut.conj t * r⁻¹ * (MulAut.conj t)⁻¹) := by group
  rw [e]
  exact mul_mem hr h1

include hRconj in
theorem conj_mem_innerPart {t n : S} (ht : t ∈ oddFixed i) (hn : n ∈ innerPart i R) :
    t * n * t⁻¹ ∈ innerPart i R := by
  obtain ⟨hnT, hnR⟩ := mem_inf.mp hn
  refine mem_inf.mpr ⟨mul_mem (mul_mem ht hnT) (inv_mem ht), ?_⟩
  rw [mem_comap, map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.mp (conj_mem_normalizer hRconj ht) _).mp hnR

theorem odd_card_innerPart [Finite S] (hZ : center S = ⊥) (hRodd : Odd (Nat.card R)) :
    Odd (Nat.card (innerPart i R)) := by
  have hle : (innerPart i R).map MulAut.conj ≤ R := by
    rintro _ ⟨n, hn, rfl⟩
    exact (mem_inf.mp hn).2
  have h1 := card_dvd_of_le hle
  rw [card_map_of_injective (conj_injective hZ)] at h1
  exact Odd.of_dvd_nat hRodd h1

variable {K : Subgroup S} (hKT : K ≤ oddFixed i)
  (hKN : ∀ k ∈ K, ∀ n ∈ innerPart i R, k * n = n * k)

include hRi hRconj hKT hKN in
theorem map_mul_mul_inv {r : MulAut S} (hr : r ∈ R) {a b : S} (ha : a ∈ K) (hb : b ∈ K) :
    r (a * b) * (a * b)⁻¹ = (r a * a⁻¹) * (r b * b⁻¹) := by
  have hc := hKN a ha _ (mul_inv_mem_innerPart hRi hRconj hr (hKT hb))
  rw [map_mul]
  calc r a * r b * (a * b)⁻¹ = r a * (a⁻¹ * (a * (r b * b⁻¹))) * a⁻¹ := by group
    _ = r a * (a⁻¹ * ((r b * b⁻¹) * a)) * a⁻¹ := by rw [hc]
    _ = (r a * a⁻¹) * (r b * b⁻¹) := by group

include hRi hRconj hKT hKN in
theorem fix_of_perfect [Finite S] (hZ : center S = ⊥) (hRodd : Odd (Nat.card R))
    (hperf : commutator K = ⊤) {r : MulAut S} (hr : r ∈ R) {k : S} (hk : k ∈ K) : r k = k := by
  set N := innerPart i R with hN
  let φ : K →* N :=
    { toFun := fun a => ⟨r a * (a : S)⁻¹, mul_inv_mem_innerPart hRi hRconj hr (hKT a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (map_mul_mul_inv hRi hRconj hKT hKN hr a.2 b.2) }
  have hsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard N (odd_card_innerPart hZ hRodd)
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hK : ∀ m : ℕ, derivedSeries K m = ⊤ := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
  have hmem : φ ⟨k, hk⟩ ∈ derivedSeries N n := by
    apply map_derivedSeries_le_derivedSeries φ n
    exact ⟨⟨k, hk⟩, by rw [hK n]; exact mem_top _, rfl⟩
  rw [hn, mem_bot] at hmem
  have h1 : r k * k⁻¹ = 1 := congrArg Subtype.val hmem
  rwa [mul_inv_eq_one] at h1

include hRi hRconj hKT hKN in
theorem fix_of_two_pow [Finite S] (hZ : center S = ⊥) (hRodd : Odd (Nat.card R))
    {r : MulAut S} (hr : r ∈ R) {k : S} (hk : k ∈ K) {a : ℕ} (hka : k ^ (2 ^ a) = 1) :
    r k = k := by
  have hpow : ∀ m : ℕ, r (k ^ m) * (k ^ m)⁻¹ = (r k * k⁻¹) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, map_mul_mul_inv hRi hRconj hKT hKN hr (pow_mem hk m) hk, ih, pow_succ]
  have hn := mul_inv_mem_innerPart hRi hRconj hr (hKT hk)
  have h1 : (r k * k⁻¹) ^ (2 ^ a) = 1 := by rw [← hpow, hka, map_one, inv_one, mul_one]
  have h2 : (r k * k⁻¹) ^ Nat.card (innerPart i R) = 1 := by
    have := pow_card_eq_one' (G := innerPart i R) (x := ⟨_, hn⟩)
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime (Nat.card (innerPart i R)) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr (odd_card_innerPart hZ hRodd))
  have h3 : orderOf (r k * k⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
  rw [orderOf_eq_one_iff, mul_inv_eq_one] at h3
  exact h3

omit hKT hKN in
include hRi hRconj in
theorem fix_of_isComponentOf [Finite S] (hZ : center S = ⊥) (hRodd : Odd (Nat.card R))
    {r : MulAut S} (hr : r ∈ R) (hK : GorensteinWalter.IsComponentOf K (oddFixed i)) {k : S}
    (hk : k ∈ K) : r k = k := by
  set T := oddFixed i with hT
  set N := innerPart i R with hN
  have hNT : N ≤ T := inf_le_left
  have hsolv : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard N (odd_card_innerPart hZ hRodd)
  have hTN : T ≤ normalizer (N : Set S) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro n
    refine ⟨fun hn => conj_mem_innerPart hRconj ht hn, fun hn => ?_⟩
    have := conj_mem_innerPart hRconj (inv_mem ht) hn
    simpa [mul_assoc] using this
  have hE : GorensteinWalter.componentLayerOf T ≤ normalizer (N : Set S) :=
    (GorensteinWalter.componentLayerOf_isNormalIn T).1.trans hTN
  have hc := GorensteinWalter.componentLayerOf_centralizes_solvable_of_le_normalizer T N hNT hsolv
    hE
  have hKE : K ≤ GorensteinWalter.componentLayerOf T := le_sSup hK
  have hKN' : ∀ a ∈ K, ∀ n ∈ N, a * n = n * a := by
    intro a ha n hn
    have h1 : ⁅a, n⁆ ∈ ⁅GorensteinWalter.componentLayerOf T, N⁆ :=
      commutator_mem_commutator (hKE ha) hn
    rw [hc, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  exact fix_of_perfect hRi hRconj hK.1 hKN' hZ hRodd hK.2.2.2.1 hr hk

omit hKT hKN in
include hRi hRconj in
theorem fix_of_normal_two [Finite S] (hZ : center S = ⊥) (hRodd : Odd (Nat.card R))
    {r : MulAut S} (hr : r ∈ R) {Q : Subgroup S} (hQT : Q ≤ oddFixed i)
    (hQn : ∀ t ∈ oddFixed i, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hQ2 : IsPGroup 2 Q) {q : S}
    (hq : q ∈ Q) : r q = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQN : ∀ a ∈ Q, ∀ n ∈ innerPart i R, a * n = n * a := by
    intro a ha n hn
    have hnT : n ∈ oddFixed i := (mem_inf.mp hn).1
    have h1 : n * a * n⁻¹ * a⁻¹ ∈ Q := mul_mem (hQn n hnT a ha) (inv_mem ha)
    have h2 : n * a * n⁻¹ * a⁻¹ ∈ innerPart i R := by
      have := conj_mem_innerPart hRconj (hQT ha) (inv_mem hn)
      rw [show n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) by group]
      exact mul_mem hn this
    obtain ⟨m, hm⟩ := hQ2 ⟨_, h1⟩
    have h3 : (n * a * n⁻¹ * a⁻¹) ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h4 : (n * a * n⁻¹ * a⁻¹) ^ Nat.card (innerPart i R) = 1 := by
      have := pow_card_eq_one' (G := innerPart i R) (x := ⟨_, h2⟩)
      exact congrArg Subtype.val this
    have hcop : Nat.Coprime (Nat.card (innerPart i R)) (2 ^ m) :=
      Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr (odd_card_innerPart hZ hRodd))
    have h5 : orderOf (n * a * n⁻¹ * a⁻¹) = 1 := Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h4) (orderOf_dvd_of_pow_eq_one h3)
    rw [orderOf_eq_one_iff] at h5
    calc a * n = (n * a * n⁻¹ * a⁻¹)⁻¹ * n * a := by group
      _ = n * a := by rw [h5, inv_one, one_mul]
  obtain ⟨m, hm⟩ := hQ2 ⟨q, hq⟩
  have hqm : q ^ (2 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  exact fix_of_two_pow hRi hRconj hQT hQN hZ hRodd hr hq hqm

end CFSG.ComponentClassification.Foote5.OddLieCore
