module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step212Prod
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2NatModule
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Z
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import Certificates.Data.A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.Quasithin
open scoped commutatorElement

namespace Sec2

variable {G : Type} [Group G]

theorem le_upperCentralSeries_of_normal {H : Type*} [Group H] [Finite H] {p : ℕ}
    [hp : Fact p.Prime] (hH : IsPGroup p H) (k : ℕ) (N : Subgroup H) [N.Normal]
    (hN : Nat.card N ∣ p ^ k) : N ≤ Subgroup.upperCentralSeries H k := by
  have hnil : Group.IsNilpotent H := hH.isNilpotent
  have hfix : ∀ M : Subgroup H, ⁅M, ⊤⁆ = M → M = ⊥ := by
    intro M hM
    obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries).mp hnil
    have h : ∀ j, M ≤ (⊤ : Subgroup H).lowerCentralSeries j := by
      intro j
      induction j with
      | zero =>
        rw [Subgroup.lowerCentralSeries_zero]
        exact le_top
      | succ j ih =>
        rw [Subgroup.lowerCentralSeries_succ, ← hM]
        exact Subgroup.commutator_mono ih le_rfl
    exact le_bot_iff.mp (hn ▸ h n)
  induction k generalizing N with
  | zero =>
    rw [pow_zero, Nat.dvd_one, Subgroup.card_eq_one] at hN
    rw [hN]
    exact bot_le
  | succ k ih =>
    have hCN : ⁅N, ⊤⁆ ≤ N := Subgroup.commutator_le_left N ⊤
    have hCk : Nat.card (⁅N, ⊤⁆ : Subgroup H) ∣ p ^ k := by
      by_cases hN1 : N = ⊥
      · rw [hN1, Subgroup.commutator_bot_left, card_bot]
        exact one_dvd _
      have hlt : Nat.card (⁅N, ⊤⁆ : Subgroup H) < Nat.card N :=
        lt_of_le_of_ne (Subgroup.card_le_of_le hCN) fun h =>
          hN1 (hfix N (Subgroup.eq_of_le_of_card_ge hCN h.ge))
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp.out).mp ((Subgroup.card_dvd_of_le hCN).trans hN)
      obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).mp hN
      rw [hi, hj'] at hlt
      have hij : i < j := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
      rw [hi]
      exact pow_dvd_pow p (by omega)
    have : (⁅N, ⊤⁆ : Subgroup H).Normal := Subgroup.commutator_normal N ⊤
    have h1 := ih ⁅N, ⊤⁆ hCk
    intro x hx
    rw [Subgroup.mem_upperCentralSeries_succ_iff]
    intro y
    exact h1 (Subgroup.commutator_mem_commutator hx (mem_top y))

theorem eq_one_of_pow_three_of_pow_two_pow {M : Type*} [Monoid M] {x : M} {m : ℕ}
    (h3 : x ^ 3 = 1) (h2 : x ^ 2 ^ m = 1) : x = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact orderOf_eq_one_iff.mp h
  · have h2' := orderOf_dvd_of_pow_eq_one h2
    rw [h] at h2'
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2') (by norm_num)

theorem mem_of_mul_zpow_of_pow_eq_one {T : Subgroup G} (hT : IsPGroup 2 T) {y : G}
    (hyT : y ∈ normalizer (T : Set G)) (hy3 : y ^ 3 = 1) {t : G} (ht : t ∈ T) (m : ℤ) {a : ℕ}
    (h : (t * y ^ m) ^ 2 ^ a = 1) : t * y ^ m ∈ T := by
  have hym : y ^ m ∈ normalizer (T : Set G) := zpow_mem hyT m
  have hpow : ∀ N : ℕ, ∃ t' ∈ T, (t * y ^ m) ^ N = t' * (y ^ m) ^ N := by
    intro N
    induction N with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ N ih =>
      obtain ⟨t', ht', e⟩ := ih
      refine ⟨t' * ((y ^ m) ^ N * t * ((y ^ m) ^ N)⁻¹), mul_mem ht' ?_, ?_⟩
      · exact (mem_normalizer_iff.mp (pow_mem hym N) t).mp ht
      · rw [pow_succ, e]
        group
  obtain ⟨t', ht', e⟩ := hpow (2 ^ a)
  rw [h] at e
  have hx3 : (y ^ m) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have h1 : (y ^ m) ^ 2 ^ a ∈ T := by
    rw [eq_inv_of_mul_eq_one_right e.symm]
    exact inv_mem ht'
  obtain ⟨b, hb⟩ := hT ⟨_, h1⟩
  have h2 : ((y ^ m) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h3 : ((y ^ m) ^ 2 ^ a) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow]
  have h4 := eq_one_of_pow_three_of_pow_two_pow hx3 (eq_one_of_pow_three_of_pow_two_pow h3 h2)
  rwa [h4, mul_one]

theorem theta_inv {θ : (Fin 6 → ZMod 2) → G}
    (hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → θ (v + w) = θ v * θ w)
    (hker : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → (θ v = 1 ↔ v = 0 ∨ v = fun _ => 1))
    {u : Fin 6 → ZMod 2} (hu : ∑ i, u i = 0) : (θ u)⁻¹ = θ u := by
  have h0 : θ 0 = 1 := (hker 0 (by simp)).mpr (Or.inl rfl)
  have h := hadd u u hu hu
  rw [show u + u = 0 from funext fun i => CharTwo.add_self_eq_zero (u i), h0] at h
  exact inv_eq_of_mul_eq_one_left h.symm

theorem theta_comm {K : Subgroup G} {φ : ↥K →* alternatingGroup (Fin 6)}
    {θ : (Fin 6 → ZMod 2) → G}
    (hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → θ (v + w) = θ v * θ w)
    (hker : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → (θ v = 1 ↔ v = 0 ∨ v = fun _ => 1))
    (hconj : ∀ k : ↥K, ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
      (k : G) * θ v * (k : G)⁻¹ =
        θ (fun i => v (((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))⁻¹ i)))
    (k : ↥K) {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    θ v * (k : G) * (θ v)⁻¹ * (k : G)⁻¹ =
      θ (v + Sec2Nat.act ((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) v) := by
  rw [theta_inv hadd hker hv, hadd v _ hv ((Sec2Nat.sum_act _ v).trans hv)]
  change _ = θ v * θ (fun i => v (((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))⁻¹ i))
  rw [← hconj k v hv]
  group

theorem theta_mem_upperCentralSeries_iff {K T : Subgroup G} (hTK : T ≤ K)
    {φ : ↥K →* alternatingGroup (Fin 6)} {θ : (Fin 6 → ZMod 2) → G}
    (hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → θ (v + w) = θ v * θ w)
    (hker : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → (θ v = 1 ↔ v = 0 ∨ v = fun _ => 1))
    (hconj : ∀ k : ↥K, ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
      (k : G) * θ v * (k : G)⁻¹ =
        θ (fun i => v (((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))⁻¹ i)))
    (hθT : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → θ v ∈ T)
    {ι : Type*} (D : ι → Equiv.Perm (Fin 6))
    (hD : ∀ t : ↥K, (t : G) ∈ T →
      ∃ i, ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = D i)
    (hD' : ∀ i, ∃ t : ↥K, (t : G) ∈ T ∧
      ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = D i)
    (k : ℕ) {v : Fin 6 → ZMod 2} (hv : ∑ i, v i = 0) :
    θ v ∈ (Subgroup.upperCentralSeries ↥T k).map T.subtype ↔ v ∈ Sec2Nat.lay D k := by
  induction k generalizing v with
  | zero =>
    rw [Subgroup.upperCentralSeries_zero, Subgroup.map_bot, mem_bot, Sec2Nat.mem_lay_zero]
    exact hker v hv
  | succ k ih =>
    change T.subtype ⟨θ v, hθT v hv⟩ ∈ _ ↔ _
    rw [Subgroup.mem_map_iff_mem T.subtype_injective, Subgroup.mem_upperCentralSeries_succ_iff,
      Sec2Nat.mem_lay_succ]
    constructor
    · intro h i
      obtain ⟨t, htT, hti⟩ := hD' i
      have h1 := (Subgroup.mem_map_iff_mem T.subtype_injective).mpr (h ⟨t, htT⟩)
      have e : T.subtype ⁅(⟨θ v, hθT v hv⟩ : ↥T), ⟨(t : G), htT⟩⁆ =
          θ (v + Sec2Nat.act (D i) v) := by
        rw [← hti, ← theta_comm hadd hker hconj t hv]
        simp [commutatorElement_def]
      rw [e, ih (Sec2Nat.sum_add_act _ v)] at h1
      exact h1
    · intro h y
      obtain ⟨i, hi⟩ := hD ⟨y, hTK y.2⟩ y.2
      rw [← Subgroup.mem_map_iff_mem T.subtype_injective]
      have e : T.subtype ⁅(⟨θ v, hθT v hv⟩ : ↥T), y⁆ = θ (v + Sec2Nat.act (D i) v) := by
        rw [← hi, ← theta_comm hadd hker hconj ⟨y, hTK y.2⟩ hv]
        simp [commutatorElement_def]
      rw [e, ih (Sec2Nat.sum_add_act _ v)]
      exact h i

theorem exists_conj_layers [Finite G] {K T : Subgroup G} (hTK : T ≤ K) (hTsyl : IsSylowOf 2 T K)
    {φ : ↥K →* alternatingGroup (Fin 6)} (hφs : Function.Surjective φ)
    {θ : (Fin 6 → ZMod 2) → G}
    (hadd : ∀ v w : Fin 6 → ZMod 2, ∑ i, v i = 0 → ∑ i, w i = 0 → θ (v + w) = θ v * θ w)
    (hker : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → (θ v = 1 ↔ v = 0 ∨ v = fun _ => 1))
    (hconj : ∀ k : ↥K, ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 →
      (k : G) * θ v * (k : G)⁻¹ =
        θ (fun i => v (((φ k : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))⁻¹ i)))
    (hθT : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → θ v ∈ T) :
    ∃ γ : alternatingGroup (Fin 6),
      (∀ t : ↥K, (t : G) ∈ T → ∃ i, ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        (γ : Equiv.Perm (Fin 6)) * Sec2Nat.d0 i * (γ : Equiv.Perm (Fin 6))⁻¹) ∧
      (∀ i, ∃ t : ↥K, (t : G) ∈ T ∧ ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        (γ : Equiv.Perm (Fin 6)) * Sec2Nat.d0 i * (γ : Equiv.Perm (Fin 6))⁻¹) ∧
      ∀ (k : ℕ) {v : Fin 6 → ZMod 2}, ∑ i, v i = 0 →
        (θ v ∈ (Subgroup.upperCentralSeries ↥T k).map T.subtype ↔
          Sec2Nat.act (γ : Equiv.Perm (Fin 6))⁻¹ v ∈ Sec2Nat.lay Sec2Nat.d0 k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ST, hST⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have hmemS : ∀ x : alternatingGroup (Fin 6),
      x ∈ ((ST.mapSurjective hφs : Sylow 2 (alternatingGroup (Fin 6))) :
        Subgroup (alternatingGroup (Fin 6))) ↔ ∃ t : ↥K, (t : G) ∈ T ∧ φ t = x := by
    intro x
    rw [Sylow.coe_mapSurjective, hST]
    exact ⟨fun ⟨t, ht, htx⟩ => ⟨t, ht, htx⟩, fun ⟨t, ht, htx⟩ => ⟨t, ht, htx⟩⟩
  obtain ⟨γ, hγ⟩ := Sec2Nat.exists_conj_D0 (ST.mapSurjective hφs)
  have hf : ∀ t : ↥K, (t : G) ∈ T → ∃ i,
      ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        (γ : Equiv.Perm (Fin 6)) * Sec2Nat.d0 i * (γ : Equiv.Perm (Fin 6))⁻¹ := by
    intro t ht
    obtain ⟨i, hi⟩ := Sec2Nat.mem_D0.mp ((hγ (φ t)).mp ((hmemS _).mpr ⟨t, ht, rfl⟩))
    refine ⟨i, ?_⟩
    rw [hi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hf' : ∀ i, ∃ t : ↥K, (t : G) ∈ T ∧
      ((φ t : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        (γ : Equiv.Perm (Fin 6)) * Sec2Nat.d0 i * (γ : Equiv.Perm (Fin 6))⁻¹ := by
    intro i
    have hx : γ * ⟨Sec2Nat.d0 i, Sec2Nat.d0_mem i⟩ * γ⁻¹ ∈
        ((ST.mapSurjective hφs : Sylow 2 (alternatingGroup (Fin 6))) :
          Subgroup (alternatingGroup (Fin 6))) := by
      rw [hγ]
      exact Sec2Nat.mem_D0.mpr ⟨i, by simp [mul_assoc]⟩
    obtain ⟨t, ht, htx⟩ := (hmemS _).mp hx
    exact ⟨t, ht, by rw [htx]; simp⟩
  exact ⟨γ, hf, hf', fun k v hv =>
    (theta_mem_upperCentralSeries_iff hTK hadd hker hconj hθT _ hf hf' k hv).trans
      (Sec2Nat.mem_lay_conj Sec2Nat.d0 _ k v)⟩

theorem vec_eq_of_add_eq_zero {a b : Fin 6 → ZMod 2} (h : a + b = 0) : a = b := by
  funext j
  have h1 := congrFun h j
  simp only [Pi.add_apply, Pi.zero_apply] at h1
  generalize a j = x at h1 ⊢
  generalize b j = y at h1 ⊢
  revert x y
  decide

theorem vec_eq_of_add_eq_one {a b : Fin 6 → ZMod 2} (h : a + b = fun _ => 1) : a = b + 1 := by
  funext j
  have h1 := congrFun h j
  simp only [Pi.add_apply, Pi.one_apply] at h1 ⊢
  generalize a j = x at h1 ⊢
  generalize b j = y at h1 ⊢
  revert x y
  decide

theorem eq_one_of_forall_commute_alternatingGroup_six {σ : alternatingGroup (Fin 6)}
    (h : ∀ τ, σ * τ = τ * σ) : σ = 1 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hσ : σ ∈ center (alternatingGroup (Fin 6)) := mem_center_iff.mpr fun τ => (h τ).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (alternatingGroup (Fin 6))) with hc | hc
  · rwa [hc, mem_bot] at hσ
  · exfalso
    let a : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    let b : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    have ha : a ∈ center (alternatingGroup (Fin 6)) := hc ▸ mem_top a
    exact absurd (mem_center_iff.mp ha b) (by decide)

theorem mem_normalizer_map_conj {Q : Subgroup G} {g n : G}
    (h : n⁻¹ * g * n ∈ normalizer (Q : Set G)) :
    g ∈ normalizer ((Q.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(n⁻¹ * g * n) * q * (n⁻¹ * g * n)⁻¹, (mem_normalizer_iff.mp h q).mp hq, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨q, hq, hqx⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hqx
    refine ⟨(n⁻¹ * g * n)⁻¹ * q * (n⁻¹ * g * n), ?_, ?_⟩
    · have := (mem_normalizer_iff.mp (inv_mem h) q).mp hq
      rwa [inv_inv] at this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have e : n * ((n⁻¹ * g * n)⁻¹ * q * (n⁻¹ * g * n)) * n⁻¹ = g⁻¹ * (n * q * n⁻¹) * g := by
        group
      rw [e, hqx]
      group

variable [Finite G]

theorem exists_mem_sec2P_not_mem_sec2S (h26 : Step26) {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (hS : Sec2Setting G A R g E F) :
    ∃ x ∈ sec2P F, x ∉ sec2S A R E F := by
  by_contra hall
  push Not at hall
  obtain ⟨-, hSH, ⟨φ, hφs, hφker⟩, -, -, -, -, hHS, -⟩ := h26 G A R g E F hS
  let a : alternatingGroup (Fin 5) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  obtain ⟨h, hh⟩ := hφs a
  have hPS : sec2P E ≤ normalizer (sec2S A R E F : Set G) := le_sup_left.trans hHS
  have hHPS : sec2H E F ≤ sec2P E ⊔ sec2S A R E F :=
    sup_le le_sup_left fun x hx => mem_sup_right (hall x hx)
  have hhPS : (h : G) ∈ ((sec2P E ⊔ sec2S A R E F : Subgroup G) : Set G) := hHPS h.2
  rw [coe_mul_of_left_le_normalizer_right _ _ hPS] at hhPS
  obtain ⟨p, hp, s, hs, hps⟩ := hhPS
  have hpH : p ∈ sec2H E F := mem_sup_left hp
  have hsH : s ∈ sec2H E F := hSH hs
  have hφs1 : φ ⟨s, hsH⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hφker]
    exact hs
  have hφh : φ h = φ ⟨p, hpH⟩ := by
    have e : h = ⟨p, hpH⟩ * ⟨s, hsH⟩ := Subtype.ext hps.symm
    rw [e, map_mul, hφs1, mul_one]
  obtain ⟨m, hm⟩ := isPGroup_sec2P E ⟨p, hp⟩
  have h2 : a ^ 2 ^ m = 1 := by
    rw [← hh, hφh, ← map_pow]
    have e : (⟨p, hpH⟩ : ↥(sec2H E F)) ^ 2 ^ m = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [e, map_one]
  exact absurd (eq_one_of_pow_three_of_pow_two_pow (by decide) h2) (by decide)

theorem mem_normalizer_E_of_sec2UY (h23 : Step23) (h26 : Step26) {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (hS : Sec2Setting G A R g E F)
    (hPZ : sec2P E ≤ normalizer (sec2Z A E F : Set G)) {u y : G} (huy : Sec2UY A R E F u y) :
    y ∈ normalizer (E : Set G) := by
  have hF := hS.frame
  obtain ⟨x, hx, hxS⟩ := exists_mem_sec2P_not_mem_sec2S h26 hS
  obtain ⟨hEx, -, -, -, -, -, -, hEH, -, -, -⟩ := h23 G A R g E F hS x hx hxS
  have hyH : y ∈ sec2H E F := huy.2.2.2.1.1.1
  have hyR : y ∈ normalizer (R : Set G) := huy.2.2.2.1.1.2
  have hmem : rightConjugate E y ∈ conjSet E (sec2H E F) := ⟨y, hyH, rfl⟩
  rw [hEH] at hmem
  rcases hmem with h | ⟨p, hp, hpe⟩
  · exact (rightConjugate_eq_self_iff E y).mp h
  · exfalso
    have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
    have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hS.odd
    have hPE : sec2P E ≤ normalizer (E : Set G) := sec2P_le E
    have hRZ : R ≤ sec2Z A E F := by
      intro r hr
      have h1 : r ∈ rightConjugate E y := by
        rw [mem_rightConjugate_iff]
        exact hF.R_le_E ((mem_normalizer_iff.mp hyR r).mp hr)
      rw [hpe, rightConjugate_mul, mem_rightConjugate_iff] at h1
      have h2 : p * r * p⁻¹ ∈ rightConjugate E x ⊓ E := by
        refine ⟨(mem_rightConjugate_iff _ _ _).mpr ?_,
          (mem_normalizer_iff.mp (hPE hp) r).mp (hF.R_le_E hr)⟩
        simpa [mul_assoc] using h1
      rw [hEx] at h2
      have h3 := (mem_normalizer_iff.mp (hPZ (inv_mem hp)) _).mp h2
      simpa [mul_assoc] using h3
    have hR1 : R = ⊥ := by
      rw [eq_bot_iff, ← hRA1]
      exact fun r hr => ⟨hr, (inf_le_left : sec2Z A E F ≤ A) (hRZ hr)⟩
    have := hF.cardR
    rw [hR1, card_bot] at this
    norm_num at this

end Sec2

namespace Sec2Q

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F T₀ Q : Subgroup G}
  {u y z : G}

theorem comm_mem_zpowers (hQ : Sec2Q G A R g E F T₀ Q u y z) {a b : G} (ha : a ∈ Q)
    (hb : b ∈ Q) : a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  obtain ⟨-, hcomm, -, -⟩ := hQ.q8.1
  have h1 : ⁅(⟨a, ha⟩ : ↥Q), ⟨b, hb⟩⁆ ∈ Subgroup.center ↥Q := by
    rw [← hcomm, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _)
  rw [← hQ.centerIn_Q, Sec2.centerIn_eq_map]
  exact ⟨_, h1, by simp [commutatorElement_def]⟩

end Sec2Q

open Sec2 in

theorem step215_of
    (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h21 : Step21) (h211 : Step211)
    (h211N : Step211Natural) (h212 : Step212) (h23 : Step23) (h26 : Step26) : Step215 := by
  intro G _ _ A R g E F T₀ Q u y z hQ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hQ.data.setting
  have hF := hS.frame
  have huy := hQ.data.uy
  obtain ⟨hPOK, hidx, -, hyPO, hyfix, -, -, -, -⟩ := h211 G A R g E F hS
  obtain ⟨φ, θ, hφs, hφker, hθadd, hθV, hθsurj, hθker, hθconj⟩ := h211N G A R g E F hS
  obtain ⟨hT₀syl, hPST, -, -, -, hT₀P⟩ := (h212 G A R g E F hS).2 T₀ hQ.data.le hQ.data.sylow
  have hKP : sec2K E ≤ normalizer (sec2P E : Set G) := sec2K_le_normalizer E
  have hP2 : IsPGroup 2 (sec2P E) := isPGroup_sec2P E
  have hPK : sec2P E ≤ sec2K E := le_sup_left.trans hPOK
  have hKO := AS76b.le_normalizer_oddCoreIn (sec2K E)
  have hKPO := NXKernel.le_normalizer_sup hKP hKO
  have hPO := sec2P_le_centralizer_oddCoreIn hPK
  have hPOC := sup_oddCoreIn_le_ker hPOK hφs hφker
  have hC3 := relIndex_sup_oddCoreIn hPOK hidx hφs hφker
  have hφker' : ∀ k : ↥(sec2K E), φ k = 1 ↔
      (k : G) ∈ sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) := fun k => by
    rw [← MonoidHom.mem_ker, hφker, mem_subgroupOf]
  have hTK : sec2T E T₀ ≤ sec2K E := inf_le_right
  have hTsyl : IsSylowOf 2 (sec2T E T₀) (sec2K E) :=
    (hT₀syl.of_le hT₀P le_top).inf_of_le_normalizer hKP fun n hn => mem_normalizer_oUpperTwo hn
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 6) (by rw [hF.cardE]; norm_num)
  have hEP : E ≤ sec2P E := le_sec2P hE2 le_normalizer le_rfl
  have hPT : sec2P E ≤ sec2T E T₀ := le_sup_left.trans hPST
  have hVT : E ⊓ A ≤ sec2T E T₀ := inf_le_left.trans (hEP.trans hPT)
  have hRA : R ≤ centralizer (A : Set G) := hF.sylowR.le
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hF.sylowR.isPGroup hS.odd
  have hV16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have hθT : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → θ v ∈ sec2T E T₀ :=
    fun v hv => hVT (hθV v hv)
  have hKV : sec2K E ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    have h1 : ∀ k : ↥(sec2K E), ∀ a ∈ E ⊓ A, (k : G) * a * (k : G)⁻¹ ∈ E ⊓ A := by
      intro k a ha
      obtain ⟨v, hv, rfl⟩ := hθsurj a ha
      rw [hθconj k v hv]
      exact hθV _ ((Sec2Nat.sum_act _ v).trans hv)
    intro k hk
    rw [mem_normalizer_iff]
    intro a
    refine ⟨h1 ⟨k, hk⟩ a, fun ha => ?_⟩
    have := h1 (⟨k, hk⟩⁻¹) _ ha
    simpa [mul_assoc] using this
  have hTQ : sec2T E T₀ ≤ normalizer (Q : Set G) := hQ.T_le_normalizer
  have hT2 : IsPGroup 2 (sec2T E T₀) := hQ.isPGroup_T₀.to_le inf_le_left
  have hVQ8 : Nat.card (E ⊓ A ⊓ Q : Subgroup G) = 8 := by
    have h1 := Subgroup.relIndex_mul_card (E ⊓ A ⊓ Q) (E ⊓ A)
    rw [hQ.index, inf_eq_left.mpr inf_le_left, hV16] at h1
    omega
  have hVQZ : E ⊓ A ⊓ Q ≤
      (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype := by
    have hle : E ⊓ A ⊓ Q ≤ sec2T E T₀ := inf_le_left.trans hVT
    have : ((E ⊓ A ⊓ Q).subgroupOf (sec2T E T₀)).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).mpr
        fun t ht => mem_normalizer_inf (hKV (hTK ht)) (hTQ ht)
    have hcard : Nat.card ((E ⊓ A ⊓ Q).subgroupOf (sec2T E T₀)) ∣ 2 ^ 3 := by
      rw [NXKernel.card_subgroupOf, inf_eq_left.mpr hle, hVQ8]
      norm_num
    have h1 := le_upperCentralSeries_of_normal hT2 3 _ hcard
    intro x hx
    exact ⟨⟨x, hle hx⟩, h1 (show (⟨x, hle hx⟩ : ↥(sec2T E T₀)) ∈
      (E ⊓ A ⊓ Q).subgroupOf (sec2T E T₀) from hx), rfl⟩
  obtain ⟨γ, hf, hf', hlay⟩ := exists_conj_layers hTK hTsyl hφs hθadd hθker hθconj hθT
  set g' : Equiv.Perm (Fin 6) := (γ : Equiv.Perm (Fin 6)) with hg'
  have hv₁ : ∑ i, Sec2Nat.act g' Sec2Nat.w1 i = 0 := (Sec2Nat.sum_act g' _).trans Sec2Nat.sum_w1
  have hθv₁ : θ (Sec2Nat.act g' Sec2Nat.w1) ∉
      (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype := by
    rw [hlay 3 hv₁, Sec2Nat.act_inv_act]
    exact Sec2Nat.w1_not_mem_lay_three
  have h215ii : E ⊓ A ⊓ Q =
      (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓ (E ⊓ A) := by
    have hle : E ⊓ A ⊓ Q ≤
        (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓ (E ⊓ A) :=
      le_inf hVQZ inf_le_left
    have hWV : (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓ (E ⊓ A) ≤
        E ⊓ A := inf_le_right
    have hdvd := Subgroup.card_dvd_of_le hWV
    have hge := Subgroup.card_le_of_le hle
    rw [hV16] at hdvd
    rw [hVQ8] at hge
    have hne : Nat.card ((Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓
        (E ⊓ A) : Subgroup G) ≠ 16 := by
      intro h16
      have hWeq := Subgroup.eq_of_le_of_card_ge hWV (by rw [hV16, h16])
      apply hθv₁
      have h1 : θ (Sec2Nat.act g' Sec2Nat.w1) ∈
          (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓ (E ⊓ A) := by
        rw [hWeq]
        exact hθV _ hv₁
      exact h1.1
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show _ ∣ 2 ^ 4 from hdvd)
    have h8 : Nat.card ((Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype ⊓
        (E ⊓ A) : Subgroup G) = 8 := by
      rw [hci] at hge hne ⊢
      interval_cases i
      · norm_num at hge
      · norm_num at hge
      · norm_num at hge
      · rfl
      · exact absurd rfl hne
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hVQ8, h8])
  have hZV : sec2Z A E F ≤ E ⊓ A := by
    rw [hF.sec2Z_eq]
    exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hzV : z ∈ E ⊓ A := hZV (hQ.z_mem_Z h212)
  have hPV : sec2P E ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    fun p hp => (hPOC (mem_sup_left hp)).2
  have hPZ : sec2P E ≤ normalizer (sec2Z A E F : Set G) := fun p hp =>
    centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun w hw => mem_centralizer_iff.mp (hPV hp) w (hZV hw))
  have hyE := mem_normalizer_E_of_sec2UY h23 h26 hS hPZ huy
  have hy3 : orderOf y = 3 := huy.2.2.2.2
  have hyK : y ∈ sec2K E :=
    subset_closure ⟨normalizer_le_normalizer_sec2P E hyE, by rw [hy3]; decide⟩
  obtain ⟨I, hPI, hIO, hIOK, hOI⟩ := step212Prod_of h4 h34 hE16 h21 h211 h212 hS
  have hIC : I ≤ centralizer (AS76b.oddCoreIn (sec2K E) : Set G) :=
    Subgroup.le_centralizer_iff.mp hOI
  have hIK : I ≤ sec2K E := le_sup_left.trans hIOK.le
  have hOodd := AS76b.odd_card_oddCoreIn (sec2K E)
  have hdec : ∀ k ∈ sec2K E, ∃ i ∈ I, ∃ o ∈ AS76b.oddCoreIn (sec2K E), k = i * o ∧
      i * o = o * i := fun k hk =>
    NXKernel.exists_mul_of_mem_sup hIC (by rw [hIOK]; exact hk)
  have hcommIO : ∀ i ∈ I, ∀ o ∈ AS76b.oddCoreIn (sec2K E), i * o = o * i :=
    fun i hi o ho => (mem_centralizer_iff.mp (hIC hi) o ho).symm
  have hPOI : ∀ x ∈ sec2P E ⊔ AS76b.oddCoreIn (sec2K E), x ∈ I → x ∈ sec2P E := by
    intro x hx hxI
    obtain ⟨p, hp, o, ho, rfl, -⟩ := NXKernel.exists_mul_of_mem_sup hPO hx
    have hoI : o ∈ I := by
      have := I.mul_mem (I.inv_mem (hPI hp)) hxI
      rwa [inv_mul_cancel_left] at this
    have ho1 : o ∈ I ⊓ AS76b.oddCoreIn (sec2K E) := ⟨hoI, ho⟩
    rw [hIO, mem_bot] at ho1
    rw [ho1, mul_one]
    exact hp
  have hTI : sec2T E T₀ ≤ I := by
    intro t ht
    obtain ⟨i, hi, o, ho, rfl, hio⟩ := hdec t (hTK ht)
    obtain ⟨a, ha⟩ := hT2 ⟨_, ht⟩
    have h1 : (i * o) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    rw [NXKernel.eq_one_of_mul_pow hIO hOodd hi ho hio h1, mul_one]
    exact hi
  have hQI : Q ≤ I := hQ.le.trans hTI
  obtain ⟨yI, hyI, yO, hyO, hyeq, hycomm⟩ := hdec y hyK
  have hyIK : yI ∈ sec2K E := hIK hyI
  have hyIy : yI = y * yO⁻¹ := by rw [hyeq, mul_inv_cancel_right]
  have hyIcomm : ∀ k ∈ I, k * yI * k⁻¹ * yI⁻¹ ∈ sec2P E := by
    intro k hk
    have h1 := hyPO u y huy k⁻¹ (hIK (I.inv_mem hk))
    have hw : yI⁻¹ * k * yI ∈ I := I.mul_mem (I.mul_mem (I.inv_mem hyI) hk) hyI
    have hcw : yO⁻¹ * (yI⁻¹ * k * yI) * yO = yI⁻¹ * k * yI := by
      rw [mul_assoc, hcommIO _ hw yO hyO, ← mul_assoc, inv_mul_cancel, one_mul]
    have e : y⁻¹ * k⁻¹⁻¹ * y * k⁻¹ = yI⁻¹ * k * yI * k⁻¹ := by
      rw [hyeq, inv_inv, ← hcw]
      group
    rw [e] at h1
    have h4 : yI⁻¹ * k * yI * k⁻¹ ∈ sec2P E := hPOI _ h1 (I.mul_mem hw (I.inv_mem hk))
    have h5 := (mem_normalizer_iff.mp (hKP hyIK) _).mp h4
    have e2 : yI * (yI⁻¹ * k * yI * k⁻¹) * yI⁻¹ = k * yI * k⁻¹ * yI⁻¹ := by group
    rwa [e2] at h5
  have hyI3 : yI ^ 3 = 1 := by
    have h1 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    rw [hyeq, Commute.mul_pow hycomm 3] at h1
    have h2 : yI ^ 3 = (yO ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : yI ^ 3 ∈ I ⊓ AS76b.oddCoreIn (sec2K E) :=
      mem_inf.mpr ⟨pow_mem hyI 3, by rw [h2]; exact inv_mem (pow_mem hyO 3)⟩
    rwa [hIO, mem_bot] at h3
  have hyI1 : yI ≠ 1 := by
    intro h1
    have hyO' : y = yO := by rw [hyeq, h1, one_mul]
    obtain ⟨r, hr, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
      by_contra hc
      push Not at hc
      have hR : R = ⊥ := eq_bot_iff.mpr fun r hr => (mem_bot).mpr (hc r hr)
      have := hF.cardR
      rw [hR, card_bot] at this
      norm_num at this
    apply hyfix u y huy r hr hr1
    have hrI : r ∈ I := hPI (hEP (hF.R_le_E hr))
    have h2 : r * y = y * r := by rw [hyO']; exact hcommIO r hrI yO hyO
    rw [mul_assoc, h2, inv_mul_cancel_left]
  have hyIo : orderOf yI = 3 := orderOf_eq_prime hyI3 hyI1
  have hyIP : yI ∉ sec2P E := fun h => hyI1 (by
    obtain ⟨a, ha⟩ := hP2 ⟨yI, h⟩
    exact eq_one_of_pow_three_of_pow_two_pow hyI3 (by simpa using congrArg Subtype.val ha))
  have hPyI : sec2P E ⊓ zpowers yI = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxP, hxy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hxy
    obtain ⟨a, ha⟩ := hP2 ⟨_, hxP⟩
    refine (mem_bot).mpr (eq_one_of_pow_three_of_pow_two_pow ?_
      (by simpa using congrArg Subtype.val ha))
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyI3, one_zpow]
  have hyOQ : yO ∈ normalizer (Q : Set G) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun q hq => hcommIO q (hQI hq) yO hyO)
  have hyIQ : yI ∈ normalizer (Q : Set G) := by
    rw [hyIy]
    exact mul_mem hQ.mem_normalizer (inv_mem hyOQ)
  have hφy : φ ⟨y, hyK⟩ = 1 := by
    apply eq_one_of_forall_commute_alternatingGroup_six
    intro τ
    obtain ⟨k, rfl⟩ := hφs τ
    have h1 := hyPO u y huy k k.2
    have h2 : (⟨y, hyK⟩⁻¹ * k⁻¹ * ⟨y, hyK⟩ * k : ↥(sec2K E)) ∈ φ.ker := by
      rw [hφker, mem_subgroupOf]
      simpa using hPOC h1
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc φ ⟨y, hyK⟩ * φ k
        = φ k * φ ⟨y, hyK⟩ * ((φ ⟨y, hyK⟩)⁻¹ * (φ k)⁻¹ * φ ⟨y, hyK⟩ * φ k) := by group
      _ = φ k * φ ⟨y, hyK⟩ := by rw [h2, mul_one]
  have hyC : y ∈ sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
    (hφker' ⟨y, hyK⟩).mp hφy
  have hyOC := hPOC (mem_sup_right hyO)
  have hyIC : yI ∈ sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    rw [hyIy]
    exact mul_mem hyC (inv_mem hyOC)
  have hyPO' : y ∉ sec2P E ⊔ AS76b.oddCoreIn (sec2K E) := by
    intro h
    obtain ⟨p, hp, o, ho, hpo, -⟩ := NXKernel.exists_mul_of_mem_sup hPO h
    apply hyIP
    have e : yI = p * (o * yO⁻¹) := by rw [← mul_assoc, ← hpo, hyIy]
    have h2 : o * yO⁻¹ ∈ I ⊓ AS76b.oddCoreIn (sec2K E) := by
      refine mem_inf.mpr ⟨?_, mul_mem ho (inv_mem hyO)⟩
      have := I.mul_mem (I.inv_mem (hPI hp)) hyI
      rwa [e, ← mul_assoc, inv_mul_cancel, one_mul] at this
    rw [hIO, mem_bot] at h2
    rw [e, h2, mul_one]
    exact hp
  have hCPOy : sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) ≤
      sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ⊔ zpowers y := by
    have hle : sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ⊔ zpowers y ≤
        sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
      sup_le hPOC (zpowers_le.mpr hyC)
    have h1 := Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left hle
    rw [hC3] at h1
    have h2 : (sec2P E ⊔ AS76b.oddCoreIn (sec2K E)).relIndex
        (sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ⊔ zpowers y) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun h => hyPO' (h (mem_sup_right (mem_zpowers y)))
    have h3 : (sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ⊔ zpowers y).relIndex
        (sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp ⟨_, h1.symm⟩ with h | h
      · exact absurd h h2
      · rw [h] at h1
        omega
    exact Subgroup.relIndex_eq_one.mp h3
  have hCI : ∀ k ∈ sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G), k ∈ I →
      ∃ p ∈ sec2P E, ∃ m : ℤ, k = p * yI ^ m := by
    intro k hk hkI
    have hk' : k ∈ ((sec2P E ⊔ AS76b.oddCoreIn (sec2K E) ⊔ zpowers y : Subgroup G) : Set G) :=
      hCPOy hk
    rw [coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr (hKPO hyK))] at hk'
    obtain ⟨w, hw, x, hx, rfl⟩ := hk'
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨p, hp, o, ho, rfl, -⟩ := NXKernel.exists_mul_of_mem_sup hPO hw
    have hco : o * yI ^ m = yI ^ m * o := (hcommIO _ (zpow_mem hyI m) o ho).symm
    have e : p * o * y ^ m = p * yI ^ m * (o * yO ^ m) := by
      rw [hyeq, Commute.mul_zpow hycomm m]
      calc p * o * (yI ^ m * yO ^ m) = p * (o * yI ^ m) * yO ^ m := by group
        _ = p * (yI ^ m * o) * yO ^ m := by rw [hco]
        _ = p * yI ^ m * (o * yO ^ m) := by group
    dsimp only at hkI ⊢
    rw [e] at hkI ⊢
    have h1 : o * yO ^ m ∈ I ⊓ AS76b.oddCoreIn (sec2K E) := by
      refine mem_inf.mpr ⟨?_, mul_mem ho (zpow_mem hyO m)⟩
      have := I.mul_mem (I.inv_mem (I.mul_mem (hPI hp) (zpow_mem hyI m))) hkI
      rwa [inv_mul_cancel_left] at this
    rw [hIO, mem_bot] at h1
    exact ⟨p, hp, m, by rw [h1, mul_one]⟩
  have hyIT : yI ∈ normalizer (sec2T E T₀ : Set G) := by
    have h1 : ∀ t ∈ sec2T E T₀, yI * t * yI⁻¹ ∈ sec2T E T₀ := fun t ht => by
      have h := hyIcomm t (hTI ht)
      have e : yI * t * yI⁻¹ = (t * yI * t⁻¹ * yI⁻¹)⁻¹ * t := by group
      rw [e]
      exact mul_mem (inv_mem (hPT h)) ht
    have h2 : ∀ t ∈ sec2T E T₀, yI⁻¹ * t * yI ∈ sec2T E T₀ := fun t ht => by
      have h := hyIcomm t (hTI ht)
      have h' := (mem_normalizer_iff.mp (hKP (inv_mem hyIK)) _).mp h
      rw [inv_inv] at h'
      have e : yI⁻¹ * t * yI = yI⁻¹ * (t * yI * t⁻¹ * yI⁻¹) * yI * t := by group
      rw [e]
      exact mul_mem (hPT h') ht
    rw [mem_normalizer_iff]
    intro t
    refine ⟨h1 t, fun ht => ?_⟩
    have := h2 _ ht
    simpa [mul_assoc] using this
  obtain ⟨zb, hzb, hzbz⟩ := hθsurj z hzV
  have hzc : ∀ x ∈ zpowers z,
      x ∈ (Subgroup.upperCentralSeries ↥(sec2T E T₀) 1).map (sec2T E T₀).subtype := by
    intro x hx
    rw [Subgroup.upperCentralSeries_one, ← centerIn_eq_map, hQ.center]
    exact hx
  have hzbar : Sec2Nat.act g'⁻¹ zb = Sec2Nat.z0 ∨ Sec2Nat.act g'⁻¹ zb = Sec2Nat.z0 + 1 := by
    have h1 := hzc z (mem_zpowers z)
    rw [← hzbz, hlay 1 hzb, Sec2Nat.mem_lay_d0_one ((Sec2Nat.sum_act _ _).trans hzb)] at h1
    have hz1 : z ≠ 1 := by
      intro h
      have := hQ.order
      rw [h, orderOf_one] at this
      norm_num at this
    rcases h1 with h | h | h | h
    · exfalso
      apply hz1
      rw [← hzbz]
      exact (hθker zb hzb).mpr
        (Or.inl (Sec2Nat.act_injective g'⁻¹ (h.trans (Sec2Nat.act_zero _).symm)))
    · exfalso
      apply hz1
      rw [← hzbz]
      exact (hθker zb hzb).mpr
        (Or.inr (Sec2Nat.act_injective g'⁻¹ (h.trans (Sec2Nat.act_ones _).symm)))
    · exact Or.inl h
    · exact Or.inr h
  have hflag : ∀ n ∈ I, n ∈ centralizer ({z} : Set G) → ∀ q ∈ Q, n * q * n⁻¹ ∈ sec2T E T₀ := by
    intro n hnI hnz q hq
    have hnK : n ∈ sec2K E := hIK hnI
    have hqT : q ∈ sec2T E T₀ := hQ.le hq
    have hqK : q ∈ sec2K E := hTK hqT
    obtain ⟨i, hi⟩ := hf ⟨q, hqK⟩ hqT
    have hfl : ∀ w : Fin 6 → ZMod 2, ∑ j, w j = 0 → w ∈ Sec2Nat.lay Sec2Nat.d0 3 →
        w + Sec2Nat.act (Sec2Nat.d0 i) w ∈ Sec2Nat.lay Sec2Nat.d0 1 := by
      intro w hw hw3
      have hw' : ∑ j, Sec2Nat.act g' w j = 0 := (Sec2Nat.sum_act g' w).trans hw
      have hw'3 : θ (Sec2Nat.act g' w) ∈
          (Subgroup.upperCentralSeries ↥(sec2T E T₀) 3).map (sec2T E T₀).subtype := by
        rw [hlay 3 hw', Sec2Nat.act_inv_act]
        exact hw3
      have hw'Q : θ (Sec2Nat.act g' w) ∈ Q := by
        have h1 : θ (Sec2Nat.act g' w) ∈ E ⊓ A ⊓ Q := by
          rw [h215ii]
          exact ⟨hw'3, hθV _ hw'⟩
        exact h1.2
      have h1 : θ (Sec2Nat.act g' w + Sec2Nat.act
          ((φ ⟨q, hqK⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) (Sec2Nat.act g' w)) ∈
          (Subgroup.upperCentralSeries ↥(sec2T E T₀) 1).map (sec2T E T₀).subtype := by
        rw [← theta_comm hθadd hθker hθconj ⟨q, hqK⟩ hw']
        exact hzc _ (hQ.comm_mem_zpowers hw'Q hq)
      rw [hlay 1 (Sec2Nat.sum_add_act _ _), Sec2Nat.act_add, Sec2Nat.act_inv_act, hi,
        Sec2Nat.act_conj] at h1
      exact h1
    have hi4 := Sec2Nat.lt_four_of_flag hfl
    set τ : Equiv.Perm (Fin 6) := ((φ ⟨n, hnK⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))
      with hτ
    have hτz : Sec2Nat.act τ zb = zb ∨ Sec2Nat.act τ zb = zb + 1 := by
      have h1 : θ (Sec2Nat.act τ zb) = θ zb := by
        have hn' : n * z * n⁻¹ = z := by
          rw [mem_centralizer_singleton_iff.mp hnz, mul_inv_cancel_right]
        have := hθconj ⟨n, hnK⟩ zb hzb
        rw [hzbz] at this
        change n * z * n⁻¹ = _ at this
        rw [hn'] at this
        rw [hzbz]
        exact this.symm
      have h2 : θ (Sec2Nat.act τ zb + zb) = 1 := by
        have hinv := theta_inv hθadd hθker hzb
        calc θ (Sec2Nat.act τ zb + zb) = θ (Sec2Nat.act τ zb) * θ zb :=
              hθadd _ _ ((Sec2Nat.sum_act _ _).trans hzb) hzb
          _ = (θ zb)⁻¹ * θ zb := by rw [h1, hinv]
          _ = 1 := inv_mul_cancel _
      have hev : ∑ j, (Sec2Nat.act τ zb + zb) j = 0 := by
        simp only [Pi.add_apply, Finset.sum_add_distrib, Sec2Nat.sum_act, hzb, add_zero]
      rcases (hθker _ hev).mp h2 with h | h
      · exact Or.inl (vec_eq_of_add_eq_zero h)
      · exact Or.inr (vec_eq_of_add_eq_one h)
    have key : Sec2Nat.act (g'⁻¹ * τ * g') (Sec2Nat.act g'⁻¹ zb) =
        Sec2Nat.act g'⁻¹ (Sec2Nat.act τ zb) := by
      rw [← Sec2Nat.act_mul, ← Sec2Nat.act_mul]
      congr 1
      group
    have hτ₀ : Sec2Nat.act (g'⁻¹ * τ * g') Sec2Nat.z0 = Sec2Nat.z0 ∨
        Sec2Nat.act (g'⁻¹ * τ * g') Sec2Nat.z0 = Sec2Nat.z0 + 1 := by
      rcases hzbar with hzb' | hzb' <;> rcases hτz with hτ' | hτ'
      · left
        rw [← hzb', key, hτ']
      · right
        rw [← hzb', key, hτ', Sec2Nat.act_add, Sec2Nat.act_ones]
      · left
        rw [hτ', hzb', Sec2Nat.act_add, Sec2Nat.act_ones] at key
        exact add_right_cancel key
      · right
        rw [hτ', Sec2Nat.act_add, Sec2Nat.act_ones, hzb', Sec2Nat.act_add,
          Sec2Nat.act_ones] at key
        exact add_right_cancel key
    obtain ⟨j, hj⟩ := Sec2Nat.conj_u0 _ hτ₀ hi4
    have hnqK : n * q * n⁻¹ ∈ sec2K E := mul_mem (mul_mem hnK hqK) (inv_mem hnK)
    have hφnq : ((φ ⟨n * q * n⁻¹, hnqK⟩ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
        g' * Sec2Nat.d0 j * g'⁻¹ := by
      have e : (⟨n * q * n⁻¹, hnqK⟩ : ↥(sec2K E)) = ⟨n, hnK⟩ * ⟨q, hqK⟩ * ⟨n, hnK⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hi, ← hτ, ← hj]
      group
    obtain ⟨t, htT, htf⟩ := hf' j
    have hk : (t : G)⁻¹ * (n * q * n⁻¹) ∈
        sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G) := by
      have h1 : (t⁻¹ * ⟨n * q * n⁻¹, hnqK⟩ : ↥(sec2K E)) ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv,
          show φ t = φ ⟨n * q * n⁻¹, hnqK⟩ from Subtype.ext (htf.trans hφnq.symm), inv_mul_cancel]
      rw [hφker, mem_subgroupOf] at h1
      exact h1
    have hkI : (t : G)⁻¹ * (n * q * n⁻¹) ∈ I :=
      mul_mem (inv_mem (hTI htT)) (mul_mem (mul_mem hnI (hQI hq)) (inv_mem hnI))
    obtain ⟨p, hp, m, hpm⟩ := hCI _ hk hkI
    have e : n * q * n⁻¹ = (t * p) * yI ^ m := by
      rw [show t * p * yI ^ m = t * (p * yI ^ m) from mul_assoc _ _ _, ← hpm,
        mul_inv_cancel_left]
    obtain ⟨a, ha⟩ := hT2 ⟨q, hqT⟩
    have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hnqa : (n * q * n⁻¹) ^ 2 ^ a = 1 := by rw [conj_pow, hqa, mul_one, mul_inv_cancel]
    rw [e] at hnqa ⊢
    exact mem_of_mul_zpow_of_pow_eq_one hT2 hyIT hyI3 (mul_mem htT (hPT hp)) m hnqa
  refine ⟨hTsyl, h215ii, ?_⟩
  rintro c ⟨hcK, hcz⟩
  obtain ⟨cI, hcI, cO, hcO, rfl, -⟩ := hdec c hcK
  have hcOz : cO ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr (hcommIO z (hTI hQ.z_mem_T) cO hcO).symm
  have hcIz : cI ∈ centralizer ({z} : Set G) := by
    have e : cI = cI * cO * cO⁻¹ := by group
    rw [e]
    exact mul_mem hcz (inv_mem hcOz)
  have hLI : sec2P E ⊔ zpowers yI ≤ I := sup_le hPI (zpowers_le.mpr hyI)
  have hLcard : Nat.card (sec2P E ⊔ zpowers yI : Subgroup G) = Nat.card (sec2P E) * 3 := by
    rw [AschbacherTheorem3.card_sup_of_le_normalizer (zpowers_le.mpr (hKP hyIK)) hPyI,
      Nat.card_zpowers, hyIo]
  have hsyl3 : ∀ x ∈ sec2P E ⊔ zpowers yI, orderOf x = 3 →
      IsSylowOf 3 (zpowers x) (sec2P E ⊔ zpowers yI) := by
    intro x hx hx3
    rw [isSylowOf_iff]
    refine ⟨zpowers_le.mpr hx, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3,
      pow_one]), fun h3 => ?_⟩
    have h1 := Subgroup.relIndex_mul_card (zpowers x) (sec2P E ⊔ zpowers yI)
    rw [inf_eq_left.mpr (zpowers_le.mpr hx), Nat.card_zpowers, hx3, hLcard] at h1
    have h2 : (zpowers x).relIndex (sec2P E ⊔ zpowers yI) = Nat.card (sec2P E) :=
      Nat.eq_of_mul_eq_mul_right (by norm_num) h1
    rw [h2] at h3
    obtain ⟨a, ha⟩ := hP2.exists_card_eq
    rw [ha] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hy'L : cI * yI * cI⁻¹ ∈ sec2P E ⊔ zpowers yI := by
    have e : cI * yI * cI⁻¹ = (cI * yI * cI⁻¹ * yI⁻¹) * yI := by group
    rw [e]
    exact mul_mem (mem_sup_left (hyIcomm cI hcI)) (mem_sup_right (mem_zpowers yI))
  have hy'o : orderOf (cI * yI * cI⁻¹) = 3 := by
    refine orderOf_eq_prime (by rw [conj_pow, hyI3, mul_one, mul_inv_cancel]) fun h => hyI1 ?_
    have e : yI = cI⁻¹ * (cI * yI * cI⁻¹) * cI := by group
    rw [e, h, mul_one, inv_mul_cancel]
  obtain ⟨l, hlL, hl⟩ := (hsyl3 yI (mem_sup_right (mem_zpowers yI)) hyIo).exists_mem_conj
    (hsyl3 _ hy'L hy'o)
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp ((hl _).mp (mem_zpowers _))
  have hlI : l ∈ I := hLI hlL
  have h2 : l⁻¹ * (cI * yI * cI⁻¹) * l * yI⁻¹ ∈ sec2P E := by
    have e : l⁻¹ * (cI * yI * cI⁻¹) * l * yI⁻¹ = l⁻¹ * cI * yI * (l⁻¹ * cI)⁻¹ * yI⁻¹ := by group
    rw [e]
    exact hyIcomm _ (mul_mem (inv_mem hlI) hcI)
  have h3 : yI ^ m = yI := by
    have h4 : yI ^ m * yI⁻¹ ∈ sec2P E ⊓ zpowers yI :=
      mem_inf.mpr ⟨by rw [hm]; exact h2,
        mul_mem (zpow_mem (mem_zpowers yI) m) (inv_mem (mem_zpowers yI))⟩
    rw [hPyI, mem_bot] at h4
    exact mul_inv_eq_one.mp h4
  have hLz : sec2P E ⊔ zpowers yI ≤ centralizer ({z} : Set G) := by
    have hCz : ∀ x ∈ sec2K E ⊓ centralizer ((E ⊓ A : Subgroup G) : Set G),
        x ∈ centralizer ({z} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hx.2 z hzV).symm
    exact sup_le (fun p hp => hCz p (hPOC (mem_sup_left hp))) (zpowers_le.mpr (hCz yI hyIC))
  have hLQ : sec2P E ⊔ zpowers yI ≤ normalizer (Q : Set G) :=
    sup_le (hPT.trans hTQ) (zpowers_le.mpr hyIQ)
  have hnI : l⁻¹ * cI ∈ I := mul_mem (inv_mem hlI) hcI
  have hnz : l⁻¹ * cI ∈ centralizer ({z} : Set G) := mul_mem (inv_mem (hLz hlL)) hcIz
  have hny : l⁻¹ * cI * yI = yI * (l⁻¹ * cI) := by
    have e : l⁻¹ * cI * yI * (l⁻¹ * cI)⁻¹ = yI :=
      calc l⁻¹ * cI * yI * (l⁻¹ * cI)⁻¹ = l⁻¹ * (cI * yI * cI⁻¹) * l := by group
        _ = yI ^ m := hm.symm
        _ = yI := h3
    calc l⁻¹ * cI * yI = l⁻¹ * cI * yI * (l⁻¹ * cI)⁻¹ * (l⁻¹ * cI) := by group
      _ = yI * (l⁻¹ * cI) := by rw [e]
  have hQnT : Q.map (MulAut.conj (l⁻¹ * cI)).toMonoidHom ≤ sec2T E T₀ := by
    rintro _ ⟨q, hq, rfl⟩
    exact hflag _ hnI hnz q hq
  have hyQn : (l⁻¹ * cI)⁻¹ * y * (l⁻¹ * cI) ∈ normalizer (Q : Set G) := by
    have hnK : l⁻¹ * cI ∈ sec2K E := hIK hnI
    have h1 : (l⁻¹ * cI)⁻¹ * yO * (l⁻¹ * cI) ∈ AS76b.oddCoreIn (sec2K E) := by
      have := (mem_normalizer_iff.mp (hKO (inv_mem hnK)) yO).mp hyO
      rwa [inv_inv] at this
    have h2 : (l⁻¹ * cI)⁻¹ * yO * (l⁻¹ * cI) ∈ normalizer (Q : Set G) :=
      centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun q hq => hcommIO q (hQI hq) _ h1)
    have hny' : (l⁻¹ * cI)⁻¹ * yI = yI * (l⁻¹ * cI)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hny, mul_inv_cancel_right]
    have e : (l⁻¹ * cI)⁻¹ * y * (l⁻¹ * cI) = yI * ((l⁻¹ * cI)⁻¹ * yO * (l⁻¹ * cI)) := by
      rw [hyeq]
      calc (l⁻¹ * cI)⁻¹ * (yI * yO) * (l⁻¹ * cI) =
          ((l⁻¹ * cI)⁻¹ * yI) * yO * (l⁻¹ * cI) := by group
        _ = (yI * (l⁻¹ * cI)⁻¹) * yO * (l⁻¹ * cI) := by rw [hny']
        _ = yI * ((l⁻¹ * cI)⁻¹ * yO * (l⁻¹ * cI)) := by group
    rw [e]
    exact mul_mem hyIQ h2
  have hQn : Q.map (MulAut.conj (l⁻¹ * cI)).toMonoidHom = Q :=
    hQ.unique _ (Sec2Q.isQ8Cube_map hQ.q8 _) hQnT (mem_normalizer_map_conj hyQn)
  have hnQ : l⁻¹ * cI ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr hQn
  have hcOQ : cO ∈ normalizer (Q : Set G) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun q hq => hcommIO q (hQI hq) cO hcO)
  have e : cI * cO = l * (l⁻¹ * cI) * cO := by group
  rw [e]
  exact mul_mem (mul_mem (hLQ hlL) hnQ) hcOQ

end CFSG.ComponentClassification.AS81
