module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Step0
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def SmallRankCaseDelta3 (P : Sylow 3 G) (M : Subgroup G) : Prop :=
  ∃ N : Subgroup G, N ≤ (P : Subgroup G) ∧ IsCyclic N ∧ 9 ∣ Nat.card N ∧
    N ⊔ rankThreePrimeCore 3 M ≤ M ∧
      ((N ⊔ rankThreePrimeCore 3 M).subgroupOf M).Normal

@[expose] def GL83SmallRankLemma62At3 (G : Type) [Group G] [Finite G] : Prop :=
  Setting G → FullCoreLocal G →
    ∀ (P : Sylow 3 G) (M : Subgroup G), SmallRankSituation G 3 P M →
      ∀ x z : G, SmallRankPoint P M x → SmallRankCentral P z →
        HasPrimeConstraint (G := M) 3 ∨ SmallRankCaseDelta3 P M

private theorem pow_apply_aux {M : Type*} [Mul M] (φ : MulAut M) (n : ℕ) (x : M) :
    (φ ^ n) x = (⇑φ)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, ih, Function.iterate_succ_apply']

private theorem dvd_three_aux {d : ℕ} (h9 : d ∣ 9) (h8 : d ≤ 8) : d ∣ 3 := by
  interval_cases d <;> omega

theorem aut_quaternion_pow {φ : MulAut (QuaternionGroup 2)} (h : φ ^ 9 = 1) : φ ^ 3 = 1 := by
  refine MulEquiv.ext fun x => ?_
  have h9 : Function.IsPeriodicPt (⇑φ) 9 x := by
    show (⇑φ)^[9] x = x
    rw [← pow_apply_aux, h, MulAut.one_apply]
  have hle : Function.minimalPeriod (⇑φ) x ≤ 8 := by
    have hcard := Function.minimalPeriod_le_card (f := ⇑φ) (x := x)
    rw [QuaternionGroup.card] at hcard
    omega
  have h3 : Function.IsPeriodicPt (⇑φ) 3 x :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr (dvd_three_aux h9.minimalPeriod_dvd hle)
  rw [pow_apply_aux, MulAut.one_apply]
  exact h3


omit [Finite G] in
private theorem r10h9_pow_conj {z s c : G} (hzc : Commute z c) (h1 : z * s = c * s * z)
    (k : ℕ) : z ^ k * s = c ^ k * s * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hzk : z * c ^ k = c ^ k * z := (hzc.pow_right k).eq
    calc z ^ (k + 1) * s = z * (z ^ k * s) := by rw [pow_succ', mul_assoc]
      _ = z * (c ^ k * s * z ^ k) := by rw [ih]
      _ = (z * c ^ k) * s * z ^ k := by simp only [mul_assoc]
      _ = (c ^ k * z) * s * z ^ k := by rw [hzk]
      _ = c ^ k * (z * s) * z ^ k := by simp only [mul_assoc]
      _ = c ^ k * (c * s * z) * z ^ k := by rw [h1]
      _ = (c ^ k * c) * s * (z * z ^ k) := by simp only [mul_assoc]
      _ = c ^ (k + 1) * s * z ^ (k + 1) := by rw [pow_succ, pow_succ']

omit [Finite G] in
private theorem r10h9_mem_normalizer {z q : G} {S : Subgroup G} (hqz : q * z = z * q)
    (hqS : q ∈ normalizer (S : Set G)) :
    q ∈ normalizer ((⁅zpowers z, S⁆ : Subgroup G) : Set G) := by
  have hfz : (MulAut.conj q).toMonoidHom z = z := by
    show q * z * q⁻¹ = z
    rw [hqz, mul_inv_cancel_right]
  have hS' : S.map (MulAut.conj q).toMonoidHom = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hqS
  have key : (⁅zpowers z, S⁆ : Subgroup G).map (MulAut.conj q).toMonoidHom
      = ⁅zpowers z, S⁆ := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers, hfz, hS']
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr key

omit [Finite G] in
private theorem r10h9_cube_centralizes {q : G} {R : Subgroup G}
    (hN : q ∈ normalizer (R : Set G)) (e : R ≃* QuaternionGroup 2) (hq9 : q ^ 9 = 1) :
    ∀ r ∈ R, q ^ 3 * r = r * q ^ 3 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : normalizer (R : Set G), (Q : G) = q := ⟨⟨q, hN⟩, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut R, φ = R.normalizerMonoidHom Q := ⟨_, rfl⟩
  have happ : ∀ (m : normalizer (R : Set G)) (r : R),
      ((R.normalizerMonoidHom m r : R) : G) = (m : G) * (r : G) * (m : G)⁻¹ :=
    fun _ _ => rfl
  have hQ9 : Q ^ 9 = 1 := Subtype.ext (by simp [hQ, hq9])
  have hφ9 : φ ^ 9 = 1 := by
    rw [hφ, ← map_pow, hQ9, map_one]
  have hψ3 : (MulAut.congr e φ) ^ 3 = 1 := by
    apply aut_quaternion_pow
    rw [← map_pow, hφ9, map_one]
  have hφ3 : φ ^ 3 = 1 := by
    apply (MulAut.congr e).injective
    rw [map_pow, map_one]
    exact hψ3
  have hQ3 : ((Q ^ 3 : normalizer (R : Set G)) : G) = q ^ 3 := by
    simp [hQ]
  have hQ3' : R.normalizerMonoidHom (Q ^ 3) = 1 := by
    rw [map_pow, ← hφ, hφ3]
  have hkey : ∀ r : R,
      ((R.normalizerMonoidHom (Q ^ 3) r : R) : G) = q ^ 3 * (r : G) * (q ^ 3)⁻¹ := by
    intro r
    rw [happ, hQ3]
  intro r hr
  have h1 : ((R.normalizerMonoidHom (Q ^ 3) ⟨r, hr⟩ : R) : G) = r := by
    rw [hQ3', MulAut.one_apply]
  rw [hkey] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

private theorem r10h9_zpowers_cube_eq {z q : G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hq9 : orderOf q = 9) (hq3 : q ^ 3 ∈ zpowers z) : zpowers (q ^ 3) = zpowers z := by
  have hq9' : q ^ 9 = 1 := by
    have h := pow_orderOf_eq_one q
    rwa [hq9] at h
  have hw9 : (q ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    exact hq9'
  have hw_ne : q ^ 3 ≠ 1 := by
    intro h
    have h1 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one h
    rw [hq9] at h1
    norm_num at h1
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hword : orderOf (q ^ 3) = 3 := orderOf_eq_prime hw9 hw_ne
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hq3)
  apply le_of_eq
  rw [Nat.card_zpowers, Nat.card_zpowers, hword, hzord]

private theorem r10h9_z_comm_of_cube {z q : G} {R : Subgroup G} (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) (hq9 : orderOf q = 9) (hq3 : q ^ 3 ∈ zpowers z)
    (hcube : ∀ r ∈ R, q ^ 3 * r = r * q ^ 3) : ∀ r ∈ R, z * r = r * z := by
  intro r hr
  have hz : z ∈ zpowers (q ^ 3) := by
    rw [r10h9_zpowers_cube_eq hz3 hz1 hq9 hq3]
    exact Subgroup.mem_zpowers z
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hc : Commute (q ^ 3) r := hcube r hr
  have hz' : Commute ((q ^ 3) ^ k) r := hc.zpow_left k
  rw [hk] at hz'
  exact hz'

theorem false_of_central_order_nine {z q : G} {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hqz : q * z = z * q) (hqS : q ∈ normalizer (S : Set G))
    (hq9 : orderOf q = 9) (hq3 : q ^ 3 ∈ zpowers z)
    (hR : Nonempty (↥(⁅zpowers z, S⁆) ≃* QuaternionGroup 2)) : False := by
  obtain ⟨e⟩ := hR
  have hq9' : q ^ 9 = 1 := by
    have h := pow_orderOf_eq_one q
    rwa [hq9] at h
  have hN := r10h9_mem_normalizer hqz hqS
  have hcube := r10h9_cube_centralizes hN e hq9'
  have hzR := r10h9_z_comm_of_cube hz3 hz1 hq9 hq3 hcube
  have hRcard : Nat.card ↥(⁅zpowers z, S⁆ : Subgroup G) = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] <;> norm_num
  have hcomm : ∀ s ∈ S, z * s = s * z := by
    intro s hs
    have hcR : z * s * z⁻¹ * s⁻¹ ∈ ⁅zpowers z, S⁆ := by
      have h := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers z) hs
      exact h
    have hc3 : (z * s * z⁻¹ * s⁻¹) ^ 3 = 1 := by
      have h1 : z * s = z * s * z⁻¹ * s⁻¹ * s * z := by group
      have h2 := r10h9_pow_conj (hzR _ hcR : Commute z (z * s * z⁻¹ * s⁻¹)) h1 3
      rw [hz3, one_mul, mul_one] at h2
      exact mul_right_cancel (h2.symm.trans (one_mul s).symm)
    have hx3 : (⟨z * s * z⁻¹ * s⁻¹, hcR⟩ : ↥(⁅zpowers z, S⁆)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    have hx8 : (⟨z * s * z⁻¹ * s⁻¹, hcR⟩ : ↥(⁅zpowers z, S⁆)) ^ 8 = 1 := by
      have h := pow_card_eq_one' (x := (⟨z * s * z⁻¹ * s⁻¹, hcR⟩ : ↥(⁅zpowers z, S⁆)))
      rwa [hRcard] at h
    have hx1 := pow_gcd_eq_one.mpr ⟨hx3, hx8⟩
    have h8 : Nat.gcd 3 8 = 1 := by norm_num
    rw [h8, pow_one] at hx1
    have hc1 : z * s * z⁻¹ * s⁻¹ = 1 := congrArg Subtype.val hx1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc1)
  have hzS : zpowers z ≤ centralizer (S : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun s hs => (hcomm s hs).symm)
  have hbot : ⁅zpowers z, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hzS
  have h1 : Nat.card ↥(⁅zpowers z, S⁆ : Subgroup G) = 1 := by
    rw [hbot, Subgroup.card_bot]
  omega


private theorem r10h10_decomp {G : Type} [Group G] {N D : Subgroup G}
    (hND : N ≤ normalizer (D : Set G)) {x : G} (hx : x ∈ N ⊔ D) :
    ∃ n ∈ N, ∃ d ∈ D, n * d = x := by
  have h : x ∈ ((N ⊔ D : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right N D hND] at h
  obtain ⟨n, hn, d, hd, hnd⟩ := Set.mem_mul.1 h
  exact ⟨n, hn, d, hd, hnd⟩

private theorem r10h10_alg {X : Type} [Group X] (k₀ t w : X) (e : ℤ) (hw : w * k₀ = k₀ * w)
    (ht : t⁻¹ * k₀ * t = k₀ ^ e) : (t * w * t⁻¹) * k₀ = k₀ * (t * w * t⁻¹) := by
  have hA : t⁻¹ * k₀ = k₀ ^ e * t⁻¹ := by
    calc t⁻¹ * k₀ = t⁻¹ * k₀ * t * t⁻¹ := by group
      _ = k₀ ^ e * t⁻¹ := by rw [ht]
  have hB : t * k₀ ^ e * t⁻¹ = k₀ := by
    calc t * k₀ ^ e * t⁻¹ = t * (t⁻¹ * k₀ * t) * t⁻¹ := by rw [ht]
      _ = k₀ := by group
  have hC : w * k₀ ^ e = k₀ ^ e * w := (Commute.zpow_right (hw : Commute w k₀) e).eq
  calc (t * w * t⁻¹) * k₀ = t * w * (t⁻¹ * k₀) := by group
    _ = t * w * (k₀ ^ e * t⁻¹) := by rw [hA]
    _ = t * (w * k₀ ^ e) * t⁻¹ := by group
    _ = t * (k₀ ^ e * w) * t⁻¹ := by rw [hC]
    _ = (t * k₀ ^ e * t⁻¹) * (t * w * t⁻¹) := by group
    _ = k₀ * (t * w * t⁻¹) := by rw [hB]

private theorem r10h10_commutator_mem_centralizer {X : Type} [Group X] (K : Subgroup X)
    [K.Normal] [IsCyclic K] (x y : X) : ⁅x, y⁆ ∈ centralizer (K : Set X) := by
  obtain ⟨k₀, hk₀⟩ := IsCyclic.exists_generator (α := ↥K)
  have hpow : ∀ k ∈ K, ∃ m : ℤ, (k₀ : X) ^ m = k := by
    intro k hk
    obtain ⟨m, hm⟩ := hk₀ ⟨k, hk⟩
    exact ⟨m, by rw [← Subgroup.coe_zpow]; exact congrArg Subtype.val hm⟩
  have hconj : ∀ u : X, ∃ e : ℤ, u * (k₀ : X) * u⁻¹ = (k₀ : X) ^ e := by
    intro u
    obtain ⟨m, hm⟩ := hpow _ ((inferInstance : K.Normal).conj_mem (k₀ : X) k₀.2 u)
    exact ⟨m, hm.symm⟩
  obtain ⟨a, ha⟩ := hconj x
  obtain ⟨b, hb⟩ := hconj y
  obtain ⟨e, he⟩ := hconj (y * x)⁻¹
  rw [inv_inv] at he
  have hs : x * y * (k₀ : X) * (x * y)⁻¹ = (k₀ : X) ^ (a * b) := by
    calc x * y * (k₀ : X) * (x * y)⁻¹ = x * (y * (k₀ : X) * y⁻¹) * x⁻¹ := by group
      _ = x * (k₀ : X) ^ b * x⁻¹ := by rw [hb]
      _ = (x * (k₀ : X) * x⁻¹) ^ b := conj_zpow.symm
      _ = ((k₀ : X) ^ a) ^ b := by rw [ha]
      _ = (k₀ : X) ^ (a * b) := (zpow_mul _ _ _).symm
  have ht : y * x * (k₀ : X) * (y * x)⁻¹ = (k₀ : X) ^ (b * a) := by
    calc y * x * (k₀ : X) * (y * x)⁻¹ = y * (x * (k₀ : X) * x⁻¹) * y⁻¹ := by group
      _ = y * (k₀ : X) ^ a * y⁻¹ := by rw [ha]
      _ = (y * (k₀ : X) * y⁻¹) ^ a := conj_zpow.symm
      _ = ((k₀ : X) ^ b) ^ a := by rw [hb]
      _ = (k₀ : X) ^ (b * a) := (zpow_mul _ _ _).symm
  have hst : x * y * (k₀ : X) * (x * y)⁻¹ = y * x * (k₀ : X) * (y * x)⁻¹ := by
    rw [hs, ht, mul_comm a b]
  have hw : ((y * x)⁻¹ * (x * y)) * (k₀ : X) = (k₀ : X) * ((y * x)⁻¹ * (x * y)) := by
    calc ((y * x)⁻¹ * (x * y)) * (k₀ : X)
        = (y * x)⁻¹ * (x * y * (k₀ : X) * (x * y)⁻¹) * (x * y) := by group
      _ = (y * x)⁻¹ * (y * x * (k₀ : X) * (y * x)⁻¹) * (x * y) := by rw [hst]
      _ = (k₀ : X) * ((y * x)⁻¹ * (x * y)) := by group
  have hc := r10h10_alg (k₀ : X) (y * x) ((y * x)⁻¹ * (x * y)) e hw he
  have hcomm : y * x * ((y * x)⁻¹ * (x * y)) * (y * x)⁻¹ = ⁅x, y⁆ := by
    rw [commutatorElement_def]
    group
  rw [hcomm] at hc
  have hc' : Commute ⁅x, y⁆ (k₀ : X) := hc
  rw [mem_centralizer_iff]
  intro h hh
  obtain ⟨m, rfl⟩ := hpow h hh
  exact (hc'.zpow_right m).eq.symm

private theorem r10h10_exists_K {G X : Type} [Group G] [Group X] {M D N : Subgroup G}
    {π : M →* X}
    (hπs : Function.Surjective π) (hker : ∀ u : M, π u = 1 ↔ (u : G) ∈ D) (hNM : N ≤ M)
    (hND : N ≤ normalizer (D : Set G)) (hNc : IsCyclic N)
    (hNn : ∀ a : M, ∀ n : N, (a : G) * (n : G) * (a : G)⁻¹ ∈ N ⊔ D) :
    ∃ K : Subgroup X, K.Normal ∧ IsCyclic K ∧ ∀ n : N, π (Subgroup.inclusion hNM n) ∈ K := by
  refine ⟨(π.comp (Subgroup.inclusion hNM)).range, ⟨fun k hk g => ?_⟩, ?_,
    fun n => MonoidHom.mem_range.2 ⟨n, rfl⟩⟩
  · obtain ⟨n, rfl⟩ := MonoidHom.mem_range.1 hk
    obtain ⟨a, rfl⟩ := hπs g
    obtain ⟨m, hm, d, hd, hmd⟩ := r10h10_decomp hND (hNn a n)
    have hcoe : (((Subgroup.inclusion hNM ⟨m, hm⟩)⁻¹ *
        (a * Subgroup.inclusion hNM n * a⁻¹) : M) : G) = d := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hmd]
      group
    have h1 : π ((Subgroup.inclusion hNM ⟨m, hm⟩)⁻¹ *
        (a * Subgroup.inclusion hNM n * a⁻¹)) = 1 := (hker _).2 (by rw [hcoe]; exact hd)
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, ← h1]
    exact MonoidHom.mem_range.2 ⟨⟨m, hm⟩, rfl⟩
  · exact isCyclic_of_surjective (π.comp (Subgroup.inclusion hNM)).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)

private theorem r10h10_eq_one {G : Type} [Group G] (P : Sylow 3 G) {D : Subgroup G}
    (hcop : Nat.Coprime 3 (Nat.card D)) {x : G} (hxP : x ∈ (P : Subgroup G)) (hxD : x ∈ D) :
    x = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hxP⟩
  have hpow : x ^ 3 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hd1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hpow
  have hd2 : orderOf x ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hxD
  have hcop' : Nat.Coprime (orderOf x) (Nat.card D) :=
    Nat.Coprime.coprime_dvd_left hd1 (Nat.Coprime.pow_left k hcop)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop' hd2)

private theorem r10h10_central {G X : Type} [Group G] [Group X] [Finite G] {P : Sylow 3 G}
    {M D N : Subgroup G} {π : M →* X} (hπs : Function.Surjective π)
    (hker : ∀ u : M, π u = 1 ↔ (u : G) ∈ D) (hNM : N ≤ M) (hND : N ≤ normalizer (D : Set G))
    (hNc : IsCyclic N) (hNP : N ≤ (P : Subgroup G))
    (hNn : ∀ a : M, ∀ n : N, (a : G) * (n : G) * (a : G)⁻¹ ∈ N ⊔ D)
    (hcop : Nat.Coprime 3 (Nat.card D)) (hPM : (P : Subgroup G) ≤ ⁅M, M⁆) :
    ∀ g ∈ (P : Subgroup G), ∀ n ∈ N, g * n = n * g := by
  obtain ⟨K, hKn, hKc, hKN⟩ := r10h10_exists_K hπs hker hNM hND hNc hNn
  have hle : ⁅M, M⁆ ≤ ((centralizer (K : Set X)).comap π).map M.subtype := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine Subgroup.mem_map.2 ⟨⁅(⟨g₁, hg₁⟩ : M), ⟨g₂, hg₂⟩⁆, ?_, ?_⟩
    · rw [Subgroup.mem_comap, map_commutatorElement]
      exact r10h10_commutator_mem_centralizer K _ _
    · simp [commutatorElement_def]
  intro g hg n hn
  obtain ⟨h, hh, hhg⟩ := Subgroup.mem_map.1 (hle (hPM hg))
  have hgh : (h : G) = g := hhg
  have hπh : π h ∈ centralizer (K : Set X) := Subgroup.mem_comap.1 hh
  have hnK : π (Subgroup.inclusion hNM ⟨n, hn⟩) ∈ K := hKN ⟨n, hn⟩
  have hc := Subgroup.mem_centralizer_iff.1 hπh _ hnK
  have h1 : π ((Subgroup.inclusion hNM ⟨n, hn⟩ * h)⁻¹ * (h * Subgroup.inclusion hNM ⟨n, hn⟩))
      = 1 := by
    simp only [map_mul, map_inv]
    rw [hc, inv_mul_cancel]
  have h2 := (hker _).1 h1
  have h3 : g⁻¹ * n⁻¹ * g * n ∈ D := by
    rw [← hgh]
    simpa [mul_assoc] using h2
  have hxP : g⁻¹ * n⁻¹ * g * n ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem
      ((P : Subgroup G).inv_mem hg) ((P : Subgroup G).inv_mem (hNP hn))) hg) (hNP hn)
  have h4 : g⁻¹ * n⁻¹ * g * n = 1 := r10h10_eq_one P hcop hxP h3
  have h5 : n⁻¹ * g * n = g := by
    calc n⁻¹ * g * n = g * (g⁻¹ * n⁻¹ * g * n) := by group
      _ = g := by rw [h4, mul_one]
  calc g * n = n * (n⁻¹ * g * n) := by group
    _ = n * g := by rw [h5]

private theorem r10h10_order_nine {G : Type} [Group G] [Finite G] (N : Subgroup G) [IsCyclic N]
    (h9 : 9 ∣ Nat.card N) : ∃ q ∈ N, orderOf q = 9 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥N)
  have hord : orderOf g = Nat.card N := orderOf_eq_card_of_forall_mem_zpowers hg
  have hne : orderOf g ≠ 0 := by
    rw [hord]
    exact (Nat.card_pos).ne'
  have h9' : 9 ∣ orderOf g := by
    rw [hord]
    exact h9
  refine ⟨((g ^ (orderOf g / 9) : ↥N) : G), (g ^ (orderOf g / 9) : ↥N).2, ?_⟩
  rw [Subgroup.orderOf_coe, orderOf_pow_orderOf_div hne h9']

theorem exists_central_order_nine (hS : Setting G) (hU0 : FullCoreLocal G) {P : Sylow 3 G}
    {M : Subgroup G} (hs : SmallRankSituation G 3 P M) (hδ : SmallRankCaseDelta3 P M) :
    ∃ q : G, q ∈ (P : Subgroup G) ∧ q ∈ centralizer ((P : Subgroup G) : Set G) ∧
      orderOf q = 9 := by
  obtain ⟨N, hNP, hNcyc, h9, hNDM, hNQ⟩ := hδ
  obtain ⟨hDM, hMD, hD3⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 3 M
  have hNM : N ≤ M := le_sup_left.trans hNDM
  haveI hDn : ((rankThreePrimeCore 3 M).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hDM).2 hMD
  have hNn : ∀ a : M, ∀ n : N, (a : G) * (n : G) * (a : G)⁻¹ ∈ N ⊔ rankThreePrimeCore 3 M := by
    intro a n
    have hy : (⟨(n : G), hNM n.2⟩ : M) ∈ (N ⊔ rankThreePrimeCore 3 M).subgroupOf M :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left n.2)
    have h2 := Subgroup.mem_subgroupOf.1 (hNQ.conj_mem _ hy a)
    simpa using h2
  have hcentral := r10h10_central
    (π := QuotientGroup.mk' ((rankThreePrimeCore 3 M).subgroupOf M))
    (QuotientGroup.mk'_surjective _)
    (fun u => by rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf])
    hNM (hNM.trans hMD) hNcyc hNP hNn hD3 (sylow_le_commutator_of_situation hS hU0 hs)
  obtain ⟨q, hqN, hq9⟩ := r10h10_order_nine N h9
  exact ⟨q, hNP hqN, mem_centralizer_iff.2 fun g hg => hcentral g hg q hqN, hq9⟩


theorem lemma628_ii_three (hS : Setting G) (hU0 : FullCoreLocal G) {P : Sylow 3 G}
    {M : Subgroup G} {x z : G} {T : Subgroup G} (hf : Prop627Failure G 3 P M x z T)
    (hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) :
    ¬ SmallRankCaseDelta3 P M := by
  intro hδ
  obtain ⟨q, hqP, hqc, hq9⟩ := exists_central_order_nine hS hU0 hf.situation hδ
  have hpl := SmallRankPlane.of_situation hS hf.situation hf.point hf.central
  have hqx : q * x = x * q := (mem_centralizer_iff.mp hqc x hf.point.mem).symm
  have hqz : q * z = z * q := (mem_centralizer_iff.mp hqc z hf.central.mem).symm
  have hqT : q ∈ normalizer (T : Set G) := hf.sylowTwo.normalized hqP
  have hqC : q ∈ normalizer (centralizer ({x} : Set G) : Set G) :=
    le_normalizer (mem_centralizer_singleton_iff.2 hqx)
  have hqS : q ∈ normalizer ((smallRankS x T : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hqT, hqC⟩
  have hq3 : q ^ 3 ∈ zpowers z := by
    refine hpl.center (q ^ 3) (pow_mem hqP 3) (pow_mem hqc 3) ?_
    rw [← pow_mul]
    have := pow_orderOf_eq_one q
    rwa [hq9] at this
  exact false_of_central_order_nine (hf.sylowTwo.isPGroup.to_le inf_le_left)
    hf.central.pow_eq_one hf.central.ne_one hqz hqS hq9 hq3 hR

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
