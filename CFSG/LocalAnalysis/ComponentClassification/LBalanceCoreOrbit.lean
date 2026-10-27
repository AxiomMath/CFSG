module

public import CFSG.LocalAnalysis.ComponentClassification.LBalanceCoreFixedPoints
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddFixedNormalizer

public section

namespace CFSG.ComponentClassification.LBalance.Core

open CFSG CFSG.LocalCores Subgroup
open scoped commutatorElement

variable {H : Type*} [Group H]

@[expose] def orbitJoin (K : Subgroup H) (x : H) : Subgroup H :=
  ⨆ i : ℤ, conjugate K (x ^ i)

theorem conjugate_le_orbitJoin (K : Subgroup H) (x : H) (i : ℤ) :
    conjugate K (x ^ i) ≤ orbitJoin K x :=
  le_iSup (fun i : ℤ => conjugate K (x ^ i)) i

theorem le_orbitJoin (K : Subgroup H) (x : H) : K ≤ orbitJoin K x := by
  have h := conjugate_le_orbitJoin K x 0
  rwa [zpow_zero, UnbalancedLayer.conjugate_one] at h

theorem conjugate_orbitJoin_eq_iSup (K : Subgroup H) (x g : H) :
    conjugate (orbitJoin K x) g = ⨆ i : ℤ, conjugate K (x ^ i * g) := by
  unfold orbitJoin
  rw [show conjugate (⨆ i : ℤ, conjugate K (x ^ i)) g =
    ⨆ i : ℤ, conjugate (conjugate K (x ^ i)) g from map_iSup _ _]
  simp_rw [UnbalancedLayer.conjugate_conjugate]

theorem conjugate_orbitJoin (K : Subgroup H) {x g : H} (hg : Commute g x) :
    conjugate (orbitJoin K x) g = orbitJoin (conjugate K g) x := by
  rw [conjugate_orbitJoin_eq_iSup]
  unfold orbitJoin
  simp_rw [UnbalancedLayer.conjugate_conjugate, (hg.zpow_right _).eq]

theorem conjugate_orbitJoin_self (K : Subgroup H) (x : H) :
    conjugate (orbitJoin K x) x = orbitJoin K x := by
  rw [conjugate_orbitJoin_eq_iSup]
  simp_rw [← zpow_add_one]
  exact (Equiv.addRight (1 : ℤ)).iSup_comp (g := fun i : ℤ => conjugate K (x ^ i))

theorem orbitJoin_le_layer {K : Subgroup H} (hK : IsComponent K) (x : H) :
    orbitJoin K x ≤ layer H :=
  iSup_le fun _ => component_le_layer (UnbalancedLayer.isComponent_conjugate hK _)

variable [Finite H]

theorem orbitJoin_le_centralizer {K K' : Subgroup H} (hK : IsComponent K) (hK' : IsComponent K')
    {x : H} (hKK' : ∀ i : ℤ, K' ≠ conjugate K (x ^ i)) :
    orbitJoin K x ≤ centralizer (orbitJoin K' x : Set H) := by
  refine iSup_le fun i => le_centralizer_iff.mpr (iSup_le fun j => ?_)
  rcases distinct_components_commute (UnbalancedLayer.isComponent_conjugate hK' (x ^ j))
      (UnbalancedLayer.isComponent_conjugate hK (x ^ i)) with h | h
  · refine absurd ?_ (hKK' (i - j))
    rw [← UnbalancedLayer.conjugate_conjugate_inv K' (x ^ j), h,
      UnbalancedLayer.conjugate_conjugate, ← zpow_neg, ← zpow_add, sub_eq_add_neg]
  · exact commutator_eq_bot_iff_le_centralizer.mp h

theorem center_le_center_orbitJoin {K : Subgroup H} (hK : IsComponent K) (x : H) :
    (center K).map K.subtype ≤ (center (orbitJoin K x)).map (orbitJoin K x).subtype := by
  intro z hz
  obtain ⟨hzK, hzc⟩ := (mem_map_center_iff _).mp hz
  refine (mem_map_center_iff _).mpr ⟨le_orbitJoin K x hzK, ?_⟩
  have hle : orbitJoin K x ≤ centralizer ({z} : Set H) := by
    refine iSup_le fun i k hk => mem_centralizer_singleton_iff.mpr ?_
    rcases distinct_components_commute (UnbalancedLayer.isComponent_conjugate hK (x ^ i)) hK
      with h | h
    · rw [h] at hk
      exact mem_centralizer_iff.mp hzc k hk
    · exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h hk) z hzK).symm
  rw [mem_centralizer_iff]
  intro k hk
  exact mem_centralizer_singleton_iff.mp (hle hk)

theorem center_orbitJoin_le {K : Subgroup H} (hK : IsComponent K) (x : H) :
    (center (orbitJoin K x)).map (orbitJoin K x).subtype ≤
      (center (layer H)).map (layer H).subtype := by
  intro z hz
  obtain ⟨hzM, hzc⟩ := (mem_map_center_iff _).mp hz
  refine (mem_map_center_iff _).mpr ⟨orbitJoin_le_layer hK x hzM, ?_⟩
  have hle : layer H ≤ centralizer ({z} : Set H) := by
    refine sSup_le fun K' hK' k hk => mem_centralizer_singleton_iff.mpr ?_
    by_cases hin : ∃ i : ℤ, K' = conjugate K (x ^ i)
    · obtain ⟨i, rfl⟩ := hin
      exact mem_centralizer_iff.mp hzc k (conjugate_le_orbitJoin K x i hk)
    · push Not at hin
      exact mem_centralizer_iff.mp (orbitJoin_le_centralizer hK hK' hin hzM) k
        (le_orbitJoin K' x hk)
  rw [mem_centralizer_iff]
  intro k hk
  exact mem_centralizer_singleton_iff.mp (hle hk)

theorem exists_orbit_witness {p : ℕ} [Fact p.Prime] {x : H} {n : ℕ} (hxn : x ^ p ^ n = 1)
    {K : Subgroup H} (hK : IsComponent K) (hdvd : p ∣ Nat.card (K ⧸ center K)) :
    ∃ u ∈ orbitJoin K x, (∃ a : ℕ, u ^ p ^ a = 1) ∧ (∃ k ∈ orbitJoin K x, u * k ≠ k * u) ∧
      u⁻¹ * (x⁻¹ * u * x) ∈ (center (layer H)).map (layer H).subtype := by
  set M := orbitJoin K x
  have heq : M.map ((MulAut.conj x⁻¹ : MulAut H) : H →* H) = M := conjugate_orbitJoin_self K x
  let φ : MulAut M := ((MulAut.conj x⁻¹).subgroupMap M).trans (MulEquiv.subgroupCongr heq)
  have hφ : ∀ m : M, (φ m : H) = x⁻¹ * m * x := fun m => by
    change x⁻¹ * (m : H) * x⁻¹⁻¹ = _
    rw [inv_inv]
  have hφpow : ∀ (k : ℕ) (m : M), ((φ ^ k) m : H) = (x ^ k)⁻¹ * m * x ^ k := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ, MulAut.mul_apply, ih, hφ, pow_succ]
      group
  have hφp : φ ^ p ^ n = 1 := by
    ext m
    rw [hφpow, hxn, inv_one, one_mul, mul_one]
    rfl
  set α := PerfectAutomorphisms.onCenterQuotient φ with hαdef
  have hαp : α ^ p ^ n = 1 := by
    have h := map_pow (PerfectAutomorphisms.centerQuotientHom M) φ (p ^ n)
    rw [hφp, map_one] at h
    exact h.symm
  have hdvdM : p ∣ Nat.card (M ⧸ center M) := by
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (center K) w
    have hk1 : QuotientGroup.mk' (center K) k ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw
      exact (Fact.out : p.Prime).one_lt.ne hw
    obtain ⟨k', hk', hkk'⟩ := UnbalancedLayer.exists_not_commute_of_mk_ne_one hk1
    have hkp : k ^ p ∈ center K := by
      rw [← QuotientGroup.ker_mk' (center K), MonoidHom.mem_ker, map_pow, ← hw,
        pow_orderOf_eq_one]
    let kM : M := ⟨k, le_orbitJoin K x k.2⟩
    have hkM1 : QuotientGroup.mk' (center M) kM ≠ 1 := by
      intro h
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_center_iff] at h
      exact hkk' (congrArg Subtype.val (h ⟨k', le_orbitJoin K x hk'⟩)).symm
    have hkMp : QuotientGroup.mk' (center M) kM ^ p = 1 := by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      have h := center_le_center_orbitJoin hK x ⟨k ^ p, hkp, rfl⟩
      exact (mem_map_iff_mem M.subtype_injective).mp h
    exact orderOf_eq_prime hkMp hkM1 ▸ orderOf_dvd_natCard _
  obtain ⟨v, hv1, hαv, k, hvk⟩ := exists_fixed_pElement hdvdM α hαp
  obtain ⟨g, hgv, a, hga⟩ := exists_pElement_lift hvk
  have hg1 : QuotientGroup.mk' (center M) g ≠ 1 := hgv ▸ hv1
  obtain ⟨k₀, hk₀, hk₀g⟩ := UnbalancedLayer.exists_not_commute_of_mk_ne_one hg1
  have hcen : g⁻¹ * φ g ∈ center M := by
    rw [← QuotientGroup.ker_mk' (center M), MonoidHom.mem_ker, map_mul, map_inv,
      ← PerfectAutomorphisms.onCenterQuotient_apply_mk, ← hαdef, hgv, hαv, inv_mul_cancel]
  refine ⟨g, g.2, ⟨a, ?_⟩, ⟨k₀, hk₀, hk₀g⟩, center_orbitJoin_le hK x ⟨g⁻¹ * φ g, hcen, ?_⟩⟩
  · have h := congrArg Subtype.val hga
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h
  · change ((g⁻¹ * φ g : M) : H) = _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]

theorem conjugate_mem_orbit {p : ℕ} {K : Subgroup H} (hK : IsComponent K) {x : H}
    {L O : Subgroup H} (hLx : L ≤ centralizer ({x} : Set H)) (hO : Nat.Coprime p (Nat.card O))
    {u : H} (hu : u ∈ orbitJoin K x) {a : ℕ} (hua : u ^ p ^ a = 1) {k₀ : H}
    (hk₀ : k₀ ∈ orbitJoin K x) (hk₀u : u * k₀ ≠ k₀ * u)
    (hdisp : ∀ l ∈ L, l * u * l⁻¹ * u⁻¹ ∈ O) :
    ∀ l ∈ L, ∃ i : ℤ, conjugate K l⁻¹ = conjugate K (x ^ i) := by
  intro l hl
  by_contra hcon
  push Not at hcon
  have hlx : Commute l⁻¹ x :=
    (show Commute l x from mem_centralizer_singleton_iff.mp (hLx hl)).inv_left
  have hc := orbitJoin_le_centralizer hK (UnbalancedLayer.isComponent_conjugate hK l⁻¹) hcon
  have hlu : l * u * l⁻¹ ∈ orbitJoin (conjugate K l⁻¹) x := by
    rw [← conjugate_orbitJoin K hlx]
    have h := UnbalancedLayer.conj_mem_conjugate hu l⁻¹
    rwa [inv_inv] at h
  have hcomm : Commute u (l * u * l⁻¹) := (mem_centralizer_iff.mp (hc hu) _ hlu).symm
  have hδ : (l * u * l⁻¹ * u⁻¹) ^ p ^ a = 1 := by
    rw [hcomm.symm.inv_right.mul_pow, conj_pow, inv_pow, hua]
    simp
  have hlu' : l * u * l⁻¹ = u :=
    mul_inv_eq_one.mp (eq_one_of_mem_of_pow_prime_pow hO (hdisp l hl) hδ)
  apply hk₀u
  have hk₀c := mem_centralizer_iff.mp (hc hk₀) _ hlu
  rwa [hlu'] at hk₀c

omit [Finite H] in
theorem le_normalizer_of_perfect {L : Subgroup H} (hL : Group.IsPerfect L) {x : H}
    (hLx : L ≤ centralizer ({x} : Set H)) {K : Subgroup H}
    (horb : ∀ l ∈ L, ∃ i : ℤ, conjugate K l = conjugate K (x ^ i)) :
    L ≤ normalizer (K : Set H) := by
  have hx : ∀ l ∈ L, ∀ i : ℤ, x ^ i * l = l * x ^ i := fun l hl i =>
    ((show Commute l x from mem_centralizer_singleton_iff.mp (hLx hl)).zpow_right i).eq.symm
  have hmul : ∀ a ∈ L, ∀ b ∈ L, ∀ i j : ℤ, conjugate K a = conjugate K (x ^ i) →
      conjugate K b = conjugate K (x ^ j) → conjugate K (a * b) = conjugate K (x ^ (j + i)) := by
    intro a ha b hb i j hi hj
    calc conjugate K (a * b) = conjugate (conjugate K a) b :=
          (UnbalancedLayer.conjugate_conjugate K a b).symm
      _ = conjugate K (x ^ i * b) := by rw [hi, UnbalancedLayer.conjugate_conjugate]
      _ = conjugate (conjugate K b) (x ^ i) := by
          rw [hx b hb i, UnbalancedLayer.conjugate_conjugate]
      _ = conjugate K (x ^ (j + i)) := by rw [hj, UnbalancedLayer.conjugate_conjugate, zpow_add]
  have hswap : ∀ a ∈ L, ∀ b ∈ L, conjugate K (a * b) = conjugate K (b * a) := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := horb a ha
    obtain ⟨j, hj⟩ := horb b hb
    rw [hmul a ha b hb i j hi hj, hmul b hb a ha j i hj hi, add_comm]
  have hcomm : ⁅L, L⁆ ≤ normalizer (K : Set H) := by
    rw [commutator_le]
    intro a ha b hb
    have hK : conjugate K ⁅a, b⁆ = K := by
      rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * b * (b * a)⁻¹ by group,
        ← UnbalancedLayer.conjugate_conjugate, hswap a ha b hb,
        UnbalancedLayer.conjugate_conjugate_inv]
    rw [mem_normalizer_iff]
    intro h
    rw [← UnbalancedLayer.mem_conjugate_iff, hK]
  have : Group.IsPerfect L := hL
  exact (commutator_eq_self (H := L)).symm.le.trans hcomm

end CFSG.ComponentClassification.LBalance.Core
