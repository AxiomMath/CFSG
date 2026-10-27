module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_congr_modEq {p : ℕ} {x : G} (hx : x ^ p = 1) {a b : ℕ} (h : a ≡ b [MOD p]) :
    x ^ a = x ^ b :=
  pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) h)

omit [Finite G] in
theorem mem_zpowers_of_mem_zpowers_of_prime {p : ℕ} (hp : p.Prime) {g w : G} (hg : orderOf g = p)
    (hw : w ∈ Subgroup.zpowers g) (hw1 : w ≠ 1) : g ∈ Subgroup.zpowers w := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_prime_card hcard
    (g := ⟨w, hw⟩) (g' := ⟨g, Subgroup.mem_zpowers g⟩) fun h => hw1 (congrArg Subtype.val h))
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

@[expose] def fusionSet (R : Subgroup G) (z : G) : Set G :=
  {w | w ≠ 1 ∧ ∃ n ∈ Subgroup.normalizer (R : Set G), w ∈ Subgroup.zpowers (n * z * n⁻¹)}

omit [Finite G] in
theorem fusionSet_subset {R : Subgroup G} {z : G} (hzR : z ∈ R) : fusionSet R z ⊆ R := by
  rintro w ⟨-, n, hn, hw⟩
  have h1 : n * z * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn z).mp hzR
  exact (Subgroup.zpowers_le.mpr h1) hw

omit [Finite G] in
theorem conj_mem_fusionSet {R : Subgroup G} {z w n : G} (hn : n ∈ Subgroup.normalizer (R : Set G))
    (hw : w ∈ fusionSet R z) : n * w * n⁻¹ ∈ fusionSet R z := by
  obtain ⟨hw1, m, hm, hwm⟩ := hw
  refine ⟨fun h => hw1 ?_, n * m, Subgroup.mul_mem _ hn hm, ?_⟩
  · calc w = n⁻¹ * (n * w * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hwm
  have : n * (m * z * m⁻¹) ^ j * n⁻¹ = (n * m * z * (n * m)⁻¹) ^ j := by
    rw [← conj_zpow]
    group
  rw [this]
  exact Subgroup.zpow_mem_zpowers _ j

omit [Finite G] in
theorem pow_mem_fusionSet {R : Subgroup G} {z w : G} (hw : w ∈ fusionSet R z) {m : ℕ}
    (hm : w ^ m ≠ 1) :
    w ^ m ∈ fusionSet R z := by
  obtain ⟨-, n, hn, hwn⟩ := hw
  exact ⟨hm, n, hn, Subgroup.pow_mem _ hwn m⟩

omit [Finite G] in
theorem self_mem_fusionSet {R : Subgroup G} {z : G} (hz1 : z ≠ 1) : z ∈ fusionSet R z :=
  ⟨hz1, 1, Subgroup.one_mem _, by simp⟩

theorem p_dvd_ncard_fusionSet {p : ℕ} [Fact p.Prime] {R : Subgroup G} {z x : G}
    (hzp : orderOf z = p) (hxN : x ∈ Subgroup.normalizer (R : Set G)) {k : ℕ}
    (hxk : x ^ p ^ k = 1) (hxR : x ∉ R)
    (hSyl : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z = z * y → y ^ p ^ k = 1 → y ∈ R) :
    p ∣ (fusionSet R z).ncard := by
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (R : Set G) := Subgroup.zpowers_le.mpr hxN
  let act : MulAction (Subgroup.zpowers x) (fusionSet R z) :=
    { smul := fun g w => ⟨(g : G) * w * (g : G)⁻¹, conj_mem_fusionSet (hle g.2) w.2⟩
      one_smul := fun w => Subtype.ext (show ((1 : Subgroup.zpowers x) : G) * w *
        ((1 : Subgroup.zpowers x) : G)⁻¹ = w by simp)
      mul_smul := fun g h w => Subtype.ext (show ((g * h : Subgroup.zpowers x) : G) * w *
        ((g * h : Subgroup.zpowers x) : G)⁻¹ = g * (h * w * (h : G)⁻¹) * (g : G)⁻¹ by
          simp only [Subgroup.coe_mul]; group) }
  have hpg : IsPGroup p (Subgroup.zpowers x) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hxk)
    exact ⟨j, hj⟩
  have hmod := hpg.card_modEq_card_fixedPoints (fusionSet R z)
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers x) (fusionSet R z)) = 0 := by
    rw [Nat.card_eq_zero]
    left
    refine ⟨fun ⟨w, hw⟩ => ?_⟩
    have h1 := hw ⟨x, Subgroup.mem_zpowers x⟩
    have hxw : x * (w : G) * x⁻¹ = w := congrArg Subtype.val h1
    obtain ⟨hw1, n, hn, hwn⟩ := w.2
    have hnzo : orderOf (n * z * n⁻¹) = p := by
      have := orderOf_injective (MulAut.conj n).toMonoidHom (MulAut.conj n).injective z
      rw [← hzp, ← this]
      rfl
    have hnz := mem_zpowers_of_mem_zpowers_of_prime (Fact.out) hnzo hwn hw1
    have hxc : x * (n * z * n⁻¹) * x⁻¹ = n * z * n⁻¹ := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hnz
      rw [← hj, ← conj_zpow, hxw]
    apply hxR
    have hy := hSyl (n⁻¹ * x * n) (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn)
      hxN) hn) (by
        calc n⁻¹ * x * n * z = n⁻¹ * (x * (n * z * n⁻¹) * x⁻¹) * x * n := by group
          _ = n⁻¹ * (n * z * n⁻¹) * x * n := by rw [hxc]
          _ = z * (n⁻¹ * x * n) := by group) (by
        have h2 : (n⁻¹ * x * n) ^ p ^ k = n⁻¹ * x ^ p ^ k * n := by
          have := conj_pow (a := n⁻¹) (b := x) (i := p ^ k)
          simpa using this
        rw [h2, hxk]
        group)
    have : x = n * (n⁻¹ * x * n) * n⁻¹ := by group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp hn _).mp hy
  rw [hfix] at hmod
  rw [← Nat.card_coe_set_eq]
  exact Nat.dvd_of_mod_eq_zero hmod

@[expose] def commPlane {p : ℕ} (hp : 0 < p) {z t : G} (hc : Commute z t) (hz : z ^ p = 1)
    (ht : t ^ p = 1) : Subgroup G where
  carrier := {g | ∃ i j : ℕ, g = z ^ i * t ^ j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    refine ⟨i + i', j + j', ?_⟩
    rw [pow_add, pow_add]
    have h1 : Commute (t ^ j) (z ^ i') := (hc.pow_pow i' j).symm
    calc z ^ i * t ^ j * (z ^ i' * t ^ j') = z ^ i * (t ^ j * z ^ i') * t ^ j' := by group
      _ = z ^ i * (z ^ i' * t ^ j) * t ^ j' := by rw [h1.eq]
      _ = z ^ i * z ^ i' * (t ^ j * t ^ j') := by group
  one_mem' := ⟨0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    refine ⟨i * (p - 1), j * (p - 1), ?_⟩
    have hpw : ∀ {g : G}, g ^ p = 1 → ∀ k : ℕ, (g ^ k)⁻¹ = g ^ (k * (p - 1)) := by
      intro g hg k
      rw [inv_eq_iff_mul_eq_one, ← pow_add]
      have : k + k * (p - 1) = k * p := by
        have h1 : p = (p - 1) + 1 := by omega
        conv_rhs => rw [h1]
        ring
      rw [this, pow_mul', hg, one_pow]
    rw [mul_inv_rev, hpw ht j, hpw hz i]
    exact ((hc.pow_pow _ _).symm).eq

omit [Finite G] in
theorem card_commPlane_le {p : ℕ} (hp : 0 < p) {z t : G} (hc : Commute z t) (hz : z ^ p = 1)
    (ht : t ^ p = 1) : Nat.card (commPlane hp hc hz ht) ≤ p ^ 2 := by
  let f : Fin p × Fin p → commPlane hp hc hz ht := fun ij =>
    ⟨z ^ (ij.1 : ℕ) * t ^ (ij.2 : ℕ), ⟨ij.1, ij.2, rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, i, j, rfl⟩
    refine ⟨⟨⟨i % p, Nat.mod_lt _ hp⟩, ⟨j % p, Nat.mod_lt _ hp⟩⟩, Subtype.ext ?_⟩
    show z ^ (i % p) * t ^ (j % p) = z ^ i * t ^ j
    rw [pow_congr_modEq hz (Nat.mod_modEq i p), pow_congr_modEq ht (Nat.mod_modEq j p)]
  have := Nat.card_le_card_of_surjective f hf
  rwa [Nat.card_prod, Nat.card_fin, ← sq] at this

omit [Finite G] in
theorem isElemAbelian_commPlane {p : ℕ} (hp : 0 < p) {z t : G} (hc : Commute z t)
    (hz : z ^ p = 1) (ht : t ^ p = 1) : IsElemAbelian p (commPlane hp hc hz ht) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨i, j, hij⟩ := a.2
    obtain ⟨i', j', hij'⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hij, hij']
    have h1 : Commute (z ^ i * t ^ j) (z ^ i' * t ^ j') :=
      ((Commute.pow_pow_self z i i').mul_right (hc.pow_pow i j')).mul_left
        (((hc.pow_pow i' j).symm).mul_right (Commute.pow_pow_self t j j'))
    exact h1.eq
  · rintro _ ⟨i, j, rfl⟩
    rw [(hc.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul,
      hz, ht, one_pow, one_pow, one_mul]

end CFSG.AGLEmbedding
