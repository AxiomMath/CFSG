module

public import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.AGLEmbedding

open Equiv MulAction

variable {α : Type*} [Finite α] {E : Subgroup (Perm α)}

omit [Finite α] in
theorem mem_orbit_perm_iff {y z : α} : z ∈ orbit E y ↔ ∃ f ∈ E, f y = z :=
  ⟨fun ⟨f, hf⟩ => ⟨f, f.2, hf⟩, fun ⟨f, hf, hfy⟩ => ⟨⟨f, hf⟩, hfy⟩⟩

omit [Finite α] in
theorem apply_mem_orbit_of_mem {f : Perm α} (hf : f ∈ E) {y z : α} (hz : z ∈ orbit E y) :
    f z ∈ orbit E y := by
  rw [← orbit_eq_iff.mpr hz]
  exact mem_orbit_perm_iff.mpr ⟨f, hf, rfl⟩

omit [Finite α] in
theorem apply_mem_orbit_of_mem_normalizer {g : Perm α}
    (hg : g ∈ Subgroup.normalizer (E : Set (Perm α))) {y z : α} (hz : z ∈ orbit E y) :
    g z ∈ orbit E (g y) := by
  obtain ⟨f, hf, rfl⟩ := mem_orbit_perm_iff.mp hz
  exact mem_orbit_perm_iff.mpr ⟨g * f * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg f).mp hf,
    by simp [Perm.mul_apply]⟩

omit [Finite α] in
theorem pow_apply_mem_orbit {g : Perm α} (hg : g ∈ Subgroup.normalizer (E : Set (Perm α)))
    {y : α} (hgy : g y ∈ orbit E y) (u : ℕ) : (g ^ u) y ∈ orbit E y := by
  induction u with
  | zero => exact mem_orbit_self y
  | succ u ih =>
    rw [pow_succ', Perm.mul_apply, ← orbit_eq_iff.mpr hgy]
    exact apply_mem_orbit_of_mem_normalizer hg ih

omit [Finite α] in
theorem conj_apply_eq_of_forall_apply_eq {g : Perm α}
    (hg : g ∈ Subgroup.normalizer (E : Set (Perm α))) {y : α} (hy : ∀ f ∈ E, f y = y)
    {e : Perm α} (he : e ∈ E) : (g * e * g⁻¹) y = e y := by
  have h1 : g (e (g⁻¹ y)) = y := by
    simpa [Perm.mul_apply] using hy _ ((Subgroup.mem_normalizer_iff.mp hg e).mp he)
  rw [hy e he, Perm.mul_apply, Perm.mul_apply, h1]

theorem card_orbit_eq_one_or_eq {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E)
    (hα : Nat.card α < p ^ 2) (y : α) :
    Nat.card (orbit E y) = 1 ∨ Nat.card (orbit E y) = p := by
  obtain ⟨k, hk⟩ := hE.card_orbit y
  have hle : Nat.card (orbit E y) ≤ Nat.card α := Finite.card_subtype_le _
  rw [hk] at hle ⊢
  have hk2 : k < 2 :=
    (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp (lt_of_le_of_lt hle hα)
  interval_cases k <;> simp

theorem orbit_zpowers_eq {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) {y : α}
    (hO : Nat.card (orbit E y) = p) {f : Perm α} (hf : f ∈ E) {z : α} (hz : z ∈ orbit E y)
    (hfz : f z ≠ z) : orbit (Subgroup.zpowers f) z = orbit E y := by
  have hsub : orbit (Subgroup.zpowers f) z ⊆ orbit E y := by
    rintro v ⟨⟨g, hg⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact apply_mem_orbit_of_mem (zpow_mem hf i) hz
  obtain ⟨k, hk⟩ := (hE.to_le (Subgroup.zpowers_le.mpr hf)).card_orbit z
  have hne : Nat.card (orbit (Subgroup.zpowers f) z) ≠ 1 := by
    intro h1
    rw [Nat.card_coe_set_eq] at h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hz1 : z ∈ orbit (Subgroup.zpowers f) z := mem_orbit_self z
    have hz2 : f z ∈ orbit (Subgroup.zpowers f) z := ⟨⟨f, Subgroup.mem_zpowers f⟩, rfl⟩
    rw [ha, Set.mem_singleton_iff] at hz1 hz2
    exact hfz (hz2.trans hz1.symm)
  refine Set.eq_of_subset_of_ncard_le hsub ?_
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hO, hk]
  rw [hk] at hne
  rcases k with _ | k
  · exact absurd (pow_zero p) hne
  · exact Nat.le_self_pow (Nat.succ_ne_zero k) p

theorem apply_eq_of_apply_eq_of_mem_orbit {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) {y : α}
    (hO : Nat.card (orbit E y) = p) {f : Perm α} (hf : f ∈ E) {z : α} (hz : z ∈ orbit E y)
    (hfz : f z = z) {w : α} (hw : w ∈ orbit E y) : f w = w := by
  by_contra hfw
  rw [← orbit_zpowers_eq hE hO hf hw hfw] at hz
  obtain ⟨⟨g, hg⟩, hgz⟩ := hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hgz' : (f ^ i) w = z := hgz
  have h1 : (f ^ (-i)) z = z := Perm.zpow_apply_eq_self_of_apply_eq_self hfz _
  have hwz : w = z :=
    calc w = (f ^ (-i)) ((f ^ i) w) := by simp [zpow_neg]
      _ = z := by rw [hgz', h1]
  exact hfw (by rw [hwz, hfz])

theorem apply_eq_apply_of_mem_orbit {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) {y : α}
    (hO : Nat.card (orbit E y) = p) {f g : Perm α} (hf : f ∈ E) (hg : g ∈ E) {z : α}
    (hz : z ∈ orbit E y) (hfg : f z = g z) {w : α} (hw : w ∈ orbit E y) : f w = g w := by
  have h1 := apply_eq_of_apply_eq_of_mem_orbit hE hO (mul_mem (inv_mem hg) hf) hz
    (by rw [Perm.mul_apply, hfg]; simp) hw
  rw [Perm.mul_apply, Perm.inv_eq_iff_eq] at h1
  exact h1

theorem minimalPeriod_eq_of_mem_orbit {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) {y : α}
    (hO : Nat.card (orbit E y) = p) {f : Perm α} (hf : f ∈ E) {z : α} (hz : z ∈ orbit E y)
    (hfz : f z ≠ z) : Function.minimalPeriod (f • ·) z = p := by
  classical
  let : Fintype (orbit (Subgroup.zpowers f) z) := Fintype.ofFinite _
  rw [minimalPeriod_eq_card, ← Nat.card_eq_fintype_card, orbit_zpowers_eq hE hO hf hz hfz, hO]

omit [Finite α] in
theorem pow_apply_eq_pow_apply {c d : Perm α} (hd : d ∈ E) {y : α}
    (hcd : ∀ w ∈ orbit E y, c w = d w) (m : ℕ) : ∀ w ∈ orbit E y, (c ^ m) w = (d ^ m) w := by
  induction m with
  | zero => simp
  | succ m ih =>
    intro w hw
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, hcd w hw,
      ih _ (apply_mem_orbit_of_mem hd hw)]

omit [Finite α] in
theorem conj_pow_apply_eq {h : Perm α} {y : α} (hinv : ∀ w ∈ orbit E y, h⁻¹ w ∈ orbit E y)
    {e₀ : Perm α} (he₀ : e₀ ∈ E) {k : ℕ} (hk : ∀ w ∈ orbit E y, (h * e₀ * h⁻¹) w = (e₀ ^ k) w)
    (j : ℕ) : ∀ w ∈ orbit E y, (h ^ j * e₀ * (h ^ j)⁻¹) w = (e₀ ^ (k ^ j)) w := by
  induction j with
  | zero => simp
  | succ j ih =>
    intro w hw
    have h1 : (h ^ (j + 1) * e₀ * (h ^ (j + 1))⁻¹) w = h ((h ^ j * e₀ * (h ^ j)⁻¹) (h⁻¹ w)) := by
      rw [pow_succ', mul_inv_rev]
      simp only [Perm.mul_apply]
    rw [h1, ih _ (hinv w hw), pow_succ', pow_mul,
      ← pow_apply_eq_pow_apply (pow_mem he₀ k) hk _ w hw, conj_pow]
    simp only [Perm.mul_apply]

omit [Finite α] in
theorem pow_apply_eq_of_pow_pow_apply_eq {p N k : ℕ} [Fact p.Prime] {f : Perm α} {z : α}
    (hper : Function.minimalPeriod (f • ·) z = p) (hN : N.Coprime (p - 1)) (hN0 : N ≠ 0)
    (h : (f ^ (k ^ N)) z = f z) : (f ^ k) z = f z := by
  have key : ∀ m : ℕ, (f ^ m) z = f z ↔ (m : ZMod p) = 1 := by
    intro m
    have e1 : (f ^ m) z = f z ↔ f ^ ((m : ℤ) - 1) • z = z := by
      rw [sub_eq_neg_add, zpow_add, zpow_neg_one, zpow_natCast, mul_smul, Perm.smul_def,
        Perm.smul_def, Perm.inv_eq_iff_eq, eq_comm]
    rw [e1, zpow_smul_eq_iff_minimalPeriod_dvd, hper,
      ← ZMod.intCast_eq_intCast_iff_dvd_sub 1 (m : ℤ) p, eq_comm]
    push_cast
    rfl
  rw [key] at h ⊢
  push_cast at h
  have h0 : (k : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, zero_pow hN0] at h
    exact zero_ne_one h
  have h2 := ZMod.pow_card_sub_one_eq_one h0
  have h3 : (k : ZMod p) ^ N.gcd (p - 1) = 1 := pow_gcd_eq_one.mpr ⟨h, h2⟩
  rwa [hN, pow_one] at h3

theorem apply_mem_orbit_of_card_lt {p : ℕ} {y : α} (hO : Nat.card (orbit E y) = p)
    (hα : Nat.card α < 4 * p) {h : Perm α} (hh : h ∈ Subgroup.normalizer (E : Set (Perm α)))
    (h6 : (orderOf h).Coprime 6) : h y ∈ orbit E y := by
  have key : ∀ d : ℕ, 0 < d → d ≤ 3 → (h ^ d) y ∈ orbit E y → h y ∈ orbit E y := by
    intro d hd0 hd3 hd
    have hd6 : d ∣ 6 := by interval_cases d <;> norm_num
    obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime (h6.coprime_dvd_right hd6).symm
    rw [← hu]
    exact pow_apply_mem_orbit (pow_mem hh d) hd u
  by_contra hcon
  have hdis : ∀ i j : ℕ, i < j → j ≤ 3 → orbit E ((h ^ i) y) ≠ orbit E ((h ^ j) y) := by
    intro i j hij hj heq
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    refine hcon (key d (by omega) (by omega) ?_)
    have h1 : (h ^ (i + d)) y ∈ orbit E ((h ^ i) y) := heq ▸ mem_orbit_self _
    simpa [pow_add, Perm.mul_apply] using
      apply_mem_orbit_of_mem_normalizer (inv_mem (pow_mem hh i)) h1
  let F : Fin 4 × orbit E y → α := fun x => (h ^ (x.1 : ℕ)) x.2
  have hF : Function.Injective F := by
    rintro ⟨i, z, hz⟩ ⟨j, z', hz'⟩ hij
    have hij : (h ^ (i : ℕ)) z = (h ^ (j : ℕ)) z' := hij
    have hi : orbit E ((h ^ (i : ℕ)) y) = orbit E ((h ^ (j : ℕ)) y) := by
      rw [← orbit_eq_iff.mpr (apply_mem_orbit_of_mem_normalizer (pow_mem hh _) hz),
        ← orbit_eq_iff.mpr (apply_mem_orbit_of_mem_normalizer (pow_mem hh _) hz'), hij]
    have hi4 := i.2
    have hj4 := j.2
    obtain rfl : i = j := by
      rcases lt_trichotomy (i : ℕ) j with h1 | h1 | h1
      · exact absurd hi (hdis _ _ h1 (by omega))
      · exact Fin.ext h1
      · exact absurd hi.symm (hdis _ _ h1 (by omega))
    obtain rfl : z = z' := (h ^ (i : ℕ)).injective hij
    rfl
  have h4 := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_fin, hO] at h4
  omega

theorem conj_apply_eq_of_mem_orbit {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E) {y : α}
    (hO : Nat.card (orbit E y) = p) {h : Perm α}
    (hh : h ∈ Subgroup.normalizer (E : Set (Perm α))) (hhy : h y ∈ orbit E y)
    (hp1 : (orderOf h).Coprime (p - 1)) {e : Perm α} (he : e ∈ E) :
    (h * e * h⁻¹) y = e y := by
  have hp := (Fact.out : p.Prime).two_le
  have hy : y ∈ orbit E y := mem_orbit_self y
  have hinv : ∀ w ∈ orbit E y, h⁻¹ w ∈ orbit E y := by
    have h0 : y ∈ orbit E (h y) := by rw [orbit_eq_iff.mpr hhy]; exact hy
    have h1 : h⁻¹ y ∈ orbit E y := by
      simpa using apply_mem_orbit_of_mem_normalizer (inv_mem hh) h0
    intro w hw
    rw [← orbit_eq_iff.mpr h1]
    exact apply_mem_orbit_of_mem_normalizer (inv_mem hh) hw
  obtain ⟨e₀, he₀, hy₀⟩ : ∃ e₀ ∈ E, e₀ y ≠ y := by
    by_contra hcon
    push Not at hcon
    have h1 : orbit E y = {y} := by
      ext z
      refine ⟨fun hz => ?_, fun hz => (Set.mem_singleton_iff.mp hz) ▸ hy⟩
      obtain ⟨f, hf, rfl⟩ := mem_orbit_perm_iff.mp hz
      exact hcon f hf
    rw [h1, Nat.card_unique] at hO
    omega
  have hper := minimalPeriod_eq_of_mem_orbit hE hO he₀ hy hy₀
  have hpow : ∀ f ∈ E, ∃ c : ℕ, ∀ w ∈ orbit E y, f w = (e₀ ^ c) w := by
    intro f hf
    have hfy : f y ∈ orbit (Subgroup.zpowers e₀) y := by
      rw [orbit_zpowers_eq hE hO he₀ hy hy₀]
      exact apply_mem_orbit_of_mem hf hy
    obtain ⟨⟨g, hg⟩, hgy⟩ := hfy
    obtain ⟨c, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
    have hgy : f y = (e₀ ^ c) y := hgy.symm
    exact ⟨c, fun w hw => apply_eq_apply_of_mem_orbit hE hO hf (pow_mem he₀ c) hy hgy hw⟩
  obtain ⟨k, hk⟩ := hpow _ ((Subgroup.mem_normalizer_iff.mp hh e₀).mp he₀)
  have hk1 : ∀ w ∈ orbit E y, (h * e₀ * h⁻¹) w = e₀ w := by
    have hN := conj_pow_apply_eq hinv he₀ hk (orderOf h) y hy
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hN
    have h2 := pow_apply_eq_of_pow_pow_apply_eq hper hp1 (orderOf_pos h).ne' hN.symm
    intro w hw
    rw [hk w hw]
    exact apply_eq_apply_of_mem_orbit hE hO (pow_mem he₀ k) he₀ hy h2 hw
  obtain ⟨c, hc⟩ := hpow e he
  have h3 : (h * e * h⁻¹) y = (h * e₀ ^ c * h⁻¹) y := by
    simp only [Perm.mul_apply]
    rw [hc _ (hinv y hy)]
  rw [h3, ← conj_pow, pow_apply_eq_pow_apply he₀ hk1 c y hy, hc y hy]

theorem conj_eq_of_mem_normalizer_of_card_lt {p : ℕ} [Fact p.Prime] (hE : IsPGroup p E)
    (hα4 : Nat.card α < 4 * p) (hαp : Nat.card α < p ^ 2) {h : Perm α}
    (hh : h ∈ Subgroup.normalizer (E : Set (Perm α))) (h6 : (orderOf h).Coprime 6)
    (hp1 : (orderOf h).Coprime (p - 1)) {e : Perm α} (he : e ∈ E) : h * e * h⁻¹ = e := by
  ext y
  rcases card_orbit_eq_one_or_eq hE hαp y with h1 | hO
  · refine conj_apply_eq_of_forall_apply_eq hh (fun f hf => ?_) he
    rw [Nat.card_coe_set_eq] at h1
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp h1
    have hy1 : y ∈ orbit E y := mem_orbit_self y
    have hy2 : f y ∈ orbit E y := apply_mem_orbit_of_mem hf (mem_orbit_self y)
    rw [ha, Set.mem_singleton_iff] at hy1 hy2
    exact hy2.trans hy1.symm
  · exact conj_apply_eq_of_mem_orbit hE hO hh (apply_mem_orbit_of_card_lt hO hα4 hh h6) hp1 he

end CFSG.AGLEmbedding
