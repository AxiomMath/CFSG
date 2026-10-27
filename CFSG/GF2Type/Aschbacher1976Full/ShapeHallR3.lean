module

public import CFSG.GF2Type.Aschbacher1976Full.ShapeHallR2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

section Msub

variable {P : Type*} [Group P] [Finite P] {D E R : Subgroup P} {z : P} {a : P} {k : ℕ}

def Msub (c : CritData D E R z) : Subgroup P where
  carrier := {m | ∀ y ∈ Zof D, m * y * m⁻¹ * y⁻¹ ∈ zpowers z}
  one_mem' := fun y _ => by simp
  mul_mem' := fun {m m'} hm hm' y hy => by
    have h1 : (m * m') * y * (m * m')⁻¹ * y⁻¹ =
        (m * (m' * y * m'⁻¹ * y⁻¹) * m⁻¹) * (m * y * m⁻¹ * y⁻¹) := by group
    rw [h1, conj_zpowers_central c.z_center (hm' y hy) m]
    exact mul_mem (hm' y hy) (hm y hy)
  inv_mem' := fun {m} hm y hy => by
    have h1 : m⁻¹ * y * m⁻¹⁻¹ * y⁻¹ = m⁻¹ * (m * y * m⁻¹ * y⁻¹)⁻¹ * m := by group
    have h2 := conj_zpowers_central c.z_center (inv_mem (hm y hy)) m⁻¹
    rw [inv_inv] at h2
    rw [h1, h2]
    exact inv_mem (hm y hy)

theorem Msub_char (c : CritData D E R z) : (Msub c).Characteristic := by
  refine characteristic_of_forall_mem fun φ m hm y hy => ?_
  have hy' : φ.symm y ∈ Zof D := char_apply_mem c.char φ.symm hy
  have h := hm _ hy'
  have hz : φ z = z := by
    refine c.z_uniq _ (char_apply_mem c.char φ c.z_mem) ?_
    exact (orderOf_injective φ.toMonoidHom φ.injective z).trans c.z_ord
  have h2 : φ (m * φ.symm y * m⁻¹ * (φ.symm y)⁻¹) = φ m * y * (φ m)⁻¹ * y⁻¹ := by
    simp [map_mul, map_inv]
  rw [← h2]
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp h
  exact mem_zpowers_iff.mpr ⟨n, by rw [← hn, map_zpow, hz]⟩

theorem D_le_Msub (c : CritData D E R z) : D ≤ Msub c := by
  intro d hd y hy
  have : d * y * d⁻¹ = y := by
    rw [mul_inv_eq_iff_eq_mul]
    exact CritData.Z_comm D hy hd
  rw [this, mul_inv_cancel]
  exact one_mem _

theorem Gen.zpow_z (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) (n : ℤ) :
    z ^ n = a ^ ((2 : ℤ) ^ (k - 1) * n) := by
  rw [hg.z_eq c hk, ← zpow_natCast, ← zpow_mul]
  congr 1

theorem Gen.tau_eq (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) :
    a ^ ((1 : ℤ) + 2 ^ (k - 1)) = a * z := by
  rw [zpow_add, zpow_one]
  congr 1
  have := hg.zpow_z c hk 1
  rw [zpow_one, mul_one] at this
  exact this.symm

theorem Gen.x_mem_Msub (c : CritData D E R z) (hg : Gen c a k) (hk : 1 ≤ k) {x : P}
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) : x ∈ Msub c := by
  intro y hy
  obtain ⟨n, rfl⟩ := hg.gen y hy
  have h : a ^ (((1 : ℤ) + 2 ^ (k - 1)) * n) * (a ^ n)⁻¹ = z ^ n := by
    rw [hg.zpow_z c hk n, ← zpow_neg, ← zpow_add]
    congr 1
    ring
  rw [conj_zpow_eq hxτ n, h]
  exact zpow_mem (mem_zpowers z) n

theorem Gen.Msub_cases (c : CritData D E R z) (hg : Gen c a k) (hk : 2 ≤ k) {x : P}
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) {m : P} (hm : m ∈ Msub c) :
    m ∈ D ∨ x⁻¹ * m ∈ D := by
  have hzc : ∀ g : P, g * z = z * g := mem_center_iff.mp c.z_center
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [c.z_ord, pow_two] at this
    exact this
  have hza : z * a = a * z := (CritData.Z_comm D c.z_mem (CritData.Z_le_D D hg.mem)).symm
  have hxinv := hg.x_act_inv c (by omega) hxτ
  rcases eq_one_or_eq_of_mem_zpowers_two c.z_ord (hm a hg.mem) with h1 | h1
  · left
    rw [hg.mem_D_iff c]
    exact mul_inv_eq_one.mp h1
  · right
    rw [hg.mem_D_iff c]
    have hma : m * a * m⁻¹ = z * a := mul_inv_eq_iff_eq_mul.mp h1
    have e : x⁻¹ * (z * a) * x = z * (x⁻¹ * a * x) := by
      rw [← mul_assoc x⁻¹ z a, hzc x⁻¹]
      group
    calc (x⁻¹ * m) * a * (x⁻¹ * m)⁻¹ = x⁻¹ * (m * a * m⁻¹) * x := by group
      _ = x⁻¹ * (z * a) * x := by rw [hma]
      _ = z * (x⁻¹ * a * x) := e
      _ = z * (a * z) := by rw [hxinv, hg.tau_eq c (by omega)]
      _ = a := by rw [← mul_assoc, hza, mul_assoc, hz2, mul_one]

theorem Gen.Msub_comm_C2 (c : CritData D E R z) (hg : Gen c a k) {m : P} (hm : m ∈ Msub c)
    {w : P} (hw : w ∈ zpowers (a ^ 2)) : m * w = w * m := by
  have hza : z * a = a * z := (CritData.Z_comm D c.z_mem (CritData.Z_le_D D hg.mem)).symm
  have hu := hm a hg.mem
  have hma : m * a * m⁻¹ = (m * a * m⁻¹ * a⁻¹) * a := by group
  have hcomm : Commute (m * a * m⁻¹ * a⁻¹) a := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hu
    rw [← hn]
    exact Commute.zpow_left hza n
  have hu2 : (m * a * m⁻¹ * a⁻¹) ^ 2 = 1 := sq_eq_one_of_mem_zpowers c.z_ord hu
  have h2 : m * a ^ 2 * m⁻¹ = a ^ 2 := by
    calc m * a ^ 2 * m⁻¹ = (m * a * m⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = ((m * a * m⁻¹ * a⁻¹) * a) ^ 2 := by rw [← hma]
      _ = (m * a * m⁻¹ * a⁻¹) ^ 2 * a ^ 2 := hcomm.mul_pow 2
      _ = a ^ 2 := by rw [hu2, one_mul]
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hw
  have : m * (a ^ 2) ^ j * m⁻¹ = (a ^ 2) ^ j := by rw [← conj_zpow, h2]
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem Gen.comm_Msub (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) {x : P} (hxR : x ∈ R)
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) (hx2 : x ^ 2 ∈ D) (f : P) {m : P}
    (hm : m ∈ Msub c) : f * m * f⁻¹ * m⁻¹ ∈ zpowers (a ^ 2) := by
  rcases hg.Msub_cases c (by omega) hxτ hm with hmD | hd'
  · exact hg.comm_D_mem c hk f hmD
  · obtain ⟨d', hd'D, rfl⟩ : ∃ d' ∈ D, m = x * d' := ⟨x⁻¹ * m, hd', by group⟩
    have h1 := hg.comm_P_x c hk hxR hxτ hx2 f
    have h2 := hg.comm_D_mem c hk f hd'D
    have h3 : f * (x * d') * f⁻¹ * (x * d')⁻¹ =
        (f * x * f⁻¹ * x⁻¹) * (x * (f * d' * f⁻¹ * d'⁻¹) * x⁻¹) := by group
    rw [h3]
    exact mul_mem h1 ((hg.C2_normal c (by omega)).conj_mem _ h2 x)

theorem Gen.sq_Msub (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k) {x : P} (hxR : x ∈ R)
    (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1))) (hx2 : x ^ 2 ∈ D) {m : P}
    (hm : m ∈ Msub c) : m ^ 2 ∈ zpowers (a ^ 2) := by
  rcases hg.Msub_cases c (by omega) hxτ hm with hmD | hd'
  · exact hg.sq_D_mem c (by omega) hmD
  · obtain ⟨d', hd'D, rfl⟩ : ∃ d' ∈ D, m = x * d' := ⟨x⁻¹ * m, hd', by group⟩
    have h1 : x ^ 2 ∈ zpowers (a ^ 2) := by
      obtain ⟨c', hc'⟩ := hg.sq_x_mem c (by omega) hxR hxτ hx2
      rw [hc']
      exact zpow_mem_zpowers_sq a c'
    have h2 : x⁻¹ * d' * x * d'⁻¹ ∈ zpowers (a ^ 2) := by
      have := hg.comm_D_mem c hk x⁻¹ hd'D
      rwa [inv_inv] at this
    have h3 := hg.sq_D_mem c (by omega) hd'D
    have h4 : (x * d') ^ 2 = x ^ 2 * (x⁻¹ * d' * x * d'⁻¹) * d' ^ 2 := by
      simp only [pow_two]
      group
    rw [h4]
    exact mul_mem (mul_mem h1 h2) h3

theorem critical_Msub (hP : IsPGroup 2 P) (c : CritData D E R z) (hg : Gen c a k) (hk : 3 ≤ k)
    {x : P} (hxR : x ∈ R) (hxτ : x * a * x⁻¹ = a ^ ((1 : ℤ) + 2 ^ (k - 1)))
    (hx2 : x ^ 2 ∈ D) : ThompsonCritical (Msub c) := by
  have hC2 : zpowers (a ^ 2) ≤ Msub c ⊓ centralizer ((Msub c : Subgroup P) : Set P) := by
    refine le_inf ?_ ?_
    · exact (hg.C2_le_Z c).trans ((CritData.Z_le_D D).trans (D_le_Msub c))
    · intro w hw
      rw [mem_centralizer_iff]
      intro m hm
      exact hg.Msub_comm_C2 c hm hw
  have hcomm : ∀ f m : P, m ∈ Msub c → f * m * f⁻¹ * m⁻¹ ∈ Msub c ⊓
      centralizer ((Msub c : Subgroup P) : Set P) :=
    fun f m hm => hC2 (hg.comm_Msub c hk hxR hxτ hx2 f hm)
  unfold ThompsonCritical IsThompsonCritical
  refine ⟨Msub_char c, ?_, ?_, ?_⟩
  · haveI : Fact (IsPGroup 2 ↥(Msub c)) := ⟨hP.to_subgroup _⟩
    refine le_trans ?_ hC2
    rw [Subgroup.map_le_iff_le_comap, frattini_eq_closure_commutator_union_powers (p := 2),
      Subgroup.closure_le]
    rintro g (hg' | ⟨y, rfl⟩)
    · have hcom : commutator ↥(Msub c) ≤ (zpowers (a ^ 2)).comap (Msub c).subtype := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro u _ v _
        exact hg.comm_Msub c hk hxR hxτ hx2 (u : P) v.2
      exact hcom hg'
    · exact hg.sq_Msub c hk hxR hxτ hx2 y.2
  · refine Subgroup.commutator_le.mpr fun f _ m hm => hcomm f m hm
  · have hle : centralizer ((Msub c : Subgroup P) : Set P) ≤ Msub c := by
      have h1 : centralizer ((Msub c : Subgroup P) : Set P) ≤ centralizer (D : Set P) :=
        Subgroup.centralizer_le (D_le_Msub c)
      have h2 : centralizer (D : Set P) ≤ D := by
        have := c.crit.2.2.2
        exact this.le.trans inf_le_left
      exact h1.trans (h2.trans (D_le_Msub c))
    exact le_antisymm (le_inf hle le_rfl) inf_le_right

theorem exists_critical_gt (hP : IsPGroup 2 P) (c : CritData D E R z) (hg : Gen c a k)
    (hk : 3 ≤ k) {x : P} (hxR : x ∈ R) (hxD : x ∉ D) (hx2 : x ^ 2 ∈ D)
    (hx4 : x * a ^ ((2 : ℤ) ^ (k - 2)) * x⁻¹ = a ^ ((2 : ℤ) ^ (k - 2))) :
    ∃ M : Subgroup P, ThompsonCritical M ∧ D < M := by
  have hxτ := hg.x_act c hk hxD hx2 hx4
  refine ⟨Msub c, critical_Msub hP c hg hk hxR hxτ hx2, lt_of_le_of_ne (D_le_Msub c) ?_⟩
  intro h
  exact hxD (h ▸ hg.x_mem_Msub c (by omega) hxτ)

theorem hallR (hP : IsPGroup 2 P) (c : CritData D E R z)
    (hmax : ∀ D' : Subgroup P, ThompsonCritical D' → Nat.card D' ≤ Nat.card D)
    (hk8 : 8 ≤ Nat.card (Zof D)) {g : P} (hg : ∀ y ∈ Zof D, y ^ 4 = 1 → g * y * g⁻¹ = y) :
    g ∈ D := by
  obtain ⟨a, k, hag⟩ := exists_gen hP c
  have hk : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hag.card] at this
    omega
  by_contra hgD
  haveI := c.R_normal
  have hgER : g ∈ E ⊔ R := by rw [c.ER]; exact mem_top g
  obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hgER
  have hrD : r ∉ D := fun h => hgD (mul_mem (c.E_le_D he) h)
  have hrfix : ∀ y ∈ Zof D, y ^ 4 = 1 → r * y = y * r := by
    intro y hy hy4
    have h1 := hg y hy hy4
    have h2 : e * y * e⁻¹ = y := by
      rw [mul_inv_eq_iff_eq_mul]
      exact CritData.Z_comm D hy (c.E_le_D he)
    have h3 : r * y * r⁻¹ = y := by
      calc r * y * r⁻¹ = e⁻¹ * ((e * r) * y * (e * r)⁻¹) * e := by group
        _ = e⁻¹ * y * e := by rw [h1]
        _ = e⁻¹ * (e * y * e⁻¹) * e := by rw [h2]
        _ = y := by group
    rwa [mul_inv_eq_iff_eq_mul] at h3
  obtain ⟨n, hn⟩ := hP r
  have hex : ∃ n, r ^ (2 ^ n) ∈ D := ⟨n, by rw [hn]; exact one_mem _⟩
  classical
  have hn₀ : r ^ (2 ^ Nat.find hex) ∈ D := Nat.find_spec hex
  have hn₀pos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, pow_one] at hn₀
    exact hrD hn₀
  obtain ⟨i, hi⟩ : ∃ i, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hxD : r ^ (2 ^ i) ∉ D := Nat.find_min hex (by omega)
  have hx2 : (r ^ (2 ^ i)) ^ 2 ∈ D := by
    rw [hi] at hn₀
    rwa [← pow_mul, ← pow_succ]
  have hxR : r ^ (2 ^ i) ∈ R := pow_mem hr _
  have hyZ : a ^ ((2 : ℤ) ^ (k - 2)) ∈ Zof D := zpow_mem hag.mem _
  have hy4 : (a ^ ((2 : ℤ) ^ (k - 2))) ^ 4 = 1 := by
    have h1 : (a ^ ((2 : ℤ) ^ (k - 2))) ^ 4 = a ^ ((2 : ℤ) ^ k) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      push_cast
      ring_nf
    have h2 : a ^ ((2 : ℤ) ^ k) = a ^ (0 : ℤ) :=
      (zpow_eq_zpow_iff_dvd hag.ord).mpr (by simp)
    rw [h1, h2, zpow_zero]
  have hx4 : r ^ (2 ^ i) * a ^ ((2 : ℤ) ^ (k - 2)) * (r ^ (2 ^ i))⁻¹ =
      a ^ ((2 : ℤ) ^ (k - 2)) := by
    rw [mul_inv_eq_iff_eq_mul]
    exact ((Commute.pow_left (hrfix _ hyZ hy4 : Commute r _) (2 ^ i))).eq
  obtain ⟨M, hM, hDM⟩ := exists_critical_gt hP c hag hk hxR hxD hx2 hx4
  exact absurd (hmax M hM) (not_le.mpr (Subgroup.card_lt_of_lt hDM))

end Msub

end CFSG.GF2Type.Aschbacher1976Full.Shape
