module

public import CFSG.LargeExtraspecial.S3Thompson

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup

variable {O : Type*} [Group O]

theorem eq_one_or_eq_of_mem_zpowers {t x : O} (htt : t * t = 1) (hx : x ∈ zpowers t) :
    x = 1 ∨ x = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, htt]
  rcases Int.even_or_odd k with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · left
    rw [← two_mul, zpow_mul, ht2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one]

structure WeakSetting (X : Subgroup O) (t : O) (N : Subgroup O) : Prop where
  t_mem : t ∈ X
  tt : t * t = 1
  t1 : t ≠ 1
  N_le : N ≤ X
  t_mem_N : t ∈ N
  N_comm : ∀ n ∈ N, n * t = t * n
  N_norm : ∀ h ∈ X, h * t = t * h → ∀ n ∈ N, h * n * h⁻¹ ∈ N
  comm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ ∈ zpowers t
  center : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) → x = 1 ∨ x = t
  sq : ∀ x ∈ N, x * x ∈ zpowers t
  self : ∀ h ∈ X, (∀ n ∈ N, h * n * h⁻¹ * n⁻¹ ∈ zpowers t) → h ∈ N
  nonab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a

namespace WeakSetting

variable {X : Subgroup O} {t : O} {N : Subgroup O} (W : WeakSetting X t N)
include W

theorem comm_eq {x y : O} (hx : x ∈ N) (hy : y ∈ N) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = t :=
  eq_one_or_eq_of_mem_zpowers W.tt (W.comm x hx y hy)

theorem zpowers_comm {z n : O} (hz : z ∈ zpowers t) (hn : n ∈ N) : z * n = n * z := by
  rcases eq_one_or_eq_of_mem_zpowers W.tt hz with rfl | rfl
  · rw [one_mul, mul_one]
  · exact (W.N_comm n hn).symm

theorem zpowers_comm' {z₁ z₂ : O} (h₁ : z₁ ∈ zpowers t) (h₂ : z₂ ∈ zpowers t) :
    z₁ * z₂ = z₂ * z₁ := by
  rcases eq_one_or_eq_of_mem_zpowers W.tt h₁ with rfl | rfl
  · rw [one_mul, mul_one]
  · rcases eq_one_or_eq_of_mem_zpowers W.tt h₂ with rfl | rfl
    · rw [one_mul, mul_one]
    · rfl

theorem t_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right W.tt

theorem comm_mul_left {a b c : O} (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N) :
    (a * b) * c * (a * b)⁻¹ * c⁻¹ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹) := by
  have hk := W.comm b hb c hc
  have h1 : (b * c * b⁻¹ * c⁻¹) * a = a * (b * c * b⁻¹ * c⁻¹) := W.zpowers_comm hk ha
  calc (a * b) * c * (a * b)⁻¹ * c⁻¹ = a * (b * c * b⁻¹ * c⁻¹) * (c * a⁻¹ * c⁻¹) := by group
    _ = b * c * b⁻¹ * c⁻¹ * a * (c * a⁻¹ * c⁻¹) := by rw [h1]
    _ = (b * c * b⁻¹ * c⁻¹) * (a * c * a⁻¹ * c⁻¹) := by group
    _ = (a * c * a⁻¹ * c⁻¹) * (b * c * b⁻¹ * c⁻¹) := W.zpowers_comm' hk (W.comm a ha c hc)

omit W in
theorem comm_inv (a b : O) : (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ := by group

theorem comm_mul_right {a b c : O} (ha : a ∈ N) (hb : b ∈ N) (hc : c ∈ N) :
    a * (b * c) * a⁻¹ * (b * c)⁻¹ = (a * b * a⁻¹ * b⁻¹) * (a * c * a⁻¹ * c⁻¹) := by
  have h := W.comm_mul_left hb hc ha
  have e1 : a * (b * c) * a⁻¹ * (b * c)⁻¹ = ((b * c) * a * (b * c)⁻¹ * a⁻¹)⁻¹ := by group
  rw [e1, h, mul_inv_rev, comm_inv, comm_inv]
  exact W.zpowers_comm' (W.comm a ha c hc) (W.comm a ha b hb)

omit W in
theorem comm_eq_one_iff (a b : O) : a * b * a⁻¹ * b⁻¹ = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  · intro h
    rw [h]; group

theorem exists_comm_eq_t {x : O} (hx : x ∈ N) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    ∃ a ∈ N, a * x * a⁻¹ * x⁻¹ = t := by
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ N, a * x ≠ x * a := by
    by_contra h
    push Not at h
    rcases W.center x hx (fun y hy => (h y hy).symm) with h1 | h1
    · exact hx1 h1
    · exact hxt h1
  exact ⟨a, ha, (W.comm_eq ha hx).resolve_left fun h => hax ((comm_eq_one_iff a x).mp h)⟩

theorem t_mem_of_relIndex_eq_two {F : Subgroup O} (hF : F.relIndex N = 2) : t ∈ F := by
  obtain ⟨a, ha, b, hb, hab⟩ := W.nonab
  have hc : a * b * a⁻¹ * b⁻¹ = t :=
    (W.comm_eq ha hb).resolve_left fun h => hab ((comm_eq_one_iff a b).mp h)
  rw [← hc]
  have h1 := mul_mem_iff_of_relIndex_eq_two hF (mul_mem (mul_mem ha hb) (inv_mem ha))
    (inv_mem hb)
  have h2 := mul_mem_iff_of_relIndex_eq_two hF (mul_mem ha hb) (inv_mem ha)
  have h3 := mul_mem_iff_of_relIndex_eq_two hF ha hb
  rw [h1, h2, h3, inv_mem_iff, inv_mem_iff]
  tauto

theorem relIndex_centralizer_eq_two {x : O} (hx : x ∈ N) (hx1 : x ≠ 1) (hxt : x ≠ t) :
    (N ⊓ centralizer ({x} : Set O)).relIndex N = 2 := by
  obtain ⟨a, ha, hat⟩ := W.exists_comm_eq_t hx hx1 hxt
  have hiff : ∀ b ∈ N, b ∈ N ⊓ centralizer ({x} : Set O) ↔ b * x * b⁻¹ * x⁻¹ = 1 := by
    intro b hb
    rw [mem_inf, mem_centralizer_singleton_iff, comm_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨hb, h⟩⟩
  rw [relIndex_eq_two_iff]
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hiff _ (mul_mem hb ha), hiff _ hb, W.comm_mul_left hb ha hx, hat]
  rcases W.comm_eq hb hx with h | h
  · rw [h, one_mul]
    simp [W.t1]
  · rw [h, W.tt]
    simp [W.t1]

theorem mem_centralizer_centralizer {x : O} (hx : x ∈ N) (hx1 : x ≠ 1) (hxt : x ≠ t) {y : O}
    (hy : y ∈ N) (hyc : ∀ b ∈ N, b * x = x * b → y * b = b * y) :
    y = 1 ∨ y = t ∨ y = x ∨ y = x * t := by
  obtain ⟨a, ha, hat⟩ := W.exists_comm_eq_t hx hx1 hxt
  have hsplit : ∀ b ∈ N, b * x * b⁻¹ * x⁻¹ = 1 ∨ (b * a) * x * (b * a)⁻¹ * x⁻¹ = 1 := by
    intro b hb
    rcases W.comm_eq hb hx with h | h
    · exact Or.inl h
    · right
      rw [W.comm_mul_left hb ha hx, h, hat, W.tt]
  have hya : ∀ b ∈ N, b * x * b⁻¹ * x⁻¹ = 1 → y * b * y⁻¹ * b⁻¹ = 1 := fun b hb h =>
    (comm_eq_one_iff y b).mpr (hyc b hb ((comm_eq_one_iff b x).mp h))
  have hyb : ∀ b ∈ N, (b * a) * x * (b * a)⁻¹ * x⁻¹ = 1 →
      y * b * y⁻¹ * b⁻¹ = y * a * y⁻¹ * a⁻¹ := by
    intro b hb h
    have h1 := hya _ (mul_mem hb ha) h
    rw [W.comm_mul_right hy hb ha] at h1
    rcases W.comm_eq hy ha with h2 | h2 <;> rcases W.comm_eq hy hb with h3 | h3
    · rw [h2, h3]
    · rw [h2, h3, mul_one] at h1; exact absurd h1 W.t1
    · rw [h2, h3, one_mul] at h1; exact absurd h1 W.t1
    · rw [h2, h3]
  rcases W.comm_eq hy ha with h | h
  ·
    rcases W.center y hy (fun b hb => (comm_eq_one_iff y b).mp (by
      rcases hsplit b hb with h' | h'
      · exact hya b hb h'
      · rw [hyb b hb h', h])) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  ·
    have hxa : x * a * x⁻¹ * a⁻¹ = t := by rw [← comm_inv, hat, W.t_inv]
    have hxb : ∀ b ∈ N, (b * a) * x * (b * a)⁻¹ * x⁻¹ = 1 → x * b * x⁻¹ * b⁻¹ = t := by
      intro b hb hba
      rw [W.comm_mul_left hb ha hx, hat] at hba
      have : b * x * b⁻¹ * x⁻¹ = t := by
        rw [← mul_one (b * x * b⁻¹ * x⁻¹), ← W.tt, ← mul_assoc, hba, one_mul]
      rw [← comm_inv, this, W.t_inv]
    have hc : ∀ b ∈ N, (y * x) * b = b * (y * x) := by
      intro b hb
      rw [← comm_eq_one_iff, W.comm_mul_left hy hx hb]
      rcases hsplit b hb with h' | h'
      · rw [hya b hb h', (comm_eq_one_iff x b).mpr ((comm_eq_one_iff b x).mp h').symm, one_mul]
      · rw [hyb b hb h', h, hxb b hb h', W.tt]
    have hxx : x * x = 1 ∨ x * x = t := eq_one_or_eq_of_mem_zpowers W.tt (W.sq x hx)
    rcases W.center _ (mul_mem hy hx) hc with h' | h'
    · right; right
      rcases hxx with hxx | hxx
      · left
        calc y = y * x * x := by rw [mul_assoc, hxx, mul_one]
          _ = x := by rw [h', one_mul]
      · right
        calc y = y * x * x * t := by rw [mul_assoc y x x, hxx, mul_assoc, W.tt, mul_one]
          _ = x * t := by rw [h', one_mul]
    · right; right
      rcases hxx with hxx | hxx
      · right
        calc y = y * x * x := by rw [mul_assoc, hxx, mul_one]
          _ = x * t := by rw [h', ← W.N_comm x hx]
      · left
        calc y = y * x * x * t := by rw [mul_assoc y x x, hxx, mul_assoc, W.tt, mul_one]
          _ = x := by rw [h', ← W.N_comm x hx, mul_assoc, W.tt, mul_one]

theorem mem_of_commute {h : O} (hX : h ∈ X) (hc : ∀ n ∈ N, h * n = n * h) : h ∈ N :=
  W.self h hX fun n hn => by rw [(comm_eq_one_iff h n).mpr (hc n hn)]; exact one_mem _

theorem pow_four_eq_one {x : O} (hx : x ∈ N) : x ^ 4 = 1 := by
  have h : x ^ 4 = (x * x) * (x * x) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  rcases eq_one_or_eq_of_mem_zpowers W.tt (W.sq x hx) with h' | h' <;> rw [h, h']
  · rw [one_mul]
  · exact W.tt

theorem mem_of_sq_eq_one_of_commute {F : Subgroup O} (hFN : F ≤ N) (hF : F.relIndex N = 2)
    {x : O} (hxX : x ∈ X) (hxx : x * x = 1) (hxF : ∀ f ∈ F, x * f = f * x) : x ∈ N := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxt : x * t = t * x := hxF t (W.t_mem_of_relIndex_eq_two hF)
  by_contra hxN
  obtain ⟨w, hwN, hxw⟩ : ∃ w ∈ N, x * w ≠ w * x := by
    by_contra h
    push Not at h
    exact hxN (W.mem_of_commute hxX h)
  have hwF : w ∉ F := fun h => hxw (hxF w h)
  have hconjN : ∀ v ∈ N, x * v * x⁻¹ ∈ N := W.N_norm x hxX hxt
  set c := x * w * x⁻¹ * w⁻¹ with hc
  have hcN : c ∈ N := mul_mem (hconjN w hwN) (inv_mem hwN)
  have hc1 : c ≠ 1 := fun h => hxw ((comm_eq_one_iff x w).mp h)
  have hfx : ∀ f ∈ F, x * f * x⁻¹ = f := fun f hf => by rw [hxF f hf]; group
  have key : ∀ v ∈ N, v ∉ F → x * v * x⁻¹ * v⁻¹ = c := by
    intro v hvN hvF
    have hf : w⁻¹ * v ∈ F :=
      (mul_mem_iff_of_relIndex_eq_two hF (inv_mem hwN) hvN).mpr
        ⟨fun h => absurd (inv_inv w ▸ F.inv_mem h) hwF, fun h => absurd h hvF⟩
    calc x * v * x⁻¹ * v⁻¹
        = x * w * x⁻¹ * (x * (w⁻¹ * v) * x⁻¹) * (w⁻¹ * v)⁻¹ * w⁻¹ := by group
      _ = c := by rw [hfx _ hf, hc]; group
  have hcF : ∀ f ∈ F, f * c = c * f := by
    intro f hf
    have hfw : f * w ∉ F := fun h =>
      hwF ((mul_mem_iff_of_relIndex_eq_two hF (hFN hf) hwN).mp h |>.mp hf)
    have h1 := key _ (mul_mem (hFN hf) hwN) hfw
    have h2 : x * (f * w) * x⁻¹ * (f * w)⁻¹ = f * c * f⁻¹ := by
      calc x * (f * w) * x⁻¹ * (f * w)⁻¹
          = (x * f * x⁻¹) * (x * w * x⁻¹ * w⁻¹) * f⁻¹ := by group
        _ = f * c * f⁻¹ := by rw [hfx f hf]
    rw [h2] at h1
    calc f * c = f * c * f⁻¹ * f := by group
      _ = c * f := by rw [h1]
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    have hxw' : x * w * x⁻¹ = c * w := by rw [hc]; group
    have h3 : w = x * c * x⁻¹ * (c * w) := by
      calc w = x * (x * w * x⁻¹) * x⁻¹ := by
            rw [show x * (x * w * x⁻¹) * x⁻¹ = (x * x) * w * (x * x)⁻¹ by group, hxx]; group
        _ = x * (c * w) * x⁻¹ := by rw [hxw']
        _ = x * c * x⁻¹ * (x * w * x⁻¹) := by group
        _ = x * c * x⁻¹ * (c * w) := by rw [hxw']
    calc x * c * x⁻¹ = x * c * x⁻¹ * (c * w) * w⁻¹ * c⁻¹ := by group
      _ = c⁻¹ := by rw [← h3]; group
  by_cases hcF' : c ∈ F
  ·
    have hcc : c⁻¹ = c := by rw [← hxc, hfx c hcF']
    have hcomm : ∀ v ∈ N, c * v = v * c := by
      intro v hvN
      by_cases hvF : v ∈ F
      · exact (hcF v hvF).symm
      · have hv2 : v * v ∈ F := (mul_mem_iff_of_relIndex_eq_two hF hvN hvN).mpr Iff.rfl
        have hxv : x * v * x⁻¹ = c * v := by
          calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
            _ = c * v := by rw [key v hvN hvF]
        have h4 : c * v * (c * v) = v * v := by
          rw [← hxv]
          calc x * v * x⁻¹ * (x * v * x⁻¹) = x * (v * v) * x⁻¹ := by group
            _ = v * v := hfx _ hv2
        calc c * v = c * v * (c * v) * v⁻¹ * c⁻¹ := by group
          _ = v * c := by rw [h4, hcc]; group
    have hct : c = t := (W.center c hcN hcomm).resolve_left hc1
    apply hxN
    refine W.self x hxX fun v hvN => ?_
    by_cases hvF : v ∈ F
    · rw [hfx v hvF, mul_inv_cancel]; exact one_mem _
    · rw [key v hvN hvF, hct]; exact mem_zpowers t
  ·
    have h5 := key c hcN hcF'
    have h6 : c ^ 3 = 1 := by
      have h7 : x * c * x⁻¹ = c * c := by
        calc x * c * x⁻¹ = x * c * x⁻¹ * c⁻¹ * c := by group
          _ = c * c := by rw [h5]
      rw [hxc] at h7
      calc c ^ 3 = c * (c * c) := pow_three c
        _ = 1 := by rw [← h7]; group
    apply hc1
    have h8 : c ^ 4 = c ^ 3 * c := pow_succ c 3
    rw [W.pow_four_eq_one hcN, h6, one_mul] at h8
    exact h8.symm

end WeakSetting

theorem mem_map_conj_iff {N : Subgroup O} {k z : O} :
    z ∈ N.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * z * k ∈ N := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    simpa [mul_assoc] using hn
  · intro h
    exact ⟨k⁻¹ * z * k, h, by simp [mul_assoc]⟩

theorem mem_zpowers_conj_iff {t k z : O} :
    z ∈ zpowers (k * t * k⁻¹) ↔ k⁻¹ * z * k ∈ zpowers t := by
  have h := MonoidHom.map_zpowers (MulAut.conj k).toMonoidHom t
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  rw [← h, mem_map_conj_iff]

namespace WeakSetting

variable {X : Subgroup O} {t : O} {N : Subgroup O} (W : WeakSetting X t N)
include W

theorem conj {k : O} (hk : k ∈ X) :
    WeakSetting X (k * t * k⁻¹) (N.map (MulAut.conj k).toMonoidHom) := by
  have hmem : ∀ {z : O}, z ∈ N.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * z * k ∈ N :=
    mem_map_conj_iff
  have hzp : ∀ {z : O}, z ∈ zpowers (k * t * k⁻¹) ↔ k⁻¹ * z * k ∈ zpowers t :=
    mem_zpowers_conj_iff
  have hkt : k⁻¹ * (k * t * k⁻¹) * k = t := by group
  refine ⟨mul_mem (mul_mem hk W.t_mem) (inv_mem hk), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [W.tt]; group
  · intro h
    apply W.t1
    calc t = k⁻¹ * (k * t * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  · intro z hz
    have h := W.N_le (hmem.mp hz)
    have : z = k * (k⁻¹ * z * k) * k⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hk h) (inv_mem hk)
  · rw [hmem, hkt]; exact W.t_mem_N
  · intro z hz
    have h := W.N_comm _ (hmem.mp hz)
    calc z * (k * t * k⁻¹) = k * ((k⁻¹ * z * k) * t) * k⁻¹ := by group
      _ = k * (t * (k⁻¹ * z * k)) * k⁻¹ := by rw [h]
      _ = (k * t * k⁻¹) * z := by group
  · intro h hX hht z hz
    rw [hmem]
    have hh' : k⁻¹ * h * k * t = t * (k⁻¹ * h * k) := by
      calc k⁻¹ * h * k * t = k⁻¹ * (h * (k * t * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * t * k⁻¹) * h) * k := by rw [hht]
        _ = t * (k⁻¹ * h * k) := by group
    have := W.N_norm _ (mul_mem (mul_mem (inv_mem hk) hX) hk) hh' _ (hmem.mp hz)
    convert this using 1
    group
  · intro x hx y hy
    rw [hzp]
    convert W.comm _ (hmem.mp hx) _ (hmem.mp hy) using 1
    group
  · intro x hx hxc
    have h := W.center _ (hmem.mp hx) fun y hy => by
      have e := hxc (k * y * k⁻¹) (by rw [hmem]; simpa [mul_assoc] using hy)
      have := congrArg (fun w => k⁻¹ * w * k) e
      simpa [mul_assoc] using this
    rcases h with h | h
    · left
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = 1 := by rw [h]; group
    · right
      calc x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        _ = k * t * k⁻¹ := by rw [h]
  · intro x hx
    rw [hzp]
    convert W.sq _ (hmem.mp hx) using 1
    group
  · intro h hX hh
    rw [hmem]
    refine W.self _ (mul_mem (mul_mem (inv_mem hk) hX) hk) fun n hn => ?_
    have := hh (k * n * k⁻¹) (by rw [hmem]; simpa [mul_assoc] using hn)
    rw [hzp] at this
    convert this using 1
    group
  · obtain ⟨a, ha, b, hb, hab⟩ := W.nonab
    refine ⟨k * a * k⁻¹, by rw [hmem]; simpa [mul_assoc] using ha, k * b * k⁻¹,
      by rw [hmem]; simpa [mul_assoc] using hb, fun h => hab ?_⟩
    have := congrArg (fun w => k⁻¹ * w * k) h
    simpa [mul_assoc] using this

end WeakSetting

end CFSG.LargeExtraspecial.S14
