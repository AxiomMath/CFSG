module

public import CFSG.GH74.GLS.Stage2.Local.P27.L4Rel
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Iface
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Dih1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.L4

open Subgroup CFSG.GH74.GLS.Stage2.Local.P27.Psp4
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_dih {r s : G} {M : ℕ} (h : DihPair r s M) {g g' : G}
    (hg : g ∈ zpowers r ⊔ zpowers s) (hg' : g' ∈ zpowers r ⊔ zpowers s) :
    g * g' * g⁻¹ * g'⁻¹ ∈ zpowers (r ^ 2) := by
  have hr2 : ∀ k : ℤ, r ^ (2 * k) ∈ zpowers (r ^ 2) := fun k => by
    refine ⟨k, ?_⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul]; norm_num
  have hconj : ∀ k : ℤ, s * r ^ k * s⁻¹ = r ^ (-k) := fun k => by
    rw [h.s_zpow, mul_inv_cancel_right]
  obtain ⟨j, hj | hj⟩ := h.mem_iff.1 hg'
  · obtain ⟨i, hi | hi⟩ := h.mem_iff.1 hg
    · rw [hi, hj]
      have : r ^ i * r ^ j * (r ^ i)⁻¹ * (r ^ j)⁻¹ = 1 := by
        rw [← zpow_neg, ← zpow_neg, ← zpow_add, ← zpow_add, ← zpow_add]; simp
      rw [this]; exact one_mem _
    · have e : r ^ i * s * r ^ j * (r ^ i * s)⁻¹ = r ^ (-j) := by
        calc r ^ i * s * r ^ j * (r ^ i * s)⁻¹ = r ^ i * (s * r ^ j * s⁻¹) * (r ^ i)⁻¹ := by group
          _ = r ^ i * r ^ (-j) * (r ^ i)⁻¹ := by rw [hconj j]
          _ = r ^ (-j) := by rw [← zpow_neg, ← zpow_add, ← zpow_add]; congr 1; ring
      rw [hi, hj, e, ← zpow_neg, ← zpow_add]
      have : -j + -j = 2 * (-j) := by ring
      rw [this]; exact hr2 _
  · obtain ⟨m, hm⟩ := h.conj_refl hg j
    rw [hj, hm]
    have e : r ^ (j + 2 * m) * s * (r ^ j * s)⁻¹ = r ^ (2 * m) := by
      calc r ^ (j + 2 * m) * s * (r ^ j * s)⁻¹ = r ^ (j + 2 * m) * (s * s⁻¹) * (r ^ j)⁻¹ := by group
        _ = r ^ (j + 2 * m) * (r ^ j)⁻¹ := by rw [mul_inv_cancel, mul_one]
        _ = r ^ (2 * m) := by rw [← zpow_neg, ← zpow_add]; congr 1; ring
    rw [e]; exact hr2 m

theorem comm_prod {D₁ D₂ : Subgroup G} (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    {a a' b b' : G} (ha : a ∈ D₁) (ha' : a' ∈ D₁) (hb : b ∈ D₂) (hb' : b' ∈ D₂) :
    ⁅a * b, a' * b'⁆ = ⁅a, a'⁆ * ⁅b, b'⁆ := by
  let f : D₁ × D₂ →* G := D₁.subtype.noncommCoprod D₂.subtype (fun p q => hc _ p.2 _ q.2)
  have h := map_commutatorElement f ((⟨a, ha⟩ : D₁), (⟨b, hb⟩ : D₂))
    ((⟨a', ha'⟩ : D₁), (⟨b', hb'⟩ : D₂))
  have e : f ⁅((⟨a, ha⟩ : D₁), (⟨b, hb⟩ : D₂)), ((⟨a', ha'⟩ : D₁), (⟨b', hb'⟩ : D₂))⁆ =
      ⁅a, a'⁆ * ⁅b, b'⁆ := rfl
  have e' : ⁅f ((⟨a, ha⟩ : D₁), (⟨b, hb⟩ : D₂)), f ((⟨a', ha'⟩ : D₁), (⟨b', hb'⟩ : D₂))⁆ =
      ⁅a * b, a' * b'⁆ := rfl
  rw [e, e'] at h
  exact h.symm

theorem sq_split {D₁ D₂ : Subgroup G} (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) (hi : D₁ ⊓ D₂ = ⊥)
    {a b : G} (ha : a ∈ D₁) (hb : b ∈ D₂) (h : a * b * (a * b) = 1) : a * a = 1 ∧ b * b = 1 := by
  have h1 : a * b * (a * b) = (a * a) * (b * b) := by
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hc a ha b hb]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
  rw [h1] at h
  have hinv : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hm1 : a * a ∈ D₁ := mul_mem ha ha
  have hm2 : a * a ∈ D₂ := by rw [hinv]; exact inv_mem (mul_mem hb hb)
  have hmem : a * a ∈ D₁ ⊓ D₂ := ⟨hm1, hm2⟩
  rw [hi, mem_bot] at hmem
  refine ⟨hmem, ?_⟩
  rw [hmem, one_mul] at h
  exact h

theorem card_le_four [Finite G] {K : Subgroup G} {p q r s : G}
    (h : ∀ g ∈ K, g = p ∨ g = q ∨ g = r ∨ g = s) : Nat.card ↥K ≤ 4 := by
  have hsub : (K : Set G) ⊆ ({p, q, r, s} : Set G) := by
    intro g hg
    rcases h g hg with rfl | rfl | rfl | rfl <;> simp
  have h1 : Nat.card ↥K = (K : Set G).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [h1]
  calc (K : Set G).ncard ≤ ({p, q, r, s} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 4 := by
      refine (Set.ncard_insert_le p _).trans ?_
      refine Nat.succ_le_succ ((Set.ncard_insert_le q _).trans ?_)
      refine Nat.succ_le_succ ((Set.ncard_insert_le r _).trans ?_)
      rw [Set.ncard_singleton]

theorem cent_split {D₁ D₂ : Subgroup G} (hc : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) (hi : D₁ ⊓ D₂ = ⊥)
    {a b d₁ d₂ : G} (ha : a ∈ D₁) (hb : b ∈ D₂) (hd₁ : d₁ ∈ D₁) (hd₂ : d₂ ∈ D₂)
    (h : a * b * (d₁ * d₂) = d₁ * d₂ * (a * b)) : a * d₁ = d₁ * a ∧ b * d₂ = d₂ * b := by
  have e1 : a * b * (d₁ * d₂) = (a * d₁) * (b * d₂) := by
    calc a * b * (d₁ * d₂) = a * (b * d₁) * d₂ := by simp only [mul_assoc]
      _ = a * (d₁ * b) * d₂ := by rw [← hc d₁ hd₁ b hb]
      _ = (a * d₁) * (b * d₂) := by simp only [mul_assoc]
  have e2 : d₁ * d₂ * (a * b) = (d₁ * a) * (d₂ * b) := by
    calc d₁ * d₂ * (a * b) = d₁ * (d₂ * a) * b := by simp only [mul_assoc]
      _ = d₁ * (a * d₂) * b := by rw [← hc a ha d₂ hd₂]
      _ = (d₁ * a) * (d₂ * b) := by simp only [mul_assoc]
  rw [e1, e2] at h
  have hx : (d₁ * a)⁻¹ * (a * d₁) = (d₂ * b) * (b * d₂)⁻¹ := by
    calc (d₁ * a)⁻¹ * (a * d₁) = (d₁ * a)⁻¹ * ((a * d₁) * (b * d₂)) * (b * d₂)⁻¹ := by group
      _ = (d₁ * a)⁻¹ * ((d₁ * a) * (d₂ * b)) * (b * d₂)⁻¹ := by rw [h]
      _ = (d₂ * b) * (b * d₂)⁻¹ := by group
  have hx1 : (d₁ * a)⁻¹ * (a * d₁) ∈ D₁ := mul_mem (inv_mem (mul_mem hd₁ ha)) (mul_mem ha hd₁)
  have hx2 : (d₁ * a)⁻¹ * (a * d₁) ∈ D₂ := by
    rw [hx]; exact mul_mem (mul_mem hd₂ hb) (inv_mem (mul_mem hb hd₂))
  have hmem : (d₁ * a)⁻¹ * (a * d₁) ∈ D₁ ⊓ D₂ := ⟨hx1, hx2⟩
  rw [hi, mem_bot] at hmem
  constructor
  · have := hmem
    calc a * d₁ = (d₁ * a) * ((d₁ * a)⁻¹ * (a * d₁)) := by group
      _ = d₁ * a := by rw [this, mul_one]
  · have h3 : (d₂ * b) * (b * d₂)⁻¹ = 1 := by rw [← hx]; exact hmem
    calc b * d₂ = ((d₂ * b) * (b * d₂)⁻¹)⁻¹ * (d₂ * b) := by group
      _ = d₂ * b := by rw [h3]; simp

structure Skel (T : Subgroup G) (z u τ x₀ y e : G) (n : ℕ) (Z X : Set G) : Prop where
  core : Core4 z u τ x₀ y e n
  D₁_le : zpowers τ ⊔ zpowers x₀ ≤ T
  D₂_le : zpowers y ⊔ zpowers e ≤ T
  T_le : T ≤ (zpowers τ ⊔ zpowers x₀) ⊔ (zpowers y ⊔ zpowers e)
  u_cent : ∀ g ∈ T, u * g = g * u
  z_cent : ∀ g ∈ T, z * g = g * z
  Z_conj : ∀ g ∈ T, ∀ x ∈ Z, g * x * g⁻¹ ∈ Z
  X_conj : ∀ g ∈ T, ∀ x ∈ X, g * x * g⁻¹ ∈ X
  part : ∀ x ∈ T, x * x = 1 → x ≠ 1 → (x ∈ Z ∨ x ∈ X) ∧ ¬ (x ∈ Z ∧ x ∈ X)
  one_Z : (1 : G) ∉ Z
  z_Z : z ∈ Z
  u_X : u ∈ X
  uz_X : u * z ∈ X
  e_X : e ∈ X
  ue_Z : u * e ∈ Z
  ey_X : e * y ∈ X
  uey_Z : u * (e * y) ∈ Z

namespace Skel

variable {T : Subgroup G} {z u τ x₀ y e : G} {n : ℕ} {Z X : Set G}
  (S : Skel T z u τ x₀ y e n Z X)

include S

theorem n_pos [Finite G] : 0 < n := by
  rw [← S.core.τ_ord]; exact orderOf_pos τ

theorem two_dvd : 2 ∣ n := (Nat.dvd_trans (by norm_num) S.core.four_dvd)

theorem half_ge [Finite G] : 2 ≤ n / 2 := by
  obtain ⟨k, hk⟩ := S.core.four_dvd
  have := S.n_pos
  omega

theorem dih₁ [Finite G] : DihPair τ x₀ (n / 2) where
  one_le := by have := S.half_ge; omega
  ord := by
    rw [S.core.τ_ord]; have := S.two_dvd; omega
  s_sq := S.core.x₀_sq
  s_conj := S.core.x₀_τ

theorem dih₂ [Finite G] : DihPair y e (n / 2) where
  one_le := by have := S.half_ge; omega
  ord := by
    rw [S.core.y_ord]; have := S.two_dvd; omega
  s_sq := S.core.e_sq
  s_conj := S.core.e_y

theorem τ_mem_T : τ ∈ T := S.D₁_le (mem_sup_left (mem_zpowers τ))
theorem y_mem_T : y ∈ T := S.D₂_le (mem_sup_left (mem_zpowers y))
theorem e_mem_T : e ∈ T := S.D₂_le (mem_sup_right (mem_zpowers e))

theorem u_mem_T : u ∈ T := by
  rw [S.core.u_eq]; exact pow_mem S.τ_mem_T _

theorem uz_mem_T : u * z ∈ T := by
  rw [S.core.uz_eq]; exact pow_mem S.y_mem_T _

theorem u_sq [Finite G] : u * u = 1 := by
  rw [S.core.u_eq, ← pow_add]
  have := S.core.τ_ord ▸ pow_orderOf_eq_one τ
  rw [show n / 2 + n / 2 = n by have := S.two_dvd; omega]
  exact this

theorem comm_D12 : ∀ g ∈ zpowers τ ⊔ zpowers x₀, ∀ g' ∈ zpowers y ⊔ zpowers e, g * g' = g' * g :=
  commute_sup_sup S.core.τ_y S.core.τ_e S.core.x₀_y S.core.x₀_e

theorem z_mem_T [Finite G] : z ∈ T := by
  have h1 : u * u * z = z := by rw [S.u_sq, one_mul]
  have : z = u * (u * z) := by rw [← mul_assoc, S.u_sq, one_mul]
  rw [this]
  exact mul_mem S.u_mem_T S.uz_mem_T

theorem cls_refl [Finite G] (i : ℤ) : y ^ i * e ∈ X ∧ u * (y ^ i * e) ∈ Z := by
  have hd := S.dih₂
  have hyT := S.y_mem_T
  have hye : y * e ∈ X ∧ u * (y * e) ∈ Z := by
    have e1 : y * (e * y) * y⁻¹ = y * e := by group
    have e2 : u * (y * e) = y * (u * (e * y)) * y⁻¹ := by
      calc u * (y * e) = u * (y * (e * y) * y⁻¹) := by rw [e1]
        _ = (u * y) * (e * y) * y⁻¹ := by simp only [mul_assoc]
        _ = (y * u) * (e * y) * y⁻¹ := by rw [S.u_cent y hyT]
        _ = y * (u * (e * y)) * y⁻¹ := by simp only [mul_assoc]
    refine ⟨?_, ?_⟩
    · rw [← e1]; exact S.X_conj y hyT _ S.ey_X
    · rw [e2]; exact S.Z_conj y hyT _ S.uey_Z
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' i
  ·
    have hg : y ^ j ∈ T := zpow_mem hyT j
    have e1 : y ^ i * e = y ^ j * e * (y ^ j)⁻¹ := by
      have h1 : e * y ^ (-j) = y ^ j * e := by
        have := hd.s_zpow (-j)
        rwa [neg_neg] at this
      calc y ^ i * e = y ^ j * (y ^ j * e) := by rw [hj, two_mul, zpow_add, mul_assoc]
        _ = y ^ j * (e * y ^ (-j)) := by rw [h1]
        _ = y ^ j * e * (y ^ j)⁻¹ := by rw [zpow_neg, mul_assoc]
    have e2 : u * (y ^ j * e * (y ^ j)⁻¹) = y ^ j * (u * e) * (y ^ j)⁻¹ := by
      calc u * (y ^ j * e * (y ^ j)⁻¹) = (u * y ^ j) * e * (y ^ j)⁻¹ := by simp only [mul_assoc]
        _ = (y ^ j * u) * e * (y ^ j)⁻¹ := by rw [S.u_cent _ hg]
        _ = y ^ j * (u * e) * (y ^ j)⁻¹ := by simp only [mul_assoc]
    rw [e1, e2]
    exact ⟨S.X_conj _ hg _ S.e_X, S.Z_conj _ hg _ S.ue_Z⟩
  ·
    have hg : y ^ j ∈ T := zpow_mem hyT j
    have e1 : y ^ i * e = y ^ j * (y * e) * (y ^ j)⁻¹ := by
      have h1 : e * y ^ (-j) = y ^ j * e := by
        have := hd.s_zpow (-j)
        rwa [neg_neg] at this
      calc y ^ i * e = y ^ j * (y * (y ^ j * e)) := by
            rw [hj, show 2 * j + 1 = j + (1 + j) by ring, zpow_add, zpow_one_add]; simp only [mul_assoc]
        _ = y ^ j * (y * (e * y ^ (-j))) := by rw [h1]
        _ = y ^ j * (y * e) * (y ^ j)⁻¹ := by rw [zpow_neg]; simp only [mul_assoc]
    have e2 : u * (y ^ j * (y * e) * (y ^ j)⁻¹) = y ^ j * (u * (y * e)) * (y ^ j)⁻¹ := by
      calc u * (y ^ j * (y * e) * (y ^ j)⁻¹) = (u * y ^ j) * (y * e) * (y ^ j)⁻¹ := by
            simp only [mul_assoc]
        _ = (y ^ j * u) * (y * e) * (y ^ j)⁻¹ := by rw [S.u_cent _ hg]
        _ = y ^ j * (u * (y * e)) * (y ^ j)⁻¹ := by simp only [mul_assoc]
    rw [e1, e2]
    exact ⟨S.X_conj _ hg _ hye.1, S.Z_conj _ hg _ hye.2⟩

theorem D₂_invol [Finite G] {b : G} (hb : b ∈ zpowers y ⊔ zpowers e) (hb2 : b * b = 1) :
    b = 1 ∨ b = u * z ∨ ∃ i : ℤ, b = y ^ i * e := by
  obtain ⟨i, hi | hi⟩ := S.dih₂.mem_iff.1 hb
  · rw [hi] at hb2
    rcases S.dih₂.zpow_half hb2 with h1 | h1
    · exact Or.inl (hi.trans h1)
    · right; left; rw [hi, h1, S.core.uz_eq]
  · exact Or.inr (Or.inr ⟨i, hi⟩)

theorem D₁_invol [Finite G] {a : G} (ha : a ∈ zpowers τ ⊔ zpowers x₀) (ha2 : a * a = 1) :
    a = 1 ∨ a = u ∨ ∃ i : ℤ, a = τ ^ i * x₀ := by
  obtain ⟨i, hi | hi⟩ := S.dih₁.mem_iff.1 ha
  · rw [hi] at ha2
    rcases S.dih₁.zpow_half ha2 with h1 | h1
    · exact Or.inl (hi.trans h1)
    · right; left; rw [hi, h1, S.core.u_eq]
  · exact Or.inr (Or.inr ⟨i, hi⟩)

theorem D₂_cls [Finite G] {d : G} (hd : d ∈ zpowers y ⊔ zpowers e) (hd2 : d * d = 1) (hd1 : d ≠ 1) :
    d ∈ X ∧ u * d ∈ Z := by
  rcases S.D₂_invol hd hd2 with h1 | h1 | ⟨i, h1⟩
  · exact absurd h1 hd1
  · subst h1
    refine ⟨S.uz_X, ?_⟩
    rw [← mul_assoc, S.u_sq, one_mul]
    exact S.z_Z
  · subst h1
    exact S.cls_refl i

theorem M_xor [Finite G] {m : G} (hm : m ∈ zpowers τ ⊔ (zpowers y ⊔ zpowers e)) (hm2 : m * m = 1)
    (hm1 : m ≠ 1) (hmu : m ≠ u) : ¬ ((m ∈ Z) ↔ (u * m ∈ Z)) := by
  have hcomm : ∀ g ∈ zpowers τ, ∀ g' ∈ zpowers y ⊔ zpowers e, g * g' = g' * g := fun g hg g' hg' =>
    S.comm_D12 g (mem_sup_left hg) g' hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 hm
  have hab : a * a = 1 ∧ b * b = 1 := by
    have h1 : a * b * (a * b) = (a * a) * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [← hcomm a ha b hb]
        _ = (a * a) * (b * b) := by simp only [mul_assoc]
    rw [h1] at hm2
    have hinv : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left hm2
    have hmemD₁ : a * a ∈ zpowers τ ⊔ zpowers x₀ := mul_mem (mem_sup_left ha) (mem_sup_left ha)
    have hmemD₂ : a * a ∈ zpowers y ⊔ zpowers e := by rw [hinv]; exact inv_mem (mul_mem hb hb)
    have hmem : a * a ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) := ⟨hmemD₁, hmemD₂⟩
    rw [S.core.inter, mem_bot] at hmem
    refine ⟨hmem, ?_⟩
    rw [hmem, one_mul] at hm2
    exact hm2
  obtain ⟨hax, hbx⟩ := hab
  have hbT : b ∈ T := S.D₂_le hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
  rcases S.dih₁.zpow_half hax with h1 | h1
  ·
    rw [h1, one_mul] at hm1 ⊢
    have hb1 : b ≠ 1 := hm1
    obtain ⟨hbX, hbZ⟩ := S.D₂_cls hb hbx hb1
    have hbnZ : b ∉ Z := fun hZ => (S.part b hbT hbx hb1).2 ⟨hZ, hbX⟩
    intro hiff
    exact hbnZ (hiff.2 hbZ)
  ·
    rw [h1, ← S.core.u_eq] at hm1 hmu ⊢
    have hb1 : b ≠ 1 := fun e => hmu (by rw [e, mul_one])
    obtain ⟨hbX, hbZ⟩ := S.D₂_cls hb hbx hb1
    have hbnZ : b ∉ Z := fun hZ => (S.part b hbT hbx hb1).2 ⟨hZ, hbX⟩
    intro hiff
    apply hbnZ
    have : u * (u * b) = b := by rw [← mul_assoc, S.u_sq, one_mul]
    rw [← this]
    exact hiff.1 hbZ

theorem T_decomp {g : G} (hg : g ∈ T) :
    ∃ a ∈ zpowers τ ⊔ zpowers x₀, ∃ b ∈ zpowers y ⊔ zpowers e, g = a * b :=
  (mem_sup_iff_of_commute S.comm_D12).1 (S.T_le hg)

theorem zpowers_τ_invol [Finite G] {p : G} (hp : p ∈ zpowers τ) (hp2 : p * p = 1) : p = 1 ∨ p = u := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hp
  rcases S.dih₁.zpow_half hp2 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by rw [h1, S.core.u_eq])

theorem zpowers_y_invol [Finite G] {p : G} (hp : p ∈ zpowers y) (hp2 : p * p = 1) :
    p = 1 ∨ p = u * z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hp
  rcases S.dih₂.zpow_half hp2 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (by rw [h1, S.core.uz_eq])

theorem derived_inv [Finite G] {x : G} (hx : x ∈ ⁅T, T⁆) (hx2 : x * x = 1) : x ∈ zpowers z ⊔ zpowers u := by
  have hN : ⁅T, T⁆ ≤ zpowers (τ ^ 2) ⊔ zpowers (y ^ 2) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a, ha, b, hb, rfl⟩ := S.T_decomp hg₁
    obtain ⟨a', ha', b', hb', rfl⟩ := S.T_decomp hg₂
    rw [comm_prod S.comm_D12 ha ha' hb hb']
    exact mul_mem (mem_sup_left (commutator_dih S.dih₁ ha ha'))
      (mem_sup_right (commutator_dih S.dih₂ hb hb'))
  have hcomm : ∀ g ∈ zpowers (τ ^ 2), ∀ g' ∈ zpowers (y ^ 2), g * g' = g' * g := by
    intro g hg g' hg'
    have hg1 : g ∈ zpowers τ ⊔ zpowers x₀ :=
      mem_sup_left ((zpowers_le.2 (pow_mem (mem_zpowers τ) 2)) hg)
    have hg2 : g' ∈ zpowers y ⊔ zpowers e :=
      mem_sup_left ((zpowers_le.2 (pow_mem (mem_zpowers y) 2)) hg')
    exact S.comm_D12 g hg1 g' hg2
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 (hN hx)
  have hpτ : p ∈ zpowers τ := (zpowers_le.2 (pow_mem (mem_zpowers τ) 2)) hp
  have hqy : q ∈ zpowers y := (zpowers_le.2 (pow_mem (mem_zpowers y) 2)) hq
  obtain ⟨hp2, hq2⟩ := sq_split S.comm_D12 S.core.inter (mem_sup_left hpτ) (mem_sup_left hqy) hx2
  have hzu : zpowers z ⊔ zpowers u ≥ zpowers z := le_sup_left
  have huS : u ∈ zpowers z ⊔ zpowers u := mem_sup_right (mem_zpowers u)
  have hzS : z ∈ zpowers z ⊔ zpowers u := mem_sup_left (mem_zpowers z)
  have huz : u * z ∈ zpowers z ⊔ zpowers u := mul_mem huS hzS
  rcases S.zpowers_τ_invol hpτ hp2 with h1 | h1 <;> rcases S.zpowers_y_invol hqy hq2 with h2 | h2
  · rw [h1, h2, one_mul]; exact one_mem _
  · rw [h1, h2, one_mul]; exact huz
  · rw [h1, h2, mul_one]; exact huS
  · rw [h1, h2, ← mul_assoc, S.u_sq, one_mul]; exact hzS

theorem u_ne_one [Finite G] : u ≠ 1 := by
  rw [S.core.u_eq]
  exact pow_ne_one_of_lt_orderOf (by have := S.half_ge; omega) (by rw [S.core.τ_ord]; have := S.half_ge; omega)

theorem uz_ne_one [Finite G] : u * z ≠ 1 := by
  rw [S.core.uz_eq]
  exact pow_ne_one_of_lt_orderOf (by have := S.half_ge; omega) (by rw [S.core.y_ord]; have := S.half_ge; omega)

theorem uz_sq [Finite G] : (u * z) * (u * z) = 1 := by
  rw [S.core.uz_eq, ← pow_add, show n / 2 + n / 2 = n by have := S.two_dvd; omega, ← S.core.y_ord]
  exact pow_orderOf_eq_one y

theorem uz_cent {g : G} (hg : g ∈ T) : (u * z) * g = g * (u * z) := by
  calc (u * z) * g = u * (z * g) := by rw [mul_assoc]
    _ = u * (g * z) := by rw [S.z_cent g hg]
    _ = (u * g) * z := by rw [mul_assoc]
    _ = (g * u) * z := by rw [S.u_cent g hg]
    _ = g * (u * z) := by rw [mul_assoc]

theorem notZ_of_X {x : G} (hxT : x ∈ T) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hX : x ∈ X) : x ∉ Z :=
  fun hZ => (S.part x hxT hx2 hx1).2 ⟨hZ, hX⟩

theorem refl₂_mem_T [Finite G] (j : ℤ) : y ^ j * e ∈ T :=
  S.D₂_le (S.dih₂.refl_mem_D j)

theorem refl₂_ne_one [Finite G] (j : ℤ) : y ^ j * e ≠ 1 := by
  intro h1
  apply S.dih₂.refl_ne_rot S.core.e_not j 0
  rw [h1, zpow_zero]

theorem card_cent_le_16 [Finite G] (i j : ℤ) :
    Nat.card ↥(T ⊓ centralizer ({(τ ^ i * x₀) * (y ^ j * e)} : Set G)) ≤ 16 := by
  have hd₁ : τ ^ i * x₀ ∈ zpowers τ ⊔ zpowers x₀ := S.dih₁.refl_mem_D i
  have hd₂ : y ^ j * e ∈ zpowers y ⊔ zpowers e := S.dih₂.refl_mem_D j
  let C₁ : Subgroup G := (zpowers τ ⊔ zpowers x₀) ⊓ centralizer ({τ ^ i * x₀} : Set G)
  let C₂ : Subgroup G := (zpowers y ⊔ zpowers e) ⊓ centralizer ({y ^ j * e} : Set G)
  have hcomm : ∀ g ∈ C₁, ∀ g' ∈ C₂, g * g' = g' * g := fun g hg g' hg' =>
    S.comm_D12 g hg.1 g' hg'.1
  have hinf : C₁ ⊓ C₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) := ⟨hx.1.1, hx.2.1⟩
    rw [S.core.inter] at hx'
    exact hx'
  have h1 : Nat.card ↥C₁ ≤ 4 := by
    refine card_le_four (p := 1) (q := τ ^ (n / 2)) (r := τ ^ i * x₀) (s := τ ^ (n / 2) * (τ ^ i * x₀)) ?_
    intro g hg
    exact (S.dih₁.centralizer_refl i hg.1).1 (mem_centralizer_singleton_iff.1 hg.2)
  have h2 : Nat.card ↥C₂ ≤ 4 := by
    refine card_le_four (p := 1) (q := y ^ (n / 2)) (r := y ^ j * e) (s := y ^ (n / 2) * (y ^ j * e)) ?_
    intro g hg
    exact (S.dih₂.centralizer_refl j hg.1).1 (mem_centralizer_singleton_iff.1 hg.2)
  have hle : T ⊓ centralizer ({(τ ^ i * x₀) * (y ^ j * e)} : Set G) ≤ C₁ ⊔ C₂ := by
    intro g hg
    obtain ⟨hgT, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨a', ha', b', hb', rfl⟩ := S.T_decomp hgT
    have hc : a' * b' * ((τ ^ i * x₀) * (y ^ j * e)) = ((τ ^ i * x₀) * (y ^ j * e)) * (a' * b') :=
      mem_centralizer_singleton_iff.1 hgc
    obtain ⟨e1, e2⟩ := cent_split S.comm_D12 S.core.inter ha' hb' hd₁ hd₂ hc
    exact mul_mem (mem_sup_left ⟨ha', mem_centralizer_singleton_iff.2 e1⟩)
      (mem_sup_right ⟨hb', mem_centralizer_singleton_iff.2 e2⟩)
  calc Nat.card ↥(T ⊓ centralizer ({(τ ^ i * x₀) * (y ^ j * e)} : Set G)) ≤ Nat.card ↥(C₁ ⊔ C₂) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card ↥C₁ * Nat.card ↥C₂ := card_sup_of_commute hcomm hinf
    _ ≤ 4 * 4 := Nat.mul_le_mul h1 h2
    _ = 16 := by norm_num

theorem w0_good [Finite G] {a : ℕ} (ha : 3 ≤ a) {w0 : G} (hw0T : w0 ∈ T) (hw0sq : w0 * w0 = 1)
    (hw0Z : w0 ∈ Z) (hw0z : w0 ≠ z) (huw0Z : u * w0 ∈ Z)
    (hcard : 2 ^ (a + 2) ≤ Nat.card ↥(T ⊓ centralizer ({w0} : Set G))) :
    ∃ (i : ℤ) (c : G), (c = 1 ∨ c = u * z) ∧ w0 = τ ^ i * x₀ * c := by
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := S.T_decomp hw0T
  obtain ⟨h1, h2⟩ := sq_split S.comm_D12 S.core.inter hd₁ hd₂ hw0sq
  rcases S.D₁_invol hd₁ h1 with h1' | h1' | ⟨i, h1'⟩
  ·
    rcases S.D₂_invol hd₂ h2 with h2' | h2' | ⟨j, h2'⟩
    · exfalso; rw [h1', h2', mul_one] at hw0Z; exact S.one_Z hw0Z
    · exfalso
      rw [h1', h2', one_mul] at hw0Z
      exact S.notZ_of_X S.uz_mem_T S.uz_sq S.uz_ne_one S.uz_X hw0Z
    · exfalso
      rw [h1', h2', one_mul] at hw0Z
      exact S.notZ_of_X (S.refl₂_mem_T j) (S.dih₂.refl_sq j) (S.refl₂_ne_one j) (S.cls_refl j).1 hw0Z
  ·
    rcases S.D₂_invol hd₂ h2 with h2' | h2' | ⟨j, h2'⟩
    · exfalso
      rw [h1', h2', mul_one] at hw0Z
      exact S.notZ_of_X S.u_mem_T S.u_sq S.u_ne_one S.u_X hw0Z
    · exfalso
      apply hw0z
      rw [h1', h2', ← mul_assoc, S.u_sq, one_mul]
    · exfalso
      rw [h1', h2'] at huw0Z
      have : u * (u * (y ^ j * e)) = y ^ j * e := by rw [← mul_assoc, S.u_sq, one_mul]
      rw [this] at huw0Z
      exact S.notZ_of_X (S.refl₂_mem_T j) (S.dih₂.refl_sq j) (S.refl₂_ne_one j) (S.cls_refl j).1 huw0Z
  ·
    rcases S.D₂_invol hd₂ h2 with h2' | h2' | ⟨j, h2'⟩
    · exact ⟨i, 1, Or.inl rfl, by rw [h1', h2', mul_one]⟩
    · exact ⟨i, u * z, Or.inr rfl, by rw [h1', h2']⟩
    · exfalso
      have := S.card_cent_le_16 i j
      rw [h1', h2'] at hcard
      have h32 : 2 ^ 5 ≤ 2 ^ (a + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem c_mem_D₂ [Finite G] {c : G} (hc : c = 1 ∨ c = u * z) : c ∈ zpowers y ⊔ zpowers e := by
  rcases hc with rfl | rfl
  · exact one_mem _
  · rw [S.core.uz_eq]; exact mem_sup_left (pow_mem (mem_zpowers y) _)

theorem c_cent {c g : G} (hc : c = 1 ∨ c = u * z) (hg : g ∈ T) : c * g = g * c := by
  rcases hc with rfl | rfl
  · simp
  · exact S.uz_cent hg

theorem w0_conj_τ [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c) :
    w0 * τ * w0⁻¹ = τ⁻¹ := by
  have hcτ : c * τ = τ * c := S.c_cent hc S.τ_mem_T
  calc w0 * τ * w0⁻¹ = (τ ^ i * x₀) * (c * τ * c⁻¹) * (τ ^ i * x₀)⁻¹ := by rw [hw0]; group
    _ = (τ ^ i * x₀) * τ * (τ ^ i * x₀)⁻¹ := by
        rw [show c * τ * c⁻¹ = τ by rw [hcτ]; group]
    _ = τ ^ i * (x₀ * τ * x₀⁻¹) * (τ ^ i)⁻¹ := by group
    _ = τ⁻¹ := by rw [S.core.x₀_τ]; group

theorem w0_not_mem [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c) :
    w0 ∉ zpowers τ := by
  intro hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
  have hcD₂ : c⁻¹ ∈ zpowers y ⊔ zpowers e := inv_mem (S.c_mem_D₂ hc)
  have e0 : x₀ = (τ ^ i)⁻¹ * τ ^ k * c⁻¹ := by rw [hk, hw0]; group
  have e1 : (τ ^ (k - i))⁻¹ * x₀ = c⁻¹ := by rw [e0]; group
  have hτk : τ ^ (k - i) ∈ zpowers τ ⊔ zpowers x₀ := mem_sup_left (zpow_mem (mem_zpowers τ) _)
  have hD₁ : (τ ^ (k - i))⁻¹ * x₀ ∈ zpowers τ ⊔ zpowers x₀ :=
    mul_mem (inv_mem hτk) (mem_sup_right (mem_zpowers x₀))
  have hmem' : (τ ^ (k - i))⁻¹ * x₀ ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) :=
    ⟨hD₁, by rw [e1]; exact hcD₂⟩
  rw [S.core.inter, mem_bot] at hmem'
  apply S.core.x₀_not
  have : x₀ = τ ^ (k - i) := by
    calc x₀ = τ ^ (k - i) * ((τ ^ (k - i))⁻¹ * x₀) := by group
      _ = τ ^ (k - i) := by rw [hmem', mul_one]
  rw [this]; exact zpow_mem (mem_zpowers τ) _

theorem dihW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) : DihPair τ w0 (n / 2) where
  one_le := by have := S.half_ge; omega
  ord := by rw [S.core.τ_ord]; have := S.two_dvd; omega
  s_sq := hw0sq
  s_conj := S.w0_conj_τ hc hw0

theorem commW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c) :
    ∀ g ∈ zpowers τ ⊔ zpowers w0, ∀ g' ∈ zpowers y ⊔ zpowers e, g * g' = g' * g := by
  have hw : ∀ g : G, g ∈ T → τ * g = g * τ → x₀ * g = g * x₀ → w0 * g = g * w0 := by
    intro g hg h1 h2
    have hτg : Commute τ g := h1
    have hxg : Commute x₀ g := h2
    have hcg : Commute c g := S.c_cent hc hg
    rw [hw0]
    exact (((hτg.zpow_left i).mul_left hxg).mul_left hcg).eq
  exact commute_sup_sup S.core.τ_y S.core.τ_e
    (hw y S.y_mem_T S.core.τ_y S.core.x₀_y) (hw e S.e_mem_T S.core.τ_e S.core.x₀_e)

theorem interW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) : (zpowers τ ⊔ zpowers w0) ⊓ (zpowers y ⊔ zpowers e) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 hg
  have dW := S.dihW hc hw0 hw0sq
  obtain ⟨k, hk | hk⟩ := dW.mem_iff.1 hg1
  · have : g ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) :=
      ⟨mem_sup_left (hk ▸ zpow_mem (mem_zpowers τ) k), hg2⟩
    rw [S.core.inter, mem_bot] at this
    exact this
  · exfalso
    have hcD₂ : c ∈ zpowers y ⊔ zpowers e := S.c_mem_D₂ hc
    have e1 : τ ^ (k + i) * x₀ = g * c⁻¹ := by rw [hk, hw0]; group
    have hD₁ : τ ^ (k + i) * x₀ ∈ zpowers τ ⊔ zpowers x₀ :=
      mul_mem (mem_sup_left (zpow_mem (mem_zpowers τ) _)) (mem_sup_right (mem_zpowers x₀))
    have hmem' : τ ^ (k + i) * x₀ ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) :=
      ⟨hD₁, by rw [e1]; exact (zpowers y ⊔ zpowers e).mul_mem hg2 ((zpowers y ⊔ zpowers e).inv_mem hcD₂)⟩
    rw [S.core.inter, mem_bot] at hmem'
    apply S.core.x₀_not
    have : x₀ = τ ^ (-(k + i)) := by
      calc x₀ = (τ ^ (k + i))⁻¹ * (τ ^ (k + i) * x₀) := by group
        _ = (τ ^ (k + i))⁻¹ := by rw [hmem', mul_one]
        _ = τ ^ (-(k + i)) := by rw [zpow_neg]
    rw [this]; exact zpow_mem (mem_zpowers τ) _

theorem T_leW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c) :
    T ≤ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) := by
  have hτ : τ ∈ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) :=
    mem_sup_left (mem_sup_left (mem_zpowers τ))
  have hw0' : w0 ∈ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) :=
    mem_sup_left (mem_sup_right (mem_zpowers w0))
  have hτi : τ ^ i ∈ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) := zpow_mem hτ i
  have hcm : c ∈ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) :=
    mem_sup_right (S.c_mem_D₂ hc)
  have hx₀ : x₀ ∈ (zpowers τ ⊔ zpowers w0) ⊔ (zpowers y ⊔ zpowers e) := by
    have : x₀ = (τ ^ i)⁻¹ * w0 * c⁻¹ := by rw [hw0]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hτi) hw0') (inv_mem hcm)
  refine S.T_le.trans (sup_le (sup_le ?_ ?_) le_sup_right)
  · rw [zpowers_le]; exact hτ
  · rw [zpowers_le]; exact hx₀

theorem u_memW [Finite G] {w0 : G} : u ∈ zpowers τ ⊔ zpowers w0 := by
  rw [S.core.u_eq]; exact mem_sup_left (pow_mem (mem_zpowers τ) _)

theorem centerW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) :
    (center ↥(zpowers τ ⊔ zpowers w0)).map (zpowers τ ⊔ zpowers w0).subtype = zpowers u := by
  have dW := S.dihW hc hw0 hw0sq
  have huD : u ∈ zpowers τ ⊔ zpowers w0 := S.u_memW
  apply center_map_eq_of_forall
  · exact zpowers_le.2 huD
  · intro g hg hcent
    rcases (dW.central_iff S.half_ge hg).1 hcent with h | h
    · rw [h]; exact one_mem _
    · rw [h, ← S.core.u_eq]; exact mem_zpowers u
  · intro g hg d hd
    rcases (mem_zpowers_of_sq S.u_sq).1 hg with h | h
    · rw [h, one_mul, mul_one]
    · have h2 : g = τ ^ (n / 2) := by rw [h, S.core.u_eq]
      exact (dW.central_iff S.half_ge (h ▸ huD)).2 (Or.inr h2) d hd

theorem idxW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) : (zpowers τ).relIndex (zpowers τ ⊔ zpowers w0) = 2 := by
  have dW := S.dihW hc hw0 hw0sq
  have hnm := S.w0_not_mem hc hw0
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨w0, mem_sup_right (mem_zpowers w0), fun b hb => ?_⟩
  obtain ⟨k, hk | hk⟩ := dW.mem_iff.1 hb
  · refine Or.inr ⟨by rw [hk]; exact zpow_mem (mem_zpowers τ) k, fun h => hnm ?_⟩
    rw [hk] at h
    have : w0 = (τ ^ k)⁻¹ * (τ ^ k * w0) := by group
    rw [this]
    exact mul_mem (inv_mem (zpow_mem (mem_zpowers τ) k)) h
  · refine Or.inl ⟨?_, fun h => hnm ?_⟩
    · rw [hk, mul_assoc, hw0sq, mul_one]; exact zpow_mem (mem_zpowers τ) k
    · rw [hk] at h
      have : w0 = (τ ^ k)⁻¹ * (τ ^ k * w0) := by group
      rw [this]
      exact mul_mem (inv_mem (zpow_mem (mem_zpowers τ) k)) h

theorem reflW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) {d : G} (hd : d ∈ zpowers τ ⊔ zpowers w0) (hdτ : d ∉ zpowers τ) :
    d * d = 1 := by
  have dW := S.dihW hc hw0 hw0sq
  obtain ⟨k, hk | hk⟩ := dW.mem_iff.1 hd
  · exact absurd (hk ▸ zpow_mem (mem_zpowers τ) k) hdτ
  · rw [hk]; exact dW.refl_sq k

theorem u_derivedW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c) :
    u ∈ ⁅zpowers τ ⊔ zpowers w0, zpowers τ ⊔ zpowers w0⁆ := by
  obtain ⟨q, hq⟩ := S.core.four_dvd
  have hτq : τ ^ q ∈ zpowers τ ⊔ zpowers w0 := mem_sup_left (pow_mem (mem_zpowers τ) q)
  have hw0m : w0 ∈ zpowers τ ⊔ zpowers w0 := mem_sup_right (mem_zpowers w0)
  have e1 : w0 * τ ^ q * w0⁻¹ = (τ⁻¹) ^ q := by
    rw [← S.w0_conj_τ hc hw0, conj_pow]
  have hn2 : n / 2 = 2 * q := by omega
  have key : w0 * τ ^ q * w0⁻¹ * (τ ^ q)⁻¹ = u := by
    rw [e1, inv_pow]
    have : u = τ ^ (2 * q) := by rw [S.core.u_eq, hn2]
    have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right S.u_sq
    calc (τ ^ q)⁻¹ * (τ ^ q)⁻¹ = (τ ^ q * τ ^ q)⁻¹ := by rw [mul_inv_rev]
      _ = (τ ^ (2 * q))⁻¹ := by rw [← pow_add, two_mul]
      _ = u⁻¹ := by rw [this]
      _ = u := hu
  rw [← key]
  exact Subgroup.commutator_mem_commutator hw0m hτq

theorem sepW [Finite G] {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z) (hw0 : w0 = τ ^ i * x₀ * c)
    (hw0sq : w0 * w0 = 1) {s : G} (hs : s ∈ zpowers τ ⊔ zpowers w0) (hsτ : s ∉ zpowers τ) {m : G}
    (hm : m ∈ zpowers τ ⊔ (zpowers y ⊔ zpowers e)) (hm2 : m * m = 1) (hm1 : m ≠ 1) (hmu : m ≠ u) :
    ¬ ((s ∈ Z ↔ m ∈ Z) ∧ (u * s ∈ Z ↔ u * m ∈ Z)) := by
  have dW := S.dihW hc hw0 hw0sq
  obtain ⟨k, hk | hk⟩ := dW.mem_iff.1 hs
  · exact absurd (hk ▸ zpow_mem (mem_zpowers τ) k) hsτ
  obtain ⟨q, hq⟩ := S.core.four_dvd
  have hn2 : n / 2 = 2 * q := by omega
  have hgT : τ ^ (q : ℤ) ∈ T := zpow_mem S.τ_mem_T q
  have hu2 : u = τ ^ ((2 * q : ℕ) : ℤ) := by rw [zpow_natCast, S.core.u_eq, hn2]
  have e2 : w0 * τ ^ (-(q : ℤ)) = τ ^ (q : ℤ) * w0 := by
    have := dW.s_zpow (-(q : ℤ))
    rwa [neg_neg] at this
  have hus : u * s = τ ^ (q : ℤ) * s * (τ ^ (q : ℤ))⁻¹ := by
    rw [hk]
    calc u * (τ ^ k * w0) = τ ^ ((2 * q : ℕ) : ℤ) * (τ ^ k * w0) := by rw [← hu2]
      _ = τ ^ ((q : ℤ) + k + q) * w0 := by
          rw [← mul_assoc, ← zpow_add]; congr 2; push_cast; ring
      _ = τ ^ (q : ℤ) * τ ^ k * (τ ^ (q : ℤ) * w0) := by
          rw [zpow_add, zpow_add]; simp only [mul_assoc]
      _ = τ ^ (q : ℤ) * τ ^ k * (w0 * τ ^ (-(q : ℤ))) := by rw [e2]
      _ = τ ^ (q : ℤ) * (τ ^ k * w0) * (τ ^ (q : ℤ))⁻¹ := by
          rw [zpow_neg]; simp only [mul_assoc]
  have hZ : s ∈ Z ↔ u * s ∈ Z := by
    constructor
    · intro h1; rw [hus]; exact S.Z_conj _ hgT _ h1
    · intro h1
      have h3 := S.Z_conj _ (inv_mem hgT) _ h1
      rw [hus] at h3
      have e : (τ ^ (q : ℤ))⁻¹ * (τ ^ (q : ℤ) * s * (τ ^ (q : ℤ))⁻¹) * ((τ ^ (q : ℤ))⁻¹)⁻¹ = s := by
        group
      rw [e] at h3; exact h3
  rintro ⟨h1, h2⟩
  exact S.M_xor hm hm2 hm1 hmu (h1.symm.trans (hZ.trans h2))

theorem notX_of_Z {x : G} (hxT : x ∈ T) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hZ : x ∈ Z) : x ∉ X :=
  fun hX => (S.part x hxT hx2 hx1).2 ⟨hZ, hX⟩

theorem ub_sq [Finite G] {b : G} (hb : b ∈ zpowers y ⊔ zpowers e) (hb2 : b * b = 1) :
    (u * b) * (u * b) = 1 := by
  have hbT : b ∈ T := S.D₂_le hb
  calc (u * b) * (u * b) = u * (b * u) * b := by simp only [mul_assoc]
    _ = u * (u * b) * b := by rw [← S.u_cent b hbT]
    _ = (u * u) * (b * b) := by simp only [mul_assoc]
    _ = 1 := by rw [S.u_sq, hb2, mul_one]

theorem ub_ne_one [Finite G] {b : G} (hb : b ∈ zpowers y ⊔ zpowers e) : u * b ≠ 1 := by
  intro h
  have hbu : b = u := by
    calc b = u⁻¹ * (u * b) := by group
      _ = u⁻¹ := by rw [h, mul_one]
      _ = u := inv_eq_of_mul_eq_one_right S.u_sq
  have hu1 : u ∈ zpowers τ ⊔ zpowers x₀ := by
    rw [S.core.u_eq]; exact mem_sup_left (pow_mem (mem_zpowers τ) _)
  have hmem : u ∈ (zpowers τ ⊔ zpowers x₀) ⊓ (zpowers y ⊔ zpowers e) := ⟨hu1, hbu ▸ hb⟩
  rw [S.core.inter, mem_bot] at hmem
  exact S.u_ne_one hmem

theorem rigid [Finite G] {a : ℕ} {i : ℤ} {c w0 : G} (hc : c = 1 ∨ c = u * z)
    (hw0 : w0 = τ ^ i * x₀ * c) (hw0sq : w0 * w0 = 1) (hw0T : w0 ∈ T) {U : Subgroup G}
    (hU_le : U ≤ T ⊓ centralizer ({w0} : Set G)) (hU_dih : IVK.IsDihedralTwoGroup ↥U (a - 1))
    (hU_inf : ∀ y ∈ U, y ∈ zpowers u ⊔ zpowers w0 → y = 1)
    (hU_cls : ∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ X ∧ w0 * d ∈ X ∧ u * w0 * d ∈ X ∧ u * d ∈ Z) :
    U ≤ zpowers y ⊔ zpowers e := by
  by_contra hnot
  obtain ⟨-, k, -, hk2, ⟨eU⟩⟩ := hU_dih
  obtain ⟨d, hdU, hdD, hord⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih.exists_invol_not_mem hk2 eU hnot
  have hd2 : d * d = 1 := by
    have := pow_orderOf_eq_one d
    rw [hord, pow_two] at this
    exact this
  have hd1 : d ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hord; omega
  have hdT : d ∈ T := (Subgroup.mem_inf.1 (hU_le hdU)).1
  have hdc : d * w0 = w0 * d := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hU_le hdU)).2
  have dW := S.dihW hc hw0 hw0sq
  have hw0D : w0 ∈ zpowers τ ⊔ zpowers w0 := mem_sup_right (mem_zpowers w0)
  have hcomm := S.commW hc hw0
  have hinter := S.interW hc hw0 hw0sq
  have hu_w0 : u * w0 = w0 * u := S.u_cent w0 hw0T
  obtain ⟨a', ha', b', hb', rfl⟩ := (mem_sup_iff_of_commute hcomm).1 (S.T_leW hc hw0 hdT)
  obtain ⟨ha2, hb2⟩ := sq_split hcomm hinter ha' hb' hd2
  have hac : a' * w0 = w0 * a' := by
    have h1 : a' * b' * (w0 * 1) = w0 * 1 * (a' * b') := by rw [mul_one]; exact hdc
    exact (cent_split hcomm hinter ha' hb' hw0D (one_mem _) h1).1
  have hacs : a' * (τ ^ (0 : ℤ) * w0) = (τ ^ (0 : ℤ) * w0) * a' := by
    rw [zpow_zero, one_mul]; exact hac
  have hcases := (dW.centralizer_refl 0 ha').1 hacs
  simp only [zpow_zero, one_mul] at hcases
  rw [← S.core.u_eq] at hcases
  have hbT : b' ∈ T := S.D₂_le hb'
  by_cases hb1 : b' = 1
  ·
    have hd : a' * b' ∈ zpowers u ⊔ zpowers w0 := by
      rw [hb1, mul_one]
      rcases hcases with h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_sup_left (mem_zpowers u)
      · rw [h]; exact mem_sup_right (mem_zpowers w0)
      · rw [h]; exact mul_mem (mem_sup_left (mem_zpowers u)) (mem_sup_right (mem_zpowers w0))
    exact hd1 (hU_inf _ hdU hd)
  · obtain ⟨hbX, hbZ⟩ := S.D₂_cls hb' hb2 hb1
    have hbnZ : b' ∉ Z := S.notZ_of_X hbT hb2 hb1 hbX
    have hubT : u * b' ∈ T := mul_mem S.u_mem_T hbT
    have hubnX : u * b' ∉ X := S.notX_of_Z hubT (S.ub_sq hb' hb2) (S.ub_ne_one hb') hbZ
    obtain ⟨hX1, hX2, hX3, hZ4⟩ := hU_cls _ hdU hd2 hd1
    rcases hcases with h | h | h | h
    · apply hdD
      rw [h, one_mul]; exact hb'
    · apply hbnZ
      rw [h] at hZ4
      have : u * (u * b') = b' := by rw [← mul_assoc, S.u_sq, one_mul]
      rwa [this] at hZ4
    · apply hubnX
      rw [h] at hX3
      have : u * w0 * (w0 * b') = u * b' := by
        calc u * w0 * (w0 * b') = u * (w0 * w0) * b' := by simp only [mul_assoc]
          _ = u * b' := by rw [hw0sq, mul_one]
      rwa [this] at hX3
    · apply hubnX
      rw [h] at hX2
      have : w0 * (u * w0 * b') = u * b' := by
        calc w0 * (u * w0 * b') = (w0 * u) * w0 * b' := by simp only [mul_assoc]
          _ = (u * w0) * w0 * b' := by rw [← hu_w0]
          _ = u * (w0 * w0) * b' := by simp only [mul_assoc]
          _ = u * b' := by rw [hw0sq, mul_one]
      rwa [this] at hX2

theorem decomp [Finite G] {a : ℕ} (ha : 3 ≤ a) (hn : n = 2 ^ (a - 1)) {w0 : G} (hw0T : w0 ∈ T)
    (hw0sq : w0 * w0 = 1) (hw0Z : w0 ∈ Z) (hw0z : w0 ≠ z) (huw0Z : u * w0 ∈ Z)
    (hcard : Nat.card ↥(T ⊓ centralizer ({w0} : Set G)) = 2 ^ (a + 2)) {U : Subgroup G}
    (hU_le : U ≤ T ⊓ centralizer ({w0} : Set G)) (hU_card : Nat.card ↥U = 2 ^ (a - 1))
    (hU_dih : IVK.IsDihedralTwoGroup ↥U (a - 1))
    (hU_inf : ∀ y ∈ U, y ∈ zpowers u ⊔ zpowers w0 → y = 1)
    (hU_cls : ∀ d ∈ U, d * d = 1 → d ≠ 1 → d ∈ X ∧ w0 * d ∈ X ∧ u * w0 * d ∈ X ∧ u * d ∈ Z) :
    ∃ D₁ D₂ T₁ : Subgroup G, L4Decomp T D₁ D₂ T₁ U z u w0 a Z X := by
  obtain ⟨i, c, hc, hw0⟩ := S.w0_good ha hw0T hw0sq hw0Z hw0z huw0Z hcard.ge
  refine ⟨zpowers τ ⊔ zpowers w0, zpowers y ⊔ zpowers e, zpowers τ, ?_⟩
  have dW := S.dihW hc hw0 hw0sq
  have hUD := S.rigid hc hw0 hw0sq hw0T hU_le hU_dih hU_inf hU_cls
  have hnpos : 0 < n := S.n_pos
  have hD₂card : Nat.card ↥(zpowers y ⊔ zpowers e) = 2 * n := by
    have : NeZero n := ⟨hnpos.ne'⟩
    exact card_dihedral_sup n y e S.core.y_ord S.core.e_sq S.core.e_y S.core.e_not
  have hrel : U.relIndex (zpowers y ⊔ zpowers e) = 2 := by
    have h1 := Subgroup.relIndex_mul_card U (zpowers y ⊔ zpowers e)
    rw [inf_eq_left.2 hUD, hD₂card, hU_card, ← hn] at h1
    exact Nat.eq_of_mul_eq_mul_right hnpos h1
  have hyyU : y * y ∈ U := by
    have hyD : y ∈ zpowers y ⊔ zpowers e := mem_sup_left (mem_zpowers y)
    have hidx : (U.subgroupOf (zpowers y ⊔ zpowers e)).index = 2 := hrel
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hyD⟩ : ↥(zpowers y ⊔ zpowers e)))
      (b := ⟨y, hyD⟩)).2 Iff.rfl
    exact this
  have huzU : u * z ∈ U := by
    obtain ⟨q, hq⟩ := S.core.four_dvd
    have hn2 : n / 2 = 2 * q := by omega
    rw [S.core.uz_eq, hn2, pow_mul, pow_two]
    exact pow_mem hyyU q
  refine
    { D₁_dih := ?_
      D₂_dih := ?_
      D₁_le := sup_le (zpowers_le.2 S.τ_mem_T) (zpowers_le.2 hw0T)
      D₂_le := S.D₂_le
      comm := S.commW hc hw0
      inter := S.interW hc hw0 hw0sq
      T_le := S.T_leW hc hw0
      u_mem := S.u_memW
      center_D₁ := S.centerW hc hw0 hw0sq
      w0_mem := mem_sup_right (mem_zpowers w0)
      uz_mem := by rw [S.core.uz_eq]; exact mem_sup_left (pow_mem (mem_zpowers y) _)
      U_le := hUD
      D₂_card := by rw [hD₂card, hU_card, ← hn]
      uz_U := huzU
      T₁_le := le_sup_left
      T₁_cyc := Subgroup.isCyclic_zpowers τ
      u_T₁ := by rw [S.core.u_eq]; exact pow_mem (mem_zpowers τ) _
      T₁_idx := S.idxW hc hw0 hw0sq
      T₁_refl := fun d hd hdτ => S.reflW hc hw0 hw0sq hd hdτ
      sep := fun s hs hsτ m hm hm2 hm1 hmu => S.sepW hc hw0 hw0sq hs hsτ hm hm2 hm1 hmu
      D₂_cls := fun d hd hd2 hd1 => S.D₂_cls hd hd2 hd1
      derived := fun x hx hx2 => S.derived_inv hx hx2
      u_derived := S.u_derivedW hc hw0 }
  · have := isDihedralTwoGroup_sup (a - 1) (by omega) τ w0 (S.core.τ_ord.trans hn) hw0sq
      (S.w0_conj_τ hc hw0) (S.w0_not_mem hc hw0)
    rwa [show a - 1 + 1 = a by omega] at this
  · have := isDihedralTwoGroup_sup (a - 1) (by omega) y e (S.core.y_ord.trans hn) S.core.e_sq
      S.core.e_y S.core.e_not
    rwa [show a - 1 + 1 = a by omega] at this

end Skel

end CFSG.GH74.GLS.Stage2.Local.P27.L4
