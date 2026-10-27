module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Pure

public section

namespace CFSG.ComponentClassification.Asc76X.Hall32

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X

variable {G : Type} [Group G]

structure Split (S T : Subgroup G) (z t v : G) (P₁ : Subgroup G) : Prop where
  t_mem : t ∈ T
  t_ne_one : t ≠ 1
  t_ne_z : t ≠ z
  v_mem : v ∈ S
  v_conj : ∃ n : G, n⁻¹ * z * n = v
  v_not_mem : v ∉ centralizer (T : Set G)
  v_mul_v : v * v = 1
  v_conj_t : v * t * v⁻¹ = t * z
  zv_conj : ∃ n : G, n⁻¹ * z * n = z * v
  le : P₁ ≤ S
  comm_z : ∀ p ∈ P₁, p * z = z * p
  comm_v : ∀ p ∈ P₁, p * v = v * p
  comm_t : ∀ p ∈ P₁, p * t = t * p
  z_not_mem : z ∉ P₁
  v_not_mem' : v ∉ P₁
  zv_not_mem : z * v ∉ P₁
  decomp : ∀ x ∈ S, x * v = v * x →
    ∃ q ∈ P₁, x = q ∨ x = z * q ∨ x = v * q ∨ x = z * v * q
  conj_vp : ∀ p ∈ P₁, ∃ g : G, g⁻¹ * (v * p) * g = z * p
  conj_zvp : ∀ p ∈ P₁, ∃ g : G, g⁻¹ * (z * v * p) * g = z * p

variable [Finite G]

namespace Setup

variable {S T : Subgroup G} {z : G}

theorem exists_split (h : Setup S T z) {t n : G} (htT : t ∈ T) (ht1 : t ≠ 1) (htz : t ≠ z)
    (hvS : n⁻¹ * z * n ∈ S) (hvC : n⁻¹ * z * n ∉ centralizer (T : Set G))
    (hmax : ∀ m : G, m⁻¹ * z * m ∈ S → m⁻¹ * z * m ∉ centralizer (T : Set G) →
      Nat.card (S ⊓ centralizer ({m⁻¹ * z * m} : Set G) : Subgroup G) ≤
        Nat.card (S ⊓ centralizer ({n⁻¹ * z * n} : Set G) : Subgroup G)) :
    ∃ P₁ : Subgroup G, Split S T z t (n⁻¹ * z * n) P₁ := by
  obtain ⟨k, hk, hle, hzk, hzC⟩ := h.exists_partner hvS hvC
  have h' := h.conj k
  rw [hk] at h'
  have hz2 : z * z = 1 := h.z_mul_z
  have hv2 : n⁻¹ * z * n * (n⁻¹ * z * n) = 1 := by
    calc n⁻¹ * z * n * (n⁻¹ * z * n) = n⁻¹ * (z * z) * n := by group
      _ = 1 := by rw [hz2]; group
  generalize hvdef : n⁻¹ * z * n = v at hvS hvC hmax hk hle h' hv2 ⊢
  have hzi : z⁻¹ = z := h.inv_eq h.mem
  have ht2 : t * t = 1 := (pow_two t).symm.trans (h.sq t htT)
  have hti : t⁻¹ = t := h.inv_eq htT
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
  have hzv : z * v = v * z := (h.central v hvS).symm
  have hzt : z * t = t * z := h.comm z h.mem t htT
  have hvt0 : t * v ≠ v * t := fun e => hvC (by
    refine mem_centralizer_of_comm h.card h.sq h.mem htT h.ne_one ht1 htz hzv ?_
    exact e)
  have hvt : v * t * v⁻¹ = t * z := h.conj_eq_mul hvS htT hvt0
  obtain ⟨t', ht'T, ht'z⟩ : ∃ t' ∈ rightConjugate T k, t' * z ≠ z * t' := by
    by_contra hcon
    push Not at hcon
    exact hzC (mem_centralizer_iff.mpr fun y hy => (hcon y hy))
  have ht'2 : t' * t' = 1 := (pow_two t').symm.trans (h'.sq t' ht'T)
  have ht'i : t'⁻¹ = t' := inv_eq_of_mul_eq_one_left ht'2
  have hvt' : v * t' = t' * v := h'.comm v h'.mem t' ht'T
  have hzt' : z * t' * z⁻¹ = t' * v := h'.conj_eq_mul hzk ht'T ht'z
  have htvt : t * v * t = z * v := by
    have e1 : v * t * v = t * z := by rw [← hvi]; simpa [hvi] using hvt
    calc t * v * t = t * (v * t * v) * v := by
          rw [show t * (v * t * v) * v = t * v * t * (v * v) by group, hv2, mul_one]
      _ = t * (t * z) * v := by rw [e1]
      _ = z * v := by rw [← mul_assoc, ht2, one_mul]
  have ht'zt' : t' * z * t' = v * z := by
    have e1 : z * t' * z = t' * v := by rw [← hzi]; simpa [hzi] using hzt'
    calc t' * z * t' = t' * (z * t' * z) * z := by
          rw [show t' * (z * t' * z) * z = t' * z * t' * (z * z) by group, hz2, mul_one]
      _ = t' * (t' * v) * z := by rw [e1]
      _ = v * z := by rw [← mul_assoc, ht'2, one_mul]
  have htzt : t * z * t = z := by rw [← hzt, mul_assoc, ht2, mul_one]
  have ht'vt' : t' * v * t' = v := by rw [← hvt', mul_assoc, ht'2, mul_one]
  have hv1 : v ≠ 1 := fun e => hvC (by rw [e]; exact one_mem _)
  have hvz : v ≠ z := fun e => hvC (by
    rw [e]; exact mem_centralizer_iff.mpr fun y hy => h.comm y hy z h.mem)
  set ρ := t * t' with hρdef
  have hρz : ρ * z * ρ⁻¹ = v := by
    calc ρ * z * ρ⁻¹ = t * (t' * z * t') * t := by rw [hρdef, mul_inv_rev, ht'i, hti]; group
      _ = t * (v * z) * t := by rw [ht'zt']
      _ = (t * v * t) * (t * z * t) := by
          rw [show (t * v * t) * (t * z * t) = t * v * (t * t) * z * t by group, ht2, mul_one]
          group
      _ = v := by rw [htvt, htzt, hzv, mul_assoc, hz2, mul_one]
  have hρv : ρ * v * ρ⁻¹ = z * v := by
    calc ρ * v * ρ⁻¹ = t * (t' * v * t') * t := by rw [hρdef, mul_inv_rev, ht'i, hti]; group
      _ = z * v := by rw [ht'vt', htvt]
  have hρzv : ρ * (z * v) * ρ⁻¹ = z := by
    calc ρ * (z * v) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * v * ρ⁻¹) := by group
      _ = z := by
        rw [hρz, hρv, ← mul_assoc, ← hzv, mul_assoc, hv2, mul_one]
  have hρiz : ρ⁻¹ * v * ρ = z := by
    rw [← hρz]; group
  have hρizv : ρ⁻¹ * (z * v) * ρ = v := by
    rw [← hρv]; group
  have htρ : t * ρ * t⁻¹ = ρ⁻¹ := by
    calc t * ρ * t⁻¹ = (t * t) * t' * t⁻¹ := by rw [hρdef]; group
      _ = t' * t := by rw [ht2, one_mul, hti]
      _ = ρ⁻¹ := by rw [hρdef, mul_inv_rev, ht'i, hti]
  set P := S ⊓ centralizer ({v} : Set G) with hPdef
  have memP : ∀ {x}, x ∈ P ↔ x ∈ S ∧ x * v = v * x := by
    intro x
    rw [hPdef, mem_inf, mem_centralizer_singleton_iff]
  have htP : ∀ x ∈ P, t * x * t⁻¹ ∈ P := by
    intro x hx
    rw [memP] at hx ⊢
    refine ⟨mul_mem (mul_mem (h.le htT) hx.1) (inv_mem (h.le htT)), ?_⟩
    have hxz : x * z = z * x := (h.central x hx.1)
    have e1 : t * (z * v) * t⁻¹ = v := by
      rw [hti]
      calc t * (z * v) * t = (t * z * t) * (t * v * t) := by
            rw [show (t * z * t) * (t * v * t) = t * z * (t * t) * v * t by group, ht2, mul_one]
            group
        _ = v := by rw [htzt, htvt, ← mul_assoc, hz2, one_mul]
    have hxzv : x * (z * v) = (z * v) * x := by
      rw [← mul_assoc, hxz, mul_assoc, hx.2, ← mul_assoc]
    calc t * x * t⁻¹ * v = t * x * t⁻¹ * (t * (z * v) * t⁻¹) := by rw [e1]
      _ = t * (x * (z * v)) * t⁻¹ := by group
      _ = t * ((z * v) * x) * t⁻¹ := by rw [hxzv]
      _ = (t * (z * v) * t⁻¹) * (t * x * t⁻¹) := by group
      _ = v * (t * x * t⁻¹) := by rw [e1]
  set w := k * z * k⁻¹ with hwdef
  have hwS : w ∈ S := by
    have h1 := hzk
    rw [mem_rightConjugate_iff] at h1
    exact h1
  have hwC : w ∉ centralizer (T : Set G) := fun hw => hzC (mem_centralizer_iff.mpr fun y hy => by
    rw [SetLike.mem_coe, mem_rightConjugate_iff] at hy
    have h1 := mem_centralizer_iff.mp hw _ hy
    calc y * z = k⁻¹ * ((k * y * k⁻¹) * w) * k := by rw [hwdef]; group
      _ = k⁻¹ * (w * (k * y * k⁻¹)) * k := by rw [h1]
      _ = z * y := by rw [hwdef]; group)
  have hmaxw := hmax k⁻¹ (by simpa [hwdef] using hwS) (by simpa [hwdef] using hwC)
  set Q := rightConjugate S k ⊓ centralizer ({z} : Set G) with hQdef
  have hPQ : P ≤ Q := fun x hx => by
    rw [memP] at hx
    refine mem_inf.mpr ⟨hle (mem_inf.mpr ⟨hx.1, ?_⟩), ?_⟩
    · rw [mem_centralizer_singleton_iff]; exact hx.2
    · rw [mem_centralizer_singleton_iff]; exact h.central x hx.1
  have hQconj : Q = rightConjugate (S ⊓ centralizer ({w} : Set G)) k := by
    ext x
    rw [hQdef, mem_inf, mem_rightConjugate_iff, mem_rightConjugate_iff, mem_inf,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, hwdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      calc k * x * k⁻¹ * (k * z * k⁻¹) = k * (x * z) * k⁻¹ := by group
        _ = k * (z * x) * k⁻¹ := by rw [h2]
        _ = k * z * k⁻¹ * (k * x * k⁻¹) := by group
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      calc x * z = k⁻¹ * (k * x * k⁻¹ * (k * z * k⁻¹)) * k := by group
        _ = k⁻¹ * (k * z * k⁻¹ * (k * x * k⁻¹)) * k := by rw [h2]
        _ = z * x := by group
  have hQcard : Nat.card Q ≤ Nat.card P := by
    rw [hQconj, rightConjugate_card]
    simpa [hwdef] using hmaxw
  have hPQeq : P = Q := eq_of_le_of_card_ge hPQ hQcard
  have ht'P : ∀ x ∈ P, t' * x * t'⁻¹ ∈ P := by
    intro x hx
    rw [hPQeq] at hx ⊢
    rw [hQdef, mem_inf, mem_centralizer_singleton_iff] at hx ⊢
    have ht'S : t' ∈ rightConjugate S k := h'.le ht'T
    refine ⟨mul_mem (mul_mem ht'S hx.1) (inv_mem ht'S), ?_⟩
    have hxv : x * v = v * x := h'.central x hx.1
    have hxz : z * x = x * z := hx.2.symm
    have e1 : t' * (v * z) * t'⁻¹ = z := by
      rw [ht'i]
      calc t' * (v * z) * t' = (t' * v * t') * (t' * z * t') := by
            rw [show (t' * v * t') * (t' * z * t') = t' * v * (t' * t') * z * t' by group, ht'2,
              mul_one]
            group
        _ = z := by rw [ht'vt', ht'zt', ← mul_assoc, hv2, one_mul]
    have hxvz : (v * z) * x = x * (v * z) := by
      rw [mul_assoc, hxz, ← mul_assoc, ← hxv, mul_assoc]
    calc (t' * x * t'⁻¹) * z = (t' * x * t'⁻¹) * (t' * (v * z) * t'⁻¹) := by rw [e1]
      _ = t' * (x * (v * z)) * t'⁻¹ := by group
      _ = t' * ((v * z) * x) * t'⁻¹ := by rw [hxvz]
      _ = (t' * (v * z) * t'⁻¹) * (t' * x * t'⁻¹) := by group
      _ = z * (t' * x * t'⁻¹) := by rw [e1]
  have hct : ∀ x ∈ P, t * x * t⁻¹ * x⁻¹ = 1 ∨ t * x * t⁻¹ * x⁻¹ = z := by
    intro x hx
    have h1 : t * x * t⁻¹ * x⁻¹ ∈ T := by
      have h2 : x * t⁻¹ * x⁻¹ ∈ T :=
        (mem_normalizer_iff.mp (h.le_normalizer (memP.mp hx).1) t⁻¹).mp (inv_mem htT)
      have e : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem htT h2
    have h2 : t * x * t⁻¹ * x⁻¹ ∈ P := mul_mem (htP x hx) (inv_mem hx)
    exact h.eq_of_comm hvS hvC h1 (memP.mp h2).2
  have hct' : ∀ x ∈ P, t' * x * t'⁻¹ * x⁻¹ = 1 ∨ t' * x * t'⁻¹ * x⁻¹ = v := by
    intro x hx
    have hxS : x ∈ rightConjugate S k := by
      rw [hPQeq] at hx
      exact (mem_inf.mp hx).1
    have h1 : t' * x * t'⁻¹ * x⁻¹ ∈ rightConjugate T k := by
      have h2 : x * t'⁻¹ * x⁻¹ ∈ rightConjugate T k :=
        (mem_normalizer_iff.mp (h'.le_normalizer hxS) t'⁻¹).mp (inv_mem ht'T)
      have e : t' * x * t'⁻¹ * x⁻¹ = t' * (x * t'⁻¹ * x⁻¹) := by group
      rw [e]
      exact mul_mem ht'T h2
    have h2 : t' * x * t'⁻¹ * x⁻¹ ∈ P := mul_mem (ht'P x hx) (inv_mem hx)
    rw [hPQeq, hQdef, mem_inf, mem_centralizer_singleton_iff] at h2
    exact h'.eq_of_comm hzk hzC h1 h2.2
  set P₁ := P ⊓ centralizer ({ρ} : Set G) with hP₁def
  have memP₁ : ∀ {x}, x ∈ P₁ ↔ x ∈ P ∧ x * ρ = ρ * x := by
    intro x
    rw [hP₁def, mem_inf, mem_centralizer_singleton_iff]
  have hzP : z ∈ P := memP.mpr ⟨h.le h.mem, hzv⟩
  have hvP : v ∈ P := memP.mpr ⟨hvS, rfl⟩
  have hρp : ∀ p ∈ P₁, ρ⁻¹ * p * ρ = p := fun p hp => by
    rw [mul_assoc, (memP₁.mp hp).2, inv_mul_cancel_left]
  have mk : ∀ q ∈ P, ρ * q * ρ⁻¹ = q → q ∈ P₁ := fun q hq e =>
    memP₁.mpr ⟨hq, (mul_inv_eq_iff_eq_mul.mp e).symm⟩
  have hle₁ : P₁ ≤ S := fun x hx => (memP.mp (memP₁.mp hx).1).1
  have hcz : ∀ p ∈ P₁, p * z = z * p := fun p hp => h.central p (hle₁ hp)
  have hcv : ∀ p ∈ P₁, p * v = v * p := fun p hp => (memP.mp (memP₁.mp hp).1).2
  have hcomm_t : ∀ p ∈ P₁, p * t = t * p := by
    intro p hp
    have hpP := (memP₁.mp hp).1
    have hpρ := (memP₁.mp hp).2
    rcases hct p hpP with e | e
    · exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp e)).symm
    · exfalso
      have h1 : t * p * t⁻¹ = z * p := mul_inv_eq_iff_eq_mul.mp e
      have h2 : z * p * ρ⁻¹ = ρ⁻¹ * (z * p) := by
        calc z * p * ρ⁻¹ = (t * p * t⁻¹) * (t * ρ * t⁻¹) := by rw [h1, htρ]
          _ = t * (p * ρ) * t⁻¹ := by group
          _ = t * (ρ * p) * t⁻¹ := by rw [hpρ]
          _ = (t * ρ * t⁻¹) * (t * p * t⁻¹) := by group
          _ = ρ⁻¹ * (z * p) := by rw [htρ, h1]
      have hpρi : p * ρ⁻¹ = ρ⁻¹ * p := by
        calc p * ρ⁻¹ = ρ⁻¹ * (ρ * p) * ρ⁻¹ := by group
          _ = ρ⁻¹ * (p * ρ) * ρ⁻¹ := by rw [hpρ]
          _ = ρ⁻¹ * p := by group
      apply hvz
      rw [← hρz]
      calc ρ * z * ρ⁻¹ = ρ * (z * (p * ρ⁻¹)) * p⁻¹ := by rw [hpρi]; group
        _ = ρ * (z * p * ρ⁻¹) * p⁻¹ := by group
        _ = ρ * (ρ⁻¹ * (z * p)) * p⁻¹ := by rw [h2]
        _ = z := by group
  have hzP₁ : z ∉ P₁ := fun hz => hvz (by
    rw [← hρz, ← (memP₁.mp hz).2, mul_inv_cancel_right])
  have hvP₁ : v ∉ P₁ := fun hv => h.ne_one (by
    have h1 : ρ * v * ρ⁻¹ = v := by rw [← (memP₁.mp hv).2, mul_inv_cancel_right]
    rw [hρv] at h1
    calc z = z * v * v⁻¹ := by group
      _ = v * v⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel v)
  have hzvP₁ : z * v ∉ P₁ := fun hzv' => hv1 (by
    have h1 : ρ * (z * v) * ρ⁻¹ = z * v := by
      rw [← (memP₁.mp hzv').2, mul_inv_cancel_right]
    rw [hρzv] at h1
    calc v = z⁻¹ * (z * v) := by group
      _ = z⁻¹ * z := by rw [← h1]
      _ = 1 := inv_mul_cancel z)
  have hzvzv : z * v * (z * v) = 1 := by
    calc z * v * (z * v) = z * (v * z) * v := by group
      _ = z * (z * v) * v := by rw [hzv]
      _ = (z * z) * (v * v) := by group
      _ = 1 := by rw [hz2, hv2, one_mul]
  have hdecomp : ∀ x ∈ S, x * v = v * x →
      ∃ q ∈ P₁, x = q ∨ x = z * q ∨ x = v * q ∨ x = z * v * q := by
    intro x hxS hxv
    have hx : x ∈ P := memP.mpr ⟨hxS, hxv⟩
    have hback : ∀ e : G, e * e = 1 → x = e * (e * x) := fun e he => by
      rw [← mul_assoc, he, one_mul]
    have hyP : t' * x * t'⁻¹ ∈ P := ht'P x hx
    have hρx : ρ * x * ρ⁻¹ = t * (t' * x * t'⁻¹) * t⁻¹ := by rw [hρdef]; group
    rcases hct' x hx with ea | ea <;> rcases hct _ hyP with eb | eb
    ·
      have hy : t' * x * t'⁻¹ = x := mul_inv_eq_one.mp ea
      have e1 : ρ * x * ρ⁻¹ = x := by rw [hρx, mul_inv_eq_one.mp eb, hy]
      exact ⟨x, mk x hx e1, Or.inl rfl⟩
    ·
      have hy : t' * x * t'⁻¹ = x := mul_inv_eq_one.mp ea
      have e1 : ρ * x * ρ⁻¹ = z * x := by rw [hρx, mul_inv_eq_iff_eq_mul.mp eb, hy]
      refine ⟨v * x, mk _ (mul_mem hvP hx) ?_, Or.inr (Or.inr (Or.inl (hback v hv2)))⟩
      calc ρ * (v * x) * ρ⁻¹ = (ρ * v * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
        _ = z * v * (z * x) := by rw [hρv, e1]
        _ = v * z * (z * x) := by rw [hzv]
        _ = v * (z * z) * x := by group
        _ = v * x := by rw [hz2, mul_one]
    ·
      have hy : t' * x * t'⁻¹ = v * x := mul_inv_eq_iff_eq_mul.mp ea
      have e1 : ρ * x * ρ⁻¹ = v * x := by rw [hρx, mul_inv_eq_one.mp eb, hy]
      refine ⟨z * v * x, mk _ (mul_mem (mul_mem hzP hvP) hx) ?_,
        Or.inr (Or.inr (Or.inr (hback (z * v) hzvzv)))⟩
      calc ρ * (z * v * x) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * v * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
        _ = v * (z * v) * (v * x) := by rw [hρz, hρv, e1]
        _ = v * z * (v * v) * x := by group
        _ = v * z * x := by rw [hv2, mul_one]
        _ = z * v * x := by rw [hzv]
    ·
      have hy : t' * x * t'⁻¹ = v * x := mul_inv_eq_iff_eq_mul.mp ea
      have e1 : ρ * x * ρ⁻¹ = z * (v * x) := by rw [hρx, mul_inv_eq_iff_eq_mul.mp eb, hy]
      refine ⟨z * x, mk _ (mul_mem hzP hx) ?_, Or.inr (Or.inl (hback z hz2))⟩
      calc ρ * (z * x) * ρ⁻¹ = (ρ * z * ρ⁻¹) * (ρ * x * ρ⁻¹) := by group
        _ = v * (z * v) * x := by rw [hρz, e1]; group
        _ = v * (v * z) * x := by rw [hzv]
        _ = (v * v) * z * x := by group
        _ = z * x := by rw [hv2, one_mul]
  have hconj_vp : ∀ p ∈ P₁, ∃ g : G, g⁻¹ * (v * p) * g = z * p := fun p hp => ⟨ρ, by
    calc ρ⁻¹ * (v * p) * ρ = (ρ⁻¹ * v * ρ) * (ρ⁻¹ * p * ρ) := by group
      _ = z * p := by rw [hρiz, hρp p hp]⟩
  have hconj_zvp : ∀ p ∈ P₁, ∃ g : G, g⁻¹ * (z * v * p) * g = z * p := fun p hp => ⟨ρ * ρ, by
    have e1 : (ρ * ρ)⁻¹ * (z * v * p) * (ρ * ρ) =
        ρ⁻¹ * (ρ⁻¹ * (z * v) * ρ) * ρ * ((ρ * ρ)⁻¹ * p * (ρ * ρ)) := by group
    have e2 : (ρ * ρ)⁻¹ * p * (ρ * ρ) = p := by
      calc (ρ * ρ)⁻¹ * p * (ρ * ρ) = ρ⁻¹ * (ρ⁻¹ * p * ρ) * ρ := by group
        _ = p := by rw [hρp p hp, hρp p hp]
    rw [e1, e2, hρizv, hρiz]⟩
  have hzvc : t'⁻¹ * z * t' = z * v := by rw [ht'i, ht'zt', hzv]
  exact ⟨P₁, {
    t_mem := htT
    t_ne_one := ht1
    t_ne_z := htz
    v_mem := hvS
    v_conj := ⟨n, hvdef⟩
    v_not_mem := hvC
    v_mul_v := hv2
    v_conj_t := hvt
    zv_conj := ⟨t', hzvc⟩
    le := hle₁
    comm_z := hcz
    comm_v := hcv
    comm_t := hcomm_t
    z_not_mem := hzP₁
    v_not_mem' := hvP₁
    zv_not_mem := hzvP₁
    decomp := hdecomp
    conj_vp := hconj_vp
    conj_zvp := hconj_zvp }⟩

end Setup

end CFSG.ComponentClassification.Asc76X.Hall32
