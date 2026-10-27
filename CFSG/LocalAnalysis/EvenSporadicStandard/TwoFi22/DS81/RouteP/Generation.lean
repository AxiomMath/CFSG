module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup

variable {G : Type*} [Group G]

theorem exists_involution_commuting_or_isConj [Finite G] {a v : G} (ha : orderOf a = 2)
    (hv : orderOf v = 2) :
    (∃ w : G, orderOf w = 2 ∧ w ∈ centralizer ({a} : Set G) ∧ w ∈ centralizer ({v} : Set G)) ∨
      IsConj a v := by
  have haa : a * a = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha, sq] at h
  have hvv : v * v = 1 := by
    have h := pow_orderOf_eq_one v
    rwa [hv, sq] at h
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  obtain ⟨x, hx⟩ : ∃ x, x = a * v := ⟨_, rfl⟩
  have hxa : a * x * a⁻¹ = x⁻¹ := by
    rw [hx, mul_inv_rev, hai, hvi]
    calc a * (a * v) * a = (a * a) * v * a := by group
      _ = v * a := by rw [haa, one_mul]
  have hxv : v * x * v⁻¹ = x⁻¹ := by
    rw [hx, mul_inv_rev, hai, hvi]
    calc v * (a * v) * v = v * a * (v * v) := by group
      _ = v * a := by rw [hvv, mul_one]
  have hak : ∀ k : ℕ, a * x ^ k * a⁻¹ = (x ^ k)⁻¹ := fun k => by
    rw [← conj_pow, hxa, inv_pow]
  have hvk : ∀ k : ℕ, v * x ^ k * v⁻¹ = (x ^ k)⁻¹ := fun k => by
    rw [← conj_pow, hxv, inv_pow]
  have hn : 0 < orderOf x := orderOf_pos x
  rcases Nat.even_or_odd (orderOf x) with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    have hk0 : k ≠ 0 := by omega
    have hw : orderOf (x ^ k) = 2 := by
      rw [orderOf_pow_of_dvd hk0 ⟨2, by omega⟩, hk, show k + k = k * 2 by ring,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk0)]
    have hww : x ^ k * x ^ k = 1 := by
      have h := pow_orderOf_eq_one (x ^ k)
      rwa [hw, sq] at h
    have hwi : (x ^ k)⁻¹ = x ^ k := inv_eq_of_mul_eq_one_right hww
    refine ⟨x ^ k, hw, ?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      calc a * x ^ k = (a * x ^ k * a⁻¹) * a := by group
        _ = x ^ k * a := by rw [hak, hwi]
    · rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      calc v * x ^ k = (v * x ^ k * v⁻¹) * v := by group
        _ = x ^ k * v := by rw [hvk, hwi]
  · right
    obtain ⟨y, hy⟩ : ∃ y, y = x ^ (k + 1) := ⟨_, rfl⟩
    have hyy : y * y = x := by
      rw [hy, ← pow_add, show k + 1 + (k + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hay : a * y = y⁻¹ * a := by
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y⁻¹ * a := by rw [hy, hak]
    refine isConj_iff.2 ⟨y⁻¹, ?_⟩
    calc y⁻¹ * a * y⁻¹⁻¹ = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y⁻¹ * a) := by rw [hay]
      _ = (y * y)⁻¹ * a := by group
      _ = x⁻¹ * a := by rw [hyy]
      _ = v := by rw [hx, mul_inv_rev, inv_mul_cancel_right, hvi]

private theorem mem_of_commute_conj {M : Subgroup G} {a w v m : G}
    (hCa : centralizer ({a} : Set G) ≤ M) (hm : m ∈ M) (hw : m * a * m⁻¹ = w)
    (hvw : v * w = w * v) : v ∈ M := by
  have ha : a = m⁻¹ * w * m := by rw [← hw]; group
  have hc : m⁻¹ * v * m ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc a * (m⁻¹ * v * m) = m⁻¹ * (w * v) * m := by rw [ha]; group
      _ = m⁻¹ * (v * w) * m := by rw [hvw]
      _ = (m⁻¹ * v * m) * a := by rw [ha]; group
  have hvM : m * (m⁻¹ * v * m) * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm (hCa hc)) (M.inv_mem hm)
  simpa [mul_assoc] using hvM

theorem eq_top_of_involution_classes [Finite G] (hG : IsSimpleGroup G) (M : Subgroup G) {t z : G}
    (ht : orderOf t = 2) (hz : orderOf z = 2) (hnc : ¬ IsConj t z)
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ M) (hCz : Subgroup.centralizer ({z} : Set G) ≤ M)
    (hcls : ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a)) : M = ⊤ := by
  have key : ∀ v : G, orderOf v = 2 → v ∈ M := by
    intro v hv
    by_contra hvM
    have hcomm : ∀ w : G, w ∈ M → orderOf w = 2 → v * w = w * v → v ∈ M := by
      intro w hwM hw hvw
      rcases hcls w hwM hw with ⟨m, hm, hmw⟩ | ⟨m, hm, hmw⟩
      · exact mem_of_commute_conj hCt hm hmw hvw
      · exact mem_of_commute_conj hCz hm hmw hvw
    have h1 : IsConj t v := by
      rcases exists_involution_commuting_or_isConj ht hv with ⟨w, hw, hwt, hwv⟩ | h
      · exact absurd (hcomm w (hCt hwt) hw (mem_centralizer_iff.1 hwv v rfl)) hvM
      · exact h
    have h2 : IsConj z v := by
      rcases exists_involution_commuting_or_isConj hz hv with ⟨w, hw, hwz, hwv⟩ | h
      · exact absurd (hcomm w (hCz hwz) hw (mem_centralizer_iff.1 hwv v rfl)) hvM
      · exact h
    exact hnc (h1.trans h2.symm)
  haveI := hG
  have hnt : Subgroup.normalClosure ({t} : Set G) ≠ ⊥ := by
    intro h
    rw [Subgroup.normalClosure_eq_bot_iff] at h
    have ht1 : t = 1 := h rfl
    rw [ht1, orderOf_one] at ht
    omega
  have htop : Subgroup.normalClosure ({t} : Set G) = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_left hnt
  rw [eq_top_iff, ← htop]
  refine (Subgroup.closure_le M).2 ?_
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Group.mem_conjugatesOfSet_iff.1 hx
  rw [Set.mem_singleton_iff] at hb
  subst hb
  obtain ⟨c, hc⟩ := isConj_iff.1 hxb
  apply key
  rw [← hc]
  have : orderOf (c * b * c⁻¹) = orderOf b := by simpa using (MulAut.conj c).orderOf_eq b
  rw [this, ht]

theorem mem_of_conj_mem_of_centralizer_le (M : Subgroup G) {t : G}
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ M)
    (htM : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    {g : G} (hg : g * t * g⁻¹ ∈ M) : g ∈ M := by
  obtain ⟨m, hm, h⟩ := htM g hg
  have hc : m⁻¹ * g ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    calc t * (m⁻¹ * g) = m⁻¹ * (m * t * m⁻¹) * g := by group
      _ = m⁻¹ * (g * t * g⁻¹) * g := by rw [h]
      _ = (m⁻¹ * g) * t := by group
  have hmem : m * (m⁻¹ * g) ∈ M := M.mul_mem hm (hCt hc)
  simpa using hmem

theorem centralizer_le_of_conj_mem (M : Subgroup G) {t z : G}
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ M)
    (htM : ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹)
    (hconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c * t * c⁻¹ ∈ M) :
    Subgroup.centralizer ({z} : Set G) ≤ M :=
  fun c hc => mem_of_conj_mem_of_centralizer_le M hCt htM (hconj c hc)

theorem conj_mem_of_le_normalizer {R M : Subgroup G} {t z : G} (hRM : R ≤ M) (htR : t ∈ R)
    (hn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (R : Set G)) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G), c * t * c⁻¹ ∈ M := fun c hc =>
  hRM ((Subgroup.mem_normalizer_iff.1 (hn hc) t).1 htR)

theorem exists_conj_of_conj_mem_of_involution_classes (M : Subgroup G) {t z : G}
    (ht : orderOf t = 2) (hnc : ¬ IsConj t z)
    (hcls : ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a)) :
    ∀ g : G, g * t * g⁻¹ ∈ M → ∃ m ∈ M, g * t * g⁻¹ = m * t * m⁻¹ := by
  intro g hg
  have hord : orderOf (g * t * g⁻¹) = 2 := by
    simpa using (MulAut.conj g).orderOf_eq t |>.trans ht
  rcases hcls _ hg hord with ⟨m, hm, hmg⟩ | ⟨m, hm, hmg⟩
  · exact ⟨m, hm, hmg.symm⟩
  · exfalso
    apply hnc
    refine isConj_iff.2 ⟨m⁻¹ * g, ?_⟩
    calc m⁻¹ * g * t * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * t * g⁻¹) * m := by group
      _ = m⁻¹ * (m * z * m⁻¹) * m := by rw [hmg]
      _ = z := by group

theorem eq_top_of_unique_fixed [Finite G] (hG : IsSimpleGroup G) (M : Subgroup G) {t z : G}
    (ht : orderOf t = 2) (hz : orderOf z = 2) (hnc : ¬ IsConj t z)
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ M)
    (hcls : ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a))
    (hconj : ∀ c ∈ Subgroup.centralizer ({z} : Set G), c * t * c⁻¹ ∈ M) : M = ⊤ :=
  eq_top_of_involution_classes hG M ht hz hnc hCt
    (centralizer_le_of_conj_mem M hCt
      (exists_conj_of_conj_mem_of_involution_classes M ht hnc hcls) hconj) hcls

theorem eq_top_of_le_normalizer [Finite G] (hG : IsSimpleGroup G) (M R : Subgroup G) {t z : G}
    (ht : orderOf t = 2) (hz : orderOf z = 2) (hnc : ¬ IsConj t z)
    (hCt : Subgroup.centralizer ({t} : Set G) ≤ M)
    (hcls : ∀ a ∈ M, orderOf a = 2 →
      (∃ m ∈ M, m * t * m⁻¹ = a) ∨ (∃ m ∈ M, m * z * m⁻¹ = a))
    (hRM : R ≤ M) (htR : t ∈ R)
    (hn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (R : Set G)) : M = ⊤ :=
  eq_top_of_unique_fixed hG M ht hz hnc hCt hcls (conj_mem_of_le_normalizer hRM htR hn)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
