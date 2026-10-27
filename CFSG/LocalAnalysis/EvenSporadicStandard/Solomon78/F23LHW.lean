module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

section WSup

variable {G : Type*} [Group G]

structure WSupHyp (L WL : Subgroup G) (t : G) : Prop where
  t_mem : t ∈ centralizer (L : Set G)
  t_sq : t * t = 1
  t_ne : t ≠ 1
  disjoint : Disjoint L (zpowers t)
  le : WL ≤ L

theorem wsup_isMulCommutative_iff {E : Subgroup G} :
    IsMulCommutative E ↔ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  rw [isMulCommutative_iff]
  exact ⟨fun h a ha b hb => congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩),
    fun h a b => Subtype.ext (h _ a.2 _ b.2)⟩

theorem wsup_isElemAbelian_iff {p : ℕ} {E : Subgroup G} :
    IsElemAbelian p E ↔ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ x ∈ E, x ^ p = 1 :=
  and_congr wsup_isMulCommutative_iff Iff.rfl

theorem wsup_mem_zpowers_iff {t : G} (ht : t * t = 1) {x : G} :
    x ∈ zpowers t ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

variable {L WL : Subgroup G} {t : G}

theorem wsup_comm_left (h : WSupHyp L WL t) {a : G} (ha : a ∈ WL) : a * t = t * a :=
  mem_centralizer_iff.1 h.t_mem a (h.le ha)

theorem wsup_zpowers_le_centralizer (h : WSupHyp L WL t) :
    zpowers t ≤ centralizer (L : Set G) :=
  zpowers_le.2 h.t_mem

theorem wsup_zpowers_le_centralizer_left (h : WSupHyp L WL t) :
    zpowers t ≤ centralizer (WL : Set G) :=
  zpowers_le.2 (centralizer_le (SetLike.coe_subset_coe.2 h.le) h.t_mem)

theorem WSupHyp.mem_sup_iff (h : WSupHyp L WL t) {x : G} :
    x ∈ WL ⊔ zpowers t ↔ x ∈ WL ∨ t * x ∈ WL := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (wsup_zpowers_le_centralizer_left h) hx
    rcases (wsup_mem_zpowers_iff h.t_sq).1 hb with rfl | rfl
    · exact Or.inl (by simpa using ha)
    · refine Or.inr ?_
      rw [← mul_assoc, ← wsup_comm_left h ha, mul_assoc, h.t_sq, mul_one]
      exact ha
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have : x = t * (t * x) := by rw [← mul_assoc, h.t_sq, one_mul]
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)

theorem WSupHyp.sup_inf_left (h : WSupHyp L WL t) : (WL ⊔ zpowers t) ⊓ L = WL := by
  refine le_antisymm (fun x ⟨hxW, hxL⟩ => ?_) (le_inf le_sup_left h.le)
  rcases h.mem_sup_iff.1 hxW with hx | hx
  · exact hx
  · exfalso
    have htL : t ∈ L := by simpa using mul_mem (h.le hx) (inv_mem hxL)
    exact h.t_ne (Subgroup.disjoint_def.1 h.disjoint htL (mem_zpowers t))

theorem wsup_isMulCommutative (h : WSupHyp L WL t) (hab : IsMulCommutative WL) :
    IsMulCommutative (WL ⊔ zpowers t : Subgroup G) := by
  rw [wsup_isMulCommutative_iff] at hab ⊢
  have h1 : ∀ a ∈ WL, WL ⊔ zpowers t ≤ centralizer {a} := fun a ha =>
    sup_le (fun b hb => mem_centralizer_singleton_iff.2 (hab a ha b hb).symm)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (wsup_comm_left h ha).symm))
  have h2 : WL ⊔ zpowers t ≤ centralizer {t} :=
    sup_le (fun b hb => mem_centralizer_singleton_iff.2 (wsup_comm_left h hb))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hW : (WL ⊔ zpowers t : Subgroup G) ≤ centralizer ((WL ⊔ zpowers t : Subgroup G) : Set G) :=
    sup_le (fun a ha => mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_singleton_iff.1 (h1 a ha hy))
      (zpowers_le.2 (mem_centralizer_iff.2 fun y hy =>
        mem_centralizer_singleton_iff.1 (h2 hy)))
  exact fun x hx y hy => (mem_centralizer_iff.1 (hW hx) y hy).symm

theorem WSupHyp.isElemAbelian (h : WSupHyp L WL t) (hab : IsElemAbelian 2 WL) :
    IsElemAbelian 2 (WL ⊔ zpowers t) := by
  refine ⟨wsup_isMulCommutative h hab.1, fun x hx => ?_⟩
  rcases h.mem_sup_iff.1 hx with hx | hx
  · exact hab.2 x hx
  · have hxt : x = t * (t * x) := by rw [← mul_assoc, h.t_sq, one_mul]
    have hc : Commute t (t * x) := (wsup_comm_left h hx).symm
    rw [hxt, hc.mul_pow, sq t, h.t_sq, hab.2 _ hx, one_mul]

theorem WSupHyp.card (h : WSupHyp L WL t) :
    Nat.card (WL ⊔ zpowers t : Subgroup G) = 2 * Nat.card WL := by
  have e := mulEquivProdSup (wsup_zpowers_le_centralizer_left h) (h.disjoint.mono_left h.le)
  have ho : orderOf t = 2 := orderOf_eq_prime (by rw [sq, h.t_sq]) h.t_ne
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, ho, mul_comm]

theorem WSupHyp.centralizer_eq (h : WSupHyp L WL t)
    (hC : centralizer ({t} : Set G) = L ⊔ zpowers t)
    (hW : centralizer (WL : Set G) ⊓ L = WL) :
    centralizer ((WL ⊔ zpowers t : Subgroup G) : Set G) = WL ⊔ zpowers t := by
  have hWc : WL ≤ centralizer (WL : Set G) := hW.symm.le.trans inf_le_left
  have hcomm : IsMulCommutative WL := le_centralizer_iff_isMulCommutative.1 hWc
  refine le_antisymm (fun x hx => ?_)
    (le_centralizer_iff_isMulCommutative.2 (wsup_isMulCommutative h hcomm))
  have hxt : x ∈ centralizer ({t} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.2 (mem_sup_right (mem_zpowers t))) hx
  rw [hC] at hxt
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (wsup_zpowers_le_centralizer h) hxt
  have hlc : l ∈ centralizer (WL : Set G) := by
    refine mem_centralizer_iff.2 fun w hw => ?_
    have h1 : w * (l * b) = l * b * w := mem_centralizer_iff.1 hx w (mem_sup_left hw)
    have h2 : w * b = b * w :=
      mem_centralizer_iff.1 (wsup_zpowers_le_centralizer_left h hb) w hw
    refine mul_right_cancel (b := b) ?_
    calc w * l * b = w * (l * b) := mul_assoc _ _ _
      _ = l * b * w := h1
      _ = l * (b * w) := mul_assoc _ _ _
      _ = l * (w * b) := by rw [h2]
      _ = l * w * b := (mul_assoc _ _ _).symm
  have hlW : l ∈ WL := hW ▸ (⟨hlc, hl⟩ : l ∈ centralizer (WL : Set G) ⊓ L)
  exact mul_mem_sup hlW hb

theorem WSupHyp.normalizer_inf_centralizer (h : WSupHyp L WL t)
    (hC : centralizer ({t} : Set G) = L ⊔ zpowers t) :
    normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G) ⊓ centralizer ({t} : Set G) =
      (normalizer (WL : Set G) ⊓ L) ⊔ zpowers t := by
  have hWL : ∀ x, x ∈ WL ↔ x ∈ WL ⊔ zpowers t ∧ x ∈ L := fun x => by
    rw [← mem_inf, h.sup_inf_left]
  have htN : t ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G) :=
    le_normalizer (mem_sup_right (mem_zpowers t))
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro x hx
    obtain ⟨hxN, hxC⟩ := mem_inf.1 hx
    rw [hC] at hxC
    obtain ⟨l, hl, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (wsup_zpowers_le_centralizer h) hxC
    have hbN : b ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G) :=
      le_normalizer (mem_sup_right hb)
    have hlN : l ∈ normalizer ((WL ⊔ zpowers t : Subgroup G) : Set G) := by
      simpa using mul_mem hxN (inv_mem hbN)
    have hlWL : l ∈ normalizer (WL : Set G) := by
      rw [mem_normalizer_iff]
      intro w
      rw [hWL w, hWL (l * w * l⁻¹), mem_normalizer_iff.1 hlN w,
        mem_normalizer_iff.1 (le_normalizer hl) w]
    exact mul_mem_sup (mem_inf.2 ⟨hlWL, hl⟩) hb
  · intro l hl
    obtain ⟨hlN, hlL⟩ := mem_inf.1 hl
    have hlt : l * t = t * l := mem_centralizer_iff.1 h.t_mem l hlL
    refine mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 hlt⟩
    rw [mem_normalizer_iff]
    intro x
    have hcomm : t * (l * x * l⁻¹) = l * (t * x) * l⁻¹ :=
      calc t * (l * x * l⁻¹) = t * l * x * l⁻¹ := by simp only [mul_assoc]
        _ = l * t * x * l⁻¹ := by rw [hlt]
        _ = l * (t * x) * l⁻¹ := by simp only [mul_assoc]
    rw [h.mem_sup_iff, h.mem_sup_iff, hcomm, ← mem_normalizer_iff.1 hlN x,
      ← mem_normalizer_iff.1 hlN (t * x)]
  · exact zpowers_le.2 (mem_inf.2 ⟨htN, mem_centralizer_singleton_iff.2 rfl⟩)

end WSup

end CFSG.EvenSporadicStandard.Solomon78
