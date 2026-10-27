module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open Subgroup CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

structure TriData {Y : Type} [Group Y] (L₁ L₂ L₃ : Subgroup Y) (g : Y) : Prop where
  qs₁ : IsQuasisimple ↥L₁
  qs₂ : IsQuasisimple ↥L₂
  qs₃ : IsQuasisimple ↥L₃
  c12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  c13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a
  c23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b
  cyc₁ : L₁.map (MulAut.conj g).toMonoidHom = L₂
  cyc₂ : L₂.map (MulAut.conj g).toMonoidHom = L₃
  cyc₃ : L₃.map (MulAut.conj g).toMonoidHom = L₁
  o₁ : ∃ t ∈ L₁, orderOf t = 3 ∧ ∃ l ∈ L₁, l * t ≠ t * l
  o₂ : ∃ t ∈ L₂, orderOf t = 3 ∧ ∃ l ∈ L₂, l * t ≠ t * l
  o₃ : ∃ t ∈ L₃, orderOf t = 3 ∧ ∃ l ∈ L₃, l * t ≠ t * l

theorem eb_reorder {M : Type*} [Monoid M] {A B C A' B' C' : M}
    (hBA : B * A' = A' * B) (hCA : C * A' = A' * C) (hCB : C * B' = B' * C) :
    A * B * C * (A' * B' * C') = A * A' * (B * B') * (C * C') := by
  calc A * B * C * (A' * B' * C') = A * (B * (C * A')) * B' * C' := by simp only [mul_assoc]
    _ = A * (B * (A' * C)) * B' * C' := by rw [hCA]
    _ = A * ((B * A') * C) * B' * C' := by simp only [mul_assoc]
    _ = A * ((A' * B) * C) * B' * C' := by rw [hBA]
    _ = A * A' * (B * (C * B')) * C' := by simp only [mul_assoc]
    _ = A * A' * (B * (B' * C)) * C' := by rw [hCB]
    _ = A * A' * (B * B') * (C * C') := by simp only [mul_assoc]

theorem eb_pow_mul {W : Type*} [Group W] {a b c : W} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) (i j k i' j' k' : ℕ) :
    a ^ i * b ^ j * c ^ k * (a ^ i' * b ^ j' * c ^ k') =
      a ^ (i + i') * b ^ (j + j') * c ^ (k + k') := by
  have hab' : Commute a b := hab
  have hac' : Commute a c := hac
  have hbc' : Commute b c := hbc
  rw [eb_reorder (hab'.symm.pow_pow j i').eq (hac'.symm.pow_pow k i').eq
      (hbc'.symm.pow_pow k j').eq, pow_add, pow_add, pow_add]

theorem mem_closure_three_commute {W : Type*} [Group W] [Finite W] {a b c : W} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) :
    ∀ x ∈ Subgroup.closure ({a, b, c} : Set W), ∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k := by
  have hmul : ∀ x y : W, (∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k) →
      (∃ i j k : ℕ, y = a ^ i * b ^ j * c ^ k) → ∃ i j k : ℕ, x * y = a ^ i * b ^ j * c ^ k := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨i + i', j + j', k + k', eb_pow_mul hab hac hbc i j k i' j' k'⟩
  have hpow : ∀ x : W, (∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k) →
      ∀ n : ℕ, ∃ i j k : ℕ, x ^ n = a ^ i * b ^ j * c ^ k := by
    intro x hx n
    induction n with
    | zero => exact ⟨0, 0, 0, by simp⟩
    | succ n ih =>
      rw [pow_succ]
      exact hmul _ _ ih hx
  have hinv : ∀ x : W, (∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k) →
      ∃ i j k : ℕ, x⁻¹ = a ^ i * b ^ j * c ^ k := by
    intro x hx
    have hn : 1 ≤ orderOf x := orderOf_pos x
    have hx1 : x * x ^ (orderOf x - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [← eq_inv_of_mul_eq_one_right hx1]
    exact hpow x hx _
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy | hy
    · exact ⟨1, 0, 0, by simp [hy]⟩
    · exact ⟨0, 1, 0, by simp [hy]⟩
    · exact ⟨0, 0, 1, by simp [hy]⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact hinv x hx

theorem three_dvd_of_pow_commute {W : Type*} [Group W] {t l : W} (ht : orderOf t = 3)
    (hlt : l * t ≠ t * l) (a : ℕ) (h : l * t ^ a = t ^ a * l) : 3 ∣ a := by
  by_contra hna
  have hcase : a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hsq : a * a % 3 = 1 := by
    rcases hcase with hc | hc <;> simp [Nat.mul_mod, hc]
  have htt : t ^ (a * a) = t := by
    calc t ^ (a * a) = t ^ (a * a % orderOf t) := (pow_mod_orderOf t _).symm
      _ = t := by rw [ht, hsq, pow_one]
  have h2 : Commute l ((t ^ a) ^ a) := (show Commute l (t ^ a) from h).pow_right a
  rw [← pow_mul, htt] at h2
  exact hlt h2.eq

theorem eb_pow_eq_one_left {G : Type*} [Group G] {t l y : G} {i : ℕ} (ht : orderOf t = 3)
    (hlt : l * t ≠ t * l) (hy : Commute y l) (hx : Commute (t ^ i * y) l) : t ^ i = 1 := by
  have hu : Commute (t ^ i) l := by
    have h := hx.mul_left hy.inv_left
    rwa [mul_inv_cancel_right] at h
  have h3 : 3 ∣ i := three_dvd_of_pow_commute ht hlt i hu.symm.eq
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [ht]; exact h3)

theorem eb_pow_eq_one_right {G : Type*} [Group G] {t l y : G} {i : ℕ} (ht : orderOf t = 3)
    (hlt : l * t ≠ t * l) (hy : Commute y l) (hx : Commute (y * t ^ i) l) : t ^ i = 1 := by
  have hu : Commute (t ^ i) l := by
    have h := hy.inv_left.mul_left hx
    rwa [inv_mul_cancel_left] at h
  have h3 : 3 ∣ i := three_dvd_of_pow_commute ht hlt i hu.symm.eq
  exact orderOf_dvd_iff_pow_eq_one.1 (by rw [ht]; exact h3)

theorem ebar_perfect {Y : Type} [Group Y] {L₁ L₂ L₃ : Subgroup Y} {g : Y} (h : TriData L₁ L₂ L₃ g) :
    ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ = L₁ ⊔ L₂ ⊔ L₃ := by
  have hL1 : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hL2 : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hL3 : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  apply le_antisymm
  · apply Subgroup.commutator_le.2
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  · have e₁ : L₁ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ := by
      calc L₁ = ⁅L₁, L₁⁆ := (perfect_of_quasisimple h.qs₁).symm
        _ ≤ _ := Subgroup.commutator_mono hL1 hL1
    have e₂ : L₂ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ := by
      calc L₂ = ⁅L₂, L₂⁆ := (perfect_of_quasisimple h.qs₂).symm
        _ ≤ _ := Subgroup.commutator_mono hL2 hL2
    have e₃ : L₃ ≤ ⁅L₁ ⊔ L₂ ⊔ L₃, L₁ ⊔ L₂ ⊔ L₃⁆ := by
      calc L₃ = ⁅L₃, L₃⁆ := (perfect_of_quasisimple h.qs₃).symm
        _ ≤ _ := Subgroup.commutator_mono hL3 hL3
    exact sup_le (sup_le e₁ e₂) e₃

theorem ebar_conj {Y : Type} [Group Y] {L₁ L₂ L₃ : Subgroup Y} {g : Y} (h : TriData L₁ L₂ L₃ g) :
    ∀ y : Y, y ∈ L₁ ⊔ L₂ ⊔ L₃ ↔ g * y * g⁻¹ ∈ L₁ ⊔ L₂ ⊔ L₃ := by
  have hmap : (L₁ ⊔ L₂ ⊔ L₃).map (MulAut.conj g).toMonoidHom = L₁ ⊔ L₂ ⊔ L₃ := by
    rw [Subgroup.map_sup, Subgroup.map_sup, h.cyc₁, h.cyc₂, h.cyc₃]
    rw [sup_comm (L₂ ⊔ L₃) L₁, sup_assoc]
  intro y
  constructor
  · intro hy
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hy
    rw [hmap] at h1
    exact h1
  · intro hy
    rw [← hmap] at hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
    have hxy' : g * x * g⁻¹ = g * y * g⁻¹ := hxy
    have hxy'' : x = y := mul_left_cancel (mul_right_cancel hxy')
    rw [← hxy'']
    exact hx

theorem exists_T {Y : Type} [Group Y] [Finite Y] {L₁ L₂ L₃ : Subgroup Y} {g : Y}
    (h : TriData L₁ L₂ L₃ g) :
    ∃ T : Subgroup Y, T ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ Nat.card T = 27 ∧ (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧
      (∀ t ∈ T, t ^ 3 = 1) ∧ ∀ x ∈ T, (∀ e ∈ L₁ ⊔ L₂ ⊔ L₃, x * e = e * x) → x = 1 := by
  obtain ⟨t₁, ht₁, hord₁, l₁, hl₁, hlt₁⟩ := h.o₁
  obtain ⟨t₂, ht₂, hord₂, l₂, hl₂, hlt₂⟩ := h.o₂
  obtain ⟨t₃, ht₃, hord₃, l₃, hl₃, hlt₃⟩ := h.o₃
  have hL1 : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hL2 : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hL3 : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hab : t₁ * t₂ = t₂ * t₁ := h.c12 t₁ ht₁ t₂ ht₂
  have hac : t₁ * t₃ = t₃ * t₁ := h.c13 t₁ ht₁ t₃ ht₃
  have hbc : t₂ * t₃ = t₃ * t₂ := h.c23 t₂ ht₂ t₃ ht₃
  have hn2 : t₂ ∉ Subgroup.closure ({t₁} : Set Y) := by
    refine nf_notMem_closure (L := L₂) ?_ hl₂ hlt₂
    intro s hs x hx
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    exact h.c12 t₁ ht₁ x hx
  have hn3 : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set Y) := by
    refine nf_notMem_closure (L := L₃) ?_ hl₃ hlt₃
    intro s hs x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with hs | hs
    · rw [hs]; exact h.c13 t₁ ht₁ x hx
    · rw [hs]; exact h.c23 t₂ ht₂ x hx
  obtain ⟨hel, hcard⟩ :=
    closure_three_elemAbelian Nat.prime_three hab hac hbc hord₁ hord₂ hord₃ hn2 hn3
  refine ⟨Subgroup.closure ({t₁, t₂, t₃} : Set Y), ?_, hcard.trans (by norm_num), ?_,
    fun t ht => hel.2 t ht, ?_⟩
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact hL1 ht₁
    · rw [hx]; exact hL2 ht₂
    · rw [hx]; exact hL3 ht₃
  · intro a ha b hb
    exact congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro x hxT hxc
    obtain ⟨i, j, k, hx⟩ := mem_closure_three_commute hab hac hbc x hxT
    have cx₁ : Commute x l₁ := hxc l₁ (hL1 hl₁)
    have cx₂ : Commute x l₂ := hxc l₂ (hL2 hl₂)
    have cx₃ : Commute x l₃ := hxc l₃ (hL3 hl₃)
    have e21 : Commute t₂ l₁ := (h.c12 l₁ hl₁ t₂ ht₂).symm
    have e31 : Commute t₃ l₁ := (h.c13 l₁ hl₁ t₃ ht₃).symm
    have f12 : Commute t₁ l₂ := h.c12 t₁ ht₁ l₂ hl₂
    have f32 : Commute t₃ l₂ := (h.c23 l₂ hl₂ t₃ ht₃).symm
    have g13 : Commute t₁ l₃ := h.c13 t₁ ht₁ l₃ hl₃
    have g23 : Commute t₂ l₃ := h.c23 t₂ ht₂ l₃ hl₃
    have hx1 : x = t₁ ^ i * (t₂ ^ j * t₃ ^ k) := by rw [hx, mul_assoc]
    have hx2 : x = t₂ ^ j * (t₁ ^ i * t₃ ^ k) := by
      have hc : t₁ ^ i * t₂ ^ j = t₂ ^ j * t₁ ^ i :=
        (Commute.pow_pow (show Commute t₁ t₂ from hab) i j).eq
      rw [hx, ← mul_assoc, hc]
    have hi : t₁ ^ i = 1 :=
      eb_pow_eq_one_left hord₁ hlt₁ ((e21.pow_left j).mul_left (e31.pow_left k))
        (by rw [← hx1]; exact cx₁)
    have hj : t₂ ^ j = 1 :=
      eb_pow_eq_one_left hord₂ hlt₂ ((f12.pow_left i).mul_left (f32.pow_left k))
        (by rw [← hx2]; exact cx₂)
    have hk : t₃ ^ k = 1 :=
      eb_pow_eq_one_right hord₃ hlt₃ ((g13.pow_left i).mul_left (g23.pow_left j))
        (by rw [← hx]; exact cx₃)
    simp [hx, hi, hj, hk]

theorem ed_comm_left {Y : Type} [Group Y] (a b z : Y) (h : z * b = b * z) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h, mul_inv_cancel_right]

theorem ed_comm_right {Y : Type} [Group Y] (a b w : Y) (h : w * a = a * w) :
    ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have h2 : w * a⁻¹ = a⁻¹ * w := by
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [h]
      _ = a⁻¹ * w := by group
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2, mul_inv_cancel_right]

theorem ed_comm_central {Y : Type} [Group Y] {L : Subgroup Y} {a b z w : Y} (ha : a ∈ L)
    (hb : b ∈ L) (hz : z ∈ L) (hw : w ∈ L) (hzc : ∀ g ∈ L, g * z = z * g)
    (hwc : ∀ g ∈ L, g * w = w * g) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : w * (a * z) = a * z * w := by
    calc w * (a * z) = (w * a) * z := by group
      _ = (a * w) * z := by rw [← hwc a ha]
      _ = a * (w * z) := by group
      _ = a * (z * w) := by rw [hzc w hw]
      _ = a * z * w := by group
  rw [ed_comm_right (a * z) b w h1, ed_comm_left a b z (hzc b hb).symm]

theorem ed_decomp {Y : Type} [Group Y] {L M : Subgroup Y} (hL : IsQuasisimple ↥L)
    (hLM : ∀ x ∈ L, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (n : Y) (hn : n ∈ M ⊓ L) (x : Y) (hx : x ∈ L)
    (hxn : x * n ≠ n * x) :
    ∀ l ∈ L, ∃ n₀ ∈ M ⊓ L, ∃ z ∈ L, (∀ g ∈ L, g * z = z * g) ∧ l = n₀ * z := by
  have hN : ((M ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun k hk g => Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨?_, (g * k * g⁻¹ : ↥L).2⟩)⟩
    have hk' := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk)).1
    have := hLM g g.2 k hk'
    simpa using this
  have hK : (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases hL.2.1.eq_bot_or_eq_top_of_normal
      (((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L))) with hbot | htop
  · exfalso
    have hnL : n ∈ L := (Subgroup.mem_inf.mp hn).2
    have hmem : (QuotientGroup.mk (⟨n, hnL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈
        ((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    apply hxn
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩)
  · intro l hl
    have hmem : (QuotientGroup.mk (⟨l, hl⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) ∈
        ((M ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply] at hkeq
    have hz := QuotientGroup.eq.mp hkeq
    refine ⟨(k : Y), Subgroup.mem_subgroupOf.mp hk, ((k⁻¹ * ⟨l, hl⟩ : ↥L) : Y),
      (k⁻¹ * ⟨l, hl⟩ : ↥L).2, ?_, ?_⟩
    · intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
    · simp

theorem dich_single {Y : Type} [Group Y] {L M : Subgroup Y} (hL : IsQuasisimple ↥L)
    (hLM : ∀ x ∈ L, ∀ m ∈ M, x * m * x⁻¹ ∈ M) (hML : ∀ m ∈ M, ∀ x ∈ L, m * x * m⁻¹ ∈ L) :
    (∀ m ∈ M, ∀ x ∈ L, m * x = x * m) ∨ L ≤ M := by
  have hG : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hL.1
  by_cases hA : ∀ n ∈ M ⊓ L, ∀ x ∈ L, x * n = n * x
  · left
    intro m hm
    refine commute_of_commutator_mem L (M ⊓ L) hG ?_ ?_ m ?_
    · intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hA n hn y hy
    · intro a ha b hb
      exact (hA a ha b (Subgroup.mem_inf.mp hb).2).symm
    · intro x hx
      have hmx' : m * x * m⁻¹ * x⁻¹ ∈ L := L.mul_mem (hML m hm x hx) (L.inv_mem hx)
      have hmM : m * (x * m⁻¹ * x⁻¹) ∈ M := M.mul_mem hm (hLM x hx m⁻¹ (M.inv_mem hm))
      have e : m * x * m⁻¹ * x⁻¹ = m * (x * m⁻¹ * x⁻¹) := by group
      rw [commutatorElement_def]
      refine Subgroup.mem_inf.mpr ⟨?_, hmx'⟩
      rw [e]
      exact hmM
  · right
    push Not at hA
    obtain ⟨n, hn, x, hx, hxn⟩ := hA
    have hdec := ed_decomp hL hLM n hn x hx hxn
    have hcomm : ⁅L, L⁆ ≤ M ⊓ L := by
      rw [Subgroup.commutator_le]
      intro l₁ hl₁ l₂ hl₂
      obtain ⟨n₁, hn₁, z₁, hz₁, hzc₁, rfl⟩ := hdec l₁ hl₁
      obtain ⟨n₂, hn₂, z₂, hz₂, hzc₂, rfl⟩ := hdec l₂ hl₂
      rw [ed_comm_central (Subgroup.mem_inf.mp hn₁).2 (Subgroup.mem_inf.mp hn₂).2 hz₁ hz₂ hzc₁ hzc₂,
        commutatorElement_def]
      exact (M ⊓ L).mul_mem ((M ⊓ L).mul_mem ((M ⊓ L).mul_mem hn₁ hn₂) ((M ⊓ L).inv_mem hn₁))
        ((M ⊓ L).inv_mem hn₂)
    calc L = ⁅L, L⁆ := hG.symm
      _ ≤ M ⊓ L := hcomm
      _ ≤ M := inf_le_left

theorem ed_mem_normalizer {Y : Type} [Group Y] (K : Subgroup Y) (g : Y)
    (h : ∀ x ∈ K, g * x = x * g) : g ∈ Subgroup.normalizer (K : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : g * x * g⁻¹ = x := by rw [h x hx, mul_inv_cancel_right]
    rw [e]
    exact hx
  · intro hy
    have h1 := h _ hy
    have h2 : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [h1]; group
        _ = g * x * g⁻¹ := by group
    rw [h2]
    exact hy

theorem ed_cyc {Y : Type} [Group Y] {M : Subgroup Y} {g : Y} (hMg : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    {K K' : Subgroup Y} (hK : K.map (MulAut.conj g).toMonoidHom = K') (hKM : K ≤ M) :
    K' ≤ M := by
  intro x hx
  rw [← hK] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hMg y (hKM hy)

theorem ebar_normalizes {Y : Type} [Group Y] {L₁ L₂ L₃ : Subgroup Y} {g : Y}
    (h : TriData L₁ L₂ L₃ g) : ∀ e ∈ L₁ ⊔ L₂ ⊔ L₃, (∀ x ∈ L₁, e * x * e⁻¹ ∈ L₁) ∧
      (∀ x ∈ L₂, e * x * e⁻¹ ∈ L₂) ∧ (∀ x ∈ L₃, e * x * e⁻¹ ∈ L₃) := by
  have hE1 : L₁ ⊔ L₂ ⊔ L₃ ≤ Subgroup.normalizer (L₁ : Set Y) :=
    sup_le (sup_le Subgroup.le_normalizer
      (fun g hg => ed_mem_normalizer L₁ g fun x hx => (h.c12 x hx g hg).symm))
      (fun g hg => ed_mem_normalizer L₁ g fun x hx => (h.c13 x hx g hg).symm)
  have hE2 : L₁ ⊔ L₂ ⊔ L₃ ≤ Subgroup.normalizer (L₂ : Set Y) :=
    sup_le (sup_le (fun g hg => ed_mem_normalizer L₂ g fun x hx => h.c12 g hg x hx)
      Subgroup.le_normalizer)
      (fun g hg => ed_mem_normalizer L₂ g fun x hx => (h.c23 x hx g hg).symm)
  have hE3 : L₁ ⊔ L₂ ⊔ L₃ ≤ Subgroup.normalizer (L₃ : Set Y) :=
    sup_le (sup_le (fun g hg => ed_mem_normalizer L₃ g fun x hx => h.c13 g hg x hx)
      (fun g hg => ed_mem_normalizer L₃ g fun x hx => h.c23 g hg x hx))
      Subgroup.le_normalizer
  intro e he
  exact ⟨fun x hx => (Subgroup.mem_normalizer_iff.mp (hE1 he) x).mp hx,
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hE2 he) x).mp hx,
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hE3 he) x).mp hx⟩

theorem ebar_dichotomy {Y : Type} [Group Y] {L₁ L₂ L₃ : Subgroup Y} {g : Y} (h : TriData L₁ L₂ L₃ g)
    (M : Subgroup Y) (hMe : M ≤ L₁ ⊔ L₂ ⊔ L₃)
    (hMn : ∀ e ∈ L₁ ⊔ L₂ ⊔ L₃, ∀ m ∈ M, e * m * e⁻¹ ∈ M)
    (hMg : ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    (∀ m ∈ M, ∀ e ∈ L₁ ⊔ L₂ ⊔ L₃, m * e = e * m) ∨ L₁ ⊔ L₂ ⊔ L₃ ≤ M := by
  have hE₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hE₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hE₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have d₁ := dich_single h.qs₁ (fun x hx m hm => hMn x (hE₁ hx) m hm)
    (fun m hm x hx => (ebar_normalizes h m (hMe hm)).1 x hx)
  have d₂ := dich_single h.qs₂ (fun x hx m hm => hMn x (hE₂ hx) m hm)
    (fun m hm x hx => (ebar_normalizes h m (hMe hm)).2.1 x hx)
  have d₃ := dich_single h.qs₃ (fun x hx m hm => hMn x (hE₃ hx) m hm)
    (fun m hm x hx => (ebar_normalizes h m (hMe hm)).2.2 x hx)
  have hp₁ : L₁ ≤ M → L₁ ≤ M ∧ L₂ ≤ M ∧ L₃ ≤ M := fun hK => by
    have h2 := ed_cyc hMg h.cyc₁ hK
    exact ⟨hK, h2, ed_cyc hMg h.cyc₂ h2⟩
  have hp₂ : L₂ ≤ M → L₁ ≤ M ∧ L₂ ≤ M ∧ L₃ ≤ M := fun hK => by
    have h3 := ed_cyc hMg h.cyc₂ hK
    exact ⟨ed_cyc hMg h.cyc₃ h3, hK, h3⟩
  have hp₃ : L₃ ≤ M → L₁ ≤ M ∧ L₂ ≤ M ∧ L₃ ≤ M := fun hK => by
    have h1 := ed_cyc hMg h.cyc₃ hK
    exact ⟨h1, ed_cyc hMg h.cyc₁ h1, hK⟩
  rcases d₁ with A₁ | B₁
  · rcases d₂ with A₂ | B₂
    · rcases d₃ with A₃ | B₃
      · left
        intro m hm e he
        have hc : L₁ ⊔ L₂ ⊔ L₃ ≤ Subgroup.centralizer ({m} : Set Y) := by
          refine sup_le (sup_le ?_ ?_) ?_
          · intro x hx
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact A₁ m hm x hx
          · intro x hx
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact A₂ m hm x hx
          · intro x hx
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact A₃ m hm x hx
        exact Subgroup.mem_centralizer_iff.mp (hc he) m (Set.mem_singleton m)
      · right
        obtain ⟨a, b, c⟩ := hp₃ B₃
        exact sup_le (sup_le a b) c
    · right
      obtain ⟨a, b, c⟩ := hp₂ B₂
      exact sup_le (sup_le a b) c
  · right
    obtain ⟨a, b, c⟩ := hp₁ B₁
    exact sup_le (sup_le a b) c

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
