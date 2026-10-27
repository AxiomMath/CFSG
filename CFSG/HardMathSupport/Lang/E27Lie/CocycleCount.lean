module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Defs

public section

namespace CFSG.HardMathSupport.Lang.E27Lie

open Finset

variable {G : Type*} [Group G]

@[expose] def cocycleProd (β : MulAut G) (y : G) : G := y * β y * β (β y)

theorem cocycleProd_mul (β : MulAut G) (y n : G) :
    cocycleProd β (y * n) = (y * n * y⁻¹) * ((y * β y) * β n * (y * β y)⁻¹) *
      (cocycleProd β y * β (β n) * (cocycleProd β y)⁻¹) * cocycleProd β y := by
  simp only [cocycleProd, map_mul]
  group

structure CocycleData (β : MulAut G) (N : ℕ → Subgroup G) (d : ℕ) {A : ℕ → Type*}
    [∀ k, CommGroup (A k)] (Φ : ∀ k, N k →* A k) (τ : ∀ k, A k →* A k) (b : ℕ → ℕ) : Prop where
  chain : ∀ k, N (k + 1) ≤ N k
  bot : N d = ⊥
  stable : ∀ k, ∀ x ∈ N k, β x ∈ N k
  conj : ∀ k, k < d → ∀ g ∈ N 0, ∀ x : N k,
    ∃ hx : g * (x : G) * g⁻¹ ∈ N k, Φ k ⟨g * (x : G) * g⁻¹, hx⟩ = Φ k x
  act : ∀ k (hk : k < d) (x : N k), Φ k ⟨β x, stable k x x.2⟩ = τ k (Φ k x)
  triv : ∀ k, k < d → ∀ x : N k, (x : G) ∈ N (k + 1) → Φ k x = 1
  ker : ∀ k, k < d → ∀ x : N k, Φ k x = 1 → (x : G) ∈ N (k + 1)
  bound : ∀ k, k < d →
    Nat.card {a : A k // a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} ≤ b k

section Count

variable {β : MulAut G} {N : ℕ → Subgroup G} {d : ℕ} {A : ℕ → Type*} [∀ k, CommGroup (A k)]
  {Φ : ∀ k, N k →* A k} {τ : ∀ k, A k →* A k} {b : ℕ → ℕ}

namespace CocycleData

theorem N_le (h : CocycleData β N d Φ τ b) {j k : ℕ} (hjk : j ≤ k) : N k ≤ N j := by
  induction hjk with
  | refl => exact le_rfl
  | step _ ih => exact (h.chain _).trans ih

theorem stable_zero (h : CocycleData β N d Φ τ b) {y : G} (hy : y ∈ N 0) : β y ∈ N 0 :=
  h.stable 0 y hy

theorem cocycleProd_mem (h : CocycleData β N d Φ τ b) {y : G} (hy : y ∈ N 0) :
    cocycleProd β y ∈ N 0 :=
  mul_mem (mul_mem hy (h.stable 0 _ hy)) (h.stable 0 _ (h.stable 0 _ hy))

@[expose] def corr (β : MulAut G) (y n : G) : G :=
  (y * n * y⁻¹) * ((y * β y) * β n * (y * β y)⁻¹) *
    (cocycleProd β y * β (β n) * (cocycleProd β y)⁻¹)

theorem cocycleProd_eq (y n : G) : cocycleProd β (y * n) = corr β y n * cocycleProd β y := by
  rw [cocycleProd_mul]
  rfl

theorem corr_mem (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) {y : G} (hy : y ∈ N 0)
    (n : N k) :
    ∃ hX : corr β y n ∈ N k,
      Φ k ⟨corr β y n, hX⟩ = Φ k n * τ k (Φ k n) * τ k (τ k (Φ k n)) := by
  obtain ⟨hA, hΦA⟩ := h.conj k hk y hy n
  let n₁ : N k := ⟨β n, h.stable k n n.2⟩
  let n₂ : N k := ⟨β n₁, h.stable k n₁ n₁.2⟩
  obtain ⟨hB, hΦB⟩ := h.conj k hk (y * β y) (mul_mem hy (h.stable_zero hy)) n₁
  obtain ⟨hC, hΦC⟩ := h.conj k hk (cocycleProd β y) (h.cocycleProd_mem hy) n₂
  have h1 : Φ k n₁ = τ k (Φ k n) := h.act k hk n
  have h2 : Φ k n₂ = τ k (Φ k n₁) := h.act k hk n₁
  have hX : corr β y n = ((⟨_, hA⟩ : N k) * ⟨_, hB⟩ * ⟨_, hC⟩ : N k) := rfl
  refine ⟨hX ▸ (⟨_, hA⟩ * ⟨_, hB⟩ * ⟨_, hC⟩ : N k).2, ?_⟩
  have : (⟨corr β y n, hX ▸ (⟨_, hA⟩ * ⟨_, hB⟩ * ⟨_, hC⟩ : N k).2⟩ : N k) =
      ⟨_, hA⟩ * ⟨_, hB⟩ * ⟨_, hC⟩ := Subtype.ext hX
  rw [this, map_mul, map_mul, hΦA, hΦB, hΦC, h2, h1]

open Classical in
noncomputable def cocycleSet [Fintype G] (β : MulAut G) (N : ℕ → Subgroup G) (k : ℕ) : Finset G :=
  Finset.univ.filter fun y => y ∈ N 0 ∧ cocycleProd β y ∈ N k

theorem mem_cocycleSet [Fintype G] {y : G} {k : ℕ} :
    y ∈ cocycleSet β N k ↔ y ∈ N 0 ∧ cocycleProd β y ∈ N k := by
  classical
  simp [cocycleSet]

open Classical in
theorem card_filter_mem [Fintype G] (H : Subgroup G) :
    (Finset.univ.filter fun x : G => x ∈ H).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

variable [Fintype G]

theorem cocycleSet_succ_subset (h : CocycleData β N d Φ τ b) (k : ℕ) :
    cocycleSet β N (k + 1) ⊆ cocycleSet β N k := fun y hy => by
  rw [mem_cocycleSet] at hy ⊢
  exact ⟨hy.1, h.chain k hy.2⟩

theorem mul_mem_cocycleSet (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) {y : G}
    (hy : y ∈ cocycleSet β N k) {n : G} (hn : n ∈ N k) : y * n ∈ cocycleSet β N k := by
  rw [mem_cocycleSet] at hy ⊢
  obtain ⟨hX, -⟩ := h.corr_mem hk hy.1 ⟨n, hn⟩
  refine ⟨mul_mem hy.1 (h.N_le (Nat.zero_le k) hn), ?_⟩
  rw [cocycleProd_eq]
  exact mul_mem hX hy.2

end CocycleData

namespace CocycleData

variable [Fintype G] [∀ k, Finite (A k)]

open Classical in
theorem card_fibre_le (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) {y₀ : G}
    (hy₀ : y₀ ∈ cocycleSet β N (k + 1)) :
    ((cocycleSet β N (k + 1)).filter fun y : G => (y : G ⧸ N k) = (y₀ : G ⧸ N k)).card ≤
      b k * Nat.card (N (k + 1)) := by
  classical
  set F := (cocycleSet β N (k + 1)).filter fun y : G => (y : G ⧸ N k) = (y₀ : G ⧸ N k) with hF
  have hy₀' := mem_cocycleSet.1 hy₀
  have hmem : ∀ y ∈ F, y₀⁻¹ * y ∈ N k := fun y hy => by
    have := (Finset.mem_filter.1 hy).2
    exact QuotientGroup.eq.1 this.symm
  let g : G → A k := fun y => if hy : y₀⁻¹ * y ∈ N k then Φ k ⟨y₀⁻¹ * y, hy⟩ else 1
  have hR : ∀ y ∈ F, g y ∈ {a : A k | a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} := by
    intro y hy
    have hyk := hmem y hy
    have hy' := mem_cocycleSet.1 (Finset.mem_filter.1 hy).1
    simp only [g, dif_pos hyk]
    refine ⟨⟨_, rfl⟩, ?_⟩
    obtain ⟨hX, hΦ⟩ := h.corr_mem hk hy₀'.1 ⟨y₀⁻¹ * y, hyk⟩
    have hcorr : corr β y₀ (y₀⁻¹ * y) = cocycleProd β y * (cocycleProd β y₀)⁻¹ := by
      have := cocycleProd_eq (β := β) y₀ (y₀⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      rw [this]
      group
    have hmem1 : corr β y₀ (y₀⁻¹ * y) ∈ N (k + 1) := by
      rw [hcorr]
      exact mul_mem hy'.2 (inv_mem hy₀'.2)
    have h1 := h.triv k hk ⟨_, hX⟩ hmem1
    rw [← hΦ]
    exact h1
  have hR' : ((F.image g : Finset (A k)) : Set (A k)) ⊆
      {a : A k | a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ha)
    exact hR y hy
  have himg : (F.image g).card ≤ b k := by
    have h1 : (F.image g).card ≤
        Nat.card {a : A k // a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} := by
      calc (F.image g).card = Set.ncard ((F.image g : Finset (A k)) : Set (A k)) :=
            (Set.ncard_coe_finset _).symm
        _ ≤ Set.ncard {a : A k | a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} :=
            Set.ncard_le_ncard hR' (Set.toFinite _)
        _ = Nat.card {a : A k // a ∈ (Φ k).range ∧ a * τ k a * τ k (τ k a) = 1} :=
            (Nat.card_coe_set_eq _).symm
    exact h1.trans (h.bound k hk)
  have hfib : ∀ a ∈ F.image g, (F.filter fun y => g y = a).card ≤ Nat.card (N (k + 1)) := by
    intro a ha
    obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.1 ha
    rw [← card_filter_mem (N (k + 1))]
    refine Finset.card_le_card_of_injOn (fun y => y₁⁻¹ * y) ?_ ?_
    · intro y hy
      have hyF := (Finset.mem_filter.1 hy)
      have hyk := hmem y hyF.1
      have hy1k := hmem y₁ hy₁
      have hg := hyF.2
      simp only [g, dif_pos hyk, dif_pos hy1k] at hg
      have hone : Φ k ⟨(y₀⁻¹ * y₁)⁻¹ * (y₀⁻¹ * y), mul_mem (inv_mem hy1k) hyk⟩ = 1 := by
        have : (⟨(y₀⁻¹ * y₁)⁻¹ * (y₀⁻¹ * y), mul_mem (inv_mem hy1k) hyk⟩ : N k) =
            (⟨y₀⁻¹ * y₁, hy1k⟩ : N k)⁻¹ * ⟨y₀⁻¹ * y, hyk⟩ := rfl
        rw [this, map_mul, map_inv, hg, inv_mul_cancel]
      have := h.ker k hk _ hone
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      have e : (y₀⁻¹ * y₁)⁻¹ * (y₀⁻¹ * y) = y₁⁻¹ * y := by group
      simpa [e] using this
    · intro y _ y' _ hyy
      simpa using hyy
  calc F.card ≤ Nat.card (N (k + 1)) * (F.image g).card :=
        Finset.card_le_mul_card_image F _ hfib
    _ ≤ Nat.card (N (k + 1)) * b k := Nat.mul_le_mul_left _ himg
    _ = b k * Nat.card (N (k + 1)) := mul_comm _ _

end CocycleData

namespace CocycleData

variable [Fintype G] [∀ k, Finite (A k)]


open Classical in
theorem card_image_mul_le (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) :
    ((cocycleSet β N (k + 1)).image (fun y : G => (y : G ⧸ N k))).card * Nat.card (N k) ≤
      (cocycleSet β N k).card := by
  set t := (cocycleSet β N (k + 1)).image (fun y : G => (y : G ⧸ N k)) with ht
  set s := (cocycleSet β N k).filter fun y : G => (y : G ⧸ N k) ∈ t with hs
  have hmaps : ∀ y ∈ s, (y : G ⧸ N k) ∈ t := fun y hy => (Finset.mem_filter.1 hy).2
  have hn : ∀ c ∈ t, Nat.card (N k) ≤ (s.filter fun y : G => (y : G ⧸ N k) = c).card := by
    intro c hc
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hc
    have hy₀k : y₀ ∈ cocycleSet β N k := h.cocycleSet_succ_subset k hy₀
    rw [← card_filter_mem (N k)]
    refine Finset.card_le_card_of_injOn (fun n => y₀ * n) ?_ ?_
    · intro n hn'
      have hn'' : n ∈ N k := by simpa using hn'
      have hmem := h.mul_mem_cocycleSet hk hy₀k hn''
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hs, Finset.mem_filter]
      refine ⟨⟨hmem, ?_⟩, ?_⟩
      · have : ((y₀ * n : G) : G ⧸ N k) = (y₀ : G ⧸ N k) :=
          QuotientGroup.eq.2 (by simpa using hn'')
        rw [this]; exact hc
      · exact QuotientGroup.eq.2 (by simpa using hn'')
    · intro n _ n' _ hnn
      exact mul_left_cancel hnn
  have := Finset.mul_card_image_le_card_of_maps_to hmaps (Nat.card (N k)) hn
  calc t.card * Nat.card (N k) = Nat.card (N k) * t.card := mul_comm _ _
    _ ≤ s.card := this
    _ ≤ (cocycleSet β N k).card := Finset.card_filter_le _ _

open Classical in
theorem card_step (h : CocycleData β N d Φ τ b) {k : ℕ} (hk : k < d) :
    (cocycleSet β N (k + 1)).card * Nat.card (N k) ≤
      b k * Nat.card (N (k + 1)) * (cocycleSet β N k).card := by
  set t := (cocycleSet β N (k + 1)).image (fun y : G => (y : G ⧸ N k)) with ht
  have hfib : ∀ c ∈ t, ((cocycleSet β N (k + 1)).filter fun y : G => (y : G ⧸ N k) = c).card ≤
      b k * Nat.card (N (k + 1)) := by
    intro c hc
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.1 hc
    exact h.card_fibre_le hk hy₀
  have h1 := Finset.card_le_mul_card_image (cocycleSet β N (k + 1)) (b k * Nat.card (N (k + 1))) hfib
  have h2 := h.card_image_mul_le hk
  calc (cocycleSet β N (k + 1)).card * Nat.card (N k)
      ≤ (b k * Nat.card (N (k + 1)) * t.card) * Nat.card (N k) := Nat.mul_le_mul_right _ h1
    _ = b k * Nat.card (N (k + 1)) * (t.card * Nat.card (N k)) := by ring
    _ ≤ b k * Nat.card (N (k + 1)) * (cocycleSet β N k).card := Nat.mul_le_mul_left _ h2

open Classical in
theorem card_cocycleSet_zero (h : CocycleData β N d Φ τ b) :
    (cocycleSet β N 0).card = Nat.card (N 0) := by
  rw [← card_filter_mem (N 0)]
  congr 1
  ext y
  simp only [mem_cocycleSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hy => hy.1, fun hy => ⟨hy, h.cocycleProd_mem hy⟩⟩

open Classical in
theorem card_cocycleSet_le (h : CocycleData β N d Φ τ b) :
    ∀ k, k ≤ d → (cocycleSet β N k).card ≤ Nat.card (N k) * ∏ j ∈ Finset.range k, b j := by
  intro k
  induction k with
  | zero => intro _; simp [h.card_cocycleSet_zero]
  | succ k ih =>
    intro hk
    have hk' : k < d := hk
    have hstep := h.card_step hk'
    have hpos : 0 < Nat.card (N k) := Nat.card_pos
    have hih := ih hk'.le
    rw [Finset.prod_range_succ]
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc (cocycleSet β N (k + 1)).card * Nat.card (N k)
        ≤ b k * Nat.card (N (k + 1)) * (cocycleSet β N k).card := hstep
      _ ≤ b k * Nat.card (N (k + 1)) * (Nat.card (N k) * ∏ j ∈ Finset.range k, b j) :=
          Nat.mul_le_mul_left _ hih
      _ = Nat.card (N (k + 1)) * ((∏ j ∈ Finset.range k, b j) * b k) * Nat.card (N k) := by ring

open Classical in
theorem card_cocycle_le (h : CocycleData β N d Φ τ b) :
    Nat.card {y : G // y ∈ N 0 ∧ y * β y * β (β y) = 1} ≤ ∏ j ∈ Finset.range d, b j := by
  have h1 := h.card_cocycleSet_le d le_rfl
  rw [h.bot, Subgroup.card_bot, one_mul] at h1
  have : Nat.card {y : G // y ∈ N 0 ∧ y * β y * β (β y) = 1} = (cocycleSet β N d).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext y
    simp [mem_cocycleSet, h.bot, cocycleProd]
  rw [this]
  exact h1

end CocycleData

end Count

section Lower

variable [Fintype G]

open Classical in
theorem card_le_card_cocycle_mul_card_fixed (β : MulAut G) (hβ3 : β ^ 3 = 1) (H : Subgroup G)
    (hH : ∀ x ∈ H, β x ∈ H) :
    Nat.card H ≤ Nat.card {y : G // y ∈ H ∧ y * β y * β (β y) = 1} *
      Nat.card {x : G // x ∈ H ∧ β x = x} := by
  set s := Finset.univ.filter fun w : G => w ∈ H with hs
  set f : G → G := fun w => w * (β w)⁻¹ with hf
  have hβ3' : ∀ w, β (β (β w)) = w := fun w => by
    have := congrArg (fun φ : MulAut G => φ w) hβ3
    simpa [pow_succ] using this
  set Z := Finset.univ.filter fun y : G => y ∈ H ∧ y * β y * β (β y) = 1 with hZ
  set C := Finset.univ.filter fun x : G => x ∈ H ∧ β x = x with hC
  have hcZ : (Z.card) = Nat.card {y : G // y ∈ H ∧ y * β y * β (β y) = 1} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcC : (C.card) = Nat.card {x : G // x ∈ H ∧ β x = x} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hmaps : ∀ w ∈ s, f w ∈ Z := by
    intro w hw
    have hwH : w ∈ H := (Finset.mem_filter.1 hw).2
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and, hf]
    refine ⟨mul_mem hwH (inv_mem (hH w hwH)), ?_⟩
    simp only [map_mul, map_inv, hβ3']
    group
  have hfib : ∀ c ∈ s.image f, (s.filter fun w => f w = c).card ≤ C.card := by
    intro c hc
    obtain ⟨w₁, hw₁, rfl⟩ := Finset.mem_image.1 hc
    refine Finset.card_le_card_of_injOn (fun w => w₁⁻¹ * w) ?_ ?_
    · intro w hw
      have hwF := Finset.mem_filter.1 hw
      have hwH : w ∈ H := (Finset.mem_filter.1 hwF.1).2
      have hw₁H : w₁ ∈ H := (Finset.mem_filter.1 hw₁).2
      simp only [hC, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      refine ⟨mul_mem (inv_mem hw₁H) hwH, ?_⟩
      have h2 : w * (β w)⁻¹ = w₁ * (β w₁)⁻¹ := hwF.2
      simp only [map_mul, map_inv]
      have h3 : w₁⁻¹ * (w * (β w)⁻¹) = (β w₁)⁻¹ := by
        rw [h2]; group
      calc (β w₁)⁻¹ * β w = (w₁⁻¹ * (w * (β w)⁻¹)) * β w := by rw [h3]
        _ = w₁⁻¹ * w := by group
    · intro w _ w' _ hww
      simpa using hww
  have h1 := Finset.card_le_mul_card_image s C.card hfib
  have h2 : (s.image f).card ≤ Z.card := Finset.card_le_card (fun c hc => by
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hc
    exact hmaps w hw)
  have hsH : s.card = Nat.card H := by
    rw [hs, Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc Nat.card H = s.card := hsH.symm
    _ ≤ C.card * (s.image f).card := h1
    _ ≤ C.card * Z.card := Nat.mul_le_mul_left _ h2
    _ = Nat.card {y : G // y ∈ H ∧ y * β y * β (β y) = 1} *
        Nat.card {x : G // x ∈ H ∧ β x = x} := by rw [hcZ, hcC, mul_comm]

end Lower




end CFSG.HardMathSupport.Lang.E27Lie
