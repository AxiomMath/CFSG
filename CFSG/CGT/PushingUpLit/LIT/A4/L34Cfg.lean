module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Blk

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4
open scoped commutatorElement

section Join

variable {G : Type} [Group G]

theorem mem_sup_of_commute {H K : Subgroup G} (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
        mul_mem' := by
          rintro _ _ ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
          refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
          calc h₁ * k₁ * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
            _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hc h₂ hh₂ k₁ hk₁]
            _ = h₁ * h₂ * (k₁ * k₂) := by group
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨h, hh, k, hk, rfl⟩
          refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
          have := hc h hh k hk
          calc (h * k)⁻¹ = k⁻¹ * h⁻¹ := by group
            _ = h⁻¹ * k⁻¹ := by
              rw [← Commute.inv_inv_iff.2 (show Commute h k from this)] }
    have hle : H ⊔ K ≤ S := sup_le (fun h hh => ⟨h, hh, 1, K.one_mem, by simp⟩)
      (fun k hk => ⟨1, H.one_mem, k, hk, by simp⟩)
    exact hle hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hk)

end Join

structure Two (G : Type) [Group G] where
  M : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  a₁ : G
  a₂ : G

namespace Two

variable {G : Type} [Group G]

@[expose] def V₁ (t : Two G) : Subgroup G := pCoreOf 2 t.X₁

@[expose] def V₂ (t : Two G) : Subgroup G := pCoreOf 2 t.X₂

@[expose] def A (t : Two G) : Subgroup G := t.V₁ ⊔ t.V₂

@[expose] def conj (t : Two G) (g : G) : Two G :=
  ⟨conjSub g t.M, conjSub g t.X₁, conjSub g t.X₂, g * t.a₁ * g⁻¹, g * t.a₂ * g⁻¹⟩

@[expose] def swap (t : Two G) : Two G := ⟨t.M, t.X₂, t.X₁, t.a₂, t.a₁⟩

theorem V₁_le (t : Two G) : t.V₁ ≤ t.X₁ := pCoreOf_le_self _

theorem V₂_le (t : Two G) : t.V₂ ≤ t.X₂ := pCoreOf_le_self _

theorem conjSub_conjSub_conj (g k : G) (X : Subgroup G) :
    conjSub k (conjSub g X) = conjSub g (conjSub (g⁻¹ * k * g) X) := by
  rw [conjSub_conjSub, conjSub_conjSub]
  congr 1
  group

theorem V₁_le_A (t : Two G) : t.V₁ ≤ t.A := le_sup_left

theorem V₂_le_A (t : Two G) : t.V₂ ≤ t.A := le_sup_right

theorem swap_A (t : Two G) : t.swap.A = t.A := sup_comm _ _

theorem conj_V₁ (t : Two G) (g : G) : (t.conj g).V₁ = conjSub g t.V₁ := pCoreOf_conjSub g _

theorem conj_V₂ (t : Two G) (g : G) : (t.conj g).V₂ = conjSub g t.V₂ := pCoreOf_conjSub g _

theorem conj_A (t : Two G) (g : G) : (t.conj g).A = conjSub g t.A := by
  unfold A
  rw [conj_V₁, conj_V₂]
  exact (Subgroup.map_sup _ _ _).symm

structure Cfg (t : Two G) : Prop where
  blk₁ : Blk3 t.X₁ t.a₁
  blk₂ : Blk3 t.X₂ t.a₂
  le₁ : t.X₁ ≤ t.M
  le₂ : t.X₂ ≤ t.M
  comm : ∀ x ∈ t.X₁, ∀ y ∈ t.X₂, x * y = y * x
  perm : ∀ k ∈ t.M, (conjSub k t.X₁ = t.X₁ ∧ conjSub k t.X₂ = t.X₂) ∨
    (conjSub k t.X₁ = t.X₂ ∧ conjSub k t.X₂ = t.X₁)
  swap : ∃ k ∈ t.M, conjSub k t.X₁ = t.X₂
  cent : ∀ z : G, z ≠ 1 → z * z = 1 →
    ((∀ x ∈ t.X₁, z * x = x * z) ∨ (∀ x ∈ t.X₂, z * x = x * z)) →
      Subgroup.centralizer ({z} : Set G) ≤ t.M

namespace Cfg

variable {t : Two G} (h : t.Cfg)
include h

theorem comm_V {y z : G} (hy : y ∈ t.V₁) (hz : z ∈ t.V₂) : y * z = z * y :=
  h.comm y (t.V₁_le hy) z (t.V₂_le hz)

theorem sq_V₁ {y : G} (hy : y ∈ t.V₁) : y * y = 1 := h.blk₁.sq y hy

theorem sq_V₂ {y : G} (hy : y ∈ t.V₂) : y * y = 1 := h.blk₂.sq y hy

theorem inf_V {y : G} (h1 : y ∈ t.V₁) (h2 : y ∈ t.V₂) : y = 1 := by
  have hc := h.comm t.a₁ h.blk₁.mem y (t.V₂_le h2)
  apply h.blk₁.fix y h1
  calc t.a₁ * y * t.a₁⁻¹ = (y * t.a₁) * t.a₁⁻¹ := by rw [hc]
    _ = y := by group

theorem X_ne : t.X₁ ≠ t.X₂ := by
  intro e
  obtain ⟨w, hw, hw1⟩ := h.blk₁.exists_ne_one
  have hw2 : w ∈ t.V₂ := by
    show w ∈ pCoreOf 2 t.X₂
    rw [← e]
    exact hw
  exact hw1 (h.inf_V hw hw2)

theorem swap_cfg : t.swap.Cfg where
  blk₁ := h.blk₂
  blk₂ := h.blk₁
  le₁ := h.le₂
  le₂ := h.le₁
  comm x hx y hy := (h.comm y hy x hx).symm
  perm k hk := by
    rcases h.perm k hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e2, e1⟩
    · exact Or.inr ⟨e2, e1⟩
  swap := by
    obtain ⟨k, hk, e⟩ := h.swap
    refine ⟨k, hk, ?_⟩
    rcases h.perm k hk with ⟨e1, -⟩ | ⟨-, e2⟩
    · exact absurd (e1.symm.trans e) h.X_ne
    · exact e2
  cent z hz1 hz2 hz := h.cent z hz1 hz2 hz.symm

theorem mem_A_iff {x : G} : x ∈ t.A ↔ ∃ y ∈ t.V₁, ∃ z ∈ t.V₂, x = y * z :=
  mem_sup_of_commute (fun _ hy _ hz => h.comm_V hy hz)

theorem A_sq {x : G} (hx : x ∈ t.A) : x * x = 1 := by
  obtain ⟨y, hy, z, hz, rfl⟩ := h.mem_A_iff.1 hx
  calc y * z * (y * z) = (y * y) * (z * z) := by
        have := h.comm_V hy hz
        calc y * z * (y * z) = y * (z * y) * z := by group
          _ = y * (y * z) * z := by rw [← this]
          _ = (y * y) * (z * z) := by group
    _ = 1 := by rw [h.sq_V₁ hy, h.sq_V₂ hz, one_mul]

theorem A_comm {x x' : G} (hx : x ∈ t.A) (hx' : x' ∈ t.A) : x * x' = x' * x := by
  obtain ⟨y, hy, z, hz, rfl⟩ := h.mem_A_iff.1 hx
  obtain ⟨y', hy', z', hz', rfl⟩ := h.mem_A_iff.1 hx'
  have c1 := h.blk₁.comm _ hy _ hy'
  have c2 := h.blk₂.comm _ hz _ hz'
  have c3 := h.comm_V hy hz'
  have c4 := h.comm_V hy' hz
  calc y * z * (y' * z') = y * (z * y') * z' := by group
    _ = y * (y' * z) * z' := by rw [← c4]
    _ = (y * y') * (z * z') := by group
    _ = (y' * y) * (z' * z) := by rw [c1, c2]
    _ = y' * (y * z') * z := by group
    _ = y' * (z' * y) * z := by rw [c3]
    _ = y' * z' * (y * z) := by group

theorem mul_inj {y y' z z' : G} (hy : y ∈ t.V₁) (hy' : y' ∈ t.V₁) (hz : z ∈ t.V₂)
    (hz' : z' ∈ t.V₂) (e : y * z = y' * z') : y = y' ∧ z = z' := by
  have e1 : y'⁻¹ * y = z' * z⁻¹ := by
    calc y'⁻¹ * y = y'⁻¹ * (y * z) * z⁻¹ := by group
      _ = y'⁻¹ * (y' * z') * z⁻¹ := by rw [e]
      _ = z' * z⁻¹ := by group
  have h1 : y'⁻¹ * y = 1 :=
    h.inf_V (t.V₁.mul_mem (t.V₁.inv_mem hy') hy) (e1 ▸ t.V₂.mul_mem hz' (t.V₂.inv_mem hz))
  have hy1 : y = y' := by
    have := mul_eq_one_iff_eq_inv.1 h1
    simpa using this.symm
  subst hy1
  have h2 : z' * z⁻¹ = 1 := by rw [← e1, h1]
  have hz1 : z = z' := by
    have := mul_eq_one_iff_eq_inv.1 h2
    simpa using this.symm
  exact ⟨rfl, hz1⟩

theorem card_V₁ : Nat.card t.V₁ = 4 := h.blk₁.card

theorem card_V₂ : Nat.card t.V₂ = 4 := h.blk₂.card

theorem card_A : Nat.card t.A = 16 := by
  let f : ↥t.V₁ × ↥t.V₂ → ↥t.A := fun p =>
    ⟨p.1.1 * p.2.1, h.mem_A_iff.2 ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ ⟨⟨y', hy'⟩, ⟨z', hz'⟩⟩ hyz
      have e : y * z = y' * z' := congrArg Subtype.val hyz
      obtain ⟨rfl, rfl⟩ := h.mul_inj hy hy' hz hz' e
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, z, hz, rfl⟩ := h.mem_A_iff.1 hx
      exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, h.card_V₁, h.card_V₂]

theorem A_le_M : t.A ≤ t.M :=
  sup_le ((t.V₁_le).trans h.le₁) ((t.V₂_le).trans h.le₂)

theorem X₁_conj_A {x z : G} (hx : x ∈ t.X₁) (hz : z ∈ t.A) : x * z * x⁻¹ ∈ t.A := by
  obtain ⟨y, hy, y', hy', rfl⟩ := h.mem_A_iff.1 hz
  have h1 : x * y * x⁻¹ ∈ t.V₁ := pCoreOf_normalized t.X₁ hx hy
  have h2 : x * y' = y' * x := h.comm x hx y' (t.V₂_le hy')
  have e : x * (y * y') * x⁻¹ = (x * y * x⁻¹) * y' := by
    calc x * (y * y') * x⁻¹ = (x * y) * y' * x⁻¹ := by group
      _ = (x * y) * (y' * x⁻¹) := by group
      _ = (x * y) * (x⁻¹ * y') := by
          have : y' * x⁻¹ = x⁻¹ * y' := by
            calc y' * x⁻¹ = x⁻¹ * (x * y') * x⁻¹ := by group
              _ = x⁻¹ * (y' * x) * x⁻¹ := by rw [h2]
              _ = x⁻¹ * y' := by group
          rw [this]
      _ = (x * y * x⁻¹) * y' := by group
  rw [e]
  exact t.A.mul_mem (t.V₁_le_A h1) (t.V₂_le_A hy')

theorem conjSub_A {k : G} (hk : k ∈ t.M) : conjSub k t.A = t.A := by
  unfold Two.A
  have hV : ∀ {X : Subgroup G}, conjSub k X = X → conjSub k (pCoreOf 2 X) = pCoreOf 2 X :=
    fun e => by rw [← pCoreOf_conjSub, e]
  have hsup : conjSub k (t.V₁ ⊔ t.V₂) = conjSub k t.V₁ ⊔ conjSub k t.V₂ := Subgroup.map_sup _ _ _
  rw [hsup]
  show conjSub k (pCoreOf 2 t.X₁) ⊔ conjSub k (pCoreOf 2 t.X₂) = pCoreOf 2 t.X₁ ⊔ pCoreOf 2 t.X₂
  rcases h.perm k hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [hV e1, hV e2]
  · rw [← pCoreOf_conjSub, ← pCoreOf_conjSub, e1, e2, sup_comm]

theorem conj_cfg (g : G) : (t.conj g).Cfg where
  blk₁ := Blk3.conj h.blk₁ g
  blk₂ := Blk3.conj h.blk₂ g
  le₁ := conjSub_mono h.le₁
  le₂ := conjSub_mono h.le₂
  comm := by
    intro x hx y hy
    have hx' : g⁻¹ * x * g ∈ t.X₁ := mem_conjSub_iff.1 hx
    have hy' : g⁻¹ * y * g ∈ t.X₂ := mem_conjSub_iff.1 hy
    have := h.comm _ hx' _ hy'
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  perm := by
    intro k hk
    have hk' : g⁻¹ * k * g ∈ t.M := mem_conjSub_iff.1 hk
    show (conjSub k (conjSub g t.X₁) = conjSub g t.X₁ ∧
        conjSub k (conjSub g t.X₂) = conjSub g t.X₂) ∨
      (conjSub k (conjSub g t.X₁) = conjSub g t.X₂ ∧
        conjSub k (conjSub g t.X₂) = conjSub g t.X₁)
    rw [conjSub_conjSub_conj g k t.X₁, conjSub_conjSub_conj g k t.X₂]
    rcases h.perm _ hk' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · left
      rw [e1, e2]
      exact ⟨rfl, rfl⟩
    · right
      rw [e1, e2]
      exact ⟨rfl, rfl⟩
  swap := by
    obtain ⟨k, hk, e⟩ := h.swap
    refine ⟨g * k * g⁻¹, conj_mem_conjSub hk, ?_⟩
    show conjSub (g * k * g⁻¹) (conjSub g t.X₁) = conjSub g t.X₂
    rw [conjSub_conjSub_conj g (g * k * g⁻¹) t.X₁]
    have : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [this, e]
  cent := by
    intro z hz1 hz2 hz c hc
    have hz1' : g⁻¹ * z * g ≠ 1 := fun e =>
      hz1 (conj_eq_one_iff.1 (show g⁻¹ * z * g⁻¹⁻¹ = 1 by simpa using e))
    have hz2' : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz2]; group
    have hzc : ∀ x : G, ∀ Y : Subgroup G, (∀ y ∈ conjSub g Y, z * y = y * z) → x ∈ Y →
        (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g) := by
      intro x Y hY hx
      have hzx := hY _ (conj_mem_conjSub (g := g) hx)
      calc (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * z) * g := by rw [hzx]
        _ = x * (g⁻¹ * z * g) := by group
    have hcent' : (∀ x ∈ t.X₁, (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g)) ∨
        (∀ x ∈ t.X₂, (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g)) := by
      rcases hz with hz | hz
      · exact Or.inl fun x hx => hzc x t.X₁ hz hx
      · exact Or.inr fun x hx => hzc x t.X₂ hz hx
    have hle := h.cent _ hz1' hz2' hcent'
    show c ∈ conjSub g t.M
    rw [mem_conjSub_iff]
    apply hle
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hzc' : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc z (Set.mem_singleton z)
    calc (g⁻¹ * z * g) * (g⁻¹ * c * g) = g⁻¹ * (z * c) * g := by group
      _ = g⁻¹ * (c * z) * g := by rw [hzc']
      _ = (g⁻¹ * c * g) * (g⁻¹ * z * g) := by group

end Cfg

end Two

section PairSection

variable {G : Type} [Group G]

structure Pair (t s : Two G) : Prop where
  cM : t.Cfg
  cN : s.Cfg
  AleN : t.A ≤ s.M
  BleM : s.A ≤ t.M
  X₁nle : ¬ t.X₁ ≤ s.M
  X₂nle : ¬ t.X₂ ≤ s.M
  Y₁nle : ¬ s.X₁ ≤ t.M
  Y₂nle : ¬ s.X₂ ≤ t.M
  card : Nat.card t.M = Nat.card s.M
  AneB : t.A ≠ s.A

namespace Pair

variable {t s : Two G} (h : Pair t s)
include h

theorem symm : Pair s t where
  cM := h.cN
  cN := h.cM
  AleN := h.BleM
  BleM := h.AleN
  X₁nle := h.Y₁nle
  X₂nle := h.Y₂nle
  Y₁nle := h.X₁nle
  Y₂nle := h.X₂nle
  card := h.card.symm
  AneB := h.AneB.symm

theorem swap_left : Pair t.swap s where
  cM := h.cM.swap_cfg
  cN := h.cN
  AleN := by rw [Two.swap_A]; exact h.AleN
  BleM := h.BleM
  X₁nle := h.X₂nle
  X₂nle := h.X₁nle
  Y₁nle := h.Y₁nle
  Y₂nle := h.Y₂nle
  card := h.card
  AneB := by rw [Two.swap_A]; exact h.AneB

end Pair

end PairSection

end CFSG.CGT.PushingUpLit.A4.L34

