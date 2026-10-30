module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantCyclic

variable {G : Type} [Group G] {α : Type} [MulAction G α]

def conjSet (g : G) (u : Set G) : Set G := (fun x => g * x * g⁻¹) '' u

theorem conjSet_one (u : Set G) : conjSet (1 : G) u = u := by
  simp [conjSet]

theorem conjSet_mul (g h : G) (u : Set G) :
    conjSet (g * h) u = conjSet g (conjSet h u) := by
  simp only [conjSet, Set.image_image]
  congr 1
  funext x
  group

instance (P : Subgroup G) : MulAction P (Set G) where
  smul g u := conjSet (g : G) u
  one_smul u := conjSet_one u
  mul_smul g h u := conjSet_mul (g : G) (h : G) u

def cosetSet (c : G) (D : Subgroup G) (y : G) : Set G := (fun d => c * y * d) '' (D : Set G)

theorem cosetSet_eq_of_mem (c : G) (D : Subgroup G) {a b : G} (h : a⁻¹ * b ∈ D) :
    cosetSet c D a = cosetSet c D b := by
  have hb : b = a * (a⁻¹ * b) := by group
  rw [hb]
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(a⁻¹ * b)⁻¹ * d, D.mul_mem (D.inv_mem h) hd, by group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨(a⁻¹ * b) * d, D.mul_mem h hd, by group⟩

theorem cosetSet_injective (c : G) (D : Subgroup G) {a b : G}
    (h : cosetSet c D a = cosetSet c D b) : a⁻¹ * b ∈ D := by
  have hmem : c * b ∈ cosetSet c D b := ⟨1, D.one_mem, by group⟩
  rw [← h] at hmem
  obtain ⟨d, hd, hdb⟩ := hmem
  have : a⁻¹ * b = d := by
    have := congrArg (fun z => a⁻¹ * (c⁻¹ * z)) hdb
    simpa [mul_assoc] using this.symm
  rw [this]
  exact hd

def cosetMap (c : G) (Y D : Subgroup G) (_hDY : D ≤ Y) : (Y ⧸ D.subgroupOf Y) → Set G :=
  Quotient.lift (fun y : Y => cosetSet c D (y : G)) (fun a b h => by
    apply cosetSet_eq_of_mem
    simpa [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] using h)

theorem cosetMap_injective (c : G) (Y D : Subgroup G) (hDY : D ≤ Y) :
    Function.Injective (cosetMap c Y D hDY) := by
  intro q1 q2
  induction q1 using Quotient.inductionOn with | h a => ?_
  induction q2 using Quotient.inductionOn with | h b => ?_
  intro h
  have h' : cosetSet c D (a : G) = cosetSet c D (b : G) := h
  apply Quotient.sound
  refine QuotientGroup.leftRel_apply.mpr ?_
  rw [Subgroup.mem_subgroupOf]
  simpa using cosetSet_injective c D h'

theorem card_range_cosetMap (c : G) (Y D : Subgroup G) (hDY : D ≤ Y) :
    Nat.card (Set.range (cosetMap c Y D hDY)) = D.relIndex Y := by
  rw [Nat.card_range_of_injective (cosetMap_injective c Y D hDY)]
  rfl

theorem exists_fixed_of_isPGroup {H : Type} [Group H] (hH : IsPGroup 2 H) (α : Type)
    [MulAction H α] [Finite α] (hodd : ¬ 2 ∣ Nat.card α) :
    ∃ x : α, ∀ h : H, h • x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card α hodd
  exact ⟨x, fun h => (hx : ∀ m : H, m • x = x) h⟩

theorem conjSet_cosetMap_mem (c : G) (Y D P : Subgroup G) (hDY : D ≤ Y)
    (hPD : ∀ g ∈ P, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hPY : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hc : ∀ g ∈ P, ∃ m ∈ Y, g * c * g⁻¹ = c * m)
    {g : G} (hg : g ∈ P) (x : Set G) (hx : x ∈ Set.range (cosetMap c Y D hDY)) :
    conjSet g x ∈ Set.range (cosetMap c Y D hDY) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  obtain ⟨m, hm, hgc⟩ := hc g hg
  have hy : m * (g * (a : G) * g⁻¹) ∈ Y :=
    Y.mul_mem hm (hPY g hg a a.2)
  refine ⟨⟦⟨m * (g * (a : G) * g⁻¹), hy⟩⟧, ?_⟩
  have key : conjSet g (cosetSet c D (a : G)) = cosetSet c D (m * (g * (a : G) * g⁻¹)) := by
    ext z
    simp only [conjSet, cosetSet, Set.mem_image, SetLike.mem_coe]
    constructor
    · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
      refine ⟨g * d * g⁻¹, hPD g hg d hd, ?_⟩
      rw [show c * (m * (g * (a : G) * g⁻¹)) * (g * d * g⁻¹)
          = (c * m) * g * (a : G) * d * g⁻¹ by group, ← hgc]
      group
    · rintro ⟨d', hd', rfl⟩
      have hd : g⁻¹ * d' * g⁻¹⁻¹ ∈ D := hPD g⁻¹ (P.inv_mem hg) d' hd'
      refine ⟨c * (a : G) * (g⁻¹ * d' * g⁻¹⁻¹), ⟨g⁻¹ * d' * g⁻¹⁻¹, hd, rfl⟩, ?_⟩
      rw [show c * (m * (g * (a : G) * g⁻¹)) * d' = (c * m) * g * (a : G) * g⁻¹ * d' by group,
        ← hgc]
      group
  exact key.symm

theorem exists_coset_fixed [Finite G] (c : G) (Y D P : Subgroup G) (hDY : D ≤ Y) (hP : IsPGroup 2 P)
    (hPD : ∀ g ∈ P, ∀ d ∈ D, g * d * g⁻¹ ∈ D)
    (hPY : ∀ g ∈ P, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y)
    (hc : ∀ g ∈ P, ∃ m ∈ Y, g * c * g⁻¹ = c * m)
    (hodd : ¬ 2 ∣ D.relIndex Y) :
    ∃ y ∈ Y, ∀ g ∈ P, ∃ d ∈ D, g * (c * y) * g⁻¹ = c * y * d := by
  have hcard := card_range_cosetMap c Y D hDY
  have hodd' : ¬ 2 ∣ Nat.card (Set.range (cosetMap c Y D hDY)) := by
    rw [hcard]; exact hodd
  have : Finite (Set.range (cosetMap c Y D hDY)) := (Set.finite_range _).to_subtype
  let : MulAction P (Set.range (cosetMap c Y D hDY)) :=
    { smul := fun g x => ⟨conjSet (g : G) x.1,
        conjSet_cosetMap_mem c Y D P hDY hPD hPY hc g.2 x.1 x.2⟩
      one_smul := fun x => Subtype.ext (conjSet_one x.1)
      mul_smul := fun g h x => Subtype.ext (conjSet_mul (g : G) (h : G) x.1) }
  obtain ⟨x, hx⟩ := exists_fixed_of_isPGroup hP _ hodd'
  obtain ⟨q, hq⟩ := x.2
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have hfix : ∀ g ∈ P, conjSet g x.1 = x.1 := fun g hg => congrArg Subtype.val (hx ⟨g, hg⟩)
  have hmem0 : c * (a : G) ∈ x.1 := by
    rw [← hq]
    exact ⟨1, D.one_mem, by group⟩
  refine ⟨(a : G), a.2, fun g hg => ?_⟩
  have hmem : g * (c * (a : G)) * g⁻¹ ∈ conjSet g x.1 := ⟨c * (a : G), hmem0, rfl⟩
  rw [hfix g hg, ← hq] at hmem
  obtain ⟨d, hd, hde⟩ := hmem
  exact ⟨d, hd, hde.symm⟩

theorem conj_mem_zpowers_sup (g z : G) (D : Subgroup G) (S : Subgroup G) (hg : g ∈ S)
    (hD : ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hz : g * z * g⁻¹ ∈ Subgroup.zpowers z ⊔ D) :
    ∀ n ∈ Subgroup.zpowers z ⊔ D, g * n * g⁻¹ ∈ Subgroup.zpowers z ⊔ D := by
  intro n hn
  let T : Subgroup G := (Subgroup.zpowers z ⊔ D).comap (MulAut.conj g).toMonoidHom
  have hT : Subgroup.zpowers z ⊔ D ≤ T := by
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact hz
    · intro d hd
      exact Subgroup.mem_sup_right (hD d hd)
  have hnT : n ∈ T := hT hn
  exact hnT

theorem le_normalizer_of_conj_mem (S K : Subgroup G)
    (h : ∀ g ∈ S, ∀ n ∈ K, g * n * g⁻¹ ∈ K) : S ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact h g hg n hn
  · intro hn
    have := h g⁻¹ (S.inv_mem hg) _ hn
    simpa [mul_assoc] using this

theorem pow_mul_mem_coset (z : G) (D : Subgroup G)
    (hz' : ∀ d ∈ D, z⁻¹ * d * z ∈ D) (d : G) (hd : d ∈ D) (r : ℕ) :
    ∃ e ∈ D, (z * d) ^ r = z ^ r * e := by
  induction r with
  | zero => exact ⟨1, D.one_mem, by simp⟩
  | succ r ih =>
    obtain ⟨e, he, hpow⟩ := ih
    refine ⟨z⁻¹ * e * z * d, D.mul_mem (hz' e he) hd, ?_⟩
    rw [pow_succ, hpow, pow_succ]
    group

theorem cover_three [Finite G] (W N₀ : Subgroup G) (hWN : W ≤ Subgroup.normalizer (N₀ : Set G))
    (h3 : N₀.relIndex W = 3)
    (c : G) (hcW : c ∈ W) (hcN : c ∉ N₀) (w : G) (hw : w ∈ W) :
    w ∈ N₀ ∨ (∃ m ∈ N₀, w = c * m) ∨ (∃ m ∈ N₀, w = c⁻¹ * m) := by
  haveI : (N₀.subgroupOf W).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hWN g.2) n).mp hn
    simpa using this⟩
  have hcard : Nat.card (↥W ⧸ N₀.subgroupOf W) = 3 := h3
  have key : ∀ a b : G, ∀ ha : a ∈ W, ∀ hb : b ∈ W,
      (QuotientGroup.mk (⟨a, ha⟩ : W) : ↥W ⧸ N₀.subgroupOf W) = QuotientGroup.mk ⟨b, hb⟩ ↔
        a⁻¹ * b ∈ N₀ := by
    intro a b ha hb
    rw [QuotientGroup.eq]
    simp [Subgroup.mem_subgroupOf]
  have hone : ∀ a : G, ∀ ha : a ∈ W,
      (QuotientGroup.mk (⟨a, ha⟩ : W) : ↥W ⧸ N₀.subgroupOf W) = 1 ↔ a ∈ N₀ := by
    intro a ha
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set cq : ↥W ⧸ N₀.subgroupOf W := QuotientGroup.mk (⟨c, hcW⟩ : W) with hcq
  set wq : ↥W ⧸ N₀.subgroupOf W := QuotientGroup.mk (⟨w, hw⟩ : W) with hwq
  have hne : cq ≠ 1 := fun h => hcN ((hone c hcW).mp h)
  have hord : orderOf cq = 3 := by
    have hdvd : orderOf cq ∣ 3 := hcard ▸ orderOf_dvd_natCard cq
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have htop : Subgroup.zpowers cq = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcard]
  have hmem : wq ∈ Subgroup.zpowers cq := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk3 : cq ^ (k % 3) = wq := by
    have hmod : k % 3 = k % (orderOf cq : ℤ) := by rw [hord]; norm_num
    rw [hmod, zpow_mod_orderOf, hk]
  have hcube : cq ^ (2 : ℤ) = cq⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast,
      ← hord, pow_orderOf_eq_one]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · left
    rw [h0, zpow_zero] at hk3
    have := (hone w hw).mp hk3.symm
    exact this
  · right; left
    rw [h1, zpow_one] at hk3
    have hk' : (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ N₀.subgroupOf W)
        = QuotientGroup.mk ⟨c, hcW⟩ := hk3.symm
    have hm := (key w c hw hcW).mp hk'
    refine ⟨c⁻¹ * w, ?_, by group⟩
    have : (w⁻¹ * c)⁻¹ ∈ N₀ := N₀.inv_mem hm
    simpa [mul_assoc] using this
  · right; right
    rw [h2, hcube] at hk3
    have hk' : (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ N₀.subgroupOf W)
        = QuotientGroup.mk ⟨c⁻¹, W.inv_mem hcW⟩ := hk3.symm
    have hm := (key w c⁻¹ hw (W.inv_mem hcW)).mp hk'
    refine ⟨c * w, ?_, by group⟩
    have : (w⁻¹ * c⁻¹)⁻¹ ∈ N₀ := N₀.inv_mem hm
    simpa [mul_assoc] using this

theorem conj_mem_of_mem_normalizer {g : G} {H : Subgroup G} (hg : g ∈ Subgroup.normalizer (H : Set G))
    {n : G} (hn : n ∈ H) : g * n * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg n).mp hn

theorem isPGroup_of_le {P S : Subgroup G} (hPS : P ≤ S) (hS : IsPGroup 2 S) : IsPGroup 2 P := by
  intro g
  obtain ⟨k, hk⟩ := hS ⟨g.1, hPS g.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem subgroupOf_normal_of_le {W N₀ : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) : (N₀.subgroupOf W).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_of_mem_normalizer (hWN g.2) hn⟩

theorem cube_mem_of_relIndex [Finite G] {W N₀ : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (h3 : N₀.relIndex W = 3)
    {w : G} (hw : w ∈ W) : w ^ 3 ∈ N₀ := by
  haveI := subgroupOf_normal_of_le hWN
  have hcard : Nat.card (↥W ⧸ N₀.subgroupOf W) = 3 := h3
  have hd : orderOf (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ N₀.subgroupOf W) ∣ 3 := by
    rw [← hcard]; exact orderOf_dvd_natCard _
  have h1 : (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ N₀.subgroupOf W) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hd
  have h2 : (⟨w, hw⟩ : W) ^ 3 ∈ N₀.subgroupOf W := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h1
  have h4 := Subgroup.mem_subgroupOf.mp h2
  simpa using h4

def centW (W N₀ S : Subgroup G) (hWN : W ≤ Subgroup.normalizer (N₀ : Set G))
    (hSN : S ≤ Subgroup.normalizer (N₀ : Set G)) : Subgroup G where
  carrier := {g | g ∈ S ∧ ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ N₀}
  one_mem' := ⟨S.one_mem, fun w _ => by simpa using N₀.one_mem⟩
  mul_mem' := by
    rintro g h ⟨hg, hgw⟩ ⟨hh, hhw⟩
    refine ⟨S.mul_mem hg hh, fun w hw => ?_⟩
    have e : g * h * w * (g * h)⁻¹ * w⁻¹
        = (g * (h * w * h⁻¹ * w⁻¹) * g⁻¹) * (g * w * g⁻¹ * w⁻¹) := by group
    rw [e]
    exact N₀.mul_mem (conj_mem_of_mem_normalizer (hSN hg) (hhw w hw)) (hgw w hw)
  inv_mem' := by
    rintro g ⟨hg, hgw⟩
    refine ⟨S.inv_mem hg, fun w hw => ?_⟩
    have hp : g * w⁻¹ * g⁻¹ * w⁻¹⁻¹ ∈ N₀ := hgw w⁻¹ (W.inv_mem hw)
    have e : g⁻¹ * w * g⁻¹⁻¹ * w⁻¹
        = g⁻¹ * (w * (g * w⁻¹ * g⁻¹ * w⁻¹⁻¹) * w⁻¹) * g⁻¹⁻¹ := by group
    rw [e]
    exact conj_mem_of_mem_normalizer (hSN (S.inv_mem hg))
      (conj_mem_of_mem_normalizer (hWN hw) hp)

theorem mem_centW_of_conj_c [Finite G] {W N₀ S : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (hSN : S ≤ Subgroup.normalizer (N₀ : Set G))
    (h3 : N₀.relIndex W = 3) {c : G} (hcW : c ∈ W) (hcN : c ∉ N₀)
    {g : G} (hg : g ∈ S) {m₁ : G} (hm₁ : m₁ ∈ N₀) (hgc : g * c * g⁻¹ = c * m₁) :
    g ∈ centW W N₀ S hWN hSN := by
  refine ⟨hg, fun w hw => ?_⟩
  have hgc' : g * c = c * m₁ * g := by
    calc g * c = (g * c * g⁻¹) * g := by group
    _ = c * m₁ * g := by rw [hgc]
  rcases cover_three W N₀ hWN h3 c hcW hcN w hw with h | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · exact N₀.mul_mem (conj_mem_of_mem_normalizer (hSN hg) h) (N₀.inv_mem h)
  · have e : g * (c * m) * g⁻¹ * (c * m)⁻¹ = c * (m₁ * (g * m * g⁻¹) * m⁻¹) * c⁻¹ := by
      calc g * (c * m) * g⁻¹ * (c * m)⁻¹ = (g * c) * m * g⁻¹ * (m⁻¹ * c⁻¹) := by group
      _ = c * m₁ * g * m * g⁻¹ * (m⁻¹ * c⁻¹) := by rw [hgc']
      _ = c * (m₁ * (g * m * g⁻¹) * m⁻¹) * c⁻¹ := by group
    rw [e]
    exact conj_mem_of_mem_normalizer (hWN hcW)
      (N₀.mul_mem (N₀.mul_mem hm₁ (conj_mem_of_mem_normalizer (hSN hg) hm)) (N₀.inv_mem hm))
  · have hgcinv : g * c⁻¹ * g⁻¹ = m₁⁻¹ * c⁻¹ := by
      calc g * c⁻¹ * g⁻¹ = (g * c * g⁻¹)⁻¹ := by group
      _ = (c * m₁)⁻¹ := by rw [hgc]
      _ = m₁⁻¹ * c⁻¹ := by group
    have hq : g * m * g⁻¹ * m⁻¹ ∈ N₀ :=
      N₀.mul_mem (conj_mem_of_mem_normalizer (hSN hg) hm) (N₀.inv_mem hm)
    have hc' : c⁻¹ * (g * m * g⁻¹ * m⁻¹) * c ∈ N₀ := by
      have := conj_mem_of_mem_normalizer (hWN (W.inv_mem hcW)) hq
      rwa [inv_inv] at this
    have e : g * (c⁻¹ * m) * g⁻¹ * (c⁻¹ * m)⁻¹
        = m₁⁻¹ * (c⁻¹ * (g * m * g⁻¹ * m⁻¹) * c) := by
      calc g * (c⁻¹ * m) * g⁻¹ * (c⁻¹ * m)⁻¹
          = (g * c⁻¹ * g⁻¹) * (g * m * g⁻¹) * (m⁻¹ * c) := by group
        _ = (m₁⁻¹ * c⁻¹) * (g * m * g⁻¹) * (m⁻¹ * c) := by rw [hgcinv]
        _ = m₁⁻¹ * (c⁻¹ * (g * m * g⁻¹ * m⁻¹) * c) := by group
    rw [e]
    exact N₀.mul_mem (N₀.inv_mem hm₁) hc'

theorem mem_centW_iff {W N₀ S : Subgroup G} {hWN : W ≤ Subgroup.normalizer (N₀ : Set G)}
    {hSN : S ≤ Subgroup.normalizer (N₀ : Set G)} {g : G} :
    g ∈ centW W N₀ S hWN hSN ↔ g ∈ S ∧ ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ N₀ := Iff.rfl

theorem conj_c_inv_of_not_mem [Finite G] {W N₀ S : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (hSN : S ≤ Subgroup.normalizer (N₀ : Set G))
    (hSW : S ≤ Subgroup.normalizer (W : Set G)) (h3 : N₀.relIndex W = 3)
    {c : G} (hcW : c ∈ W) (hcN : c ∉ N₀)
    {g : G} (hg : g ∈ S) (hnot : g ∉ centW W N₀ S hWN hSN) :
    ∃ m ∈ N₀, g * c * g⁻¹ = c⁻¹ * m := by
  have hgW : g * c * g⁻¹ ∈ W := conj_mem_of_mem_normalizer (hSW hg) hcW
  have hgN : g * c * g⁻¹ ∉ N₀ := fun h => hcN (by
    have := conj_mem_of_mem_normalizer (hSN (S.inv_mem hg)) h
    rwa [show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this)
  rcases cover_three W N₀ hWN h3 c hcW hcN (g * c * g⁻¹) hgW with h | ⟨m, hm, hm'⟩ | ⟨m, hm, hm'⟩
  · exact absurd h hgN
  · exact absurd (mem_centW_of_conj_c hWN hSN h3 hcW hcN hg hm hm') hnot
  · exact ⟨m, hm, hm'⟩

theorem conj_mem_centW {W N₀ S : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N₀ : Set G))
    (hSN : S ≤ Subgroup.normalizer (N₀ : Set G)) (hSW : S ≤ Subgroup.normalizer (W : Set G))
    {s g : G} (hs : s ∈ S) (hg : g ∈ centW W N₀ S hWN hSN) :
    s⁻¹ * g * s ∈ centW W N₀ S hWN hSN := by
  obtain ⟨hgS, hgw⟩ := mem_centW_iff.mp hg
  refine mem_centW_iff.mpr ⟨S.mul_mem (S.mul_mem (S.inv_mem hs) hgS) hs, fun w hw => ?_⟩
  have hsw : s * w * s⁻¹ ∈ W := conj_mem_of_mem_normalizer (hSW hs) hw
  have key := conj_mem_of_mem_normalizer (hSN (S.inv_mem hs)) (hgw _ hsw)
  have e : s⁻¹ * (g * (s * w * s⁻¹) * g⁻¹ * (s * w * s⁻¹)⁻¹) * s⁻¹⁻¹
      = s⁻¹ * g * s * w * (s⁻¹ * g * s)⁻¹ * w⁻¹ := by group
  rw [e] at key
  exact key

theorem inv_mul_mem_centW [Finite G] {W N₀ S : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (hSN : S ≤ Subgroup.normalizer (N₀ : Set G))
    (hSW : S ≤ Subgroup.normalizer (W : Set G)) (h3 : N₀.relIndex W = 3)
    {c : G} (hcW : c ∈ W) (hcN : c ∉ N₀)
    {s g : G} (hs : s ∈ S) (hg : g ∈ S)
    (hsn : s ∉ centW W N₀ S hWN hSN) (hgn : g ∉ centW W N₀ S hWN hSN) :
    s⁻¹ * g ∈ centW W N₀ S hWN hSN := by
  obtain ⟨m, hm, hgc⟩ := conj_c_inv_of_not_mem hWN hSN hSW h3 hcW hcN hg hgn
  have hs' : s⁻¹ ∉ centW W N₀ S hWN hSN := fun h =>
    hsn (by simpa using (centW W N₀ S hWN hSN).inv_mem h)
  obtain ⟨m', hm', hsc⟩ := conj_c_inv_of_not_mem hWN hSN hSW h3 hcW hcN (S.inv_mem hs) hs'
  rw [inv_inv] at hsc
  have hA : c⁻¹ * m'⁻¹ * c ∈ N₀ := by
    have := conj_mem_of_mem_normalizer (hWN (W.inv_mem hcW)) (N₀.inv_mem hm')
    rwa [inv_inv] at this
  have hB : s⁻¹ * m * s ∈ N₀ := by
    have := conj_mem_of_mem_normalizer (hSN (S.inv_mem hs)) hm
    rwa [inv_inv] at this
  refine mem_centW_of_conj_c hWN hSN h3 hcW hcN (S.mul_mem (S.inv_mem hs) hg)
    (N₀.mul_mem hA hB) ?_
  calc s⁻¹ * g * c * (s⁻¹ * g)⁻¹ = s⁻¹ * (g * c * g⁻¹) * s := by group
    _ = s⁻¹ * (c⁻¹ * m) * s := by rw [hgc]
    _ = (s⁻¹ * c * s)⁻¹ * (s⁻¹ * m * s) := by group
    _ = (c⁻¹ * m')⁻¹ * (s⁻¹ * m * s) := by rw [hsc]
    _ = c * ((c⁻¹ * m'⁻¹ * c) * (s⁻¹ * m * s)) := by group

theorem mk_pow_eq_one_iff {W N₀ : Subgroup G} [(N₀.subgroupOf W).Normal]
    {w : G} (hw : w ∈ W) (k : ℕ) :
    (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ N₀.subgroupOf W) ^ k = 1 ↔ w ^ k ∈ N₀ := by
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp

theorem pow_relIndex_mem [Finite G] {W D : Subgroup G}
    (hWD : W ≤ Subgroup.normalizer (D : Set G)) {w : G} (hw : w ∈ W) :
    w ^ D.relIndex W ∈ D := by
  have hd : D.relIndex W = Nat.card (↥W ⧸ D.subgroupOf W) := rfl
  haveI := subgroupOf_normal_of_le hWD
  have hdiv : orderOf (QuotientGroup.mk (⟨w, hw⟩ : W) : ↥W ⧸ D.subgroupOf W) ∣ D.relIndex W := by
    rw [hd]; exact orderOf_dvd_natCard _
  exact (mk_pow_eq_one_iff hw (D.relIndex W)).mp (orderOf_dvd_iff_pow_eq_one.mp hdiv)

theorem mem_of_pow_not_dvd_three [Finite G] {W N₀ : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (h3 : N₀.relIndex W = 3)
    {x : G} (hx : x ∈ W) {r : ℕ} (hr : ¬ 3 ∣ r) (hxr : x ^ r ∈ N₀) : x ∈ N₀ := by
  haveI := subgroupOf_normal_of_le hWN
  have hq3 := (mk_pow_eq_one_iff hx 3).mpr (cube_mem_of_relIndex hWN h3 hx)
  have hqr := (mk_pow_eq_one_iff hx r).mpr hxr
  have hg : (QuotientGroup.mk (⟨x, hx⟩ : W) : ↥W ⧸ N₀.subgroupOf W) ^ (r.gcd 3) = 1 :=
    pow_gcd_eq_one.mpr ⟨hqr, hq3⟩
  have hcop : r.gcd 3 = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr)
  rw [hcop] at hg
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : W) : ↥W ⧸ N₀.subgroupOf W) ^ 1 = 1 := hg
  have h2 := (mk_pow_eq_one_iff hx 1).mp h1
  simpa using h2

theorem finish_of_x [Finite G] {W N₀ D S : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N₀ : Set G)) (h3 : N₀.relIndex W = 3)
    (hWD : W ≤ Subgroup.normalizer (D : Set G)) (hSD : S ≤ Subgroup.normalizer (D : Set G))
    {x : G} (hx : x ∈ W) (hxN : x ∉ N₀)
    (hxS : ∀ g ∈ S, (∃ e ∈ D, g * x * g⁻¹ = x * e) ∨ (∃ e ∈ D, g * x * g⁻¹ = e * x⁻¹)) :
    ∃ z ∈ W, z ∉ N₀ ∧ (∃ a : ℕ, z ^ 3 ^ a ∈ D) ∧
      S ≤ Subgroup.normalizer ((Subgroup.zpowers z ⊔ D : Subgroup G) : Set G) := by
  have hD1 : ∀ w ∈ W, ∀ d ∈ D, w * d * w⁻¹ ∈ D := fun w hw d hd =>
    (Subgroup.mem_normalizer_iff.mp (hWD hw) d).mp hd
  have hD1' : ∀ d ∈ D, x⁻¹ * d * x ∈ D := fun d hd => by
    have := hD1 x⁻¹ (W.inv_mem hx) d hd
    rwa [inv_inv] at this
  have hD2 : ∀ d ∈ D, (x⁻¹)⁻¹ * d * x⁻¹ ∈ D := fun d hd => by
    rw [inv_inv]; exact hD1 x hx d hd
  have hm0 : D.relIndex W ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨e, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hxm : x ^ D.relIndex W ∈ D := pow_relIndex_mem hWD hx
  refine ⟨x ^ m', W.pow_mem hx m', ?_, ⟨e, ?_⟩, ?_⟩
  · intro hz
    exact hxN (mem_of_pow_not_dvd_three hWN h3 hx hm' hz)
  · rw [← pow_mul, mul_comm, ← hmeq]
    exact hxm
  · refine le_normalizer_of_conj_mem S _ ?_
    intro g hg
    have hDg : ∀ d ∈ D, g * d * g⁻¹ ∈ D := fun d hd =>
      (Subgroup.mem_normalizer_iff.mp (hSD hg) d).mp hd
    have hz : g * x ^ m' * g⁻¹ ∈ (Subgroup.zpowers (x ^ m') ⊔ D : Subgroup G) := by
      rw [← conj_pow]
      rcases hxS g hg with ⟨e, he, hge⟩ | ⟨e, he, hge⟩
      · rw [hge]
        obtain ⟨e', he', heq⟩ := pow_mul_mem_coset x D hD1' e he m'
        rw [heq]
        exact (Subgroup.zpowers (x ^ m') ⊔ D).mul_mem
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_right he')
      · rw [hge, show e * x⁻¹ = x⁻¹ * (x * e * x⁻¹) by group]
        obtain ⟨e', he', heq⟩ := pow_mul_mem_coset x⁻¹ D hD2 (x * e * x⁻¹) (hD1 x hx e he) m'
        rw [heq, inv_pow]
        exact (Subgroup.zpowers (x ^ m') ⊔ D).mul_mem
          ((Subgroup.zpowers (x ^ m') ⊔ D).inv_mem
            (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) (Subgroup.mem_sup_right he')
    exact conj_mem_zpowers_sup g (x ^ m') D S hg hDg hz

theorem exists_fixed_centW [Finite G] {W N₀ D S : Subgroup G} {c : G}
    (hDN₀ : D ≤ N₀) (hN₀W : N₀ ≤ W) (hcW : c ∈ W)
    (hWN₀ : W ≤ Subgroup.normalizer (N₀ : Set G)) (h3 : N₀.relIndex W = 3)
    (hodd : ¬ 2 ∣ D.relIndex W) (hS : IsPGroup 2 S)
    (hSN₀ : S ≤ Subgroup.normalizer (N₀ : Set G)) (hSD : S ≤ Subgroup.normalizer (D : Set G)) :
    ∃ y ∈ N₀, ∀ g ∈ centW W N₀ S hWN₀ hSN₀, ∃ d ∈ D, g * (c * y) * g⁻¹ = c * y * d := by
  have hodd' : ¬ 2 ∣ D.relIndex N₀ := fun h => hodd (by
    rw [← Subgroup.relIndex_mul_relIndex (H := D) (K := N₀) (L := W) hDN₀ hN₀W, h3]
    exact Dvd.dvd.mul_right h 3)
  have hTS : centW W N₀ S hWN₀ hSN₀ ≤ S := fun g hg => (mem_centW_iff.mp hg).1
  exact exists_coset_fixed c N₀ D (centW W N₀ S hWN₀ hSN₀) hDN₀
    (isPGroup_of_le hTS hS)
    (fun g hg d hd => conj_mem_of_mem_normalizer (hSD (hTS hg)) hd)
    (fun g hg y hy => conj_mem_of_mem_normalizer (hSN₀ (hTS hg)) hy)
    (fun g hg => by
      have hgc := (mem_centW_iff.mp hg).2 c hcW
      exact ⟨c⁻¹ * (g * c * g⁻¹ * c⁻¹) * c⁻¹⁻¹,
        conj_mem_of_mem_normalizer (hWN₀ (W.inv_mem hcW)) hgc, by group⟩)
    hodd'

theorem x_not_mem [Finite G] {W N₀ S : Subgroup G}
    (hWN₀ : W ≤ Subgroup.normalizer (N₀ : Set G)) (hSN₀ : S ≤ Subgroup.normalizer (N₀ : Set G))
    (hSW : S ≤ Subgroup.normalizer (W : Set G)) (h3 : N₀.relIndex W = 3)
    {c : G} (hcW : c ∈ W) (hcN : c ∉ N₀) {y : G} (hy : y ∈ N₀)
    {s : G} (hs : s ∈ S) (hsn : s ∉ centW W N₀ S hWN₀ hSN₀) :
    c * y * (s * (c * y) * s⁻¹)⁻¹ ∉ N₀ := by
  intro hx
  obtain ⟨m, hm, hsc⟩ := conj_c_inv_of_not_mem hWN₀ hSN₀ hSW h3 hcW hcN hs hsn
  have hsy : s * y * s⁻¹ ∈ N₀ := conj_mem_of_mem_normalizer (hSN₀ hs) hy
  have hu : s * (c * y) * s⁻¹ = c⁻¹ * (m * (s * y * s⁻¹)) := by
    calc s * (c * y) * s⁻¹ = (s * c * s⁻¹) * (s * y * s⁻¹) := by group
      _ = c⁻¹ * m * (s * y * s⁻¹) := by rw [hsc]
      _ = c⁻¹ * (m * (s * y * s⁻¹)) := by group
  rw [hu] at hx
  have hk : y * (m * (s * y * s⁻¹))⁻¹ ∈ N₀ :=
    N₀.mul_mem hy (N₀.inv_mem (N₀.mul_mem hm hsy))
  have hx' : c * (y * (m * (s * y * s⁻¹))⁻¹) * c ∈ N₀ := by
    have e : c * (y * (m * (s * y * s⁻¹))⁻¹) * c = c * y * (c⁻¹ * (m * (s * y * s⁻¹)))⁻¹ := by
      group
    rw [e]; exact hx
  have hc' : c⁻¹ * (y * (m * (s * y * s⁻¹))⁻¹)⁻¹ * c⁻¹⁻¹ ∈ N₀ :=
    conj_mem_of_mem_normalizer (hWN₀ (W.inv_mem hcW)) (N₀.inv_mem hk)
  rw [inv_inv] at hc'
  have hc2 : c ^ 2 ∈ N₀ := by
    rw [pow_two]
    have e : c * c = (c * (y * (m * (s * y * s⁻¹))⁻¹) * c) *
        (c⁻¹ * (y * (m * (s * y * s⁻¹))⁻¹)⁻¹ * c) := by group
    rw [e]; exact N₀.mul_mem hx' hc'
  exact hcN (mem_of_pow_not_dvd_three hWN₀ h3 hcW (r := 2) (by norm_num) hc2)

theorem first_case_fix {T D : Subgroup G} {a s : G}
    (hfix : ∀ g ∈ T, ∃ d ∈ D, g * a * g⁻¹ = a * d)
    (hsT : ∀ g ∈ T, s⁻¹ * g * s ∈ T) (hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D)
    (huD : ∀ d ∈ D, (s * a * s⁻¹) * d * (s * a * s⁻¹)⁻¹ ∈ D) :
    ∀ g ∈ T, ∃ e ∈ D, g * (a * (s * a * s⁻¹)⁻¹) * g⁻¹ = a * (s * a * s⁻¹)⁻¹ * e := by
  intro g hg
  obtain ⟨dg, hdg, hg1⟩ := hfix g hg
  obtain ⟨d1, hd1, h1⟩ := hfix (s⁻¹ * g * s) (hsT g hg)
  have hinv : (s⁻¹ * g * s) * a⁻¹ * (s⁻¹ * g * s)⁻¹ = d1⁻¹ * a⁻¹ := by
    have e : (s⁻¹ * g * s) * a⁻¹ * (s⁻¹ * g * s)⁻¹ =
        ((s⁻¹ * g * s) * a * (s⁻¹ * g * s)⁻¹)⁻¹ := by group
    rw [e, h1, mul_inv_rev]
  have e1 : g * (s * a * s⁻¹)⁻¹ * g⁻¹ = (s * d1⁻¹ * s⁻¹) * (s * a * s⁻¹)⁻¹ := by
    calc g * (s * a * s⁻¹)⁻¹ * g⁻¹
        = s * ((s⁻¹ * g * s) * a⁻¹ * (s⁻¹ * g * s)⁻¹) * s⁻¹ := by group
      _ = s * (d1⁻¹ * a⁻¹) * s⁻¹ := by rw [hinv]
      _ = (s * d1⁻¹ * s⁻¹) * (s * a * s⁻¹)⁻¹ := by group
  refine ⟨(s * a * s⁻¹) * (dg * (s * d1⁻¹ * s⁻¹)) * (s * a * s⁻¹)⁻¹,
    huD _ (D.mul_mem hdg (hsD _ (D.inv_mem hd1))), ?_⟩
  calc g * (a * (s * a * s⁻¹)⁻¹) * g⁻¹
      = (g * a * g⁻¹) * (g * (s * a * s⁻¹)⁻¹ * g⁻¹) := by group
    _ = (a * dg) * ((s * d1⁻¹ * s⁻¹) * (s * a * s⁻¹)⁻¹) := by rw [hg1, e1]
    _ = a * (s * a * s⁻¹)⁻¹ * ((s * a * s⁻¹) * (dg * (s * d1⁻¹ * s⁻¹)) * (s * a * s⁻¹)⁻¹) := by
      group

theorem second_case_fix {D : Subgroup G} {a s d3 : G}
    (hd3 : (s * s) * a * (s * s)⁻¹ = a * d3) (hd3D : d3 ∈ D)
    (huD : ∀ d ∈ D, (s * a * s⁻¹) * d * (s * a * s⁻¹)⁻¹ ∈ D) :
    ∃ e ∈ D, s * (a * (s * a * s⁻¹)⁻¹) * s⁻¹ = e * (a * (s * a * s⁻¹)⁻¹)⁻¹ := by
  refine ⟨(s * a * s⁻¹) * d3⁻¹ * (s * a * s⁻¹)⁻¹, huD _ (D.inv_mem hd3D), ?_⟩
  calc s * (a * (s * a * s⁻¹)⁻¹) * s⁻¹
      = (s * a * s⁻¹) * ((s * s) * a * (s * s)⁻¹)⁻¹ := by group
    _ = (s * a * s⁻¹) * (a * d3)⁻¹ := by rw [hd3]
    _ = (s * a * s⁻¹) * d3⁻¹ * (s * a * s⁻¹)⁻¹ * (a * (s * a * s⁻¹)⁻¹)⁻¹ := by group

theorem hxS_of_parts {T S D : Subgroup G} {x s : G}
    (hT : ∀ g ∈ T, ∃ e ∈ D, g * x * g⁻¹ = x * e) (hTS : T ≤ S)
    (hSD : S ≤ Subgroup.normalizer (D : Set G))
    (hsx : ∃ e ∈ D, s * x * s⁻¹ = e * x⁻¹)
    (hcov : ∀ g ∈ S, g ∈ T ∨ g * s⁻¹ ∈ T) :
    ∀ g ∈ S, (∃ e ∈ D, g * x * g⁻¹ = x * e) ∨ (∃ e ∈ D, g * x * g⁻¹ = e * x⁻¹) := by
  intro g hg
  rcases hcov g hg with hgT | ht
  · exact Or.inl (hT g hgT)
  · right
    obtain ⟨e, he, hes⟩ := hsx
    obtain ⟨e1, he1, h1⟩ := hT (g * s⁻¹) ht
    have htS : g * s⁻¹ ∈ S := hTS ht
    have hx1 : (g * s⁻¹) * x⁻¹ * (g * s⁻¹)⁻¹ = e1⁻¹ * x⁻¹ := by
      calc (g * s⁻¹) * x⁻¹ * (g * s⁻¹)⁻¹ = ((g * s⁻¹) * x * (g * s⁻¹)⁻¹)⁻¹ := by group
        _ = (x * e1)⁻¹ := by rw [h1]
        _ = e1⁻¹ * x⁻¹ := by rw [mul_inv_rev]
    refine ⟨((g * s⁻¹) * e * (g * s⁻¹)⁻¹) * e1⁻¹,
      D.mul_mem (conj_mem_of_mem_normalizer (hSD htS) he) (D.inv_mem he1), ?_⟩
    calc g * x * g⁻¹ = (g * s⁻¹) * (s * x * s⁻¹) * (g * s⁻¹)⁻¹ := by group
      _ = (g * s⁻¹) * (e * x⁻¹) * (g * s⁻¹)⁻¹ := by rw [hes]
      _ = ((g * s⁻¹) * e * (g * s⁻¹)⁻¹) * ((g * s⁻¹) * x⁻¹ * (g * s⁻¹)⁻¹) := by group
      _ = ((g * s⁻¹) * e * (g * s⁻¹)⁻¹) * (e1⁻¹ * x⁻¹) := by rw [hx1]
      _ = ((g * s⁻¹) * e * (g * s⁻¹)⁻¹) * e1⁻¹ * x⁻¹ := by group

theorem exists_invariant_cyclic_supplement [Finite G] {W N₀ D S : Subgroup G}
    (hDN₀ : D ≤ N₀) (hN₀W : N₀ ≤ W) (hWD : W ≤ Subgroup.normalizer (D : Set G))
    (hWN₀ : W ≤ Subgroup.normalizer (N₀ : Set G)) (h3 : N₀.relIndex W = 3)
    (hodd : ¬ 2 ∣ D.relIndex W) (hS : IsPGroup 2 S)
    (hSW : S ≤ Subgroup.normalizer (W : Set G)) (hSN₀ : S ≤ Subgroup.normalizer (N₀ : Set G))
    (hSD : S ≤ Subgroup.normalizer (D : Set G)) :
    ∃ z ∈ W, z ∉ N₀ ∧ (∃ a : ℕ, z ^ 3 ^ a ∈ D) ∧
      S ≤ Subgroup.normalizer ((Subgroup.zpowers z ⊔ D : Subgroup G) : Set G) := by
  obtain ⟨c, hcW, hcN⟩ : ∃ c ∈ W, c ∉ N₀ := by
    by_contra hcon
    push Not at hcon
    have h1 : N₀.relIndex W = 1 :=
      Subgroup.relIndex_eq_one.mpr (fun c hc => hcon c hc)
    omega
  obtain ⟨y, hy, hfix⟩ := exists_fixed_centW (c := c) hDN₀ hN₀W hcW hWN₀ h3 hodd hS hSN₀ hSD
  have haW : c * y ∈ W := W.mul_mem hcW (hN₀W hy)
  by_cases hall : ∀ g ∈ S, g ∈ centW W N₀ S hWN₀ hSN₀
  · have haN : c * y ∉ N₀ := fun h => hcN (by simpa using N₀.mul_mem h (N₀.inv_mem hy))
    refine finish_of_x hWN₀ h3 hWD hSD haW haN ?_
    intro g hg
    obtain ⟨d, hd, e⟩ := hfix g (hall g hg)
    exact Or.inl ⟨d, hd, e⟩
  · push Not at hall
    obtain ⟨s, hs, hsn⟩ := hall
    have huW : s * (c * y) * s⁻¹ ∈ W := conj_mem_of_mem_normalizer (hSW hs) haW
    have hxW : c * y * (s * (c * y) * s⁻¹)⁻¹ ∈ W := W.mul_mem haW (W.inv_mem huW)
    have hxN := x_not_mem hWN₀ hSN₀ hSW h3 hcW hcN hy hs hsn
    have hsT : ∀ g ∈ centW W N₀ S hWN₀ hSN₀, s⁻¹ * g * s ∈ centW W N₀ S hWN₀ hSN₀ :=
      fun g hg => conj_mem_centW hWN₀ hSN₀ hSW hs hg
    have hsD : ∀ d ∈ D, s * d * s⁻¹ ∈ D := fun d hd => conj_mem_of_mem_normalizer (hSD hs) hd
    have huD : ∀ d ∈ D, (s * (c * y) * s⁻¹) * d * (s * (c * y) * s⁻¹)⁻¹ ∈ D :=
      fun d hd => conj_mem_of_mem_normalizer (hWD huW) hd
    have hL1 := first_case_fix hfix hsT hsD huD
    have hs' : s⁻¹ ∉ centW W N₀ S hWN₀ hSN₀ := fun h =>
      hsn (by simpa using (centW W N₀ S hWN₀ hSN₀).inv_mem h)
    have hs2 : s * s ∈ centW W N₀ S hWN₀ hSN₀ := by
      have := inv_mul_mem_centW hWN₀ hSN₀ hSW h3 hcW hcN (S.inv_mem hs) hs hs' hsn
      rwa [inv_inv] at this
    obtain ⟨d3, hd3, hd3eq⟩ := hfix (s * s) hs2
    obtain ⟨e, he, hes⟩ := second_case_fix hd3eq hd3 huD
    have hcov : ∀ g ∈ S, g ∈ centW W N₀ S hWN₀ hSN₀ ∨ g * s⁻¹ ∈ centW W N₀ S hWN₀ hSN₀ := by
      intro g hg
      by_cases hgT : g ∈ centW W N₀ S hWN₀ hSN₀
      · exact Or.inl hgT
      · right
        have hg' : g⁻¹ ∉ centW W N₀ S hWN₀ hSN₀ := fun h =>
          hgT (by simpa using (centW W N₀ S hWN₀ hSN₀).inv_mem h)
        have := inv_mul_mem_centW hWN₀ hSN₀ hSW h3 hcW hcN (S.inv_mem hg) (S.inv_mem hs) hg' hs'
        rwa [inv_inv] at this
    refine finish_of_x hWN₀ h3 hWD hSD hxW hxN ?_
    exact hxS_of_parts hL1 (fun g hg => (mem_centW_iff.mp hg).1) hSD ⟨e, he, hes⟩ hcov

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.InvariantCyclic

end
