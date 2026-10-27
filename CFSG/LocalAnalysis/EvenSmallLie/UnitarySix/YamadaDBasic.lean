module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

@[expose] def oTwo (X : Subgroup G) : Subgroup G :=
  sSup {P : Subgroup G | P ≤ X ∧ X ≤ normalizer (P : Set G) ∧ IsPGroup 2 P}

theorem le_oTwo {X P : Subgroup G} (hPX : P ≤ X) (hXP : X ≤ normalizer (P : Set G))
    (hP : IsPGroup 2 P) : P ≤ oTwo X :=
  le_sSup ⟨hPX, hXP, hP⟩

theorem oTwo_le (X : Subgroup G) : oTwo X ≤ X :=
  sSup_le fun _ h => h.1

theorem conj_mem_oTwo {X : Subgroup G} {x g : G} (hx : x ∈ X) (hg : g ∈ oTwo X) :
    x * g * x⁻¹ ∈ oTwo X := by
  have hle : oTwo X ≤ (oTwo X).comap (MulAut.conj x).toMonoidHom := by
    refine sSup_le fun P hP y hy => ?_
    change x * y * x⁻¹ ∈ oTwo X
    exact le_oTwo hP.1 hP.2.1 hP.2.2 ((mem_normalizer_iff.mp (hP.2.1 hx) y).mp hy)
  exact hle hg

theorem le_normalizer_oTwo (X : Subgroup G) : X ≤ normalizer (oTwo X : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_oTwo hx, fun hg => ?_⟩
  have := conj_mem_oTwo (X.inv_mem hx) hg
  simpa [mul_assoc] using this

theorem sup_mem_oTwoSet {X P Q : Subgroup G} (hP : P ≤ X ∧ X ≤ normalizer (P : Set G) ∧
    IsPGroup 2 P) (hQ : Q ≤ X ∧ X ≤ normalizer (Q : Set G) ∧ IsPGroup 2 Q) :
    P ⊔ Q ≤ X ∧ X ≤ normalizer ((P ⊔ Q : Subgroup G) : Set G) ∧ IsPGroup 2 ↥(P ⊔ Q) := by
  refine ⟨sup_le hP.1 hQ.1, fun x hx => ?_, ?_⟩
  · have hle : ∀ y : G, y ∈ X → P ⊔ Q ≤ (P ⊔ Q).comap (MulAut.conj y).toMonoidHom := by
      intro y hy
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact mem_sup_left ((mem_normalizer_iff.mp (hP.2.1 hy) g).mp hg)
      · exact mem_sup_right ((mem_normalizer_iff.mp (hQ.2.1 hy) g).mp hg)
    rw [mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hle x hx hg, fun hg => ?_⟩
    have := hle x⁻¹ (X.inv_mem hx) hg
    simpa [mul_assoc] using this
  · exact IsPGroup.to_sup_of_normal_right' hP.2.2 hQ.2.2 (hP.1.trans hQ.2.1)

theorem isPGroup_oTwo [Finite G] (X : Subgroup G) : IsPGroup 2 (oTwo X) := by
  classical
  set Ps := {P : Subgroup G | P ≤ X ∧ X ≤ normalizer (P : Set G) ∧ IsPGroup 2 P} with hPs
  have hbot : (⊥ : Subgroup G) ∈ Ps :=
    ⟨bot_le, fun x _ => by rw [normalizer_eq_top (H := ⊥)]; trivial, IsPGroup.of_bot⟩
  obtain ⟨P₀, hP₀, hmax⟩ : ∃ P₀ ∈ Ps, ∀ P ∈ Ps, Nat.card P ≤ Nat.card P₀ := by
    have : Nonempty Ps := ⟨⟨⊥, hbot⟩⟩
    obtain ⟨⟨P₀, hP₀⟩, hmax⟩ := Finite.exists_max fun P : Ps => Nat.card (P : Subgroup G)
    exact ⟨P₀, hP₀, fun P hP => hmax ⟨P, hP⟩⟩
  have hle : ∀ P ∈ Ps, P ≤ P₀ := by
    intro P hP
    have hsup := sup_mem_oTwoSet hP₀ hP
    have heq : P₀ ⊔ P = P₀ := (Subgroup.eq_of_le_of_card_ge le_sup_left (hmax _ hsup)).symm
    rw [← heq]
    exact le_sup_right
  have : oTwo X = P₀ := le_antisymm (sSup_le hle) (le_sSup hP₀)
  rw [this]
  exact hP₀.2.2

theorem crossed_mul {t x y : G} (ht : t * t = 1)
    (hy : (x⁻¹ * t * x * t) * y = y * (x⁻¹ * t * x * t)) :
    (x * y)⁻¹ * t * (x * y) * t = (x⁻¹ * t * x * t) * (y⁻¹ * t * y * t) := by
  have h1 : y⁻¹ * (x⁻¹ * t * x * t) * y = x⁻¹ * t * x * t := by
    rw [mul_assoc, hy]; group
  calc (x * y)⁻¹ * t * (x * y) * t = y⁻¹ * x⁻¹ * t * x * (t * t) * y * t := by
        rw [ht]; group
    _ = y⁻¹ * (x⁻¹ * t * x * t) * y * (y⁻¹ * t * y * t) := by group
    _ = (x⁻¹ * t * x * t) * (y⁻¹ * t * y * t) := by rw [h1]

theorem crossed_inv {t x : G} (ht : t * t = 1)
    (hx : (x⁻¹ * t * x * t) * x = x * (x⁻¹ * t * x * t)) :
    x⁻¹⁻¹ * t * x⁻¹ * t = (x⁻¹ * t * x * t)⁻¹ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set c := x⁻¹ * t * x * t with hcdef
  have hc : x * c⁻¹ = c⁻¹ * x := by
    calc x * c⁻¹ = c⁻¹ * (c * x) * c⁻¹ := by group
      _ = c⁻¹ * (x * c) * c⁻¹ := by rw [hx]
      _ = c⁻¹ * x := by group
  have h1 : x * c⁻¹ * x⁻¹ = c⁻¹ := by rw [hc]; group
  calc x⁻¹⁻¹ * t * x⁻¹ * t = x * (t⁻¹ * x⁻¹ * t⁻¹ * x) * x⁻¹ := by rw [ht']; group
    _ = x * c⁻¹ * x⁻¹ := by rw [hcdef]; group
    _ = c⁻¹ := h1

theorem crossed_conj {t x h : G} (hh : h * t = t * h) :
    (h * x * h⁻¹)⁻¹ * t * (h * x * h⁻¹) * t = h * (x⁻¹ * t * x * t) * h⁻¹ := by
  have h1 : h⁻¹ * t * h = t := by
    calc h⁻¹ * t * h = h⁻¹ * (t * h) := by group
      _ = h⁻¹ * (h * t) := by rw [hh]
      _ = t := by group
  have h2 : h⁻¹ * t = t * h⁻¹ := by
    calc h⁻¹ * t = h⁻¹ * (t * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * t) * h⁻¹ := by rw [hh]
      _ = t * h⁻¹ := by group
  calc (h * x * h⁻¹)⁻¹ * t * (h * x * h⁻¹) * t = h * x⁻¹ * (h⁻¹ * t * h) * x * (h⁻¹ * t) := by
        group
    _ = h * x⁻¹ * t * x * (t * h⁻¹) := by rw [h1, h2]
    _ = h * (x⁻¹ * t * x * t) * h⁻¹ := by group

theorem crossed_eq_one_iff {t x : G} (ht : t * t = 1) :
    x⁻¹ * t * x * t = 1 ↔ x * t = t * x := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  constructor
  · intro h1
    have : x⁻¹ * t * x = t := by
      rw [← mul_inv_eq_one, ht']
      exact h1
    calc x * t = x * (x⁻¹ * t * x) := by rw [this]
      _ = t * x := by group
  · intro h1
    calc x⁻¹ * t * x * t = x⁻¹ * (t * x) * t := by group
      _ = 1 := by rw [← h1]; group; rw [ht]

theorem exists_conj_fixed [Finite G] {T : Set G} {e : G} (he : e ^ 3 = 1)
    (hT : ∀ x ∈ T, e * x * e⁻¹ ∈ T) (h3 : ¬ 3 ∣ T.ncard) : ∃ x ∈ T, e * x * e⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype T := Fintype.ofFinite T
  let f : Function.End T := fun x => ⟨e * x * e⁻¹, hT x x.2⟩
  have he3 : e * e * e = 1 := by rw [← he, pow_three, mul_assoc]
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    change e * (e * (e * (x : G) * e⁻¹) * e⁻¹) * e⁻¹ = x
    calc e * (e * (e * (x : G) * e⁻¹) * e⁻¹) * e⁻¹ = (e * e * e) * x * (e * e * e)⁻¹ := by
          group
      _ = x := by rw [he3]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := T) hf3
  have hcard : Fintype.card T = T.ncard := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  rw [hcard] at hmod
  have hpos : 0 < Fintype.card (Function.fixedPoints f) := by
    rcases Nat.eq_zero_or_pos (Fintype.card (Function.fixedPoints f)) with h0 | h0
    · rw [h0] at hmod
      exact absurd (Nat.modEq_zero_iff_dvd.mp hmod) h3
    · exact h0
  obtain ⟨⟨x, hx⟩⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem card_eq_card_ker_mul_card_range {X Y : Type*} [Group X] [Group Y] (f : X →* Y) :
    Nat.card X = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

@[expose] def crossedHom {t : G} (ht : t * t = 1) (B Y : Subgroup G)
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B) : Y →* B where
  toFun y := ⟨(y : G)⁻¹ * t * y * t, hY y y.2⟩
  map_one' := by
    apply Subtype.ext
    change (1 : G)⁻¹ * t * 1 * t = 1
    rw [inv_one, one_mul, mul_one, ht]
  map_mul' x y := by
    apply Subtype.ext
    change ((x : G) * y)⁻¹ * t * (x * y) * t = ((x : G)⁻¹ * t * x * t) * ((y : G)⁻¹ * t * y * t)
    refine crossed_mul ht ?_
    exact mem_centralizer_iff.mp (hYB y.2) _ (hY x x.2)

theorem crossedHom_apply {t : G} (ht : t * t = 1) {B Y : Subgroup G}
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B) (y : Y) :
    ((crossedHom ht B Y hYB hY y : B) : G) = (y : G)⁻¹ * t * y * t :=
  rfl

theorem mem_ker_crossedHom {t : G} (ht : t * t = 1) {B Y : Subgroup G}
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B) (y : Y) :
    y ∈ (crossedHom ht B Y hYB hY).ker ↔ (y : G) * t = t * y := by
  rw [MonoidHom.mem_ker, ← crossed_eq_one_iff ht]
  constructor
  · intro h1
    exact congrArg Subtype.val h1
  · intro h1
    exact Subtype.ext h1

theorem card_eq_of_crossed {t : G} (ht : t * t = 1) {B Y : Subgroup G}
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B) :
    Nat.card Y = Nat.card (Y ⊓ centralizer ({t} : Set G) : Subgroup G) *
      Nat.card (crossedHom ht B Y hYB hY).range := by
  rw [card_eq_card_ker_mul_card_range (crossedHom ht B Y hYB hY)]
  congr 1
  have hker : (crossedHom ht B Y hYB hY).ker =
      (Y ⊓ centralizer ({t} : Set G)).subgroupOf Y := by
    ext y
    rw [mem_ker_crossedHom, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h1 => ⟨y.2, h1⟩, fun h1 => h1.2⟩
  rw [hker]
  exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv

theorem card_eq_of_crossed_onto {t : G} (ht : t * t = 1) {B Y : Subgroup G}
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B)
    (honto : ∀ b ∈ B, ∃ y ∈ Y, y⁻¹ * t * y * t = b) :
    Nat.card Y = Nat.card (Y ⊓ centralizer ({t} : Set G) : Subgroup G) * Nat.card B := by
  rw [card_eq_of_crossed ht hYB hY]
  congr 1
  have : (crossedHom ht B Y hYB hY).range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨b, hb⟩ -
    obtain ⟨y, hy, hyb⟩ := honto b hb
    exact ⟨⟨y, hy⟩, Subtype.ext hyb⟩
  rw [this]
  exact Nat.card_congr (Subgroup.topEquiv).toEquiv

theorem card_le_of_crossed {t : G} (ht : t * t = 1) {B Y : Subgroup G} [Finite B]
    (hYB : Y ≤ centralizer (B : Set G)) (hY : ∀ y ∈ Y, y⁻¹ * t * y * t ∈ B) :
    Nat.card Y ≤ Nat.card (Y ⊓ centralizer ({t} : Set G) : Subgroup G) * Nat.card B := by
  rw [card_eq_of_crossed ht hYB hY]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_card_group _)

theorem mem_sup_zpowers_iff {B : Subgroup G} {t : G} (ht : t * t = 1)
    (hB : ∀ b ∈ B, b * t = t * b) {x : G} : x ∈ B ⊔ zpowers t ↔ x ∈ B ∨ x * t ∈ B := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hconj : ∀ b ∈ B, t * b * t ∈ B := by
    intro b hb
    rw [← hB b hb, mul_assoc, ht, mul_one]
    exact hb
  let S : Subgroup G :=
    { carrier := {x | x ∈ B ∨ x * t ∈ B}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (B.mul_mem hx hy)
        · right
          rw [mul_assoc]
          exact B.mul_mem hx hy
        · right
          have : x * y * t = (x * t) * (t * y * t) := by
            calc x * y * t = x * (t * t) * y * t := by rw [ht, mul_one]
              _ = (x * t) * (t * y * t) := by group
          rw [this]
          exact B.mul_mem hx (hconj y hy)
        · left
          have : x * y = (x * t) * (t * (y * t) * t) := by
            calc x * y = x * (t * t) * y * (t * t) := by rw [ht, mul_one, mul_one]
              _ = (x * t) * (t * (y * t) * t) := by group
          rw [this]
          exact B.mul_mem hx (hconj _ hy)
      one_mem' := Or.inl B.one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (B.inv_mem hx)
        · right
          have : x⁻¹ * t = t * (x * t)⁻¹ * t := by rw [ht'.symm]; group
          rw [this]
          exact hconj _ (B.inv_mem hx) }
  have hle : B ⊔ zpowers t ≤ S := by
    refine sup_le (fun b hb => Or.inl hb) ?_
    rw [zpowers_le]
    right
    rw [ht]
    exact B.one_mem
  constructor
  · intro hx
    exact hle hx
  · rintro (hx | hx)
    · exact mem_sup_left hx
    · have : x = (x * t) * t := by rw [mul_assoc, ht, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left hx) (mem_sup_right (mem_zpowers t))

theorem card_sup_zpowers {B : Subgroup G} {t : G} (ht : t * t = 1)
    (hB : ∀ b ∈ B, b * t = t * b) (htB : t ∉ B) :
    Nat.card (B ⊔ zpowers t : Subgroup G) = 2 * Nat.card B := by
  have hBle : B ≤ B ⊔ zpowers t := le_sup_left
  have hidx : (B.subgroupOf (B ⊔ zpowers t)).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨t, mem_sup_right (mem_zpowers t)⟩, fun b => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf]
    change Xor ((b : G) * t ∈ B) ((b : G) ∈ B)
    rcases (mem_sup_zpowers_iff ht hB).mp b.2 with h1 | h1
    · refine Or.inr ⟨h1, fun h2 => htB ?_⟩
      have : t = (b : G)⁻¹ * ((b : G) * t) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem h1) h2
    · refine Or.inl ⟨h1, fun h2 => htB ?_⟩
      have : t = (b : G)⁻¹ * ((b : G) * t) := by group
      rw [this]
      exact B.mul_mem (B.inv_mem h2) h1
  have := (B.subgroupOf (B ⊔ zpowers t)).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hBle).toEquiv] at this
  rw [← this, mul_comm]

theorem mem_normalizer_of_conj_mem [Finite G] {B : Subgroup G} {x : G}
    (h : ∀ b ∈ B, x * b * x⁻¹ ∈ B) : x ∈ normalizer (B : Set G) := by
  have hle : B.map (MulAut.conj x).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have heq : B.map (MulAut.conj x).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulEquiv.injective _)).ge
  rw [mem_normalizer_iff]
  intro g
  refine ⟨h g, fun hg => ?_⟩
  rw [← heq] at hg
  obtain ⟨y, hy, hyg⟩ := hg
  have : y = g := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyg
    exact mul_left_cancel (mul_right_cancel hyg)
  rwa [← this]

end CFSG.EvenSmallLie.UnitarySix.YamadaD
