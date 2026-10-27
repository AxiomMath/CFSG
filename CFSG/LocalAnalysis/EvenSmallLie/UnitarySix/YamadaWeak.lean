module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaInner
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.WeakClosure

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.UnitarySix.Yamada

open Subgroup CFSG.Quasithin
open scoped Pointwise
open SolomonWong (mul_comm_of_sq_eq_one card_conjSubgroup conjSubgroup_sq)

section Q

variable {Q : Type} [Group Q]

theorem card_sylow_two (D : ToddParabolic Q) (P : Sylow 2 Q) : Nat.card P = 2 ^ 15 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := D.finite
  rw [P.card_eq_multiplicity, D.card_Q]
  congr 1
  rw [show (9196830720 : ℕ) = 2 ^ 15 * 280665 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem card_le_of_sq (D : ToddParabolic Q) {Y : Subgroup Q} (hY : ∀ y ∈ Y, y ^ 2 = 1) :
    Nat.card Y ≤ 2 ^ 9 ∧
      (Nat.card Y = 2 ^ 9 → ∃ k : Q, Y = D.A.map (MulAut.conj k).toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := D.finite
  obtain ⟨P, hYP⟩ := (isPGroup_of_sq hY).exists_le_sylow
  obtain ⟨g, hg⟩ := D.exists_conj_le_S (card_sylow_two D P)
  have hψ : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hle : Y.map (MulAut.conj g).toMonoidHom ≤ D.S := by
    rintro _ ⟨y, hy, rfl⟩
    exact hg y (hYP hy)
  have hc : ∀ x ∈ Y.map (MulAut.conj g).toMonoidHom, ∀ y ∈ Y.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_sq_eq_one hY hx hy]
  obtain ⟨h1, h2⟩ := D.abelian_S _ hle hc
  rw [Subgroup.card_map_of_injective hψ] at h1 h2
  refine ⟨h1, fun h9 => ⟨g⁻¹, ?_⟩⟩
  rw [← h2 h9, Subgroup.map_map]
  ext y
  simp only [mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply]
  constructor
  · intro hy
    exact ⟨y, hy, by group⟩
  · rintro ⟨x, hx, rfl⟩
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]

end Q

section G

variable {G : Type} [Group G] {L : Subgroup G}

@[expose] def toddA (D : ToddParabolic L) : Subgroup G := D.A.map L.subtype

@[expose] def toddE (D : ToddParabolic L) (t : G) : Subgroup G := toddA D ⊔ zpowers t

theorem toddA_le (D : ToddParabolic L) : toddA D ≤ L := map_subtype_le _

theorem mem_toddA {D : ToddParabolic L} {x : G} :
    x ∈ toddA D ↔ ∃ hx : x ∈ L, (⟨x, hx⟩ : L) ∈ D.A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.2, ha⟩
  · rintro ⟨hx, hA⟩
    exact ⟨⟨x, hx⟩, hA, rfl⟩

theorem card_toddA (D : ToddParabolic L) : Nat.card (toddA D) = 2 ^ 9 := by
  rw [toddA, card_map_of_injective L.subtype_injective, D.card_A]

theorem toddA_sq (D : ToddParabolic L) : ∀ a ∈ toddA D, a ^ 2 = 1 := by
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, D.A_sq a ha, map_one]

theorem toddA_le_toddE (D : ToddParabolic L) (t : G) : toddA D ≤ toddE D t := le_sup_left

theorem t_mem_toddE (D : ToddParabolic L) (t : G) : t ∈ toddE D t :=
  mem_sup_right (mem_zpowers t)

theorem eq_one_or_eq_of_mem_zpowers {z c : G} (hz : z ^ 2 = 1) (hc : c ∈ zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rw [zpow_eq_zpow_emod k (n := 2) (by rw [zpow_two, ← sq, hz])]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem exists_eq_or_eq_mul {Y : Subgroup G} {z : G} (hz : z ^ 2 = 1)
    (hc : ∀ y ∈ Y, y * z = z * y) {x : G} (hx : x ∈ Y ⊔ zpowers z) :
    ∃ y ∈ Y, x = y ∨ x = y * z := by
  have hcomm : ∀ a ∈ Y, ∀ b ∈ zpowers z, a * b = b * a := by
    intro a ha b hb
    rcases eq_one_or_eq_of_mem_zpowers hz hb with rfl | rfl
    · rw [mul_one, one_mul]
    · exact hc a ha
  obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm hx
  rcases eq_one_or_eq_of_mem_zpowers hz hb with rfl | rfl
  · exact ⟨a, ha, Or.inl (mul_one a)⟩
  · exact ⟨a, ha, Or.inr rfl⟩

theorem sq_eq_one_of_mem_sup {Y : Subgroup G} {z : G} (hY : ∀ y ∈ Y, y ^ 2 = 1)
    (hz : z ^ 2 = 1) (hc : ∀ y ∈ Y, y * z = z * y) : ∀ x ∈ Y ⊔ zpowers z, x ^ 2 = 1 := by
  intro x hx
  obtain ⟨y, hy, hxy | hxy⟩ := exists_eq_or_eq_mul hz hc hx
  · rw [hxy]
    exact hY y hy
  · rw [hxy, (show Commute y z from hc y hy).mul_pow, hY y hy, hz, one_mul]

end G

namespace Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {D : ToddParabolic L} {t : G}

theorem comm_toddA (h : Setting G L D t) : ∀ a ∈ toddA D, a * t = t * a :=
  fun _ ha => h.comm (toddA_le D ha)

theorem toddE_sq (h : Setting G L D t) : ∀ e ∈ toddE D t, e ^ 2 = 1 :=
  sq_eq_one_of_mem_sup (toddA_sq D) h.t_sq h.comm_toddA

theorem toddE_le_H (h : Setting G L D t) : toddE D t ≤ centralizer ({t} : Set G) :=
  sup_le ((toddA_le D).trans h.le_H) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem eq_or_eq_mul_of_mem_toddE (h : Setting G L D t) {e : G} (he : e ∈ toddE D t) :
    ∃ a ∈ toddA D, e = a ∨ e = a * t :=
  exists_eq_or_eq_mul h.t_sq h.comm_toddA he

theorem card_toddE (h : Setting G L D t) : Nat.card (toddE D t) = 2 ^ 10 := by
  apply le_antisymm
  · have hsub : ((toddE D t : Subgroup G) : Set G) ⊆ (toddA D : Set G) * (zpowers t : Set G) := by
      intro x hx
      obtain ⟨a, ha, hxa | hxa⟩ := h.eq_or_eq_mul_of_mem_toddE hx
      · exact ⟨a, ha, 1, one_mem _, by simp [hxa]⟩
      · exact ⟨a, ha, t, mem_zpowers t, hxa.symm⟩
    calc Nat.card (toddE D t) = Nat.card ((toddE D t : Subgroup G) : Set G) := rfl
      _ ≤ Nat.card ((toddA D : Set G) * (zpowers t : Set G)) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ ≤ Nat.card (toddA D : Set G) * Nat.card (zpowers t : Set G) := Set.natCard_mul_le
      _ = 2 ^ 10 := by
        change Nat.card (toddA D) * Nat.card (zpowers t) = 2 ^ 10
        rw [card_toddA, Nat.card_zpowers, h.order]
        norm_num
  · have e := relIndex_mul_relIndex ⊥ _ _ bot_le (toddA_le_toddE D t)
    rw [relIndex_bot_left, relIndex_bot_left, card_toddA] at e
    have h1 : (toddA D).relIndex (toddE D t) ≠ 1 := fun h1 =>
      h.t_not_mem (toddA_le D ((relIndex_eq_one.1 h1) (t_mem_toddE D t)))
    have h0 : (toddA D).relIndex (toddE D t) ≠ 0 := relIndex_ne_zero_of_finite _ _
    rw [← e]
    calc 2 ^ 10 = 2 ^ 9 * 2 := by norm_num
      _ ≤ 2 ^ 9 * (toddA D).relIndex (toddE D t) := Nat.mul_le_mul_left _ (by omega)

omit [Finite G] in
theorem card_le_of_le_L (D : ToddParabolic L) {Y : Subgroup G} (hYL : Y ≤ L)
    (hY : ∀ y ∈ Y, y ^ 2 = 1) :
    Nat.card Y ≤ 2 ^ 9 ∧ (Nat.card Y = 2 ^ 9 → ∃ l ∈ L, Y = conjSubgroup (toddA D) l) := by
  have hY0 : ∀ y ∈ Y.subgroupOf L, y ^ 2 = 1 := fun y hy => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hY _ hy)
  have hcard : Nat.card (Y.subgroupOf L) = Nat.card Y :=
    Nat.card_congr (subgroupOfEquivOfLe hYL).toEquiv
  obtain ⟨h1, h2⟩ := card_le_of_sq D hY0
  rw [hcard] at h1 h2
  refine ⟨h1, fun h9 => ?_⟩
  obtain ⟨k, hk⟩ := h2 h9
  refine ⟨(k : G)⁻¹, inv_mem k.2, ?_⟩
  ext y
  rw [mem_conjSubgroup_iff, inv_inv]
  constructor
  · intro hy
    have hy0 : (⟨y, hYL hy⟩ : L) ∈ Y.subgroupOf L := hy
    rw [hk] at hy0
    obtain ⟨a, ha, hay⟩ := hy0
    have hay' : (k : G) * a * (k : G)⁻¹ = y := by
      have := congrArg Subtype.val hay
      simpa using this
    rw [mem_toddA]
    refine ⟨mul_mem (mul_mem (inv_mem k.2) (hYL hy)) k.2, ?_⟩
    have e : (⟨(k : G)⁻¹ * y * k, mul_mem (mul_mem (inv_mem k.2) (hYL hy)) k.2⟩ : L) = a := by
      apply Subtype.ext
      change (k : G)⁻¹ * y * k = a
      rw [← hay']
      group
    rw [e]
    exact ha
  · intro hy
    obtain ⟨hyL', hA⟩ := mem_toddA.1 hy
    have hyL : y ∈ L := by
      have := mul_mem (mul_mem k.2 hyL') (inv_mem k.2)
      rwa [show (k : G) * ((k : G)⁻¹ * y * k) * (k : G)⁻¹ = y by group] at this
    have hy0 : (⟨y, hyL⟩ : L) ∈ Y.subgroupOf L := by
      rw [hk]
      refine ⟨_, hA, Subtype.ext ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, coe_mul, coe_inv]
      group
    exact hy0

theorem conjSubgroup_le (h : Setting G L D t) {g : G}
    (hg : conjSubgroup (toddE D t) g ≤ centralizer ({t} : Set G)) :
    conjSubgroup (toddE D t) g ≤ L ⊔ zpowers t :=
  conjSubgroup_le_of_rank (F := L ⊔ (centralizer (L : Set G) ⊓ centralizer ({t} : Set G)))
    h.toddE_sq h.card_toddE
    (fun τ hτ hτ2 hτF B hB hB2 => (h.card_le_of_not_mem hτ
      (by rw [← hτ2]; exact pow_orderOf_eq_one τ) hτF hB hB2).trans_lt (by norm_num))
    (fun y hy hy2 => by
      obtain ⟨l, hl, -, rfl | rfl⟩ := h.eq_or_eq_mul_t hy hy2
      · exact mem_sup_left hl
      · exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers t)))
    hg

theorem sylowType (h : Setting G L D t) {g : G}
    (hg : conjSubgroup (toddE D t) g ≤ centralizer ({t} : Set G)) :
    ∃ l ∈ L, conjSubgroup (toddE D t) g = conjSubgroup (toddE D t) l := by
  set X := conjSubgroup (toddE D t) g with hXdef
  have hXLt : X ≤ L ⊔ zpowers t := h.conjSubgroup_le hg
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 := conjSubgroup_sq h.toddE_sq g
  have hXc : Nat.card X = 2 ^ 10 := by rw [card_conjSubgroup, h.card_toddE]
  have hcLt : ∀ y ∈ L, y * t = t * y := fun y hy => h.comm hy
  have hidx : L.relIndex X ≤ 2 := by
    apply SolomonWong.index_le_two_of_forall
    intro v₁ v₂ hv₁ hv₂
    rw [mem_subgroupOf] at hv₁ hv₂ ⊢
    obtain ⟨l₁, hl₁, h₁ | h₁⟩ := exists_eq_or_eq_mul h.t_sq hcLt (hXLt v₁.2)
    · exact absurd (h₁ ▸ hl₁) hv₁
    obtain ⟨l₂, hl₂, h₂ | h₂⟩ := exists_eq_or_eq_mul h.t_sq hcLt (hXLt v₂.2)
    · exact absurd (h₂ ▸ hl₂) hv₂
    simp only [coe_mul, coe_inv, h₁, h₂]
    have hm : (l₁⁻¹ * l₂) * t = t * (l₁⁻¹ * l₂) := hcLt _ (mul_mem (inv_mem hl₁) hl₂)
    have e : (l₁ * t)⁻¹ * (l₂ * t) = l₁⁻¹ * l₂ := by
      calc (l₁ * t)⁻¹ * (l₂ * t) = t⁻¹ * ((l₁⁻¹ * l₂) * t) := by group
        _ = t⁻¹ * (t * (l₁⁻¹ * l₂)) := by rw [hm]
        _ = l₁⁻¹ * l₂ := by group
    rw [e]
    exact mul_mem (inv_mem hl₁) hl₂
  have hXL : Nat.card X = Nat.card (L ⊓ X : Subgroup G) * L.relIndex X := by
    rw [← relIndex_bot_left, ← relIndex_bot_left, ← inf_relIndex_right L X,
      relIndex_mul_relIndex _ _ _ bot_le inf_le_right]
  obtain ⟨hle9, heq⟩ :=
    card_le_of_le_L D (Y := L ⊓ X) inf_le_left (fun y hy => hX2 y (mem_inf.1 hy).2)
  have hY9 : Nat.card (L ⊓ X : Subgroup G) = 2 ^ 9 := by
    refine le_antisymm hle9 ?_
    by_contra hc
    push Not at hc
    have : Nat.card (L ⊓ X : Subgroup G) * L.relIndex X < 2 ^ 9 * 2 :=
      Nat.mul_lt_mul_of_lt_of_le hc hidx (by norm_num)
    omega
  obtain ⟨l, hl, hYl⟩ := heq hY9
  have hXnL : ¬ X ≤ L := fun hXL' => by
    rw [inf_of_le_right hXL'] at hY9
    omega
  obtain ⟨x, hxX, hxL⟩ := Set.not_subset.1 hXnL
  obtain ⟨l', hl', hxl | hxl⟩ := exists_eq_or_eq_mul h.t_sq hcLt (hXLt hxX)
  · exact absurd (hxl ▸ hl') hxL
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 (hg hxX)
  have hl'e : l' = x * t := by rw [hxl, mul_assoc, ← sq, h.t_sq, mul_one]
  have hl'c : ∀ y ∈ L ⊓ X, y * l' = l' * y := by
    intro y hy
    have h1 : y * x = x * y := mul_comm_of_sq_eq_one hX2 hy.2 hxX
    have h2 : y * t = t * y := hcLt y hy.1
    rw [hl'e]
    calc y * (x * t) = (y * x) * t := by group
      _ = x * (y * t) := by rw [h1, mul_assoc]
      _ = x * t * y := by rw [h2, mul_assoc]
  have hl'2 : l' ^ 2 = 1 := by
    rw [hl'e, (show Commute x t from hxt).mul_pow, hX2 x hxX, h.t_sq, one_mul]
  have hYsup : (L ⊓ X) ⊔ zpowers l' ≤ L := sup_le inf_le_left (zpowers_le.2 hl')
  have hYsq := sq_eq_one_of_mem_sup (fun y hy => hX2 y (mem_inf.1 hy).2) hl'2 hl'c
  have hYeq : (L ⊓ X : Subgroup G) = (L ⊓ X) ⊔ zpowers l' :=
    eq_of_le_of_card_ge le_sup_left (by
      rw [hY9]
      exact (card_le_of_le_L D hYsup hYsq).1)
  have hl'X : l' ∈ X := by
    have : l' ∈ (L ⊓ X : Subgroup G) := hYeq ▸ mem_sup_right (mem_zpowers l')
    exact this.2
  have htX : t ∈ X := by
    have : t = l'⁻¹ * x := by rw [hxl]; group
    rw [this]
    exact mul_mem (inv_mem hl'X) hxX
  refine ⟨l, hl, (eq_of_le_of_card_ge (fun y hy => ?_) ?_).symm⟩
  · rw [mem_conjSubgroup_iff] at hy
    have hlt : l * t = t * l := hcLt l hl
    obtain ⟨a, ha, hya | hya⟩ := h.eq_or_eq_mul_of_mem_toddE hy
    · have hy' : y = l⁻¹ * a * l := by rw [← hya]; group
      have : y ∈ (L ⊓ X : Subgroup G) := by
        rw [hYl, mem_conjSubgroup_iff, hy']
        rwa [show l * (l⁻¹ * a * l) * l⁻¹ = a by group]
      exact this.2
    · have hy' : y = l⁻¹ * a * l * t := by
        calc y = l⁻¹ * (l * y * l⁻¹) * l := by group
          _ = l⁻¹ * a * (t * l) := by rw [hya]; group
          _ = l⁻¹ * a * l * t := by rw [← hlt]; group
      have : l⁻¹ * a * l ∈ (L ⊓ X : Subgroup G) := by
        rw [hYl, mem_conjSubgroup_iff]
        rwa [show l * (l⁻¹ * a * l) * l⁻¹ = a by group]
      rw [hy']
      exact mul_mem this.2 htX
  · rw [hXc, card_conjSubgroup, h.card_toddE]

theorem fusion (h : Setting G L D t) {g : G} (hg : g⁻¹ * t * g ∈ toddE D t) :
    ∃ n ∈ normalizer (toddE D t : Set G), g⁻¹ * t * g = n⁻¹ * t * n :=
  exists_normalizer_conj_eq (fun _ hb _ hc => mul_comm_of_sq_eq_one h.toddE_sq hb hc)
    (fun _ hg' => by
      obtain ⟨l, hl, e⟩ := h.sylowType hg'
      exact ⟨l, h.le_H hl, e⟩) hg

end Setting

end CFSG.EvenSmallLie.UnitarySix.Yamada
