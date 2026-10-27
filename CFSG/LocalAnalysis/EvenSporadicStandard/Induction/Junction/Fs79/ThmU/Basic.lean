module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Transport
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Standard

public section

namespace CFSG.EvenSporadicStandard.Induction.ThmU

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def cj (x : G) (M : Subgroup G) : Subgroup G := M.map (MulAut.conj x).toMonoidHom

@[expose] def GoodInv (B : Subgroup G) (x : G) : Prop :=
  orderOf x = 2 ∧ IsCompIn B (centralizer ({x} : Set G))

@[expose] def BadInv (B : Subgroup G) (y : G) : Prop :=
  orderOf y = 2 ∧ B ≤ centralizer ({y} : Set G) ∧ ¬ IsCompIn B (centralizer ({y} : Set G))

@[expose] def UniversalF (B : Subgroup G) : Prop := ∀ y : G, ¬ BadInv B y

@[expose] def LayerBalanceAt (G : Type) [Group G] : Prop :=
  ∀ (S : Subgroup G) (t : G), IsPGroup 2 S → orderOf t = 2 → t ∈ S → (∀ x ∈ S, x * t = t * x) →
    ∀ K : Subgroup G, IsCompIn K (centralizer (S : Set G)) →
      K ≤ layerIn (centralizer ({t} : Set G))

theorem mem_cj {x g : G} {M : Subgroup G} : g ∈ cj x M ↔ x⁻¹ * g * x ∈ M := by
  rw [cj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_cj {x m : G} {M : Subgroup G} (hm : m ∈ M) : x * m * x⁻¹ ∈ cj x M := by
  exact Subgroup.mem_map.2 ⟨m, hm, by simp [MulAut.conj_apply]⟩

theorem mem_cj_of_mul_self {x g : G} {M : Subgroup G} (hx : x * x = 1) :
    g ∈ cj x M ↔ x * g * x ∈ M := by
  rw [mem_cj, inv_eq_of_mul_eq_one_right hx]

theorem cj_cj_of_mul_self {x : G} (hx : x * x = 1) (M : Subgroup G) : cj x (cj x M) = M := by
  ext g
  rw [mem_cj_of_mul_self hx, mem_cj_of_mul_self hx]
  have hxx : x * (x * g * x) * x = g := by
    calc x * (x * g * x) * x = (x * x) * g * (x * x) := by group
      _ = g := by rw [hx]; group
  rw [hxx]

theorem card_cj (x : G) (M : Subgroup G) : Nat.card (cj x M) = Nat.card M := by
  rw [cj]
  exact (Nat.card_congr (M.equivMapOfInjective (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).toEquiv).symm

theorem cj_mono (x : G) {M N : Subgroup G} (h : M ≤ N) : cj x M ≤ cj x N := by
  rw [cj, cj]
  exact Subgroup.map_mono h

theorem cj_centralizer_singleton (x y : G) :
    cj x (centralizer ({y} : Set G)) = centralizer ({x * y * x⁻¹} : Set G) := by
  ext g
  rw [mem_cj, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g * (x * y * x⁻¹) = x * ((x⁻¹ * g * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * g * x)) * x⁻¹ := by rw [h]
      _ = (x * y * x⁻¹) * g := by group
  · intro h
    calc (x⁻¹ * g * x) * y = x⁻¹ * (g * (x * y * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * y * x⁻¹) * g) * x := by rw [h]
      _ = y * (x⁻¹ * g * x) := by group

theorem cj_eq_of_commute {x : G} {M : Subgroup G} (h : ∀ m ∈ M, x * m = m * x) : cj x M = M := by
  ext g
  rw [mem_cj]
  constructor
  · intro hg
    have hm : x * (x⁻¹ * g * x) = (x⁻¹ * g * x) * x := h _ hg
    have hg' : g = x⁻¹ * g * x := by
      calc g = x * (x⁻¹ * g * x) * x⁻¹ := by group
        _ = (x⁻¹ * g * x) * x * x⁻¹ := by rw [hm]
        _ = x⁻¹ * g * x := by group
    rw [hg']; exact hg
  · intro hg
    have hm : x * g = g * x := h g hg
    have hg' : x⁻¹ * g * x = g := by
      calc x⁻¹ * g * x = x⁻¹ * (g * x) := by group
        _ = x⁻¹ * (x * g) := by rw [hm]
        _ = g := by group
    rw [hg']; exact hg

theorem isCompIn_cj {M X : Subgroup G} (h : IsCompIn M X) (c : G) :
    IsCompIn (cj c M) (cj c X) := by
  rw [cj, cj]
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  let φ : ↥X ≃* ↥(X.map (MulAut.conj c).toMonoidHom) :=
    Subgroup.equivMapOfInjective X (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv φ h.2
  have heq : (M.subgroupOf X).map φ.toMonoidHom =
      (M.map (MulAut.conj c).toMonoidHom).subgroupOf
        (X.map (MulAut.conj c).toMonoidHom) := by
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨(w : G), hw, rfl⟩
    · rintro ⟨m, hm, hmz⟩
      obtain ⟨x, hx, hxz⟩ := z.2
      have hmx : m = x := (MulAut.conj c).injective (hmz.trans hxz.symm)
      refine ⟨⟨m, hmx ▸ hx⟩, hm, ?_⟩
      apply Subtype.ext
      exact hmz
  rwa [heq] at hc

theorem isCompIn_cj_of_mem {M X : Subgroup G} (h : IsCompIn M X) {c : G} (hc : c ∈ X) :
    IsCompIn (cj c M) X :=
  h.map_conj hc

theorem isCompIn_cj_centralizer {M : Subgroup G} {x y : G} (hxy : x * y = y * x)
    (h : IsCompIn M (centralizer ({y} : Set G))) :
    IsCompIn (cj x M) (centralizer ({y} : Set G)) := by
  have hxy' : x * y * x⁻¹ = y := by rw [hxy]; group
  have hc := isCompIn_cj h x
  rwa [cj_centralizer_singleton x y, hxy'] at hc

theorem mul_self_eq_one_of_orderOf {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

theorem GoodInv.le_centralizer {B : Subgroup G} {x : G} (h : GoodInv B x) :
    B ≤ centralizer ({x} : Set G) := h.2.1

theorem BadInv.not_goodInv {B : Subgroup G} {y : G} (h : BadInv B y) : ¬ GoodInv B y :=
  fun hg => h.2.2 hg.2

theorem goodInv_of_not_badInv {B : Subgroup G} {y : G} (hy : orderOf y = 2)
    (hB : B ≤ centralizer ({y} : Set G)) (h : ¬ BadInv B y) : GoodInv B y := by
  refine ⟨hy, ?_⟩
  by_contra hnc
  exact h ⟨hy, hB, hnc⟩

theorem universalF_iff {B : Subgroup G} :
    UniversalF B ↔ ∀ y : G, orderOf y = 2 → B ≤ centralizer ({y} : Set G) →
      IsCompIn B (centralizer ({y} : Set G)) := by
  constructor
  · intro h y hy hB
    exact (goodInv_of_not_badInv hy hB (h y)).2
  · intro h y hb
    exact hb.2.2 (h y hb.1 hb.2.1)

theorem GoodInv.conj {B : Subgroup G} {x c : G} (h : GoodInv B x) (hc : ∀ b ∈ B, c * b = b * c) :
    GoodInv B (c * x * c⁻¹) := by
  refine ⟨?_, ?_⟩
  · show orderOf (c * x * c⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
  · have hcomp := isCompIn_cj h.2 c
    rwa [cj_eq_of_commute hc, cj_centralizer_singleton c x] at hcomp

theorem BadInv.conj {B : Subgroup G} {y c : G} (h : BadInv B y) (hc : ∀ b ∈ B, c * b = b * c) :
    BadInv B (c * y * c⁻¹) := by
  have hc' : ∀ b ∈ B, c⁻¹ * b = b * c⁻¹ := by
    intro b hb
    have hbc : c * b = b * c := hc b hb
    have h1 : c⁻¹ * b * c = b := by
      rw [mul_assoc, ← hbc, ← mul_assoc, inv_mul_cancel, one_mul]
    calc c⁻¹ * b = c⁻¹ * b * c * c⁻¹ := by group
      _ = b * c⁻¹ := by rw [h1]
  refine ⟨?_, ?_, ?_⟩
  · show orderOf (c * y * c⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
  · intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hby : b * y = y * b := Subgroup.mem_centralizer_singleton_iff.1 (h.2.1 hb)
    have hbc : b * c = c * b := (hc b hb).symm
    have hbc' : b * c⁻¹ = c⁻¹ * b := (hc' b hb).symm
    calc b * (c * y * c⁻¹) = (b * c) * y * c⁻¹ := by group
      _ = (c * b) * y * c⁻¹ := by rw [hbc]
      _ = c * (b * y) * c⁻¹ := by group
      _ = c * (y * b) * c⁻¹ := by rw [hby]
      _ = c * y * (b * c⁻¹) := by group
      _ = c * y * (c⁻¹ * b) := by rw [hbc']
      _ = (c * y * c⁻¹) * b := by group
  · intro hcomp
    have hcy : orderOf (c * y * c⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.1]
    have hg : GoodInv B (c * y * c⁻¹) := ⟨hcy, hcomp⟩
    have hconj := GoodInv.conj (c := c⁻¹) hg hc'
    have hy' : c⁻¹ * (c * y * c⁻¹) * (c⁻¹)⁻¹ = y := by group
    rw [hy'] at hconj
    exact h.2.2 hconj.2

theorem IsCompIn.perfect {M X : Subgroup G} (h : IsCompIn M X) : ⁅M, M⁆ = M :=
  Subgroup.isPerfect_iff.mp h.isQuasisimple.1

theorem IsCompIn.not_commute {M X : Subgroup G} (h : IsCompIn M X) :
    ¬ ∀ a ∈ M, ∀ b ∈ M, a * b = b * a :=
  not_forall_commute_of_isQuasisimple h.isQuasisimple

theorem layerIn_le_normalizer [Finite G] {L X : Subgroup G} (h : IsCompIn L X) :
    layerIn X ≤ normalizer (L : Set G) := by
  refine sSup_le fun K hK => ?_
  by_cases hKL : K = L
  · rw [hKL]
    exact Subgroup.le_normalizer
  · intro x hx
    refine Subgroup.centralizer_le_normalizer (L : Set G)
      (mem_centralizer_iff.2 fun b hb => ?_)
    exact (hK.commute_of_ne h hKL x hx b hb).symm

theorem IsCompIn.le_layerIn {M X : Subgroup G} (h : IsCompIn M X) : M ≤ layerIn X :=
  le_sSup h

theorem exists_isCompIn_not_commute [Finite G] {B X : Subgroup G} (hB : CFSG.IsQuasisimple ↥B)
    (hBX : B ≤ layerIn X) :
    ∃ L : Subgroup G, IsCompIn L X ∧ ¬ ∀ b ∈ B, ∀ l ∈ L, b * l = l * b := by
  by_contra h
  push Not at h
  apply not_forall_commute_of_isQuasisimple hB
  intro a ha b hb
  have hlayer : layerIn X ≤ Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun K hK => ?_
    intro l hlK
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h K hK a ha l hlK).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hlayer (hBX hb))).symm

theorem commute_of_le_sup_of_ne [Finite G] {X M N L B : Subgroup G} (hM : IsCompIn M X)
    (hN : IsCompIn N X) (hL : IsCompIn L X) (hLM : L ≠ M) (hLN : L ≠ N) (hB : B ≤ M ⊔ N) :
    ∀ b ∈ B, ∀ l ∈ L, b * l = l * b := by
  intro b hb l hl
  have hMl : M ≤ Subgroup.centralizer ({l} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hM.commute_of_ne hL hLM.symm m hm l hl
  have hNl : N ≤ Subgroup.centralizer ({l} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hN.commute_of_ne hL hLN.symm n hn l hl
  exact Subgroup.mem_centralizer_singleton_iff.1 ((sup_le hMl hNl) (hB hb))

theorem LayerBalanceAt.le_layerIn [Finite G] (hLB : LayerBalanceAt G) {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a * b = b * a) {K : Subgroup G}
    (hK : IsCompIn K (centralizer ({a} : Set G))) (hKb : K ≤ centralizer ({b} : Set G)) :
    K ≤ layerIn (centralizer ({b} : Set G)) := by
  let S : Subgroup G := zpowers a ⊔ zpowers b
  have hTa : IsPGroup 2 ↥(zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)
  have hTb : IsPGroup 2 ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; norm_num)
  have hNorm : zpowers b ≤ Subgroup.normalizer (zpowers a : Subgroup G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer ((zpowers a : Subgroup G) : Set G))
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hle : (zpowers a : Subgroup G) ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hab
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  have hSp : IsPGroup 2 ↥S := hTa.to_sup_of_normal_left' hTb hNorm
  have hZX : Subgroup.centralizer (S : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le
      (Set.singleton_subset_iff.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
  have hKZ : K ≤ Subgroup.centralizer (S : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hka : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hK.1 hk)
    have hkb : k * b = b * k := Subgroup.mem_centralizer_singleton_iff.1 (hKb hk)
    have hza : (zpowers a : Subgroup G) ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hka.symm
    have hzb : (zpowers b : Subgroup G) ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.2 hkb.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 ((sup_le hza hzb) hx)
  have hKcomp : IsCompIn K (Subgroup.centralizer (S : Set G)) :=
    isCompIn_of_le hK hKZ hZX
  have hcomm : ∀ x ∈ S, x * b = b * x := by
    intro x hx
    have hSb : S ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 hab
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.2 rfl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hSb hx)
  exact hLB S b hSp hb (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) hcomm K hKcomp

end CFSG.EvenSporadicStandard.Induction.ThmU
