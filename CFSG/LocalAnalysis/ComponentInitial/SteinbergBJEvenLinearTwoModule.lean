module

public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule

section Defs

variable {G A : Type*} [Group G] [Group A]

@[expose] def actionFixed (ρ : G →* MulAut A) (H : Subgroup G) : Subgroup A where
  carrier := {x | ∀ h ∈ H, ρ h x = x}
  mul_mem' {x y} hx hy h hh := by rw [map_mul, hx h hh, hy h hh]
  one_mem' h _ := map_one (ρ h)
  inv_mem' {x} hx h hh := by rw [map_inv, hx h hh]

theorem mem_actionFixed {ρ : G →* MulAut A} {H : Subgroup G} {x : A} :
    x ∈ actionFixed ρ H ↔ ∀ h ∈ H, ρ h x = x :=
  Iff.rfl

@[expose] def actionStab (ρ : G →* MulAut A) (x : A) : Subgroup G :=
  (MulAction.stabilizer (MulAut A) x).comap ρ

theorem mem_actionStab {ρ : G →* MulAut A} {x : A} {g : G} :
    g ∈ actionStab ρ x ↔ ρ g x = x :=
  Iff.rfl

end Defs

variable {K : Type*} [Field K]

@[expose] def diagTorus (K : Type*) [Field K] : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := Set.range diagElt
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, (diagElt_mul_diagElt a b).symm⟩
  one_mem' := ⟨1, diagElt_one⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, (diagElt_inv a).symm⟩

theorem mem_diagTorus {g : SpecialLinearGroup (Fin 2) K} :
    g ∈ diagTorus K ↔ ∃ a : Kˣ, diagElt a = g :=
  Iff.rfl

theorem upperElt_mul_lowerElt_mul_upperElt_mul (g : SpecialLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) (c : K) :
    upperElt K ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) *
        lowerElt K c *
        upperElt K (-((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0)) *
        g =
      g * upperElt K (-c / (g : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2) := by
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    first
      | ring1
      | linear_combination (-((g : Matrix (Fin 2) (Fin 2) K) 0 0 * c)) * hdet
      | linear_combination (-c) * hdet

theorem upperUnipotent_sup_map_conj_eq_top {g : SpecialLinearGroup (Fin 2) K}
    (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    upperUnipotent K ⊔ (upperUnipotent K).map (MulAut.conj g).toMonoidHom = ⊤ := by
  refine eq_top_iff.2 ?_
  rw [← upperUnipotent_sup_lowerUnipotent]
  refine sup_le le_sup_left fun x hx => ?_
  obtain ⟨c, rfl⟩ := (mem_lowerUnipotent_iff K).1 hx
  have hu : ∀ t, upperElt K t ∈
      upperUnipotent K ⊔ (upperUnipotent K).map (MulAut.conj g).toMonoidHom :=
    fun t => Subgroup.mem_sup_left ((mem_upperUnipotent_iff K).2 ⟨t, rfl⟩)
  have hconj : g * upperElt K (-c / (g : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2) * g⁻¹ ∈
      upperUnipotent K ⊔ (upperUnipotent K).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_sup_right ⟨_, (mem_upperUnipotent_iff K).2 ⟨_, rfl⟩, rfl⟩
  have h := eq_mul_inv_of_mul_eq (upperElt_mul_lowerElt_mul_upperElt_mul g hg c)
  have hid : lowerElt K c = (upperElt K ((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
      (g : Matrix (Fin 2) (Fin 2) K) 1 0))⁻¹ *
      (g * upperElt K (-c / (g : Matrix (Fin 2) (Fin 2) K) 1 0 ^ 2) * g⁻¹) *
      (upperElt K (-((g : Matrix (Fin 2) (Fin 2) K) 0 0 /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0)))⁻¹ := by
    rw [← h]
    group
  rw [hid]
  exact mul_mem (mul_mem (inv_mem (hu _)) hconj) (inv_mem (hu _))

theorem lowerElt_one_mul_diagElt_mul_lowerElt_one_apply (a : Kˣ) :
    ((lowerElt K 1 * diagElt a * lowerElt K 1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 = a + ((a⁻¹ : Kˣ) : K) := by
  simp [coe_diagElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two]

section CharTwo

variable [CharP K 2]

theorem weylElt_inv_eq : (weylElt K)⁻¹ = weylElt K :=
  inv_eq_of_mul_eq_one_right weylElt_mul_self

theorem lowerElt_one_mul_self : lowerElt K 1 * lowerElt K 1 = 1 := by
  rw [lowerElt_mul, CharTwo.add_self_eq_zero, lowerElt_zero]

theorem upperElt_one_mul_lowerElt_one :
    upperElt K 1 * lowerElt K 1 = lowerElt K 1 * weylElt K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylElt, coe_upperElt, coe_lowerElt, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.add_self_eq_zero]

theorem val_add_val_inv_ne_zero {a : Kˣ} (ha : a ≠ 1) : (a : K) + ((a⁻¹ : Kˣ) : K) ≠ 0 := by
  intro h
  apply ha
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hmul : (a : K) * ((a : K) + ((a⁻¹ : Kˣ) : K)) = 0 := by rw [h, mul_zero]
  rw [mul_add, Units.mul_inv] at hmul
  have hsq : ((a : K) + 1) * ((a : K) + 1) = 0 := by linear_combination hmul + (a : K) * h2
  have h3 : (a : K) + 1 = 0 := mul_self_eq_zero.mp hsq
  ext
  rw [Units.val_one]
  linear_combination h3 - h2

end CharTwo

section Fixed

variable {A : Type*} [Group A] {ρ : SpecialLinearGroup (Fin 2) K →* MulAut A}

theorem eq_one_of_mem_of_inv_apply_mem (hD : actionFixed ρ ⊤ = ⊥)
    {g : SpecialLinearGroup (Fin 2) K} (hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) {x : A}
    (hx : x ∈ actionFixed ρ (upperUnipotent K))
    (hgx : ρ g⁻¹ x ∈ actionFixed ρ (upperUnipotent K)) : x = 1 := by
  have hB : upperUnipotent K ≤ actionStab ρ x := fun b hb => hx b hb
  have hgB : (upperUnipotent K).map (MulAut.conj g).toMonoidHom ≤ actionStab ρ x := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_actionStab]
    change ρ (g * b * g⁻¹) x = x
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, hgx b hb, map_inv,
      MulAut.apply_inv_self]
  have htop : ⊤ ≤ actionStab ρ x := upperUnipotent_sup_map_conj_eq_top hg ▸ sup_le hB hgB
  have hfix : x ∈ actionFixed ρ ⊤ := fun h _ => htop (Subgroup.mem_top h)
  rw [hD] at hfix
  exact hfix

end Fixed

section Module

variable [CharP K 2] {A : Type*} [CommGroup A] {ρ : SpecialLinearGroup (Fin 2) K →* MulAut A}

theorem disjoint_map_weylElt (hD : actionFixed ρ ⊤ = ⊥) :
    Disjoint (actionFixed ρ (upperUnipotent K))
      ((actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)).toMonoidHom) := by
  rw [Subgroup.disjoint_def]
  rintro _ hx ⟨y, hy, rfl⟩
  refine eq_one_of_mem_of_inv_apply_mem hD (g := weylElt K) (by simp [coe_weylElt]) hx ?_
  change ρ (weylElt K)⁻¹ (ρ (weylElt K) y) ∈ _
  rwa [map_inv, MulAut.inv_apply_self]

theorem isComplement'_map_weylElt [Finite A] (hD : actionFixed ρ ⊤ = ⊥)
    (hA : Nat.card A = Nat.card (actionFixed ρ (upperUnipotent K)) *
      Nat.card (actionFixed ρ (upperUnipotent K))) :
    (actionFixed ρ (upperUnipotent K)).IsComplement'
      ((actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)).toMonoidHom) := by
  refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ (disjoint_map_weylElt hD)
  rw [Subgroup.card_map_of_injective (by exact (ρ (weylElt K)).injective), hA]

variable (hD : actionFixed ρ ⊤ = ⊥)
  (hc : (actionFixed ρ (upperUnipotent K)).IsComplement'
    ((actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)).toMonoidHom))
include hD hc

omit hD in
theorem exists_eq_mul_weylElt_apply (x : A) :
    ∃ u ∈ actionFixed ρ (upperUnipotent K), ∃ y ∈ actionFixed ρ (upperUnipotent K),
      x = u * ρ (weylElt K) y := by
  obtain ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, h⟩ := hc.2 x
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨u, hu, y, hy, h.symm⟩

theorem mem_of_upperElt_apply_eq {t : K} (ht : t ≠ 0) {x : A}
    (hx : ρ (upperElt K t) x = x) : x ∈ actionFixed ρ (upperUnipotent K) := by
  obtain ⟨u, hu, y, hy, rfl⟩ := exists_eq_mul_weylElt_apply hc x
  have htB : upperElt K t ∈ upperUnipotent K := (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩
  rw [map_mul, hu _ htB, mul_right_inj] at hx
  have hl : ρ (lowerElt K t) y = y := by
    rw [← weylElt_mul_upperElt_mul_weylElt, map_mul, map_mul, MulAut.mul_apply,
      MulAut.mul_apply, hx, ← MulAut.mul_apply, ← map_mul, weylElt_mul_self, map_one,
      MulAut.one_apply]
  have hli : ρ (lowerElt K t)⁻¹ y = y := by
    rw [map_inv]
    calc (ρ (lowerElt K t))⁻¹ y = (ρ (lowerElt K t))⁻¹ (ρ (lowerElt K t) y) := by rw [hl]
      _ = y := MulAut.inv_apply_self _ _ _
  have hy1 : y = 1 :=
    eq_one_of_mem_of_inv_apply_mem hD (g := lowerElt K t) (by simpa [coe_lowerElt] using ht) hy
      (by rw [hli]; exact hy)
  rw [hy1, map_one, mul_one]
  exact hu

theorem lowerElt_one_apply_mem {x : A} (hx : ρ (weylElt K) x = x) :
    ρ (lowerElt K 1) x ∈ actionFixed ρ (upperUnipotent K) := by
  refine mem_of_upperElt_apply_eq hD hc one_ne_zero ?_
  rw [← MulAut.mul_apply, ← map_mul, upperElt_one_mul_lowerElt_one, map_mul, MulAut.mul_apply,
    hx]

theorem eq_one_of_diagElt_apply_eq {a : Kˣ} (ha : a ≠ 1) {u : A}
    (hu : u ∈ actionFixed ρ (upperUnipotent K)) (hau : ρ (diagElt a) u = u) : u = 1 := by
  have hau' : ρ (diagElt a)⁻¹ u = u := by
    rw [map_inv]
    calc (ρ (diagElt a))⁻¹ u = (ρ (diagElt a))⁻¹ (ρ (diagElt a) u) := by rw [hau]
      _ = u := MulAut.inv_apply_self _ _ _
  have hcomm : diagElt a * weylElt K = weylElt K * (diagElt a)⁻¹ := by
    rw [diagElt_inv, weylElt_mul_diagElt, inv_inv]
  have hav : ρ (diagElt a) (ρ (weylElt K) u) = ρ (weylElt K) u := by
    rw [← MulAut.mul_apply, ← map_mul, hcomm, map_mul, MulAut.mul_apply, hau']
  have hWW : ∀ z : A, ρ (weylElt K) (ρ (weylElt K) z) = z := fun z => by
    rw [← MulAut.mul_apply, ← map_mul, weylElt_mul_self, map_one, MulAut.one_apply]
  have hWx : ρ (weylElt K) (u * ρ (weylElt K) u) = u * ρ (weylElt K) u := by
    rw [map_mul, hWW, mul_comm]
  have hav' : ρ (diagElt a)⁻¹ (ρ (weylElt K) u) = ρ (weylElt K) u := by
    rw [map_inv]
    calc (ρ (diagElt a))⁻¹ (ρ (weylElt K) u) =
        (ρ (diagElt a))⁻¹ (ρ (diagElt a) (ρ (weylElt K) u)) := by rw [hav]
      _ = ρ (weylElt K) u := MulAut.inv_apply_self _ _ _
  have hyU := lowerElt_one_apply_mem hD hc hWx
  have hl : (lowerElt K 1)⁻¹ = lowerElt K 1 := inv_eq_of_mul_eq_one_right lowerElt_one_mul_self
  have hll : ∀ z : A, ρ (lowerElt K 1) (ρ (lowerElt K 1) z) = z := fun z => by
    rw [← MulAut.mul_apply, ← map_mul, lowerElt_one_mul_self, map_one, MulAut.one_apply]
  have hg : ((lowerElt K 1 * diagElt a * lowerElt K 1 : SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    rw [lowerElt_one_mul_diagElt_mul_lowerElt_one_apply]
    exact val_add_val_inv_ne_zero ha
  have hgy : ρ (lowerElt K 1 * diagElt a * lowerElt K 1)⁻¹
      (ρ (lowerElt K 1) (u * ρ (weylElt K) u)) = ρ (lowerElt K 1) (u * ρ (weylElt K) u) := by
    simp only [_root_.mul_inv_rev, hl, map_mul, MulAut.mul_apply, hll, hau', hav']
  have hy1 := eq_one_of_mem_of_inv_apply_mem hD hg hyU (by rw [hgy]; exact hyU)
  rw [map_eq_one_iff _ (ρ (lowerElt K 1)).injective] at hy1
  have hu' : u ∈ (actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)).toMonoidHom := by
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    change ρ (weylElt K) u⁻¹ = u
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_left hy1).symm
  exact Subgroup.disjoint_def.mp (disjoint_map_weylElt hD) hu hu'

omit [CharP K 2] hD hc in
theorem diagElt_apply_mem (a : Kˣ) {u : A} (hu : u ∈ actionFixed ρ (upperUnipotent K)) :
    ρ (diagElt a) u ∈ actionFixed ρ (upperUnipotent K) := by
  intro b hb
  have hb' : (diagElt a)⁻¹ * b * diagElt a ∈ upperUnipotent K := by
    have := (Subgroup.mem_normalizer_iff.mp (diagElt_mem_normalizer_upperUnipotent a⁻¹) b).mp hb
    rwa [← diagElt_inv, inv_inv] at this
  calc ρ b (ρ (diagElt a) u) = ρ (diagElt a) (ρ ((diagElt a)⁻¹ * b * diagElt a) u) := by
        simp only [map_mul, MulAut.mul_apply, map_inv, MulAut.apply_inv_self]
    _ = ρ (diagElt a) u := by rw [hu _ hb']

theorem exists_diagElt_apply_eq [Finite A] [Finite K]
    (hcard : Nat.card (actionFixed ρ (upperUnipotent K)) = Nat.card K) {u u' : A}
    (hu : u ∈ actionFixed ρ (upperUnipotent K)) (hu1 : u ≠ 1)
    (hu' : u' ∈ actionFixed ρ (upperUnipotent K)) (hu'1 : u' ≠ 1) :
    ∃ a : Kˣ, ρ (diagElt a) u = u' := by
  classical
  have hinj : Function.Injective fun a : Kˣ => ρ (diagElt a) u := by
    intro a b hab
    simp only at hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    apply hu1
    refine eq_one_of_diagElt_apply_eq hD hc hba hu ?_
    rw [← diagElt_mul_diagElt, map_mul, MulAut.mul_apply, hab, ← diagElt_inv, map_inv,
      MulAut.inv_apply_self]
  have hsub : Set.range (fun a : Kˣ => ρ (diagElt a) u) ⊆
      (actionFixed ρ (upperUnipotent K) : Set A) \ {1} := by
    rintro _ ⟨a, rfl⟩
    refine ⟨diagElt_apply_mem a hu, ?_⟩
    rw [Set.mem_singleton_iff, map_eq_one_iff _ (ρ (diagElt a)).injective]
    exact hu1
  have hle : ((actionFixed ρ (upperUnipotent K) : Set A) \ {1}).ncard ≤
      (Set.range fun a : Kˣ => ρ (diagElt a) u).ncard := by
    rw [Set.ncard_range_of_injective hinj, Set.ncard_sdiff_singleton_of_mem (by exact one_mem _),
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard, Nat.card_units]
  have heq := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
  have hmem : u' ∈ (actionFixed ρ (upperUnipotent K) : Set A) \ {1} := ⟨hu', hu'1⟩
  rw [← heq] at hmem
  exact hmem

theorem exists_apply_eq_of_ne_one [Finite A] [Finite K]
    (hcard : Nat.card (actionFixed ρ (upperUnipotent K)) = Nat.card K) {u₀ : A}
    (hu₀ : u₀ ∈ actionFixed ρ (upperUnipotent K)) (hu₀1 : u₀ ≠ 1) {x : A} (hx : x ≠ 1) :
    ∃ d, ρ d u₀ = x := by
  obtain ⟨u, hu, y, hy, rfl⟩ := exists_eq_mul_weylElt_apply hc x
  by_cases hy1 : y = 1
  · rw [hy1, map_one, mul_one] at hx ⊢
    obtain ⟨a, ha⟩ := exists_diagElt_apply_eq hD hc hcard hu₀ hu₀1 hu hx
    exact ⟨diagElt a, ha⟩
  by_cases hu1 : u = 1
  · obtain ⟨a, ha⟩ := exists_diagElt_apply_eq hD hc hcard hu₀ hu₀1 hy hy1
    exact ⟨weylElt K * diagElt a, by rw [map_mul, MulAut.mul_apply, ha, hu1, one_mul]⟩
  obtain ⟨a, ha⟩ := exists_diagElt_apply_eq hD hc hcard hu hu1 hy hy1
  obtain ⟨b, hb⟩ : ∃ b : Kˣ, b * b = a := by
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' (a : K)
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    exact ⟨Units.mk0 r hr0, Units.ext hr.symm⟩
  have hdiag : ∀ (c e : Kˣ) (z : A), ρ (diagElt c) (ρ (diagElt e) z) = ρ (diagElt (c * e)) z :=
    fun c e z => by rw [← MulAut.mul_apply, ← map_mul, diagElt_mul_diagElt]
  have hcomm : diagElt b * weylElt K = weylElt K * diagElt b⁻¹ := by
    rw [weylElt_mul_diagElt, inv_inv]
  have hz : ρ (diagElt b) (u * ρ (weylElt K) y) =
      ρ (diagElt b) u * ρ (weylElt K) (ρ (diagElt b) u) := by
    rw [map_mul, ← MulAut.mul_apply (e₁ := ρ (diagElt b)), ← map_mul, hcomm, map_mul,
      MulAut.mul_apply, ← ha, hdiag, ← hb, inv_mul_cancel_left]
  have hWW : ∀ z : A, ρ (weylElt K) (ρ (weylElt K) z) = z := fun z => by
    rw [← MulAut.mul_apply, ← map_mul, weylElt_mul_self, map_one, MulAut.one_apply]
  have hWz : ρ (weylElt K) (ρ (diagElt b) u * ρ (weylElt K) (ρ (diagElt b) u)) =
      ρ (diagElt b) u * ρ (weylElt K) (ρ (diagElt b) u) := by
    rw [map_mul, hWW, mul_comm]
  have hmem := lowerElt_one_apply_mem hD hc hWz
  have hne : ρ (lowerElt K 1) (ρ (diagElt b) u * ρ (weylElt K) (ρ (diagElt b) u)) ≠ 1 := by
    rw [← hz, ne_eq, map_eq_one_iff _ (ρ (lowerElt K 1)).injective,
      map_eq_one_iff _ (ρ (diagElt b)).injective]
    exact hx
  obtain ⟨a', ha'⟩ := exists_diagElt_apply_eq hD hc hcard hu₀ hu₀1 hmem hne
  refine ⟨(lowerElt K 1 * diagElt b)⁻¹ * diagElt a', ?_⟩
  rw [map_mul, MulAut.mul_apply, ha', ← hz, ← MulAut.mul_apply (e₁ := ρ (lowerElt K 1)), ← map_mul,
    map_inv, MulAut.inv_apply_self]

theorem card_actionStab_and_transitive [Finite A] [Finite K]
    (hcard : Nat.card (actionFixed ρ (upperUnipotent K)) = Nat.card K)
    (hA : Nat.card A = Nat.card K ^ 2) :
    (∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ d, ρ d x = y) ∧
      ∀ x : A, x ≠ 1 → Nat.card (actionStab ρ x) = Nat.card K := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u₀ ∈ actionFixed ρ (upperUnipotent K), u₀ ≠ 1 := by
    have : Nontrivial (actionFixed ρ (upperUnipotent K)) :=
      Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hq)
    obtain ⟨⟨v, hv⟩, hv1⟩ := exists_ne (1 : actionFixed ρ (upperUnipotent K))
    exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩
  have htrans : ∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ d, ρ d x = y := by
    intro x y hx hy
    obtain ⟨d₁, hd₁⟩ := exists_apply_eq_of_ne_one hD hc hcard hu₀ hu₀1 hx
    obtain ⟨d₂, hd₂⟩ := exists_apply_eq_of_ne_one hD hc hcard hu₀ hu₀1 hy
    refine ⟨d₂ * d₁⁻¹, ?_⟩
    rw [map_mul, MulAut.mul_apply, ← hd₁, map_inv, MulAut.inv_apply_self, hd₂]
  refine ⟨htrans, fun x hx => ?_⟩
  let : MulAction (SpecialLinearGroup (Fin 2) K) A := MulAction.compHom A ρ
  have horbit : MulAction.orbit (SpecialLinearGroup (Fin 2) K) x = {y | y ≠ 1} := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      change ρ d x ≠ 1
      rw [ne_eq, map_eq_one_iff _ (ρ d).injective]
      exact hx
    · intro hy
      exact htrans x y hx hy
  have hstab : actionStab ρ x = MulAction.stabilizer (SpecialLinearGroup (Fin 2) K) x :=
    Subgroup.ext fun _ => Iff.rfl
  have hidx : (actionStab ρ x).index = Nat.card A - 1 := by
    rw [hstab, MulAction.index_stabilizer, horbit,
      show {y : A | y ≠ 1} = Set.univ \ {1} by ext; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  have hmul := (actionStab ρ x).card_mul_index
  rw [hidx, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hA] at hmul
  have hpos : 0 < Nat.card K ^ 2 - 1 := by
    have := Nat.one_lt_pow two_ne_zero hq
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

end Module

theorem even_linear_two_half_fixed_module_transitivity {n : ℕ} [CharP K 2]
    (hK : Nat.card K = 2 ^ n) {A : Type*} [CommGroup A] (hA : Nat.card A = (2 ^ n) ^ 2)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut A) (hD : actionFixed ρ ⊤ = ⊥)
    (hB : Nat.card (actionFixed ρ (upperUnipotent K)) = 2 ^ n) :
    Function.Injective ρ ∧
      (actionFixed ρ (upperUnipotent K)).IsComplement'
        ((actionFixed ρ (upperUnipotent K)).map (ρ (weylElt K)⁻¹).toMonoidHom) ∧
      (∀ t ∈ diagTorus K, ∀ u ∈ actionFixed ρ (upperUnipotent K),
        ρ t u ∈ actionFixed ρ (upperUnipotent K)) ∧
      (∀ u ∈ actionFixed ρ (upperUnipotent K), u ≠ 1 →
        ∀ u' ∈ actionFixed ρ (upperUnipotent K), u' ≠ 1 → ∃! t : diagTorus K, ρ t u = u') ∧
      (∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ d, ρ d x = y) ∧
      (∀ u ∈ actionFixed ρ (upperUnipotent K), u ≠ 1 →
        ∀ d, ρ d u = u ↔ d ∈ upperUnipotent K) ∧
      ∀ x : A, x ≠ 1 → ∃ P : Sylow 2 (SpecialLinearGroup (Fin 2) K), ∀ d, ρ d x = x ↔ d ∈ P := by
  have hKf : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hAf : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; positivity)
  have hcard : Nat.card (actionFixed ρ (upperUnipotent K)) = Nat.card K := hB.trans hK.symm
  have hA' : Nat.card A = Nat.card K ^ 2 := by rw [hA, hK]
  have hc := isComplement'_map_weylElt hD (by rw [hA', hcard, sq])
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hn : n ≠ 0 := by
    rintro rfl
    rw [hK, pow_zero] at hq
    exact lt_irrefl 1 hq
  obtain ⟨htrans, hstab⟩ := card_actionStab_and_transitive hD hc hcard hA'
  have hstabB : ∀ u ∈ actionFixed ρ (upperUnipotent K), u ≠ 1 →
      ∀ d, ρ d u = u ↔ d ∈ upperUnipotent K := by
    intro u hu hu1 d
    have heq : upperUnipotent K = actionStab ρ u :=
      Subgroup.eq_of_le_of_card_ge (fun b hb => hu b hb)
        (by rw [hstab u hu1, card_upperUnipotent])
    rw [heq, mem_actionStab]
  obtain ⟨u₀, hu₀, hu₀1⟩ : ∃ u₀ ∈ actionFixed ρ (upperUnipotent K), u₀ ≠ 1 := by
    have : Nontrivial (actionFixed ρ (upperUnipotent K)) :=
      Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hq)
    obtain ⟨⟨v, hv⟩, hv1⟩ := exists_ne (1 : actionFixed ρ (upperUnipotent K))
    exact ⟨v, hv, fun h => hv1 (Subtype.ext h)⟩
  refine ⟨?_, ?_, ?_, ?_, htrans, hstabB, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro d hd
    have hdB : d ∈ upperUnipotent K := (hstabB u₀ hu₀ hu₀1 d).1 (by rw [hd, MulAut.one_apply])
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff K).1 hdB
    have hl : lowerElt K t ∈ upperUnipotent K := by
      refine (hstabB u₀ hu₀ hu₀1 _).1 ?_
      rw [← weylElt_mul_upperElt_mul_weylElt, map_mul, map_mul, hd, mul_one, ← map_mul,
        weylElt_mul_self, map_one, MulAut.one_apply]
    obtain ⟨s, hs⟩ := (mem_upperUnipotent_iff K).1 hl
    have ht : t = 0 := by
      have := congrArg
        (fun g : SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 0) hs
      simpa [coe_lowerElt, coe_upperElt] using this
    rw [ht, upperElt_zero]
  · rw [weylElt_inv_eq]
    exact hc
  · rintro _ ⟨a, rfl⟩ u hu
    exact diagElt_apply_mem a hu
  · intro u hu hu1 u' hu' hu'1
    obtain ⟨a, ha⟩ := exists_diagElt_apply_eq hD hc hcard hu hu1 hu' hu'1
    refine ⟨⟨diagElt a, a, rfl⟩, ha, ?_⟩
    rintro ⟨_, b, rfl⟩ hb
    have hba : b = a := by
      by_contra hne
      have h1 : a⁻¹ * b ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
      apply hu1
      refine eq_one_of_diagElt_apply_eq hD hc h1 hu ?_
      change ρ (diagElt b) u = u' at hb
      rw [← diagElt_mul_diagElt, map_mul, MulAut.mul_apply, hb, ← ha, ← diagElt_inv, map_inv,
        MulAut.inv_apply_self]
    subst hba
    rfl
  · intro x hx
    have hcardx : Nat.card (actionStab ρ x) = 2 ^ n := (hstab x hx).trans hK
    have hp : IsPGroup 2 (actionStab ρ x) := IsPGroup.of_card hcardx
    have hidx : ¬ 2 ∣ (actionStab ρ x).index := by
      have hmul := (actionStab ρ x).card_mul_index
      rw [hcardx, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK] at hmul
      rw [Nat.eq_of_mul_eq_mul_left (by positivity) hmul]
      have hd : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn) two_ne_zero
      have hpos : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      generalize (2 ^ n) ^ 2 = Q at hd hpos ⊢
      omega
    exact ⟨hp.toSylow hidx, fun d => by rw [IsPGroup.mem_toSylow, mem_actionStab]⟩

end CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule
