module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3Basic
public import Mathlib.GroupTheory.Rank

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

theorem card_conj_mul_card_centralizer' {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card {h : G | IsConj g h} * Nat.card (centralizer {g}) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card, Subgroup.nat_card_centralizer_nat_card_stabilizer,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g
  ext h
  simp only [Set.mem_ofPred_eq, ConjAct.mem_orbit_conjAct, isConj_comm]

variable {S Q : Type*} [Group S] [Group Q]

theorem conj_mul_mem_ker_inf_centralizer (f : S →* Q) {y c : S} (hy2 : y * y = 1)
    (hks : ∀ a ∈ f.ker, a * a = 1) (hc : f c * f y = f y * f c) :
    c * y * c⁻¹ * y ∈ f.ker ⊓ centralizer ({y} : Set S) := by
  have hfy : f c * f y * (f c)⁻¹ = f y := by rw [hc]; group
  have hk : c * y * c⁻¹ * y ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, hfy, ← map_mul, hy2, map_one]
  refine Subgroup.mem_inf.2 ⟨hk, mem_centralizer_singleton_iff.2 ?_⟩
  have hw2 : (c * y * c⁻¹) * (c * y * c⁻¹) = 1 := by
    calc c * y * c⁻¹ * (c * y * c⁻¹) = c * (y * y) * c⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hsq := hks _ hk
  have h3 : y * (c * y * c⁻¹) * y = c * y * c⁻¹ := by
    calc y * (c * y * c⁻¹) * y = (c * y * c⁻¹)⁻¹ * ((c * y * c⁻¹ * y) * (c * y * c⁻¹ * y)) := by
          group
      _ = (c * y * c⁻¹)⁻¹ := by rw [hsq, mul_one]
      _ = c * y * c⁻¹ := inv_eq_of_mul_eq_one_right hw2
  calc c * y * c⁻¹ * y * y = (c * y * c⁻¹) * (y * y) := by group
    _ = c * y * c⁻¹ := by rw [hy2, mul_one]
    _ = y * (c * y * c⁻¹) * y := h3.symm
    _ = y * (c * y * c⁻¹ * y) := by group

variable [Finite S]

theorem card_ker_mul_card_range_le (f : S →* Q) {y : S} (hy2 : y * y = 1)
    (hks : ∀ a ∈ f.ker, a * a = 1) :
    Nat.card f.ker * Nat.card ↥(f.range ⊓ centralizer ({f y} : Set Q)) ≤
      Nat.card ↥(centralizer ({y} : Set S)) * Nat.card ↥(f.ker ⊓ centralizer ({y} : Set S)) := by
  classical
  set S' : Subgroup S := (centralizer ({f y} : Set Q)).comap f with hS'
  have hmemS' : ∀ s, s ∈ S' ↔ f s * f y = f y * f s := fun s => by
    rw [hS', Subgroup.mem_comap, mem_centralizer_singleton_iff]
  have hyS' : y ∈ S' := (hmemS' y).2 rfl
  have hkerS' : f.ker ≤ S' := fun k hk => by
    rw [hmemS', MonoidHom.mem_ker.1 hk, one_mul, mul_one]
  have h1 : Nat.card f.ker * Nat.card ↥(f.range ⊓ centralizer ({f y} : Set Q)) = Nat.card S' := by
    set g : ↥S' →* Q := f.comp S'.subtype with hg
    have h := Subgroup.card_ker_mul_card_range g
    have hrange : g.range = f.range ⊓ centralizer ({f y} : Set Q) := by
      ext q
      constructor
      · rintro ⟨s, rfl⟩
        exact Subgroup.mem_inf.2 ⟨⟨(s : S), rfl⟩, mem_centralizer_singleton_iff.2
          ((hmemS' s).1 s.2)⟩
      · intro hq
        obtain ⟨hqr, hqc⟩ := Subgroup.mem_inf.1 hq
        obtain ⟨s, rfl⟩ := hqr
        exact ⟨⟨s, (hmemS' s).2 (mem_centralizer_singleton_iff.1 hqc)⟩, rfl⟩
    have hkerc : Nat.card g.ker = Nat.card f.ker := by
      refine Nat.card_congr
        { toFun := fun w => ⟨((w : ↥S') : S), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 w.2)⟩
          invFun := fun k => ⟨⟨(k : S), hkerS' k.2⟩, MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 k.2)⟩
          left_inv := fun w => rfl
          right_inv := fun k => rfl }
    rw [← h, hrange, hkerc]
  have hCsub : centralizer ({y} : Set S) ≤ S' := fun c hc => by
    rw [hmemS']
    have := mem_centralizer_singleton_iff.1 hc
    rw [show f c * f y = f (c * y) from (map_mul f c y).symm, this, map_mul]
  have hC : Nat.card (centralizer ({(⟨y, hyS'⟩ : ↥S')} : Set ↥S')) =
      Nat.card (centralizer ({y} : Set S)) := by
    refine Nat.card_congr
      { toFun := fun w => ⟨((w : ↥S') : S),
          mem_centralizer_singleton_iff.2
            (congrArg Subtype.val (mem_centralizer_singleton_iff.1 w.2))⟩
        invFun := fun c => ⟨⟨(c : S), hCsub c.2⟩,
          mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_singleton_iff.1 c.2))⟩
        left_inv := fun w => rfl
        right_inv := fun c => rfl }
  have hcl : Nat.card {h : ↥S' | IsConj (⟨y, hyS'⟩ : ↥S') h} ≤
      Nat.card ↥(f.ker ⊓ centralizer ({y} : Set S)) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨((w : ↥S') : S) * y, ?_⟩) ?_
    · obtain ⟨⟨c, hc⟩, hcw⟩ := isConj_iff.1 w.2
      have hw : ((w : ↥S') : S) = c * y * c⁻¹ := by rw [← hcw]; rfl
      rw [hw]
      exact conj_mul_mem_ker_inf_centralizer f hy2 hks ((hmemS' c).1 hc)
    · intro a b hab
      have h1 := congrArg Subtype.val hab
      have h2 : ((a : ↥S') : S) = ((b : ↥S') : S) := mul_right_cancel h1
      exact Subtype.ext (Subtype.ext h2)
  have h2 := card_conj_mul_card_centralizer' (⟨y, hyS'⟩ : ↥S')
  rw [hC] at h2
  calc Nat.card f.ker * Nat.card ↥(f.range ⊓ centralizer ({f y} : Set Q))
      = Nat.card S' := h1
    _ = Nat.card {h : ↥S' | IsConj (⟨y, hyS'⟩ : ↥S') h} *
        Nat.card (centralizer ({y} : Set S)) := h2.symm
    _ ≤ Nat.card ↥(f.ker ⊓ centralizer ({y} : Set S)) *
        Nat.card (centralizer ({y} : Set S)) := Nat.mul_le_mul_right _ hcl
    _ = Nat.card ↥(centralizer ({y} : Set S)) *
        Nat.card ↥(f.ker ⊓ centralizer ({y} : Set S)) := mul_comm _ _

end CFSG.EvenSporadicStandard.M22Std
