module

public import CFSG.ClassicalInvolution.Q3.TL4AlphaFrE2D
public import CFSG.ClassicalInvolution.Q3.TL4D1ME8C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2E

open Matrix
open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin (E8Struct comm_of_sq)

@[expose] def stab3 (a : Fin 3 → ZMod 2) : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)) where
  carrier := {M | M.1 *ᵥ a = a}
  mul_mem' {M N} hM hN := by
    have hM' : M.1 *ᵥ a = a := hM
    have hN' : N.1 *ᵥ a = a := hN
    show (M.1 * N.1) *ᵥ a = a
    rw [← mulVec_mulVec, hN', hM']
  one_mem' := by
    show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a = a
    rw [one_mulVec]
  inv_mem' {M} hM := by
    have hM' : M.1 *ᵥ a = a := hM
    show M⁻¹.1 *ᵥ a = a
    have h : (M⁻¹ * M).1 *ᵥ a = a := by
      rw [inv_mul_cancel]
      show (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ a = a
      rw [one_mulVec]
    change (M⁻¹.1 * M.1) *ᵥ a = a at h
    rw [← mulVec_mulVec, hM'] at h
    exact h

theorem mem_stab3 {a : Fin 3 → ZMod 2} {M : SpecialLinearGroup (Fin 3) (ZMod 2)} :
    M ∈ stab3 a ↔ M.1 *ᵥ a = a :=
  Iff.rfl

instance (a : Fin 3 → ZMod 2) : DecidablePred (· ∈ stab3 a) := fun M =>
  inferInstanceAs (Decidable (M.1 *ᵥ a = a))

theorem card_stab3 : ∀ a : Fin 3 → ZMod 2, a ≠ 0 → Fintype.card ↥(stab3 a) = 24 := by
  decide +kernel

theorem exists_mem_stab3_not_mem : ∀ a b : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ M : SpecialLinearGroup (Fin 3) (ZMod 2), M ∈ stab3 b ∧ M ∉ stab3 a := by
  decide +kernel

theorem stab3_sup_eq_top {a b : Fin 3 → ZMod 2} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    stab3 a ⊔ stab3 b = ⊤ := by
  have h24 : Nat.card ↥(stab3 a) = 24 := by
    rw [Nat.card_eq_fintype_card]
    exact card_stab3 a ha
  have hdvd : 24 ∣ Nat.card ↥(stab3 a ⊔ stab3 b) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : stab3 a ≤ stab3 a ⊔ stab3 b)
    rwa [h24] at this
  have hdvd' : Nat.card ↥(stab3 a ⊔ stab3 b) ∣ 24 * 7 := by
    have := Subgroup.card_subgroup_dvd_card (stab3 a ⊔ stab3 b)
    rwa [card_sl3Two] at this
  have hne : Nat.card ↥(stab3 a ⊔ stab3 b) ≠ 24 := by
    intro h
    obtain ⟨M, hMb, hMa⟩ := exists_mem_stab3_not_mem a b ha hb hab
    have heq : stab3 a = stab3 a ⊔ stab3 b :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h, h24])
    have hM : M ∈ stab3 a ⊔ stab3 b := Subgroup.mem_sup_right hMb
    rw [← heq] at hM
    exact hMa hM
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hdvd' hne
  have hk7 : k ∣ 7 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd'
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hk7 with rfl | rfl
  · exact (hne (by norm_num)).elim
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hk, card_sl3Two])

variable {Y : Type} [Group Y] [Finite Y]

theorem centralizer_sup_eq_top_of_e8 {E : Subgroup Y} (hE : E8Struct ⊤ E) {a b : Y} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y) = ⊤ := by
  obtain ⟨e, he⟩ := exists_e8Basis hE.sq hE.card
  have hea : e8Coord e (e8Inv he a) = a := e8Coord_e8Inv he ha
  have heb : e8Coord e (e8Inv he b) = b := e8Coord_e8Inv he hb
  have hα : e8Inv he a ≠ 0 := fun h => ha1 (by rw [← hea, h, e8Coord_zero])
  have hβ : e8Inv he b ≠ 0 := fun h => hb1 (by rw [← heb, h, e8Coord_zero])
  have hαβ : e8Inv he a ≠ e8Inv he b := fun h => hab (by rw [← hea, ← heb, h])
  have key : ∀ x : Y, x ∈ E → ∀ y : ↥(⊤ : Subgroup Y), e8Hom hE he y ∈ stab3 (e8Inv he x) →
      (y : Y) ∈ Subgroup.centralizer ({x} : Set Y) := by
    intro x hx y hy
    have h1 := conj_e8Coord_e8Hom hE he y (e8Inv he x)
    rw [mem_stab3.mp hy, e8Coord_e8Inv he hx] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : Y) * x = y * x * (y : Y)⁻¹ * y := by group
      _ = x * y := by rw [h1]
  have hT : stab3 (e8Inv he a) ⊔ stab3 (e8Inv he b) ≤
      ((Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y)).subgroupOf
        ⊤).map (e8Hom hE he) := by
    refine sup_le (fun M hM => ?_) (fun M hM => ?_)
    · obtain ⟨y, rfl⟩ := e8Hom_surjective hE he M
      exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (key a ha y hM)), rfl⟩
    · obtain ⟨y, rfl⟩ := e8Hom_surjective hE he M
      exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (key b hb y hM)), rfl⟩
  rw [stab3_sup_eq_top hα hβ hαβ] at hT
  rw [eq_top_iff]
  intro y _
  obtain ⟨y', hy', hφ⟩ := hT (Subgroup.mem_top (e8Hom hE he ⟨y, Subgroup.mem_top y⟩))
  have hk : y'⁻¹ * ⟨y, Subgroup.mem_top y⟩ ∈ (e8Hom hE he).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, inv_mul_cancel]
  rw [ker_e8Hom] at hk
  have hkE : (y' : Y)⁻¹ * y ∈ E := Subgroup.mem_subgroupOf.mp hk
  have hkC : (y' : Y)⁻¹ * y ∈ Subgroup.centralizer ({a} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_sq hE.sq hkE ha
  have := Subgroup.mul_mem _ (Subgroup.mem_subgroupOf.mp hy') (Subgroup.mem_sup_left hkC)
  rwa [mul_inv_cancel_left] at this

variable {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem mem_e8_of_isUniqueInvolution (hd : TightDatum R S t) (hO2 : TightInO2 t)
    {E : Subgroup Y} (hE : E8Struct ⊤ E) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {u : Y} (hu : IsUniqueInvolution L u) :
    u ∈ E := by
  obtain ⟨Q, hQn, hQ2, huQ⟩ := E2D.exists_normal hd hO2 L hL u hu
  exact hE.core Q le_top (fun x _ q hq => hQn.conj_mem q hq x) hQ2 huQ

theorem linkGen_of_e8 (hd : TightDatum R S t) (hO2 : TightInO2 t) {E : Subgroup Y}
    (hE : E8Struct ⊤ E) {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    {v : Y} (hv : IsUniqueInvolution L v) :
    Subgroup.centralizer ({t} : Set Y) ⊔ Subgroup.centralizer ({v} : Set Y) ⊔
      Subgroup.centralizer ({t * v} : Set Y) = ⊤ := by
  have hut := hd.isUniqueInvolution_core
  by_cases htv : t = v
  · rw [eq_top_iff]
    intro y _
    refine Subgroup.mem_sup_right ?_
    rw [Subgroup.mem_centralizer_singleton_iff, ← htv, hut.sq, one_mul, mul_one]
  · rw [centralizer_sup_eq_top_of_e8 hE
      (mem_e8_of_isUniqueInvolution hd hO2 hE (CoreAssembly.mem_conjClass_self _) hut)
      (mem_e8_of_isUniqueInvolution hd hO2 hE hL hv) hut.ne_one hv.ne_one htv, top_sup_eq]

end CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2E
