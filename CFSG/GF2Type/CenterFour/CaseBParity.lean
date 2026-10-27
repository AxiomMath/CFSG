module

public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.GF2Type.CenterFour.BasicIndex
public import CFSG.GF2Type.CenterFour.CaseBCard
public import CFSG.GF2Type.CenterFour.CaseBPsiHom

public section

namespace CFSG.GF2Type.CenterFour

section Pairing

variable {P : Type*} [Group P] [Finite P] (S : Subgroup P) [S.Normal]

open scoped IsMulCommutative in
theorem exists_card_eq_mul_two_pow_two_mul (B : P → P → ZMod 2)
    (hcomm : ∀ a b : P, (a * b)⁻¹ * (b * a) ∈ S) (hsq : ∀ a : P, a * a ∈ S)
    (hl : ∀ a b c, B (a * b) c = B a c + B b c) (hr : ∀ a b c, B a (b * c) = B a b + B a c)
    (halt : ∀ a, B a a = 0) (hinv : ∀ a, ∀ s ∈ S, ∀ b, B (a * s) b = B a b)
    (hnd : ∀ a, (∀ b, B a b = 0) → a ∈ S) :
    ∃ m : ℕ, Nat.card P = Nat.card S * 2 ^ (2 * m) := by
  have two_add : ∀ t : ZMod 2, t + t = 0 := by decide
  have hsymm : ∀ a b, B a b = B b a := by
    intro a b
    have h := halt (a * b)
    rw [hl, hr, hr, halt a, halt b] at h
    linear_combination h - two_add (B b a)
  have hinv' : ∀ a, ∀ s ∈ S, ∀ b, B a (b * s) = B a b := fun a s hs b => by
    rw [hsymm a (b * s), hinv b s hs a, hsymm b a]
  have hMcomm : ∀ a b : P ⧸ S, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rename_i x y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact hcomm x y
  haveI : CFSG.IsElementaryAbelian 2 (P ⧸ S) :=
    { is_comm := ⟨hMcomm⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun q => by
        induction q using QuotientGroup.induction_on
        rename_i x
        rw [sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        exact hsq _) }
  let Bq : P ⧸ S → P ⧸ S → ZMod 2 := fun a b =>
    Quotient.liftOn₂' a b B (fun x₁ y₁ x₂ y₂ hx hy => by
      rw [QuotientGroup.leftRel_apply] at hx hy
      have e : x₂ = x₁ * (x₁⁻¹ * x₂) := by group
      have e' : y₂ = y₁ * (y₁⁻¹ * y₂) := by group
      rw [e, e', hinv _ _ hx, hsymm x₁, hinv' _ _ hy, hsymm])
  have hBq : ∀ x y : P, Bq (x : P ⧸ S) (y : P ⧸ S) = B x y := fun x y => rfl
  have hBq_l : ∀ a b c : P ⧸ S, Bq (a * b) c = Bq a c + Bq b c := by
    intro a b c
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    induction c using QuotientGroup.induction_on
    rename_i x y w
    rw [← QuotientGroup.mk_mul, hBq, hBq, hBq, hl]
  have hBq_r : ∀ a b c : P ⧸ S, Bq a (b * c) = Bq a b + Bq a c := by
    intro a b c
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    induction c using QuotientGroup.induction_on
    rename_i x y w
    rw [← QuotientGroup.mk_mul, hBq, hBq, hBq, hr]
  have hBq_zero : ∀ b : P ⧸ S, Bq 1 b = 0 := by
    intro b
    have h := hBq_l 1 1 b
    rw [mul_one] at h
    have h2 : Bq 1 b + Bq 1 b = Bq 1 b + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h2
  have hBq_zero' : ∀ a : P ⧸ S, Bq a 1 = 0 := by
    intro a
    have h := hBq_r a 1 1
    rw [mul_one] at h
    have h2 : Bq a 1 + Bq a 1 = Bq a 1 + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h2
  have hBq_alt : ∀ a : P ⧸ S, Bq a a = 0 := by
    intro a
    induction a using QuotientGroup.induction_on
    rename_i x
    rw [hBq, halt]
  have hBq_symm : ∀ a b : P ⧸ S, Bq a b = Bq b a := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rename_i x y
    rw [hBq, hBq, hsymm]
  let β : LinearMap.BilinForm (ZMod 2) (Additive (P ⧸ S)) :=
    LinearMap.mk₂ (ZMod 2) (fun a b => Bq (Additive.toMul a) (Additive.toMul b))
      (fun m₁ m₂ n => hBq_l _ _ _)
      (fun c m n => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · rw [zero_smul, zero_smul]
          exact hBq_zero _
        · rw [one_smul, one_smul])
      (fun m n₁ n₂ => hBq_r _ _ _)
      (fun c m n => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · rw [zero_smul, zero_smul]
          exact hBq_zero' _
        · rw [one_smul, one_smul])
  have hβ : ∀ a b : Additive (P ⧸ S), β a b = Bq (Additive.toMul a) (Additive.toMul b) :=
    fun a b => by simp [β, LinearMap.mk₂_apply]
  have hβalt : β.IsAlt := fun a => by rw [hβ]; exact hBq_alt _
  have hβleft : ∀ a : Additive (P ⧸ S), (∀ b, β a b = 0) → a = 0 := by
    intro a ha
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
    have hxS : x ∈ S := hnd x (fun y => by
      have := ha (Additive.ofMul (y : P ⧸ S))
      rw [hβ] at this
      rw [← hBq, hx]
      exact this)
    have : Additive.toMul a = 1 := by rw [← hx, QuotientGroup.eq_one_iff]; exact hxS
    exact this
  have hβnd : β.Nondegenerate := ⟨hβleft, fun b hb => hβleft b (fun a => by
    have h := hb a
    rw [hβ] at h ⊢
    rw [hBq_symm]
    exact h)⟩
  haveI : Module.Finite (ZMod 2) (Additive (P ⧸ S)) := Module.Finite.of_finite
  obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank hβalt hβnd
  refine ⟨m, ?_⟩
  have h1 : Nat.card (Additive (P ⧸ S)) = 2 ^ Module.finrank (ZMod 2) (Additive (P ⧸ S)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h2 : Nat.card (Additive (P ⧸ S)) = Nat.card (P ⧸ S) :=
    Nat.card_congr Additive.toMul
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup S, mul_comm, ← h2, h1, hm, ← two_mul]

end Pairing

section Config

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

open Classical in
noncomputable def cmBit (x y : G) : ZMod 2 := if x * y = y * x then 0 else 1

theorem cmBit_comm (x y : G) : cmBit x y = cmBit y x := by
  by_cases h : x * y = y * x
  · rw [cmBit, cmBit, if_pos h, if_pos h.symm]
  · have h' : ¬ y * x = x * y := fun h'' => h h''.symm
    rw [cmBit, cmBit, if_neg h, if_neg h']

theorem cmBit_eq_zero_iff (x y : G) : cmBit x y = 0 ↔ x * y = y * x := by
  by_cases h : x * y = y * x
  · rw [cmBit, if_pos h]
    exact iff_of_true rfl h
  · rw [cmBit, if_neg h]
    exact iff_of_false (by decide) h

theorem cmBit_eq_zero_of_comm {x y : G} (h : ⁅x, y⁆ = 1) : cmBit x y = 0 :=
  (cmBit_eq_zero_iff x y).2 (commutatorElement_eq_one_iff_mul_comm.1 h)

theorem cmBit_eq_one_of_comm_ne {x y : G} (h : ⁅x, y⁆ ≠ 1) : cmBit x y = 1 := by
  rw [cmBit, if_neg (fun h' => h (commutatorElement_eq_one_iff_mul_comm.2 h'))]

theorem cmBit_mul_right (hC : Config z n) {x y y' : G} (hx : x ∈ coreAt z) (hy : y ∈ coreAt z)
    (hy' : y' ∈ coreAt z) : cmBit x (y * y') = cmBit x y + cmBit x y' := by
  have key := hC.commutator_mul hx hy hy'
  have hz1 : z ≠ 1 := fun h => by simpa [h] using hC.orderOf_eq
  have hzz : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hC.orderOf_eq, sq] at h
  rcases hC.comm_eq x hx y hy with h1 | h1 <;> rcases hC.comm_eq x hx y' hy' with h2 | h2
  · rw [cmBit_eq_zero_of_comm (by rw [key, h1, h2, one_mul]), cmBit_eq_zero_of_comm h1,
      cmBit_eq_zero_of_comm h2, add_zero]
  · rw [cmBit_eq_one_of_comm_ne (by rw [key, h1, h2, one_mul]; exact hz1),
      cmBit_eq_zero_of_comm h1, cmBit_eq_one_of_comm_ne (by rw [h2]; exact hz1), zero_add]
  · rw [cmBit_eq_one_of_comm_ne (by rw [key, h1, h2, mul_one]; exact hz1),
      cmBit_eq_one_of_comm_ne (by rw [h1]; exact hz1), cmBit_eq_zero_of_comm h2, add_zero]
  · rw [cmBit_eq_zero_of_comm (by rw [key, h1, h2]; exact hzz),
      cmBit_eq_one_of_comm_ne (by rw [h1]; exact hz1),
      cmBit_eq_one_of_comm_ne (by rw [h2]; exact hz1)]
    decide

theorem cmBit_mul_left (hC : Config z n) {x x' y : G} (hx : x ∈ coreAt z) (hx' : x' ∈ coreAt z)
    (hy : y ∈ coreAt z) : cmBit (x * x') y = cmBit x y + cmBit x' y := by
  rw [cmBit_comm, cmBit_mul_right hC hy hx hx', cmBit_comm y x, cmBit_comm y x']

private theorem conj_mul_self_eq_one' (hC : Config z n) (g : G) :
    (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hC.orderOf_eq, sq] at h
  calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
    _ = 1 := by rw [hz2]; group

theorem cmBit_psi_mul (hC : Config z n) {g : G} (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    {x y y' : G} (hx : x ∈ coreAt z) (hy : y ∈ coreAt z) (hy' : y' ∈ coreAt z) :
    cmBit x (psi (g⁻¹ * z * g) (y * y')) =
      cmBit x (psi (g⁻¹ * z * g) y) + cmBit x (psi (g⁻¹ * z * g) y') := by
  have hz₁ := conj_mul_self_eq_one' hC g
  have hψy := psi_mem_core hC hz₁ hH hy
  have hψy' := psi_mem_core hC hz₁ hH hy'
  have hxz : cmBit x z = 0 :=
    (cmBit_eq_zero_iff x z).2
      (Subgroup.mem_centralizer_singleton_iff.mp (hC.core_le_centralizer hx))
  rw [CaseB.psi_mul hz₁ y y']
  rcases CaseB.conj_psi hC hH hy hy' with h | h
  · rw [h, cmBit_mul_right hC hx hψy hψy']
  · rw [h, cmBit_mul_right hC hx hψy (mul_mem hψy' hC.mem_core),
      cmBit_mul_right hC hx hψy' hC.mem_core, hxz, add_zero]

theorem commute_psi_self_aux {z₁ x : G} (hz₁ : z₁ * z₁ = 1) (hxx : x * x * z₁ = z₁ * (x * x))
    (hcomm : psi z₁ x * z₁ = z₁ * psi z₁ x) : x * psi z₁ x = psi z₁ x * x := by
  have h1 : z₁ * (x * z₁ * x⁻¹) * z₁ = x * z₁ * x⁻¹ := by
    calc z₁ * (x * z₁ * x⁻¹) * z₁ = z₁ * (z₁ * (x * z₁ * x⁻¹)) := hcomm
      _ = (z₁ * z₁) * (x * z₁ * x⁻¹) := (mul_assoc _ _ _).symm
      _ = x * z₁ * x⁻¹ := by rw [hz₁, one_mul]
  have hu : z₁ * (x * z₁ * x⁻¹) = (x * z₁ * x⁻¹) * z₁ := by
    calc z₁ * (x * z₁ * x⁻¹) = z₁ * (x * z₁ * x⁻¹) * (z₁ * z₁) := by rw [hz₁, mul_one]
      _ = (z₁ * (x * z₁ * x⁻¹) * z₁) * z₁ := by rw [mul_assoc _ z₁ z₁]
      _ = (x * z₁ * x⁻¹) * z₁ := by rw [h1]
  have hxu : x * (x * z₁ * x⁻¹) * x⁻¹ = z₁ := by
    calc x * (x * z₁ * x⁻¹) * x⁻¹ = (x * x) * z₁ * (x * x)⁻¹ := by group
      _ = z₁ := mul_inv_eq_iff_eq_mul.mpr hxx
  have hconj : x * psi z₁ x * x⁻¹ = psi z₁ x := by
    calc x * psi z₁ x * x⁻¹ = (x * z₁ * x⁻¹) * (x * (x * z₁ * x⁻¹) * x⁻¹) := by
          unfold psi; group
      _ = (x * z₁ * x⁻¹) * z₁ := by rw [hxu]
      _ = z₁ * (x * z₁ * x⁻¹) := hu.symm
      _ = psi z₁ x := rfl
  exact mul_inv_eq_iff_eq_mul.mp hconj

theorem cmBit_psi_self (hC : Config z n) {g : G} (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hall : ∀ q ∈ coreAt z,
      psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {x : G} (hx : x ∈ coreAt z) : cmBit x (psi (g⁻¹ * z * g) x) = 0 := by
  have hz₁ := conj_mul_self_eq_one' hC g
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hall x hx)).2
  have hxx : x * x * (g⁻¹ * z * g) = (g⁻¹ * z * g) * (x * x) := by
    rcases hC.sq_eq x hx with h | h
    · rw [← sq, h, one_mul, mul_one]
    · rw [← sq, h]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hH).symm
  exact (cmBit_eq_zero_iff _ _).2 (commute_psi_self_aux hz₁ hxx hcomm)

theorem CaseB.exists_psi_eq (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {r : G} (hr : r ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) :
    ∃ q ∈ coreAt z, psi (g⁻¹ * z * g) q = r := by
  have hcard := CaseB.ncard_range_psi hC (g⁻¹ * z * g)
  rw [CaseB.card hC hH hK, hC.card_core] at hcard
  have hS : ((fun q => psi (g⁻¹ * z * g) q) '' (coreAt z : Set G)).ncard = 2 ^ (n + 1) := by
    have h2 : (2 : ℕ) ^ (2 * n + 2) = 2 ^ (n + 1) * 2 ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h2] at hcard
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hcard
  have hRc : ((((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) : Subgroup G) : Set G)).ncard
      = 2 ^ (n + 1) := by
    rw [← Nat.card_coe_set_eq]
    exact CaseB.card hC hH hK
  have hsub : (fun q => psi (g⁻¹ * z * g) q) '' (coreAt z : Set G) ⊆
      ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    exact hall q hq
  have heq := Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hRc, hS])) (Set.toFinite _)
  have hmem : r ∈ (fun q => psi (g⁻¹ * z * g) q) '' (coreAt z : Set G) := by
    rw [heq]
    exact hr
  obtain ⟨q, hq, hqr⟩ := hmem
  exact ⟨q, hq, hqr⟩

theorem cmBit_psi_of_mem_sup (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {s y : G} (hs : s ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z)
    (hy : y ∈ coreAt z) : cmBit s (psi (g⁻¹ * z * g) y) = 0 := by
  rw [cmBit_eq_zero_iff]
  have hz₁ := conj_mul_self_eq_one' hC g
  have hψQ := psi_mem_core hC hz₁ hH hy
  have hψR := hall y hy
  have hle : (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z ≤
      centralizer ({psi (g⁻¹ * z * g) y} : Set G) := by
    refine sup_le ?_ ?_
    · intro r hr
      obtain ⟨hcomm, -⟩ := CaseB.isElemAbelian hC hH hK
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hcomm.is_comm.comm ⟨r, hr⟩ ⟨_, hψR⟩))
    · intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp (hC.core_le_centralizer_center hψQ) c hc)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hs)

theorem mem_sup_of_cmBit_psi (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G))
    {x : G} (hx : x ∈ coreAt z)
    (h : ∀ y ∈ coreAt z, cmBit x (psi (g⁻¹ * z * g) y) = 0) :
    x ∈ (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z := by
  refine CaseB.mem_sup_of_commute hC hH hK hx (fun r hr => ?_)
  obtain ⟨y, hy, rfl⟩ := CaseB.exists_psi_eq hC hH hK hall hr
  exact (cmBit_eq_zero_iff _ _).1 (h y hy)

theorem normal_subgroupOf_sup_center (hC : Config z n) {g : G} :
    ((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G) ⊔ centerAt z).subgroupOf
      (coreAt z)).Normal := by
  refine ⟨fun s hs q => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hs ⊢
  have hsQ : (s : G) ∈ coreAt z := s.2
  have hqQ : (q : G) ∈ coreAt z := q.2
  have e : ((q * s * q⁻¹ : ↥(coreAt z)) : G) = ⁅(q : G), (s : G)⁆ * (s : G) := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  refine mul_mem ?_ hs
  rcases hC.comm_eq (q : G) hqQ (s : G) hsQ with h | h
  · rw [h]
    exact one_mem _
  · rw [h]
    exact Subgroup.mem_sup_right hC.mem_center

theorem CaseB.even_of_forall_mem (hC : Config z n) {g : G}
    (hH : g⁻¹ * z * g ∈ centralizer ({z} : Set G))
    (hK : g⁻¹ * z * g ∉ centralizer (centerAt z : Set G))
    (hall : ∀ q ∈ coreAt z, psi (g⁻¹ * z * g) q ∈ coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) :
    Even n := by
  haveI := normal_subgroupOf_sup_center (hC := hC) (g := g)
  have hTQ : (coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z ≤ coreAt z :=
    sup_le inf_le_left hC.center_le_core
  obtain ⟨m, hm⟩ := exists_card_eq_mul_two_pow_two_mul
    (((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z).subgroupOf (coreAt z))
    (fun a b => cmBit (a : G) (psi (g⁻¹ * z * g) (b : G)))
    (fun a b => by
      rw [Subgroup.mem_subgroupOf]
      have e : ((((a * b)⁻¹ * (b * a) : ↥(coreAt z))) : G) = ⁅((b : G))⁻¹, ((a : G))⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      rcases hC.comm_eq _ (inv_mem b.2) _ (inv_mem a.2) with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_sup_right hC.mem_center)
    (fun a => by
      rw [Subgroup.mem_subgroupOf]
      have e : ((a * a : ↥(coreAt z)) : G) = (a : G) ^ 2 := by
        simp only [Subgroup.coe_mul, sq]
      rw [e]
      rcases hC.sq_eq _ a.2 with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_sup_right hC.mem_center)
    (fun a b c => cmBit_mul_left hC a.2 b.2 (psi_mem_core hC (conj_mul_self_eq_one' hC g) hH c.2))
    (fun a b c => cmBit_psi_mul hC hH a.2 b.2 c.2)
    (fun a => cmBit_psi_self hC hH hall a.2)
    (fun a s hs b => by
      rw [Subgroup.mem_subgroupOf] at hs
      show cmBit ((a : G) * (s : G)) _ = _
      rw [cmBit_mul_left hC a.2 s.2 (psi_mem_core hC (conj_mul_self_eq_one' hC g) hH b.2),
        cmBit_psi_of_mem_sup hC hH hK hall hs b.2, add_zero])
    (fun a ha => by
      rw [Subgroup.mem_subgroupOf]
      exact mem_sup_of_cmBit_psi hC hH hK hall a.2 (fun y hy => ha ⟨y, hy⟩))
  have h1 : Nat.card ↥(coreAt z) = 2 ^ (2 * n + 2) := hC.card_core
  have h2 : Nat.card ↥(((coreAt z ⊓ centralizer ({g⁻¹ * z * g} : Set G)) ⊔ centerAt z).subgroupOf
      (coreAt z)) = 2 ^ (n + 2) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv, CaseB.card_sup hC hH hK,
      CaseB.card hC hH hK]
    ring
  rw [h1, h2, ← pow_add] at hm
  have := Nat.pow_right_injective (le_refl 2) hm
  exact ⟨m, by omega⟩

end Config

end CFSG.GF2Type.CenterFour
