module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic

import CFSG.Mathlib.GroupTheory.PermCenter
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped CharTwo

open Equiv Equiv.Perm

namespace A10TwoFourSFive

abbrev Pt : Type := Fin 5 ⊕ Fin 5

@[expose] def blk : Pt → Fin 5 := Sum.elim id id

@[simp] theorem blk_inl (i : Fin 5) : blk (Sum.inl i) = i := by simp [blk]
@[simp] theorem blk_inr (i : Fin 5) : blk (Sum.inr i) = i := by simp [blk]

@[expose] def Full : Subgroup (Perm Pt) where
  carrier := {σ | ∃ τ : Perm (Fin 5), ∀ p, blk (σ p) = τ (blk p)}
  one_mem' := ⟨1, by intro p; simp⟩
  mul_mem' := by
    rintro σ τ ⟨π, hπ⟩ ⟨ρ, hρ⟩
    refine ⟨π * ρ, fun p => ?_⟩
    simp only [Perm.mul_apply]
    rw [hπ, hρ]
  inv_mem' := by
    rintro σ ⟨π, hπ⟩
    refine ⟨π⁻¹, fun p => ?_⟩
    have h := hπ (σ⁻¹ p)
    have h1 : blk p = π (blk (σ⁻¹ p)) := by simpa using h
    have h2 := congrArg (fun x => π⁻¹ x) h1
    simpa using h2.symm

theorem Full.block_eq {σ : Full} {p q : Pt} (h : blk p = blk q) :
    blk (σ.val p) = blk (σ.val q) := by
  obtain ⟨π, hπ⟩ := σ.2
  rw [hπ p, hπ q, h]

@[expose] noncomputable def blockPermFull (σ : Full) : Perm (Fin 5) :=
  Equiv.ofBijective (fun i => blk (σ.val (Sum.inl i))) (by
    obtain ⟨π, hπ⟩ := σ.2
    have hf : ∀ i, blk (σ.val (Sum.inl i)) = π i := by
      intro i
      simpa using hπ (Sum.inl i)
    refine ⟨?_, ?_⟩
    · intro i j hij
      exact π.injective (by simpa only [hf] using hij)
    · intro j
      refine ⟨π.symm j, ?_⟩
      change blk (σ.val (Sum.inl (π.symm j))) = j
      rw [hf]
      simp)

@[simp] theorem blockPermFull_apply (σ : Full) (i : Fin 5) :
    blockPermFull σ i = blk (σ.val (Sum.inl i)) := rfl

@[expose] noncomputable def blockHomFull : Full →* Perm (Fin 5) where
  toFun := blockPermFull
  map_one' := by
    ext i
    simp [blockPermFull_apply]
  map_mul' := by
    intro σ τ
    ext i
    simp only [blockPermFull_apply]
    rw [show ((σ * τ : Full) : Perm Pt) = (σ : Perm Pt) * (τ : Perm Pt) from rfl,
      Perm.mul_apply, Perm.mul_apply]
    have hτ : blk ((τ : Perm Pt) (Sum.inl i)) =
        blk (Sum.inl (blockPermFull τ i)) := by
      rw [blockPermFull_apply]
      simp
    rw [Full.block_eq (σ := σ) hτ]
    simp only [blockPermFull_apply]

@[expose] def Base : Subgroup (Perm Pt) := Full ⊓ alternatingGroup Pt

theorem base_le_full : Base ≤ Full := inf_le_left

@[expose] noncomputable def blockHomBase : Base →* Perm (Fin 5) :=
  blockHomFull.comp (Subgroup.inclusion base_le_full)

theorem blockHomBase_surjective : Function.Surjective blockHomBase := by
  intro π
  let d : Perm Pt := Equiv.sumCongr π π
  have hdFull : d ∈ Full := ⟨π, by rintro (i | i) <;> rfl⟩
  have hsign : Equiv.Perm.sign d = 1 := by
    rw [show d = Equiv.sumCongr π π from rfl, Equiv.Perm.sign_sumCongr]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  have hdA : d ∈ alternatingGroup Pt := by
    rwa [Equiv.Perm.mem_alternatingGroup]
  refine ⟨⟨d, hdFull, hdA⟩, ?_⟩
  ext i
  simp [blockHomBase, blockHomFull, blockPermFull_apply, d, blk]

@[expose] def Fiber : Subgroup (Perm Pt) where
  carrier := {σ | ∀ p, blk (σ p) = blk p}
  one_mem' := by intro p; simp
  mul_mem' := by
    intro σ τ hσ hτ p
    rw [Perm.mul_apply, hσ, hτ]
  inv_mem' := by
    intro σ hσ p
    have h := hσ (σ⁻¹ p)
    simpa using h.symm

theorem fiber_le_full : Fiber ≤ Full := by
  intro σ hσ
  exact ⟨1, fun p => by simp [hσ p]⟩

theorem fiber_inl_cases {σ : Perm Pt} (hσ : σ ∈ Fiber) (i : Fin 5) :
    σ (Sum.inl i) = Sum.inl i ∨ σ (Sum.inl i) = Sum.inr i := by
  have h := hσ (Sum.inl i)
  rcases h' : σ (Sum.inl i) with j | j
  · left
    rw [h'] at h
    simpa using h
  · right
    rw [h'] at h
    simpa using h

theorem fiber_inr_cases {σ : Perm Pt} (hσ : σ ∈ Fiber) (i : Fin 5) :
    σ (Sum.inr i) = Sum.inr i ∨ σ (Sum.inr i) = Sum.inl i := by
  have h := hσ (Sum.inr i)
  rcases h' : σ (Sum.inr i) with j | j
  · right
    rw [h'] at h
    simpa using h
  · left
    rw [h'] at h
    simpa using h

theorem fiber_inr_eq_of_inl_eq {σ : Perm Pt} (hσ : σ ∈ Fiber) {i : Fin 5}
    (h : σ (Sum.inl i) = Sum.inl i) : σ (Sum.inr i) = Sum.inr i := by
  rcases fiber_inr_cases hσ i with h2 | h2
  · exact h2
  · exfalso
    have : (Sum.inr i : Pt) = Sum.inl i := σ.injective (by rw [h2, h])
    exact Sum.inr_ne_inl this

theorem fiber_inr_eq_of_inl_eq' {σ : Perm Pt} (hσ : σ ∈ Fiber) {i : Fin 5}
    (h : σ (Sum.inl i) = Sum.inr i) : σ (Sum.inr i) = Sum.inl i := by
  rcases fiber_inr_cases hσ i with h2 | h2
  · exfalso
    have : (Sum.inr i : Pt) = Sum.inl i := σ.injective (by rw [h2, h])
    exact Sum.inr_ne_inl this
  · exact h2

@[expose] noncomputable def bitPerm (v : Fin 5 → ZMod 2) : Perm Pt where
  toFun p := match p with
    | Sum.inl i => if v i = 0 then Sum.inl i else Sum.inr i
    | Sum.inr i => if v i = 0 then Sum.inr i else Sum.inl i
  invFun p := match p with
    | Sum.inl i => if v i = 0 then Sum.inl i else Sum.inr i
    | Sum.inr i => if v i = 0 then Sum.inr i else Sum.inl i
  left_inv := by
    rintro (i | i) <;> by_cases h : v i = 0 <;> simp [h]
  right_inv := by
    rintro (i | i) <;> by_cases h : v i = 0 <;> simp [h]

theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem bitPerm_mem_fiber (v : Fin 5 → ZMod 2) : bitPerm v ∈ Fiber := by
  rintro (i | i) <;> by_cases h : v i = 0 <;> simp [bitPerm, h]

@[expose] noncomputable def bitPermHom : Multiplicative (Fin 5 → ZMod 2) →* Perm Pt where
  toFun v := bitPerm (Multiplicative.toAdd v)
  map_one' := by
    ext p
    rcases p with i | i <;> simp [bitPerm]
  map_mul' := by
    intro v w
    ext p
    rcases p with i | i
    · rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd v) i) with hv | hv <;>
      rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd w) i) with hw | hw <;>
      simp [bitPerm, Pi.add_apply, hv, hw]
    · rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd v) i) with hv | hv <;>
      rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd w) i) with hw | hw <;>
      simp [bitPerm, Pi.add_apply, hv, hw]

theorem bitPermHom_injective : Function.Injective bitPermHom := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hv : (Multiplicative.toAdd v) i = 0
  · by_cases hw : (Multiplicative.toAdd w) i = 0
    · simp [hv, hw]
    · exfalso
      have hpoint : (bitPermHom v) (Sum.inl i) = (bitPermHom w) (Sum.inl i) :=
        congrArg (fun f : Perm Pt => f (Sum.inl i)) h
      simp [bitPermHom, bitPerm, hv, hw] at hpoint
  · by_cases hw : (Multiplicative.toAdd w) i = 0
    · exfalso
      have hpoint : (bitPermHom v) (Sum.inl i) = (bitPermHom w) (Sum.inl i) :=
        congrArg (fun f : Perm Pt => f (Sum.inl i)) h
      simp [bitPermHom, bitPerm, hv, hw] at hpoint
    · have hv1 : (Multiplicative.toAdd v) i = 1 := by
        rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd v) i) with h0 | h1
        · exact absurd h0 hv
        · exact h1
      have hw1 : (Multiplicative.toAdd w) i = 1 := by
        rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd w) i) with h0 | h1
        · exact absurd h0 hw
        · exact h1
      rw [hv1, hw1]

@[expose] noncomputable def bits (σ : Fiber) : Multiplicative (Fin 5 → ZMod 2) :=
  Multiplicative.ofAdd
    (fun i => if (σ : Perm Pt) (Sum.inl i) = Sum.inl i then 0 else 1)

theorem bitPermHom_bits (σ : Fiber) : bitPermHom (bits σ) = (σ : Perm Pt) := by
  ext p
  rcases p with i | i
  · by_cases h : (σ : Perm Pt) (Sum.inl i) = Sum.inl i
    · simp [bitPermHom, bitPerm, bits, h]
    · have h' : (σ : Perm Pt) (Sum.inl i) = Sum.inr i :=
        (fiber_inl_cases σ.2 i).resolve_left h
      simp [bitPermHom, bitPerm, bits, h']
  · by_cases h : (σ : Perm Pt) (Sum.inl i) = Sum.inl i
    · have h2 : (σ : Perm Pt) (Sum.inr i) = Sum.inr i := fiber_inr_eq_of_inl_eq σ.2 h
      simp [bitPermHom, bitPerm, bits, h, h2]
    · have h' : (σ : Perm Pt) (Sum.inl i) = Sum.inr i :=
        (fiber_inl_cases σ.2 i).resolve_left h
      have h2 : (σ : Perm Pt) (Sum.inr i) = Sum.inl i := fiber_inr_eq_of_inl_eq' σ.2 h'
      simp [bitPermHom, bitPerm, bits, h, h2]

theorem bits_bitPerm (v : Multiplicative (Fin 5 → ZMod 2)) :
    bits ⟨bitPermHom v, bitPerm_mem_fiber (Multiplicative.toAdd v)⟩ = v := by
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hv : (Multiplicative.toAdd v) i = 0
  · simp [bits, bitPermHom, bitPerm, hv]
  · have hv1 : (Multiplicative.toAdd v) i = 1 := by
      rcases zmod_two_eq_zero_or_one ((Multiplicative.toAdd v) i) with h0 | h1
      · exact absurd h0 hv
      · exact h1
    simp [bits, bitPermHom, bitPerm, hv1]

@[expose] noncomputable def fiberEquiv : Fiber ≃ Multiplicative (Fin 5 → ZMod 2) where
  toFun := bits
  invFun v := ⟨bitPermHom v, by
    change bitPerm (Multiplicative.toAdd v) ∈ Fiber
    exact bitPerm_mem_fiber _⟩
  left_inv σ := Subtype.ext (bitPermHom_bits σ)
  right_inv v := bits_bitPerm v

theorem mul_apply_bitPermHom (v w : Multiplicative (Fin 5 → ZMod 2)) :
    bitPermHom (v * w) = bitPermHom v * bitPermHom w :=
  map_mul bitPermHom v w

@[expose] noncomputable def fiberMulEquiv : Fiber ≃* Multiplicative (Fin 5 → ZMod 2) where
  toEquiv := fiberEquiv
  map_mul' := by
    intro σ τ
    apply bitPermHom_injective
    calc
      bitPermHom (bits (σ * τ)) = ((σ * τ : Fiber) : Perm Pt) := bitPermHom_bits (σ * τ)
      _ = (σ : Perm Pt) * (τ : Perm Pt) := rfl
      _ = bitPermHom (bits σ) * bitPermHom (bits τ) := by rw [bitPermHom_bits σ, bitPermHom_bits τ]
      _ = bitPermHom (bits σ * bits τ) := (mul_apply_bitPermHom (bits σ) (bits τ)).symm

instance instElemAbelianBits : CFSG.IsElementaryAbelian 2 (Multiplicative (Fin 5 → ZMod 2)) where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    have h : x * x = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd x i) with h0 | h1
      · simp [h0]
      · simp [h1]
    simpa [pow_two] using h

instance fiber_isElementaryAbelian : CFSG.IsElementaryAbelian 2 Fiber :=
  CFSG.IsElementaryAbelian.of_mulEquiv fiberMulEquiv.symm instElemAbelianBits

theorem fiber_isElemAbelian : CFSG.Open.IsElemAbelian 2 Fiber :=
  CFSG.Open.isElemAbelian_of_isElementaryAbelian

theorem card_fiber : Nat.card Fiber = 32 := by
  rw [Nat.card_congr fiberMulEquiv.toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := Fin 5 → ZMod 2)), Nat.card_pi]
  simp [ZMod.card]

@[expose] noncomputable def K : Subgroup Base := blockHomBase.ker

instance K_normal : K.Normal := by
  rw [K]
  exact MonoidHom.normal_ker blockHomBase

theorem K_eq_fiberSub : K = Fiber.subgroupOf Base := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    intro p
    have h : blockPermFull (Subgroup.inclusion base_le_full x) = 1 := by
      simpa [K, blockHomBase, blockHomFull] using hx
    have hblock : blk ((x : Perm Pt) (Sum.inl (blk p))) = blk p := by
      have := congrArg (fun f : Perm (Fin 5) => f (blk p)) h
      simpa [blockPermFull_apply] using this
    exact Full.block_eq (σ := Subgroup.inclusion base_le_full x) (by rw [blk_inl]) |>.trans hblock
  · intro hx
    rw [K, MonoidHom.mem_ker]
    ext i
    have h := Subgroup.mem_subgroupOf.mp hx (Sum.inl i)
    have h' : blockPermFull (Subgroup.inclusion base_le_full x) i = i := by
      rw [blockPermFull_apply]
      simpa [blk] using h
    exact congrArg (fun y : Fin 5 => (y : ℕ)) h'

theorem card_K : Nat.card K = 16 := by
  let s : Fiber →* ℤˣ := Equiv.Perm.sign.comp Fiber.subtype
  let Fe : Subgroup Fiber := s.ker
  have hs : Function.Surjective s := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one s⟩
    · let v : Fin 5 → ZMod 2 := fun i => if i = 0 then 1 else 0
      refine ⟨⟨bitPerm v, bitPerm_mem_fiber v⟩, ?_⟩
      have hbit : bitPerm v = Equiv.swap (Sum.inl 0) (Sum.inr 0) := by
        ext p
        rcases p with i | i
        · by_cases hi : i = 0
          · subst hi; simp [bitPerm, v]
          · simp [bitPerm, v, hi, Equiv.swap_apply_of_ne_of_ne, Sum.inl_ne_inr]
        · by_cases hi : i = 0
          · subst hi; simp [bitPerm, v]
          · simp [bitPerm, v, hi, Equiv.swap_apply_of_ne_of_ne]
      change Equiv.Perm.sign (bitPerm v) = -1
      rw [hbit, Equiv.Perm.sign_swap (by simp : (Sum.inl (0 : Fin 5)) ≠ (Sum.inr (0 : Fin 5)))]
  have hrange : s.range = ⊤ := MonoidHom.range_eq_top.mpr hs
  have hidx : Fe.index = 2 := by
    change s.ker.index = 2
    rw [Subgroup.index_ker, hrange, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hmul : Fe.index * Nat.card Fe = Nat.card Fiber := Subgroup.index_mul_card (H := Fe)
  rw [hidx, card_fiber] at hmul
  have hFe : Nat.card Fe = 16 := by omega
  have hmap : Fe.map Fiber.subtype = Fiber ⊓ Base := by
    rw [Base, ← inf_assoc, inf_eq_left.mpr fiber_le_full]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact Equiv.Perm.mem_alternatingGroup.mpr (by
        have hy' : s y = 1 := hy
        simpa [s] using hy')
    · rintro ⟨hxF, hxA⟩
      refine ⟨⟨x, hxF⟩, ?_, rfl⟩
      change s ⟨x, hxF⟩ = 1
      simpa [s] using Equiv.Perm.mem_alternatingGroup.mp hxA
  have hcardmap : Nat.card (Fe.map Fiber.subtype) = Nat.card Fe :=
    Subgroup.card_map_of_injective Fiber.subtype_injective
  rw [K_eq_fiberSub]
  have hsub : Fiber.subgroupOf Base = (Fiber ⊓ Base).subgroupOf Base := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  calc
    Nat.card ↥(Fiber.subgroupOf Base) = Nat.card ↥((Fiber ⊓ Base).subgroupOf Base) := by
      rw [hsub]
    _ = Nat.card ↥(Fiber ⊓ Base) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Fiber ⊓ Base) (K := Base) inf_le_right).toEquiv
    _ = Nat.card ↥(Fe.map Fiber.subtype) := by rw [hmap]
    _ = Nat.card Fe := hcardmap
    _ = 16 := hFe

theorem normal_two_eq_bot (N : Subgroup (Perm (Fin 5))) (hN : N.Normal) (h2 : IsPGroup 2 N) :
    N = ⊥ := by
  let A : Subgroup (Perm (Fin 5)) := alternatingGroup (Fin 5)
  have : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  have : (N.subgroupOf A).Normal := hN.subgroupOf A
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with hbot | htop
  · have hinf : N ⊓ A = ⊥ := by
      have h := Subgroup.subgroupOf_map_subtype N A
      rw [hbot, Subgroup.map_bot] at h
      exact h.symm
    have hcommN : ⁅N, (⊤ : Subgroup (Perm (Fin 5)))⁆ ≤ N :=
      Subgroup.commutator_le_left (H₁ := N) (H₂ := (⊤ : Subgroup (Perm (Fin 5))))
    have hcommA : ⁅N, (⊤ : Subgroup (Perm (Fin 5)))⁆ ≤ A := by
      calc
        ⁅N, (⊤ : Subgroup (Perm (Fin 5)))⁆ ≤ ⁅(⊤ : Subgroup (Perm (Fin 5))), ⊤⁆ :=
          Subgroup.commutator_mono le_top le_rfl
        _ = A := alternatingGroup.commutator_perm_eq (by simp)
    have hcommBot : ⁅N, (⊤ : Subgroup (Perm (Fin 5)))⁆ = ⊥ := by
      apply le_bot_iff.mp
      rw [← hinf]
      exact le_inf hcommN hcommA
    have hcen : N ≤ Subgroup.center (Perm (Fin 5)) :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mp hcommBot
    rw [CFSG.center_perm_eq_bot_of_three_le_card (α := Fin 5) (by simp)] at hcen
    exact le_bot_iff.mp hcen
  · have hAle : A ≤ N := by
      intro a ha
      have : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
    have hA2 : IsPGroup 2 A := h2.to_le hAle
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := A)).mp hA2
    have hcard : Nat.card A = 60 := by
      rw [nat_card_alternatingGroup]
      norm_num
    rw [hcard] at hn
    have hn6 : n ≤ 6 := by
      by_contra h
      have h7 : 7 ≤ n := by omega
      have hpow : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h7
      norm_num at hpow
      omega
    interval_cases n <;> norm_num at hn

theorem pCore_perm_five_eq_bot : CFSG.pCore 2 (Perm (Fin 5)) = ⊥ := by
  rw [CFSG.pCore]
  apply le_bot_iff.mp
  apply sSup_le
  intro N hN
  exact (normal_two_eq_bot N hN.1 hN.2).le

theorem pCore_eq_K : CFSG.pCore 2 ↥Base = K := by
  apply le_antisymm
  ·
    have hmapbot : (CFSG.pCore 2 ↥Base).map blockHomBase = ⊥ := by
      apply le_bot_iff.mp
      rw [← pCore_perm_five_eq_bot]
      apply le_sSup
      refine ⟨(CFSG.pCore_normal).map blockHomBase blockHomBase_surjective, ?_⟩
      exact (CFSG.pCore_isPGroup).map blockHomBase
    rw [K]
    exact (Subgroup.map_eq_bot_iff (H := CFSG.pCore 2 ↥Base) (f := blockHomBase)).mp hmapbot
  ·
    have hK2 : IsPGroup 2 (blockHomBase.ker) := by
      rw [show blockHomBase.ker = K from rfl, K_eq_fiberSub]
      have : CFSG.Open.IsElemAbelian 2 (Fiber.subgroupOf Base) :=
        fiber_isElemAbelian.subgroupOf Base
      exact CFSG.Open.IsElemAbelian.isPGroup this
    exact le_sSup ⟨inferInstance, hK2⟩

@[expose] noncomputable def P : Subgroup (Perm Pt) := Base

theorem isTwoFourSFive_P : KFactsPair.IsTwoFourSFive P := by
  have hpc : CFSG.Open.pCoreOf 2 P = K.map Base.subtype := by
    change (CFSG.pCore 2 ↥Base).map Base.subtype = K.map Base.subtype
    rw [pCore_eq_K]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpc]
    have : CFSG.Open.IsElemAbelian 2 K := by
      rw [K_eq_fiberSub]
      exact fiber_isElemAbelian.subgroupOf Base
    exact CFSG.Open.IsElemAbelian.map this Base.subtype
  · rw [hpc, Subgroup.card_map_of_injective Base.subtype_injective, card_K]
    norm_num
  · change Nonempty (↥Base ⧸ CFSG.pCore 2 ↥Base ≃* Perm (Fin 5))
    refine ⟨(QuotientGroup.quotientMulEquivOfEq pCore_eq_K).trans ?_⟩
    exact QuotientGroup.quotientKerEquivOfSurjective blockHomBase blockHomBase_surjective

end A10TwoFourSFive

open A10TwoFourSFive

end CFSG.LocalAnalysis.RankThreeUC.S15
