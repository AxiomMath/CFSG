module

public import CFSG.Quasithin.H13.A5Setting
public import CFSG.GH74.QTGen4.U42.Coords
public meta import CFSG.Quasithin.H13.A5Setting
public meta import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.Foundations
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.Helpers
public import CFSG.LocalAnalysis.ComponentClassification.Helpers
public meta import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public meta import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.F9Basic
public meta import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public meta import CFSG.Quasithin.Background.G2A5Setting

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin.A5Model CFSG.QuasithinUnique CFSG.Quasithin.H13.A5

instance : Fintype Mc := Fintype.ofEquiv (W5 × Equiv.Perm (Fin 5)) SemidirectProduct.equivProd.symm

theorem InK4_mul : ∀ σ τ : Equiv.Perm (Fin 5), InK4 σ → InK4 τ → InK4 (σ * τ) := by
  rintro σ τ (rfl | rfl | rfl | rfl) (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem InK4_inv : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → InK4 σ⁻¹ := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem InK4_four : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → σ 4 = 4 := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem InD_mul : ∀ σ τ : Equiv.Perm (Fin 5), InD σ → InD τ → InD (σ * τ) := by
  decide +kernel

theorem InD_inv : ∀ σ : Equiv.Perm (Fin 5), InD σ → InD σ⁻¹ := by
  decide +kernel

@[expose] def U0 : Subgroup Mc where
  carrier := {x | x.left ∈ W3 ∧ InK4 x.right}
  one_mem' := ⟨W3.one_mem, Or.inl rfl⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, InK4_mul _ _ ha2 hb2⟩
    rw [SemidirectProduct.mul_left]
    refine W3.mul_mem ha1 (mem_W3.2 ?_)
    exact pact_mem_W3 _ _ (InK4_four _ ha2) (mem_W3.1 hb1)
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, InK4_inv _ ha2⟩
    rw [SemidirectProduct.inv_left]
    refine mem_W3.2 ?_
    refine pact_mem_W3 _ _ ?_ (mem_W3.1 (W3.inv_mem ha1))
    rw [Equiv.Perm.inv_eq_iff_eq, InK4_four _ ha2]

instance : DecidablePred (· ∈ W3) := fun x => decidable_of_iff (c4 x = 1) mem_W3.symm

instance : DecidablePred (· ∈ U0) := fun x =>
  inferInstanceAs (Decidable (x.left ∈ W3 ∧ InK4 x.right))

instance : Fintype U0 := Subtype.fintype _

instance : DecidableEq U0 := fun a b => decidable_of_iff ((a : Mc) = (b : Mc)) Subtype.coe_inj

theorem card_U0 : Nat.card U0 = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def zc : U0 := ⟨⟨W4, 1⟩, W4_mem_W3, Or.inl rfl⟩

theorem center_U0 : Subgroup.center U0 = Subgroup.zpowers zc := by
  letI : DecidableEq U0 := fun x y =>
    if h : (x : Mc).left = (y : Mc).left ∧ (x : Mc).right = (y : Mc).right then
      isTrue (Subtype.ext (SemidirectProduct.ext h.1 h.2))
    else
      isFalse (fun hxy => h ⟨congrArg (fun u : U0 => (u : Mc).left) hxy,
        congrArg (fun u : U0 => (u : Mc).right) hxy⟩)
  have hsq : zc ^ 2 = 1 := by decide
  have hne : zc ≠ 1 := by decide
  have hcen : ∀ x : U0, ((∀ g : U0, g * x = x * g) ↔ (x = 1 ∨ x = zc)) := by
    decide
  have hk : ∀ k : ℤ, zc ^ k = 1 ∨ zc ^ k = zc := by
    intro k
    have hord : orderOf zc = 2 := orderOf_eq_prime hsq hne
    have h := zpow_mod_orderOf zc k
    rw [hord] at h
    rw [← h]
    rcases Int.emod_two_eq_zero_or_one k with h2 | h2 <;> simp [h2]
  ext x
  rw [Subgroup.mem_center_iff, Subgroup.mem_zpowers_iff]
  constructor
  · intro hx
    rcases (hcen x).1 hx with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · rintro ⟨k, rfl⟩
    exact (hcen _).2 (hk k)

@[expose] def Wc : Subgroup Mc := (SemidirectProduct.inl : W5 →* Mc).range

@[expose] def Tc : Subgroup Mc where
  carrier := {x | InK4 x.right}
  one_mem' := Or.inl rfl
  mul_mem' := fun ha hb => InK4_mul _ _ ha hb
  inv_mem' := fun ha => InK4_inv _ ha

instance : DecidablePred (· ∈ Tc) := fun x => inferInstanceAs (Decidable (InK4 x.right))

@[expose] def Thc : Subgroup Mc where
  carrier := {x | InD x.right}
  one_mem' := by decide
  mul_mem' := fun {a b} ha hb => InD_mul _ _ ha hb
  inv_mem' := fun {a} ha => InD_inv _ ha

instance : DecidablePred (· ∈ Thc) := fun x => inferInstanceAs (Decidable (InD x.right))

@[expose] def Bc : Subgroup Mc where
  carrier := {x | x.right.sign = 1 ∧ x.right 4 = 4}
  one_mem' := ⟨Equiv.Perm.sign_one, rfl⟩
  mul_mem' := by
    intro a b ha hb
    change a.right.sign = 1 ∧ a.right 4 = 4 at ha
    change b.right.sign = 1 ∧ b.right 4 = 4 at hb
    refine ⟨?_, ?_⟩
    · change (a.right * b.right).sign = 1
      rw [Equiv.Perm.sign_mul, ha.1, hb.1, one_mul]
    · change (a.right * b.right) 4 = 4
      rw [Equiv.Perm.mul_apply, hb.2, ha.2]
  inv_mem' := by
    intro a ha
    change a.right.sign = 1 ∧ a.right 4 = 4 at ha
    refine ⟨?_, ?_⟩
    · change a.right⁻¹.sign = 1
      rw [Equiv.Perm.sign_inv, ha.1]
    · change a.right⁻¹ 4 = 4
      exact Equiv.Perm.inv_eq_iff_eq.mpr ha.2.symm

instance : DecidablePred (· ∈ Bc) := fun x =>
  inferInstanceAs (Decidable (x.right.sign = 1 ∧ x.right 4 = 4))

@[expose] def Bhc : Subgroup Mc where
  carrier := {x | x.right 4 = 4}
  one_mem' := rfl
  mul_mem' := by
    intro a b ha hb
    change a.right 4 = 4 at ha
    change b.right 4 = 4 at hb
    change (a.right * b.right) 4 = 4
    rw [Equiv.Perm.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change a.right 4 = 4 at ha
    change a.right⁻¹ 4 = 4
    exact Equiv.Perm.inv_eq_iff_eq.mpr ha.symm

instance : DecidablePred (· ∈ Bhc) := fun x => inferInstanceAs (Decidable (x.right 4 = 4))

theorem card_Tc : Nat.card Tc = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Thc : Nat.card Thc = 128 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Bc : Nat.card Bc = 192 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_Bhc : Nat.card Bhc = 384 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have e : Nat.card (alternatingGroup (Fin 5)) = Nat.card {σ : Equiv.Perm (Fin 5) // σ.sign = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun σ => Equiv.Perm.mem_alternatingGroup)
  rw [e, Nat.card_eq_fintype_card]
  decide +kernel

end CFSG.GH74.QTGen4.U42
