module

public import CFSG.GH74.GLS.C3.Prop121.Card7Facts2
public import CFSG.GH74.GLS.C3.Prop121.Card7H1
public meta import CFSG.GH74.GLS.C3.Prop121.Card7H1
public import CFSG.GH74.GLS.C3.Layer2.NumMoved
public meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public meta import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs
public meta import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs
public import Certificates.Certificate5083

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7.Syl

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Prop121.Card7.HC

theorem SL_len_true :
    decide (SL.length = 128) = true :=
  Certificates.certificate5083.1

theorem SL_nodup_true : decide SL.Nodup = true :=
  Certificates.certificate5083.2.1

theorem SL_even_true :
    (SL.all fun σ => decide (sign σ = 1)) = true :=
  Certificates.certificate5083.2.2.1

theorem SL_one_true :
    decide ((1 : P11) ∈ SL) = true :=
  Certificates.certificate5083.2.2.2.1

theorem SL_mul_true :
    (SL.all fun a => SL.all fun b => decide (a * b ∈ SL)) = true :=
  Certificates.certificate5083.2.2.2.2.1

theorem SL_inv_true :
    (SL.all fun a => decide (a⁻¹ ∈ SL)) = true :=
  Certificates.certificate5083.2.2.2.2.2.1

theorem SL_count_true :
    decide (SL.countP (fun σ => decide (σ * σ = 1 ∧ σ ≠ 1 ∧ numMoved σ = 4)) = 14) = true :=
  Certificates.certificate5083.2.2.2.2.2.2

theorem SL_len : SL.length = 128 := of_decide_eq_true SL_len_true

theorem SL_nodup : SL.Nodup := of_decide_eq_true SL_nodup_true

theorem SL_even {σ : P11} (h : σ ∈ SL) : sign σ = 1 :=
  of_decide_eq_true (List.all_eq_true.1 SL_even_true σ h)

theorem SL_one : (1 : P11) ∈ SL := of_decide_eq_true SL_one_true

theorem SL_mul
    {a b : P11} (ha : a ∈ SL) (hb : b ∈ SL) : a * b ∈ SL :=
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 SL_mul_true a ha) b hb)

theorem SL_inv {a : P11} (ha : a ∈ SL) : a⁻¹ ∈ SL :=
  of_decide_eq_true (List.all_eq_true.1 SL_inv_true a ha)

@[expose] def Sstar : Subgroup A11 where
  carrier := {g | ((g : A11) : P11) ∈ SL}
  mul_mem' := fun ha hb => SL_mul ha hb
  one_mem' := SL_one
  inv_mem' := fun ha => SL_inv ha

theorem card_Sstar : Nat.card Sstar = 128 := by
  have h := card_subtype_eq_countP (M := A11) (N := P11) (fun g => ((g : A11) : P11))
    Subtype.val_injective SL SL_nodup (fun g => ((g : A11) : P11) ∈ SL) (fun _ => true)
    (fun _ hm => hm) (fun _ _ => rfl)
    (fun n hn _ => ⟨⟨n, mem_alternatingGroup.2 (SL_even hn)⟩, rfl, hn⟩)
  rw [List.countP_true, SL_len] at h
  exact h

theorem count_Sstar :
    Nat.card {v : ↥Sstar // orderOf (v : A11) = 2 ∧ numMoved ((v : A11) : Perm (Fin 11)) = 4} = 14 := by
  have h := card_subtype_eq_countP (M := ↥Sstar) (N := P11) (fun v => (((v : A11)) : P11))
    (fun a b hab => Subtype.ext (Subtype.ext hab)) SL SL_nodup
    (fun v => orderOf (v : A11) = 2 ∧ numMoved ((v : A11) : Perm (Fin 11)) = 4)
    (fun σ => decide (σ * σ = 1 ∧ σ ≠ 1 ∧ numMoved σ = 4))
    (fun v _ => v.2)
    (by
      intro v hv
      obtain ⟨h2, h4⟩ := hv
      have hp := orderOf_eq_prime_iff.1 h2
      refine decide_eq_true ⟨?_, ?_, h4⟩
      · have := congrArg (fun a : A11 => (a : P11)) hp.1
        simpa [sq] using this
      · intro h1
        apply hp.2
        exact Subtype.ext h1)
    (by
      intro n hn hQ
      have hQ' := of_decide_eq_true hQ
      refine ⟨⟨⟨n, mem_alternatingGroup.2 (SL_even hn)⟩, hn⟩, rfl, ?_, hQ'.2.2⟩
      apply orderOf_eq_prime
      · apply Subtype.ext
        show (n * n : P11) = 1
        exact hQ'.1
      · intro h1
        exact hQ'.2.1 (congrArg (fun a : A11 => (a : P11)) h1))
  rw [h]
  exact of_decide_eq_true SL_count_true

theorem card_A11 : Nat.card A11 = 19958400 := by
  have h := card_alternatingGroup (α := Fin 11)
  rw [Nat.card_eq_fintype_card, h, Fintype.card_fin]
  decide

theorem card7SylFacts : SylFacts := by
  refine ⟨fun S' => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 Sstar := IsPGroup.of_card (n := 7) (by rw [card_Sstar]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup A11) ≤ 128 := by
    rw [Sylow.card_eq_multiplicity Q, card_A11]
    have h : (19958400 : ℕ).factorization 2 = 7 := by decide +kernel
    rw [h]
    norm_num
  have hEq : (Q : Subgroup A11) = Sstar :=
    (Subgroup.eq_of_le_of_card_ge hQ (by rw [card_Sstar]; exact hQcard)).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A11 Q S'
  have hmem : ∀ u : A11, u ∈ (S' : Subgroup A11) ↔ g⁻¹ * u * g ∈ Sstar := by
    intro u
    rw [← hEq, ← hg, Sylow.smul_def, Sylow.pointwise_smul_def,
      Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨u0, hu0, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hu0
    · intro hm
      exact ⟨g⁻¹ * u * g, hm, by simp [MulAut.conj_apply, mul_assoc]⟩
  let e1 : ↥(S' : Subgroup A11) ≃ ↥Sstar :=
    { toFun := fun u => ⟨g⁻¹ * (u : A11) * g, (hmem u).1 u.2⟩
      invFun := fun u => ⟨g * (u : A11) * g⁻¹, (hmem _).2 (by simp [mul_assoc])⟩
      left_inv := fun u => by ext; simp [mul_assoc]
      right_inv := fun u => by ext; simp [mul_assoc] }
  have hP : ∀ u : ↥(S' : Subgroup A11),
      (orderOf (u : A11) = 2 ∧ numMoved ((u : A11) : Perm (Fin 11)) = 4) ↔
      (orderOf ((e1 u : ↥Sstar) : A11) = 2 ∧
        numMoved (((e1 u : ↥Sstar) : A11) : Perm (Fin 11)) = 4) := by
    intro u
    have ho : orderOf (g⁻¹ * (u : A11) * g) = orderOf (u : A11) := by
      have : g⁻¹ * (u : A11) * g = MulAut.conj g⁻¹ (u : A11) := by simp
      rw [this, MulEquiv.orderOf_eq]
    have hn : numMoved (((g⁻¹ * (u : A11) * g : A11)) : Perm (Fin 11)) =
        numMoved ((u : A11) : Perm (Fin 11)) := by
      have := numMoved_conj ((u : A11) : Perm (Fin 11)) ((g : A11) : Perm (Fin 11))⁻¹
      simpa [mul_assoc] using this
    show _ ↔ (orderOf (g⁻¹ * (u : A11) * g) = 2 ∧
      numMoved (((g⁻¹ * (u : A11) * g : A11)) : Perm (Fin 11)) = 4)
    rw [ho, hn]
  let E1 := Equiv.subtypeEquiv (p := fun u : ↥(S' : Subgroup A11) =>
      orderOf (u : A11) = 2 ∧ numMoved ((u : A11) : Perm (Fin 11)) = 4)
    (q := fun u : ↥Sstar => orderOf (u : A11) = 2 ∧ numMoved ((u : A11) : Perm (Fin 11)) = 4) e1 hP
  rw [Nat.card_congr E1]
  exact count_Sstar

end CFSG.GH74.GLS.C3.Prop121.Card7.Syl
