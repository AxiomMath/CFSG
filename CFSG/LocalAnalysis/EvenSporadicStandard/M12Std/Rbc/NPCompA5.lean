module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Certificates.Data.A5

public section

namespace CFSG.EvenSporadicStandard.M12Std.Rbc

open Equiv Subgroup

private theorem sign_eq_one_of_card_centralizer_eq_four :
    ∀ π : Perm (Fin 5), π * π = 1 →
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * π = π * (a : Perm (Fin 5))} = 4 →
      Perm.sign π = 1 ∧ π ≠ 1 := by
  decide +kernel

private theorem card_centralizer_alt5_of_involution :
    ∀ c : alternatingGroup (Fin 5), c * c = 1 → c ≠ 1 →
      Fintype.card {a : alternatingGroup (Fin 5) // a * c = c * a} = 4 ∧
        ∀ a : alternatingGroup (Fin 5), a * c = c * a → a * a = 1 := by
  decide +kernel

theorem exists_noncommuting_centralizer_perm5 {π₀ : Perm (Fin 5)} (h2 : π₀ * π₀ = 1)
    (h1 : π₀ ≠ 1) :
    ∃ a b : Perm (Fin 5), a * π₀ = π₀ * a ∧ b * π₀ = π₀ * b ∧ a * b ≠ b * a := by
  revert h1 h2 π₀
  decide +kernel

theorem exists_inner_of_card_fixedPoints_eq_four {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) (α : H ≃* H) (hα : ∀ h, α (α h) = h)
    (hcard : Nat.card {h : H // α h = h} = 4) :
    ∃ c : H, c * c = 1 ∧ c ≠ 1 ∧ ∀ h, α h = c * h * c⁻¹ := by
  classical
  let β : alternatingGroup (Fin 5) ≃* alternatingGroup (Fin 5) := e.symm.trans (α.trans e)
  have hββ : β * β = 1 := by
    ext a
    simp [β, hα]
  have hinj :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).1
  obtain ⟨π, hπ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)).2 β
  have hππ : π * π = 1 := by
    apply hinj
    rw [map_mul, map_one, hπ]
    exact hββ
  have hcard₁ : Nat.card {h : H // α h = h} =
      Nat.card {a : alternatingGroup (Fin 5) // MulAut.conjNormal π a = a} :=
    Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun h => by
      change α h = h ↔ MulAut.conjNormal π (e h) = e h
      rw [hπ]
      constructor
      · intro hh
        simp [β, hh]
      · intro hh
        exact e.injective (by simpa [β] using hh))
  have hcard₂ : Nat.card {a : alternatingGroup (Fin 5) // MulAut.conjNormal π a = a} =
      Fintype.card {a : alternatingGroup (Fin 5) //
        (a : Perm (Fin 5)) * π = π * (a : Perm (Fin 5))} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => by
      rw [Subtype.ext_iff, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact eq_comm)
  have hcard' : Fintype.card {a : alternatingGroup (Fin 5) //
      (a : Perm (Fin 5)) * π = π * (a : Perm (Fin 5))} = 4 := by
    rw [← hcard₂, ← hcard₁]
    exact hcard
  obtain ⟨hsign, hπ1⟩ := sign_eq_one_of_card_centralizer_eq_four π hππ hcard'
  let c : H := e.symm ⟨π, Equiv.Perm.mem_alternatingGroup.2 hsign⟩
  have hc : (e c : Perm (Fin 5)) = π := by simp [c]
  refine ⟨c, ?_, ?_, ?_⟩
  · apply e.injective
    rw [map_mul, map_one]
    apply Subtype.ext
    simp [hc, hππ]
  · intro hc1
    apply hπ1
    have := congrArg (fun x : H => (e x : Perm (Fin 5))) hc1
    simpa [c] using this
  · intro h
    apply e.injective
    have hmain : e (α h) = MulAut.conjNormal π (e h) := by
      rw [hπ]
      simp [β]
    rw [hmain, map_mul, map_mul, map_inv]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp [hc]

theorem card_centralizer_of_involution_alt5 {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) {c : H} (hc : c * c = 1) (hc1 : c ≠ 1) :
    Nat.card {a : H // a * c = c * a} = 4 ∧ ∀ a : H, a * c = c * a → a * a = 1 := by
  have hec : e c * e c = 1 := by
    rw [← map_mul, hc, map_one]
  have hec1 : e c ≠ 1 := by
    intro h
    exact hc1 (e.injective (by rw [h, map_one]))
  obtain ⟨h4, hall⟩ := card_centralizer_alt5_of_involution (e c) hec hec1
  have hiff : ∀ a : H, a * c = c * a ↔ e a * e c = e c * e a := by
    intro a
    constructor
    · intro h
      rw [← map_mul, ← map_mul, h]
    · intro h
      apply e.injective
      rw [map_mul, map_mul]
      exact h
  have hcard : Nat.card {a : H // a * c = c * a} =
      Fintype.card {a : alternatingGroup (Fin 5) // a * (e c) = (e c) * a} :=
    calc Nat.card {a : H // a * c = c * a}
        = Nat.card {a : alternatingGroup (Fin 5) // a * (e c) = (e c) * a} :=
          Nat.card_congr (Equiv.subtypeEquiv e.toEquiv hiff)
      _ = Fintype.card {a : alternatingGroup (Fin 5) // a * (e c) = (e c) * a} :=
          Nat.card_eq_fintype_card
  refine ⟨?_, ?_⟩
  · rw [hcard]; exact h4
  · intro a ha
    have h := hall (e a) ((hiff a).mp ha)
    apply e.injective
    rw [map_mul, map_one]
    exact h

end CFSG.EvenSporadicStandard.M12Std.Rbc
