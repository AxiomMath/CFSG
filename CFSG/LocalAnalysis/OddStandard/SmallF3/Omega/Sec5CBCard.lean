module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSub

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5cb_perm_comm_sq {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6))) :
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1 := by
  have h0 := sec5cb_phi_zero hφ
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨v, -, rfl⟩ := (hφ.2.2.1 a).mp ha
    obtain ⟨w, -, rfl⟩ := (hφ.2.2.1 b).mp hb
    rw [← hφ.1 v w trivial trivial, ← hφ.1 w v trivial trivial, add_comm]
  · obtain ⟨v, -, rfl⟩ := (hφ.2.2.1 a).mp ha
    have hvv : v + v = 0 := by
      funext i
      show v i + v i = 0
      generalize v i = c
      revert c
      decide
    rw [← hφ.1 v v trivial trivial, hvv, h0]

theorem sec5cb_perm_card {φ : (Fin 6 → ZMod 2) → G} {E H : Subgroup G}
    (hφ : IsPermModuleVia (n := 6) (fun _ => True) φ E H (alternatingGroup (Fin 6))) :
    Nat.card E = 2 ^ 6 := by
  have hbij : Function.Bijective
      (fun v : Fin 6 → ZMod 2 => (⟨φ v, (hφ.2.2.1 _).mpr ⟨v, trivial, rfl⟩⟩ : E)) := by
    constructor
    · intro v w h
      exact hφ.2.1 v w trivial trivial (congrArg Subtype.val h)
    · intro x
      obtain ⟨v, -, hv⟩ := (hφ.2.2.1 x.1).mp x.2
      exact ⟨v, Subtype.ext hv⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp [Nat.card_eq_fintype_card]

theorem sec5cb_card_eq_two_mul {A N : Subgroup G} {t : G} (htt : t * t = 1)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hNA : N ≤ A) (htA : t ∈ A) (htN : t ∉ N)
    (hsup : A = N ⊔ zpowers t) : Nat.card A = 2 * Nat.card N := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hcov : ∀ a ∈ A, a ∈ N ∨ a * t ∈ N := by
    let K : Subgroup G :=
      { carrier := {a | a ∈ A ∧ (a ∈ N ∨ a * t ∈ N)}
        mul_mem' := by
          rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
          refine ⟨A.mul_mem haA hbA, ?_⟩
          have hbt : b * t = t * b := hcomm b hbA t htA
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (N.mul_mem ha hb)
          · exact Or.inr (by rw [mul_assoc]; exact N.mul_mem ha hb)
          · refine Or.inr ?_
            have : a * b * t = a * t * b := by rw [mul_assoc, hbt, ← mul_assoc]
            rw [this]
            exact N.mul_mem ha hb
          · refine Or.inl ?_
            have : a * b = (a * t) * (b * t) := by
              calc a * b = a * ((t * t) * b) := by rw [htt, one_mul]
                _ = (a * t) * (b * t) := by rw [hbt]; group
            rw [this]
            exact N.mul_mem ha hb
        one_mem' := ⟨A.one_mem, Or.inl N.one_mem⟩
        inv_mem' := by
          rintro a ⟨haA, ha⟩
          refine ⟨A.inv_mem haA, ?_⟩
          rcases ha with ha | ha
          · exact Or.inl (N.inv_mem ha)
          · refine Or.inr ?_
            have hinv : a⁻¹ * t = (a * t)⁻¹ := by
              rw [mul_inv_rev, htinv]
              exact (hcomm t htA a⁻¹ (A.inv_mem haA)).symm
            rw [hinv]
            exact N.inv_mem ha }
    have hle : A ≤ K := by
      rw [hsup]
      refine sup_le (fun n hn => ⟨hNA hn, Or.inl hn⟩) ?_
      rw [Subgroup.zpowers_le]
      exact ⟨htA, Or.inr (by rw [htt]; exact N.one_mem)⟩
    intro a ha
    exact (hle (hsup ▸ ha)).2
  have hidx : N.relIndex A = 2 := by
    rw [Subgroup.relIndex_eq_two_iff']
    refine ⟨t, htA, fun b hb => ?_⟩
    have hbt : t * b = b * t := hcomm t htA b hb
    by_cases hbN : b ∈ N
    · refine Or.inr ⟨hbN, fun h' => htN ?_⟩
      simpa using N.mul_mem h' (N.inv_mem hbN)
    · refine Or.inl ⟨?_, hbN⟩
      rcases hcov b hb with h | h
      · exact absurd h hbN
      · rw [hbt]
        exact h
  have hcard := Subgroup.relIndex_mul_card (H := N) (K := A)
  rw [hidx, inf_of_le_left hNA] at hcard
  exact hcard.symm

end CFSG.OddStandard.SmallF3.Omega
