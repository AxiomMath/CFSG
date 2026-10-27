module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BHeartPerm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure HeartData (φ : (Fin 8 → ZMod 2) → G) (A M : Subgroup G)
    (Alt : Subgroup (Equiv.Perm (Fin 8))) : Prop where
  mem : ∀ v, IsEvenVec v → φ v ∈ A
  add : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  add_one : ∀ v, IsEvenVec v → φ (v + 1) = φ v
  inj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → w = v ∨ w = v + 1
  surj : ∀ x ∈ A, ∃ v, IsEvenVec v ∧ φ v = x
  act : ∀ h ∈ M, ∃ σ ∈ Alt, ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)
  lift : ∀ σ ∈ Alt, ∃ h ∈ M, ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)

private lemma sec5b_add_add_self (v w : Fin 8 → ZMod 2) : (v + w) + w = v := by
  funext i
  exact CharTwo.add_cancel_right (v i) (w i)

private lemma sec5b_add_eq_zero_imp {v w : Fin 8 → ZMod 2} (h : v + w = 0) : w = v := by
  funext i
  have hi : v i + w i = 0 := congrFun h i
  exact (CharTwo.add_cancel_left (v i) (w i)).symm.trans (by rw [hi, add_zero])

private lemma sec5b_add_eq_one_imp {v w : Fin 8 → ZMod 2} (h : v + w = 1) : w = v + 1 := by
  funext i
  have hi : v i + w i = 1 := congrFun h i
  show w i = v i + 1
  exact (CharTwo.add_cancel_left (v i) (w i)).symm.trans (by rw [hi])

private lemma sec5b_phi_one {φ : (Fin 8 → ZMod 2) → G}
    (hker : ∀ v, IsEvenVec v → (φ v ∈ (⊥ : Subgroup G) ↔
      v ∈ ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)))) :
    φ 1 = 1 := by
  have hN : (1 : Fin 8 → ZMod 2) ∈ ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) :=
    Set.mem_insert_iff.mpr (Or.inr rfl)
  have hb : φ 1 ∈ (⊥ : Subgroup G) := (hker 1 sec5b_isEvenVec_one).mpr hN
  exact Subgroup.mem_bot.mp hb

theorem sec5b_heartData {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))}
    (h : IsPermModuleMod (n := 8) IsEvenVec ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) φ A ⊥ M Alt) :
    HeartData φ A M Alt := by
  obtain ⟨-, -, -, -, hmem, hadd, hker, hsurj, hact, hlift⟩ := h
  refine ⟨hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w hv hw
    exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hadd v w hv hw))).symm
  · intro v hv
    have h1 : φ 1 = 1 := sec5b_phi_one hker
    calc φ (v + 1) = φ v * φ 1 :=
          (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hadd v 1 hv sec5b_isEvenVec_one))).symm
      _ = φ v * 1 := by rw [h1]
      _ = φ v := mul_one _
  · intro v w hv hw heq
    have hvw : IsEvenVec (v + w) := sec5b_isEvenVec_add hv hw
    have h2 : φ (v + w) * φ v = φ v := by
      have h3 : φ ((v + w) + w) = φ (v + w) * φ w :=
        (inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hadd (v + w) w hvw hw))).symm
      rw [sec5b_add_add_self v w, ← heq] at h3
      exact h3.symm
    have hsum : φ (v + w) = 1 := mul_right_cancel (by rw [h2, one_mul])
    have hmem' : (v + w) ∈ ({0, fun _ => 1} : Set (Fin 8 → ZMod 2)) :=
      (hker (v + w) hvw).mp (Subgroup.mem_bot.mpr hsum)
    rcases (Set.mem_insert_iff.mp hmem') with h0 | h1
    · exact Or.inl (sec5b_add_eq_zero_imp h0)
    · exact Or.inr (sec5b_add_eq_one_imp (Set.mem_singleton_iff.mp h1))
  · intro x hx
    obtain ⟨v, hv, hmem'⟩ := hsurj x hx
    exact ⟨v, hv, inv_mul_eq_one.mp (Subgroup.mem_bot.mp hmem')⟩
  · intro h hh
    obtain ⟨σ, hσ, hσφ⟩ := hact h hh
    exact ⟨σ, hσ, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hσφ v hv))⟩
  · intro σ hσ
    obtain ⟨h, hh, hhφ⟩ := hlift σ hσ
    exact ⟨h, hh, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hhφ v hv))⟩

theorem sec5b_mem_conj_iff {φ : (Fin 8 → ZMod 2) → G} {A M : Subgroup G}
    {Alt : Subgroup (Equiv.Perm (Fin 8))} (hd : HeartData φ A M Alt) {v : Fin 8 → ZMod 2}
    (hv : IsEvenVec v) {y : G} :
    y ∈ conjClassIn M (φ v) ↔ ∃ σ ∈ Alt, y = φ (permVec σ v) := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨σ, hσ, hσv⟩ := hd.act h hh
    exact ⟨σ, hσ, hσv v hv⟩
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨h, hh, hhv⟩ := hd.lift σ hσ
    exact ⟨h, hh, (hhv v hv).symm⟩

end CFSG.OddStandard.SmallF3.Omega
