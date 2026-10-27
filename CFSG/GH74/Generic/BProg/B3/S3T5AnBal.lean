module

public import CFSG.GH74.Generic.BProg.B3.S3T5AnCore
public import CFSG.GH74.Generic.BProg.B3.S3T5Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

open Equiv Equiv.Perm CFSG.ClassicalInvolution.Balance

namespace S3T5An

noncomputable def autPerm {K : Type*} [Group K] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) : MulAut K ≃* Perm (Fin n) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective MulAut.conjNormal
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)).symm

theorem autPerm_conj {K : Type*} [Group K] {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (e : K ≃* alternatingGroup (Fin n)) (k : K) :
    autPerm hn5 hn6 e (MulAut.conj k) = ((e k : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  rw [autPerm, MulEquiv.trans_apply, MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply,
    MulAut.conjNormal_val]
  ext a
  simp [MulAut.congr_apply]

end S3T5An

theorem altLocBal2_proved : S3T5.AltLocBal2 := by
  intro K _ _ n hn8 hn10 ⟨e⟩
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  have hα : ¬ (4 : ℤ) ∣ (Fintype.card (Fin n) : ℤ) - 3 := by
    rw [Fintype.card_fin]
    omega
  intro H hInn F hF4 hF2
  have hF4' : 4 ≤ Nat.card F := by simpa using hF4
  set Φ := S3T5An.autPerm hn5 hn6 e with hΦ
  have : Finite (MulAut K) := Finite.of_equiv _ Φ.symm.toEquiv
  have hA : alternatingGroup (Fin n) ≤ H.map Φ.toMonoidHom := by
    intro σ hσ
    obtain ⟨k, hk⟩ := e.surjective ⟨σ, hσ⟩
    refine ⟨MulAut.conj k, hInn ⟨k, rfl⟩, ?_⟩
    show Φ (MulAut.conj k) = σ
    rw [hΦ, S3T5An.autPerm_conj, hk]
  set ψ := H.equivMapOfInjective Φ.toMonoidHom Φ.injective with hψ
  have hF'4 : 4 ≤ Nat.card (F.map ψ.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective ψ.injective]
  have hF'2 : ∀ f ∈ F.map ψ.toMonoidHom, f * f = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    rw [← map_mul, hF2 f hf, map_one]
  have hbot := S3T5An.deltaCore_eq_bot_of_alternatingGroup_le hα hA hF'4 hF'2
  have hle := map_deltaCore_le_of_surjective ψ.toMonoidHom ψ.surjective hF2
  rw [hbot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 hle

end CFSG.GH74.Generic.BProg.B3
