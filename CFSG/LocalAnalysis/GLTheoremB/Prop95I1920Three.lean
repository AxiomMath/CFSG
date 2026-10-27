module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvFactOmega

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1920

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

@[expose] def OmegaFourComponentCentre : Prop :=
  ∀ (ε : Bool) (X : Type) [Group X] [Finite X] (K : Subgroup X), IsComponentOf K ⊤ →
    IsOmegaTwo ε 2 ↥K → Subgroup.center ↥K = ⊥

theorem center_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 := Subgroup.mem_center_iff.1 hz (e.symm w)
    calc w * e z = e (e.symm w * z) := by rw [map_mul, e.apply_symm_apply]
      _ = e (z * e.symm w) := by rw [h1]
      _ = e z * w := by rw [map_mul, e.apply_symm_apply]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (hz'.trans (map_one e).symm)

theorem center_eq_bot_of_omega (hZ1 : OmegaFourComponentCentre) {X : Type} [Group X] [Finite X]
    {K : Subgroup X} (hK : IsComponentOf K ⊤) {n : ℕ} (hn : 1 ≤ n) (ε : Bool)
    (hΩ : IsOmegaTwo ε (n + 1) ↥K) : Subgroup.center ↥K = ⊥ := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact hZ1 ε X K hK hΩ
  · have hc := omegaCentreTrivial_holds n h
    cases ε
    · obtain ⟨e⟩ := hΩ
      exact center_bot_of_mulEquiv e hc.2
    · obtain ⟨e⟩ := hΩ
      exact center_bot_of_mulEquiv e hc.1

theorem isOmegaTwo_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (ε : Bool) (m : ℕ)
    (h : IsOmegaTwo ε m A) : IsOmegaTwo ε m B := by
  cases ε
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩
  · obtain ⟨f⟩ := h
    exact ⟨e.symm.trans f⟩

theorem eq_of_le_of_card_two {G : Type*} [Group G] {A B : Subgroup G} (hle : A ≤ B) (hne : A ≠ ⊥)
    (hB : Nat.card B = 2) : A = B := by
  have h1 : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hle
  rw [hB] at h1
  have h2 : Nat.card A ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have h3 : Nat.card A = 2 := ((Nat.dvd_prime Nat.prime_two).1 h1).resolve_left h2
  haveI : Finite B := Nat.finite_of_card_ne_zero (by omega)
  exact Subgroup.eq_of_le_of_card_ge hle (by omega)

theorem congr_trans_toMonoidHom {A B C : Type*} [Group A] [Group B] [Group C] (ι : A ≃* B)
    (e : B ≃* C) :
    (MulAut.congr (ι.trans e)).toMonoidHom =
      (MulAut.congr e).toMonoidHom.comp (MulAut.congr ι).toMonoidHom :=
  MonoidHom.ext fun f => MulEquiv.ext fun k => rfl

theorem actsAsTransvectionAt_transport {Y Y' : Type*} [Group Y] [Group Y'] (ε : Bool) (n : ℕ)
    (W A : Subgroup Y) (W' A' : Subgroup Y') (ι : ↥A ≃* ↥A')
    (hle : (inducedAutGroup W A).map (MulAut.congr ι).toMonoidHom ≤ inducedAutGroup W' A')
    (hne : (inducedAutGroup W A).map (MulAut.congr ι).toMonoidHom ≠ ⊥) :
    ActsAsTransvectionAt ε n W' A' → ActsAsTransvectionAt ε n W A := by
  cases ε
  · rintro ⟨e, hcard, t, ht, hQ, hT, hlike⟩
    have hind := eq_of_le_of_card_two hle hne hcard
    refine ⟨ι.trans e, ?_, t, ht, hQ, hT, ?_⟩
    · rw [← Subgroup.card_map_of_injective (f := (MulAut.congr ι).toMonoidHom)
        (MulAut.congr ι).injective, hind]
      exact hcard
    · show (inducedAutGroup W A).map (MulAut.congr (ι.trans e)).toMonoidHom = _
      rw [congr_trans_toMonoidHom ι e, ← Subgroup.map_map, hind]
      exact hlike
  · rintro ⟨e, hcard, t, ht, hQ, hT, hlike⟩
    have hind := eq_of_le_of_card_two hle hne hcard
    refine ⟨ι.trans e, ?_, t, ht, hQ, hT, ?_⟩
    · rw [← Subgroup.card_map_of_injective (f := (MulAut.congr ι).toMonoidHom)
        (MulAut.congr ι).injective, hind]
      exact hcard
    · show (inducedAutGroup W A).map (MulAut.congr (ι.trans e)).toMonoidHom = _
      rw [congr_trans_toMonoidHom ι e, ← Subgroup.map_map, hind]
      exact hlike

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1920
