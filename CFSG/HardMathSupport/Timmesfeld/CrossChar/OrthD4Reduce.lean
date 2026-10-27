module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator

@[expose] def InnerPlanesBalanced (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ E : Subgroup (MulAut X), E ≤ innerAut X → IsElemAbelian p E → Nat.card E = p ^ 2 →
    ∀ H : Subgroup (MulAut X), innerAut X ≤ H → localDeltaIn p H E = ⊥

theorem isElemAbelian_of_le {M : Type*} [Group M] {p : ℕ} {D E : Subgroup M}
    (hD : IsElemAbelian p D) (hED : E ≤ D) : IsElemAbelian p E :=
  CFSG.Open.IsElemAbelian.mono hD hED

theorem d4_isElemAbelian_map {M N : Type*} [Group M] [Group N] {p : ℕ} (ψ : M →* N)
    {D : Subgroup M} (hD : IsElemAbelian p D) : IsElemAbelian p (D.map ψ) :=
  CFSG.Open.IsElemAbelian.map hD _

theorem InnerPlanesBalanced.of_mulEquiv {p : ℕ} {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : InnerPlanesBalanced p Y) : InnerPlanesBalanced p X := by
  intro E hE hEl hc H hH
  set ψ : MulAut X →* MulAut Y := (MulAut.congr e).toMonoidHom with hψdef
  have hψ : Function.Injective ψ := (MulAut.congr e).injective
  have hinn : innerAut Y ≤ (innerAut X).map ψ := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
    ext z
    simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have hEY : E.map ψ ≤ innerAut Y := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, rfl⟩ := hE ha
    refine ⟨e x, ?_⟩
    ext z
    simp [hψdef, MulAut.congr_apply, MulAut.conj_apply]
  have h0 := h (E.map ψ) hEY (d4_isElemAbelian_map ψ hEl)
    (by rw [Subgroup.card_map_of_injective hψ, hc]) (H.map ψ)
    (hinn.trans (Subgroup.map_mono hH))
  have hle := map_localDeltaIn_le p ψ hψ H E
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ hψ] at hle
  exact hle

theorem isLocallyBalancedAbs_of_planes_or_element {X : Type*} [Group X] {p : ℕ}
    (hpl : InnerPlanesBalanced p X)
    (h : ∀ D : Subgroup (MulAut X), IsElemAbelian p D → Nat.card D = p ^ 3 →
      (∃ E : Subgroup (MulAut X), E ≤ D ∧ E ≤ innerAut X ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ 2) ∨
      ∀ H : Subgroup (MulAut X), innerAut X ≤ H → localDeltaIn p H D = ⊥) :
    IsLocallyBalancedAbs p 3 X := by
  intro D hD hcard H hH _
  rcases h D hD hcard with ⟨E, hED, hEin, hE, hEc⟩ | hall
  · exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans (hpl E hEin hE hEc H hH).le)
  · exact hall H hH

theorem card_inf_ge_of_index_le {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    {D E : Subgroup M} (hD : Nat.card D = p ^ 3) (hE : E.index ≤ p) :
    p ^ 2 ≤ Nat.card (D ⊓ E : Subgroup M) := by
  have h1 : E.relIndex D ≤ E.index := by
    have h := Subgroup.relIndex_le_of_le_right (H := E) (le_top : D ≤ ⊤)
      (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right] at h
  have h2 := Subgroup.relIndex_mul_card E D
  rw [hD, inf_comm] at h2
  have h3 : p ^ 3 ≤ p * Nat.card (D ⊓ E : Subgroup M) := by
    rw [← h2]
    exact Nat.mul_le_mul_right _ (h1.trans hE)
  have h4 : p * p ^ 2 ≤ p * Nat.card (D ⊓ E : Subgroup M) := by
    rw [show p * p ^ 2 = p ^ 3 by ring]
    exact h3
  exact Nat.le_of_mul_le_mul_left h4 hp.pos

theorem exists_plane_of_card_inf_ge {M : Type*} [Group M] {p : ℕ} (hp : p.Prime)
    {D I : Subgroup M} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3)
    (h : p ^ 2 ≤ Nat.card (D ⊓ I : Subgroup M)) :
    ∃ E : Subgroup M, E ≤ D ∧ E ≤ I ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : Nat.card (D ⊓ I : Subgroup M) ∣ p ^ 3 :=
    hcard ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hjk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    push Not at hlt
    have h1 : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hfin : Finite (D ⊓ I : Subgroup M) :=
    Nat.finite_of_card_ne_zero (by rw [hjk]; exact pow_ne_zero j hp.ne_zero)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime p
    (show p ^ 2 ∣ Nat.card (D ⊓ I : Subgroup M) from hjk ▸ pow_dvd_pow p hj2)
  have hle : P.map (D ⊓ I).subtype ≤ D ⊓ I := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  refine ⟨P.map (D ⊓ I).subtype, hle.trans inf_le_left, hle.trans inf_le_right,
    isElemAbelian_of_le hD (hle.trans inf_le_left), ?_⟩
  rw [Subgroup.card_map_of_injective (D ⊓ I).subtype_injective, hP]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
