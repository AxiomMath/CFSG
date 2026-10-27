module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.IsolatedFive

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Subgroup

section ZStarClass

variable {H : Type} [Group H] [Finite H]

theorem isolated_of_huniq {v : H} (hv : v * v = 1) (hv1 : v ≠ 1)
    (huniq : ∀ t : H, t * t = 1 → t * v = v * t → t = 1 ∨ t = v) (g : H)
    (hg : (g * v * g⁻¹) * v = v * (g * v * g⁻¹)) : g * v * g⁻¹ = v := by
  have ht2 : (g * v * g⁻¹) * (g * v * g⁻¹) = 1 := by
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv]; group
  rcases huniq _ ht2 hg with h | h
  · exfalso
    apply hv1
    have := congrArg (fun a => g⁻¹ * a * g) h
    simpa [mul_assoc] using this
  · exact h

theorem odd_ncard_conj_of_zStar {v : H} (hv : v * v = 1) (hv1 : v ≠ 1)
    (hiso : ∀ g : H, (g * v * g⁻¹) * v = v * (g * v * g⁻¹) → g * v * g⁻¹ = v) :
    Odd {w : H | IsConj v w}.ncard := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨N, hNn, hNodd, hNc⟩ := CFSG.ZStar.glauberman_zStar H v hv1 hv hiso
  have hfr := exists_mul_centralizer_of_zStar hv hNodd hNc
  set V : Set H := {w : H | IsConj v w} with hVdef
  have hV : ∀ g ∈ N, ∀ s ∈ V, g * s * g⁻¹ ∈ V := fun g _ s hs =>
    hs.trans (isConj_iff.2 ⟨g, rfl⟩)
  letI : MulAction N V := conjSMulOn N V hV
  let s₀ : V := ⟨v, IsConj.refl v⟩
  have horbit : MulAction.orbit N s₀ = Set.univ := by
    ext s
    simp only [Set.mem_univ, iff_true]
    obtain ⟨h, hh⟩ := isConj_iff.1 s.2
    obtain ⟨m, hm, k, hk, rfl⟩ := hfr h
    refine ⟨⟨m, hm⟩, Subtype.ext ?_⟩
    show m * v * m⁻¹ = s
    rw [← hh]
    have hkv : k * v * k⁻¹ = v := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hk]
      group
    calc m * v * m⁻¹ = m * (k * v * k⁻¹) * m⁻¹ := by rw [hkv]
      _ = m * k * v * (m * k)⁻¹ := by group
  have hidx : (MulAction.stabilizer N s₀).index = V.ncard := by
    rw [MulAction.index_stabilizer, horbit, Set.ncard_univ, Nat.card_coe_set_eq]
  have hdvd : V.ncard ∣ Nat.card N := hidx ▸ Subgroup.index_dvd_card _
  exact Odd.of_dvd_nat hNodd hdvd

theorem isConj_of_involution_of_zStar {v : H} (hv : v * v = 1) (hv1 : v ≠ 1)
    (huniq : ∀ t : H, t * t = 1 → t * v = v * t → t = 1 ∨ t = v) {t : H} (ht : t * t = 1)
    (ht1 : t ≠ 1) : IsConj v t := by
  have hodd := odd_ncard_conj_of_zStar hv hv1 (isolated_of_huniq hv hv1 huniq)
  have ht2 : orderOf t = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hmod := ncard_modEq_fixed (p := 2) Nat.prime_two ht2 (F := {w : H | IsConj v w}) (by
    intro g _ s hs
    exact hs.trans (isConj_iff.2 ⟨g, rfl⟩))
  have hne : {s | s ∈ {w : H | IsConj v w} ∧ t * s = s * t}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Set.ncard_empty] at hmod
    have h2 := (Nat.modEq_zero_iff_dvd).1 hmod
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨s, hsV, hts⟩ := hne
  obtain ⟨h, hh⟩ := isConj_iff.1 hsV
  have h1 : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
    calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
      _ = 1 := by rw [ht]; group
  have h2 : (h⁻¹ * t * h) * v = v * (h⁻¹ * t * h) := by
    have e : t * (h * v * h⁻¹) = (h * v * h⁻¹) * t := by rw [hh]; exact hts
    calc (h⁻¹ * t * h) * v = h⁻¹ * (t * (h * v * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * v * h⁻¹) * t) * h := by rw [e]
      _ = v * (h⁻¹ * t * h) := by group
  rcases huniq _ h1 h2 with h3 | h3
  · exfalso
    apply ht1
    have := congrArg (fun a => h * a * h⁻¹) h3
    simpa [mul_assoc] using this
  · refine isConj_iff.2 ⟨h, ?_⟩
    have := congrArg (fun a => h * a * h⁻¹) h3
    simpa [mul_assoc] using this.symm

end ZStarClass

end CFSG.HardMathSupport.Dickson.Sec6.I1431
