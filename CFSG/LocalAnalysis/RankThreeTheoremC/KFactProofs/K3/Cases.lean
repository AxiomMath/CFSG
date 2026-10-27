module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.Invariant

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.ABGLocalTools (IsSylowOf)

section Invariant

variable {H : Type} [Group H] [Finite H]

theorem cc_map_conj_eq_iff (L : Subgroup H) (g : H) :
    L.map (MulAut.conj g).toMonoidHom = L ↔ g ∈ normalizer (L : Set H) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MulEquiv.toMonoidHom_eq_coe]

theorem cc_map_conj_map (L : Subgroup H) (g q : H) :
    (L.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom =
      L.map (MulAut.conj (q * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc, mul_inv_rev]

theorem cc_map_conj_one (L : Subgroup H) :
    L.map (MulAut.conj (1 : H)).toMonoidHom = L := by
  ext x
  simp

theorem three_group_fixes_of_two {Q : Subgroup H} (hQ : IsPGroup 3 Q) {A B : Subgroup H}
    {q : H} (hq : q ∈ Q)
    (hA : A.map (MulAut.conj q).toMonoidHom = A ∨ A.map (MulAut.conj q).toMonoidHom = B)
    (hB : B.map (MulAut.conj q).toMonoidHom = A ∨ B.map (MulAut.conj q).toMonoidHom = B) :
    A.map (MulAut.conj q).toMonoidHom = A := by
  by_contra hne
  have hAB : A.map (MulAut.conj q).toMonoidHom = B := hA.resolve_left hne
  have hBA : B.map (MulAut.conj q).toMonoidHom = A := by
    rcases hB with h | h
    · exact h
    · exfalso
      have hAeq : A = B :=
        Subgroup.map_injective (f := (MulAut.conj q).toMonoidHom) (MulAut.conj q).injective
          (hAB.trans h.symm)
      exact hne (hAB.trans hAeq.symm)
  have hcomp : (MulAut.conj q).toMonoidHom.comp (MulAut.conj q).toMonoidHom =
      (MulAut.conj (q ^ 2)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, pow_two, mul_assoc, mul_inv_rev]
  have h2 : A.map (MulAut.conj (q ^ 2)).toMonoidHom = A := by
    rw [← hcomp, ← Subgroup.map_map, hAB, hBA]
  have hsq : q ^ 2 ∈ normalizer (A : Set H) := (cc_map_conj_eq_iff A (q ^ 2)).mp h2
  obtain ⟨a, ha⟩ := hQ ⟨q, hq⟩
  have hqa : q ^ 3 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  obtain ⟨m, hm⟩ : Odd (3 ^ a) := Odd.pow ⟨1, by norm_num⟩
  have h3 : q ^ (2 * m + 1) = 1 := by
    rw [← hm]
    exact hqa
  have hq1 : q = (q ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc q = q ^ (2 * m + 1) * q := by rw [h3, one_mul]
      _ = q ^ (2 * (m + 1)) := by
        rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by omega]
  have hqN : q ∈ normalizer (A : Set H) := by
    have := Subgroup.pow_mem _ hsq (m + 1)
    rwa [← hq1] at this
  exact hne ((cc_map_conj_eq_iff A q).mpr hqN)

theorem components_cases (hH : primeComplementCore (G := H) 3 = ⊥) (S : Sylow 3 H)
    (hSW : Nonempty ((S : Subgroup H) ≃* W3)) {L : Subgroup H} (hL : IsComponentOf L ⊤) :
    (∃ L₀ : Subgroup H, IsComponentOf L₀ ⊤ ∧ ∀ K : Subgroup H, IsComponentOf K ⊤ → K = L₀) ∨
    (∃ L₀ : Subgroup H, IsComponentOf L₀ ⊤ ∧
      (∀ K : Subgroup H, IsComponentOf K ⊤ →
        ∃ g ∈ (S : Subgroup H), K = L₀.map (MulAut.conj g).toMonoidHom) ∧
      ¬ (S : Subgroup H) ≤ normalizer (L₀ : Set H)) := by
  classical
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3 := pRank_top_le_three_of_wreath S hSW
  by_cases hinv : ∀ K : Subgroup H, IsComponentOf K ⊤ → (S : Subgroup H) ≤ normalizer (K : Set H)
  · left
    refine ⟨L, hL, fun K hK => ?_⟩
    by_contra hne
    exact not_two_invariant hH S hSW hK hL hne (hinv K hK) (hinv L hL)
  · right
    push_neg at hinv
    obtain ⟨L₀, hL₀, hnot⟩ := hinv
    obtain ⟨g, hgS, hgN⟩ : ∃ g ∈ (S : Subgroup H), g ∉ normalizer (L₀ : Set H) := by
      by_contra hcon
      push_neg at hcon
      apply hnot
      intro x hx
      exact hcon x hx
    have hL₁ : IsComponentOf (L₀.map (MulAut.conj g).toMonoidHom) ⊤ :=
      isComponentOf_map_conj hL₀ g
    have hne₁ : L₀.map (MulAut.conj g).toMonoidHom ≠ L₀ := by
      intro heq
      exact hgN ((cc_map_conj_eq_iff L₀ g).mp heq)
    obtain ⟨h, hhS, hh0, hh1⟩ : ∃ h ∈ (S : Subgroup H),
        L₀.map (MulAut.conj h).toMonoidHom ≠ L₀ ∧
          L₀.map (MulAut.conj h).toMonoidHom ≠ L₀.map (MulAut.conj g).toMonoidHom := by
      by_contra hcon
      push_neg at hcon
      have hcov : ∀ q ∈ (S : Subgroup H), L₀.map (MulAut.conj q).toMonoidHom = L₀ ∨
          L₀.map (MulAut.conj q).toMonoidHom = L₀.map (MulAut.conj g).toMonoidHom := by
        intro q hq
        by_cases hq0 : L₀.map (MulAut.conj q).toMonoidHom = L₀
        · exact Or.inl hq0
        · exact Or.inr (hcon q hq hq0)
      have hfix : ∀ q ∈ (S : Subgroup H), L₀.map (MulAut.conj q).toMonoidHom = L₀ := by
        intro q hq
        have hB : (L₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom = L₀ ∨
            (L₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj q).toMonoidHom =
              L₀.map (MulAut.conj g).toMonoidHom := by
          rw [cc_map_conj_map]
          exact hcov (q * g) (Subgroup.mul_mem _ hq hgS)
        exact three_group_fixes_of_two S.isPGroup' hq (hcov q hq) hB
      apply hnot
      intro q hq
      exact (cc_map_conj_eq_iff L₀ q).mp (hfix q hq)
    have hL₂ : IsComponentOf (L₀.map (MulAut.conj h).toMonoidHom) ⊤ :=
      isComponentOf_map_conj hL₀ h
    have hcover : ∀ K : Subgroup H, IsComponentOf K ⊤ →
        K = L₀ ∨ K = L₀.map (MulAut.conj g).toMonoidHom ∨
          K = L₀.map (MulAut.conj h).toMonoidHom := by
      intro K hK
      by_contra hcon
      push_neg at hcon
      obtain ⟨k0, k1, k2⟩ := hcon
      exact no_four_components hH hrank hL₀ hL₁ hL₂ hK hne₁.symm hh0.symm k0.symm
        hh1.symm k1.symm k2.symm
    refine ⟨L₀, hL₀, ?_, hnot⟩
    intro K hK
    rcases hcover K hK with hK0 | hK1 | hK2
    · exact ⟨1, Subgroup.one_mem _, by rw [hK0, cc_map_conj_one]⟩
    · exact ⟨g, hgS, hK1⟩
    · exact ⟨h, hhS, hK2⟩

end Invariant

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3
