module

public import CFSG.Open.GLBDefs
public import CFSG.Open.RankThreeDefs
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open
open CFSG.GH74.Uniqueness.SU

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_of_unique_isElemAbelian {p : ℕ} {Q E : Subgroup G}
    (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2) (hEQ : E ≤ Q)
    (hunique : ∀ D : Subgroup G, D ≤ Q → IsElemAbelian p D → Nat.card D = p ^ 2 → D = E) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  have hconj : ∀ n ∈ Subgroup.normalizer (Q : Set G), ∀ e ∈ E, n * e * n⁻¹ ∈ E := by
    intro n hn e he
    have hcard : Nat.card (E.map (MulAut.conj n).toMonoidHom) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hEcard]
    have hel : IsElemAbelian p (E.map (MulAut.conj n).toMonoidHom) := by
      rw [SU1.isElemAbelian_iff] at hE ⊢
      refine ⟨?_, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        rw [← map_mul, ← map_mul, hE.1 a ha b hb]
      · rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hE.2 a ha, map_one]
    have hle : E.map (MulAut.conj n).toMonoidHom ≤ Q := by
      rintro _ ⟨y, hy, rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp hn y).mp (hEQ hy)
      simpa [MulAut.conj_apply] using this
    have heq := hunique _ hle hel hcard
    have h2 : n * e * n⁻¹ ∈ E.map (MulAut.conj n).toMonoidHom :=
      ⟨e, he, by simp [MulAut.conj_apply]⟩
    rwa [heq] at h2
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hconj n hn h, fun hh => ?_⟩
  have h2 := hconj n⁻¹ (Subgroup.inv_mem _ hn) _ hh
  have e : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h := by group
  rwa [e] at h2

theorem eq_of_isElemAbelian_of_pRank_lt_three [Finite G] {p : ℕ} (hp : p.Prime)
    {P Q E : Subgroup G} (hEP : E ≤ P) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEcent : ∀ e ∈ E, ∀ x ∈ P, e * x = x * e) (hQP : Q ≤ P)
    (hQ : pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G))) < 3) :
    ∀ D : Subgroup G, D ≤ Q → IsElemAbelian p D → Nat.card D = p ^ 2 → D = E := by
  intro D hDQ hD hDcard
  by_contra hDE
  have hsup : IsElemAbelian p (D ⊔ E) :=
    SU1.IsElemAbelian.sup hD hE fun d hd e he => (hEcent e he d (hQP (hDQ hd))).symm
  have hlt : D < D ⊔ E := by
    refine lt_of_le_of_ne le_sup_left fun h => hDE ?_
    have hED : E ≤ D := le_sup_right.trans h.ge
    exact (Subgroup.eq_of_le_of_card_ge hED (hDcard.trans hEcard.symm).le).symm
  obtain ⟨m, hm⟩ := SU1.IsElemAbelian.exists_card hp hsup
  have hcard := SU1.card_lt_of_lt hlt
  rw [hDcard, hm] at hcard
  have h3m : 3 ≤ m := by
    by_contra hm3
    have : p ^ m ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    exact absurd this (not_le.mpr hcard)
  refine absurd (h3m.trans (SU1.le_pRank hp.one_lt ?_ hsup hm)) (not_le.mpr hQ)
  refine sup_le (le_sup_of_le_left hDQ) (le_sup_of_le_right (le_inf hEP fun e he => ?_))
  exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hEcent e he x (hQP hx)).symm

theorem rankThreeGamma_two_le_GLBWeakCore [Finite G] {p : ℕ} (hp : p.Prime) {P E : Subgroup G}
    (hEP : E ≤ P) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    (hEcent : ∀ e ∈ E, ∀ x ∈ P, e * x = x * e) (h3 : 3 ≤ pRank p P) :
    rankThreeGamma 2 p P ≤ GLBWeakCore p P := by
  have hPle : P ≤ E ⊔ (P ⊓ Subgroup.centralizer (E : Set G)) := fun x hx =>
    Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun e he => hEcent e he x hx⟩)
  have hN : Subgroup.normalizer (E : Set G) ≤ GLBWeakCore p P :=
    le_sSup ⟨E, hEP, SU1.le_pRank hp.one_lt le_rfl hE hEcard,
      h3.trans (SU1.pRank_mono hp.one_lt hPle), rfl⟩
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hQ2, rfl⟩
  by_cases hcase : 3 ≤ pRank p (Q ⊔ (P ⊓ Subgroup.centralizer (Q : Set G)))
  · exact le_sSup ⟨Q, hQP, hQ2, hcase, rfl⟩
  refine le_trans ?_ hN
  have key := eq_of_isElemAbelian_of_pRank_lt_three hp hEP hE hEcard hEcent hQP (not_le.mp hcase)
  have hEQ : E ≤ Q := by
    obtain ⟨D, hDQ, hD, hDcard⟩ := SU1.exists_isElemAbelian_of_le_pRank hp hQ2
    rwa [← key D hDQ hD hDcard]
  exact normalizer_le_normalizer_of_unique_isElemAbelian hE hEcard hEQ key

end CFSG.LocalAnalysis.RankThreeTheoremC
