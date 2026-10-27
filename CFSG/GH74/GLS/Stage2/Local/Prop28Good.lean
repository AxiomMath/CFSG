module

public import CFSG.GH74.GLS.Stage2.Local.Prop28Basic
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk103Bar

public section

namespace CFSG.GH74.GLS.Stage2.Local.Prop28

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GorensteinWalter

theorem lieModel_of_isL2 {X : Type} [Group X] {r : ℕ} (hr3 : 3 < r)
    (h : IVK.IsL2 X (fun s => s = r)) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ p ^ f = r ∧ LieModel X .PSL 2 p f := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := h
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).mp
    (show IsPrimePow (Nat.card F) by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.isPrimePow_card F)
  have hcard : Nat.card F = p ^ k := hpk.symm
  refine ⟨p, k, hp, hk, hpk.trans hq, ?_⟩
  have hadm : StatedLieAdmissible .PSL 2 p k := by
    refine ⟨hp, hk, le_rfl, ?_, ?_⟩
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
    · intro h
      simp only [Prod.mk.injEq, true_and] at h
      omega
  exact .inl ⟨by decide, hadm, F, hF, hfin, hcard, ⟨e⟩⟩

theorem isSimpleGroup_of_isL2 {X : Type} [Group X] {r : ℕ} (hr3 : 3 < r)
    (h : IVK.IsL2 X (fun s => s = r)) : IsSimpleGroup X := by
  obtain ⟨F, hF, hfin, hq, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card F := by omega
  have : IsSimpleGroup (PSL2 F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (e.trans (IVK.L2.equivPSL F)).isSimpleGroup

theorem isSimpleGroup_of_A7 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 7))) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  exact e.isSimpleGroup

theorem good_of_A7 {K : Type} [Group K] (hq : IsQuasisimple K)
    (h : Nonempty (K ≃* alternatingGroup (Fin 7))) : Good K :=
  Or.inr ⟨hq, Or.inr (Or.inr (Or.inl h))⟩

theorem good_of_isL2
    {K : Type} [Group K] (hq : IsQuasisimple K) {r : ℕ} (hr : Odd r) (hr3 : 3 < r)
    (h : IVK.IsL2 K (fun s => s = r)) : Good K := by
  obtain ⟨p, f, hp, hf, hpf, hL⟩ := lieModel_of_isL2 hr3 h
  by_cases hfm : IsFM9 r
  · exact Or.inl (IVK.Proofs2.inC2_of_hasL2Model_fm9 hq ⟨p, f, hp, hf, hpf ▸ hfm, hL⟩)
  · exact Or.inr ⟨hq, Or.inl ⟨p, f, hp, hf, ⟨hpf ▸ hr, hpf ▸ hfm⟩, hL⟩⟩

end CFSG.GH74.GLS.Stage2.Local.Prop28
