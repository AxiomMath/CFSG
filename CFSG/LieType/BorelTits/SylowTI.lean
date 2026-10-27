module

public import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LieType.BorelTits

variable {X : Type*} [Group X]

private theorem covBy_top_normalizer_of_smul {r : ℕ} [Fact r.Prime] [Finite X]
    {S₀ S₁ : Sylow r X}
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ⋖ ⊤) :
    Subgroup.normalizer ((S₁ : Subgroup X) : Set X) ⋖ ⊤ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S₀ S₁
  have hcoe : (S₁ : Subgroup X) = (S₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hcoe, ← Subgroup.map_equiv_normalizer_eq]
  have htop : (⊤ : Subgroup X).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  rw [← htop]
  exact (apply_covBy_apply_iff (MulEquiv.mapSubgroup (MulAut.conj g))).mpr hS₀

private theorem isPGroup_le_of_le_normalizer {r : ℕ} [Fact r.Prime] {H : Subgroup X}
    (hH : IsPGroup r H) (Q : Sylow r X)
    (hN : H ≤ Subgroup.normalizer (Q : Set X)) : H ≤ Q := by
  have h := hH.inf_normalizer_sylow Q
  rw [inf_eq_left.mpr hN] at h
  exact inf_eq_left.mp h.symm

private theorem exists_sylow_normalizer_ge {r : ℕ} [Fact r.Prime] [Finite X]
    (h : Holds X r) {S₀ : Sylow r X}
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ⋖ ⊤)
    {V : Subgroup X} (hV : V ≠ ⊥) (hp : IsPGroup r V) :
    ∃ S₁ : Sylow r X, Subgroup.normalizer (V : Set X) ≤
        Subgroup.normalizer ((S₁ : Subgroup X) : Set X) ∧ V ≤ S₁ := by
  obtain ⟨S₁, P, hP, hNV, -, hVP, hNS⟩ := h V hV hp
  have hmax : Subgroup.normalizer ((S₁ : Subgroup X) : Set X) ⋖ ⊤ :=
    covBy_top_normalizer_of_smul hS₀
  have hPeq : P = Subgroup.normalizer ((S₁ : Subgroup X) : Set X) :=
    (hmax.eq_or_eq hNS le_top).resolve_right hP
  rw [hPeq] at hNV hVP
  exact ⟨S₁, hNV, hVP.trans (isPGroup_le_of_le_normalizer (pCoreOf_isPGroup r _) S₁
    (pCoreOf_le r _))⟩

private theorem lt_inf_sylow_of_normalizer_le {r : ℕ} [Fact r.Prime] [Finite X]
    {V : Subgroup X} {S₁ : Sylow r X}
    (hN : Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer ((S₁ : Subgroup X) : Set X))
    {P : Subgroup X} (hPp : IsPGroup r P) (hVP : V < P) :
    V < P ⊓ (S₁ : Subgroup X) := by
  have hlt : V < P ⊓ Subgroup.normalizer (V : Set X) :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hPp hVP
  have hle : P ⊓ Subgroup.normalizer (V : Set X) ≤ (S₁ : Subgroup X) :=
    isPGroup_le_of_le_normalizer (hPp.to_le inf_le_left) S₁ (inf_le_right.trans hN)
  exact lt_of_lt_of_le hlt (le_inf inf_le_left hle)

private theorem card_sub_lt_of_lt [Finite X] {V W : Subgroup X} (hVW : V < W) :
    Nat.card X - Nat.card ↥W < Nat.card X - Nat.card ↥V :=
  Nat.sub_lt_sub_left
    (lt_of_lt_of_le (Subgroup.card_lt_of_lt hVW) (Subgroup.card_le_card_group (H := W)))
    (Subgroup.card_lt_of_lt hVW)

theorem Holds.eq_of_inf_ne_bot [Finite X] {r : ℕ} [Fact r.Prime] (h : Holds X r)
    {S₀ : Sylow r X} (hS₀ : Subgroup.normalizer ((S₀ : Subgroup X) : Set X) ⋖ ⊤)
    {S T : Sylow r X} (hST : (S : Subgroup X) ⊓ T ≠ ⊥) : S = T := by
  classical
  have key : ∀ n, ∀ S T : Sylow r X,
      Nat.card X - Nat.card ↥((S : Subgroup X) ⊓ (T : Subgroup X)) = n →
      (S : Subgroup X) ⊓ (T : Subgroup X) ≠ ⊥ → S = T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S T hmeas hST
      by_contra hne
      let V : Subgroup X := (S : Subgroup X) ⊓ (T : Subgroup X)
      have hVne : V ≠ ⊥ := hST
      have hVp : IsPGroup r V := S.isPGroup'.to_le inf_le_left
      obtain ⟨S₁, hNle, -⟩ := exists_sylow_normalizer_ge h hS₀ hVne hVp
      have hVltS : V < (S : Subgroup X) := by
        refine lt_of_le_of_ne inf_le_left fun hEq =>
          hne (Sylow.ext (S.is_maximal' T.isPGroup' (hEq ▸ inf_le_right))).symm
      have hVltT : V < (T : Subgroup X) := by
        refine lt_of_le_of_ne inf_le_right fun hEq =>
          hne (Sylow.ext (T.is_maximal' S.isPGroup' (hEq ▸ inf_le_left)))
      have hVltSS₁ : V < (S : Subgroup X) ⊓ (S₁ : Subgroup X) :=
        lt_inf_sylow_of_normalizer_le hNle S.isPGroup' hVltS
      have hVltTS₁ : V < (T : Subgroup X) ⊓ (S₁ : Subgroup X) :=
        lt_inf_sylow_of_normalizer_le hNle T.isPGroup' hVltT
      have hSS₁ne : (S : Subgroup X) ⊓ (S₁ : Subgroup X) ≠ ⊥ := fun hbot =>
        hVne (le_bot_iff.mp (hbot ▸ hVltSS₁.le))
      have hTS₁ne : (T : Subgroup X) ⊓ (S₁ : Subgroup X) ≠ ⊥ := fun hbot =>
        hVne (le_bot_iff.mp (hbot ▸ hVltTS₁.le))
      have hSS₁ : S = S₁ := by
        refine ih _ ?_ S S₁ rfl hSS₁ne
        rw [← hmeas]
        exact card_sub_lt_of_lt hVltSS₁
      have hTS₁ : T = S₁ := by
        refine ih _ ?_ T S₁ rfl hTS₁ne
        rw [← hmeas]
        exact card_sub_lt_of_lt hVltTS₁
      exact hne (hSS₁.trans hTS₁.symm)
  exact key _ S T rfl hST

end CFSG.LieType.BorelTits
