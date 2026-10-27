module

public import CFSG.LieType.SeitzGeneration.LowNarrow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem _root_.CFSG.AGLEmbeddingD2.D2AlmostSimple.false_of_seitzLowN {X : Type*} [Group X]
    [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X} (h : D2AlmostSimple p X R A X₀ K)
    (hS : KFactSeitzRankTwoLowN) (d : TauCeti.ValidLieTypeIndex)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hp : p ≠ d.1.characteristic)
    (hex : ¬ IsD2SeitzException p d.1) : False := by
  have : K.Normal := h.normal
  have hrank : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
    by_contra hcon
    exact h.false_of_three_le_pRank (by omega)
  have hRK : RankLE2 p (Cat d) := RankLE2.of_mulEquiv e (RankLE2.of_pRank h.prime hrank)
  have hRX : RankLE2 p X := RankLE2.of_pRank h.prime h.pRank_top.le
  have hφ : Function.Injective (MulAut.conjNormal (H := K)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxc : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hx ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [h.centralizer_eq_bot] at hxc
    exact Subgroup.mem_bot.mp hxc
  let ψ : X →* MulAut (TauCeti.CFSGIndex.lie d).Group :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hψ : Function.Injective ψ := fun x y hxy => hφ ((MulAut.congr e).injective hxy)
  have hfix : ∀ (a : X) (k : K), ψ a (e k) = e k ↔ a * (k : X) * a⁻¹ = k := by
    intro a k
    have h1 : ψ a (e k) = e (MulAut.conjNormal (H := K) a k) := by
      simp [ψ, MulAut.congr_apply]
    rw [h1, e.apply_eq_iff_eq, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  have hKψ : K.map ψ = (MulAut.conj : Cat d →* MulAut (Cat d)).range := by
    have h1 : K.map (MulAut.conjNormal (H := K)) = (MulAut.conj : K →* MulAut K).range := by
      ext φ
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨k, k.2, MulAut.conjNormal_val⟩
    rw [← map_range_conj_congr e, ← h1, Subgroup.map_map]
  have hPR2 : PlaneRank2 p (A.map ψ) := by
    unfold PlaneRank2
    rw [← hKψ, ← Subgroup.map_sup]
    exact RankLE2.of_mulEquiv (Subgroup.equivMapOfInjective _ ψ hψ) (hRX.subgroup _)
  have hclos : Subgroup.closure
      {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ A.map ψ, ε ≠ 1 ∧ ε k = k} = ⊤ := by
    have hel : IsElemAbelian p (A.map ψ) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p h.elem ψ
    have hcard : Nat.card (A.map ψ) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hψ, h.card_A]
    by_cases hin : InnerPlane d p (A.map ψ)
    · exact hS.1 d p h.prime h.ne_two hp hex (A.map ψ) hel hcard ⟨hin, hRK⟩
    · exact hS.2 d p h.prime h.ne_two hp hex (A.map ψ) hel hcard ⟨hin, hRK, Or.inr hPR2⟩
  have hgen : Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k} = ⊤ := by
    rw [eq_top_iff]
    intro k _
    have hk : e k ∈ Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ A.map ψ, ε ≠ 1 ∧ ε k = k} := by
      rw [hclos]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure
        {k : (TauCeti.CFSGIndex.lie d).Group | ∃ ε ∈ A.map ψ, ε ≠ 1 ∧ ε k = k} ≤
        (Subgroup.closure {k : K | ∃ a ∈ A, a ≠ 1 ∧ a * (k : X) * a⁻¹ = k}).map e.toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro t ⟨_, ⟨a, haA, rfl⟩, hε1, hεt⟩
      refine ⟨e.symm t, Subgroup.subset_closure ⟨a, haA, ?_, ?_⟩, by simp⟩
      · rintro rfl
        exact hε1 (map_one ψ)
      · refine (hfix a (e.symm t)).mp ?_
        simpa using hεt
    obtain ⟨y, hy, hyk⟩ := hle hk
    exact (e.injective hyk) ▸ hy
  exact h.not_le (h.le_of_closure_fixed hgen)

end CFSG.LieType.SeitzGeneration
