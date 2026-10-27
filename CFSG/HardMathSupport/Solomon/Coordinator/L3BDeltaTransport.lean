module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem eq_one_of_transport {Y P : Type*} [Group Y] [Group P] (hperf : commutator Y = ⊤)
    (e : (Y ⧸ Subgroup.center Y) ≃* P) {D H : Subgroup (MulAut Y)} (hD : IsEkIn 3 2 ⊤ D)
    (hH : innerAut Y ≤ H) {α : MulAut Y} (hα : α ∈ localDeltaIn 3 H D) {φ : MulAut P}
    (hφ : ∀ y : Y, e (QuotientGroup.mk (α y)) = φ (e (QuotientGroup.mk y)))
    (hmodel : ∀ D' H' : Subgroup (MulAut P), IsElemAbelian 3 D' → Nat.card D' = 9 →
      innerAut P ≤ H' → φ ∈ localDeltaIn 3 H' D' → φ = 1) : α = 1 := by
  set Ψ : MulAut Y →* MulAut P :=
    (MulAut.congr e).toMonoidHom.comp (autCenterQuot Y) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.congr e).injective.comp (autCenterQuot_injective_of_perfect hperf)
  have hΨα : Ψ α = φ := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨q, rfl⟩ := e.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    show e ((autCenterQuot Y α) (e.symm (e (QuotientGroup.mk y)))) = φ (e (QuotientGroup.mk y))
    rw [MulEquiv.symm_apply_apply, autCenterQuot_mk]
    exact hφ y
  obtain ⟨hDle, ⟨hcomm, hexp⟩, hcard⟩ := hD
  have hD' : IsElemAbelian 3 (D.map Ψ) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      change Ψ x * Ψ y = Ψ y * Ψ x
      have := congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [← map_mul, ← map_mul]
      exact congrArg Ψ this
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hexp x hx, map_one]
  have hcard' : Nat.card (D.map Ψ) = 9 := by
    rw [Subgroup.card_map_of_injective hΨinj, hcard]
    norm_num
  have hinn : innerAut P ≤ (innerAut Y).map Ψ := by
    have h1 : innerAut P ≤ (innerAut (Y ⧸ Subgroup.center Y)).map (MulAut.congr e).toMonoidHom := by
      rintro _ ⟨y, rfl⟩
      refine ⟨MulAut.conj (e.symm y), ⟨e.symm y, rfl⟩, ?_⟩
      ext z
      simp [MulAut.congr_apply, MulAut.conj_apply]
    refine h1.trans ?_
    rw [hΨ, ← Subgroup.map_map]
    exact Subgroup.map_mono innerAut_le_map_autCenterQuot
  have hle := map_localDeltaIn_le 3 Ψ hΨinj H D
  have hmem : φ ∈ localDeltaIn 3 (H.map Ψ) (D.map Ψ) := by
    rw [← hΨα]
    exact hle ⟨α, hα, rfl⟩
  have h1 : Ψ α = 1 := by
    rw [hΨα]
    exact hmodel _ _ hD' hcard' (hinn.trans (Subgroup.map_mono hH)) hmem
  rw [← map_one Ψ] at h1
  exact hΨinj h1

end CFSG.HardMathSupport.Solomon.Coordinator
