module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3D73dU
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BDelta
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem localDeltaIn_eq_bot_of_transport {Y P : Type*} [Group Y] [Group P]
    (hperf : commutator Y = ⊤) (e : (Y ⧸ Subgroup.center Y) ≃* P) {D H : Subgroup (MulAut Y)}
    (hD : IsEkIn 3 2 ⊤ D) (hH : innerAut Y ≤ H) (S : Subgroup (MulAut P)) {α : MulAut Y}
    (hα : α ∈ D) (hαS : MulAut.congr e (autCenterQuot Y α) ∉ S)
    (hmodel : ∀ D' H' : Subgroup (MulAut P), IsElemAbelian 3 D' → Nat.card D' = 9 →
      innerAut P ≤ H' → ¬ D' ≤ S → localDeltaIn 3 H' D' = ⊥) : localDeltaIn 3 H D = ⊥ := by
  set Ψ : MulAut Y →* MulAut P :=
    (MulAut.congr e).toMonoidHom.comp (autCenterQuot Y) with hΨ
  have hΨinj : Function.Injective Ψ :=
    (MulAut.congr e).injective.comp (autCenterQuot_injective_of_perfect hperf)
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
  have hnot : ¬ D.map Ψ ≤ S := fun hle => hαS (hle ⟨α, hα, rfl⟩)
  have h1 := hmodel _ _ hD' hcard' (hinn.trans (Subgroup.map_mono hH)) hnot
  have hle := map_localDeltaIn_le 3 Ψ hΨinj H D
  rw [eq_bot_iff]
  intro g hg
  have h2 : Ψ g ∈ (⊥ : Subgroup (MulAut P)) := h1 ▸ hle ⟨g, hg, rfl⟩
  rw [Subgroup.mem_bot, ← map_one Ψ] at h2
  rw [Subgroup.mem_bot]
  exact hΨinj h2

theorem congr_autCenterQuot_compat {Y P : Type*} [Group Y] [Group P]
    (e : (Y ⧸ Subgroup.center Y) ≃* P) (α : MulAut Y) (y : Y) :
    e (QuotientGroup.mk (α y)) = MulAut.congr e (autCenterQuot Y α) (e (QuotientGroup.mk y)) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    autCenterQuot_mk]

theorem input19_7_3d_holds : LocalBalance.Lemma54Ns.Input19_7_3d := by
  intro K _ _ hK hT D H hD hH hDH hΔ α hα
  by_contra hα'
  apply hΔ
  have hperf : commutator K = ⊤ := hK.1
  rcases hT with ⟨F, _, _, ⟨θ⟩⟩ | ⟨F, _, _, q, hFq, ⟨θ⟩⟩
  · set e : (K ⧸ Subgroup.center K) ≃* projectiveSL 3 F := θ.trans (psiPSL F) with he
    refine localDeltaIn_eq_bot_of_transport hperf e hD hH (linearAutGroup 3 F) hα ?_ ?_
    · intro hmem
      apply hα'
      left
      rw [linearAutGroup_eq_range] at hmem
      obtain ⟨A, hA⟩ := hmem
      refine ⟨F, inferInstance, inferInstance, θ,
        MulAut.congr (psiPSL F).symm (MulAut.congr e (autCenterQuot K α)), ?_, ?_⟩
      · refine isConjByGL_of_congr_eq_conjAut F _ A ?_
        have hcancel : MulAut.congr (psiPSL F) (MulAut.congr (psiPSL F).symm
            (MulAut.congr e (autCenterQuot K α))) = MulAut.congr e (autCenterQuot K α) := by
          ext w
          simp [MulAut.congr_apply]
        exact hcancel.trans hA.symm
      · intro y
        have h1 := congr_autCenterQuot_compat e α y
        have h2 : MulAut.congr e (autCenterQuot K α) (psiPSL F (θ (QuotientGroup.mk y))) =
            psiPSL F (θ (QuotientGroup.mk (α y))) := h1.symm
        have key := congr_apply_apply (psiPSL F).symm (MulAut.congr e (autCenterQuot K α))
          (psiPSL F (θ (QuotientGroup.mk y)))
        erw [MulEquiv.symm_apply_apply] at key
        exact ((MulEquiv.symm_apply_apply (psiPSL F) _).symm.trans
          (congrArg (psiPSL F).symm h2.symm)).trans key.symm
    · intro D' H' hD' _ hH' hnot
      exact localDeltaIn_eq_bot_of_not_le_linearAutGroup_three hD' hnot hH'
  · obtain ⟨p, f, rfl, ⟨h⟩⟩ := exists_unitaryFieldData hFq
    have hq := two_lt_of_quasisimple hK h θ
    set ψ := unitaryPSUEquiv h (n := 3) (by norm_num) with hψ
    set e : (K ⧸ Subgroup.center K) ≃* unitaryPSU h 3 := θ.trans ψ.symm with he
    refine localDeltaIn_eq_bot_of_transport hperf e hD hH (psuConj h).range hα ?_ ?_
    · intro hmem
      apply hα'
      right
      obtain ⟨A, hA⟩ := hmem
      refine ⟨F, inferInstance, inferInstance, p ^ f, θ,
        MulAut.congr ψ (MulAut.congr e (autCenterQuot K α)), hFq, ?_, ?_⟩
      · refine isConjByGL_of_congr_eq_psuConj h _ A ?_
        have hcancel : MulAut.congr ψ.symm (MulAut.congr ψ
            (MulAut.congr e (autCenterQuot K α))) = MulAut.congr e (autCenterQuot K α) := by
          ext w
          simp [MulAut.congr_apply]
        exact hcancel.trans hA.symm
      · intro y
        have h1 := congr_autCenterQuot_compat e α y
        have h2 : MulAut.congr e (autCenterQuot K α) (ψ.symm (θ (QuotientGroup.mk y))) =
            ψ.symm (θ (QuotientGroup.mk (α y))) := h1.symm
        have key := congr_apply_apply ψ (MulAut.congr e (autCenterQuot K α))
          (ψ.symm (θ (QuotientGroup.mk y)))
        erw [MulEquiv.apply_symm_apply] at key
        exact ((MulEquiv.apply_symm_apply ψ _).symm.trans (congrArg ψ h2.symm)).trans key.symm
    · intro D' H' hD' hc hH' hnot
      exact localDeltaIn_eq_bot_of_not_le_psuConj h hq hD' hc hnot hH'

end CFSG.HardMathSupport.Solomon.Coordinator
