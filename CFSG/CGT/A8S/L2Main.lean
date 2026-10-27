module

public import CFSG.CGT.A8S.L2Model
public import CFSG.CGT.A8S.L2GTheta

public section

namespace CFSG.CGT.A8S

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM CFSG.CosetTable

namespace L2

theorem evalA8_genTupleA8_liftW5 {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G)
    (w : List (Fin 5 × Bool)) :
    evalA8 (genTupleA8 ψ g) (liftW5 w) =
      ((ψ (PresentedGroup.mk _ (FreeGroup.mk w)) : ↥(Subgroup.normalizer (T : Set G))) : G) := by
  rw [evalA8_liftW5]
  have hhom : (FreeGroup.lift fun j : Fin 5 => genTupleA8 ψ g (Fin.castSucc j)) =
      (Subgroup.normalizer (T : Set G)).subtype.comp
        (ψ.toMonoidHom.comp (PresentedGroup.mk {r : FreeGroup (Fin 5) |
          r ∈ relsN0A8.map FreeGroup.mk})) := by
    apply FreeGroup.ext_hom
    intro j
    simp [genTupleA8]
    rfl
  rw [hhom]
  rfl

theorem genTupleA8_five {G : Type} [Group G] {T : Subgroup G}
    (ψ : PG 5 relsN0A8 ≃* ↥(Subgroup.normalizer (T : Set G))) (g : G) :
    genTupleA8 ψ g 5 = g := by
  simp [genTupleA8]

theorem mem_thetaRelsA8 {r : A8Word} (hr : r ∈ thetaRelsA8) :
    r = [(5, true), (5, true)] ∨
      ∃ i : Fin 2, r = (5, true) :: (dWordA8 i ++ (5, true) :: invA8 (thetaWordA8 i)) := by
  simp only [thetaRelsA8, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨1, rfl⟩

end L2

open L2

theorem l2StatementA8_of_n0 (hN0 : N0StatementA8) :
    L2StatementA8 := by
  intro G _ _ T T₁ hyp
  obtain ⟨ψ, hψ⟩ := hN0 G T T₁ hyp
  have hctx : TCtx T T₁ := ⟨hyp.wc, hyp.inf_bot, hyp.conj, hyp.norm1, hyp.norm2⟩
  have h8 : Nat.card T₁ = 8 := by
    obtain ⟨s, hs⟩ := hyp.conj
    rw [hs, ← hyp.card8]
    exact Subgroup.card_map_of_injective (MulAut.conj s).injective
  have hfin : Finite (PG 5 relsN0A8) := finite_pg_relsN0A8
  let M := l2ModelA8
  let E : OntoEmb (PG 5 relsN0A8) (Subgroup.normalizer (T : Set G)) := OntoEmb.ofEquiv ψ
  have hE : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T := by
    intro x
    have h1 : x ∈ Subgroup.closure (Set.range tGenA8) ↔
        ψ x ∈ Subgroup.map ψ.toMonoidHom (Subgroup.closure (Set.range tGenA8)) := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hψ, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨E', g, hT', hgT, hgg, hrel⟩ := exists_configA8 hctx h8 M E hE
  refine ⟨⟨E'.toEquiv, ?_, g, hgT, ?_⟩⟩
  · ext y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    have h3 : E'.Φ (E'.toEquiv.symm y) = (y : G) := by
      rw [← OntoEmb.toEquiv_apply_coe, MulEquiv.apply_symm_apply]
    have := hT' (E'.toEquiv.symm y)
    rw [h3] at this
    exact this
  · intro r hr
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    rcases mem_thetaRelsA8 hr with rfl | ⟨i, rfl⟩
    · rw [evalA8_cons_true, evalA8_cons_true, evalA8_nil, genTupleA8_five, mul_one, hgg]
    · rw [evalA8_cons_true, evalA8_append, evalA8_cons_true, evalA8_invA8, genTupleA8_five,
        ← liftW5_dW5, ← liftW5_thW5, evalA8_genTupleA8_liftW5, evalA8_genTupleA8_liftW5,
        OntoEmb.toEquiv_apply_coe, OntoEmb.toEquiv_apply_coe]
      have h1 : g * E'.Φ (PresentedGroup.mk _ (FreeGroup.mk (dW5 i))) * g =
          E'.Φ (PresentedGroup.mk _ (FreeGroup.mk (thW5 i))) := by
        have := hrel i
        rw [hginv] at this
        exact this
      rw [← mul_assoc, ← mul_assoc, h1, mul_inv_cancel]

end CFSG.CGT.A8S
