module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent
public import CFSG.Quasithin.Background.SmithCurtisChevAmb

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev


variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K} {q : ℕ}

theorem permLattice_mem_nonInversionSet {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ nonInversionSet w) :
    permLattice t.perm α ∈ nonInversionSet w := by
  obtain ⟨hr, hp, hq⟩ := hα
  refine ⟨hr.permLattice t.cartan_perm, by rwa [height_permLattice], ?_⟩
  rw [(mem_relWeylTwist_iff_smul t).1 hw α, height_permLattice]
  exact hq

theorem heckeDeg_graphFixedPosUnipotent [Finite K] (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    heckeDeg (graphFixedPosUnipotent t K σ) (canonicalRep (coxeterSystem t.tag) K w) =
      q ^ (coxeterSystem t.tag).length w := by
  set n := canonicalRep (coxeterSystem t.tag) K w with hn_def
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  set U := graphFixedPosUnipotent t K σ with hU_def
  have hinf : U.map (MulAut.conj n).toMonoidHom ⊓ U =
      (rootSpan t.tag K (nonInversionSet w) ⊓ twistedFixedGroup t K σ).map
        (MulAut.conj n).toMonoidHom := by
    apply le_antisymm
    · rintro x ⟨⟨u, hu, rfl⟩, hxU⟩
      have h1 : n * u * n⁻¹ ∈ (posUnipotent t.tag K).map (MulAut.conj n).toMonoidHom ⊓
          posUnipotent t.tag K :=
        Subgroup.mem_inf.2 ⟨⟨u, (Subgroup.mem_inf.1 hu).1, rfl⟩, (Subgroup.mem_inf.1 hxU).1⟩
      rw [map_conj_posUnipotent_inf w] at h1
      obtain ⟨y, hy, hyu⟩ := h1
      have hyu' : n * y * n⁻¹ = n * u * n⁻¹ := hyu
      have e : y = u := by rwa [mul_left_inj, mul_right_inj] at hyu'
      exact ⟨u, Subgroup.mem_inf.2 ⟨e ▸ hy, (Subgroup.mem_inf.1 hu).2⟩, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
      refine ⟨⟨u, Subgroup.mem_inf.2 ⟨rootSpan_le_posUnipotent
        (fun α h => nonInversionSet_pos h) hu1, hu2⟩, rfl⟩, Subgroup.mem_inf.2
        ⟨canonicalRep_conj_mem_posUnipotent hu1, mul_mem (mul_mem hn hu2) (inv_mem hn)⟩⟩
  have h := Subgroup.relIndex_mul_card (U.map (MulAut.conj n).toMonoidHom) U
  have hJ := card_rootSpan_inf_twistedFixedGroup hσ hq (S := nonInversionSet w)
    (fun α h => nonInversionSet_pos h)
    (fun α h => permLattice_mem_nonInversionSet hw h) (nonInversionSet_closed w)
  have hpos : 0 < Nat.card ↥(rootSpan t.tag K (nonInversionSet w) ⊓ twistedFixedGroup t K σ) :=
    Nat.card_pos
  rw [hinf, Subgroup.card_map_of_injective (MulAut.conj n).injective, hJ,
    hU_def, card_graphFixedPosUnipotent hσ hq, ← ncard_nonInversionSet_add w, pow_add] at h
  rw [hJ] at hpos
  rw [heckeDeg]
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
