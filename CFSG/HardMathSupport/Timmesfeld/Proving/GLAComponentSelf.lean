module

public import CFSG.Open.GLADefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

theorem isQuasisimple_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : IsQuasisimple G) : IsQuasisimple H := by
  obtain ⟨hcomm, hsimp⟩ := hG
  refine ⟨?_, ?_⟩
  · have h1 := map_commutator_eq G (e : G →* H)
    have hr : (e : G →* H).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
    rw [hcomm, hr, ← _root_.commutator_def] at h1
    rw [← h1, ← MonoidHom.range_eq_map, hr]
  · have hc : (Subgroup.center G).map (e : G →* H) = Subgroup.center H :=
      Subgroup.map_center_eq e
    exact (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e hc).symm.isSimpleGroup

theorem mk'_injective_of_eq_bot {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : N = ⊥) : Function.Injective (QuotientGroup.mk' N) := by
  subst hN
  intro a b h
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  have h' : a⁻¹ * b = 1 := by simpa using h
  exact inv_mul_eq_one.mp h'

theorem map_mk'_eq_imp_eq {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (hN : N = ⊥)
    {J J' : Subgroup H} (h : J.map (QuotientGroup.mk' N) = J'.map (QuotientGroup.mk' N)) :
    J = J' :=
  Subgroup.map_injective (mk'_injective_of_eq_bot N hN) h

theorem isQuasisimple_top_quot {H : Type*} [Group H] (N : Subgroup H) [N.Normal] (hN : N = ⊥)
    (hH : IsQuasisimple H) : IsQuasisimple ↥(⊤ : Subgroup (H ⧸ N)) := by
  subst hN
  exact isQuasisimple_of_mulEquiv' ((Subgroup.topEquiv).trans (QuotientGroup.quotientBot)).symm hH

theorem glaPComponent_self {X : Type*} [Group X] {p : ℕ} {K : Subgroup X}
    (hK : IsQuasisimple ↥K) (hcore : GLAPPrimeCore p ↥K = ⊥) : GLAPComponent p K K := by
  refine ⟨le_rfl, IsSubnormal.refl K, ?_, ?_⟩
  · have hsurj : (K.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore p ↥K)) = ⊤ := by
      rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    rw [hsurj]
    exact ⟨le_rfl, IsSubnormal.refl _, isQuasisimple_top_quot _ hcore hK⟩
  · intro J hJ _ heq
    rw [Subgroup.subgroupOf_self] at heq
    have hJK : J.subgroupOf K = ⊤ := map_mk'_eq_imp_eq _ hcore heq
    exact (lt_iff_le_not_ge.mp hJ).2 (Subgroup.subgroupOf_eq_top.mp hJK)

end CFSG.HardMathSupport.Timmesfeld.Proving
