module

public import CFSG.Assembly.OddCoreEliminationStatements
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.Assembly.Dichotomy

variable {G : Type} [Group G]

private theorem le_centralizer_of_isElemAbelian {p : ℕ} {V : Subgroup G}
    (hV : IsElemAbelian p V) : V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val (hV.1.is_comm.comm (⟨w, hw⟩ : V) ⟨v, hv⟩)

private theorem map_conj_eq_of_forall {V : Subgroup G} {g m : G}
    (hm : ∀ x ∈ V, g⁻¹ * x * g = m⁻¹ * x * m) :
    V.map (MulAut.conj m⁻¹).toMonoidHom = V.map (MulAut.conj g⁻¹).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hm x hx)⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hm x hx).symm⟩

theorem fourSpanEqualization_of_nonisolated (hnon : NonisolatedConjugateStatement) :
    FourSpanEqualizationStatement := by
  intro G _ _ hperf hrank S W hSW hV hfus V hVS hVe hV4
  by_cases h3 : 3 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G))
  · exact hV V hVS hVe hV4 h3
  have h2 : 2 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (V : Set G)) :=
    CFSG.SectionRank.le_pRank (p := 2) one_lt_two
      (le_inf hVS (le_centralizer_of_isElemAbelian hVe)) hVe (by rw [hV4]; norm_num)
  obtain ⟨g, hgS, hg3⟩ := hnon G hperf hrank S V hVS hVe hV4 (by omega)
  have hVge : IsElemAbelian 2 (V.map (MulAut.conj g⁻¹).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hVe _
  have hVg4 : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = 4 := by
    rw [Subgroup.card_map_of_injective (MulEquiv.injective _), hV4]
  have hWg := hV _ hgS hVge hVg4 hg3
  have hVp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x.1 x.2)⟩
  obtain ⟨m, hmW, hm⟩ := hfus V hVS hVp g hgS
  have hm' : m⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hmW
  have hWm : W.map (MulAut.conj m⁻¹).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hm'
  apply Subgroup.map_injective (f := (MulAut.conj m⁻¹).toMonoidHom) (MulEquiv.injective _)
  rw [hWm, ← oddCoreSpan_conj, map_conj_eq_of_forall hm, hWg]

end CFSG.Assembly.Dichotomy
