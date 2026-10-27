module

public import CFSG.Open.RankThreeDefs
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem rankThreeLayer_le (H : Subgroup G) : rankThreeLayer H ≤ H :=
  sSup_le fun _ hL => hL.1

private theorem isSubnormal_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {H K : Subgroup A} (h : IsSubnormal H K) :
    IsSubnormal (H.map e.toMonoidHom) (K.map e.toMonoidHom) :=
  h.map e.toMonoidHom

private theorem isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsQuasisimple A) : IsQuasisimple B := by
  obtain ⟨hperf, hsimple⟩ := h
  refine ⟨?_, ?_⟩
  · rw [_root_.commutator_def] at hperf ⊢
    rw [← Subgroup.map_top_of_surjective (e : A →* B) e.surjective, ← Subgroup.map_commutator,
      hperf]
  · exact (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
      (Subgroup.map_center_eq e)).isSimpleGroup_congr.mp hsimple

theorem IsComponentOf.map_conj {L H : Subgroup G} (hL : IsComponentOf L H) {h : G} (hh : h ∈ H) :
    IsComponentOf (L.map (MulAut.conj h).toMonoidHom) H := by
  have hH : H.map (MulAut.conj h).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hh)
  obtain ⟨hLH, hsub, hqs⟩ := hL
  refine ⟨?_, ?_, ?_⟩
  · exact (Subgroup.map_mono hLH).trans hH.le
  · simpa only [hH] using isSubnormal_map_mulEquiv (MulAut.conj h) hsub
  · exact isQuasisimple_of_mulEquiv (L.equivMapOfInjective _ (MulAut.conj h).injective) hqs

private theorem map_conj_rankThreeLayer_le (H : Subgroup G) {h : G} (hh : h ∈ H) :
    (rankThreeLayer H).map (MulAut.conj h).toMonoidHom ≤ rankThreeLayer H := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L hL => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (IsComponentOf.map_conj hL hh)

theorem le_normalizer_rankThreeLayer (H : Subgroup G) :
    H ≤ normalizer ((rankThreeLayer H : Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, ∀ x ∈ rankThreeLayer H, g * x * g⁻¹ ∈ rankThreeLayer H :=
    fun g hg x hx => map_conj_rankThreeLayer_le H hg ⟨x, hx, by simp⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  refine fun x => ⟨key h hh x, fun hx => ?_⟩
  simpa [mul_assoc] using key h⁻¹ (H.inv_mem hh) _ hx

end CFSG.LocalAnalysis.RankThreeTheoremC
