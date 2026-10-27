module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFixInf

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem map_iInf_fixSubgroup_normalizerConjAutOfMem {Y : Type} [Group Y] {K B : Subgroup Y}
    (hBN : B ≤ Subgroup.normalizer (K : Set Y)) (F' : Subgroup ↥B) :
    (⨅ b : ↥F', fixSubgroup (normalizerConjAutOfMem K B hBN (b : ↥B))).map K.subtype =
      K ⊓ Subgroup.centralizer ((F'.map B.subtype : Subgroup Y) : Set Y) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_inf.2 ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    have hfix : normalizerConjAutOfMem K B hBN b k = k := Subgroup.mem_iInf.1 hk ⟨b, hb⟩
    have h1 : (b : Y) * (k : Y) * (b : Y)⁻¹ = (k : Y) := by
      have := congrArg (fun w : ↥K => (w : Y)) hfix
      simpa [normalizerConjAutOfMem, Subgroup.normalizerMonoidHom_apply_apply_coe] using this
    calc (b : Y) * (k : Y) = ((b : Y) * (k : Y) * (b : Y)⁻¹) * (b : Y) := by group
      _ = (k : Y) * (b : Y) := by rw [h1]
  · intro x hx
    obtain ⟨hxK, hxC⟩ := Subgroup.mem_inf.1 hx
    refine Subgroup.mem_map.2 ⟨⟨x, hxK⟩, ?_, rfl⟩
    refine Subgroup.mem_iInf.2 fun b => ?_
    have hb : ((b : ↥B) : Y) ∈ (F'.map B.subtype : Subgroup Y) :=
      Subgroup.mem_map.2 ⟨(b : ↥B), b.2, rfl⟩
    have hcomm : ∀ z ∈ (F'.map B.subtype : Subgroup Y), z * x = x * z :=
      Subgroup.mem_centralizer_iff.1 hxC
    have h1 : ((b : ↥B) : Y) * x = x * ((b : ↥B) : Y) := hcomm _ hb
    apply Subtype.ext
    simp only [normalizerConjAutOfMem, MulEquiv.coe_toMonoidHom,
      Subgroup.normalizerMonoidHom_apply_apply_coe, MonoidHom.id_apply, Subgroup.coe_mk]
    show ((b : ↥B) : Y) * x * ((b : ↥B) : Y)⁻¹ = x
    rw [h1]; group

theorem kd264LiftGood_holds {p : ℕ} (hp : p.Prime) : KD264LiftGood p := by
  intro Y _ _ K B hBN S _ _ eK F hFr hgood
  set ρ : ↥B →* MulAut S := kd264Rho hBN eK with hρ
  set F' : Subgroup ↥B := F.comap ρ with hF'
  set π : ↥K →* S := eK.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)) with hπ
  have hπsurj : Function.Surjective π := by
    rw [hπ]
    exact eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker ≤ Subgroup.center ↥K := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ eK.injective,
      show (QuotientGroup.mk' (Subgroup.center ↥K)).ker = Subgroup.center ↥K from
        QuotientGroup.ker_mk' _]
  have hαβ : ∀ (b : ↥F') (k : ↥K),
      π (normalizerConjAutOfMem K B hBN (b : ↥B) k) = ρ (b : ↥B) (π k) := by
    intro b k
    simp only [hπ, hρ, kd264Rho, MonoidHom.comp_apply, MulAut.congr_apply,
      normalizerConjAutOfMem_comp_mk, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulEquiv.coe_toMonoidHom]
  have hβeq : (⨅ b : ↥F', fixSubgroup (ρ (b : ↥B))) = ⨅ f ∈ F, fixSubgroup f := by
    rw [hF']
    exact iInf_fixSubgroup_comap ρ hFr
  have hLne : GLAPLayer p (⨅ b : ↥F', fixSubgroup
      (normalizerConjAutOfMem K B hBN (b : ↥B))) ≠ ⊥ := by
    intro hbot
    refine hgood ?_
    rw [← hβeq, ← map_glaPLayer_iInf_fixSubgroup_eq π hπker
      (fun b : ↥F' => normalizerConjAutOfMem K B hBN (b : ↥B))
      (fun b : ↥F' => ρ (b : ↥B)) hαβ hπsurj hp, hbot, Subgroup.map_bot]
  intro hbot
  refine hLne ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 ?_)
  rw [glaPLayer_map_eq_of_injective hp K.subtype K.subtype_injective,
    map_iInf_fixSubgroup_normalizerConjAutOfMem hBN F']
  exact hbot

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
