module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSSpecial
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerFusion

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem hsInnerFusion_at
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hL : IsSporadic L .HS) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) {S : Subgroup G} {z n : G}
    (hf : HSFusionData L t S z n) :
    ∃ E : Subgroup G, E ≤ L ∧ z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
      (∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e) ∧
      ∀ e ∈ E, ∃ m ∈ normalizer ((zpowers t ⊔ E : Subgroup G) : Set G), m * t * m⁻¹ = t * e := by
  have hnz := fusionData_conj_z hf hL htL ht2 hin
  have hzt := fusionData_conj_ne_z hf hL htL ht2 hin
  have hLC := inf_centralizer_eq_bot_hs hL
  have hSL := fusionData_relIndex_odd hf hL htL ht2 hin
  have hzSL : z ∈ S ⊓ L := ⟨hf.zS, hf.zL⟩
  obtain ⟨D⟩ := innerData_of_sylow hL hf.pgroup hSL hzSL hf.z2 hf.zc
  obtain ⟨m, hm, hmt⟩ := exists_fusing_of_innerData htL ht2 hin hLC hf.zL hnz hf.nt hzt D
  obtain ⟨E₀, hE₀L, hzE₀, hab₀, hcard₀, hφ, htrans₀⟩ :=
    exists_special_of_sylow hL hf.pgroup hSL hzSL hf.z2 hf.zc
  set E_D : Subgroup G := closure (Set.range fun j => wordEval D.g₁ D.a (D.eW j)) with hED
  have hEDL : E_D ≤ L := by
    rw [hED, closure_le]
    rintro _ ⟨j, rfl⟩
    exact wordEval_mem D.g₁_mem.1 D.a_mem.1 _
  obtain ⟨c, hc, hcE⟩ := special_unique_of_sylow hL hf.pgroup hSL hzSL hf.z2 hf.zc hEDL hE₀L
    D.E_elemAbelian hab₀ D.E_card hcard₀ D.z_mem_E hzE₀ D.E_conj
    (fun e he he1 => let ⟨a, ha, h⟩ := htrans₀ e he he1; ⟨a, ha.2, h⟩)
  refine ⟨E₀, hE₀L, hzE₀, hab₀, hcard₀, hφ, htrans₀, ?_⟩
  have hcct : c * t = t * c := mem_centralizer_iff.1 htL c hc.1
  have hccz : c * z = z * c := mem_centralizer_singleton_iff.1 hc.2
  have hct : ∀ l ∈ L, l * t = t * l := fun l hl => mem_centralizer_iff.1 htL l hl
  have hm' : c * m * c⁻¹ ∈ normalizer ((zpowers t ⊔ E₀ : Subgroup G) : Set G) := by
    have h1 := conj_mem_normalizer_map hm c
    have h2 : (zpowers t ⊔ E_D : Subgroup G).map (MulAut.conj c : G →* G) = zpowers t ⊔ E₀ := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, hcE]
      have : (MulAut.conj c : G →* G) t = t := by
        show c * t * c⁻¹ = t
        rw [hcct]
        group
      rw [this]
    rwa [h2] at h1
  have hmt' : (c * m * c⁻¹) * t * (c * m * c⁻¹)⁻¹ = z * t := by
    have hcti : c⁻¹ * t * c = t := by
      calc c⁻¹ * t * c = c⁻¹ * (t * c) * 1 := by group
        _ = c⁻¹ * (c * t) := by rw [hcct]; group
        _ = t := by group
    calc (c * m * c⁻¹) * t * (c * m * c⁻¹)⁻¹ = c * (m * (c⁻¹ * t * c) * m⁻¹) * c⁻¹ := by group
      _ = c * (z * t) * c⁻¹ := by rw [hcti, hmt]
      _ = (c * z) * t * c⁻¹ := by rw [mul_assoc c z t]
      _ = z * (c * t) * c⁻¹ := by rw [hccz]; group
      _ = z * t := by rw [hcct]; group
  exact forall_conj_mul_of_conj_mul hct hE₀L htrans₀ hm' hmt'

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
