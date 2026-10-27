module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuFiveModelA
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.EvenSporadicStandard.RuStd

theorem HasKlein.mono {G : Type*} [Group G] {S T : Set G} (h : HasKlein S) (hST : S ⊆ T) :
    HasKlein T := by
  obtain ⟨a, ha, b, hb, h1, h2, h3, h4⟩ := h
  exact ⟨a, hST ha, b, hST hb, h1, h2, h3, h4⟩

namespace FiveData

variable {G : Type} [Group G] [Finite G] (d : FiveData G)

include d

theorem exp5 (g : G) (hg : IsPGroup 5 (zpowers g)) : g ^ 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_sylow d.Q hg
  have h := d.Q_exp _ (hc g (mem_zpowers g))
  rw [conj_pow] at h
  calc g ^ 5 = c⁻¹ * (c * g ^ 5 * c⁻¹) * c := by group
    _ = 1 := by rw [h]; group

theorem typeAB (f : G) (hf : orderOf f = 5) :
    (Nat.card (centralizer ({f} : Set G)) = 300 ∧
        HasKlein ((centralizer ({f} : Set G) : Subgroup G) : Set G)) ∨
      (Nat.card (centralizer ({f} : Set G)) = 1000 ∧
        ¬ HasKlein ((centralizer ({f} : Set G) : Subgroup G) : Set G)) := by
  rcases d.exists_conj hf with ⟨c, hz⟩ | ⟨c, hz⟩
  · right
    refine ⟨by rw [card_centralizer_eq hz, d.card_C₀], ?_⟩
    rw [hasKlein_centralizer_iff hz]
    obtain ⟨ρ, hρ⟩ := d.exists_hom₀
    exact not_hasKlein_of_hom _ ρ hρ
  · left
    refine ⟨by rw [card_centralizer_eq hz, d.card_C₁], ?_⟩
    rw [hasKlein_centralizer_iff hz]
    have := d.D_simple
    obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
      (G := d.D) d.card_D
    exact (hasKlein_of_equiv_alt5 d.D e).mono d.D_le

theorem typeA (f : G) (hf : orderOf f = 5) (hc : Nat.card (centralizer ({f} : Set G)) = 300) :
    ∃ D : Subgroup G, Nonempty (↥D ≃* A5) ∧ D ≤ centralizer ({f} : Set G) ∧
      centralizer ({f} : Set G) = zpowers f ⊔ D ∧ Disjoint (zpowers f) D := by
  rcases d.exists_conj hf with ⟨c, hz⟩ | ⟨c, hz⟩
  · exfalso
    rw [card_centralizer_eq hz, d.card_C₀] at hc
    omega
  · set φ : G →* G := (MulAut.conj c).toMonoidHom with hφ
    have hinj : Function.Injective φ := (MulAut.conj c).injective
    have hC : centralizer ({f} : Set G) = (centralizer ({d.x₁} : Set G)).map φ :=
      centralizer_eq_map hz
    have hzφ : (zpowers d.x₁).map φ = zpowers f := by
      rw [MonoidHom.map_zpowers, ← hz]
      rfl
    refine ⟨d.D.map φ, ?_, ?_, ?_, ?_⟩
    · have := d.D_simple
      obtain ⟨e⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
        (G := d.D) d.card_D
      exact ⟨(Subgroup.equivMapOfInjective d.D φ hinj).symm.trans e⟩
    · rw [hC]
      exact Subgroup.map_mono d.D_le
    · rw [hC, d.centralizer_x₁_eq, Subgroup.map_sup, hzφ]
    · rw [← hzφ, disjoint_iff, ← Subgroup.map_inf _ _ _ hinj, disjoint_iff.1 d.disjoint_x₁_D,
        Subgroup.map_bot]

theorem conjA (f g : G) (hf : orderOf f = 5) (hg : orderOf g = 5)
    (hcf : Nat.card (centralizer ({f} : Set G)) = 300)
    (hcg : Nat.card (centralizer ({g} : Set G)) = 300) :
    ∃ c : G, ∃ k : ℕ, c * f * c⁻¹ = g ^ k := by
  have h1 : ∀ f : G, orderOf f = 5 → Nat.card (centralizer ({f} : Set G)) = 300 →
      ∃ c : G, zpowers (c * d.x₁ * c⁻¹) = zpowers f := by
    intro f hf hcf
    rcases d.exists_conj hf with ⟨c, hz⟩ | ⟨c, hz⟩
    · exfalso
      rw [card_centralizer_eq hz, d.card_C₀] at hcf
      omega
    · exact ⟨c, hz⟩
  obtain ⟨c, hc⟩ := h1 f hf hcf
  obtain ⟨e, he⟩ := h1 g hg hcg
  have hfm : f ∈ zpowers (c * d.x₁ * c⁻¹) := hc ▸ mem_zpowers f
  obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hfm
  have hmem : (e * c⁻¹) * f * (e * c⁻¹)⁻¹ ∈ zpowers g := by
    rw [← he]
    have : (e * c⁻¹) * f * (e * c⁻¹)⁻¹ = (e * d.x₁ * e⁻¹) ^ m := by
      calc (e * c⁻¹) * f * (e * c⁻¹)⁻¹ = (e * c⁻¹) * (c * d.x₁ * c⁻¹) ^ m * (e * c⁻¹)⁻¹ := by
            rw [hm]
        _ = e * d.x₁ ^ m * e⁻¹ := by rw [conj_zpow]; group
        _ = (e * d.x₁ * e⁻¹) ^ m := conj_zpow.symm
    rw [this]
    exact zpow_mem (mem_zpowers _) m
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
  exact ⟨e * c⁻¹, k, hk.symm⟩

theorem typeB (f : G) (hf : orderOf f = 5) (hc : Nat.card (centralizer ({f} : Set G)) = 1000) :
    ∃ φ : (↥(centralizer ({f} : Set G)) ⧸ CFSG.pCore 5 ↥(centralizer ({f} : Set G))) →* Q8,
      Function.Injective φ := by
  rcases d.exists_conj hf with ⟨c, hz⟩ | ⟨c, hz⟩
  · obtain ⟨ρ, hρ⟩ := d.exists_hom₀
    have hC := centralizer_eq_map hz
    let ε : ↥(centralizer ({f} : Set G)) ≃* ↥(centralizer ({d.x₀} : Set G)) :=
      (MulEquiv.subgroupCongr hC).trans (Subgroup.equivMapOfInjective _
        (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).symm
    refine exists_inj_of_hom (ρ.comp ε.toMonoidHom) ?_
    rw [← MonoidHom.comap_ker]
    exact hρ.comap_of_injective _ ε.injective
  · exfalso
    rw [card_centralizer_eq hz, d.card_C₁] at hc
    omega

end FiveData

end CFSG.EvenSporadicStandard.RuStd.S2
