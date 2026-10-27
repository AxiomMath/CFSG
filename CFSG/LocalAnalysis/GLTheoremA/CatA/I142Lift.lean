module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] noncomputable def Cbar (p : ℕ) (K E : Subgroup G) : Subgroup (PQuot p K) :=
  ((K ⊓ Subgroup.centralizer (E : Set G)).subgroupOf K).map (pQuotHom p K)

theorem barAut_fixed_of_mem_Cbar {p : ℕ} {K E : Subgroup G}
    {x : PQuot p K} (hx : x ∈ Cbar p K E) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (hγ : (γ : G) ∈ E) : barAut p K γ x = x := by
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
  rw [barAut_pQuotHom]
  congr 1
  apply Subtype.ext
  rw [chev_coe_normalizerMonoidHom]
  have hcC : (c : G) ∈ K ⊓ Subgroup.centralizer (E : Set G) := (Subgroup.mem_subgroupOf).1 hc
  have hcomm : (γ : G) * (c : G) = (c : G) * (γ : G) :=
    (Subgroup.mem_centralizer_iff.1 hcC.2) (γ : G) hγ
  rw [hcomm]
  group

theorem mem_Cbar_of_fixed [Finite G] {p : ℕ} [hp : Fact p.Prime] {K E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (K : Set G)) (hE : IsElemAbelian p E)
    {x : PQuot p K} (hx : ∀ γ ∈ E.subgroupOf (Subgroup.normalizer (K : Set G)),
      barAut p K γ x = x) : x ∈ Cbar p K E := by
  obtain ⟨k, rfl⟩ := pQuotHom_surjective p K x
  have hfix : ∀ d ∈ E, (k : G)⁻¹ * ((d : G)⁻¹ * (k : G) * (d : G)) ∈ GLAPPrimeCoreOf p K := by
    intro d hd
    have hd' : d⁻¹ ∈ E := E.inv_mem hd
    have hdN : d⁻¹ ∈ Subgroup.normalizer (K : Set G) := hEN hd'
    have hγ : (⟨d⁻¹, hdN⟩ : ↥(Subgroup.normalizer (K : Set G))) ∈
        E.subgroupOf (Subgroup.normalizer (K : Set G)) := Subgroup.mem_subgroupOf.2 hd'
    have h1 := hx _ hγ
    rw [barAut_pQuotHom] at h1
    have h2 := (pQuot_mk_eq_mk_iff (p := p) k (K.normalizerMonoidHom ⟨d⁻¹, hdN⟩ k)).1 h1.symm
    rw [chev_coe_normalizerMonoidHom] at h2
    simpa [mul_assoc] using h2
  obtain ⟨c, hc, m, hm, hkcm⟩ := CFSG.LocalAnalysis.GLTheoremA.S10.mem_centralizer_mul_of_coprime
    (D := E) (H := K)
    (M := GLAPPrimeCoreOf p K) (isPGroup_of_isElemAbelian hE)
    (coprime_card_glaPPrimeCoreOf p K).symm (Subgroup.map_subtype_le _)
    (normal_glaPPrimeCoreOf_subgroupOf p K) hEN
    (fun d hd => normalizer_le_normalizer_glaPPrimeCoreOf p K (hEN hd))
    k.2 (fun d hd => hfix d hd)
  have hcK : c ∈ K := hc.1
  refine Subgroup.mem_map.2 ⟨⟨c, hcK⟩, Subgroup.mem_subgroupOf.2 hc, ?_⟩
  show (QuotientGroup.mk (⟨c, hcK⟩ : ↥K) : PQuot p K) = QuotientGroup.mk k
  rw [pQuot_mk_eq_mk_iff]
  show ((⟨c, hcK⟩ : ↥K) : G)⁻¹ * (k : G) ∈ GLAPPrimeCoreOf p K
  rw [hkcm]
  simpa using hm

end CFSG.LocalAnalysis.GLTheoremA.I142
