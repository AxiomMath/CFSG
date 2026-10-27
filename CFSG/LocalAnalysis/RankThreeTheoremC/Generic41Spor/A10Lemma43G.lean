module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GEData
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GLayerLe
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GLayerY
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GTLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFBasic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFSwap
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GFusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10_YData_of_G (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hX : A10Facts) (hXe : A10Ext) (hL : A10L43Facts)
    (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore 5 J).subgroupOf J)
    (hQ : IsA10Type 5 Q) (hB : A10StageB P x J ψ) {U : Subgroup G} (hUP : IIPlane 5 P x J U)
    (hγ : A10PlaneShape J (u3T P x J) ψ U) :
    ∃ (d : G) (hd : d ∈ M) (t₁ t₂ : ↥M ⧸ primeComplementCore (G := ↥M) 5)
      (J₁ J₂ F : Subgroup (↥M ⧸ primeComplementCore (G := ↥M) 5)),
      d ∈ U ∧ d ∈ u3T P x J ∧
      QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨d, hd⟩ = t₁ * t₂ ∧
      ((u3T P x J).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)) =
        Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ ∧
      A10YData (↥M ⧸ primeComplementCore (G := ↥M) 5)
        (((P : Subgroup G).subgroupOf M).map (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5)))
        (QuotientGroup.mk' (primeComplementCore (G := ↥M) 5) ⟨x, hc.generic.2.1.1⟩) t₁ t₂ J₁ J₂ F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxM : x ∈ M := hc.generic.2.1.1
  have hx5 : x ^ 5 = 1 := hc.generic.2.1.2.2.1
  have hP : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) := hB.1
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  obtain ⟨S, hSyl⟩ := a10_T_sylow hc ψ hψ
  obtain ⟨Λ₁, Λ₂, hΛ⟩ := hL.gammaStruct Q hQ S
  obtain ⟨a₁, a₂, ha₁T, ha₂T, ho₁, ho₂, hdU, hT, hne, hz₁, hz₂, hfive⟩ :=
    a10_T_lines hX hc ψ hψ hker hQ hSyl hΛ hUP hγ
  have ha₁M : a₁ ∈ M := hPM (hTP ha₁T)
  have ha₂M : a₂ ∈ M := hPM (hTP ha₂T)
  obtain ⟨N, D, hE⟩ := a10_E_data hS hD1 hU0 hX hXe hc ψ hψ hker hQ hP hSyl hΛ
  obtain ⟨hc₁, hc₂, hne', hlay, hA₁, hA₂⟩ := a10_layer_abstract hE
  obtain ⟨hcY₁, hcY₂, hneY, hlayY, hAY₁, hAY₂⟩ := a10_layer_Y hxM hx5 hc₁ hc₂ hne' hlay hA₁ hA₂
  obtain ⟨hcat, hcore, hsyl, hrank, hPcomm, hxP, hxo⟩ := a10_Y_basic hS hX hc hP hxM
  obtain ⟨hto₁, hto₂, hxnot, htnot, hTbar⟩ :=
    a10_Y_points hX hc hP hxM ha₁M ha₂M ho₁ ho₂ hT hne
  obtain ⟨hFle, hFnorm, hFirr, hFfix⟩ := a10_F_basic hS hU0 hX hL hc ψ hψ hker hQ hP hSyl hxM
  obtain ⟨f, hfF, hf₁, hf₂⟩ := a10_F_swap hS hU0 hX hc ψ hψ hker hQ hSyl hΛ ha₁M ha₂M hz₁ hz₂
  have hfus := a10_fusion_Y hc ψ hB hxM ha₁M ha₂M hfive
  have haE : ∀ (a : G) (Λ : Subgroup Q), a ∈ Subgroup.zpowers a → orderOf a = 5 →
      a ∈ u3T P x J ⊓ a10Pre J ψ Λ → a ∈ a10E J ψ Λ := by
    intro a Λ _ ho ha
    exact Subgroup.subset_closure ⟨ha.2, 1, by rw [pow_one]; exact ho ▸ pow_orderOf_eq_one a⟩
  have ha₁E : a₁ ∈ a10E J ψ Λ₁ :=
    haE a₁ Λ₁ (Subgroup.mem_zpowers a₁) ho₁ (hz₁ ▸ Subgroup.mem_zpowers a₁)
  have ha₂E : a₂ ∈ a10E J ψ Λ₂ :=
    haE a₂ Λ₂ (Subgroup.mem_zpowers a₂) ho₂ (hz₂ ▸ Subgroup.mem_zpowers a₂)
  have hmem : ∀ (H : Subgroup G) (a : G) (ha : a ∈ M), a ∈ H → a10π M ⟨a, ha⟩ ∈ a10Img M H :=
    fun H a ha h => Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr h)
  refine ⟨a₁ * a₂, M.mul_mem ha₁M ha₂M, a10π M ⟨a₁, ha₁M⟩, a10π M ⟨a₂, ha₂M⟩,
    a10Img M (a10E J ψ Λ₁), a10Img M (a10E J ψ Λ₂),
    a10Img M (J ⊓ Subgroup.normalizer ((u3T P x J : Subgroup G) : Set G)), hdU,
    (u3T P x J).mul_mem ha₁T ha₂T, ?_, hTbar, ?_⟩
  · exact map_mul (a10π M) ⟨a₁, ha₁M⟩ ⟨a₂, ha₂M⟩
  · exact
    { catalog := hcat
      core := hcore
      sylow := hsyl
      rank := hrank
      P_comm := hPcomm
      x_mem := hxP
      x_ord := hxo
      t₁_mem := ⟨hmem _ a₁ ha₁M (hTP ha₁T), hmem _ a₁ ha₁M ha₁E⟩
      t₂_mem := ⟨hmem _ a₂ ha₂M (hTP ha₂T), hmem _ a₂ ha₂M ha₂E⟩
      t₁_ord := hto₁
      t₂_ord := hto₂
      x_not_mem := hxnot
      t₁_not_mem := htnot
      comp₁ := hcY₁
      comp₂ := hcY₂
      ne := hneY
      layer := hlayY
      A5₁ := hAY₁
      A5₂ := hAY₂
      F_le := hFle
      F_norm := by rw [← hTbar] at *; exact hFnorm
      F_irr := by rw [← hTbar] at *; exact hFirr
      F_fix := by rw [← hTbar] at *; exact hFfix
      F_swap := ⟨f, hfF, hf₁, hf₂⟩
      fusion := hfus }

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
