module

import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarProj
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarTwoA
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneLiePerfect
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCover
import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.perfect_le_component (hAut : KFactCycAut) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier) (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) {W : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hWX : W ≤ d1X0 p M H) (hWp : ⁅W, W⁆ = W) : W ≤ L₂ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hred := hd.cfg.red
  have hout : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      L ≠ L₂ → ¬ L ≤ d1X0 p M H := by
    intro L hL hne hLX
    obtain ⟨L', hL', hL'X⟩ := hd.exists_not_le hAut
    have h1 : L' ≠ L := fun h => hL'X (h ▸ hLX)
    have h2 : L' ≠ L₂ := fun h => hL'X (h ▸ hL₂X)
    exact hred.false_of_three_components hL' hL hL₂ h1 h2 hne
  have hWC : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      L ≠ L₂ → W ≤ Subgroup.centralizer (L : Set _) := by
    intro L hL hne
    have hLX := hout L hL hne
    obtain ⟨hsolv, hself⟩ := D1CaseTwoDataAt.inf_X0_facts hAut hS hKL hd hL hLX
    obtain ⟨hsimple, hnonab, hcat, -⟩ := hred.isSimpleGroup_of_isCyclic hd.cfg.catalog hL
      (hd.cyclic L hL)
    have hZ := hred.center_eq_bot_of_isCyclic hL (hd.cyclic L hL)
    have hWN : W ≤ Subgroup.normalizer (L : Set _) :=
      le_normalizer_of_perfect (fun L₁ L₂ L₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ =>
        hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) hWp hL
    have hWK : W ≤ L ⊔ Subgroup.centralizer (L : Set _) :=
      perfect_le_sup_centralizer_of_outer (hSch L hsimple hnonab hcat) hWp hWN
    obtain ⟨ρ, hρ⟩ := exists_proj hZ hWK
    have hρX : ∀ u : W, ρ u ∈ (d1X0 p M H).comap L.subtype := by
      intro u
      apply hself
      intro y hy
      set a : H ⧸ primeComplementCore (G := H) p := ((ρ u : L) : H ⧸ primeComplementCore (G := H) p)
        with ha
      set b : H ⧸ primeComplementCore (G := H) p := (u : H ⧸ primeComplementCore (G := H) p)
        with hb
      have hc : a⁻¹ * b ∈ Subgroup.centralizer (L : Set _) := hρ u
      have hconj : a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹ = b * y * b⁻¹ := by
        have h1 : (y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b) = (a⁻¹ * b) * y :=
          Subgroup.mem_centralizer_iff.mp hc (y : _) y.2
        calc a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹
            = a * ((y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b)) * b⁻¹ := by group
          _ = a * ((a⁻¹ * b) * y) * b⁻¹ := by rw [h1]
          _ = b * y * b⁻¹ := by group
      show ((ρ u * y * (ρ u)⁻¹ : L) : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← ha, hconj]
      exact (d1X0 p M H).mul_mem ((d1X0 p M H).mul_mem (hWX u.2) hy) ((d1X0 p M H).inv_mem
        (hWX u.2))
    have hρrange : ρ.range = ⊥ := by
      have hle : ρ.range ≤ (d1X0 p M H).comap L.subtype := by
        rintro _ ⟨u, rfl⟩
        exact hρX u
      have hsol : Group.IsSolvable ρ.range := Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective hle)
      have hper : ⁅ρ.range, ρ.range⁆ = ρ.range := by
        have h1 : ⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆ = ⊤ := by
          have : Group.IsPerfect W := Subgroup.isPerfect_iff.mpr hWp
          exact Group.IsPerfect.commutator_eq_top
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, h1]
      have : Group.IsPerfect ρ.range := Subgroup.isPerfect_iff.mpr hper
      obtain ⟨n, hn⟩ := hsol.solvable
      rw [Group.IsPerfect.derivedSeries_eq_top] at hn
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : ρ.range) ∈ (⊤ : Subgroup ρ.range) := Subgroup.mem_top _
      rw [hn, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h1)
    intro u hu
    have h1 : ρ ⟨u, hu⟩ = 1 := by
      have : ρ ⟨u, hu⟩ ∈ ρ.range := ⟨_, rfl⟩
      rw [hρrange, Subgroup.mem_bot] at this
      exact this
    have := hρ ⟨u, hu⟩
    rwa [h1, Subgroup.coe_one, inv_one, one_mul] at this
  obtain ⟨hsimple₂, hnonab₂, hcat₂, -⟩ := hred.isSimpleGroup_of_isCyclic hd.cfg.catalog hL₂
    (hd.cyclic L₂ hL₂)
  have hWN₂ : W ≤ Subgroup.normalizer (L₂ : Set _) :=
    le_normalizer_of_perfect (fun L₁ L₂ L₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ =>
      hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) hWp hL₂
  have hWK₂ : W ≤ L₂ ⊔ Subgroup.centralizer (L₂ : Set _) :=
    perfect_le_sup_centralizer_of_outer (hSch L₂ hsimple₂ hnonab₂ hcat₂) hWp hWN₂
  obtain ⟨K₀, hK₀⟩ := hd.cfg.exists_isComponentOf
  have hWO : W ≤ Subgroup.centralizer (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :
      Set _) := by
    have : (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p)).Normal := CFSG.pCore_normal
    exact le_centralizer_of_perfect_of_isCyclic (hred.isCyclic_pCore_of_component hK₀) hWp
  have hL₂O : L₂ ≤ Subgroup.centralizer (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :
      Set _) := by
    have hF : CFSG.fittingSubgroup (H ⧸ primeComplementCore (G := H) p) =
        CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) :=
      CFSG.Fitting_eq_pcore _ p hred.core_eq_bot
    have hKl : L₂ ≤ CFSG.layer (H ⧸ primeComplementCore (G := H) p) :=
      le_sSup (show L₂ ∈ {K : Subgroup (H ⧸ primeComplementCore (G := H) p) |
        CFSG.IsComponent K} from (CFSG.isComponent_iff_open L₂).mpr hL₂)
    have hc := CFSG.LocalCores.fitting_layer_commute (G := H ⧸ primeComplementCore (G := H) p)
    rw [hF] at hc
    exact hKl.trans (Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc))
  have hLN : L₂ ≤ Subgroup.normalizer (Subgroup.centralizer
      (L₂ : Set (H ⧸ primeComplementCore (G := H) p)) : Set (H ⧸ primeComplementCore (G := H) p)) :=
    fun l hl => mem_normalizer_centralizer (Subgroup.le_normalizer hl)
  have hdec : ∀ u ∈ W, ∃ l ∈ L₂, ∃ c, u = l * c ∧
      c ∈ Subgroup.centralizer (CFSG.pCore p (H ⧸ primeComplementCore (G := H) p) : Set _) ∧
      ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
        c ∈ Subgroup.centralizer (K : Set _) := by
    intro u hu
    have hu' := hWK₂ hu
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hu'
    obtain ⟨l, hl, c, hc, rfl⟩ := hu'
    refine ⟨l, hl, c, rfl, ?_, fun K hK => ?_⟩
    · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hL₂O hl)) (hWO hu)
      simpa using this
    · by_cases hKe : K = L₂
      · rw [hKe]; exact hc
      · have h1 : l ∈ Subgroup.centralizer (K : Set _) :=
          le_centralizer_of_component_ne hL₂ hK (Ne.symm hKe) hl
        have := Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) (hWC K hK hKe hu)
        simpa using this
  rw [← hWp, Subgroup.commutator_le]
  intro u hu v hv
  obtain ⟨l₁, hl₁, c₁, rfl, hc₁O, hc₁K⟩ := hdec u hu
  obtain ⟨l₂, hl₂, c₂, rfl, hc₂O, hc₂K⟩ := hdec v hv
  have h12 : Commute c₁ c₂ :=
    commute_of_mem_centralizer_fstar hred.core_eq_bot hc₁O hc₁K hc₂O hc₂K
  have hcl : ∀ (c : H ⧸ primeComplementCore (G := H) p), c ∈ Subgroup.centralizer (L₂ : Set _) →
      ∀ l ∈ L₂, Commute l c := fun c hc l hl => Subgroup.mem_centralizer_iff.mp hc l hl
  rw [commutatorElement_def]
  have a1 := hcl c₁ (hc₁K L₂ hL₂) l₂ hl₂
  have a2 := hcl c₂ (hc₂K L₂ hL₂) l₁ hl₁
  have e : l₁ * c₁ * (l₂ * c₂) * (l₁ * c₁)⁻¹ * (l₂ * c₂)⁻¹ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by
    calc l₁ * c₁ * (l₂ * c₂) * (l₁ * c₁)⁻¹ * (l₂ * c₂)⁻¹
        = l₁ * (c₁ * l₂) * c₂ * c₁⁻¹ * l₁⁻¹ * c₂⁻¹ * l₂⁻¹ := by group
      _ = l₁ * l₂ * (c₁ * c₂) * c₁⁻¹ * l₁⁻¹ * c₂⁻¹ * l₂⁻¹ := by rw [← a1.eq]; group
      _ = l₁ * l₂ * (c₂ * c₁) * c₁⁻¹ * l₁⁻¹ * c₂⁻¹ * l₂⁻¹ := by rw [h12.eq]
      _ = l₁ * l₂ * (c₂ * l₁⁻¹) * c₂⁻¹ * l₂⁻¹ := by group
      _ = l₁ * l₂ * (l₁⁻¹ * c₂) * c₂⁻¹ * l₂⁻¹ := by
          rw [show c₂ * l₁⁻¹ = l₁⁻¹ * c₂ from (a2.inv_left).eq.symm]
      _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by group
  rw [e]
  exact L₂.mul_mem (L₂.mul_mem (L₂.mul_mem hl₁ hl₂) (L₂.inv_mem hl₁)) (L₂.inv_mem hl₂)

theorem exists_perfect_cover_of_mem (hp : p.Prime)
    {L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL₂ : IsComponentOf L₂ ⊤)
    (hL₂X : L₂ ≤ d1X0 p M H) {z : G} (hzH : z ∈ H) (hzM : z ∈ M) (hzo : orderOf z = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩ ∈ L₂) :
    ∃ U : Subgroup G, U ≤ H ⊓ M ∧ ⁅U, U⁆ = U ∧ z ∈ U := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set Y : Subgroup G := (L₂.comap π).map H.subtype ⊓ M
  have hYHM : Y ≤ H ⊓ M := le_inf (inf_le_left.trans (Subgroup.map_subtype_le _)) inf_le_right
  have hYH : Y ≤ H := hYHM.trans inf_le_left
  set U := perfectCore Y
  have hUY : U ≤ Y := perfectCore_le Y
  refine ⟨U, hUY.trans hYHM, perfectCore_perfect Y, ?_⟩
  set ψ := π.comp (Subgroup.inclusion hYH)
  have hzY : z ∈ Y := ⟨⟨⟨z, hzH⟩, hzL, rfl⟩, hzM⟩
  have hrange : ψ.range = L₂ := by
    refine le_antisymm ?_ fun l hl => ?_
    · rintro _ ⟨⟨y, ⟨h, hh, rfl⟩, -⟩, rfl⟩
      have : Subgroup.inclusion hYH ⟨(h : G), ⟨h, hh, rfl⟩, ‹_›⟩ = h := Subtype.ext rfl
      simpa [ψ, this] using hh
    · obtain ⟨h, hh, rfl⟩ := hL₂X hl
      have hhM : (h : G) ∈ M := (Subgroup.mem_subgroupOf.mp hh).2
      refine ⟨⟨h, ⟨h, ?_, rfl⟩, hhM⟩, ?_⟩
      · exact hl
      · show π (Subgroup.inclusion hYH _) = π h
        congr 1
  have hW : (perfectCore (⊤ : Subgroup ↥Y)).map ψ = L₂ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hrange]
    exact perfectCore_eq_self_of_perfect (commutator_eq_self_of_component hL₂)
  have hWU : (perfectCore (⊤ : Subgroup ↥Y)).map Y.subtype = U := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hzW : π ⟨z, hzH⟩ ∈ (perfectCore (⊤ : Subgroup ↥Y)).map ψ := by
    rw [hW]
    exact hzL
  obtain ⟨w', hw'W, hw'z⟩ := hzW
  have hwU : (w' : G) ∈ U := hWU ▸ ⟨w', hw'W, rfl⟩
  set n : ↥Y := w'⁻¹ * ⟨z, hzY⟩
  have hn : p.Coprime (orderOf n) := by
    have h1 : ψ n = 1 := by
      rw [map_mul, map_inv, hw'z]
      exact inv_mul_cancel _
    have h2 := (mk'_primeComplementCore_eq_one_iff p _).mp h1
    have h3 : orderOf (Subgroup.inclusion hYH n) ∣ Nat.card (GLBPrimeCore p H) := by
      have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H) (x := (Subgroup.inclusion hYH n : G))
        h2
      rwa [Subgroup.orderOf_coe] at this
    rw [orderOf_injective _ (Subgroup.inclusion_injective hYH)] at h3
    exact (glbPrimeCore_coprime p H).coprime_dvd_right h3
  have hUn : (U.subgroupOf Y).Normal := perfectCore_normal Y
  set q := QuotientGroup.mk' (U.subgroupOf Y)
  have hqw : q w' = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwU)
  have hqz : q ⟨z, hzY⟩ = q n := by
    rw [show n = w'⁻¹ * ⟨z, hzY⟩ from rfl, map_mul, map_inv, hqw, inv_one, one_mul]
  have hzp : orderOf (⟨z, hzY⟩ : ↥Y) = p := by rw [Subgroup.orderOf_mk]; exact hzo
  have h1 : orderOf (q ⟨z, hzY⟩) ∣ p := hzp ▸ orderOf_map_dvd q _
  have h2 : orderOf (q ⟨z, hzY⟩) ∣ orderOf n := hqz ▸ orderOf_map_dvd q n
  have h3 : orderOf (q ⟨z, hzY⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hn) h2
  have h4 : ⟨z, hzY⟩ ∈ U.subgroupOf Y := (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h3)
  exact Subgroup.mem_subgroupOf.mp h4

end CFSG.AGLEmbedding
