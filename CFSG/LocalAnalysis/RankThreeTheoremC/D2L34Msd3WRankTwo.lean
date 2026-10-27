module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WFusion
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WY
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WNoncycD
import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WThompson

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.PreuniquenessRankFour.Helpers
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound CFSG.AGLEmbeddingD2.Tits.MsidePrelim

section Pair

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem not_isCyclic_closure_pair (hMN : M ≤ Subgroup.normalizer (V : Set G))
    {I : Finset (Subgroup (MulAut (IntMod V hU)))} (hI : S3Family I)
    {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {x₁ x₂ : G} (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M) (hcomm : x₁ * x₂ = x₂ * x₁) (ho₁ : x₁ ^ 3 = 1)
    (ho₂ : x₂ ^ 3 = 1) (hL₁ : actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁) (hL₂ : actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂)
    (h₁1 : actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1) (h₂1 : actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1) :
    ¬ IsCyclic ↥(Subgroup.closure ({x₁, x₂} : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g₁ := actM hU hMN ⟨x₁, hx₁M⟩ with hg₁
  set g₂ := actM hU hMN ⟨x₂, hx₂M⟩ with hg₂
  have hg₂3 : g₂ ^ 3 = 1 := by
    have h' : (⟨x₂, hx₂M⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using ho₂)
    rw [hg₂, ← map_pow, h', map_one]
  have hx₁1 : x₁ ≠ 1 := fun h => h₁1 (by
    have h' : (⟨x₁, hx₁M⟩ : M) = 1 := Subtype.ext h
    rw [hg₁, h', map_one])
  set X : Subgroup G := Subgroup.closure {x₁, x₂} with hX
  have hx₁X : x₁ ∈ X := Subgroup.subset_closure (by simp)
  have hx₂X : x₂ ∈ X := Subgroup.subset_closure (by simp)
  have hnot : ∀ k : ℤ, x₂ ≠ x₁ ^ k := by
    intro k hk
    have : g₂ = g₁ ^ k := by
      rw [hg₂, hg₁, ← map_zpow]
      congr 1
      exact Subtype.ext (by simpa using hk)
    exact h₂1 (hI.eq_one_of_mem_inf h₁ h₂ hne (this ▸ L₁.zpow_mem hL₁ k) hL₂ hg₂3)
  intro hcyc
  obtain ⟨z, hz⟩ := hcyc.exists_generator
  have hz3 : z ^ 3 = 1 := Subtype.ext (by
    simpa using pow_three_of_mem_closure_pair hcomm ho₁ ho₂ z.2)
  have hcard : Nat.card X = orderOf z := orderOf_eq_card_of_forall_mem_zpowers hz |>.symm
  have hle3 : Nat.card X ≤ 3 := by
    rw [hcard]; exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
  have hord : orderOf x₁ = 3 := orderOf_eq_prime ho₁ hx₁1
  have hzp : Nat.card (Subgroup.zpowers x₁) = 3 := by rw [Nat.card_zpowers, hord]
  have hzpX : Subgroup.zpowers x₁ ≤ X := (Subgroup.zpowers_le).2 hx₁X
  have heq : Subgroup.zpowers x₁ = X :=
    Subgroup.eq_of_le_of_card_ge hzpX (by rw [hzp]; exact hle3)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ hx₂X)
  exact hnot k hk.symm

section Ctx

variable {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {A H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D2L34SideCtx3.hasGoodE9_closure_pair (h : D2L34SideCtx3 G d P M A H R Rbar K)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {I : Finset (Subgroup (MulAut (IntMod V hU)))}
    (hI : S3Family I) (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    (hYn : ∀ g ∈ autI hU M, ∀ φ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))),
      g * φ * g⁻¹ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))))
    {L₁ L₂ : Subgroup (MulAut (IntMod V hU))} (h₁ : L₁ ∈ I) (h₂ : L₂ ∈ I) (hne : L₁ ≠ L₂)
    {x₁ x₂ : G} (hx₁M : x₁ ∈ M) (hx₂M : x₂ ∈ M) (hcomm : x₁ * x₂ = x₂ * x₁) (ho₁ : x₁ ^ 3 = 1)
    (ho₂ : x₂ ^ 3 = 1) (hL₁ : actM hU hMN ⟨x₁, hx₁M⟩ ∈ L₁) (hL₂ : actM hU hMN ⟨x₂, hx₂M⟩ ∈ L₂)
    (h₁1 : actM hU hMN ⟨x₁, hx₁M⟩ ≠ 1) (h₂1 : actM hU hMN ⟨x₂, hx₂M⟩ ≠ 1) :
    HasGoodE9 M (Subgroup.closure ({x₁, x₂} : Set G)) := by
  have hXM : Subgroup.closure ({x₁, x₂} : Set G) ≤ M := (Subgroup.closure_le M).2 (by
    intro a ha
    rcases ha with rfl | ha
    · exact hx₁M
    · simp at ha
      subst ha
      exact hx₂M)
  have hXY : Subgroup.closure ({x₁, x₂} : Set G) ≤ preAutM hU hMN (⨆ L ∈ I, L) :=
    (Subgroup.closure_le _).2 (by
      intro a ha
      rcases ha with rfl | ha
      · exact (mem_preAutM hU hMN).2 ⟨hx₁M, Subgroup.mem_iSup_of_mem L₁
          (Subgroup.mem_iSup_of_mem h₁ hL₁)⟩
      · simp at ha
        subst ha
        exact (mem_preAutM hU hMN).2 ⟨hx₂M, Subgroup.mem_iSup_of_mem L₂
          (Subgroup.mem_iSup_of_mem h₂ hL₂)⟩)
  exact h.hasGoodE9_of_le_preAutM_iSup hMN hI hcard hC3 hYn hXM
    (isPGroup_three_closure_pair hcomm ho₁ ho₂) hXY
    (not_isCyclic_closure_pair hMN hI h₁ h₂ hne hx₁M hx₂M hcomm ho₁ ho₂ hL₁ hL₂ h₁1 h₂1)

end Ctx

end Pair

section Main

variable {G : Type} [Group G] [Finite G] {V M : Subgroup G} {hU : IsElemAbelian 2 V}

theorem center3_of_pairData3W
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K₀) (hR9 : Nat.card R = 9) {T : Subgroup G}
    (hT : IsSylowTwoOf T M) (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M)
    (hMN : M ≤ Subgroup.normalizer (V : Set G)) {I : Finset (Subgroup (MulAut (IntMod V hU)))}
    (hI : S3Family I) (hcard : ∀ L ∈ I, Nat.card L = 6)
    (hSylJ : IsSylowTwoOf (autI hU (baum T)) (autI hU (thompsonJ M)))
    (hJM : autI hU (thompsonJ M) = ⨆ L ∈ I, L)
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M)) {C₁ C₂ : Subgroup G}
    (hdat : FFPairData M T hU I C₁ C₂) : Center3Conclusion M := by
  classical
  have := ctx.amb
  have hc := ctx.conf
  have hOnly := ctx.allResidue.onlyL34At
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hC₁1, hC₁2, hC₂1, hC₂2, hT₁, hT₂, -, hJ₂, hH⟩ := hdat
  have hN₁ : ¬ Subgroup.normalizer (C₁ : Set G) ≤ M := fun h => hNT (hT₁.trans h)
  have hN₂ : ¬ Subgroup.normalizer (C₂ : Set G) ≤ M := fun h => hNT (hT₂.trans h)
  have hYn : ∀ g ∈ autI hU M, ∀ φ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))),
      g * φ * g⁻¹ ∈ (⨆ L ∈ I, L : Subgroup (MulAut (IntMod V hU))) := by
    intro g hg φ hφ
    rw [← hJM] at hφ ⊢
    exact autI_thompsonJ_normalized g hg φ hφ
  choose! Hf hHM hHL hH3 hHcase using hH
  set KA : Subgroup G := ⨆ L ∈ I, ⨆ (_ : Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L with hKA
  set KB : Subgroup G := ⨆ L ∈ I, ⨆ (_ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G)), Hf L
    with hKB
  have hKAM : KA ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBM : KB ≤ M := iSup₂_le fun L hL => iSup_le fun _ => hHM L hL
  have hKBN : KB ≤ Subgroup.normalizer (C₂ : Set G) :=
    iSup₂_le fun L hL => iSup_le fun h => (hHcase L hL).resolve_left h
  have hKAN : KA ≤ Subgroup.normalizer (C₁ : Set G) := iSup₂_le fun L hL => iSup_le fun h => h
  have hcov : ∀ L ∈ I, L ≤ autI hU KA ∨ L ≤ autI hU KB := by
    intro L hL
    by_cases h : Hf L ≤ Subgroup.normalizer (C₁ : Set G)
    · exact Or.inl ((hHL L hL).trans (autI_mono hU (le_iSup₂_of_le L hL
        (le_iSup (fun _ : Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L) h))))
    · exact Or.inr ((hHL L hL).trans (autI_mono hU
        (le_iSup₂_of_le L hL (le_iSup (fun _ : ¬ Hf L ≤ Subgroup.normalizer (C₁ : Set G) => Hf L)
          h))))
  have hAuniq : ∀ L₁ ∈ I, ∀ L₂ ∈ I, Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) →
      Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hH₁ hH₂
    by_contra hne
    exact false_of_two_factors_in_normalizer3_of_good hc hR9 ctx.normRankTwo hOnly hMN hC₁1 hC₁2
      hN₁ hKAM hKAN hC3 hI hcard h₁ h₂ hne ((hHL L₁ h₁).trans (autI_mono hU (le_iSup₂_of_le L₁ h₁
        (le_iSup (fun _ : Hf L₁ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₁) hH₁))))
      ((hHL L₂ h₂).trans (autI_mono hU (le_iSup₂_of_le L₂ h₂
        (le_iSup (fun _ : Hf L₂ ≤ Subgroup.normalizer (C₁ : Set G) => Hf L₂) hH₂))))
      (fun x₁ x₂ _ _ hcomm ho₁ ho₂ hx₁M hx₂M hL₁ hL₂ hn₁ hn₂ =>
        ctx.hasGoodE9_closure_pair hMN hI hcard hC3 hYn h₁ h₂ hne hx₁M hx₂M hcomm ho₁ ho₂ hL₁
          hL₂ hn₁ hn₂)
  have hbA : ∀ Q' : Subgroup (MulAut (IntMod V hU)), Q' ≤ autI hU KA → IsPGroup 3 Q' →
      Nat.card Q' ≤ 3 := by
    intro Q' hQ' hQ'p
    by_cases hex : ∃ L₀ ∈ I, Hf L₀ ≤ Subgroup.normalizer (C₁ : Set G)
    · obtain ⟨L₀, hL₀, hH₀⟩ := hex
      have hKAeq : KA ≤ Hf L₀ := iSup₂_le fun L hL => iSup_le fun h => by
        rw [hAuniq L hL L₀ hL₀ h hH₀]
      exact hH3 L₀ hL₀ Q' (hQ'.trans (autI_mono hU hKAeq)) hQ'p
    · push Not at hex
      have hKAbot : KA = ⊥ := by
        refine le_bot_iff.1 (iSup₂_le fun L hL => iSup_le fun h => absurd h (hex L hL))
      have hQ'bot : Q' = ⊥ := by
        refine le_bot_iff.1 (fun φ hφ => ?_)
        obtain ⟨g, hg, rfl⟩ := (mem_autI hU).1 (hQ' hφ)
        rw [hKAbot, Subgroup.mem_bot] at hg
        have : g = 1 := Subtype.ext hg
        rw [this, map_one]
        exact Subgroup.one_mem _
      rw [hQ'bot, Subgroup.card_bot]; norm_num
  set CM : Subgroup G := Subgroup.centralizer (V : Set G) ⊓ M with hCM
  set 𝒜 : Subgroup G := CM ⊔ KA with h𝒜
  set ℬ : Subgroup G := KB ⊔ (M ⊓ Subgroup.normalizer (baum T : Set G)) with hℬ
  have h𝒜M : 𝒜 ≤ M := sup_le inf_le_right hKAM
  have hℬM : ℬ ≤ M := sup_le hKBM inf_le_left
  have hℬN : ℬ ≤ Subgroup.normalizer (C₂ : Set G) := sup_le hKBN hJ₂
  have hfac : ∀ m ∈ M, ∃ a ∈ 𝒜, ∃ b ∈ ℬ, m = a * b := by
    intro m hm
    obtain ⟨c, hc', a, ha, b, hb, n, hn, rfl⟩ := exists_factor_of_covering hMN hT (C1GN.baum_le T)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T))
      (normalizer_inf_sup_le_normalizer_baum T _) hI hSylJ hJM hKAM hKBM hcov m hm
    exact ⟨c * a, Subgroup.mul_mem _ (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right ha),
      b * n, Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hn),
      by group⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := 3) h𝒜M hℬM hfac
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  obtain ⟨E, hEW, hEel, hEc⟩ := exists_elemAbelian_le_sylow_pow hWM hWp hWidx h3
  have hE27 : Nat.card E = 27 := by rw [hEc]; norm_num
  set U : Subgroup G := W ⊓ ℬ with hUdef
  have hUW : U ≤ W := inf_le_left
  have hUM : U ≤ M := hUW.trans hWM
  have hUN : U ≤ Subgroup.normalizer (C₂ : Set G) := inf_le_right.trans hℬN
  have hUp : IsPGroup 3 U := hWp.to_le hUW
  have hA'3 : Nat.card (W ⊓ 𝒜 : Subgroup G) ≤ 3 :=
    card_le_of_le_sup_centralizer hMN hC3 hKAM inf_le_right (hWp.to_le inf_le_left) hbA
  obtain ⟨hUnc, hWle⟩ := not_isCyclic_of_E27_small_factor hEW hEel hE27 inf_le_left hUW hA'3 hWfac
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hEU : 9 ≤ Nat.card (E ⊓ U : Subgroup G) := by
    have hP : Nat.card E * Nat.card U ≤ Nat.card W * Nat.card (E ⊓ U : Subgroup G) :=
      card_mul_card_le_card_mul_card_inf hEW hUW
    rw [hE27] at hP
    by_contra hlt
    have hlt' : Nat.card (E ⊓ U : Subgroup G) ≤ 8 := by omega
    have h1 : Nat.card W * Nat.card (E ⊓ U : Subgroup G) ≤ (3 * Nat.card U) * 8 :=
      Nat.mul_le_mul hWle hlt'
    omega
  have hEUp : IsPGroup 3 (E ⊓ U : Subgroup G) := hWp.to_le (inf_le_right.trans hUW)
  have hEUel : IsElemAbelian 3 (E ⊓ U : Subgroup G) :=
    CFSG.AGLEmbeddingD2.Tits.MsidePrelim.isElemAbelian_of_le hEel inf_le_left
  obtain ⟨E₁, hE₁le, hE₁el, hE₁9⟩ := exists_E9_le_of_not_isCyclic hEUp
    (not_isCyclic_of_isElemAbelian hEUel (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hEU))
  have hgoodU : HasGoodE9 M U :=
    ctx.hasGoodE9_of_le_E27 (hE₁le.trans inf_le_right) (hE₁le.trans inf_le_left) hE₁el hE₁9
      (hEW.trans hWM) hEel hE27
  obtain ⟨-, hU9, -⟩ := D2L34BetaConf3.exists_conj_eq_of_good hc hR9 ctx.normRankTwo hOnly
    (⟨C₂, hC₂1, hC₂2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (C₂ : Set G))) hN₂ hUN hUM hUp hUnc
    hgoodU
  have hW27 : Nat.card W ≤ 27 := by rw [hU9] at hWle; omega
  have hWE : E = W := Subgroup.eq_of_le_of_card_ge hEW (by rw [hE27]; exact hW27)
  obtain ⟨E₉, hE₉E, hE₉el, hE₉c⟩ := exists_E9_le_E27 hEel hE27
  refine ⟨W, hWM, hWp, hWidx, E₉, hE₉E.trans hWE.le, hE₉el, hE₉c, fun w hw _ e he => ?_⟩
  have hwE : w ∈ E := by rw [hWE]; exact hw
  exact congrArg Subtype.val (hEel.1.is_comm.comm ⟨w, hwE⟩ ⟨e, hE₉E he⟩)

end Main

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem center3_of_coprime_centralizer3W
    (hI59 : AGL81I59) (hX : D1NoXBlock3 G)
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (ctx : D2L34SideCtx3 G d P M A H R Rbar K) (hR9 : Nat.card R = 9)
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) {T : Subgroup G} (hT : IsSylowTwoOf T M)
    (hNT : ¬ Subgroup.normalizer (T : Set G) ≤ M) (hC3 : ¬ 3 ∣ Nat.card ↥(ffC M T)) :
    Center3Conclusion M := by
  have hN : NoXBlockFor G := noXBlockFor_of_setting hX ctx.setting
  have := ctx.amb
  have hc := ctx.conf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hMtop : M ≠ ⊤ := fun h => hc.esc.not_le (h ▸ le_top)
  have hKg : CFSG.Open.IsKGroup ↥M :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup
      (CFSG.ComponentClassification.CatalogueKProper.open_isKProper_iff.1
        (D2Amb3.glob (G := G)).kProper) M hMtop
  have hF : CharTwo M := (D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal ctx.setting ctx.sigma ctx.core
  have h3 : 3 ≤ CFSG.Open.pRank 3 M := hP3.ge.trans (pRank_mono 3 Nat.prime_three hPM)
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) M : Set G)
  · exact (ctx.false_of_thompsonJ_le_of_coprime_of_nine hR9 h3 hT hNT hJ hC3).elim
  · set V := conjClosure (quasithinOmegaOneCenter T) M with hV
    obtain ⟨hU, -⟩ := B2_15 hF hT
    have hMN : M ≤ Subgroup.normalizer (V : Set G) :=
      (conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)).2.2.2.1
    have hconAut : CFSG.ABGLocalTools.IsPConstrained 3 ↥(autOn M V) :=
      isPConstrained_autI_of_coprime hU hMN hC3 hcon
    have hFF : FFConclusion M T V := by
      by_cases hs : Group.IsSolvable ↥(autOn M V)
      · exact ffConclusion_of_solvable hF hs hT hV hJ
      · exact hI59 G M T V hKg hF hT hV hconAut hJ
    obtain ⟨hU', hMN', I, -, hcard, hJM, hSyl, hperm, hI⟩ :=
      exists_family_of_ffConclusion hT hJ hFF
    obtain ⟨C₁, C₂, hdat⟩ := exists_ffPairData3_free hN ffGroupStep3Free ctx hT hNT hU' I hMN'
      hcard hJM hSyl hperm hI
    obtain ⟨hle, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    have hVT : V ≤ T := hle.trans (inf_le_left.trans (B6.pCoreOf_two_le_of_isSylowTwoOf hT))
    have hBS : autI hU' (baum T) ≤ autI hU' (thompsonJ M) :=
      autI_baum_le_autI_thompsonJ hMN' hT hVT hI hJM (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
        hperm
    have hSylB : IsSylowTwoOf (autI hU' (baum T)) (autI hU' (thompsonJ M)) :=
      isSylowTwoOf_of_le_of_le hSyl (autI_mono hU' (thompsonJ_le_baum T)) hBS
        (isPGroup_autI hU' (hT.2.1.to_le (C1GN.baum_le T)))
    exact center3_of_pairData3W ctx hR9 hT hNT hMN' hI hcard hSylB hJM hC3 hdat

end Coprime

end CFSG.LocalAnalysis.RankThreeTheoremC
