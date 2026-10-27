module

public import CFSG.LocalAnalysis.ABGTheoremB.V5Transitivity
public import CFSG.LocalAnalysis.ABGTheoremB.V6Tools
import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

section Tools

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext y
  rw [mem_map_conj_iff]
  have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y
  rw [inv_inv] at this
  exact this.symm

theorem normalizer_le_normalizer_centralizer_self (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) := by
  apply le_normalizer_of_conj_mem
  intro g hg c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro t ht
  have ht' : g⁻¹ * t * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) t).mp ht
    simpa using this
  have h := hc _ ht'
  calc t * (g * c * g⁻¹) = g * (g⁻¹ * t * g * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * t * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * t := by group

theorem normalizer_le_normalizer_oddCoreIn_self [Finite G] (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (oddCoreIn H : Set G) := by
  apply le_normalizer_of_conj_mem
  intro g hg y hy
  have hHg : H.map (MulAut.conj g).toMonoidHom = H := map_conj_eq_of_mem_normalizer hg
  have hKH : (oddCoreIn H).map (MulAut.conj g).toMonoidHom ≤ H :=
    (Subgroup.map_mono (oddCoreIn_le H)).trans hHg.le
  have hHK : H ≤ Subgroup.normalizer
      (((oddCoreIn H).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    rw [normalizer_map_conj]
    calc H = H.map (MulAut.conj g).toMonoidHom := hHg.symm
      _ ≤ _ := Subgroup.map_mono (le_normalizer_oddCoreIn H)
  have hodd : Odd (Nat.card ((oddCoreIn H).map (MulAut.conj g).toMonoidHom)) := by
    rw [card_map_conj]
    exact odd_card_oddCoreIn H
  exact le_oddCoreIn hKH hHK hodd ⟨y, hy, rfl⟩

end Tools

variable {G : Type*} [Group G] [Finite G]

theorem exists_isSylowOf_C {σ : Setting G} (hσ : σ.IsValid) (hCs : CStructure σ) :
    ∃ P : Subgroup G, IsSylowOf σ.p P σ.C ∧ σ.D ≤ Subgroup.normalizer (P : Set G) := by
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have : Fact σ.p.Prime := ⟨hp⟩
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hDC : σ.D ≤ Subgroup.normalizer (σ.C : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_centralizer_self σ.T)
  have hDO : σ.D ≤ Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
    hDC.trans (normalizer_le_normalizer_oddCoreIn_self σ.C)
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_normalized_of_odd hp hD2 hDO (odd_card_oddCoreIn σ.C)
  refine ⟨P, isSylowOf_iff.mpr ⟨hP.le.trans (oddCoreIn_le σ.C), hP.isPGroup, ?_⟩, hDP⟩
  rw [← Subgroup.relIndex_mul_relIndex P (oddCoreIn σ.C) σ.C hP.le (oddCoreIn_le σ.C)]
  refine Nat.Prime.not_dvd_mul hp (isSylowOf_iff.mp hP).2.2 ?_
  have hF₀2 : IsPGroup 2 (σ.D ⊓ Subgroup.centralizer (σ.T : Set G) : Subgroup G) :=
    hD2.to_le inf_le_left
  have hF₀O : σ.D ⊓ Subgroup.centralizer (σ.T : Set G) ≤
      Subgroup.normalizer (oddCoreIn σ.C : Set G) :=
    inf_le_right.trans (le_normalizer_oddCoreIn σ.C)
  have h0 : (oddCoreIn σ.C).relIndex σ.C = (oddCoreIn σ.C).relIndex
      (oddCoreIn σ.C ⊔ (σ.D ⊓ Subgroup.centralizer (σ.T : Set G))) := by
    rw [hCs.C_eq]
  rw [h0, sup_comm, relIndex_sup_right_of_le_normalizer hF₀O]
  intro hdvd
  have h2 := hdvd.trans (Subgroup.relIndex_dvd_card _ _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF₀2
  rw [hk] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))

theorem mem_familyMstar_of_mem_familyM {σ : Setting G} (h83 : σ.LemmaIV83)
    (hHyp : σ.HypIV7 σ.p) (d : σ.IV7Data σ.p) {K : Subgroup G} (hK : K ∈ d.familyM) :
    K ∈ σ.familyMstar σ.p := by
  obtain ⟨hDg, hodd, -⟩ := h83 σ.p hHyp d K hK
  exact ⟨hK.1, hK.2.1, hDg, hodd⟩

section Choice

variable {σ : Setting G} {J W P V : Subgroup G}

private def familyU (σ : Setting G) (W V : Subgroup G) (𝓕 : Set (Subgroup G)) :
    Set (Subgroup G) :=
  {U | ∃ K ∈ 𝓕, V ⊔ W ⊔ σ.D ≤ K ∧ U ∈ signalizersPerm K σ.D W σ.p ∧ V ≤ U}

private theorem choice_facts (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (h41 : σ.PropV41 J)
    (hV31 : LemmaV31 σ J) (hW : W ∈ σ.familyW J) (hP : IsSylowOf σ.p P σ.C)
    (hDP : σ.D ≤ Subgroup.normalizer (P : Set G)) (hPne : P ≠ ⊥) (hPV : P ≤ V)
    (hVcore : pPrimeCoreIn σ.p (V ⊔ W) = ⊥) {𝓕 : Set (Subgroup G)} {U K : Subgroup G}
    (hKloc : IsPLocal σ.p K) (hVK : V ⊔ W ⊔ σ.D ≤ K) (hUK : U ∈ signalizersPerm K σ.D W σ.p)
    (hVU : V ≤ U) (hK𝓕 : K ∈ 𝓕) (hmax : ∀ X ∈ familyU σ W V 𝓕, Nat.card X ≤ Nat.card U) :
    U ∈ maximals (signalizersPerm K σ.D W σ.p) ∧ U ∈ maximals (signalizers K σ.D σ.p) ∧
      IsSylowOf σ.p (U ⊓ oddCoreIn K) (oddCoreIn K) ∧
      U ∈ signalizersPerm ⊤ σ.D W σ.p ∧ pPrimeCoreIn σ.p (U ⊔ W) = ⊥ ∧
      U ⊔ W ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) ∧
      σ.D ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) ∧
      Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) ∧
      IsPLocal σ.p (Subgroup.normalizer (CFSG.thompsonCenter U : Set G)) ∧ U ≠ ⊥ := by
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have hWp : ¬ σ.p ∣ Nat.card W := hV31.coprime W hW
  have hWodd : Odd (Nat.card W) := odd_card_of_mem_familyW hσ hJ hW
  have hDK : σ.D ≤ K := le_sup_right.trans hVK
  have hWK : W ≤ K := (le_sup_right.trans le_sup_left).trans hVK
  have hPK : P ≤ K := (hPV.trans (le_sup_left.trans le_sup_left)).trans hVK
  have hPU : P ≤ U := hPV.trans hVU
  have hOK : oddCoreIn K ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hp hp2 hKloc
  have hmaxK : ∀ U' ∈ signalizersPerm K σ.D W σ.p, U ≤ U' → Nat.card U' ≤ Nat.card U :=
    fun U' hU' hle => hmax U' ⟨K, hK𝓕, hVK, hU', hVU.trans hle⟩
  obtain ⟨S, hS, hUS, hSmax, hSsyl⟩ := (h41 K hDK hOK P hP hDP hPK W hW hWK U hUK hPU).1
  have hSU : S = U := (Subgroup.eq_of_le_of_card_ge hUS (hmaxK S hS hUS)).symm
  rw [hSU] at hSmax hSsyl
  have hUmaxK : U ∈ maximals (signalizersPerm K σ.D W σ.p) :=
    ⟨hUK, fun U' hU' hle => (Subgroup.eq_of_le_of_card_ge hle (hmaxK U' hU' hle)).symm⟩
  have hUsig : U ∈ signalizersPerm ⊤ σ.D W σ.p :=
    ⟨⟨le_top, hUK.1.2.1, hUK.1.2.2.1, hUK.1.2.2.2⟩, hUK.2⟩
  have hUp : IsPGroup σ.p U := hUK.1.2.1
  have hUcore : pPrimeCoreIn σ.p (U ⊔ W) = ⊥ :=
    pPrimeCoreIn_sup_eq_bot_of_le hp hUp hWp hUK.2 hVU hVcore
  have hUWH := le_normalizer_thompsonCenter_of_odd hp hp2 hUp hWp hWodd hUK.2 hUcore
  have hNUH := normalizer_le_normalizer_thompsonCenter_self U
  have hUne : U ≠ ⊥ := fun h => hPne (le_bot_iff.mp (h ▸ hPU))
  exact ⟨hUmaxK, hSmax, hSsyl, hUsig, hUcore, hUWH, hUK.1.2.2.1.trans hNUH, hNUH,
    isPLocal_normalizer_thompsonCenter hp hUp hUne, hUne⟩

private theorem mem_maximals_of_card_max (hσ : σ.IsValid) (h41 : σ.PropV41 J)
    (hW : W ∈ σ.familyW J) (hP : IsSylowOf σ.p P σ.C)
    (hDP : σ.D ≤ Subgroup.normalizer (P : Set G)) {𝓕 : Set (Subgroup G)} {U H : Subgroup G}
    (hH : H ∈ 𝓕) (hVWD : V ⊔ W ⊔ σ.D ≤ H) (hUH : U ≤ H)
    (hNUH : Subgroup.normalizer (U : Set G) ≤ H) (hOH : oddCoreIn H ≠ ⊥)
    (hU : U ∈ signalizersPerm ⊤ σ.D W σ.p) (hPV : P ≤ V) (hVU : V ≤ U)
    (hmax : ∀ X ∈ familyU σ W V 𝓕, Nat.card X ≤ Nat.card U) :
    U ∈ maximals (signalizersPerm ⊤ σ.D W σ.p) := by
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  refine ⟨hU, fun U' hU' hUU' => ?_⟩
  by_contra hne
  have hlt : U < U' := lt_of_le_of_ne hUU' (Ne.symm hne)
  have hDH : σ.D ≤ H := le_sup_right.trans hVWD
  have hWH : W ≤ H := (le_sup_right.trans le_sup_left).trans hVWD
  have hPH : P ≤ H := (hPV.trans (le_sup_left.trans le_sup_left)).trans hVWD
  have hUsigH : U ∈ signalizersPerm H σ.D W σ.p :=
    ⟨⟨hUH, hU.1.2.1, hU.1.2.2.1, hU.1.2.2.2⟩, hU.2⟩
  obtain ⟨S, hS, hUS, hSmax, -⟩ :=
    (h41 H hDH hOH P hP hDP hPH W hW hWH U hUsigH (hPV.trans hVU)).1
  have hN := lt_inf_normalizer_of_lt hp hU'.1.2.1 hlt
  have hNsig : U' ⊓ Subgroup.normalizer (U : Set G) ∈ signalizers H σ.D σ.p := by
    refine ⟨inf_le_right.trans hNUH, hU'.1.2.1.to_inf_left, ?_,
      inf_eq_bot_of_isPGroup_of_two hp hp2 hU'.1.2.1.to_inf_left hD2⟩
    exact (le_inf hU'.1.2.2.1 (hU.1.2.2.1.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSU : S ≠ U := by
    intro hSU
    rw [hSU] at hSmax
    exact hN.ne (hSmax.2 _ hNsig hN.le).symm
  have hUS' : U < S := lt_of_le_of_ne hUS (Ne.symm hSU)
  exact absurd (hmax S ⟨H, hH, hVWD, hS, hVU.trans hUS⟩)
    (not_le.mpr (Subgroup.card_lt_of_lt hUS'))

end Choice

theorem propV61 {G : Type} [Group G] [Finite G] {σ : Setting G} (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts) (hV21 : σ.CorollaryV21)
    (h41 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.PropV41 J)
    (h45 : ∀ J : Subgroup G, σ.IsV21Layer J → σ.LemmaV45 J) (hCs : CStructure σ)
    (hV31 : ∀ J : Subgroup G, σ.IsV21Layer J → LemmaV31 σ J)
    (hV33 : ∀ J : Subgroup G, σ.IsV21Layer J → LemmaV33 σ J)
    (hR1 : ∀ J : Subgroup G, σ.IsV21Layer J → PropR1Input σ J)
    (hR2 : ∀ J : Subgroup G, σ.IsV21Layer J → PropR2Input σ J)
    (h32 : σ.LemmaIV32) (h61 : σ.PropIV61) (h62 : σ.PropIV62) (h71 : σ.PropIV71)
    (h81 : σ.LemmaIV81) (h83 : σ.LemmaIV83) (h91 : σ.PropIV91) :
    ¬ σ.HypIV7 σ.p := by
  intro hHyp
  obtain ⟨J, hJ⟩ := hV21.exists_isV21Layer
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have : Fact σ.p.Prime := ⟨hp⟩
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hT2 : IsPGroup 2 σ.T := hD2.to_le (σ.T_le_D hσ)
  have hJ41 := h41 J hJ
  have hJ31 := hV31 J hJ
  have hJ33 := hV33 J hJ
  obtain ⟨W, hW⟩ := hJ31.nonempty
  obtain ⟨P, hP, hDP⟩ := exists_isSylowOf_C hσ hCs
  have hPne : P ≠ ⊥ :=
    ne_bot_of_isSylowOf hp hP (hHyp.dvd_CL.trans (Subgroup.card_dvd_of_le inf_le_left))
  obtain ⟨V, hVsig, hPV, hVcore, ⟨K₁₀, hK₁₀, hVK₁₀⟩, d, -, K₂₀, hK₂₀, hVK₂₀⟩ :=
    propV51 hσ hII hJ hJ41 hJ31 hJ33 h32 h71 h81 hHyp W hW P hP hDP
  have hK₂₀' : K₂₀ ∈ σ.familyMstar σ.p := mem_familyMstar_of_mem_familyM h83 hHyp d hK₂₀
  have hVmem : ∀ 𝓕 : Set (Subgroup G), ∀ K ∈ 𝓕, V ⊔ W ⊔ σ.D ≤ K → V ∈ familyU σ W V 𝓕 :=
    fun 𝓕 K hK hVK => ⟨K, hK, hVK, ⟨⟨(le_sup_left.trans le_sup_left).trans hVK, hVsig.1.2.1,
      hVsig.1.2.2.1, hVsig.1.2.2.2⟩, hVsig.2⟩, le_rfl⟩
  obtain ⟨U₁, ⟨K₁, hK₁, hVK₁, hU₁K₁, hVU₁⟩, hmax₁⟩ :=
    Set.exists_max_image (familyU σ W V (σ.familyL σ.p)) (fun U => Nat.card U)
      (Set.toFinite _) ⟨V, hVmem _ K₁₀ hK₁₀ hVK₁₀⟩
  obtain ⟨U₂, ⟨K₂, hK₂, hVK₂, hU₂K₂, hVU₂⟩, hmax₂⟩ :=
    Set.exists_max_image (familyU σ W V (σ.familyMstar σ.p)) (fun U => Nat.card U)
      (Set.toFinite _) ⟨V, hVmem _ K₂₀ hK₂₀' hVK₂₀⟩
  obtain ⟨hU₁max, hU₁maxs, hU₁syl, hU₁sig, hU₁core, hU₁WH, hDH₁, hNU₁, hH₁loc, hU₁ne⟩ :=
    choice_facts hσ hJ hJ41 hJ31 hW hP hDP hPne hPV hVcore hK₁.1 hVK₁ hU₁K₁ hVU₁ hK₁ hmax₁
  obtain ⟨hU₂max, hU₂maxs, -, hU₂sig, hU₂core, hU₂WH, hDH₂, hNU₂, hH₂loc, -⟩ :=
    choice_facts hσ hJ hJ41 hJ31 hW hP hDP hPne hPV hVcore hK₂.1 hVK₂ hU₂K₂ hVU₂ hK₂ hmax₂
  set H₁ := Subgroup.normalizer (CFSG.thompsonCenter U₁ : Set G) with hH₁
  set H₂ := Subgroup.normalizer (CFSG.thompsonCenter U₂ : Set G) with hH₂
  have hWK₁ : W ≤ K₁ := (le_sup_right.trans le_sup_left).trans hVK₁
  have hWK₂ : W ≤ K₂ := (le_sup_right.trans le_sup_left).trans hVK₂
  have hDK₁ : σ.D ≤ K₁ := le_sup_right.trans hVK₁
  have hDK₂ : σ.D ≤ K₂ := le_sup_right.trans hVK₂
  have hPU₁ : P ≤ U₁ := hPV.trans hVU₁
  have hPU₂ : P ≤ U₂ := hPV.trans hVU₂
  have hVWDH : ∀ U : Subgroup G, V ≤ U →
      U ⊔ W ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) →
      σ.D ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) →
      V ⊔ W ⊔ σ.D ≤ Subgroup.normalizer (CFSG.thompsonCenter U : Set G) :=
    fun U hVU hUW hD => sup_le (sup_le ((hVU.trans le_sup_left).trans hUW)
      (le_sup_right.trans hUW)) hD
  obtain ⟨hR₁O, hK₁fac⟩ :=
    hR1 J hJ hHyp W hW P hP hDP K₁ hK₁ hWK₁ U₁ hU₁max hU₁maxs hPU₁ hU₁core
  have hOK₁ : oddCoreIn K₁ ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hp hp2 hK₁.1
  have hS₁ : solvRadIn K₁ = oddCoreIn K₁ ⊔ centerOf σ.D :=
    hII.qgroup_solvRad K₁ hDK₁ hOK₁ hK₁.2.1
  have hcon₁ := h61 σ.p hp hHyp.dvd_ON hHyp.exceptional K₁ hK₁
  have hH₁mem : H₁ ∈ σ.familyL σ.p := by
    have hKO : K₁ ≤ Subgroup.normalizer (oddCoreIn K₁ : Set G) := le_normalizer_oddCoreIn K₁
    have hZK : centerOf σ.D ≤ K₁ := inf_le_left.trans hDK₁
    have hZH : centerOf σ.D ≤ H₁ := inf_le_left.trans hDH₁
    have hcov : (K₁ : Set G) ⊆
        ((K₁ ⊓ H₁ : Subgroup G) : Set G) * (oddCoreIn K₁ : Set G) := by
      intro k hk
      have hk' : k ∈ ((pPrimeCoreIn σ.p K₁ ⊔ (K₁ ⊓ H₁) : Subgroup G) : Set G) := by
        rw [hK₁fac]
        exact hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (inf_le_left.trans (le_normalizer_pPrimeCoreIn σ.p K₁))] at hk'
      obtain ⟨a, ha, m, hm, rfl⟩ := hk'
      have ha' : a ∈ ((oddCoreIn K₁ ⊔ centerOf σ.D : Subgroup G) : Set G) := by
        rw [← hS₁]
        exact pPrimeCoreIn_le_solvRadIn hcon₁ ha
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hZK.trans hKO)] at ha'
      obtain ⟨o, ho, z, hz, rfl⟩ := ha'
      have hzm : z * m ∈ K₁ ⊓ H₁ := ⟨K₁.mul_mem (hZK hz) hm.1, H₁.mul_mem (hZH hz) hm.2⟩
      rw [← permutable_of_le_normalizer (inf_le_left.trans hKO)]
      exact ⟨o, ho, z * m, hzm, by group⟩
    refine h62 σ.p hp hHyp.dvd_ON K₁ hK₁ (CFSG.thompsonCenter U₁)
      (thompsonCenter_ne_bot hp hU₁sig.1.2.1 hU₁ne) (isPGroup_thompsonCenter hU₁sig.1.2.1)
      hR₁O hDH₁ hcov ⟨U₁ ⊓ oddCoreIn K₁, hU₁syl, inf_le_left.trans ?_⟩
    exact Subgroup.le_normalizer.trans hNU₁
  have hK₂fac := hR2 J hJ hHyp W hW P hP hDP K₂ hK₂ hWK₂ U₂ hU₂max hU₂maxs hPU₂ hU₂core
  have hcon₂ := h91 σ.p hHyp K₂ hK₂
  have hTH₂ : σ.T ≤ H₂ := (σ.T_le_D hσ).trans hDH₂
  have hOH₂ : oddCoreIn H₂ ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hp hp2 hH₂loc
  have hH₂mem : H₂ ∈ σ.familyMstar σ.p := by
    have hKO : K₂ ≤ Subgroup.normalizer (oddCoreIn K₂ : Set G) := le_normalizer_oddCoreIn K₂
    have hcov : (K₂ : Set G) ⊆ (oddCoreIn K₂ : Set G) * ((K₂ ⊓ H₂ : Subgroup G) : Set G) := by
      intro k hk
      have hk' : k ∈ ((pPrimeCoreIn σ.p K₂ ⊔ (K₂ ⊓ H₂) : Subgroup G) : Set G) := by
        rw [hK₂fac]
        exact hk
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
        (inf_le_left.trans (le_normalizer_pPrimeCoreIn σ.p K₂))] at hk'
      obtain ⟨a, ha, m, hm, rfl⟩ := hk'
      exact ⟨a, pPrimeCoreIn_le_oddCoreIn hcon₂ ha, m, hm, rfl⟩
    have hTab : ∀ a ∈ σ.T, ∀ b ∈ σ.T, a * b = b * a := fun a ha b hb =>
      ((Subgroup.mem_centralizer_iff.mp (σ.T_le_C hσ hb)) a ha)
    have h3 : 3 ∣ automizerIndex (σ.T.subgroupOf H₂) :=
      three_dvd_automizerIndex_of_subset_mul (oddCoreIn_le K₂) hKO (odd_card_oddCoreIn K₂) hcov
        inf_le_left inf_le_right (le_inf ((σ.T_le_D hσ).trans hDK₂) hTH₂) hT2 hTab hK₂.2.2.1.2.2
    have hcovCL : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
        (H₂ : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) :=
      (hJ31.covers W hW).trans (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr
        (sup_le (le_sup_right.trans hU₂WH) hDH₂)))
    have hnotQD := hII.not_qd_of_cover H₂ hTH₂ hOH₂ hcovCL
    have hDwrt : IsDGroupWrt (σ.T.subgroupOf H₂) :=
      (hII.qd_or_d_of_three H₂ hTH₂ (Or.inl hDH₂) h3).resolve_left hnotQD
    refine ⟨hH₂loc, hDH₂, hDwrt, ?_⟩
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨t, htT, ht1, htX⟩ := exists_ne_one_mem_T_of_even hσ hCs
      (hDH₂.trans (le_normalizer_pPrimeCoreIn σ.p H₂)) hodd
    have htK : t ∈ K₂ ⊓ pPrimeCoreIn σ.p H₂ := ⟨hDK₂ (σ.T_le_D hσ htT), htX⟩
    have htO : t ∈ oddCoreIn K₂ :=
      pPrimeCoreIn_le_oddCoreIn hcon₂ (inf_pPrimeCoreIn_le_of_sup_eq hp hK₂fac htK)
    have hbot := inf_eq_bot_of_two_of_odd hT2 (odd_card_oddCoreIn K₂)
    have : t ∈ σ.T ⊓ oddCoreIn K₂ := ⟨htT, htO⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact ht1 this
  have hU₁glob : U₁ ∈ maximals (signalizersPerm ⊤ σ.D W σ.p) :=
    mem_maximals_of_card_max hσ hJ41 hW hP hDP hH₁mem (hVWDH U₁ hVU₁ hU₁WH hDH₁)
      (le_sup_left.trans hU₁WH) hNU₁ (oddCoreIn_ne_bot_of_isPLocal hp hp2 hH₁loc) hU₁sig hPV
      hVU₁ hmax₁
  have hU₂glob : U₂ ∈ maximals (signalizersPerm ⊤ σ.D W σ.p) :=
    mem_maximals_of_card_max hσ hJ41 hW hP hDP hH₂mem (hVWDH U₂ hVU₂ hU₂WH hDH₂)
      (le_sup_left.trans hU₂WH) hNU₂ hOH₂ hU₂sig hPV hVU₂ hmax₂
  obtain ⟨c, -, hc⟩ := propV52 hσ hJ hJ41 (h45 J hJ) hJ31 hJ33 hHyp W hW P hP hDP V hVsig hPV
    hVcore U₁ hU₁glob U₂ hU₂glob hVU₁ hVU₂
  have hH₂eq : H₁.map (MulAut.conj c).toMonoidHom = H₂ := by
    rw [hH₁, hH₂, ← hc, thompsonCenter_map_conj, normalizer_map_conj]
  have hQ₁ : IsQGroup H₁ :=
    (σ.familyL_properties hσ hII hp hHyp.dvd_ON hH₁mem).1.1
  have e : H₁ ≃* H₂ :=
    (H₁.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective).trans
      (MulEquiv.subgroupCongr hH₂eq)
  exact (hII.fusion_disjoint H₂).2.2.2.1 (IsQGroup.of_mulEquiv e hQ₁) hH₂mem.2.2.1.1

end CFSG.ABGTheoremB.V56
