module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE4T
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLFin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLNoS3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLNoLong
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLAsm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCenP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLWFix

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.TC.Thin

section SecE4

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem aeIdentOn_of_sectionE4T {n : ℕ} (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card G < n)
    (F : Q8Pre G Φ) {K K' : Subgroup G} (hK : K ∈ Φ) (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K') {a : G}
    (haK : K ≤ Subgroup.centralizer ({a} : Set G)) (haK' : K' ≤ Subgroup.centralizer ({a} : Set G))
    (ha : HasS3Quot ↥(Ea Φ a)) (hW : ¬ ∃ W : Subgroup G, WSet Φ = {W})
    (mf5 : ModelNoS3 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoS3 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf7 : ModelNoS3 7 Set.univ ((AE.aeSub 7).map (AE.mkQ 7))) (hE4 : E4S3TwinModel)
    (hLong : ∀ t : G, IsUniqueInvolution K t → ¬ LongFundSetE3 K t) :
    Nonempty (AEIdentOn Φ 7 AE.e64Sets AE.e64Sub) := by
  obtain ⟨t, ht⟩ := (F.hyp.omega1 K hK).1
  have hO2 : TightInO2 t := by
    rcases trichotomy_at (hP.twin rfl) hlt F hK hK'tw hne ht with h | h | h
    · exact h
    · by_contra hno
      obtain ⟨hK'Φ, z, hz, hz'⟩ := hK'tw
      exact false_of_twinE4_twin hE4 F hK ht hno h hK hK'Φ hz hne
        (L7.twin_le_normalizer F hK hK'Φ hne hz hz') hperp haK haK' ha
    · exact absurd h (hLong t ht)
  have F' := Q8Pre.toFam_of_tightInO2 F hK ht hO2
  exact aeIdentOn_of_concl F' (F'.thmDConcl hP.thmD.d2 hlt) hK hK'tw hne hperp ha hW mf5 mf6 mf7

end SecE4

section Fin

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y} {f₁ f₂ : Y}

theorem section_dataT (hT : Thm4RTwinBelow 3 n) (ctx : LemLCtx n Y R S t K' W u e g Z V f₁ f₂)
    (hL : SecCoresTwoGroup (Om R) V) (hY1 : ModS3O ↥(rLayer (Om R) e)) :
    Nat.card (SecQuot (rLayerSub (Om R) V)) < n ∧
      Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) ∧
      ∃ Kb Kb' : Subgroup (SecQuot (rLayerSub (Om R) V)), Kb ∈ p23SecFamV R V ∧
        Kb' ∈ twinSet (p23SecFamV R V) Kb ∧ Kb' ≠ Kb ∧
        (∀ J ∈ p23SecFamV R V, J ≠ Kb →
          J ≤ Subgroup.normalizer (Kb : Set (SecQuot (rLayerSub (Om R) V))) → J = Kb') ∧
        ∃ a : SecQuot (rLayerSub (Om R) V),
          Kb ≤ Subgroup.centralizer ({a} : Set (SecQuot (rLayerSub (Om R) V))) ∧
          Kb' ≤ Subgroup.centralizer ({a} : Set (SecQuot (rLayerSub (Om R) V))) ∧
          HasS3Quot ↥(Ea (p23SecFamV R V) a) := by
  obtain ⟨hlt, F, -⟩ := section_data hT ctx hL hY1
  have hc := ctx.cfg
  have hZd := ctx.zdata
  have hVZ := ctx.vz
  obtain ⟨hfX, ha⟩ := p23_type237 hc hZd hVZ hY1 ctx.hf₁ ctx.h₁
  have hU : V ⊔ Subgroup.zpowers f₁ ≤ Z :=
    sup_le hVZ (Subgroup.zpowers_le.mpr (hZd.orb_le ctx.hf₁))
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hU
  have hVU : (V : Set Y) ⊆ ((V ⊔ Subgroup.zpowers f₁ : Subgroup Y) : Set Y) :=
    SetLike.coe_subset_coe.mpr le_sup_left
  have hfU : f₁ ∈ V ⊔ Subgroup.zpowers f₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers f₁)
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) := hP₀C'.trans (Subgroup.centralizer_le hVU)
  have hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y) := hP₀'C'.trans (Subgroup.centralizer_le hVU)
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, -⟩ :=
    p23_twin_pair_of_sylow' hc hL hP₀ hP₀' hP₀C hP₀'C
  have hcent : ∀ {Q : Subgroup Y},
      Q ≤ Subgroup.centralizer ((V ⊔ Subgroup.zpowers f₁ : Subgroup Y) : Set Y) →
      secImage (rLayerSub (Om R) V) Q ≤ Subgroup.centralizer
        ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨f₁, hfX⟩} :
          Set (SecQuot (rLayerSub (Om R) V))) := by
    intro Q hQ
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hQ (Subgroup.mem_subgroupOf.mp hy)) f₁ hfU).symm
  exact ⟨hlt, F, _, _, hKb, ⟨hKb', zb, hzb, hzb'⟩, hne', hperp, _, hcent hP₀C', hcent hP₀'C', ha⟩

end Fin

section Final

theorem p23E7LemLId_finalT {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hL1 : LemLCoreTwo n) (hW : LemLNoW n) (hLong : LemLNoLong n)
    (mfE4 : E4S3TwinModel)
    (mf5 : ModelNoS3 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)))
    (mf6 : ModelNoS3 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)))
    (mf7 : ModelNoS3 7 Set.univ ((AE.aeSub 7).map (AE.mkQ 7))) (mf64 : E64NoS3) : P23E7LemLId n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd V hVZ hV1 f₁ hf₁ f₂ hf₂ hne h₁ h₂
  have ctx : LemLCtx n Y R S t K' W u e g Z V f₁ f₂ :=
    ⟨hc, hno, hE, hZ, hZd, hVZ, hV1, hf₁, hf₂, hne, h₁, h₂⟩
  have hL := hL1 hcit hP Y R S t K' W u e g Z V f₁ f₂ ctx
  have hY1 : ModS3O ↥(rLayer (Om R) e) := modS3O_rLayer hc hE
  have hY3' : OmegaOneCenter (rLayer (Om R) e) e :=
    lemLEZ_proved n hcit hP Y R S t K' W u e g hc hno hE hZ
  have hII : Nonempty (TC.Thin.AEIdentOn (p23SecFamV R V) 7 AE.e64Sets AE.e64Sub) := by
    obtain ⟨hlt, F, Kb, Kb', hKb, hKb', hne', hperp, a, haK, haK', ha⟩ := section_dataT hT ctx hL hY1
    exact aeIdentOn_of_sectionE4T hP hlt F hKb hKb' hne' hperp haK haK' ha
      (hW hcit hP Y R S t K' W u e g Z V f₁ f₂ ctx) mf5 mf6 mf7 mfE4
      (hLong hcit hP Y R S t K' W u e g Z V f₁ f₂ ctx _ hKb)
  obtain ⟨I⟩ := hII
  exact ⟨p23SecFamV_pSpan R V, ⟨I⟩, fun f hf hVf =>
    p23_central hc hZd hVZ hY1 hY3' mf64 I hf hVf⟩

theorem p23E7LemLId_doneT {n : ℕ} (hT : Thm4RTwinBelow 3 n)
    (hL1 : LemLCoreTwo n) (hW : LemLNoW n) (hLong : LemLNoLong n)
    (mfE4 : E4S3TwinModel) : P23E7LemLId n :=
  p23E7LemLId_finalT hT hL1 hW hLong mfE4 (modelNoS3_proved (by norm_num) (by norm_num))
    (modelNoS3_proved (by norm_num) (by norm_num)) (modelNoS3_proved (by norm_num) (by norm_num))
    e64NoS3_proved

end Final

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
