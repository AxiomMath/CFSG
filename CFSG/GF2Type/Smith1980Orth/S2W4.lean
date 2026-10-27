module

public import CFSG.GF2Type.Smith1980Orth.S2Six
public import CFSG.GF2Type.Smith1980Orth.W4Pre
public import CFSG.GF2Type.Smith1980Orth.W4Irr
public import CFSG.GF2Type.Smith1980Orth.W4NoA2
public import CFSG.GF2Type.Smith1980Orth.TwoRankSmall
public import CFSG.LargeExtraspecial.S14W4LocTI
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Main
public import CFSG.Fischer.NoF25.Local
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.LargeExtraspecial.DW4Stmt
public import CFSG.LargeExtraspecial.DWTransGen
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.PSL10Fix
public import CFSG.LargeExtraspecial.S12InspUse
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.LargeExtraspecial.S14W4LocCase
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocLeaf
public import CFSG.LargeExtraspecial.S3cOddCore
public import CFSG.LargeExtraspecial.S3cSix
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S9GenA
public import CFSG.LargeExtraspecial.S9GenG
public import CFSG.LargeExtraspecial.S9PD
public import CFSG.LargeExtraspecial.S9RBQOdd
public import CFSG.LargeExtraspecial.S9TwoB
public import CFSG.LargeExtraspecial.S9TwoN
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.Open.QuasithinDefs
public import CFSG.RankThree.Literature.FSmithTheorem2
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module Equiv CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

local notation "σ₃" => finRotate 3

private theorem finRotate_three_ne_one : σ₃ ≠ 1 := by decide

private theorem finRotate_three_cube : σ₃ * σ₃ * σ₃ = 1 := by decide

private theorem conj_finRotate_three :
    ∀ τ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → τ * σ₃ * τ⁻¹ = σ₃⁻¹ := by
  decide

private theorem perm3_cases : ∀ τ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → ∀ π : Perm (Fin 3),
    π = 1 ∨ π = σ₃ ∨ π = σ₃ * σ₃ ∨ π = τ ∨ π = σ₃ * τ ∨ π = σ₃ * σ₃ * τ := by
  decide

private theorem perm3_eq_one : ∀ τ : Perm (Fin 3), τ ≠ 1 → τ * τ = 1 → ∀ π : Perm (Fin 3),
    π * σ₃ = σ₃ * π → π * τ = τ * π → π = 1 := by
  decide

section Coord

variable {G : Type} [Group G] [Finite G] {S : Setting G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {X : Subgroup (V ≃ₗ[ZMod 2] V)}

variable (K : Coord S X) {τ : Perm (Fin 3)} (hτ1 : τ ≠ 1) (hττ : τ * τ = 1) {T : S.Mbar}
  (hT : K.ι T = (τ, 1)) {K0 : S.Mbar} (hK0 : K.ι K0 = (σ₃, 1))

include hK0 in
private theorem Coord.k_ne_one : (K0 : S.O) ≠ 1 := fun h => finRotate_three_ne_one (by
  have hK1 : K0 = 1 := Subtype.ext h
  have := congrArg Prod.fst hK0
  rw [hK1, map_one] at this
  exact this.symm)

include hK0 in
private theorem Coord.k_cube : (K0 : S.O) ^ 3 = 1 := by
  have h3 : K0 * K0 * K0 = 1 := by
    apply K.inj
    rw [map_mul, map_mul, hK0, map_one]
    exact Prod.ext finRotate_three_cube (by simp)
  rw [pow_three, ← mul_assoc]
  exact congrArg Subtype.val h3

include hτ1 hττ hT hK0 in
private theorem Coord.t_inv_k : (T : S.O) * K0 * (T : S.O)⁻¹ = (K0 : S.O)⁻¹ := by
  have h : T * K0 * T⁻¹ = K0⁻¹ := by
    apply K.inj
    rw [map_mul, map_mul, map_inv, map_inv, hT, hK0]
    exact Prod.ext (conj_finRotate_three τ hτ1 hττ) (by simp)
  exact congrArg Subtype.val h

include hτ1 hττ hT hK0 in
private theorem Coord.exists_word (π : Perm (Fin 3)) : ∃ s : S.Mbar, K.ι s = (π, 1) ∧
    (s : S.O) ∈ zpowers (K0 : S.O) ⊔ zpowers (T : S.O) := by
  have hkm : ((K0 : S.O)) ∈ zpowers (K0 : S.O) ⊔ zpowers (T : S.O) :=
    mem_sup_left (mem_zpowers _)
  have htm : ((T : S.O)) ∈ zpowers (K0 : S.O) ⊔ zpowers (T : S.O) :=
    mem_sup_right (mem_zpowers _)
  rcases perm3_cases τ hτ1 hττ π with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, by rw [map_one]; rfl, one_mem _⟩
  · exact ⟨K0, hK0, hkm⟩
  · refine ⟨K0 * K0, ?_, mul_mem hkm hkm⟩
    rw [map_mul, hK0]
    exact Prod.ext rfl (by simp)
  · exact ⟨T, hT, htm⟩
  · refine ⟨K0 * T, ?_, mul_mem hkm htm⟩
    rw [map_mul, hK0, hT]
    exact Prod.ext rfl (by simp)
  · refine ⟨K0 * K0 * T, ?_, mul_mem (mul_mem hkm hkm) htm⟩
    rw [map_mul, map_mul, hK0, hT]
    exact Prod.ext rfl (by simp)

include hT hK0 in
private theorem Coord.mem_Cb_of_fst {c : S.Mbar} (hc : (K.ι c).1 = 1) :
    (c : S.O) ∈ W4.Cb S (K0 : S.O) (T : S.O) := by
  have hck : K0 * c = c * K0 := by
    apply K.inj
    rw [map_mul, map_mul, hK0]
    exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hc, mul_one, one_mul])
      (by rw [Prod.snd_mul, Prod.snd_mul, one_mul, mul_one])
  have hct : T * c = c * T := by
    apply K.inj
    rw [map_mul, map_mul, hT]
    exact Prod.ext (by rw [Prod.fst_mul, Prod.fst_mul, hc, mul_one, one_mul])
      (by rw [Prod.snd_mul, Prod.snd_mul, one_mul, mul_one])
  refine ⟨c.2, mem_centralizer_iff.mpr fun h hh => ?_⟩
  have hle : zpowers (K0 : S.O) ⊔ zpowers (T : S.O) ≤ centralizer {(c : S.O)} :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hck)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hct)))
  exact mem_centralizer_singleton_iff.mp (hle hh)

include hτ1 hττ hT hK0 in
private theorem Coord.dec {x : S.O} (hx : x ∈ S.Mbar) :
    ∃ s ∈ zpowers (K0 : S.O) ⊔ zpowers (T : S.O), ∃ c ∈ W4.Cb S (K0 : S.O) (T : S.O),
      x = s * c := by
  obtain ⟨m, rfl⟩ : ∃ m : S.Mbar, (m : S.O) = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨C0, hC0⟩ := K.surj 1 (K.ι m).2 (K.snd_mem m)
  obtain ⟨s, hs, hsmem⟩ := K.exists_word hτ1 hττ hT hK0 (K.ι m).1
  refine ⟨s, hsmem, C0, K.mem_Cb_of_fst hT hK0 (by rw [hC0]), ?_⟩
  have : m = s * C0 := by
    apply K.inj
    rw [map_mul, hs, hC0]
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  rw [this]
  rfl

include hτ1 hττ hT hK0 in
private theorem Coord.fst_eq_one_of_mem_Cb (c : W4.Cb S (K0 : S.O) (T : S.O)) :
    (K.ι ⟨c, c.2.1⟩).1 = 1 := by
  have e1 : K0 * ⟨c, c.2.1⟩ = ⟨c, c.2.1⟩ * K0 := Subtype.ext (W4.k_comm_of_mem_Cb c.2)
  have e2 : T * ⟨c, c.2.1⟩ = ⟨c, c.2.1⟩ * T := Subtype.ext (W4.t_comm_of_mem_Cb c.2)
  have f1 := congrArg (fun y => (K.ι y).1) e1
  have f2 := congrArg (fun y => (K.ι y).1) e2
  simp only [map_mul, Prod.fst_mul, hK0, hT] at f1 f2
  exact perm3_eq_one τ hτ1 hττ _ f1.symm f2.symm

include hτ1 hττ hT hK0 in
private theorem Coord.card_Cb_dvd : Nat.card (W4.Cb S (K0 : S.O) (T : S.O)) ∣ Nat.card X := by
  let f : W4.Cb S (K0 : S.O) (T : S.O) →* X :=
    { toFun := fun c => ⟨(K.ι ⟨c, c.2.1⟩).2, K.snd_mem _⟩
      map_one' := Subtype.ext (by
        change (K.ι 1).2 = 1
        rw [map_one]
        rfl)
      map_mul' := fun a b => Subtype.ext (by
        change (K.ι (⟨a, a.2.1⟩ * ⟨b, b.2.1⟩)).2 = (K.ι ⟨a, a.2.1⟩).2 * (K.ι ⟨b, b.2.1⟩).2
        rw [map_mul, Prod.snd_mul]) }
  have hf : Function.Injective f := by
    intro a b hab
    have h2 : (K.ι ⟨a, a.2.1⟩).2 = (K.ι ⟨b, b.2.1⟩).2 := congrArg Subtype.val hab
    have h : (⟨a, a.2.1⟩ : S.Mbar) = ⟨b, b.2.1⟩ :=
      K.inj (Prod.ext ((K.fst_eq_one_of_mem_Cb hτ1 hττ hT hK0 a).trans
        (K.fst_eq_one_of_mem_Cb hτ1 hττ hT hK0 b).symm) h2)
    exact Subtype.ext (congrArg (fun y : S.Mbar => (y : S.O)) h)
  exact Subgroup.card_dvd_of_injective f hf

end Coord

variable {G : Type} [Group G] [Finite G] {S : Setting G}

private theorem rank_transfer_four {n : ℕ} (hn : n = 4)
    (q : QuadraticForm (ZMod 2) (Fin n → ZMod 2)) (hq : timmesfeldNondegenerate q)
    (E : Subgroup ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)))
    (hE : E ≤ timmesfeldIsometries q) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  subst hn
  exact card_le_four_of_le_isometries hq hE hE2

private theorem exists_s2Data_w4_of_coord [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S)
    (hw : S.width = 4)
    {X : Subgroup ((Fin S.width → ZMod 2) ≃ₗ[ZMod 2] (Fin S.width → ZMod 2))}
    (hXI : X ≤ timmesfeldIsometries O.q) (K : Coord S X)
    (hX : (timmesfeldPlusType O.q → Nat.card X ∣ 72) ∧
      (¬ timmesfeldPlusType O.q → Nat.card X ∣ 120)) :
    Nonempty (S2Data S) := by
  obtain ⟨g, haQ, hne⟩ := O.exists_conj_mem_Q_of_width_eq_four hAS4 hw
  have hirr := O.not_isReducible_of_width_eq_four hThmA hw
    ⟨g, haQ, hne⟩
  have hnoAll := O.noA2All_of_not_isReducible I.hRI hirr
  have hno := hnoAll g haQ hne
  have H := S14.W4Loc.hyp4_of_w4 I.hTI (by omega) haQ hne hno hirr
  have C := S14.W4Loc.cons311_of_w4 I.hTI (by omega) haQ hne hno hirr
  have hNo : NoA2 S g := S14.noA2_of hno
  have hcard : Nat.card (S.Lbar g) = 2 ^ (2 + 1) := by
    rw [C.card_Lbar, hw]
  obtain ⟨τ, hτ1, hττ, P, hPX, hPc, hP2, hL⟩ := K.exists_decomp haQ 2
    (fun E hE hE2 => rank_transfer_four hw O.q O.nondeg E (hE.trans hXI) hE2) hcard
  have hP1 : P ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hPc
    norm_num at hPc
  obtain ⟨T, hT⟩ := K.surj τ 1 (one_mem X)
  have htL : (T : S.O) ∈ S.Lbar g :=
    (hL T).mpr ⟨by rw [hT]; exact Or.inr rfl, by rw [hT]; exact one_mem P⟩
  have ht1 : (T : S.O) ≠ 1 := fun h => hτ1 (by
    have hT1 : T = 1 := Subtype.ext h
    have := congrArg Prod.fst hT
    rw [hT1, map_one] at this
    exact this.symm)
  have hy : ∃ y ∈ X, ∃ x ∈ P, y * x * y⁻¹ ∉ P := by
    by_contra hcon
    push Not at hcon
    exact hP1 (K.eq_bot_of_normal hPX (fun u hu c hc => hcon u hu c hc) hP2)
  have hR := K.Rbar_ne_Lbar hPX hL hT hy
  obtain ⟨K0, hK0⟩ := K.surj σ₃ 1 (one_mem X)
  set k : S.O := (K0 : S.O) with hk
  have hkM : k ∈ S.Mbar := K0.2
  have hk1 : k ≠ 1 := K.k_ne_one hK0
  have hk3 : k ^ 3 = 1 := K.k_cube hK0
  have htk : (T : S.O) * k * (T : S.O)⁻¹ = k⁻¹ := K.t_inv_k hτ1 hττ hT hK0
  have hdec : ∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers (T : S.O),
      ∃ c ∈ W4.Cb S k (T : S.O), x = s * c := fun hx => K.dec hτ1 hττ hT hK0 hx
  have hCX : Nat.card (W4.Cb S k (T : S.O)) ∣ Nat.card X := K.card_Cb_dvd hτ1 hττ hT hK0
  have htt : (T : S.O) * T = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem htL
  have hN : Nbar S g (T : S.O) = zpowers (T : S.O) :=
    le_antisymm (W4.Nbar_le_zpowers H htL hirr hk3 htk hdec)
      (zpowers_le.mpr (S6.self_mem_Nbar H htL))
  have hC : Nat.card (W4.Cb S k (T : S.O)) ∣ 72 ∨ Nat.card (W4.Cb S k (T : S.O)) ∣ 120 := by
    by_cases hp : timmesfeldPlusType O.q
    · exact Or.inl (hCX.trans (hX.1 hp))
    · exact Or.inr (hCX.trans (hX.2 hp))
  have hPGL : Nat.card (W4.Cb S k (T : S.O)) ∣ 120 → ∀ hVQ : ¬ V S g (T : S.O) ≤ S.Qa g,
      ¬ PGL25Case H C htL ht1 hVQ := by
    intro _ hVQ
    by_cases hp : timmesfeldPlusType O.q
    · exact W4.not_pgl25Case_of_dvd
        ((W4.card_RmodN_dvd H htL hirr hk1 hk3 htk hdec).trans (hCX.trans (hX.1 hp)))
        (by norm_num)
    · exact hres G S O hw hp hirr hnoAll g H hNo C (T : S.O) k htL ht1 hVQ hkM hk1 hk3 htk
        hdec hR hN
  obtain ⟨hG, hfin⟩ := W4.goodT_of_width_eq_four I.hCE H hNo C htL ht1 hR hirr hnoAll hk1 hk3
    htk hdec hC hPGL
  have hP3 : Nat.card (zpowers k) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hk3 hk1]
  have hPn : ∀ m ∈ S.Mbar, ∀ p ∈ zpowers k, m * p * m⁻¹ ∈ zpowers k := by
    intro m hm p hp
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hp
    rw [← conj_zpow]
    rcases W4.conj_k_cases htt hk3 htk hdec hm with h | h
    · rw [h]
      exact zpow_mem (mem_zpowers k) n
    · rw [h]
      exact zpow_mem (inv_mem (mem_zpowers k)) n
  have hP1k : zpowers k ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hP3
    omega
  have hfpf : S13.FixFree S (zpowers k) := S13.fixFree_of hP1k hPn hirr
  exact ⟨⟨⟨g, T, k, hG.toGoodPre, by omega, hfin, hkM, hk1, hk3,
    fun x hx => W4.conj_k_cases htt hk3 htk hdec hx, htk,
    fun v hv => S13.fix_eq_zero hP3 hfpf (mem_zpowers k) hk1 v hv, hdec,
    S2Rel.full hkM⟩, hG.hΩ⟩⟩

theorem exists_s2Data_of_width_eq_four [IsSimpleGroup G] (I : TimInputs)
    (hAS4 : S14.AschbacherSmithW4Input) (hThmA : DW.W4Rank.TheoremAWidthFour)
    (hres : W4.PGL25W4Free) (O : OrthData S)
    (hw : S.width = 4) : Nonempty (S2Data S) := by
  obtain ⟨h36, h60⟩ := O.card_omega_of_width_eq_four hw
  have hiso := O.card_isometries
  rcases O.iso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · refine exists_s2Data_w4_of_coord I hAS4 hThmA hres O hw (timmesfeldOmega_le_isometries _)
      (Coord.ofEquiv e) ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [h36 hp]
      norm_num
    · rw [h60 hp]
      norm_num
  · refine exists_s2Data_w4_of_coord I hAS4 hThmA hres O hw le_rfl (Coord.ofEquiv e)
      ⟨fun hp => ?_, fun hp => ?_⟩
    · rw [hiso, h36 hp]
    · rw [hiso, h60 hp]

end CFSG.GF2Type.Smith1980Orth
