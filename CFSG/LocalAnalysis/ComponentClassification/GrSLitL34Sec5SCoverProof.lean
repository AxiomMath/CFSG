module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoverA
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoverB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SCoverStep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SBadTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SMoves
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL34InvKernel

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.GrS5
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma510CoverInvolutionStep_of_inputs
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact) (h58 : L34Lemma58)
    (h59 : L34Lemma59) (hSC : L34AutSylowCenterFact) (hComp : L34Cor217ComponentStep)
    (hType : HSFLit.L34Inv.L34Lemma55TypeStep) (hUnit : L34UnbalancingUnitaryStep) :
    L34Lemma510CoverInvolutionStep := by
  intro G _ _ L t S T hset u hu _ _ K₁ hK₁u hK₁p hK₁n htype₁ hO S₁ hS₁ hSS₁ _ _ _ _ _ _ _ _ _ h1
    _ h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htKL : t ∈ coreActionKernel L := mem_coreActionKernel_of_commute fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLt hl)).symm
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hu' := hu
  obtain ⟨huS₀, hu2, -⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  obtain ⟨hZ, hQL⟩ := le_of_twoExp_eq_two hS hU hheld hSol hGW h58 h59 hset h3
  have hexp : ∀ y ∈ S ⊓ coreActionKernel L ⊓ L, y * y = 1 := ((h58 G L t S T hset).2 hZ).2
  obtain ⟨hQΩ, -⟩ := (h58 G L t S T hset).2 hZ
  obtain ⟨z, hzo, hzt, hΩ, -, -⟩ := h59 G L t S T hset
  have hz2 : z * z = 1 := by rw [← pow_two, ← hzo, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by rintro rfl; simp at hzo
  have hzQ : z ∈ S ⊓ coreActionKernel L := by
    rw [hQΩ, hΩ]
    exact mem_sup_right (mem_zpowers z)
  have hzS : z ∈ S := (mem_inf.mp hzQ).1
  have hzc : ∀ s ∈ S, s * z = z * s := by
    intro s hs
    by_contra hne
    exact false_of_moves_center hS hU hheld hSol hGW hMax hL34 h58 h59 hSC hComp hset hexp
      ⟨z, hzo, hzt, hΩ⟩ ⟨z, mem_inf.mpr ⟨hzQ, hQL hzQ⟩, s, hs, hne⟩
  have htz : t * z = z * t := (hZS z hzS).symm
  have hperf₁ : ⁅K₁, K₁⁆ = K₁ := GSThmB.commutator_eq_self_of_isPComponent hK₁u hK₁p
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hunit := hUnit G u t K₁ hT₁ htype₁
  have hSN : S ≤ normalizer (K₁ : Set G) := hSS₁.trans hS₁.1
  have hSC' : S ≤ centralizer ({t} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (hZS s hs)
  obtain ⟨P, hP, hSP, hSKP⟩ := HSFLit.L34Inv.exists_isSylowTwoIn_normalized hS2 hSN
  have htP : t ∈ normalizer (P : Set G) := hSP htS
  have hZn : ((zStarIn K₁).subgroupOf K₁).Normal := by
    have h0 : (zStarIn K₁).subgroupOf K₁ = Open.fusionZStar K₁ :=
      comap_map_eq_self_of_injective K₁.subtype_injective _
    rw [h0, Sol78.fusionZStar_eq_comap]
    exact Subgroup.Normal.comap inferInstance _
  have hPZsyl : IsSylowTwoIn (P ⊓ zStarIn K₁) (zStarIn K₁) :=
    isSylowTwoIn_inf_of_isSubnormal hP (map_subtype_le _) hZn.isSubnormal
  have hPZc : Nat.card ↥(P ⊓ zStarIn K₁) = 2 := by
    rw [card_eq_two_pow_twoExp hPZsyl, h1, pow_one]
  have hle : S ⊓ K₁ ≤ P ⊓ centralizer ({t} : Set G) := le_inf hSKP (inf_le_left.trans hSC')
  have hge : P ⊓ centralizer ({t} : Set G) ≤ S ⊓ K₁ :=
    le_inf (HSFLit.L34Inv.le_of_isSylowTwoIn hSyl (inf_le_right.trans hCN)
      ((GrS4.isPGroup_of_isSylowTwoIn hP).to_le inf_le_left)
      fun s hs => HSFLit.L34Inv.mem_normalizer_inf' (hSP hs) (le_normalizer (hSC' hs)))
      (inf_le_left.trans hP.1)
  obtain ⟨-, h8, -⟩ := L34Facts.l34UnitaryCentralizerFact G K₁ P t hperf₁ htype₁ hunit hP htP
  have hSK8 : Nat.card ↥(S ⊓ K₁) = 8 := by rw [le_antisymm hle hge]; exact h8
  have hker : Nat.card ↥(S ⊓ K₁ ⊓ coreActionKernel K₁) ≤ 2 := by
    rw [← hPZc]
    refine Subgroup.card_le_of_le fun y hy => ?_
    obtain ⟨⟨hyS, hyK⟩, hyC⟩ := mem_inf.mp hy |>.imp_left mem_inf.mp
    refine mem_inf.mpr ⟨hSKP (mem_inf.mpr ⟨hyS, hyK⟩), ?_⟩
    have hzs : zStarIn K₁ = K₁ ⊓ coreActionKernel K₁ := GSThmB.map_fusionZStar_eq K₁
    rw [hzs]
    exact mem_inf.mpr ⟨hyK, hyC⟩
  obtain ⟨z₀, hz₀, j, hj, hjz⟩ := HSFLit.L34Inv.exists_inner_cover hperf₁ htype₁ hunit hS2 hSN
    hSC' inf_le_left inf_le_right hSK8 hker hzS hz2 fun q hq => hzc q (mem_inf.mp hq).1
  have hz₀Q : z₀ ∈ S ⊓ coreActionKernel L := by
    rcases hz₀ with rfl | rfl
    · exact hzQ
    · exact mul_mem (mem_inf.mpr ⟨htS, htKL⟩) hzQ
  have hz₀2 : z₀ * z₀ = 1 := by
    rcases hz₀ with rfl | rfl
    · exact hz2
    · calc t * z * (t * z) = t * (z * t) * z := by group
        _ = t * (t * z) * z := by rw [htz]
        _ = t * t * (z * z) := by group
        _ = 1 := by rw [ht2, hz2, one_mul]
  have hz₀1 : z₀ ≠ 1 := by
    rcases hz₀ with rfl | rfl
    · exact hz1
    · intro h
      apply hzt
      calc z = t⁻¹ * (t * z) := by group
        _ = t := by rw [h, mul_one, hti]
  have hz₀o : orderOf z₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz₀2) hz₀1
  set c := j⁻¹ * z₀ with hc
  have hcC : c ∈ centralizer (K₁ : Set G) :=
    HSFLit.L34Inv.mem_centralizer_of_mem_coreActionKernel hperf₁ hO hjz
  have hcj : c * j = j * c := (mem_centralizer_iff.mp hcC j hj).symm
  have hcN : c ∈ normalizer (P : Set G) := by
    refine mem_normalizer_iff.mpr fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have h0 : c * y = y * c := (mem_centralizer_iff.mp hcC y (hP.1 hy)).symm
      rw [h0, mul_inv_cancel_right]
      exact hy
    · have h0 : c * (c * y * c⁻¹) = c * y * c⁻¹ * c :=
        (mem_centralizer_iff.mp hcC _ (hP.1 hy)).symm
      have h1 : y = c * y * c⁻¹ := by
        calc y = c⁻¹ * (c * y * c⁻¹ * c) := by group
          _ = c⁻¹ * (c * (c * y * c⁻¹)) := by rw [h0]
          _ = c * y * c⁻¹ := by group
      rw [h1]
      exact hy
  have hjN : j ∈ normalizer (P : Set G) := by
    rw [show j = z₀ * c⁻¹ by rw [hc]; group]
    exact mul_mem (hSP (mem_inf.mp hz₀Q).1) (inv_mem hcN)
  have hj2 : j * j ∈ centralizer (K₁ : Set G) := by
    have hz : z₀ = j * c := by rw [hc]; group
    have hjj : j * j = (c * c)⁻¹ := by
      have e1 : j * c * (j * c) = 1 := by rw [← hz]; exact hz₀2
      have e2 : j * c * (j * c) = j * j * (c * c) := by
        rw [mul_assoc j c, ← mul_assoc c j c, hcj]; group
      rw [e2] at e1
      exact eq_inv_of_mul_eq_one_left e1
    rw [hjj]
    exact inv_mem (mul_mem hcC hcC)
  obtain ⟨p, hpP, hpj⟩ := L34Facts.exists_mul_of_mul_self_mem_centralizer hP hj hjN hj2
  obtain ⟨v, hvA, hz₁P, hz₁1, hz₁2, hz₁t, hz₁s⟩ :=
    L34Facts.exists_commutator_involution hperf₁ htype₁ hunit hP htP hPZc
  set z₁ := v⁻¹ * t⁻¹ * v * t with hz₁
  have hvz₀ : v * z₀ = z₀ * v := by
    have hw : p⁻¹ * j * c ∈ centralizer (K₁ : Set G) := mul_mem hpj hcC
    have hvK : v ∈ K₁ := hP.1 (mem_inf.mp hvA).1
    have hvp : p * v = v * p := mem_centralizer_iff.mp (mem_inf.mp hvA).2 p hpP
    have hvw : v * (p⁻¹ * j * c) = p⁻¹ * j * c * v := mem_centralizer_iff.mp hw v hvK
    have hz₀e : z₀ = p * (p⁻¹ * j * c) := by rw [hc]; group
    rw [hz₀e]
    calc v * (p * (p⁻¹ * j * c)) = v * p * (p⁻¹ * j * c) := by group
      _ = p * v * (p⁻¹ * j * c) := by rw [hvp]
      _ = p * (v * (p⁻¹ * j * c)) := by group
      _ = p * (p⁻¹ * j * c * v) := by rw [hvw]
      _ = p * (p⁻¹ * j * c) * v := by group
  have hv : v⁻¹ * t * v = t * z₁ := by
    calc v⁻¹ * t * v = v⁻¹ * t⁻¹ * v * (t * t) := by rw [ht2, mul_one, hti]
      _ = z₁ * t := by rw [hz₁]; group
      _ = t * z₁ := hz₁t
  have hz₁L : z₁ ∈ coreActionKernel L := HSFLit.L34Inv.mem_coreActionKernel_of_conj hS hU hheld
    hSol hGW hMax hL34 hType hset hz₀Q hz₀o hz₁t hvz₀ hv
  have hz₁N : z₁ ∈ normalizer (L : Set G) := hCN (mem_centralizer_singleton_iff.mpr hz₁t)
  have hz₁S : z₁ ∈ S := HSFLit.L34Inv.mem_of_isSylowTwoIn hSyl hz₁N hz₁2 fun s hs => by
    have h1 := hz₁s s (hSP hs) (hZS s hs)
    calc s * z₁ = s * z₁ * s⁻¹ * s := by group
      _ = z₁ * s := by rw [h1]
  refine ⟨z₁, mem_inf.mpr ⟨hz₁S, hz₁L⟩, orderOf_eq_prime (by rw [pow_two]; exact hz₁2) hz₁1,
    fun h => ?_, hP.1 hz₁P⟩
  apply hunit.2.2.1
  rw [← h]
  exact mem_sup_left (hP.1 hz₁P)

end CFSG.ComponentClassification.GrSLit.GrS5S
