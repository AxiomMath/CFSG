module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldFactorTwist
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4HeldFactorCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPump
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeStep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGW36
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Normal
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
public import CFSG.LocalAnalysis.ComponentClassification.GSLitMaximalTriple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.GroupTheory.PCore.CommutingBalance
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKCInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace GrS4

variable {G : Type} [Group G] [Finite G]

theorem le_coreActionKernel_of_ne {M K K' : Subgroup G} (hKM : K ≤ M) (hK'M : K' ≤ M)
    (hK : IsPComponent 2 (K.subgroupOf M)) (hK' : IsPComponent 2 (K'.subgroupOf M))
    (hne : K ≠ K') : K ≤ coreActionKernel K' := by
  have hne' : K.subgroupOf M ≠ K'.subgroupOf M := fun h => hne (by
    have h1 := congrArg (map M.subtype) h
    rwa [subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hKM,
      inf_eq_left.mpr hK'M] at h1)
  obtain ⟨-, h2⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two
    _ _ hK hK'
  obtain ⟨-, hKN, hcomm, -⟩ := h2 hne'
  intro k hk
  have hkM := hKM hk
  have hkX : (⟨k, hkM⟩ : ↥M) ∈ K.subgroupOf M := hk
  refine ⟨mem_normalizer_of_subgroupOf hK'M (hKN hkX), fun j hj => ?_⟩
  have hjM := hK'M hj
  have hjX : (⟨j, hjM⟩ : ↥M) ∈ K'.subgroupOf M := hj
  have h1 : ⁅(⟨j, hjM⟩ : ↥M)⁻¹, (⟨k, hkM⟩ : ↥M)⁻¹⁆ ∈ ⁅K.subgroupOf M, K'.subgroupOf M⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (inv_mem hjX) (inv_mem hkX)
  have h3 := mem_map_of_mem M.subtype (hcomm h1).2
  rw [pPrimeCore_map_subgroupOf 2 K' M hK'M] at h3
  convert h3 using 1
  simp [commutatorElement_def]

theorem le_normalizer_layerIn (C : Subgroup G) :
    C ≤ normalizer (layerIn C : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  have hn : (pLayer ↥C 2).Normal := GrSLit.pLayer_two_normal'
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, hn.conj_mem y hy ⟨c, hc⟩, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨(⟨c, hc⟩ : ↥C)⁻¹ * y * ⟨c, hc⟩, ?_, ?_⟩
    · have := hn.conj_mem y hy (⟨c, hc⟩ : ↥C)⁻¹
      rwa [inv_inv] at this
    · simp only [coe_subtype, coe_mul, coe_inv] at hyx ⊢
      rw [hyx]
      group

omit [Finite G] in
theorem le_layerIn {C N : Subgroup G} (hNC : N ≤ C) (hN : IsPComponent 2 (N.subgroupOf C)) :
    N ≤ layerIn C := by
  intro x hx
  exact ⟨⟨x, hNC hx⟩, le_sSup (s := {L : Subgroup ↥C | IsPComponent 2 L}) hN hx, rfl⟩

theorem layerIn_le_normalizer {C N : Subgroup G} (hNC : N ≤ C)
    (hN : IsPComponent 2 (N.subgroupOf C)) : layerIn C ≤ normalizer (N : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mem_normalizer_of_subgroupOf hNC (GrSLit.pLayer_le_normalizer_of_isPComponent hN hy)

end GrS4

theorem l34Lemma43HeldFactorCase_holds
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (c : ℕ) : L34Lemma43HeldFactorCase c := by
  intro G _ _ a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJK m hm hK'ne haN' _
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := he
  obtain ⟨hbase, hU3, hL34, hmax, -, -, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, hHe, -⟩ := hbase
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hCaJ : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hCa : centralizer ({a} : Set G) ≤ M := hCaJ.trans hNJ
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have haM : a ∈ M := hCa (mem_centralizer_singleton_iff.mpr rfl)
  have hno : ∀ L : Subgroup G, L ≤ centralizer ({a} : Set G) →
      IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G))) →
      ¬ Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* Blueprint.NativeSporadic.He) :=
    fun L h1 h2 h3 => hHe ⟨a, L, ha2, h1, h2, h3⟩
  set KX : Subgroup ↥M := conjugate (K.subgroupOf M) ⟨m, hm⟩ with hKX
  have hKXmap : KX.map M.subtype = conjugate K m := by
    rw [hKX, GrS4.map_conjugate_subtype, GrS4.map_subgroupOf_subtype hKM]
  have hK'M : conjugate K m ≤ M := hKXmap ▸ map_subtype_le KX
  have hK'c : IsPComponent 2 ((conjugate K m).subgroupOf M) := by
    have h1 : (conjugate K m).subgroupOf M = KX := by
      rw [← hKXmap]
      exact comap_map_eq_self_of_injective M.subtype_injective KX
    rw [h1]
    exact LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
      (MulAut.conj (⟨m, hm⟩ : ↥M)⁻¹) hKc
  have e' : ↥(conjugate K m) ⧸ pPrimeCore 2 ↥(conjugate K m) ≃* Blueprint.NativeSporadic.He :=
    (Sol78.coreQuotCongr (K.equivMapOfInjective _ (MulAut.conj m⁻¹).injective)).symm.trans e
  have haK' : a ∉ coreActionKernel (conjugate K m) := fun h => by
    obtain ⟨L, h1, h2, h3⟩ := GrS4.exists_held_of_mem_coreActionKernel haa hCa hK'c e' h
    exact hno L h1 h2 h3
  have haN : a ∈ normalizer (K : Set G) := by
    by_contra h
    obtain ⟨L, h1, h2, h3⟩ := GrS4.exists_held_of_not_mem_normalizer haM haa hCa hKM hKc e h
    exact hno L h1 h2 h3
  have hJperf : ⁅J, J⁆ = J := GrS4.commutator_eq_self_of_gsMaximalSetting hgs
  have hJKle : J ≤ K := by
    have hOK := GrS4.oddIn_le_normalizer_of_isPComponent hKM hKc
    exact GrS5.le_of_le_sup_of_odd (isPerfect_iff.mpr hJperf) (odd_card_map_pPrimeCore M) hOK
      (hJK.trans (sup_le le_normalizer hOK)) (by rwa [sup_comm])
  have h64J : 64 ∣ Nat.card J := by
    have h1 : 20160 ∣ Nat.card J := by
      rw [← CatLeaf.card_of_isL34Type hL34]
      exact Subgroup.card_quotient_dvd_card _
    exact (show 64 ∣ 20160 by norm_num).trans h1
  have hfix : Nat.card ↥(autFixed (GrS4.heldQuotConj K ⟨a, haN⟩)) ≠ 15120 := by
    intro h15
    have hcount := GrS4.card_inf_centralizer_eq haN haa
    rw [h15] at hcount
    have hodd : Odd (Nat.card ↥(oddIn K ⊓ centralizer ({a} : Set G))) :=
      (odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
    have h64 : 64 ∣ Nat.card ↥(K ⊓ centralizer ({a} : Set G)) :=
      h64J.trans (Subgroup.card_dvd_of_le (le_inf hJKle hJa))
    rw [hcount] at h64
    have hcop : Nat.Coprime (2 ^ 6) (Nat.card ↥(oddIn K ⊓ centralizer ({a} : Set G))) :=
      Nat.Coprime.pow_left 6 (Nat.coprime_two_left.mpr hodd)
    have := hcop.dvd_of_dvd_mul_right h64
    norm_num at this
  obtain ⟨n, hnK, hna, hnn, htK, hnJ⟩ := GrS4.exists_twist e haN haa hfix
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
  set t : G := a * n with ht
  have htt : t * t = 1 := by
    calc a * n * (a * n) = a * (n * a) * n := by group
      _ = a * (a * n) * n := by rw [hna]
      _ = (a * a) * (n * n) := by group
      _ = 1 := by rw [haa, hnn, one_mul]
  have ht1 : t ≠ 1 := by
    intro h
    have han : a = n := by
      rw [← hni]
      exact eq_inv_of_mul_eq_one_left h
    apply haK'
    rw [han]
    exact GrS4.le_coreActionKernel_of_ne hKM hK'M hKc hK'c (Ne.symm hK'ne) hnK
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hat : a * t = t * a := by
    rw [ht, ← mul_assoc, mul_assoc a n a, hna, ← mul_assoc]
  have htCa : t ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hat.symm
  have htJ : t ∈ normalizer (J : Set G) := hCaJ htCa
  have hnCa : n ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hna
  have hJO : ∀ y ∈ J, y ∈ oddIn K → y ∈ oddIn J := by
    intro y hyJ hyO
    have hn : ((J ⊓ oddIn K).subgroupOf J).Normal := by
      refine ⟨fun z hz g => ?_⟩
      rw [mem_subgroupOf] at hz ⊢
      obtain ⟨hzJ, hzO⟩ := mem_inf.mp hz
      refine mem_inf.mpr ⟨mul_mem (mul_mem g.2 hzJ) (inv_mem g.2), ?_⟩
      exact (mem_normalizer_iff.mp (normalizer_le_normalizer_map_of_characteristic K
        (pPrimeCore 2 ↥K) (le_normalizer (hJKle g.2))) _).mp hzO
    have hodd : Odd (Nat.card ↥((J ⊓ oddIn K).subgroupOf J)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv]
      exact (odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
    exact ⟨⟨y, hyJ⟩, le_pPrimeCore_of_normal_of_odd hn hodd (mem_inf.mpr ⟨hyJ, hyO⟩), rfl⟩
  have hJt : ∀ j ∈ J, j⁻¹ * t⁻¹ * j * t ∈ (pPrimeCore 2 ↥J).map J.subtype := by
    intro j hj
    have hja : j * a = a * j := mem_centralizer_singleton_iff.mp (hJa hj)
    have h1 := hnJ j (hJKle hj) hja
    have h2 : j⁻¹ * t⁻¹ * j * t = j⁻¹ * (n * j * n⁻¹) := by
      have hjn : a * (n * j) = n * j * a := by
        calc a * (n * j) = (a * n) * j := by group
          _ = (n * a) * j := by rw [hna]
          _ = n * (j * a) := by rw [mul_assoc, hja]
          _ = n * j * a := by group
      calc j⁻¹ * t⁻¹ * j * t = j⁻¹ * (n⁻¹ * (a⁻¹ * (j * a)) * n) := by rw [ht]; group
        _ = j⁻¹ * (n⁻¹ * (a * (a * j)) * n) := by rw [hai, ← hja]
        _ = j⁻¹ * (n * j * n⁻¹) := by rw [← mul_assoc a a, haa, one_mul, hni]
    rw [h2]
    have hnJmem : n * j * n⁻¹ ∈ J := (mem_normalizer_iff.mp (hCaJ hnCa) j).mp hj
    exact hJO _ (mul_mem (inv_mem hj) hnJmem) h1
  set Jt : Subgroup G := gsFixedLayer J t with hJtdef
  have hJtle : Jt ≤ centralizer ({a} : Set G) ⊓ centralizer ({t} : Set G) :=
    (gsFixedLayer_le_inf J t).trans (inf_le_inf_right _ hJa)
  obtain ⟨hJsub, -, hJq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJa).1 hJc
  have hJtp : IsPComponent 2 (Jt.subgroupOf
      (centralizer ({a} : Set G) ⊓ centralizer ({t} : Set G))) :=
    UnbalancedCorr.gsFixedLayer_isPComponent hJa hJsub htCa ht2 htJ hJq hJt
  have htZ : t ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hnab ht2
  have htop : centralizer ({t} : Set G) ≠ ⊤ := fun h => htZ (mem_center_iff.mpr fun g =>
    mem_centralizer_singleton_iff.mp (h ▸ mem_top g : g ∈ centralizer ({t} : Set G)))
  obtain ⟨N, hNt, hNp, hJtN, -⟩ := HeK.exists_pump hS hK ha2 hat htop hJtle hJtp
  have hJtNN : Jt ≤ N ⊔ conjugate N a := hJtN.trans inf_le_left
  obtain ⟨hNat, hNap⟩ := UGSChain.conjugate_isPComponent_centralizer hat hNt hNp
  have hcorr : GSWeakCorr a J t N := ⟨ha2, ht2, hat, hJa, hJc, hNt, hNp, htJ, hJt, hJtNN⟩
  have hcorr' : GSWeakCorr a J t (conjugate N a) := by
    refine ⟨ha2, ht2, hat, hJa, hJc, hNat, hNap, htJ, hJt, ?_⟩
    have hNaa : conjugate (conjugate N a) a = N := by
      ext y
      rw [GrS4.mem_conjugate_iff_held, GrS4.mem_conjugate_iff_held, hai]
      have e1 : a * (a * y * a) * a = y := by
        calc a * (a * y * a) * a = (a * a) * y * (a * a) := by group
          _ = y := by rw [haa, one_mul, mul_one]
      rw [e1]
    rw [hNaa, sup_comm]
    exact hJtNN
  have htype : ∀ {N' : Subgroup G}, GSWeakCorr a J t N' →
      IsL34Type (↥N' ⧸ Open.fusionZStar ↥N') := fun {N'} h => by
    obtain ⟨eN⟩ := hmax.2 N' (GSWeakReach.single h)
    exact LieType.CurtisTits.lieModel_of_mulEquiv eN hL34
  have hJtperf : ⁅Jt, Jt⁆ = Jt := by
    rw [hJtdef, gsFixedLayer, ← map_commutator, UnbalancedCorr.pLayer_two_isPerfect]
  obtain ⟨-, -, ⟨eJt⟩⟩ := gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hcorr htZ
  have hJt2 : Even (Nat.card Jt) := by
    have h2J : 2 ∣ Nat.card (↥J ⧸ pPrimeCore 2 ↥J) := by
      have h1 := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J)
      have hO : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥J)) := pPrimeCore_coprime_card
      have h2 : 2 ∣ Nat.card ↥J := (show 2 ∣ 64 by norm_num).trans h64J
      rw [h1] at h2
      exact hO.dvd_of_dvd_mul_right h2
    rw [← Nat.card_congr eJt.toEquiv] at h2J
    exact even_iff_two_dvd.mpr (h2J.trans (Subgroup.card_quotient_dvd_card _))
  have hNΛ : N ≤ layerIn (centralizer ({t} : Set G)) := GrS4.le_layerIn hNt hNp
  have hNaΛ : conjugate N a ≤ layerIn (centralizer ({t} : Set G)) := GrS4.le_layerIn hNat hNap
  obtain ⟨P, hJtP, -, hPΛ, -, hsmall⟩ := GrS4.exists_perfect_cover e htt htK
    (GrS4.le_normalizer_layerIn _) ((gsFixedLayer_le_inf J t).trans (inf_le_left.trans hJKle))
    ((gsFixedLayer_le_inf J t).trans inf_le_right) (hJtNN.trans (sup_le hNΛ hNaΛ)) hJtperf hJt2
  have hPN := hPΛ.trans (GrS4.layerIn_le_normalizer hNt hNp)
  have hPNa := hPΛ.trans (GrS4.layerIn_le_normalizer hNat hNap)
  have hPk := GrS4.le_coreActionKernel_of_small
    (GSThmB.commutator_eq_self_of_isPComponent hNt hNp) (htype hcorr) hPN hsmall
  have hPk' := GrS4.le_coreActionKernel_of_small
    (GSThmB.commutator_eq_self_of_isPComponent hNat hNap) (htype hcorr') hPNa hsmall
  exact GrS4.false_of_le_coreActionKernel (hNaΛ.trans (GrS4.layerIn_le_normalizer hNt hNp))
    (hNΛ.trans (GrS4.layerIn_le_normalizer hNat hNap)) hJtperf hJt2 hJtNN (hJtP.trans hPk)
    (hJtP.trans hPk')

theorem l34Lemma43HeldFactor2AStep_holds
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) : L34Lemma43HeldFactor2AStep :=
  l34Lemma43HeldFactorCase_holds hMax hS 161280

theorem l34Lemma43HeldFactor2BStep_holds
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) : L34Lemma43HeldFactor2BStep :=
  l34Lemma43HeldFactorCase_holds hMax hS 21504

theorem l34Lemma43HeldFactorOuterStep_holds
    (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) : L34Lemma43HeldFactorOuterStep :=
  l34Lemma43HeldFactorCase_holds hMax hS 15120

end CFSG.ComponentClassification.GrSLit
