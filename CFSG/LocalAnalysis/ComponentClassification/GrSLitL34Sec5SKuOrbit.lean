module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Orbit58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SKu55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Comp582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs582
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs58O
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools510
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Tools59
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL2Central

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem l34Lemma58OrbitStep_of_inputs_ku
    (hS : SchreierFor Blueprint.Catalog)
    (hU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hheld : KProperRelativeB.HeldInput)
    (hSol : SolomonCommutingCoreInput) (hGW : GorensteinWalterConnectedInput)
    (hMax : MaximalTwoComponentInput) (hL34 : L34InvolutionCentralizerFact)
    (hKu : GrS5S.L34Sec5KuOddStep)
    (hFour : L34UnbalancingFourFact) (hL2 : L2UnbalancingAutFact)
    (hOut : L2UnbalancingOuterFact) :
    L34Lemma58OrbitStep := by
  intro G _ _ L t S T hset u hu hsyl hw y hyQ hy4 hyc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hE, -⟩ :=
    isElemTwo_omegaOne_of_setting_ku hS hU hheld hSol hGW hMax hL34 hKu hFour hset
  obtain ⟨-, hLt, hLpt⟩ := eq_of_mem_inf_centralizer hS hU hheld hSol hGW hset
  have hZS := mem_center_of_setting hS hU hheld hSol hGW hset
  have hset' := hset
  obtain ⟨-, ⟨⟨-, -, -, -, -, hto, -, -⟩, -⟩, -, hSyl, htS, -, -⟩ := hset'
  have hS2 : IsPGroup 2 S := IsSylowTwoIn.isPGroup hSyl
  have hw' := hw
  obtain ⟨w, hwΩ, hw1, hwc⟩ := hw'
  have hu' := hu
  obtain ⟨huS₀, hu2, hUu⟩ := hu'
  have huS : u ∈ S := (sup_le inf_le_left (zpowers_le.mpr htS) : S ⊓ L ⊔ zpowers t ≤ S) huS₀
  have htu : t * u = u * t := (hZS u huS).symm
  have hYD : oddIn L ⊓ centralizer ({u} : Set G) ≤
      oddIn (centralizer ({t} : Set G)) ⊓ centralizer ({u} : Set G) :=
    inf_le_inf_right _ (GSLit.map_pPrimeCore_le_of_isPComponent hLt hLpt)
  have hCN := centralizer_le_normalizer_of_setting hS hU hheld hSol hGW hMax hset
  obtain ⟨K₀, hK₀u, hK₀p, hK₀n⟩ := exists_isPComponent_not_le hSol hto hu2 htu hYD hUu
  obtain ⟨htype₀, -⟩ := hcon K₀ hK₀u hK₀p hK₀n
  have hT₀ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₀u hK₀p hYD hK₀n
  obtain ⟨k, hk, hko⟩ := HSFLit.AutL2.exists_involution_centralizer_of_unbalancing hT₀ htype₀
  have hk2 : k * k = 1 := by rw [← pow_two, ← hko, pow_orderOf_eq_one]
  have hkH : k ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) :=
    mem_inf.mpr ⟨(mem_inf.mp hk).2, hK₀u (mem_inf.mp hk).1⟩
  obtain ⟨c, hcH, hcS⟩ := exists_conj_mem_of_isSylowTwoIn hsyl hkH
    (HSFLit.L34Inv.isPGroup_zpowers_of_mul_self hk2)
  have hcu : c ∈ centralizer ({u} : Set G) := (mem_inf.mp hcH).2
  have hcL : c ∈ normalizer (L : Set G) := hCN (mem_inf.mp hcH).1
  obtain ⟨hK₁u, hK₁p⟩ := GSThmB.Six.isPComponent_conjugate hK₀u hK₀p c
  have hCc : conjugate (centralizer ({u} : Set G)) c = centralizer ({u} : Set G) :=
    conjugate_eq_of_mem_normalizer (le_normalizer hcu)
  rw [hCc] at hK₁u hK₁p
  have hDc : conjugate (oddIn L ⊓ centralizer ({u} : Set G)) c =
      oddIn L ⊓ centralizer ({u} : Set G) := by
    rw [GSThmB.conjugate_inf, hCc,
      conjugate_eq_of_mem_normalizer (normalizer_le_normalizer_oddIn L hcL)]
  have hK₁n : ¬ ⁅conjugate K₀ c, oddIn L ⊓ centralizer ({u} : Set G)⁆ ≤
      oddIn (conjugate K₀ c) := by
    rw [commutator_le_oddIn_conjugate_iff hDc]
    exact hK₀n
  have hz₀ : c⁻¹ * k * c ∈ S ⊓ conjugate K₀ c :=
    mem_inf.mpr ⟨(mem_inf.mp hcS).1, conj_mem_conjugate (mem_inf.mp hk).1 c⟩
  have hz₀2 : orderOf (c⁻¹ * k * c) = 2 := by rw [GSLit.orderOf_conj_inv, hko]
  set K₁ := conjugate K₀ c with hK₁def
  obtain ⟨htype₁, hyN₁⟩ := hcon K₁ hK₁u hK₁p hK₁n
  have hT₁ := gsUnbalancingTriple_of_not_le hSol hto hu2 htu hK₁u hK₁p hYD hK₁n
  have hyS : y ∈ S := (mem_inf.mp hyQ).1
  have hyK : y ∈ coreActionKernel L := (mem_inf.mp hyQ).2
  have hyu : y * u = u * y :=
    commute_of_mem_unbalancingSet hS hU hheld hSol hGW hset hyQ huS₀
  have hyC : y ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.mpr hyu
  have hconjD : ∀ c ∈ S, c ∈ centralizer ({u} : Set G) →
      conjugate (oddIn L ⊓ centralizer ({u} : Set G)) c = oddIn L ⊓ centralizer ({u} : Set G) := by
    intro c hcS hcu
    refine conjugate_eq_of_mem_normalizer ?_
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (normalizer_le_normalizer_oddIn L (hSyl.1 hcS)) x
    have h2 := mem_normalizer_iff.mp (le_normalizer hcu) x
    simp only [mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  set C := centralizer ({u} : Set G) with hC
  set D := oddIn L ⊓ C with hD
  obtain ⟨hK₂u, hK₂p⟩ := GSThmB.Six.isPComponent_conjugate hK₁u hK₁p y
  have hCy : conjugate C y = C := conjugate_eq_of_mem_normalizer (le_normalizer hyC)
  rw [hCy] at hK₂u hK₂p
  set K₂ := conjugate K₁ y with hK₂
  have hne : K₁ ≠ K₂ := fun h => hyN₁ (mem_normalizer_of_conjugate_eq h.symm)
  obtain ⟨z₁, hz₁, hz₁2⟩ : ∃ z₁ ∈ S ⊓ K₁, orderOf z₁ = 2 := ⟨_, hz₀, hz₀2⟩
  have hz₁S : z₁ ∈ S := (mem_inf.mp hz₁).1
  have hz₁K : z₁ ∈ K₁ := (mem_inf.mp hz₁).2
  have hzy : y⁻¹ * z₁ * y ∈ K₂ := conj_mem_conjugate hz₁K y
  have heΩ : z₁⁻¹ * y⁻¹ * z₁ * y ∈ omegaOne (S ⊓ coreActionKernel L) := hyc z₁ hz₁S
  have heK : z₁⁻¹ * y⁻¹ * z₁ * y ∈ K₁ ⊔ K₂ := by
    rw [show z₁⁻¹ * y⁻¹ * z₁ * y = z₁⁻¹ * (y⁻¹ * z₁ * y) by group]
    exact mul_mem (mem_sup_left (inv_mem hz₁K)) (mem_sup_right hzy)
  have hq₁ : IsQuasisimple (K₁ ⧸ pPrimeCore 2 K₁) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K₁ _ hK₁u).mp hK₁p).2.2
  have hz₁Z : z₁ ∉ zStarIn K₁ := by
    rcases htype₁ with h | h
    · exact not_mem_zStarIn_of_lieModel_psl_two h hq₁ hz₁2
    · exact not_mem_zStarIn_of_lieModel_psl_two h hq₁ hz₁2
  have he1 : z₁⁻¹ * y⁻¹ * z₁ * y ≠ 1 := by
    intro h
    have h' : y⁻¹ * z₁ * y = z₁ := by
      calc y⁻¹ * z₁ * y = z₁ * (z₁⁻¹ * y⁻¹ * z₁ * y) := by group
        _ = z₁ := by rw [h, mul_one]
    have hzK₂ : z₁ ∈ K₂ := h' ▸ hzy
    exact hz₁Z (inf_le_zStarIn_of_ne hK₁u hK₂u hK₁p hK₂p hne (mem_inf.mpr ⟨hz₁K, hzK₂⟩))
  have het : z₁⁻¹ * y⁻¹ * z₁ * y ≠ t := by
    intro h
    apply hOut G u t K₁ hT₁ htype₁ z₁⁻¹ (inv_mem hz₁K)
    rw [show z₁⁻¹⁻¹ * t = y⁻¹ * z₁ * y by rw [← h]; group]
    exact GSThmB.B5a.le_coreActionKernel_of_ne hK₁u hK₂u hK₁p hK₂p hne hzy
  have heQ : z₁⁻¹ * y⁻¹ * z₁ * y ∈ S ⊓ coreActionKernel L := omegaOne_le _ heΩ
  have he2 : orderOf (z₁⁻¹ * y⁻¹ * z₁ * y) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hE.2 _ heΩ) he1
  have hinv := conj_eq_inv_of_setting hS hU hheld hSol hGW hMax hL34 hset heQ he2 het
  obtain ⟨hDN, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₁ hK₁u hK₁p
  obtain ⟨hDN₂, -⟩ := (solomon_involutions hSol hto hu2 htu).2 K₂ hK₂u hK₂p
  have hoddD : Odd (Nat.card D) := by
    have h1 : Nat.card D ∣ Nat.card (oddIn L) := card_dvd_of_le inf_le_left
    have hoddL : Odd (Nat.card (oddIn L)) := by
      rw [oddIn, card_map_of_injective (subtype_injective _)]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact hoddL.of_dvd_nat h1
  have hDK : D ≤ K₁ ⊔ K₂ :=
    le_of_conj_eq_inv heK (fun d hd => mem_normalizer_sup_of_normalizes (hDN (hYD hd))
      (hDN₂ (hYD hd))) (fun d hd => hinv d (mem_inf.mp hd).1) hoddD
  have hcomp : ∀ K₃ : Subgroup G, K₃ ≤ C → IsPComponent 2 (K₃.subgroupOf C) →
      ¬ ⁅K₃, D⁆ ≤ oddIn K₃ → K₃ = K₁ ∨ K₃ = K₂ := by
    intro K₃ hK₃u hK₃p hK₃n
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have hle : K₁ ⊔ K₂ ≤ coreActionKernel K₃ :=
      sup_le (GSThmB.B5a.le_coreActionKernel_of_ne hK₃u hK₁u hK₃p hK₁p h1)
        (GSThmB.B5a.le_coreActionKernel_of_ne hK₃u hK₂u hK₃p hK₂p h2)
    apply hK₃n
    rw [commutator_le]
    intro k hk d hd
    have hdK := hle (hDK hd)
    have h3 := (mem_coreActionKernel.mp (inv_mem hdK)).2 k⁻¹ (inv_mem hk)
    rw [inv_inv, inv_inv] at h3
    rwa [commutatorElement_def]
  set P := S ⊓ C ⊓ centralizer ({y} : Set G) with hP
  have hyP : y ∈ P := mem_inf.mpr ⟨mem_inf.mpr ⟨hyS, hyC⟩, mem_centralizer_singleton_iff.mpr rfl⟩
  have hPK : ∀ c ∈ P, conjugate K₁ c = K₁ ∨ conjugate K₁ c = K₂ := by
    intro c hc
    have hcS : c ∈ S := (mem_inf.mp (mem_inf.mp hc).1).1
    have hcu : c ∈ C := (mem_inf.mp (mem_inf.mp hc).1).2
    obtain ⟨hK₁cu, hK₁cp⟩ := GSThmB.Six.isPComponent_conjugate hK₁u hK₁p c
    have hCc : conjugate C c = C := conjugate_eq_of_mem_normalizer (le_normalizer hcu)
    rw [hCc] at hK₁cu hK₁cp
    refine hcomp _ hK₁cu hK₁cp ?_
    rw [commutator_le_oddIn_conjugate_iff (hconjD c hcS hcu)]
    exact hK₁n
  set D₁ := P ⊓ normalizer (K₁ : Set G) with hD₁
  have hsplit : ∀ c ∈ P, ∃ c₀ ∈ D₁, ∃ k : G, (k = 1 ∨ k = y) ∧ c = c₀ * k := by
    intro c hc
    rcases hPK c hc with h | h
    · exact ⟨c, mem_inf.mpr ⟨hc, mem_normalizer_of_conjugate_eq h⟩, 1, Or.inl rfl,
        (mul_one c).symm⟩
    · refine ⟨c * y⁻¹, mem_inf.mpr ⟨mul_mem hc (inv_mem hyP),
        mem_normalizer_of_conjugate_eq ?_⟩, y, Or.inr rfl, by group⟩
      rw [← conjugate_conjugate'', h, hK₂, conjugate_conjugate'', mul_inv_cancel]
      ext x
      simp [conjugate]
  have hyc' : ∀ c ∈ P, Commute y c := fun c hc =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2).symm
  have hD₁sq : ∀ r ∈ D₁, r * r ∈ coreActionKernel K₁ := by
    have hD₁2 : IsPGroup 2 D₁ := hS2.to_le (inf_le_left.trans (inf_le_left.trans inf_le_left))
    have hD₁le : D₁ ≤ normalizer (K₁ : Set G) ⊓ centralizer ({t} : Set G) := fun r hr =>
      mem_inf.mpr ⟨(mem_inf.mp hr).2, mem_centralizer_singleton_iff.mpr
        (hZS r (mem_inf.mp (mem_inf.mp (mem_inf.mp hr).1).1).1)⟩
    exact ((hL2 G u t K₁ D₁ hT₁ htype₁ hD₁2).1 hD₁le).1
  have hcommK : ∀ a ∈ D₁, ∀ b ∈ D₁, a⁻¹ * b⁻¹ * a * b ∈ coreActionKernel K₁ := by
    intro a ha b hb
    have haN : a ∈ normalizer (coreActionKernel K₁ : Set G) :=
      normalizer_le_normalizer_coreActionKernel K₁ (mem_inf.mp ha).2
    have h2 : a * (b * b)⁻¹ * a⁻¹ ∈ coreActionKernel K₁ :=
      (mem_normalizer_iff.mp haN _).mp (inv_mem (hD₁sq b hb))
    rw [show a⁻¹ * b⁻¹ * a * b = (a * a)⁻¹ * (a * (b * b)⁻¹ * a⁻¹) * (a * b * (a * b)) by
      group]
    exact mul_mem (mul_mem (inv_mem (hD₁sq a ha)) h2) (hD₁sq (a * b) (mul_mem ha hb))
  have hPcomm : ∀ a ∈ P, ∀ b ∈ P, a⁻¹ * b⁻¹ * a * b ∈ coreActionKernel K₁ := by
    intro a ha b hb
    obtain ⟨a₀, ha₀, k, hk, rfl⟩ := hsplit a ha
    obtain ⟨b₀, hb₀, k', hk', rfl⟩ := hsplit b hb
    have ha₀P : a₀ ∈ P := (mem_inf.mp ha₀).1
    have hb₀P : b₀ ∈ P := (mem_inf.mp hb₀).1
    have hkc : ∀ c ∈ P, Commute k c := by
      rcases hk with rfl | rfl
      · exact fun c _ => Commute.one_left c
      · exact hyc'
    have hk'c : ∀ c ∈ P, Commute k' c := by
      rcases hk' with rfl | rfl
      · exact fun c _ => Commute.one_left c
      · exact hyc'
    have hkk' : Commute k k' := by
      rcases hk' with rfl | rfl
      · exact Commute.one_right k
      · exact (hyc' k (by rcases hk with rfl | rfl; exact one_mem _; exact hyP)).symm
    rw [commutator_mul_commuting_eq (hkc a₀ ha₀P) (hkc b₀ hb₀P) (hk'c a₀ ha₀P)
      (hk'c b₀ hb₀P) hkk']
    exact hcommK a₀ ha₀ b₀ hb₀
  have hP'K : ⁅P, P⁆ ≤ coreActionKernel K₁ := by
    rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    simpa using hPcomm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)
  have hS₀P : S ⊓ L ⊓ C ≤ P := by
    intro s hs
    have hsS : s ∈ S := (mem_inf.mp (mem_inf.mp hs).1).1
    have hsL : s ∈ L := (mem_inf.mp (mem_inf.mp hs).1).2
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hsS, (mem_inf.mp hs).2⟩, mem_centralizer_singleton_iff.mpr
      (commute_of_mem_coreActionKernel hS2 hyS hyK hsS hsL).symm⟩
  have hwK : w ∈ coreActionKernel K₁ := hP'K (commutator_mono hS₀P hS₀P hwc)
  have hwQ : w ∈ S ⊓ coreActionKernel L := omegaOne_le _ hwΩ
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hE.2 w hwΩ) hw1
  exact not_mem_coreActionKernel_of_involution hS hU hheld hSol hGW hMax hL34 hset hu2 htu
    hK₁u hK₁p hK₁n hwQ hw2 hwK

end CFSG.ComponentClassification.GrSLit.GrS5
