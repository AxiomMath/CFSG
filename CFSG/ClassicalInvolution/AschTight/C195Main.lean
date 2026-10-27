module

public import CFSG.ClassicalInvolution.AschTight.C195
public import CFSG.ClassicalInvolution.AschTight.C195Wreath
public import CFSG.ClassicalInvolution.AschTight.E3StarD
public import CFSG.ClassicalInvolution.AschTight.WreathedData

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62 CFSG.ABGLocalTools
  CFSG.GorensteinWalter
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem mem_range_inl_of_le_of_ne (h62 : L6_2ModTmp p f) [IsSimpleGroup G]
    (ht : S19R.TightStd p f K z) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    {A R' J : Subgroup G} (hR' : R' ∈ RSet (CoreAssembly.conjClass K)) (hAR' : A ≤ R')
    (hAidx : A.relIndex R' = 2) (hJ : J ∈ CoreAssembly.conjClass K) (hR'J : R' ≤ J)
    (hJK : J ≠ K) (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) {a : G} (ha : a ∈ A)
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩ ∈
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := (isPGroup_of_mem_rSet hR').to_le hAR'
  rcases Nat.even_or_odd f with hfe | hfo
  swap
  · exact innerDiagonalTwo_of_odd hfo e hFcard hF h3 ⟨a, haN⟩ (isPGroup_zpowers_mk hA2 ha haN)
  have htb := ht.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hNC := normalizer_eq_centralizer_of_tight htb
  have hΩ := hypOmegaMod_of_tightD ht
  obtain ⟨g, rfl⟩ := CoreAssembly.single_class K J hJ
  have hJt : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hI.conj g
  have htz : g * z * g⁻¹ ≠ z := by
    intro h
    apply hJK
    rw [conjSub_eq_conjSub_of_tight htb (a := g) (b := 1) (by rw [h]; group)]
    exact conjSub_eq_self_of_mem K.one_mem
  have h8 := (exists_ne_comm_of_mem_rSet ht.branch.odd ht.branch.five ht.branch.member hR').2
  have hAcard : Nat.card R' = 2 * Nat.card A := by
    have h1 := Subgroup.relIndex_mul_card (H := A) (K := R')
    rw [inf_eq_left.mpr hAR', hAidx] at h1
    exact h1.symm
  have hAJ : A ≤ conjSub g K := hAR'.trans hR'J
  have htA : g * z * g⁻¹ ∈ A := mem_of_uniqueInvolution_of_pGroup hJt hAJ hA2 (by omega)
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 (le_inf hAJ hAz)
  have htwin : conjSub g K ∉ twinSet (CoreAssembly.conjClass K) K := by
    rintro ⟨-, z', hz'K, hz'J⟩
    exact htz ((hJt.eq hz'J).trans (hI.eq hz'K).symm)
  have hVcard : 4 ≤ Nat.card V := by
    have := Subgroup.card_le_of_le hAV
    omega
  have hVJ : V ≤ conjSub g K := hV.1.trans inf_le_left
  have hVz : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have htV : g * z * g⁻¹ ∈ V := hAV htA
  have hzt2 : Nat.card (Subgroup.zpowers (g * z * g⁻¹)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hJt.sq) hJt.ne_one
  rcases h62 ht.branch.odd ht.branch.five G _ hΩ K (CoreAssembly.mem_conjClass_self K) z hI
      (conjSub g K) hJ htwin (g * z * g⁻¹) hJt V hV htV with
    ⟨hV1, -⟩ | ⟨hV1, -⟩ | ⟨hVU, -, R₀, hR₀R, hR₀K, hVNR₀, hwr⟩ | ⟨hVR, -⟩
  · rw [hV1, hzt2] at hVcard
    omega
  · rw [hV1, hzt2] at hVcard
    omega
  ·
    obtain ⟨-, -, -, hVc, -⟩ := hVU
    have hsq := exists_mul_self_eq_of_isCyclic hJt hVJ hVc hV.2.1 hVcard
    have hR₀2 : IsPGroup 2 R₀ := isPGroup_of_mem_rSet hR₀R
    have hRJ : R₀ ⊓ conjSub g K = ⊥ := by
      by_contra hne
      have h2 : 2 ≤ Nat.card ↥(R₀ ⊓ conjSub g K) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      have hzR := mem_of_uniqueInvolution_of_pGroup hI (inf_le_left.trans hR₀K)
        (hR₀2.to_le inf_le_left) h2
      exact htz ((hJt.unique z hzR.2 hI.sq).resolve_left hI.ne_one).symm
    obtain ⟨B, hBab, hBcard, hBcomm⟩ := exists_abelian_of_isWreathed hVNR₀ hVJ hsq hwr
      (centralizer_le_normalizer_conjSub htb g) hRJ
    obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hA2 ⟨a, ha⟩
    exact mem_range_inl_of_centralizes ht.branch.odd ht.branch.five hfe e hFcard hF h3 hR₀R hR₀K
      hBab hBcard ⟨n, by rw [← hn, Subgroup.orderOf_mk]⟩ haN (hBcomm a (hAV ha))
  ·
    exfalso
    obtain ⟨J', hJ', P, hVP⟩ := hVR
    have hVJ' : V ≤ J' := hVP ▸ Subgroup.map_subtype_le _
    by_cases hJ'K : J' = K
    · exact htz ((hI.unique _ (hJ'K ▸ hVJ' htV) hJt.sq).resolve_left hJt.ne_one)
    · apply ht.edgeless K (CoreAssembly.mem_conjClass_self K) J' hJ'
      left
      refine ⟨hJ', hJ'K, V, ⟨J', hJ', P, hVP⟩, hVJ', ?_⟩
      rw [hNC]
      exact hVz

theorem mem_range_inl_of_mem_gen (h62 : L6_2ModTmp p f) [IsSimpleGroup G]
    (ht : S19R.TightStd p f K z) (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, GaloisField p f))
    (hFcard : Nat.card (GaloisField p f) = p ^ f)
    (hF : IsOddPrimePower (Nat.card (GaloisField p f))) (h3 : 3 < Nat.card (GaloisField p f))
    {A : Subgroup G}
    (hA : A ∈ RSet (CoreAssembly.conjClass K) ∨ A ∈ USet (CoreAssembly.conjClass K))
    (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) {a : G} (ha : a ∈ A)
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨a, haN⟩ ∈
      (SemidirectProduct.inl : PGL2 (GaloisField p f) →* PGammaL2 (GaloisField p f)).range := by
  have hNC := normalizer_eq_centralizer_of_tight ht.toTightBranch
  rcases hA with hR | hU
  · obtain ⟨J, hJ, Q, hAQ⟩ := id hR
    have hAJ : A ≤ J := hAQ ▸ Subgroup.map_subtype_le _
    by_cases hJK : J = K
    · exact normalizerToPGammaL2Mod_mem_range_inl_of_mem e hFcard hF h3 (hJK ▸ hAJ ha) haN
    · exfalso
      apply ht.edgeless K (CoreAssembly.mem_conjClass_self K) J hJ
      left
      exact ⟨hJ, hJK, A, hR, hAJ, hNC ▸ hAz⟩
  · obtain ⟨R', hR', hAR', -, hAidx⟩ := hU
    obtain ⟨J, hJ, Q, hR'Q⟩ := id hR'
    have hR'J : R' ≤ J := hR'Q ▸ Subgroup.map_subtype_le _
    by_cases hJK : J = K
    · exact normalizerToPGammaL2Mod_mem_range_inl_of_mem e hFcard hF h3 (hJK ▸ hR'J (hAR' ha))
        haN
    · exact mem_range_inl_of_le_of_ne h62 ht e hFcard hF h3 hR' hAR' hAidx hJ hR'J hJK hAz ha haN

variable (p f) in
theorem c19_5Tmp_of_l6_2 (h62 : L6_2ModTmp p f) : C19_5Tmp p f := by
  intro G _ _ _ K z ht e hFcard hF h3 x hx
  have hNC := normalizer_eq_centralizer_of_tight ht.toTightBranch
  have hle : xGroup K z ≤ (((SemidirectProduct.inl : PGL2 (GaloisField p f) →*
      PGammaL2 (GaloisField p f)).range).comap (normalizerToPGammaL2Mod e hFcard hF h3)).map
        (Subgroup.normalizer (K : Set G)).subtype := by
    refine iSup₂_le fun A hA a ha => ?_
    have haN : a ∈ Subgroup.normalizer (K : Set G) := hNC ▸ hA.2 ha
    exact ⟨⟨a, haN⟩, mem_range_inl_of_mem_gen h62 ht e hFcard hF h3 hA.1 hA.2 ha haN, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hle hx
  have hyx' : y = x := Subtype.ext hyx
  rw [← hyx']
  exact hy

end CFSG.ClassicalInvolution.Disconnected.AschTight
