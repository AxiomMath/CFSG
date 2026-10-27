module

public import CFSG.LocalAnalysis.OddStandard.MathieuInvolutionCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.MathieuOddCoreTransport

public section

namespace CFSG.OddStandard

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native

theorem m11_innerRecordsValid :
    InnerClassRecordsValid NativeSporadic.M11 m11Records := by
  have hn : (11 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m11Certificate := m11Certificate_check.1
  have hA : m11gA ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11a.2
  have hB : m11gB ∈ m11Certificate.originalSubgroup := by
    rw [m11Certificate_originalSubgroup]; exact m11b.2
  have hcardG : Nat.card m11Certificate.originalSubgroup = 7920 := by
    rw [m11Certificate_originalSubgroup]; exact m11_card
  obtain ⟨hok, hsz, -⟩ := m11_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m11_rep_data
  obtain ⟨hc, hco, -, -⟩ := m11_oddcore_cent1
  rw [← m11Certificate_originalSubgroup]
  refine innerRecordsValid_of_checks hn m11Certificate hQ hA hB m11Records 400 hok hsz ?_
  intro r hr'
  simp only [m11Records, List.mem_singleton] at hr'
  subst hr'
  have hcg : m11CentQ1.originalSubgroup =
      Subgroup.closure {g | g ∈ m11Rec1.centralizerGenerators} := by
    rw [m11CentQ1, certificate_originalSubgroup]; rfl
  refine ⟨hr, hro, m11CentQ1, hc, hcg, hK, hco, ?_, ?_⟩
  · show 165 * 48 = _
    rw [hcardG]
  · exact oddCoreRowsValid_of_check_card hn m11CentQ1 hc hcg (by decide)
      (by rw [← m11CentQ1.orderCertificate_eq_card hc, hco])
      (by simp [Nat.primeFactors, m11Primes1]) m11Specs1 2000 (by decide) m11_rows1_check


theorem m12_innerRecordsValid :
    InnerClassRecordsValid NativeSporadic.M12 m12Records := by
  have hn : (12 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m12Certificate := m12Certificate_check
  have hA : m12gA ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hB : m12gB ∈ m12Certificate.originalSubgroup := m12_gens_mem _ (by simp)
  have hcardG : Nat.card m12Certificate.originalSubgroup = 95040 := by
    rw [m12Certificate_originalSubgroup]; exact m12_card
  obtain ⟨hok, hsz, -⟩ := m12_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m12_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m12_rep_data2
  obtain ⟨hc1, hco1, -, -⟩ := m12_oddcore_cent1
  obtain ⟨hc2, hco2, -, -⟩ := m12_oddcore_cent2
  rw [← m12Certificate_originalSubgroup]
  refine innerRecordsValid_of_checks hn m12Certificate hQ hA hB m12Records 1000 hok hsz ?_
  intro r hr'
  have hcg1 : m12CentQ1.originalSubgroup =
      Subgroup.closure {g | g ∈ m12Rec1.centralizerGenerators} := by
    rw [m12CentQ1, certificate_originalSubgroup]; rfl
  have hcg2 : m12CentQ2.originalSubgroup =
      Subgroup.closure {g | g ∈ m12Rec2.centralizerGenerators} := by
    rw [m12CentQ2, certificate_originalSubgroup]; rfl
  simp only [m12Records, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨hr1, hro1, m12CentQ1, hc1, hcg1, hK1, hco1, ?_, ?_⟩
    · show 495 * 192 = _
      rw [hcardG]
    · exact oddCoreRowsValid_of_check_card hn m12CentQ1 hc1 hcg1 (by decide)
        (by rw [← m12CentQ1.orderCertificate_eq_card hc1, hco1])
        (by simp [Nat.primeFactors, m12Primes1]) m12Specs1 2000 (by decide) m12_rows1_check
  · refine ⟨hr2, hro2, m12CentQ2, hc2, hcg2, hK2, hco2, ?_, ?_⟩
    · show 396 * 240 = _
      rw [hcardG]
    · exact oddCoreRowsValid_of_check_card hn m12CentQ2 hc2 hcg2 (by decide)
        (by rw [← m12CentQ2.orderCertificate_eq_card hc2, hco2])
        (by simp [Nat.primeFactors, m12Primes2]) m12Specs2 2000 (by decide) m12_rows2_check

theorem m22_innerRecordsValid :
    InnerClassRecordsValid NativeSporadic.M22 m22Records := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hcardG : Nat.card m22Certificate.originalSubgroup = 443520 := by
    rw [m22Certificate_originalSubgroup]; exact m22_card
  obtain ⟨hok, hsz, -⟩ := m22_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m22_rep_data1
  obtain ⟨hc, hco, -, -⟩ := m22_oddcore_cent1
  rw [← m22Certificate_originalSubgroup]
  refine innerRecordsValid_of_checks hn m22Certificate hQ hA hB m22Records 2000 hok hsz ?_
  intro r hr'
  simp only [m22Records, List.mem_singleton] at hr'
  subst hr'
  have hcg : m22CentQ1.originalSubgroup =
      Subgroup.closure {g | g ∈ m22Rec1.centralizerGenerators} := by
    rw [m22CentQ1, certificate_originalSubgroup]; rfl
  refine ⟨hr, hro, m22CentQ1, hc, hcg, hK, hco, ?_, ?_⟩
  · show 1155 * 384 = _
    rw [hcardG]
  · exact oddCoreRowsValid_of_check_card hn m22CentQ1 hc hcg (by decide)
      (by rw [← m22CentQ1.orderCertificate_eq_card hc, hco])
      (by simp [Nat.primeFactors, m22Primes1]) m22Specs1 2000 (by decide) m22_rows1_check

theorem m23_innerRecordsValid :
    InnerClassRecordsValid NativeSporadic.M23 m23Records := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hcardG : Nat.card m23Certificate.originalSubgroup = 10200960 := by
    rw [m23Certificate_originalSubgroup]; exact m23_card
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr, hro, hK, hKc, -⟩ := m23_rep_data1
  obtain ⟨hc, hco, -, -⟩ := m23_oddcore_cent1
  rw [← m23Certificate_originalSubgroup]
  refine innerRecordsValid_of_checks hn m23Certificate hQ hA hB m23Records 4000 hok hsz ?_
  intro r hr'
  simp only [m23Records, List.mem_singleton] at hr'
  subst hr'
  have hcg : m23CentQ1.originalSubgroup =
      Subgroup.closure {g | g ∈ m23Rec1.centralizerGenerators} := by
    rw [m23CentQ1, certificate_originalSubgroup]; rfl
  refine ⟨hr, hro, m23CentQ1, hc, hcg, hK, hco, ?_, ?_⟩
  · show 3795 * 2688 = _
    rw [hcardG]
  · exact oddCoreRowsValid_of_check_card hn m23CentQ1 hc hcg (by decide)
      (by rw [← m23CentQ1.orderCertificate_eq_card hc, hco])
      (by simp [Nat.primeFactors, m23Primes1]) m23Specs1 2000 (by decide) m23_rows1_check

theorem m24_innerRecordsValid_checked :
    InnerClassRecordsValid NativeSporadic.M24 [m24Rec1, m24Rec2] := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m24Certificate := m24Certificate_check
  have hA : m24gA ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hB : m24gB ∈ m24Certificate.originalSubgroup := m24_gens_mem _ (by simp)
  have hcardG : Nat.card m24Certificate.originalSubgroup = 244823040 := by
    rw [m24Certificate_originalSubgroup]; exact m24_card
  obtain ⟨hok, hsz, -⟩ := m24_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m24_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m24_rep_data2
  obtain ⟨hc1, hco1, -, -⟩ := m24_oddcore_cent1
  obtain ⟨hc2, hco2, -, -⟩ := m24_oddcore_cent2
  rw [← m24Certificate_originalSubgroup]
  refine innerRecordsValid_of_checks hn m24Certificate hQ hA hB [m24Rec1, m24Rec2] 40000 hok hsz ?_
  intro r hr'
  have hcg1 : m24CentQ1.originalSubgroup =
      Subgroup.closure {g | g ∈ m24Rec1.centralizerGenerators} := by
    rw [m24CentQ1, certificate_originalSubgroup]; rfl
  have hcg2 : m24CentQ2.originalSubgroup =
      Subgroup.closure {g | g ∈ m24Rec2.centralizerGenerators} := by
    rw [m24CentQ2, certificate_originalSubgroup]; rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl
  · refine ⟨hr1, hro1, m24CentQ1, hc1, hcg1, hK1, hco1, ?_, ?_⟩
    · show 31878 * 7680 = _
      rw [hcardG]
    · exact oddCoreRowsValid_of_check_card hn m24CentQ1 hc1 hcg1 (by decide)
        (by rw [← m24CentQ1.orderCertificate_eq_card hc1, hco1])
        (by simp [Nat.primeFactors, m24Primes1]) m24Specs1 2000 (by decide) m24_rows1_check
  · refine ⟨hr2, hro2, m24CentQ2, hc2, hcg2, hK2, hco2, ?_, ?_⟩
    · show 11385 * 21504 = _
      rw [hcardG]
    · exact oddCoreRowsValid_of_check_card hn m24CentQ2 hc2 hcg2 (by decide)
        (by rw [← m24CentQ2.orderCertificate_eq_card hc2, hco2])
        (by simp [Nat.primeFactors, m24Primes2]) m24Specs2 2000 (by decide) m24_rows2_check

theorem m24_innerRecordsValid :
    InnerClassRecordsValid NativeSporadic.M24 m24Records :=
  m24_innerRecordsValid_checked.of_perm (List.Perm.swap _ _ _)


theorem ctuc_mathieu_inner_involution_centralizer_odd_core_trivial :
    MathieuInnerStatement NativeSporadic.M11 [(165, 48)] ∧
    MathieuInnerStatement NativeSporadic.M12 [(495, 192), (396, 240)] ∧
    MathieuInnerStatement NativeSporadic.M22 [(1155, 384)] ∧
    MathieuInnerStatement NativeSporadic.M23 [(3795, 2688)] ∧
    MathieuInnerStatement NativeSporadic.M24 [(11385, 21504), (31878, 7680)] :=
  ⟨mathieuInnerStatement_of_recordsValid rfl m11_innerRecordsValid,
    mathieuInnerStatement_of_recordsValid rfl m12_innerRecordsValid,
    mathieuInnerStatement_of_recordsValid rfl m22_innerRecordsValid,
    mathieuInnerStatement_of_recordsValid rfl m23_innerRecordsValid,
    mathieuInnerStatement_of_recordsValid rfl m24_innerRecordsValid⟩

theorem ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_carrier
    (s : TauCeti.SporadicName) (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24)
    (t : NativeSporadic.Carrier s) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set (NativeSporadic.Carrier s))) = ⊥ := by
  obtain ⟨h11, h12, h22, h23, h24⟩ := ctuc_mathieu_inner_involution_centralizer_odd_core_trivial
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · exact h11.2 t ht
  · exact h12.2 t ht
  · exact h22.2 t ht
  · exact h23.2 t ht
  · exact h24.2 t ht


theorem ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_of_isSporadic
    {G : Type} [Group G] (s : TauCeti.SporadicName)
    (hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24)
    (hG : NativeSporadic.IsSporadic G s) (t : G) (ht : orderOf t = 2) :
    CFSG.oddCore (Subgroup.centralizer ({t} : Set G)) = ⊥ := by
  obtain ⟨e⟩ := hG
  exact inner_of_equiv e
    (fun u hu => ctuc_mathieu_inner_involution_centralizer_odd_core_trivial_carrier s hs u hu) t ht

end CFSG.OddStandard
