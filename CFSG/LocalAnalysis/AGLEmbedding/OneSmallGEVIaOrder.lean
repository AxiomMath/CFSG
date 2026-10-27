module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem three_mul_card_le_of_lt {A B : Subgroup G} (hB : IsPGroup 3 B) (hAB : A ≤ B)
    (hne : A ≠ B) : 3 * Nat.card A ≤ Nat.card B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hb⟩ := hB.exists_card_eq
  have hdvd : Nat.card A ∣ 3 ^ b := hb ▸ Subgroup.card_dvd_of_le hAB
  obtain ⟨a, ha, hacard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hab : a < b := by
    rcases lt_or_eq_of_le ha with h | h
    · exact h
    · exfalso
      apply hne
      exact Subgroup.eq_of_le_of_card_ge hAB (by rw [hb, hacard, h])
  rw [hacard, hb]
  calc 3 * 3 ^ a = 3 ^ (a + 1) := by ring
    _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hab

theorem card_le_mul_card_rPart {M P R : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 3 P)
    (hRM : R ≤ M) (hR : IsPGroup 3 R) {z : G} (hzP : z ∈ P)
    (hPz : ∀ y ∈ P, y * z = z * y → y ∈ R) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hC : C ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hPM hzP⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {k : ℕ} (hk : (barM M P ⊓ C).relIndex (barM M P) ≤ k) :
    Nat.card P ≤ k * Nat.card (rPart M R C) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hle : barM M P ⊓ C ≤ barM M (rPart M R C) := by
    rintro x ⟨⟨⟨y, hyM⟩, hyP, rfl⟩, hxC⟩
    have hyP' : y ∈ P := Subgroup.mem_subgroupOf.mp hyP
    have hcomm : mk ⟨y, hyM⟩ * mk ⟨z, hPM hzP⟩ = mk ⟨z, hPM hzP⟩ * mk ⟨y, hyM⟩ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hC hxC)
    have h1 : mk (⟨y, hyM⟩ * ⟨z, hPM hzP⟩ * (⟨z, hPM hzP⟩ * ⟨y, hyM⟩)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm, mul_inv_cancel]
    have h2 := eq_one_of_mem_pCoreOf_two hp (by norm_num) hP
      (P.mul_mem (P.mul_mem hyP' hzP) (P.inv_mem (P.mul_mem hzP hyP')))
      (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    have hyz : y * z = z * y := by
      have := mul_inv_eq_one.mp h2
      simpa using this
    have hyR := hPz y hyP' hyz
    exact ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr ((mem_rPart hRM hyR).mpr hxC), rfl⟩
  have hRC : IsPGroup 3 (rPart M R C) := hR.to_le inf_le_left
  have hcardR : Nat.card (barM M (rPart M R C)) = Nat.card (rPart M R C) :=
    card_barM_of_isPGroup hp (by norm_num) (inf_le_left.trans hRM) hRC
  have hcardP : Nat.card (barM M P) = Nat.card P := card_barM_of_isPGroup hp (by norm_num) hPM hP
  have hmul : Nat.card (barM M P ⊓ C : Subgroup _) *
      (barM M P ⊓ C).relIndex (barM M P) = Nat.card (barM M P) := by
    have h1 := Subgroup.card_mul_index ((barM M P ⊓ C).subgroupOf (barM M P))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : barM M P ⊓ C ≤ barM M P)).toEquiv] at h1
  have hcle : Nat.card (barM M P ⊓ C : Subgroup _) ≤ Nat.card (rPart M R C) :=
    hcardR ▸ Subgroup.card_le_of_le hle
  calc Nat.card P = Nat.card (barM M P) := hcardP.symm
    _ = Nat.card (barM M P ⊓ C : Subgroup _) * (barM M P ⊓ C).relIndex (barM M P) := hmul.symm
    _ ≤ Nat.card (rPart M R C) * k := Nat.mul_le_mul hcle hk
    _ = k * Nat.card (rPart M R C) := mul_comm _ _

theorem three_mul_card_rPart_le {M R : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 3 R) {z : G}
    (hzR : z ∈ R) {C : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hzC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hRM hzR⟩ ∉ C) :
    3 * Nat.card (rPart M R C) ≤ Nat.card R :=
  three_mul_card_le_of_lt hR inf_le_left fun h =>
    hzC ((mem_rPart hRM hzR).mp (h.symm ▸ hzR))

theorem nine_mul_card_rPart_le {M R L : Subgroup G} (hRM : R ≤ M) (hR : IsPGroup 3 R) {r s : G}
    (hrR : r ∈ R) (hrL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hRM hrR⟩ ∈ barM M L)
    (hrC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨r, hRM hrR⟩ ∉
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hsR : s ∈ R) (hsr : s * r ≠ r * s) :
    9 * Nat.card (rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))) ≤
      Nat.card R := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set C := Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  set D := R ⊓ Subgroup.centralizer ({r} : Set G) with hD
  have hRD : rPart M R C ≤ D := by
    intro y hy
    have hyR : y ∈ R := hy.1
    have hyC : mk ⟨y, hRM hyR⟩ ∈ C := (mem_rPart hRM hyR).mp hy
    have hcomm : mk ⟨y, hRM hyR⟩ * mk ⟨r, hRM hrR⟩ = mk ⟨r, hRM hrR⟩ * mk ⟨y, hRM hyR⟩ :=
      (Subgroup.mem_centralizer_iff.mp hyC _ hrL).symm
    have h1 : mk (⟨y, hRM hyR⟩ * ⟨r, hRM hrR⟩ * (⟨r, hRM hrR⟩ * ⟨y, hRM hyR⟩)⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hcomm, mul_inv_cancel]
    have h2 := eq_one_of_mem_pCoreOf_two hp (by norm_num) hR
      (R.mul_mem (R.mul_mem hyR hrR) (R.inv_mem (R.mul_mem hrR hyR)))
      (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    have hyr : y * r = r * y := by
      have := mul_inv_eq_one.mp h2
      simpa using this
    exact ⟨hyR, Subgroup.mem_centralizer_singleton_iff.mpr hyr⟩
  have hDp : IsPGroup 3 D := hR.to_le inf_le_left
  have h1 : 3 * Nat.card (rPart M R C) ≤ Nat.card D :=
    three_mul_card_le_of_lt hDp hRD fun h => hrC ((mem_rPart hRM hrR).mp
      (h.symm ▸ (⟨hrR, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : r ∈ D)))
  have h2 : 3 * Nat.card D ≤ Nat.card R :=
    three_mul_card_le_of_lt hR inf_le_left fun h => hsr
      (Subgroup.mem_centralizer_singleton_iff.mp (h.symm ▸ hsR : s ∈ D).2)
  omega

end CFSG.AGLEmbedding
