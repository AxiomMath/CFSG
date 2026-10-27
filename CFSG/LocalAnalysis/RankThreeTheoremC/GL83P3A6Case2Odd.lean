module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Core
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6SylowProved
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Core

variable {G : Type} [Group G] [Finite G]

theorem a6_odd_involution (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hKA : KFactA6TwoNormalized) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G}
    (hJ : IsA6Normal M x J) :
    ∀ w ∈ GLBPrimeCore 3 M, w ^ 2 = 1 → w * x = x * w → w = 1 := by
  classical
  haveI hf3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA1 : A6SylowData := a6SylowData_proved
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup G := GLBPrimeCore 3 M with hO
  set D : Subgroup G := (P : Subgroup G) ⊓ J with hD
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hJC : J ≤ C := hJ.le_centralizer
  have hDM : D ≤ M := inf_le_left.trans hPM
  have hDC : D ≤ C := inf_le_right.trans hJC
  have hD3 : IsPGroup 3 D := P.isPGroup'.to_le inf_le_left
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  set Z : Subgroup G := O ⊓ C with hZ
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h =>
    hO3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hDZ : D ≤ normalizer (Z : Set G) := by
    intro d hd
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 := mem_normalizer_iff.mp (le_normalizer_glbPrimeCore 3 M (hDM hd)) z
    have h2 := mem_normalizer_iff.mp (Subgroup.le_normalizer (hDC hd)) z
    rw [hZ, mem_inf, mem_inf, ← h1, ← h2]
  obtain ⟨S, hSsyl, hDS⟩ := GL83P3A6Syl.exists_invariant_sylow_two hD3 hZ3 hDZ
  have hSZ : S ≤ Z := hSsyl.le
  have hSC : S ≤ C := hSZ.trans inf_le_right
  have hS2 : IsPGroup 2 S := hSsyl.isPGroup
  obtain ⟨hKtn, hKtc, hKtA6⟩ := a6_quot_data hS hU0 hp hM hgen hJ
  have hTt : IsSylowOf 3 (l34Img x J D) (l34Img x J J) :=
    (a6_T_data hS hU0 hA1 hp hM hgen hJ).1
  have hSt2 : IsPGroup 2 (l34Img x J S) := (hS2.comap_subtype (K := C)).map _
  have hTtN : l34Img x J D ≤
      normalizer ((l34Img x J S : Subgroup (L34Quot x J)) : Set (L34Quot x J)) := by
    rintro _ ⟨⟨d, hdC⟩, hd, rfl⟩
    have hd' : d ∈ D := Subgroup.mem_subgroupOf.mp hd
    apply mem_normalizer_of_map_le
    rintro _ ⟨σ, ⟨⟨s, hsC⟩, hs, rfl⟩, rfl⟩
    have hs' : s ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hdsd : d * s * d⁻¹ ∈ S := (mem_normalizer_iff.mp (hDS hd') s).mp hs'
    refine ⟨⟨d * s * d⁻¹, C.mul_mem (C.mul_mem hdC hsC) (C.inv_mem hdC)⟩,
      Subgroup.mem_subgroupOf.mpr hdsd, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hSt : l34Img x J S = ⊥ :=
    hKA (L34Quot x J) (l34Img x J J) hKtn hKtc hKtA6 (l34Img x J D) hTt (l34Img x J S) hSt2 hTtN
  have hDred : IsPGroup 3 (reducedCentralizerOfJ x J) :=
    a6_reducedCentralizer_isPGroup hS hU0 hA1 hp hM hgen hJ
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hp hM hgen.2.2.2.ge hgen.2.1.2.2.2.2
  have hSbot : S = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    have hsC := hSC hs
    have himg : l34Hom x J ⟨s, hsC⟩ ∈ l34Img x J S :=
      ⟨⟨s, hsC⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hSt, Subgroup.mem_bot] at himg
    set ψ₁ : ↥C →* GenericReduced 3 x :=
      QuotientGroup.mk' (primeComplementCore (G := C) 3) with hψ₁
    have hyD : ψ₁ ⟨s, hsC⟩ ∈ reducedCentralizerOfJ x J := by
      have h1 : (QuotientGroup.mk' (reducedCentralizerOfJ x J).normalCore) (ψ₁ ⟨s, hsC⟩) = 1 :=
        himg
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact normalCore_le _ h1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hDred) ⟨ψ₁ ⟨s, hsC⟩, hyD⟩
    have hk' : orderOf (ψ₁ ⟨s, hsC⟩) = 3 ^ k := by
      rw [← hk, Subgroup.orderOf_mk]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨s, hs⟩
    have hdvd : orderOf (ψ₁ ⟨s, hsC⟩) ∣ 2 ^ m := by
      have := orderOf_map_dvd ψ₁ (⟨s, hsC⟩ : C)
      have e : orderOf (⟨s, hsC⟩ : C) = 2 ^ m := by
        rw [← hm, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      rwa [e] at this
    have hk0 : k = 0 := by
      by_contra hne
      rw [hk'] at hdvd
      have : 3 ∣ 2 ^ m := (dvd_pow_self 3 hne).trans hdvd
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    have hy1 : ψ₁ ⟨s, hsC⟩ = 1 := by
      rw [hk0, pow_zero] at hk'
      exact orderOf_eq_one_iff.mp hk'
    have hsO : (⟨s, hsC⟩ : C) ∈ primeComplementCore (G := C) 3 := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := C) 3), MonoidHom.mem_ker]
      exact hy1
    have hsGLB : s ∈ GLBPrimeCore 3 C :=
      (CFSG.AGLEmbedding.mem_primeComplementCore_iff_mem_glbPrimeCore 3 _).mp hsO
    have hsP : s ∈ CFSG.ABGTheoremB.pPrimeCoreIn 3 C := glbPrimeCore_le_pPrimeCoreIn 3 C hsGLB
    have hdvd2 : orderOf s ∣ Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn 3 C) := by
      have := orderOf_dvd_natCard (⟨s, hsP⟩ : CFSG.ABGTheoremB.pPrimeCoreIn 3 C)
      rwa [Subgroup.orderOf_mk] at this
    have hos : orderOf s = 2 ^ m := by
      rw [← hm, Subgroup.orderOf_mk]
    have hm0 : m = 0 := by
      by_contra hne
      exact hodd ((dvd_pow_self 2 hne).trans (hos ▸ hdvd2))
    rw [hm0, pow_zero] at hos
    exact orderOf_eq_one_iff.mp hos
  have hZodd : ¬ 2 ∣ Nat.card Z := by
    intro h2
    have hcard := hSsyl.card_eq
    rw [hSbot, Subgroup.card_bot] at hcard
    have hpos : 0 < (Nat.card Z).factorization 2 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos).ne' h2)
    have : 2 ^ (Nat.card Z).factorization 2 ≠ 1 := by
      exact (Nat.one_lt_pow hpos.ne' (by norm_num)).ne'
    exact this hcard.symm
  intro w hwO hw2 hwx
  by_contra hw1
  apply hZodd
  have hwC : w ∈ C := mem_centralizer_singleton_iff.mpr hwx
  have hwZ : w ∈ Z := ⟨hwO, hwC⟩
  have hord : orderOf w = 2 := orderOf_eq_prime hw2 hw1
  have := orderOf_dvd_natCard (⟨w, hwZ⟩ : Z)
  rwa [Subgroup.orderOf_mk, hord] at this

end CFSG.LocalAnalysis.RankThreeTheoremC
