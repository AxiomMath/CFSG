module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryCover
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open

theorem exists_su_cover
    {Λ : Type} [Group Λ] [Finite Λ] [Group.IsPerfect Λ]
    (hodd : Odd (Nat.card (Subgroup.center Λ))) {K : Type} [Field K] [Finite K] {m f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hm : 3 ≤ m) (hq : (m, 2 ^ f) ≠ (3, 2))
    (e : Λ ⧸ Subgroup.center Λ ≃* StatedProj (StatedSU m (2 ^ f) K)) :
    ∃ φ : StatedSU m (2 ^ f) K →* Λ, Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ f) K) ∧
      ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ f) K)).map φ = Subgroup.center Λ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := f * 2) (by rw [hK, pow_mul])
  obtain ⟨hsurj, hcen, hdvd⟩ := CFSG.SectionRank.EvenCover.pullbackFst_centralQuotientMap e
  obtain ⟨σ, hσ⟩ :=
    CFSG.AGLEmbedding.ToralCensus.statedSU_exists_section_of_odd hK hf hm hq hsurj hcen
      (Odd.of_dvd_nat hodd hdvd)
  exact CFSG.SectionRank.EvenCover.perfect_cover_map_of_section e σ hσ

theorem scalar_mem_statedSU {K : Type} [Field K] [Finite K] {m f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) {c : Kˣ} (hcm : c ^ m = 1) (hcq : c ^ (2 ^ f + 1) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin m) c ∈ StatedSU m (2 ^ f) K := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h1 : Matrix.GeneralLinearGroup.scalar (Fin 0) c = 1 := by
      apply Units.ext
      ext i j
      exact i.elim0
    rw [h1]
    exact Subgroup.one_mem _
  · exact (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK hm c).2 ⟨hcm, hcq⟩

theorem exists_orderOf_eq_of_dvd {K : Type} [Field K] [Finite K] {f r : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hr : r.Prime) (hrq : r ∣ 2 ^ f + 1) :
    ∃ c : Kˣ, orderOf c = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hcard : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by rw [Nat.card_units, hK]
  have hdvd : r ∣ Nat.card Kˣ := by
    rw [hcard]
    have h := Nat.sq_sub_sq (2 ^ f) 1
    rw [one_pow] at h
    rw [h]
    exact dvd_mul_of_dvd_left hrq _
  exact exists_prime_orderOf_dvd_card' r hdvd

theorem exists_su_cover_scalar_mem_ker
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn L) (hperf : Group.IsPerfect ↥L) {m f r : ℕ}
    (hr : r.Prime) (hrm : r ∣ m) (hrq : r ∣ 2 ^ f + 1)
    (hZ : ¬ r ∣ Nat.card (Subgroup.center ↥L))
    (hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU m 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (φ : StatedSU m (2 ^ f) K →* ↥L) (c : Kˣ)
      (hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈ StatedSU m (2 ^ f) K),
      Nat.card K = (2 ^ f) ^ 2 ∧ Function.Surjective φ ∧
      φ.ker ≤ (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ f) K) ∧
      orderOf c = r ∧ φ ⟨_, hc⟩ = 1 := by
  obtain ⟨⟨-, hf, hm, hq⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  letI := hKf
  letI := hKfin
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) :=
    CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.odd_card_center_of_isIrrOn hV hirr
  obtain ⟨φ, hφs, hφk, hφmap⟩ := exists_su_cover hodd hK hf hm hq e
  obtain ⟨c, hc_ord⟩ := exists_orderOf_eq_of_dvd hK hr hrq
  have hcm : c ^ m = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc_ord]
    exact hrm
  have hcq : c ^ (2 ^ f + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hc_ord]
    exact hrq
  have hc : Matrix.GeneralLinearGroup.scalar (Fin m) c ∈ StatedSU m (2 ^ f) K :=
    scalar_mem_statedSU hK hcm hcq
  have hs : (⟨_, hc⟩ : StatedSU m (2 ^ f) K) ∈
      (StatedScalars (Fin m) K).subgroupOf (StatedSU m (2 ^ f) K) :=
    Subgroup.mem_subgroupOf.mpr ⟨c, rfl⟩
  have hmem : φ ⟨_, hc⟩ ∈ Subgroup.center ↥L := by
    rw [← hφmap]
    exact Subgroup.mem_map_of_mem φ hs
  have hs_r : (⟨_, hc⟩ : StatedSU m (2 ^ f) K) ^ r = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, ← hc_ord, pow_orderOf_eq_one, map_one]
  have hφr : (φ ⟨_, hc⟩) ^ r = 1 := by
    rw [← map_pow, hs_r, map_one]
  have hdvd_r : orderOf (φ ⟨_, hc⟩) ∣ r := orderOf_dvd_of_pow_eq_one hφr
  have hdvd_Z : orderOf (φ ⟨_, hc⟩) ∣ Nat.card (Subgroup.center ↥L) := by
    have := orderOf_dvd_natCard (⟨φ ⟨_, hc⟩, hmem⟩ : Subgroup.center ↥L)
    simpa [Subgroup.orderOf_mk] using this
  have hφ1 : φ ⟨_, hc⟩ = 1 := by
    rcases (Nat.dvd_prime hr).1 hdvd_r with h1 | hr'
    · exact orderOf_eq_one_iff.1 h1
    · exact absurd (hr' ▸ hdvd_Z) hZ
  exact ⟨K, hKf, hKfin, φ, c, hc, hK, hφs, hφk, hc_ord, hφ1⟩

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
