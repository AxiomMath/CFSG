module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroChar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroAb
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroNoTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

omit [Finite G] in
theorem d1SmallLa_of_not (hL : ¬ (p = 3 ∧ IsLinThreeFour K)) : D1SmallLa p M H Rbar K :=
  fun h3 hK => absurd ⟨h3, hK⟩ hL

theorem D1OneSmallData.not_twoCore_inf_le (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hShape : KFactSmallSylowShape) (hOrb : KFactSmallOrbits)
    (hd : D1OneSmallData p P M H R Rbar K) {z : G} (hz : D1SmallCZElt p H R K z)
    (hB0 : D1CzB0 p R z) (hA6 : ¬ (p = 3 ∧ IsAltTwoP 3 K)) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hFi : ¬ (p = 5 ∧ IsFi22 K)) :
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) := by
  intro hQz
  have hp := hd.cfg.red.prime
  have hp2 := hd.cfg.red.ne_two
  obtain ⟨-, hdec⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hRC : R ≤ Subgroup.centralizer ({z} : Set G) := hd.le_centralizer_czElt hz
  have hzp1 : z ^ p = 1 := by rw [← hz.2.1]; exact pow_orderOf_eq_one z
  have hexpR : ∀ r ∈ R, r ^ p = 1 := by
    intro r hr
    obtain ⟨t, ht, i, rfl⟩ := hdec r hr
    have hc : Commute t (z ^ i) := Commute.pow_right
      (show Commute t z from Subgroup.mem_centralizer_singleton_iff.mp
        (hRC (d1LiftX_le p H R K ht))) i
    rw [hc.mul_pow, hd.pow_eq_one_of_mem_d1LiftX hExp ht, ← pow_mul, mul_comm, pow_mul, hzp1,
      one_pow, one_mul]
  obtain ⟨T₁, hT₁, hs, hnab, hc, hT₁nc, hΓ, -⟩ := hd.exists_sylow
  rcases hShape K hs hnab hc p hp hp2 T₁ hT₁nc hΓ hd.small with h2 | ⟨-, hZ⟩
  · have hcard : Nat.card ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup _) = p ^ 2 := by
      rw [← hT₁, Subgroup.card_map_of_injective K.subtype_injective, h2]
    exact hd.false_of_ab hOrb hz hB0 hQz hdec hexpR hFi
      (fun h => hA6 ⟨h.1, h.2.1⟩) hcard
  · exact hd.false_of_na hz hB0 hQz hdec hexpR hT₁ hZ

theorem D1OneSmallData.twoCore_inf_core_ne_bot (hOut : KFactSmallOutPPrime)
    (hExp : KFactSmallSylowExp) (hNo2 : KFactSmallNoTwo) (hShape : KFactSmallSylowShape)
    (hOrb : KFactSmallOrbits) (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hz : D1SmallCZElt p H R K z) (hB0 : D1CzB0 p R z) (hIso : D1CzIso p z K)
    (hA6 : ¬ (p = 3 ∧ IsAltTwoP 3 K)) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hFi : ¬ (p = 5 ∧ IsFi22 K)) :
    pCoreOf 2 M ⊓ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  have hnot := hd.not_twoCore_inf_le hOut hExp hShape hOrb hz hB0 hA6 hL hFi
  obtain ⟨hcardR, -⟩ := hd.card_le_and_decomp_of_b0 hOut hExp hz hB0 (d1SmallLa_of_not hL)
  have hcomm := hd.twoCore_comm_mem_core hNo2 hz hB0 hIso hFi hcardR
  intro hbot
  apply hnot
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hrM : r ∈ M := hd.cfg.ext.le_M hr
  have huQ : r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M hrM) _).mp
      ((pCoreOf 2 M).inv_mem hu.1)
  have hcQ : u * r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M := by
    have h := (pCoreOf 2 M).mul_mem hu.1 huQ
    simpa only [mul_assoc] using h
  have hc1 : u * r * u⁻¹ * r⁻¹ = 1 := by
    have hmem : u * r * u⁻¹ * r⁻¹ ∈
        pCoreOf 2 M ⊓ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) :=
      ⟨hcQ, hcomm u hu r hr⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  calc r * u = (u * r * u⁻¹ * r⁻¹)⁻¹ * (u * r) := by group
    _ = u * r := by rw [hc1, inv_one, one_mul]

theorem D1OneSmallData.glbPrimeCore_centralizer_le (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z) :
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ M :=
  intersecting_local_primeCore_le p hd.cfg.red.prime P hd.cfg.ext.sylow_le
    hd.cfg.ext.weakCore_le (hd.cfg.ext.three_le_pRank.trans
      (pRank_mono p hd.cfg.red.prime (le_inf (hd.le_centralizer_czElt hz) hd.cfg.ext.le_M)))

theorem D1OneSmallData.pCoreOf_two_glbPrimeCore_ne_bot (hd : D1OneSmallData p P M H R Rbar K)
    {z : G} (hz : D1SmallCZElt p H R K z)
    (hne : pCoreOf 2 M ⊓ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) ≠ ⊥ := by
  set O := GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) with hO
  have hOM : O ≤ M := hd.glbPrimeCore_centralizer_le hz
  have hle : pCoreOf 2 M ⊓ O ≤ pCoreOf 2 O := by
    refine normal_pGroup_le_pCoreOf 2 _ O inf_le_right ?_
      ((RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro o ho
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxQ, hxO⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M (hOM ho))
        x).mp hxQ, O.mul_mem (O.mul_mem ho hxO) (O.inv_mem ho)⟩
    · rintro ⟨hxQ, hxO⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M (hOM ho))
        x).mpr hxQ, ?_⟩
      have h := O.mul_mem (O.mul_mem (O.inv_mem ho) hxO) ho
      simpa [mul_assoc] using h
  intro hbot
  apply hne
  rw [eq_bot_iff, ← hbot]
  exact hle

end CFSG.AGLEmbedding
