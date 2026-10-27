module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaL34PU

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.normalizer_twoCore_inf_le (hUE : KFactUPrimeExc)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K)
    (hp3 : p = 3) (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H := by
  by_contra hN
  refine hd.false_of_l34_pu hUE hO hNO h93 hD2 hI hp3 hL hS fun C hCU hC1 hchar hHC => hN ?_
  have hNC : Subgroup.normalizer (C : Set G) = H :=
    hd.cfg.ext.maxTwoLocal_H.2 _
      ⟨C, hC1, (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)).to_le hCU,
        rfl⟩ hHC
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (H := pCoreOf 2 (H ⊓ M)) (C.subgroupOf (pCoreOf 2 (H ⊓ M)))
  rw [Subgroup.map_subgroupOf_eq_of_le hCU] at h1
  exact h1.trans hNC.le

omit [Finite G] in
theorem le_normalizer_inf_right_of_le {X H M : Subgroup G}
    (hX : H ⊓ M ≤ Subgroup.normalizer (X : Set G)) :
    H ⊓ M ≤ Subgroup.normalizer ((X ⊓ H : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.mp (hX hx) y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨h1.mp hy1, H.mul_mem (H.mul_mem hx.1 hy2) (H.inv_mem hx.1)⟩
  · rintro ⟨hy1, hy2⟩
    refine ⟨h1.mpr hy1, ?_⟩
    have := H.mul_mem (H.mul_mem (H.inv_mem hx.1) hy2) hx.1
    simpa [mul_assoc] using this

theorem pCoreOf_two_le_of_normalizer_le {M H : Subgroup G}
    (hNU : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H) :
    pCoreOf 2 M ≤ pCoreOf 2 (H ⊓ M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 M with hQ
  set U := pCoreOf 2 (H ⊓ M) with hU
  have hQp : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hUp : IsPGroup 2 U := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 (H ⊓ M)
  have hUM : U ≤ M := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 (H ⊓ M)).trans
    inf_le_right
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hHMU : H ⊓ M ≤ Subgroup.normalizer (U : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ M)
  set J := Q ⊔ U with hJ
  have hJp : IsPGroup 2 J := hQp.to_sup_of_normal_left' hUp (hUM.trans hMQ)
  have hJM : J ≤ M := sup_le (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M) hUM
  have hHMJ : H ⊓ M ≤ Subgroup.normalizer (J : Set G) := by
    intro x hx
    have hxQ := hMQ hx.2
    have hxU := hHMU hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hxQ hxU ⊢
    rw [hJ, Subgroup.map_sup, hxQ, hxU]
  have hJH : J ⊓ H ≤ U :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (fun x hx => ⟨hx.2, hJM hx.1⟩) (le_normalizer_inf_right_of_le hHMJ) (hJp.to_le inf_le_left)
  have hnc : NormalizerCondition J := by
    have := (hJp.isNilpotent)
    exact Group.normalizerCondition_of_isNilpotent
  have hself : Subgroup.normalizer (U.subgroupOf J : Set J) = U.subgroupOf J := by
    refine le_antisymm (fun x hx => ?_) Subgroup.le_normalizer
    have hxN : (x : G) ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨u, (le_sup_right : U ≤ J) hu⟩).mp
          (Subgroup.mem_subgroupOf.mpr hu)
        simpa using Subgroup.mem_subgroupOf.mp h1
      · intro hu
        have huJ : u ∈ J := by
          have h2 : (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * (x : G) ∈ J :=
            J.mul_mem (J.mul_mem (J.inv_mem x.2) ((le_sup_right : U ≤ J) hu)) x.2
          simpa [mul_assoc] using h2
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨u, huJ⟩).mpr
          (Subgroup.mem_subgroupOf.mpr (by simpa using hu))
        exact Subgroup.mem_subgroupOf.mp h1
    exact Subgroup.mem_subgroupOf.mpr (hJH ⟨x.2, hNU hxN⟩)
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.mp hnc _ hself
  intro q hq
  have hqJ : q ∈ J := (le_sup_left : Q ≤ J) hq
  have : (⟨q, hqJ⟩ : J) ∈ U.subgroupOf J := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem D1OneSmallData.normalizer_twoCore_inf_eq (hUE : KFactUPrimeExc)
    (hO : KFactSmallThreeOrders) (hNO : KFactL34NotOrthogonal) (h93 : Asc81bNineThree)
    (hD2 : D1NoXBlock) (hd : D1OneSmallData p P M H R Rbar K) (hI : D1SmallIa p H K)
    (hp3 : p = 3) (hL : IsLinThreeFour K) (hS : pCoreOf 2 (H ⊓ M) ≠ pCoreOf 2 H) :
    Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M ∧
      M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M ∧
      pCoreOf 2 (M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G)) = pCoreOf 2 (H ⊓ M) ∧
      pCoreOf 2 M ≤ pCoreOf 2 (H ⊓ M) := by
  have hNH := hd.normalizer_twoCore_inf_le hUE hO hNO h93 hD2 hI hp3 hL hS
  have hNHM := hd.inf_normalizer_twoCore_inf hUE hp3 hL hS
  have hN : Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M :=
    (inf_eq_right.mpr hNH).symm.trans hNHM
  have hNM : M ⊓ Subgroup.normalizer (pCoreOf 2 (H ⊓ M) : Set G) = H ⊓ M := by
    rw [hN, inf_comm, inf_assoc, inf_idem]
  exact ⟨hN, hNM, by rw [hNM], pCoreOf_two_le_of_normalizer_le hNH⟩

end CFSG.AGLEmbedding
