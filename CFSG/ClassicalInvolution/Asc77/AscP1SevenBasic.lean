module

public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem uniqueInvolution_mem_W (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K)
    {z : G} (hz : IsUniqueInvolution K z) : z ∈ K ⊓ W := by
  have hinfo := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  have hKW : K ⊓ W ≤ K := inf_le_left
  have hA2 : IsPGroup 2 ↥(K ⊓ W) := (isPGroup_of_mem_WSet hW).to_inf_right
  have hcard : 2 ≤ Nat.card ↥(K ⊓ W) := by
    have := hinfo.2.2.2.1
    rw [← hinfo.1]
    omega
  exact T3.mem_of_isPGroup hz hKW hA2 hcard

theorem inf_W_le_normalizer_left (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    K ⊓ W ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨zJ, hzJ⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hzW : zJ ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hzJ
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hinfo := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  refine hΩ.le_normalizer_of_le_centralizer hp hq hJ hK (Ne.symm hKJ) hzJ inf_le_left
    (isPGroup_of_mem_WSet hW).to_inf_right ?_ ?_
  · have := hinfo.2.2.2.1
    rw [← hinfo.1]
    omega
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hWab x hx.2 zJ hzW.2

theorem inf_W_le_normalizer_of_ne (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    K ⊓ W ≤ Subgroup.normalizer (J : Set G) ∧ J ⊓ W ≤ Subgroup.normalizer (K : Set G) :=
  ⟨inf_W_le_normalizer_left hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ,
    inf_W_le_normalizer_left hp hq hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK⟩

theorem mem_omegaStarNbr_of_inf_W (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) :
    J ∈ omegaStarNbr Ω K ∧ K ∈ omegaStarNbr Ω J := by
  have hN := inf_W_le_normalizer_of_ne hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ
  have hKU := (inf_W_of_mem_D hp hq hΩ hW hR hK hRK).2.1
  have hJU := (inf_W_of_mem_D hp hq hΩ hW hT hJ hTJ).2.1
  exact ⟨⟨hJ, Ne.symm hKJ, J ⊓ W, hJU, inf_le_left, hN.2⟩,
    ⟨hK, hKJ, K ⊓ W, hKU, inf_le_left, hN.1⟩⟩

theorem comm_mem_inf_W (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) : r * v * r⁻¹ * v⁻¹ ∈ K ⊓ W := by
  have hN := (inf_W_le_normalizer_of_ne hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ).2 hv
  have hrK : r ∈ K := hRK.1 hr
  refine ⟨?_, ?_⟩
  · have h1 : v * r⁻¹ * v⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hN r⁻¹).mp (K.inv_mem hrK)
    have : r * v * r⁻¹ * v⁻¹ = r * (v * r⁻¹ * v⁻¹) := by group
    rw [this]
    exact K.mul_mem hrK h1
  · have h1 := comm_mem_of_mem hv.2 (hR.2 hr)
    have e : r * v * r⁻¹ * v⁻¹ = (v * r * v⁻¹ * r⁻¹)⁻¹ := by group
    rw [e]
    exact W.inv_mem h1

theorem conj_mem_of_mem_inf_W (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    {r v : G} (hr : r ∈ R) (hv : v ∈ J ⊓ W) : v * r * v⁻¹ ∈ R := by
  have hc := comm_mem_inf_W hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hr hv
  have hinfo := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  have hcR : r * v * r⁻¹ * v⁻¹ ∈ R := (hinfo.1 ▸ hc : r * v * r⁻¹ * v⁻¹ ∈ R ⊓ W).1
  have e : v * r * v⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ * r := by group
  rw [e]
  exact R.mul_mem (R.inv_mem hcR) hr

end Thompson

end CFSG.ClassicalInvolution.Asc77
