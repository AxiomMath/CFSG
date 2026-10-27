module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenCube
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem ne_and_not_omegaNbr_of_noncomm (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W)
    (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) {r t : G} (hr : r ∈ R) (ht : t ∈ T)
    (hrW : r ∉ W) (htW : t ∉ W)
    (hnc : piG W r * piG W t ≠ piG W t * piG W r) : K ≠ J ∧ J ∉ omegaNbr Ω K := by
  have hKJ : K ≠ J := by
    intro h
    subst h
    exact hnc (piG_comm_of_le hp hq hΩ hW hR hT (hkey R hR T hT K hK hRK.1 hTJ.1) hr ht hrW htW)
  exact ⟨hKJ, fun hnbr => hnc (piG_comm_of_mem_omegaNbr h62 hp hq hΩ hW hkey hK hJ hKJ hR hT hRK
    hTJ hnbr hr ht hrW)⟩

theorem piG_comm_third (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J L R T S : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hL : L ∈ Ω) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hS : S ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hSL : IsSylow2In S L) {r t s : G} (hr : r ∈ R) (ht : t ∈ T) (hs : s ∈ S) (hrW : r ∉ W)
    (htW : t ∉ W) (hsW : s ∉ W)
    (hrt : piG W r * piG W t ≠ piG W t * piG W r)
    (hsr : piG W s * piG W r ≠ piG W r * piG W s)
    (hst : piG W s * piG W t ≠ piG W t * piG W s) :
    piG W s * piG W (r * t * r⁻¹) = piG W (r * t * r⁻¹) * piG W s := by
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  obtain ⟨hKJ, hnotJK⟩ := ne_and_not_omegaNbr_of_noncomm h62 hp hq hΩ hW hkey hK hJ hR hT hRK hTJ
    hr ht hrW htW hrt
  obtain ⟨hLK, hnotKL⟩ := ne_and_not_omegaNbr_of_noncomm h62 hp hq hΩ hW hkey hL hK hS hR hSL hRK
    hs hr hsW hrW hsr
  obtain ⟨hLJ, hnotJL⟩ := ne_and_not_omegaNbr_of_noncomm h62 hp hq hΩ hW hkey hL hJ hS hT hSL hTJ
    hs ht hsW htW hst
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  obtain ⟨ℓ, hℓ⟩ := hΩ.exists_uniqueInvolution hp hq hL
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hj
  have hℓW : ℓ ∈ L ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hL hS hSL hℓ
  have hrj := conj_involution_eq_mul h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnotJK hz hj hr hrW
  have hsz := conj_involution_eq_mul h62 hp hq hΩ hW hL hK hLK hS hR hSL hRK hnotKL hℓ hz hs hsW
  have hsj := conj_involution_eq_mul h62 hp hq hΩ hW hL hJ hLJ hS hT hSL hTJ hnotJL hℓ hj hs hsW
  have hszj : s * (z * j) = (z * j) * s := by
    have h1 : s * (z * j) * s⁻¹ = z * j := by
      calc s * (z * j) * s⁻¹ = (s * z * s⁻¹) * (s * j * s⁻¹) := by group
        _ = (ℓ * z) * (ℓ * j) := by rw [hsz, hsj]
        _ = ℓ * (z * ℓ) * j := by group
        _ = ℓ * (ℓ * z) * j := by rw [hWab z hzW.2 ℓ hℓW.2]
        _ = (ℓ * ℓ) * (z * j) := by group
        _ = z * j := by rw [hℓ.sq, one_mul]
    calc s * (z * j) = (s * (z * j) * s⁻¹) * s := by group
      _ = (z * j) * s := by rw [h1]
  have hzjW : z * j ∈ W := W.mul_mem hzW.2 hjW.2
  have hSc := le_centralizer_of_mem hp hq hΩ hW hS hs hsW hzjW hszj
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := hS.2 hs
  have hP : conjSub r T ∈ DSet Ω W := conjSub_mem_D hΩ hT hrN
  have hKP : conjSub r J ∈ Ω := hΩ.conjInvariant r J hJ
  have hPKP : IsSylow2In (conjSub r T) (conjSub r J) := hTJ.conj r
  have hzP : IsUniqueInvolution (conjSub r J) (z * j) := hrj ▸ hj.conj r
  have hrtP : r * t * r⁻¹ ∈ conjSub r T := conj_mem_conjSub ht
  have hrtW : r * t * r⁻¹ ∉ W := fun h => htW ((mem_normalizer_iff_of_mem hrN t).mp h)
  by_cases hLP : L = conjSub r J
  · subst hLP
    have hle := hkey (conjSub r T) hP S hS (conjSub r J) hKP hPKP.1 hSL.1
    exact (piG_comm_of_le hp hq hΩ hW hP hS hle hrtP hs hrtW hsW).symm
  · have hSN : S ≤ Subgroup.normalizer ((conjSub r J : Subgroup G) : Set G) :=
      hΩ.le_normalizer_of_le_centralizer hp hq hKP hL (Ne.symm hLP) hzP hSL.1 hSL.2.1
        (by have := hΩ.eight_le_of_mem_RSet hp hS.1; omega) hSc
    have hnbr : L ∈ omegaNbr Ω (conjSub r J) := ⟨hL, hLP, S, hS.1, hSL.1, hSN⟩
    exact (piG_comm_of_mem_omegaNbr h62 hp hq hΩ hW hkey hKP hL (Ne.symm hLP) hP hS hPKP hSL hnbr
      hrtP hs hrtW).symm

end Thompson

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonStar_of_key (hkey : ThompsonKey p f) : ThompsonStar p f := by
  intro G _ _ Ω hP W hW R hR T hT S hS r hr t ht s hs hrW htW hsW hnc
  have hp : p ≠ 2 := hP.1
  have hq : 5 ≤ p ^ f := hP.2.1
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  have h62 := l6_2 p f
  have hkey' := hkey G Ω hP W hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  obtain ⟨L, hL, hSL⟩ := exists_isSylow2In_of_mem_RSet hS.1
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  have hsN : s ∈ Subgroup.normalizer (W : Set G) := hS.2 hs
  have hrtrN : r * t * r⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) (Subgroup.inv_mem _ hrN)
  by_cases h1 : s * r * s⁻¹ * r⁻¹ ∈ W ⊔ OCW W
  · exact Or.inl h1
  by_cases h2 : s * t * s⁻¹ * t⁻¹ ∈ W ⊔ OCW W
  · exact Or.inr (Or.inl h2)
  right
  right
  refine (Thompson.piG_comm_iff hsN hrtrN).mp ?_
  refine Thompson.piG_comm_third h62 hp hq hΩ hW
    (fun R hR T hT J hJ hRJ hTJ' => hkey' R hR T hT J hJ hRJ hTJ') hK hJ hL hR hT hS hRK hTJ hSL
    hr ht hs hrW htW hsW ?_ ?_ ?_
  · exact fun h => hnc ((Thompson.piG_comm_iff hrN htN).mp h)
  · exact fun h => h1 ((Thompson.piG_comm_iff hsN hrN).mp h)
  · exact fun h => h2 ((Thompson.piG_comm_iff hsN htN).mp h)

end CFSG.ClassicalInvolution.Asc77
