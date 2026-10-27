module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenOmega

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

variable (p f : ℕ) [Fact p.Prime]

@[expose] def ThompsonKey : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp p f Ω →
    ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J →
      T ≤ R ⊔ W ⊔ OCW W

variable {p f}

namespace Thompson

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

theorem piG_mul_self_of_mem_D (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) :
    piG W r * piG W r = 1 := by
  rw [← piG_mul (hR.2 hr) (hR.2 hr)]
  exact piG_of_mem_sup (Subgroup.mem_sup_left (D_sq_mem hp hq hΩ hW hR hr))

theorem piG_comm_of_le (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hle : T ≤ R ⊔ W ⊔ OCW W)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    piG W r * piG W t = piG W t * piG W r := by
  rw [piG_eq_of_le_sup hp hq hΩ hW hR hT hle hr ht hrW htW]

theorem piG_comm_of_mem_omegaNbr (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) (hnbr : J ∈ omegaNbr Ω K)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) :
    piG W r * piG W t = piG W t * piG W r := by
  have hnbr' : K ∈ omegaNbr Ω J := T3.omegaNbr_symm h62 hp hq hΩ hK hJ hnbr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  have hcent : ∀ u ∈ K ⊓ W, t * u = u * t := fun u hu =>
    centralizes_inf_W_of_mem_omegaNbr h62 hp hq hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK hnbr'
      ht hu
  have hU : K ⊓ W ∈ USet Ω := (inf_W_of_mem_D hp hq hΩ hW hR hK hRK).2.1
  have hK₄ : conjSub t K ∈ Ω := hΩ.conjInvariant t K hK
  have hUle : K ⊓ W ≤ conjSub t K := by
    intro u hu
    rw [mem_conjSub_iff]
    have : t⁻¹ * u * t = u := by
      calc t⁻¹ * u * t = t⁻¹ * (u * t) := by group
        _ = t⁻¹ * (t * u) := by rw [hcent u hu]
        _ = u := by group
    rw [this]
    exact hu.1
  have hKeq : K = conjSub t K := hΩ.eq_of_mem_USet hp hU hK hK₄ inf_le_left hUle
  have hR₄ : conjSub t R ∈ DSet Ω W := conjSub_mem_D hΩ hR htN
  have hR₄K : conjSub t R ≤ K := by
    calc conjSub t R ≤ conjSub t K := conjSub_mono hRK.1
      _ = K := hKeq.symm
  have hle := hkey R hR (conjSub t R) hR₄ K hK hRK.1 hR₄K
  have htrW : t * r * t⁻¹ ∉ W := fun h => hrW ((mem_normalizer_iff_of_mem htN r).mp h)
  have heq := piG_eq_of_le_sup hp hq hΩ hW hR hR₄ hle hr (conj_mem_conjSub hr) hrW htrW
  rw [piG_mul (Subgroup.mul_mem _ htN (hR.2 hr)) (Subgroup.inv_mem _ htN),
    piG_mul htN (hR.2 hr), piG_inv htN] at heq
  have : piG W t * piG W r = piG W r * piG W t := by
    calc piG W t * piG W r = (piG W t * piG W r * (piG W t)⁻¹) * piG W t := by group
      _ = piG W r * piG W t := by rw [heq]
  exact this.symm

end Thompson

end CFSG.ClassicalInvolution.Asc77
