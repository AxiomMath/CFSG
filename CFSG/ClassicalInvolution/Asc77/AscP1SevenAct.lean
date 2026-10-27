module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenCubeKey

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem exists_sq_ne_one {U : Subgroup G} (hcyc : IsCyclic ↥U) (h3 : 3 ≤ Nat.card U) :
    ∃ v ∈ U, v * v ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥U)
  refine ⟨(g : G), g.2, fun h => ?_⟩
  have hg2 : g * g = 1 := Subtype.ext h
  have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
  have hcard : orderOf g = Nat.card U := orderOf_eq_card_of_forall_mem_zpowers hg
  have := Nat.le_of_dvd (by norm_num) hord
  omega

theorem conj_eq_inv_of_mem_inf_W (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K)
    {r u : G} (hr : r ∈ R) (hrW : r ∉ W) (hu : u ∈ K ⊓ W) : r * u * r⁻¹ = u⁻¹ := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨hRW, -, hcyc, -, hcard⟩ := inf_W_of_mem_D hp hq hΩ hW hR hK hRK
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
  have hzR : z ∈ R := by
    have : z ∈ R ⊓ W := hRW ▸ hzW
    exact this.1
  have hu' : u ∈ R ⊓ W := hRW ▸ hu
  exact AscL62.conj_eq_inv_of_not_mem (hΩ.isQuatSub_of_mem_RSet hp hR.1)
    (AscL62.isUniqueInvolution_of_le hz hRK.1 hzR) inf_le_left hcyc hcard hr (fun h => hrW h.2) hu'

theorem conj_eq_of_piG_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {r t : G} (hr : r ∈ Subgroup.normalizer (W : Set G))
    (ht : t ∈ Subgroup.normalizer (W : Set G)) (h : piG W r = piG W t) {w : G} (hw : w ∈ W) :
    t * w * t⁻¹ = r * w * r⁻¹ := by
  have hWab := commutes_of_mem_WSet hp hq hΩ hW
  have hξ : r⁻¹ * t ∈ W ⊔ OCW W := (piG_eq_iff hr ht).mp h
  have hξc : r⁻¹ * t ∈ Subgroup.centralizer (W : Set G) := by
    have : W ⊔ OCW W ≤ Subgroup.centralizer (W : Set G) := by
      refine sup_le (fun x hx => ?_) (OCW_le_centralizer W)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hWab y hy x hx
    exact this hξ
  have hcomm : w * (r⁻¹ * t) = (r⁻¹ * t) * w := Subgroup.mem_centralizer_iff.mp hξc w hw
  calc t * w * t⁻¹ = r * ((r⁻¹ * t) * w * (r⁻¹ * t)⁻¹) * r⁻¹ := by group
    _ = r * w * r⁻¹ := by rw [← hcomm]; group

theorem eq_of_piG_eq (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) {r t : G} (hr : r ∈ R)
    (ht : t ∈ T) (htW : t ∉ W) (h : piG W r = piG W t) : K = J := by
  by_contra hne
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  by_cases hnbr : J ∈ omegaNbr Ω K
  · obtain ⟨-, -, hcyc, h4, -⟩ := inf_W_of_mem_D hp hq hΩ hW hT hJ hTJ
    obtain ⟨hTW, -, -, -, -⟩ := inf_W_of_mem_D hp hq hΩ hW hT hJ hTJ
    obtain ⟨v, hvU, hv2⟩ := exists_sq_ne_one hcyc (by omega)
    have hvJW : v ∈ J ⊓ W := hTW ▸ hvU
    have h1 : t * v * t⁻¹ = v⁻¹ := conj_eq_inv_of_mem_inf_W hp hq hΩ hW hJ hT hTJ ht htW hvJW
    have h2 : t * v * t⁻¹ = r * v * r⁻¹ := conj_eq_of_piG_eq hp hq hΩ hW hrN htN h hvJW.2
    have h3 : r * v = v * r :=
      centralizes_inf_W_of_mem_omegaNbr h62 hp hq hΩ hW hK hJ hne hR hT hRK hTJ hnbr hr hvJW
    have h4' : r * v * r⁻¹ = v := by rw [h3]; group
    rw [h1, h4'] at h2
    apply hv2
    calc v * v = v⁻¹ * v := by rw [h2]
      _ = 1 := inv_mul_cancel v
  · obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
    obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq hJ
    have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
    have h1 : t * z * t⁻¹ = z * j :=
      conj_involution_eq_mul' h62 hp hq hΩ hW hK hJ hne hR hT hRK hTJ hnbr hz hj ht htW
    have h2 : t * z * t⁻¹ = r * z * r⁻¹ := conj_eq_of_piG_eq hp hq hΩ hW hrN htN h hzW.2
    have h3 : r * z * r⁻¹ = z := by
      have := hz.commute_of_mem (hRK.1 hr)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    rw [h1, h3] at h2
    exact hj.ne_one (mul_eq_left.mp h2)

theorem not_comm_of_not_mem_omegaNbr (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    piG W r * piG W t ≠ piG W t * piG W r := by
  intro hcomm
  have hcube := piG_cube_of_key h62 hp hq hΩ hW hkey hAK hK hJ hKJ hR hT hRK hTJ hnot hr ht hrW htW
  have ha := piG_mul_self_of_mem_D hp hq hΩ hW hR hr
  have hb := piG_mul_self_of_mem_D hp hq hΩ hW hT ht
  have h2 : (piG W r * piG W t) * (piG W r * piG W t) = 1 := by
    calc (piG W r * piG W t) * (piG W r * piG W t) = piG W r * (piG W t * piG W r) * piG W t := by
          simp only [mul_assoc]
      _ = piG W r * (piG W r * piG W t) * piG W t := by rw [← hcomm]
      _ = (piG W r * piG W r) * (piG W t * piG W t) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  have h1 : piG W r * piG W t = 1 := by
    calc piG W r * piG W t = (piG W r * piG W t) * ((piG W r * piG W t) * (piG W r * piG W t)) := by
          rw [h2, mul_one]
      _ = (piG W r * piG W t) ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hcube
  have hbi : (piG W t)⁻¹ = piG W t := inv_eq_of_mul_eq_one_left hb
  have : piG W r = piG W t := by
    calc piG W r = (piG W r * piG W t) * (piG W t)⁻¹ := by group
      _ = piG W t := by rw [h1, one_mul, hbi]
  exact hKJ (eq_of_piG_eq h62 hp hq hΩ hW hK hJ hR hT hRK hTJ hr ht htW this)

theorem mem_omegaNbr_of_comm (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W)
    (hcomm : piG W r * piG W t = piG W t * piG W r) : J ∈ omegaNbr Ω K := by
  by_contra hnot
  exact not_comm_of_not_mem_omegaNbr h62 hp hq hΩ hW hkey hAK hK hJ hKJ hR hT hRK hTJ hnot hr ht
    hrW htW hcomm

end Thompson

end CFSG.ClassicalInvolution.Asc77
