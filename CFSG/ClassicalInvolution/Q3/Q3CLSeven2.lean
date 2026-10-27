module

public import CFSG.ClassicalInvolution.Q3.Q3CLKey
public import CFSG.ClassicalInvolution.Q3.Q3CLSeven1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {W : Subgroup G}

namespace Thompson

open CFSG.ClassicalInvolution.Asc77.Thompson

theorem piG_mul_self_of_mem_D (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) :
    piG W r * piG W r = 1 := by
  rw [← piG_mul (hR.2 hr) (hR.2 hr)]
  exact piG_of_mem_sup (Subgroup.mem_sup_left (D_sq_mem hΩ hW hR hr))

theorem piG_comm_of_le (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    {R T : Subgroup G} (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hle : T ≤ R ⊔ W ⊔ OCW W)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    piG W r * piG W t = piG W t * piG W r := by
  rw [piG_eq_of_le_sup hΩ hW hR hT hle hr ht hrW htW]

theorem piG_comm_of_mem_omegaNbr (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) (hnbr : J ∈ omegaNbr Ω K)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) :
    piG W r * piG W t = piG W t * piG W r := by
  have hnbr' : K ∈ omegaNbr Ω J := T3.omegaNbr_symm h62 hΩ hK hJ hnbr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  have hcent : ∀ u ∈ K ⊓ W, t * u = u * t := fun u hu =>
    centralizes_inf_W_of_mem_omegaNbr h62 hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK hnbr'
      ht hu
  have hU : K ⊓ W ∈ USet Ω := (inf_W_of_mem_D hΩ hW hR hK hRK).2.1
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
  have hKeq : K = conjSub t K := Sec6Gen.eq_of_mem_USet hΩ hU hK hK₄ inf_le_left hUle
  have hR₄ : conjSub t R ∈ DSet Ω W := conjSub_mem_D hΩ hR htN
  have hR₄K : conjSub t R ≤ K := by
    calc conjSub t R ≤ conjSub t K := conjSub_mono hRK.1
      _ = K := hKeq.symm
  have hle := hkey R hR (conjSub t R) hR₄ K hK hRK.1 hR₄K
  have htrW : t * r * t⁻¹ ∉ W := fun h => hrW ((mem_normalizer_iff_of_mem htN r).mp h)
  have heq := piG_eq_of_le_sup hΩ hW hR hR₄ hle hr (conj_mem_conjSub hr) hrW htrW
  rw [piG_mul (Subgroup.mul_mem _ htN (hR.2 hr)) (Subgroup.inv_mem _ htN),
    piG_mul htN (hR.2 hr), piG_inv htN] at heq
  have : piG W t * piG W r = piG W r * piG W t := by
    calc piG W t * piG W r = (piG W t * piG W r * (piG W t)⁻¹) * piG W t := by group
      _ = piG W r * piG W t := by rw [heq]
  exact this.symm

theorem exists_zpow_odd_of_key (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    ∃ i : ℤ, (piG W r * piG W t) ^ (2 * i + 1) = 1 := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hnot' : K ∉ omegaNbr Ω J := fun h => hnot (T3.omegaNbr_symm h62 hΩ hJ hK h)
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hΩ hW hJ hT hTJ hj
  have hcomm : z * j = j * z := commutes_of_mem_WSet hΩ hW z hzW.2 j hjW.2
  have hzj : z ≠ j := by
    intro h
    rw [← h] at hj
    exact hnot (T3.twin_mem_omegaNbr hΩ hK hJ (Ne.symm hKJ) hz hj)
  have hrj := conj_involution_eq_mul h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj hr hrW
  have htz := conj_involution_eq_mul' h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj ht htW
  have hA1 := inf_centralizer_le_normalizer_of_D h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hj
  have hB1 := inf_centralizer_le_normalizer_of_D h62 hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK
    hnot' hz
  have hstar := (mem_omegaStarNbr_of_inf_W hΩ hW hK hJ hKJ hR hT hRK hTJ).1
  have hAE := hAK J hstar hnot z j hz hj
  obtain ⟨w, hw, hwK⟩ := exists_mem_closure_conj_eq hz hj hzj hcomm hA1 hB1 (hRK.1 hr) (hTJ.1 ht)
    hrj htz hAE
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  obtain ⟨hwN, hwcl⟩ := piG_mem_closure hrN htN hw
  have hT' : conjSub w R ∈ DSet Ω W := conjSub_mem_D hΩ hR hwN
  have hT'J : conjSub w R ≤ J := hwK ▸ conjSub_mono hRK.1
  have hle := hkey (conjSub w R) hT' T hT J hJ hT'J hTJ.1
  have hwrW : w * r * w⁻¹ ∉ W := fun h => hrW ((mem_normalizer_iff_of_mem hwN r).mp h)
  have heq := piG_eq_of_le_sup hΩ hW hT' hT hle (conj_mem_conjSub hr) ht hwrW htW
  rw [piG_mul (Subgroup.mul_mem _ hwN hrN) (Subgroup.inv_mem _ hwN), piG_mul hwN hrN,
    piG_inv hwN] at heq
  exact exists_zpow_eq_one_of_conj_mem_closure (piG_mul_self_of_mem_D hΩ hW hR hr)
    (piG_mul_self_of_mem_D hΩ hW hT ht) hwcl heq.symm

theorem pow_six_of_key (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    (piG W r * piG W t) ^ 6 = 1 := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hrj := conj_involution_eq_mul h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj hr hrW
  have htz := conj_involution_eq_mul' h62 hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj ht htW
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  have hnN : r * t * r ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hrN htN) hrN
  have hrz : r * z * r⁻¹ = z := by
    have := hz.commute_of_mem (hRK.1 hr)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have htj : t * j * t⁻¹ = j := by
    have := hj.commute_of_mem (hTJ.1 ht)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hjj := hj.sq
  have hu : (r * t * r) * j * (r * t * r)⁻¹ = z := by
    calc (r * t * r) * j * (r * t * r)⁻¹ = r * (t * (r * j * r⁻¹) * t⁻¹) * r⁻¹ := by group
      _ = r * (t * (z * j) * t⁻¹) * r⁻¹ := by rw [hrj]
      _ = r * ((t * z * t⁻¹) * (t * j * t⁻¹)) * r⁻¹ := by group
      _ = r * ((z * j) * j) * r⁻¹ := by rw [htz, htj]
      _ = r * z * r⁻¹ := by rw [mul_assoc z j j, hjj, mul_one]
      _ = z := hrz
  have hK₃ : conjSub (r * t * r) J ∈ Ω := hΩ.conjInvariant _ J hJ
  have hz₃ : IsUniqueInvolution (conjSub (r * t * r) J) z := by
    have := hj.conj (r * t * r)
    rwa [hu] at this
  have hT₃ : conjSub (r * t * r) T ∈ DSet Ω W := conjSub_mem_D hΩ hT hnN
  have hT₃K₃ : IsSylow2In (conjSub (r * t * r) T) (conjSub (r * t * r) J) := hTJ.conj _
  have ht₃ : (r * t * r) * t * (r * t * r)⁻¹ ∈ conjSub (r * t * r) T := conj_mem_conjSub ht
  have ht₃W : (r * t * r) * t * (r * t * r)⁻¹ ∉ W :=
    fun h => htW ((mem_normalizer_iff_of_mem hnN t).mp h)
  have ha := piG_mul_self_of_mem_D hΩ hW hR hr
  have hb := piG_mul_self_of_mem_D hΩ hW hT ht
  have hai : (piG W r)⁻¹ = piG W r := inv_eq_of_mul_eq_one_left ha
  have hbi : (piG W t)⁻¹ = piG W t := inv_eq_of_mul_eq_one_left hb
  have h1 : piG W (r * t * r) = piG W r * piG W t * piG W r := by
    rw [piG_mul (Subgroup.mul_mem _ hrN htN) hrN, piG_mul hrN htN]
  have he : piG W ((r * t * r) * t * (r * t * r)⁻¹) =
      piG W r * piG W t * piG W r * piG W t * (piG W r * piG W t * piG W r) := by
    rw [piG_mul (Subgroup.mul_mem _ hnN htN) (Subgroup.inv_mem _ hnN), piG_mul hnN htN,
      piG_inv hnN, h1]
    simp only [mul_inv_rev, hai, hbi, mul_assoc]
  by_cases hK₃K : conjSub (r * t * r) J = K
  · have hT₃K : conjSub (r * t * r) T ≤ K := hK₃K ▸ hT₃K₃.1
    have hle := hkey R hR _ hT₃ K hK hRK.1 hT₃K
    have heq := piG_eq_of_le_sup hΩ hW hR hT₃ hle hr ht₃ hrW ht₃W
    rw [he] at heq
    exact pow_six_eq_one_of_eq heq.symm
  · have hnbr : conjSub (r * t * r) J ∈ omegaNbr Ω K :=
      T3.twin_mem_omegaNbr hΩ hK hK₃ hK₃K hz hz₃
    have hcomm := piG_comm_of_mem_omegaNbr h62 hΩ hW hkey hK hK₃ (Ne.symm hK₃K) hR hT₃ hRK
      hT₃K₃ hnbr hr ht₃ hrW
    rw [he] at hcomm
    exact pow_six_eq_one_of_comm ha hb hcomm

theorem piG_cube_of_key (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    (piG W r * piG W t) ^ 3 = 1 := by
  obtain ⟨i, hi⟩ := exists_zpow_odd_of_key h62 hΩ hW hkey hAK hK hJ hKJ hR hT hRK hTJ hnot
    hr ht hrW htW
  exact pow_three_of_odd_of_six hi
    (pow_six_of_key h62 hΩ hW hkey hK hJ hKJ hR hT hRK hTJ hnot hr ht hrW htW)

end Thompson

omit [Finite G] in
@[expose] def CubeOn (Ω : Set (Subgroup G)) : Prop :=
  ∀ W ∈ WSet Ω, ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ r ∈ R, ∀ t ∈ T, r ∉ W → t ∉ W →
    r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W ∨ (r * t) ^ 3 ∈ W ⊔ OCW W

theorem thompsonCube_of_key (hP : PartIHypG Ω) (hkey : Sec7.KeyOn Ω) : CubeOn Ω := by
  intro W hW R hR T hT r hr t ht hrW htW
  have hΩ : HypOmegaGen Ω := hP.hyp
  have h62 := Sec6Gen.l6_2Gen
  have hkey' := hkey W hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  by_cases hKJ : K = J
  · left
    subst hKJ
    exact (Thompson.piG_comm_iff hrN htN).mp
      (Thompson.piG_comm_of_le hΩ hW hR hT (hkey' R hR T hT K hK hRK.1 hTJ.1) hr ht hrW htW)
  · by_cases hnbr : J ∈ omegaNbr Ω K
    · left
      exact (Thompson.piG_comm_iff hrN htN).mp
        (Thompson.piG_comm_of_mem_omegaNbr h62 hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW)
    · right
      exact (Thompson.piG_cube_iff hrN htN).mp
        (Thompson.piG_cube_of_key h62 hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') (hP.aEmpty K hK) hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW
          htW)

theorem thompsonKey (hP : PartIHypG Ω) : Sec7.KeyOn Ω := Sec7.l7_1Key hP

theorem thompsonCube (hP : PartIHypG Ω) : CubeOn Ω := thompsonCube_of_key hP (thompsonKey hP)

namespace Thompson

open CFSG.ClassicalInvolution.Asc77.Thompson

theorem conj_eq_inv_of_mem_inf_W (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K)
    {r u : G} (hr : r ∈ R) (hrW : r ∉ W) (hu : u ∈ K ⊓ W) : r * u * r⁻¹ = u⁻¹ := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨hRW, -, hcyc, -, hcard⟩ := inf_W_of_mem_D hΩ hW hR hK hRK
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hΩ hW hK hR hRK hz
  have hzR : z ∈ R := by
    have : z ∈ R ⊓ W := hRW ▸ hzW
    exact this.1
  have hu' : u ∈ R ⊓ W := hRW ▸ hu
  exact AscL62.conj_eq_inv_of_not_mem (Sec6Gen.isQuatSub_of_mem_RSet hΩ hR.1)
    (AscL62.isUniqueInvolution_of_le hz hRK.1 hzR) inf_le_left hcyc hcard hr (fun h => hrW h.2) hu'

theorem conj_eq_of_piG_eq (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {r t : G} (hr : r ∈ Subgroup.normalizer (W : Set G))
    (ht : t ∈ Subgroup.normalizer (W : Set G)) (h : piG W r = piG W t) {w : G} (hw : w ∈ W) :
    t * w * t⁻¹ = r * w * r⁻¹ := by
  have hWab := commutes_of_mem_WSet hΩ hW
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

theorem eq_of_piG_eq (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω)
    (hW : W ∈ WSet Ω) {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) {r t : G} (hr : r ∈ R)
    (ht : t ∈ T) (htW : t ∉ W) (h : piG W r = piG W t) : K = J := by
  by_contra hne
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  by_cases hnbr : J ∈ omegaNbr Ω K
  · obtain ⟨-, -, hcyc, h4, -⟩ := inf_W_of_mem_D hΩ hW hT hJ hTJ
    obtain ⟨hTW, -, -, -, -⟩ := inf_W_of_mem_D hΩ hW hT hJ hTJ
    obtain ⟨v, hvU, hv2⟩ := exists_sq_ne_one hcyc (by omega)
    have hvJW : v ∈ J ⊓ W := hTW ▸ hvU
    have h1 : t * v * t⁻¹ = v⁻¹ := conj_eq_inv_of_mem_inf_W hΩ hW hJ hT hTJ ht htW hvJW
    have h2 : t * v * t⁻¹ = r * v * r⁻¹ := conj_eq_of_piG_eq hΩ hW hrN htN h hvJW.2
    have h3 : r * v = v * r :=
      centralizes_inf_W_of_mem_omegaNbr h62 hΩ hW hK hJ hne hR hT hRK hTJ hnbr hr hvJW
    have h4' : r * v * r⁻¹ = v := by rw [h3]; group
    rw [h1, h4'] at h2
    apply hv2
    calc v * v = v⁻¹ * v := by rw [h2]
      _ = 1 := inv_mul_cancel v
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
    obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
    have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hΩ hW hK hR hRK hz
    have h1 : t * z * t⁻¹ = z * j :=
      conj_involution_eq_mul' h62 hΩ hW hK hJ hne hR hT hRK hTJ hnbr hz hj ht htW
    have h2 : t * z * t⁻¹ = r * z * r⁻¹ := conj_eq_of_piG_eq hΩ hW hrN htN h hzW.2
    have h3 : r * z * r⁻¹ = z := by
      have := hz.commute_of_mem (hRK.1 hr)
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    rw [h1, h3] at h2
    exact hj.ne_one (mul_eq_left.mp h2)

theorem not_comm_of_not_mem_omegaNbr (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    piG W r * piG W t ≠ piG W t * piG W r := by
  intro hcomm
  have hcube := piG_cube_of_key h62 hΩ hW hkey hAK hK hJ hKJ hR hT hRK hTJ hnot hr ht hrW htW
  have ha := piG_mul_self_of_mem_D hΩ hW hR hr
  have hb := piG_mul_self_of_mem_D hΩ hW hT ht
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
  exact hKJ (eq_of_piG_eq h62 hΩ hW hK hJ hR hT hRK hTJ hr ht htW this)

structure Ctx (Ω : Set (Subgroup G)) (W : Subgroup G) : Prop where
  hΩ : HypOmegaGen Ω
  hW : W ∈ WSet Ω
  hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W
  hA : ∀ K ∈ Ω, AEmpty Ω K

end Thompson

namespace Thompson.Ctx

open CFSG.ClassicalInvolution.Asc77.Thompson

variable (c : Ctx Ω W)
include c

theorem comm_W : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := commutes_of_mem_WSet c.hΩ c.hW

theorem K_eq_of_img_eq (ρ σ : Rep Ω W) (h : ρ.img = σ.img) : ρ.K = σ.K :=
  eq_of_piG_eq Sec6Gen.l6_2Gen c.hΩ c.hW ρ.hK σ.hK ρ.hR σ.hR ρ.hRK σ.hRK ρ.hr σ.hr σ.hrW h

theorem noncomm (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) :
    ρ.img * σ.img ≠ σ.img * ρ.img :=
  not_comm_of_not_mem_omegaNbr Sec6Gen.l6_2Gen c.hΩ c.hW c.hkey (c.hA ρ.K ρ.hK) ρ.hK σ.hK hne
    ρ.hR σ.hR ρ.hRK σ.hRK hnot ρ.hr σ.hr ρ.hrW σ.hrW

theorem conj_involution (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) (hnot : σ.K ∉ omegaNbr Ω ρ.K) {z j : G}
    (hz : IsUniqueInvolution ρ.K z) (hj : IsUniqueInvolution σ.K j) :
    ρ.r * j * ρ.r⁻¹ = z * j :=
  conj_involution_eq_mul Sec6Gen.l6_2Gen c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK hnot
    hz hj ρ.hr ρ.hrW

end Thompson.Ctx

namespace T8

open CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.GH74.Uniqueness
  CFSG.StronglyEmbedded.UniqueCoset

theorem ctxOf (hP : PartIHypG Ω) (hW : W ∈ WSet Ω) : Thompson.Ctx Ω W :=
  ⟨hP.hyp, hW, thompsonKey hP W hW, hP.aEmpty⟩

@[expose] noncomputable def mkRep (hP : PartIHypG Ω) (hW : W ∈ WSet Ω) {K R : Subgroup G}
    (hK : K ∈ Ω) (hR : R ∈ DSet Ω W) (hRK : IsSylow2In R K) : Rep Ω W :=
  have h := Thompson.exists_not_mem_of_mem_D hP.hyp hW hR
  ⟨K, R, h.choose, hK, hR, hRK, h.choose_spec.1, h.choose_spec.2⟩

end T8


end CFSG.ClassicalInvolution.Q3.Q3CL
