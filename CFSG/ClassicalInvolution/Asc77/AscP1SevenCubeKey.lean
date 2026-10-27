module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenCube
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenTori
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenOrbit
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenDihedral
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonInputs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem piG_one : piG W (1 : G) = 1 := by
  have h := piG_mul (W := W) (Subgroup.one_mem _) (Subgroup.one_mem _)
  rw [mul_one] at h
  exact mul_left_cancel (a := piG W 1) (by rw [mul_one]; exact h.symm)

omit [Finite G] in
theorem piG_mem_closure {r t w : G} (hr : r ∈ Subgroup.normalizer (W : Set G))
    (ht : t ∈ Subgroup.normalizer (W : Set G)) (hw : w ∈ Subgroup.closure ({r, t} : Set G)) :
    w ∈ Subgroup.normalizer (W : Set G) ∧
      piG W w ∈ Subgroup.closure ({piG W r, piG W t} : Set (NQuot (W ⊔ OCW W))) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · rw [hx]
      exact ⟨hr, Subgroup.subset_closure (by simp)⟩
    · rw [Set.mem_singleton_iff.mp hx]
      exact ⟨ht, Subgroup.subset_closure (by simp)⟩
  | one => exact ⟨Subgroup.one_mem _, by rw [piG_one]; exact Subgroup.one_mem _⟩
  | mul x y _ _ hx hy =>
    exact ⟨Subgroup.mul_mem _ hx.1 hy.1, by
      rw [piG_mul hx.1 hy.1]
      exact Subgroup.mul_mem _ hx.2 hy.2⟩
  | inv x _ hx =>
    exact ⟨Subgroup.inv_mem _ hx.1, by
      rw [piG_inv hx.1]
      exact Subgroup.inv_mem _ hx.2⟩

theorem exists_zpow_odd_of_key (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    ∃ i : ℤ, (piG W r * piG W t) ^ (2 * i + 1) = 1 := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hnot' : K ∉ omegaNbr Ω J := fun h => hnot (T3.omegaNbr_symm h62 hp hq hΩ hJ hK h)
  have hzW : z ∈ K ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hK hR hRK hz
  have hjW : j ∈ J ⊓ W := uniqueInvolution_mem_W hp hq hΩ hW hJ hT hTJ hj
  have hcomm : z * j = j * z := commutes_of_mem_WSet hp hq hΩ hW z hzW.2 j hjW.2
  have hzj : z ≠ j := by
    intro h
    rw [← h] at hj
    exact hnot (T3.twin_mem_omegaNbr hΩ hK hJ (Ne.symm hKJ) hz hj)
  have hrj := conj_involution_eq_mul h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj hr hrW
  have htz := conj_involution_eq_mul' h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj ht htW
  have hA1 := inf_centralizer_le_normalizer_of_D h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hj
  have hB1 := inf_centralizer_le_normalizer_of_D h62 hp hq hΩ hW hJ hK (Ne.symm hKJ) hT hR hTJ hRK
    hnot' hz
  have hstar := (mem_omegaStarNbr_of_inf_W hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ).1
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
  have heq := piG_eq_of_le_sup hp hq hΩ hW hT' hT hle (conj_mem_conjSub hr) ht hwrW htW
  rw [piG_mul (Subgroup.mul_mem _ hwN hrN) (Subgroup.inv_mem _ hwN), piG_mul hwN hrN,
    piG_inv hwN] at heq
  exact exists_zpow_eq_one_of_conj_mem_closure (piG_mul_self_of_mem_D hp hq hΩ hW hR hr)
    (piG_mul_self_of_mem_D hp hq hΩ hW hT ht) hwcl heq.symm

theorem pow_six_of_key (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J) (hnot : J ∉ omegaNbr Ω K)
    {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    (piG W r * piG W t) ^ 6 = 1 := by
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hrj := conj_involution_eq_mul h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj hr hrW
  have htz := conj_involution_eq_mul' h62 hp hq hΩ hW hK hJ hKJ hR hT hRK hTJ hnot hz hj ht htW
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
  have ha := piG_mul_self_of_mem_D hp hq hΩ hW hR hr
  have hb := piG_mul_self_of_mem_D hp hq hΩ hW hT ht
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
    have heq := piG_eq_of_le_sup hp hq hΩ hW hR hT₃ hle hr ht₃ hrW ht₃W
    rw [he] at heq
    exact pow_six_eq_one_of_eq heq.symm
  · have hnbr : conjSub (r * t * r) J ∈ omegaNbr Ω K :=
      T3.twin_mem_omegaNbr hΩ hK hK₃ hK₃K hz hz₃
    have hcomm := piG_comm_of_mem_omegaNbr h62 hp hq hΩ hW hkey hK hK₃ (Ne.symm hK₃K) hR hT₃ hRK
      hT₃K₃ hnbr hr ht₃ hrW
    rw [he] at hcomm
    exact pow_six_eq_one_of_comm ha hb hcomm

theorem piG_cube_of_key (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hW : W ∈ WSet Ω)
    (hkey : ∀ R ∈ DSet Ω W, ∀ T ∈ DSet Ω W, ∀ J ∈ Ω, R ≤ J → T ≤ J → T ≤ R ⊔ W ⊔ OCW W)
    {K J R T : Subgroup G} (hAK : AEmpty Ω K) (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J)
    (hR : R ∈ DSet Ω W) (hT : T ∈ DSet Ω W) (hRK : IsSylow2In R K) (hTJ : IsSylow2In T J)
    (hnot : J ∉ omegaNbr Ω K) {r t : G} (hr : r ∈ R) (ht : t ∈ T) (hrW : r ∉ W) (htW : t ∉ W) :
    (piG W r * piG W t) ^ 3 = 1 := by
  obtain ⟨i, hi⟩ := exists_zpow_odd_of_key h62 hp hq hΩ hW hkey hAK hK hJ hKJ hR hT hRK hTJ hnot
    hr ht hrW htW
  exact pow_three_of_odd_of_six hi
    (pow_six_of_key h62 hp hq hΩ hW hkey hK hJ hKJ hR hT hRK hTJ hnot hr ht hrW htW)

end Thompson

variable {p f : ℕ} [Fact p.Prime]

theorem thompsonCube_of_key (hkey : ThompsonKey p f) : ThompsonCube p f := by
  intro G _ _ Ω hP W hW R hR T hT r hr t ht hrW htW
  have hp : p ≠ 2 := hP.1
  have hq : 5 ≤ p ^ f := hP.2.1
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  have h62 := l6_2 p f
  have hkey' := hkey G Ω hP W hW
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  obtain ⟨J, hJ, hTJ⟩ := exists_isSylow2In_of_mem_RSet hT.1
  have hrN : r ∈ Subgroup.normalizer (W : Set G) := hR.2 hr
  have htN : t ∈ Subgroup.normalizer (W : Set G) := hT.2 ht
  by_cases hKJ : K = J
  · left
    subst hKJ
    exact (Thompson.piG_comm_iff hrN htN).mp
      (Thompson.piG_comm_of_le hp hq hΩ hW hR hT (hkey' R hR T hT K hK hRK.1 hTJ.1) hr ht hrW htW)
  · by_cases hnbr : J ∈ omegaNbr Ω K
    · left
      exact (Thompson.piG_comm_iff hrN htN).mp
        (Thompson.piG_comm_of_mem_omegaNbr h62 hp hq hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW)
    · right
      exact (Thompson.piG_cube_iff hrN htN).mp
        (Thompson.piG_cube_of_key h62 hp hq hΩ hW (fun R hR T hT J hJ hRJ hTJ' =>
          hkey' R hR T hT J hJ hRJ hTJ') (hP.2.2.2 K hK) hK hJ hKJ hR hT hRK hTJ hnbr hr ht hrW
          htW)

end CFSG.ClassicalInvolution.Asc77
