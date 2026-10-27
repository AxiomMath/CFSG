module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3KFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryInvolution
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.UnitaryThreeRecognition.Model CFSG.AGLEmbedding.UnitaryModel
  CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External

section Matrices

variable {K : Type} [Field K]

theorem q8_matrices (b : K) (hb2 : b * b = -1) (h3 : (3 : K) = 0) :
    let Mu : Matrix (Fin 3) (Fin 3) K := !![1, 0, b; 0, 1, 0; 0, 0, 1]
    let Mu' : Matrix (Fin 3) (Fin 3) K := !![1, 0, -b; 0, 1, 0; 0, 0, 1]
    let Ma : Matrix (Fin 3) (Fin 3) K := !![0, 0, b; 0, 1, 0; b, 0, 0]
    let Mi : Matrix (Fin 3) (Fin 3) K := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
    (Mu * Ma * Mu') * Ma = Mi * Ma * (Mu * Ma * Mu') ∧
    Mu * (Mu * Ma * Mu') * Mu' = Mi * Ma * (Mu * Ma * Mu') := by
  intro Mu Mu' Ma Mi
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Mu, Mu', Ma, Mi, Matrix.mul_apply, Fin.sum_univ_three] <;>
      first
        | ring1
        | linear_combination ((-1 : K) * b ^ 2) * hb2 + (0 : K) * h3
        | linear_combination ((-5 : K) * b) * hb2 + ((2 : K) * b) * h3
        | linear_combination ((1 : K) * b) * hb2 + (0 : K) * h3
        | linear_combination (3 : K) * hb2 + (-1 : K) * h3
        | linear_combination ((3 : K) + (-1 : K) * b ^ 2) * hb2 + (-1 : K) * h3

end Matrices

section Model

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

omit hJ in
theorem mem_normalizer_of_conj_le {G : Type*} [Group G] {H : Subgroup G} {n : G}
    (h : ∀ t ∈ H, n * t * n⁻¹ ∈ H) (h' : ∀ t ∈ H, n⁻¹ * t * n ∈ H) :
    n ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

omit hJ in
theorem isPGroup_two_zpowers_sup {G : Type*} [Group G] {x y : G} (hx : x ^ 4 = 1) (hy : y ^ 4 = 1)
    (hyx : y * x * y⁻¹ = x⁻¹) : IsPGroup 2 (zpowers x ⊔ zpowers y : Subgroup G) := by
  have hpow : ∀ z : G, z ^ 4 = 1 → IsPGroup 2 (zpowers z) := by
    intro z hz
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show orderOf z ∣ 2 ^ 2 from orderOf_dvd_of_pow_eq_one hz)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  have hyn : y ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj_le (fun t ht => ?_) (fun t ht => ?_)
    · obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
      have : y * x ^ j * y⁻¹ = (y * x * y⁻¹) ^ j := (conj_zpow).symm
      rw [this, hyx, inv_zpow']
      exact zpow_mem (mem_zpowers x) _
    · obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
      have hinv : y⁻¹ * x * y = x⁻¹ := by
        calc y⁻¹ * x * y = y⁻¹ * (y * x * y⁻¹)⁻¹ * y := by rw [hyx, inv_inv]
          _ = x⁻¹ := by group
      have : y⁻¹ * x ^ j * y = (y⁻¹ * x * y) ^ j := by
        have h := conj_zpow (a := y⁻¹) (b := x) (i := j)
        simpa using h.symm
      rw [this, hinv, inv_zpow']
      exact zpow_mem (mem_zpowers x) _
  exact IsPGroup.to_sup_of_normal_left' (hpow x hx) (hpow y hy)
    (zpowers_le.mpr hyn)

theorem u3_model_two_group [CharP K 3] (b : K) (hb0 : b ≠ 0) (hbσ : J.conj b = -b)
    (hb2 : b * b = -1) :
    ∃ V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), IsPGroup 2 V ∧
      root J hJ (skewCoord J b (by rw [hbσ]; ring)) ∈
        normalizer (V : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ∧
      ∃ v ∈ V, v • pinf J hJ ≠ pinf J hJ := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hb : b + J.conj b = 0 := by rw [hbσ]; ring
  have hbinv : b⁻¹ = -b := inv_eq_of_mul_eq_one_right (by linear_combination (-1 : K) * hb2)
  set z : Coord J := skewCoord J b hb with hz
  set k : Kˣ := Units.mk0 b hb0 with hk
  have hUg : (hermitianUnipotentGL J z : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, b; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianUnipotentMatrix, hz, skewCoord]
  have hUg' : (hermitianUnipotentGL J z⁻¹ : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, -b; 0, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianUnipotentMatrix, coord_inv_val, hz, skewCoord, hbσ]
  have hTW : ((hermitianTorusGL J k * hermitianWeylGL : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = !![0, 0, b; 0, 1, 0; b, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianTorusMatrix, hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply,
        Fin.sum_univ_three, hk, hbσ, hbinv]
    linear_combination (-1 : K) * hb2
  have hIg : (hermitianTorusGL J (-1) : Matrix (Fin 3) (Fin 3) K) =
      !![-1, 0, 0; 0, 1, 0; 0, 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianTorusMatrix]
  obtain ⟨hGL4, hGL5⟩ := q8_matrices b hb2 h3
  have hGL4' : (hermitianUnipotentGL J z * (hermitianTorusGL J k * hermitianWeylGL) *
        hermitianUnipotentGL J z⁻¹) * (hermitianTorusGL J k * hermitianWeylGL) =
      hermitianTorusGL J (-1) * (hermitianTorusGL J k * hermitianWeylGL) *
        (hermitianUnipotentGL J z * (hermitianTorusGL J k * hermitianWeylGL) *
          hermitianUnipotentGL J z⁻¹) := by
    apply Units.ext
    simp only [Units.val_mul, hUg, hUg', hTW, hIg]
    exact hGL4
  have hGL5' : hermitianUnipotentGL J z * (hermitianUnipotentGL J z *
        (hermitianTorusGL J k * hermitianWeylGL) * hermitianUnipotentGL J z⁻¹) *
        hermitianUnipotentGL J z⁻¹ =
      hermitianTorusGL J (-1) * (hermitianTorusGL J k * hermitianWeylGL) *
        (hermitianUnipotentGL J z * (hermitianTorusGL J k * hermitianWeylGL) *
          hermitianUnipotentGL J z⁻¹) := by
    apply Units.ext
    simp only [Units.val_mul, hUg, hUg', hTW, hIg]
    exact hGL5
  set u : ProjectiveSpecialUnitaryMatrixGroup J := root J hJ z with hu
  set A : ProjectiveSpecialUnitaryMatrixGroup J := torus J hJ k * weyl J hJ with hA
  set ι : ProjectiveSpecialUnitaryMatrixGroup J := invol J hJ with hι
  have hu' : u⁻¹ = root J hJ z⁻¹ := (map_inv (root J hJ) z).symm
  set B : ProjectiveSpecialUnitaryMatrixGroup J := u * A * u⁻¹ with hB
  have hιι : ι * ι = 1 := invol_mul_self J hJ
  have hAA : A * A = ι := by
    have h1 : A * A = torus J hJ k * (weyl J hJ * torus J hJ k * weyl J hJ) := by
      simp only [hA]
      group
    rw [h1, weyl_mul_torus_mul_weyl, ← map_mul]
    have : k * (Units.map J.conj.toMonoidHom k)⁻¹ = -1 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one]
      change b * (J.conj b)⁻¹ = -1
      rw [hbσ, inv_neg, hbinv]
      linear_combination hb2
    rw [this]
    rfl
  have hιu : ι * u = u * ι := by
    have h := torus_mul_root_mul_inv J hJ (-1) z
    have hact : hermitianTorusAction J (-1) z = z := by
      apply Subtype.ext
      rw [invol_action_val]
      simp [hz, skewCoord]
    rw [hact] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hιA : ι * A = A * ι := by
    have hTι : torus J hJ (-1) * torus J hJ k = torus J hJ k * torus J hJ (-1) := by
      rw [← map_mul, ← map_mul, mul_comm]
    have hWι : weyl J hJ * ι = ι * weyl J hJ := weyl_mul_invol J hJ
    have hιT : ι = torus J hJ (-1) := rfl
    calc ι * (torus J hJ k * weyl J hJ) = (ι * torus J hJ k) * weyl J hJ := by group
      _ = (torus J hJ k * ι) * weyl J hJ := by rw [hιT, hTι]
      _ = torus J hJ k * (ι * weyl J hJ) := by group
      _ = torus J hJ k * (weyl J hJ * ι) := by rw [hWι]
      _ = (torus J hJ k * weyl J hJ) * ι := by group
  have hcu : ((root J hJ z : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z) :=
    rfl
  have hcu' : ((root J hJ z⁻¹ : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk (hermitianUnipotentGL J z⁻¹) :=
    rfl
  have hcT : ((torus J hJ k : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) := rfl
  have hcW : ((weyl J hJ : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk hermitianWeylGL := rfl
  have hcI : ((torus J hJ (-1) : ProjectiveSpecialUnitaryMatrixGroup J) :
      Matrix.ProjGenLinGroup (Fin 3) K) = Matrix.ProjGenLinGroup.mk (hermitianTorusGL J (-1)) :=
    rfl
  have hBA : B * A = ι * A * B := by
    rw [hB, hu']
    apply Subtype.ext
    simp only [hA, hι, invol, hu, Subgroup.coe_mul, hcu, hcu', hcT, hcW, hcI, ← map_mul]
    exact congrArg Matrix.ProjGenLinGroup.mk hGL4'
  have huB : u * B * u⁻¹ = ι * A * B := by
    rw [hB, hu']
    apply Subtype.ext
    simp only [hA, hι, invol, hu, Subgroup.coe_mul, hcu, hcu', hcT, hcW, hcI, ← map_mul]
    exact congrArg Matrix.ProjGenLinGroup.mk hGL5'
  have hAinv : A⁻¹ = ι * A := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc A * (ι * A) = (A * ι) * A := by group
      _ = (ι * A) * A := by rw [← hιA]
      _ = ι * (A * A) := by group
      _ = 1 := by rw [hAA, hιι]
  have hA4 : A ^ 4 = 1 := by
    calc A ^ 4 = (A * A) * (A * A) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
      _ = 1 := by rw [hAA, hιι]
  have hB4 : B ^ 4 = 1 := by
    rw [hB, conj_pow, hA4]
    simp
  have hBAB : B * A * B⁻¹ = A⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul, hAinv]
    exact hBA
  have hV2 : IsPGroup 2
      (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    isPGroup_two_zpowers_sup hA4 hB4 hBAB
  have hιV : ι ∈ (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [← hAA]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers A))
      (Subgroup.mem_sup_left (mem_zpowers A))
  have hAV : A ∈ (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.mem_sup_left (mem_zpowers A)
  have hBV : B ∈ (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Subgroup.mem_sup_right (mem_zpowers B)
  have hmapV : (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (MulAut.conj u).toMonoidHom ≤ zpowers A ⊔ zpowers B := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact hBV
    · change u * B * u⁻¹ ∈ _
      rw [huB]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hιV hAV) hBV
  have hconjV : ∀ t ∈ (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      u * t * u⁻¹ ∈ (zpowers A ⊔ zpowers B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    fun t ht => hmapV (Subgroup.mem_map.mpr ⟨t, ht, by simp [MulAut.conj_apply]⟩)
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← map_pow, coord_pow_prime J Nat.prime_three (by norm_num) z, map_one]
  have hu3' : u * u * u = 1 := by
    calc u * u * u = u ^ 3 := by rw [pow_succ, pow_two]
      _ = 1 := hu3
  have huN : u ∈ normalizer ((zpowers A ⊔ zpowers B :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    refine mem_normalizer_of_conj_le hconjV (fun t ht => ?_)
    have h2 : u⁻¹ * t * u = u * (u * t * u⁻¹) * u⁻¹ := by
      calc u⁻¹ * t * u = (u * u * u) * (u⁻¹ * t * u) * (u * u * u)⁻¹ := by rw [hu3']; group
        _ = u * (u * t * u⁻¹) * u⁻¹ := by group
    rw [h2]
    exact hconjV _ (hconjV t ht)
  refine ⟨zpowers A ⊔ zpowers B, hV2, huN, A, hAV, ?_⟩
  rw [hA, mul_smul, weyl_smul_pinf, torus_smul_pzero]
  exact (pinf_ne_pzero J hJ).symm

end Model

open CFSG.Open in
theorem u3TwoSignalizer_proved : KFactU3TwoSignalizer := by
  intro K _ _ hK T u hu hu3
  obtain ⟨d, hd, hfe, he⟩ := u3_index hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hf, hq, F, _, _, J, hJ, hKF, hfix, ⟨e⟩⟩ :=
    exists_equiv_psu (statedClassicalModel hd he)
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootGroup J hJ hKF hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e T S
  have hTR : (T : Subgroup K).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (normalizer ((T : Subgroup K) : Set K)).map e'.toMonoidHom =
      normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hTR]
  have hchar : CharP F 3 := charP_of_card Nat.prime_three hKF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F 3] at this
    omega
  have hfrob : ∀ x : F, J.conj x = x ^ 3 := by
    have := huppert_II_10_4_conj_eq_frobenius J (3 ^ d.1.fieldExponent) hKF hfix
    simpa [hfe] using this
  obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hu
  have huT : u ∈ (T : Subgroup K) := hwu ▸ w.2
  have hucomm : ∀ t ∈ (T : Subgroup K), t * u = u * t := by
    intro t ht
    have := Subgroup.mem_center_iff.mp hw ⟨t, ht⟩
    have h' := congrArg Subtype.val this
    rw [← hwu]
    exact h'
  have heuR : e' u ∈ rootGroup J hJ := hTR ▸ Subgroup.mem_map_of_mem _ huT
  have heuC : e' u ∈ Subgroup.centralizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rw [← hTR] at hr
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hr
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hucomm t ht]
  have heuι : e' u ∈ Subgroup.centralizer
      ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    have hmem : e' u ∈ rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := ⟨heuR, heuC⟩
    rw [← rootGroup_inf_centralizer_invol J hJ hKF hfix h2] at hmem
    exact hmem.2
  obtain ⟨z, hz⟩ := (mem_rootGroup J hJ).1 heuR
  have hz1 : z.1.1 = 0 := by
    rw [← hz] at heuι
    exact (root_mem_centralizer_invol_iff J hJ h2 z).1 heuι
  have hu1 : e' u ≠ 1 := by
    intro h
    have := e'.injective (h.trans (map_one e').symm)
    rw [this] at hu3
    simp at hu3
  have hc0 : z.1.2 ≠ 0 := by
    intro h0
    apply hu1
    rw [← hz, coord_eq_one_of_snd_eq_zero J h0, map_one]
  have hc : z.1.2 + J.conj z.1.2 = 0 := by
    have := z.2
    rw [hz1] at this
    simpa using this
  have hczs : skewCoord J z.1.2 hc = z := by
    apply Subtype.ext
    exact Prod.ext hz1.symm rfl
  have hcσ : J.conj z.1.2 = -z.1.2 := by linear_combination hc
  have hc2 : z.1.2 * z.1.2 = -1 := by
    have h1 : z.1.2 + z.1.2 ^ 3 = 0 := by rw [← hfrob]; exact hc
    have h2' : z.1.2 * (z.1.2 * z.1.2 + 1) = 0 := by linear_combination h1
    have := (mul_eq_zero.mp h2').resolve_left hc0
    linear_combination this
  obtain ⟨V, hV2, hVn, v, hvV, hvpinf⟩ := u3_model_two_group J hJ z.1.2 hc0 hcσ hc2
  rw [hczs, hz] at hVn
  set VK : Subgroup K := V.comap e'.toMonoidHom with hVK
  have hVK2 : IsPGroup 2 VK := by
    intro x
    obtain ⟨k, hk⟩ := hV2 ⟨e' x, x.2⟩
    refine ⟨k, Subtype.ext (e'.injective ?_)⟩
    have := congrArg Subtype.val hk
    simpa [map_pow] using this
  have hVKn : u ∈ normalizer (VK : Set K) := by
    rw [mem_normalizer_iff]
    intro h
    have := (mem_normalizer_iff.mp hVn) (e' h)
    simp only [hVK, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact this
  have hVKnot : ¬ VK ≤ normalizer ((T : Subgroup K) : Set K) := by
    intro hle
    have hv' : e'.symm v ∈ VK := by
      simpa [hVK] using hvV
    have hvN : e' (e'.symm v) ∈ (normalizer ((T : Subgroup K) : Set K)).map e'.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (hle hv')
    rw [hN, normalizer_rootGroup_eq_stabilizer_pinf J hJ hKF hfix
      (by rw [hfe]; norm_num)] at hvN
    exact hvpinf (by simpa using hvN)
  have hrank : 1 ≤ CFSG.Open.pRank 3 (T : Subgroup K) := by
    have hu3' : u ^ 3 = 1 := by
      have := pow_orderOf_eq_one u
      rwa [hu3] at this
    have hel := CFSG.AGLEmbedding.isElemAbelian_zpowers hu3'
    exact le_pRank_of_elemAbelian_card (p := 3) (k := 1) (zpowers_le.mpr huT) hel
      (by rw [Nat.card_zpowers, hu3]; norm_num)
  have hNΓ : normalizer ((T : Subgroup K) : Set K) ≤ rankThreeGamma 1 3 (T : Subgroup K) :=
    le_sSup ⟨T, le_rfl, hrank, rfl⟩
  have hVsup : VK ≤ sSup {V : Subgroup K | IsPGroup 2 V ∧ u ∈ normalizer (V : Set K)} :=
    le_sSup ⟨hVK2, hVKn⟩
  have hmax := (u3SylowData_proved K hK T).2.2.2.2.2
  have htop : normalizer ((T : Subgroup K) : Set K) ⊔ VK = ⊤ := by
    rcases hmax _ le_sup_left with h | h
    · exact absurd (sup_eq_left.mp h) hVKnot
    · exact h
  rw [← htop]
  exact sup_le_sup hNΓ hVsup


end CFSG.LocalAnalysis.RankThreeTheoremC
