module

public import CFSG.YGroups.Y443.Native.CoverFactsCx
public import Certificates.Certificate17594
public import Certificates.Certificate17595

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271.TabMThreeA

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated CFSG.YGroups
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native CFSG.Monster.B.Short CFSG.Open

theorem commute_pow_aux {G : Type*} [Group G] {A U c Ω t Z : G} (n : ℕ)
    (hA : c * A = A * c) (hΩ : Ω * c * Ω⁻¹ = t) (hW : Ω * (U * A) * Ω⁻¹ = Z)
    (h : c * (A * U) ^ n = (A * U) ^ n * c) : t * Z ^ n = Z ^ n * t := by
  have hA' : A⁻¹ * c * A = c := by
    calc A⁻¹ * c * A = A⁻¹ * (c * A) := by group
      _ = c := by rw [hA]; group
  have h1 : (A * U) ^ n = A * (U * A) ^ n * A⁻¹ := by
    calc (A * U) ^ n = (A * (U * A) * A⁻¹) ^ n := by congr 1; group
      _ = A * (U * A) ^ n * A⁻¹ := conj_pow
  have h2 : c * (U * A) ^ n = (U * A) ^ n * c := by
    rw [h1] at h
    calc c * (U * A) ^ n = (A⁻¹ * c * A) * (U * A) ^ n := by rw [hA']
      _ = A⁻¹ * (c * (A * (U * A) ^ n * A⁻¹)) * A := by group
      _ = A⁻¹ * ((A * (U * A) ^ n * A⁻¹) * c) * A := by rw [h]
      _ = (U * A) ^ n * (A⁻¹ * c * A) := by group
      _ = (U * A) ^ n * c := by rw [hA']
  have hZ : Z ^ n = Ω * (U * A) ^ n * Ω⁻¹ := by
    rw [← hW]; exact conj_pow
  calc t * Z ^ n = Ω * (c * (U * A) ^ n) * Ω⁻¹ := by rw [← hΩ, hZ]; group
    _ = Ω * ((U * A) ^ n * c) * Ω⁻¹ := by rw [h2]
    _ = Z ^ n * t := by rw [← hΩ, hZ]; group

theorem conj_W_aux {G : Type*} [Group G] {x4 c B A Ω p Z : G} (hc : c * c = 1) (hx : x4 * x4 = 1)
    (hP : Ω * (c * x4) = p * Ω) (hBA : Ω * (B * A) = p * Z * Ω) :
    Ω * ((x4 * c * B) * A) * Ω⁻¹ = Z := by
  have h1 : Ω * (c * x4) * Ω⁻¹ = p := by rw [hP]; group
  have h2 : Ω * (B * A) * Ω⁻¹ = p * Z := by rw [hBA]; group
  have h3 : x4 * c = (c * x4)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc x4 * c * (c * x4) = x4 * (c * c) * x4 := by group
      _ = 1 := by rw [hc, mul_one, hx]
  calc Ω * (x4 * c * B * A) * Ω⁻¹ = (Ω * (x4 * c) * Ω⁻¹) * (Ω * (B * A) * Ω⁻¹) := by group
    _ = (Ω * (c * x4)⁻¹ * Ω⁻¹) * (p * Z) := by rw [h3, h2]
    _ = p⁻¹ * (p * Z) := by
      rw [← h1]
      group
    _ = Z := by group

theorem no_comm_aux {t Z : SpaceB ≃ₗ[ℚ] SpaceB} {x : SpaceB}
    (hx : t x = x) (hmv : t ((Z ^ 17) x) ≠ (Z ^ 17) x) : t * Z ^ 17 ≠ Z ^ 17 * t := by
  intro key
  apply hmv
  calc t ((Z ^ 17) x) = (t * Z ^ 17) x := (LinearEquiv.mul_apply t (Z ^ 17) x).symm
    _ = (Z ^ 17 * t) x := by rw [key]
    _ = (Z ^ 17) (t x) := LinearEquiv.mul_apply (Z ^ 17) t x
    _ = (Z ^ 17) x := by rw [hx]

theorem commute_pow_V {G : Type*} [Group G]
    {T0 T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 c Ω p Z t : G}
    (hcc : c * c = 1) (h44 : T4 * T4 = 1)
    (hc0 : c * T0 = T0 * c) (hc1 : c * T1 = T1 * c) (hc2 : c * T2 = T2 * c)
    (hc3 : c * T3 = T3 * c) (hΩ : Ω * c * Ω⁻¹ = t) (hP : Ω * (c * T4) = p * Ω)
    (hBA : Ω * (T0 * T5 * T6 * T7 * T8 * T0 * T9 * T10 * (T0 * T1 * T2 * T3)) = p * Z * Ω)
    (h : c * (T0 * T1 * T2 * T3 * T4 * c * T0 * T5 * T6 * T7 * T8 * T0 * T9 * T10) ^ 17 =
      (T0 * T1 * T2 * T3 * T4 * c * T0 * T5 * T6 * T7 * T8 * T0 * T9 * T10) ^ 17 * c) :
    t * Z ^ 17 = Z ^ 17 * t := by
  have hA : c * (T0 * T1 * T2 * T3) = (T0 * T1 * T2 * T3) * c :=
    (((Commute.mul_right hc0 hc1).mul_right hc2).mul_right hc3).eq
  have hV : T0 * T1 * T2 * T3 * T4 * c * T0 * T5 * T6 * T7 * T8 * T0 * T9 * T10 =
      (T0 * T1 * T2 * T3) * (T4 * c * (T0 * T5 * T6 * T7 * T8 * T0 * T9 * T10)) := by
    simp only [mul_assoc]
  rw [hV] at h
  exact commute_pow_aux 17 hA hΩ (conj_W_aux hcc h44 hP hBA) h

@[expose] noncomputable def denseV :
    Gmat :=
  fM (y443Tl 0) * fM (y443Tl 1) * fM (y443Tl 2) * fM (y443Tl 3) * fM (y443Tl 4) * fM y443C *
    fM (y443Tl 0) * fM (y443Tl 5) * fM (y443Tl 6) * fM (y443Tl 7) * fM (y443Tl 8) *
    fM (y443Tl 0) * fM (y443Tl 9) * fM (y443Tl 10)

theorem fM_Tl_mul_Tl
    (a b : ℕ) :
    fM (y443Tl a) * fM (y443Tl b) = (EdgeNoncomm.agC a)⁻¹ * EdgeNoncomm.agC b := by
  rw [← map_mul]
  show fM (y443T (y443GenOfLetter a) * y443T (y443GenOfLetter b)) =
    (EdgeNoncomm.agS (y443GenOfLetter a))⁻¹ * EdgeNoncomm.agS (y443GenOfLetter b)
  rw [EdgeNoncomm.y443T_mul_eq, map_mul, map_inv, EdgeNoncomm.fM_axS, EdgeNoncomm.fM_axS]

theorem fM_C_comm_Tl
    {i : ℕ} (hi : i < 12) (hi4 : i ≠ 4) :
    fM y443C * fM (y443Tl i) = fM (y443Tl i) * fM y443C := by
  have h := y443C_comm_T (s := y443GenOfLetter i) (by
    intro hs
    have h4 := y443LetterOfGen_eq_four_iff.2 hs
    rw [y443LetterOfGen_genOfLetter i hi] at h4
    exact hi4 h4)
  rw [← map_mul, ← map_mul]
  exact congrArg fM h.symm

theorem BA_eq_pairsProd :
    fM (y443Tl 0) * fM (y443Tl 5) * fM (y443Tl 6) * fM (y443Tl 7) * fM (y443Tl 8) *
      fM (y443Tl 0) * fM (y443Tl 9) * fM (y443Tl 10) *
      (fM (y443Tl 0) * fM (y443Tl 1) * fM (y443Tl 2) * fM (y443Tl 3)) =
    EdgeNoncomm.pairsProd densePairs := by
  simp only [EdgeNoncomm.pairsProd, densePairs, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, ← fM_Tl_mul_Tl, mul_assoc]

@[expose] noncomputable def gmatOp : Gmat →* (SpaceB ≃ₗ[ℚ] SpaceB) := Gmat.subtype

theorem gmatOp_pairsProd
    {ps : List (ℕ × ℕ)} (h : ∀ p ∈ ps, p.1 < 12 ∧ p.2 < 12) :
    gmatOp (EdgeNoncomm.pairsProd ps) = wordLin (EdgeNoncomm.pairsWord ps) :=
  EdgeNoncomm.coe_pairsProd h

theorem denseAlign_wordLin :
    wordLin omegaWord * wordLin (EdgeNoncomm.pairsWord densePairs) =
      wordLin coverPHat * wordLin denseZWord * wordLin omegaWord := by
  obtain ⟨ha, hb, hw⟩ := Certificates.certificate17594
  have h := eq_of_eqWords ha hb hw
  simp only [wordLin_append] at h
  rw [h, mul_assoc]

theorem denseMove_sound {v : Native.DVec}
    (h : denseMoveCheck v = true) :
    wordLin tWord (interp v) = interp v ∧
      wordLin tWord ((wordLin denseZWord ^ 17) (interp v)) ≠
        (wordLin denseZWord ^ 17) (interp v) := by
  unfold denseMoveCheck at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hz, he⟩, hm⟩ := h
  have hzv : ∀ g ∈ denseZWord, g.validB = true := fun g hg => List.all_eq_true.1 hz g hg
  have htv : ∀ g ∈ tWord, g.validB = true := by
    intro g hg
    simp only [tWord, List.mem_singleton] at hg
    subst hg
    rfl
  have hpv : ∀ g ∈ powL 17 denseZWord, g.validB = true := by
    intro g hg
    simp only [powL, List.mem_flatten, List.mem_replicate] at hg
    obtain ⟨l, ⟨_, rfl⟩, hl⟩ := hg
    exact hzv g hl
  refine ⟨?_, ?_⟩
  · have h1 := eqv_sound he
    rwa [evalWord_sound tWord htv v] at h1
  · have h1 := EdgeNoncomm.moveCheck_sound hm
    rwa [evalWord_sound (powL 17 denseZWord) hpv v, wordLin_powL] at h1

theorem fM_C_mul_denseV_pow_ne :
    fM y443C * denseV ^ 17 ≠ denseV ^ 17 * fM y443C := by
  intro h
  have hι := congrArg gmatOp h
  simp only [denseV, map_mul, map_pow] at hι
  have hcc : gmatOp (fM y443C) * gmatOp (fM y443C) = 1 := by
    rw [← map_mul, ← map_mul, y443C_mul_self, map_one, map_one]
  have h44 : gmatOp (fM (y443Tl 4)) * gmatOp (fM (y443Tl 4)) = 1 := by
    rw [← map_mul, ← map_mul, y443Tl_mul_self, map_one, map_one]
  have hcT : ∀ {i : ℕ}, i < 12 → i ≠ 4 →
      gmatOp (fM y443C) * gmatOp (fM (y443Tl i)) = gmatOp (fM (y443Tl i)) * gmatOp (fM y443C) := by
    intro i hi hi4
    rw [← map_mul gmatOp, ← map_mul gmatOp, fM_C_comm_Tl hi hi4]
  have hP : wordLin omegaWord * (gmatOp (fM y443C) * gmatOp (fM (y443Tl 4))) =
      wordLin coverPHat * wordLin omegaWord := by
    rw [← map_mul, ← EdgeNoncomm.y443X_eq, EdgeNoncomm.fM_C_X,
      gmatOp_pairsProd EdgeNoncomm.nP_lt]
    exact cover_comm_p
  have hBA := denseAlign_wordLin
  rw [← gmatOp_pairsProd (ps := densePairs) (by decide), ← BA_eq_pairsProd] at hBA
  simp only [map_mul] at hBA
  have key := commute_pow_V hcc h44 (hcT (i := 0) (by norm_num) (by norm_num))
    (hcT (i := 1) (by norm_num) (by norm_num)) (hcT (i := 2) (by norm_num) (by norm_num))
    (hcT (i := 3) (by norm_num) (by norm_num)) omega_conj hP hBA hι
  obtain ⟨hv, hmv⟩ := denseMove_sound (v := wV ()) Certificates.certificate17595
  rw [wordLin_tWord] at hv hmv
  exact no_comm_aux hv hmv key

end CFSG.HardMathSupport.Dickson.I271.TabMThreeA
