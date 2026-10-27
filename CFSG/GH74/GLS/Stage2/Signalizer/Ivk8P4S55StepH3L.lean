module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3LAlg
public import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

namespace StepH3L

variable {K : Type} [Field K] {n : ℕ}

theorem conjAut_inv_apply_self (A : GL (Fin n) K) (y : projectiveSL n K) :
    (conjAut n K A)⁻¹ (conjAut n K A y) = y := by
  rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem exists_rgroup_of_orbitSpan {r : ℕ} [CharP K r] (A : GL (Fin n) K) {c : K} (hc : c ≠ 0)
    (hA : (A : Matrix (Fin n) (Fin n) K) ^ 3 = c • (1 : Matrix (Fin n) (Fin n) K))
    {v : Fin n → K} (hv : v ≠ 0) (htop : orbitSpan (A : Matrix (Fin n) (Fin n) K) v ≠ ⊤) :
    ∃ E : Subgroup (projectiveSL n K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, conjAut n K A x ∈ E :=
  ⟨(elat (orbitSpan (A : Matrix (Fin n) (Fin n) K) v)).map (proj n K),
    map_elat_ne_bot (orbitSpan_ne_bot _ hv) htop, (isPGroup_elat _).map _,
    fun _ hx => conjAut_mem_map_elat (fun _ hw => mulVec_mem_orbitSpan hA v hw)
      (fun _ hw => inv_mulVec_mem_orbitSpan hc hA v hw) hx⟩

theorem hhObs_of_isUnit_cycMat (h2 : (2 : K) ≠ 0) (A : GL (Fin 3) K) {c : K} (hc : c ≠ 0)
    (hA : (A : Matrix (Fin 3) (Fin 3) K) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) K))
    {v : Fin 3 → K} (hB : IsUnit (cycMat (A : Matrix (Fin 3) (Fin 3) K) v).det) :
    HHObsAt 3 2 (projectiveSL 3 K) (conjAut 3 K A) := by
  set B : Matrix (Fin 3) (Fin 3) K := cycMat (A : Matrix (Fin 3) (Fin 3) K) v with hBdef
  have hBu : IsUnit B := (Matrix.isUnit_iff_isUnit_det B).mpr hB
  set BG : GL (Fin 3) K := hBu.unit with hBG
  have hBGc : (BG : Matrix (Fin 3) (Fin 3) K) = B := hBu.unit_spec
  have hAeq : A = BG * companGL hc * BG⁻¹ := by
    apply Units.ext
    have h1 : (A : Matrix (Fin 3) (Fin 3) K) * (BG : Matrix (Fin 3) (Fin 3) K) =
        (BG : Matrix (Fin 3) (Fin 3) K) * compan c := by
      rw [hBGc]
      exact mul_cycMat hA v
    rw [Units.val_mul, Units.val_mul]
    change (A : Matrix (Fin 3) (Fin 3) K) =
      (BG : Matrix (Fin 3) (Fin 3) K) * compan c *
        ((BG⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hact : ∀ g : SpecialLinearGroup (Fin 3) K,
      conjAut 3 K A (conjAut 3 K BG (proj 3 K g)) =
        conjAut 3 K BG
          (proj 3 K (CatalogueBHigherLinearAction.slConjugation 3 K (companGL hc) g)) := by
    intro g
    rw [hAeq, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply,
      conjAut_inv_apply_self, conjAut_proj]
  set E : Subgroup (projectiveSL 3 K) :=
    (signDiag.map (proj 3 K)).map (conjAut 3 K BG).toMonoidHom with hE
  have hmemE : ∀ g ∈ signDiag, conjAut 3 K BG (proj 3 K g) ∈ E := fun g hg =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hg)
  have hEx : ∀ x ∈ E, ∃ g ∈ signDiag, x = conjAut 3 K BG (proj 3 K g) := by
    rintro x ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  refine ⟨Nat.prime_two, by norm_num, E, (isPGroup_signDiag.map _).map _, fun _ x hx y hy => ?_,
    fun x hx => ?_, conjAut 3 K BG (proj 3 K sgn0), hmemE _ sgn0_mem, ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hEx x hx
    obtain ⟨h, hh, rfl⟩ := hEx y hy
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, commute_of_mem_signDiag hg hh]
  · obtain ⟨g, hg, rfl⟩ := hEx x hx
    rw [hact]
    exact hmemE _ (slConjugation_companGL_mem_signDiag hc hg)
  · rw [hact, slConjugation_companGL_sgn0]
    intro h
    exact proj_sgn1_ne_proj_sgn0 h2 ((conjAut 3 K BG).injective h)

theorem exists_rgroup_of_field {r : ℕ} [hr : Fact r.Prime] [CharP K r] (hn : 2 ≤ n)
    (H : GL (Fin n) K) (σ : K ≃+* K) :
    ∃ E : Subgroup (projectiveSL n K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, (conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹) x ∈ E := by
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by
    rw [hi, hj, Ne, Fin.ext_iff]
    norm_num
  set t : SpecialLinearGroup (Fin n) K := ⟨transvection i j 1, det_transvection_of_ne i j hij 1⟩
    with ht
  have htsub : (t : Matrix (Fin n) (Fin n) K) - 1 = single i j 1 := by
    change transvection i j (1 : K) - 1 = _
    rw [transvection, add_sub_cancel_left]
  have htmem : t ∈ elat (Submodule.span K {(Pi.single i 1 : Fin n → K)}) := by
    rw [mem_elat, htsub]
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · rw [single_mulVec, Submodule.mem_span_singleton]
      refine ⟨v j, ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [hk]
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [single_mulVec]
      funext k
      by_cases hk : k = i
      · subst hk
        simp [hij.symm]
      · simp [hk]
  have htσ : SpecialLinearGroup.map (σ : K →+* K) t = t := by
    apply Subtype.ext
    change (transvection i j (1 : K)).map σ = transvection i j 1
    ext a b
    simp only [Matrix.map_apply, transvection, Matrix.add_apply, Matrix.one_apply, single_apply]
    split_ifs <;> simp
  set x : projectiveSL n K := conjAut n K H (proj n K t) with hx
  have hfix : (conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹) x = x := by
    rw [hx, MulAut.mul_apply, MulAut.mul_apply, conjAut_inv_apply_self, fieldAut_proj]
    change conjAut n K H (proj n K (SpecialLinearGroup.map (σ : K →+* K) t)) = _
    rw [htσ]
  have hxr : x ^ r = 1 := by
    rw [hx, ← map_pow, ← map_pow, pow_char_eq_one_of_mem_elat htmem, map_one, map_one]
  have ht1 : proj n K t ≠ 1 := by
    intro h
    obtain ⟨c, -, hc⟩ := proj_eq_one_iff.mp h
    have h3 : (transvection i j (1 : K)) i j = scalar (Fin n) (c : K) i j :=
      congrFun (congrFun hc i) j
    rw [scalar_apply, diagonal_apply_ne _ hij] at h3
    simp [transvection, hij] at h3
  have hx1 : x ≠ 1 := by
    intro h
    have h4 : conjAut n K H (proj n K t) = conjAut n K H 1 := by rw [map_one, ← hx, h]
    exact ht1 ((conjAut n K H).injective h4)
  refine ⟨zpowers x, ?_, ?_, ?_⟩
  · intro h
    apply hx1
    have h5 := mem_zpowers x
    rw [h, Subgroup.mem_bot] at h5
    exact h5
  · have hord : orderOf x ∣ r ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one hxr
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hr.out).mp hord
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hm])
  · intro y hy
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
    rw [map_zpow, hfix]
    exact zpow_mem (mem_zpowers x) k

theorem ord3_psl {r : ℕ} [Fact r.Prime] [CharP K r] [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (α : MulAut (projectiveSL n K)) (hα : α ^ 3 = 1) :
    (∃ E : Subgroup (projectiveSL n K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, α x ∈ E) ∨
      (n = 3 ∧ HHObsAt 3 2 (projectiveSL n K) α) := by
  by_cases hD : α ∈ linearAutGroup n K
  · obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hD
    have h1 : conjAut n K (A ^ 3) * fieldAut n K 1 = 1 := by rw [map_one, mul_one, map_pow, hα]
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h1
    have hA3 : (A : Matrix (Fin n) (Fin n) K) ^ 3 = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      have h := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hc
      simp only [Units.val_pow_eq_pow_val] at h
      rw [← h, smul_one_eq_diagonal]
      rfl
    set v : Fin n → K := Pi.single ⟨0, by omega⟩ 1 with hvdef
    have hv : v ≠ 0 := by
      intro h
      have h3 := congrFun h ⟨0, by omega⟩
      simp [hvdef] at h3
    by_cases h4 : 4 ≤ n
    · exact Or.inl (exists_rgroup_of_orbitSpan A c.ne_zero hA3 hv
        (orbitSpan_ne_top_of_four h4 _ _))
    · obtain rfl : n = 3 := by omega
      by_cases hB : IsUnit (cycMat (A : Matrix (Fin 3) (Fin 3) K) v).det
      · exact Or.inr ⟨rfl, hhObs_of_isUnit_cycMat h2 A c.ne_zero hA3 hB⟩
      · exact Or.inl (exists_rgroup_of_orbitSpan A c.ne_zero hA3 hv
          (orbitSpan_ne_top_of_not_isUnit hB))
  · obtain ⟨σ, -, H, rfl⟩ :=
      CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent hn α hα hD
    exact Or.inl (exists_rgroup_of_field (by omega) H σ)

theorem two_ne_zero_of_charP {r : ℕ} [CharP K r] (hr : r.Prime) (hr2 : r ≠ 2) : (2 : K) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff K r 2).mp h'))

theorem exists_model {r f : ℕ} (hr : r.Prime) {Y : Type} [Group Y]
    (h : CFSG.Blueprint.LieModel Y .PSL n r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r),
      Nonempty (Y ≃* projectiveSL n K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact ⟨K, inferInstance, inferInstance, this, ⟨e⟩⟩

end StepH3L

theorem ord3_fl4d : Ord3 FL4d := by
  intro r Y _ _ hr hr2 _ hY b hb
  obtain ⟨f, -, -, hLM⟩ := hY
  obtain ⟨K, _, _, _, ⟨e⟩⟩ := StepH3L.exists_model hr hLM
  have : Fact r.Prime := ⟨hr⟩
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hb3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hα : (MulAut.congr e b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  rcases StepH3L.ord3_psl (StepH3L.two_ne_zero_of_charP hr hr2) (by norm_num) _ hα with
    h | ⟨h43, -⟩
  · exact Or.inl h
  · exact absurd h43 (by norm_num)

theorem ord3_fl3d_of_noR
    (hN : ∀ (r : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → r ≠ 3 → FL3d r Y →
      NoR 2 Y) : Ord3 FL3d := by
  intro r Y _ _ hr hr2 hr3 hY b hb
  have hNY := hN r Y hr hr2 hr3 hY
  obtain ⟨f, -, hLM⟩ := hY
  obtain ⟨K, _, _, _, ⟨e⟩⟩ := StepH3L.exists_model hr hLM
  have : Fact r.Prime := ⟨hr⟩
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hb3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hα : (MulAut.congr e b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  rcases StepH3L.ord3_psl (StepH3L.two_ne_zero_of_charP hr hr2) le_rfl _ hα with h | ⟨-, hobs⟩
  · exact Or.inl h
  · exact Or.inr ⟨2, hobs, fun _ => NoR.of_mulEquiv e.symm hNY⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
