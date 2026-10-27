module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3Tr
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepH3SpAlg
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55StepHStmts
public import CFSG.RankThree.SubgroupLists.SymplecticTransvections

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
  CFSG.RankThree.SubgroupLists CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
  (conjAut_mul_fieldAut_eq_one_iff)

namespace StepH3Sp

variable {K : Type} [Field K]

@[expose] def spElatImage (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    Subgroup (StatedProj (StatedSp 2 K)) :=
  ((glElat W).comap (StatedSp 2 K).subtype).map (proj 2 K)

theorem isPGroup_spElatImage {r : ℕ} [CharP K r] (W : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    IsPGroup r ↥(spElatImage W) :=
  ((isPGroup_glElat W).comap_of_injective _ Subtype.coe_injective).map _

theorem conjAut_mem_spElatImage {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (A : gsp 2 K)
    (hA : ∀ w ∈ W,
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w ∈ W)
    (hA' : ∀ w ∈ W,
      (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w ∈ W)
    {x : StatedProj (StatedSp 2 K)} (hx : x ∈ spElatImage W) :
    conjAut 2 K A x ∈ spElatImage W := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [conjAut_proj]
  refine Subgroup.mem_map_of_mem _ ?_
  rw [Subgroup.mem_comap, Subgroup.coe_subtype, coe_conjSp]
  exact conj_mem_glElat hA hA' hg

theorem proj_spTrans_ne_one {u : Fin 2 ⊕ Fin 2 → K} (hu : u ≠ 0) :
    proj 2 K (⟨spTrans u 1, spTrans_mem_statedSp u 1⟩ : StatedSp 2 K) ≠ 1 := by
  intro h
  have hmem := (QuotientGroup.eq_one_iff _).mp h
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
  have hcM : Matrix.scalar (Fin 2 ⊕ Fin 2) (c : K) = spTransMat u 1 :=
    congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
  have hTu : spTransMat u (1 : K) *ᵥ u = u := by
    rw [spTransMat_mulVec, spForm_self, mul_zero, zero_smul, add_zero]
  have hc1 : (c : K) = 1 := by
    rw [← hcM, scalar_apply] at hTu
    obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hu (funext hall)
    have h3 := congrFun hTu i
    rw [mulVec_diagonal] at h3
    exact mul_right_cancel₀ hi (by rw [h3, one_mul])
  have hzero : ∀ v, spForm 2 K v u = 0 := by
    intro v
    have h4 : spTransMat u (1 : K) *ᵥ v = v := by
      rw [← hcM, hc1, map_one, Matrix.one_mulVec]
    rw [spTransMat_mulVec, one_mul, add_eq_left] at h4
    by_contra hne
    apply hu
    have h5 := congrArg (fun x => (spForm 2 K v u)⁻¹ • x) h4
    simp only [smul_zero, smul_smul, inv_mul_cancel₀ hne, one_smul] at h5
    exact h5
  apply hu
  refine spForm_separatingLeft u fun y => ?_
  rw [spForm_antisymm, hzero y, neg_zero]

theorem exists_rgroup_of_inner {r : ℕ} [CharP K r] [Finite K] (A : gsp 2 K) {c : K} (hc : c ≠ 0)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 3 =
      c • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, conjAut 2 K A x ∈ E := by
  set M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  obtain ⟨u, hu0, hu⟩ := exists_ne_zero_spForm_eq_zero le_rfl M
  set W := orbI M u with hW
  have hiso : ∀ x ∈ W, ∀ y ∈ W, spForm 2 K x y = 0 := fun x hx y hy =>
    spForm_eq_zero_of_mem_orbI A hA hu hx hy
  have huW : u ∈ W := self_mem_orbI M u
  set t : StatedSp 2 K := ⟨spTrans u 1, spTrans_mem_statedSp u 1⟩ with ht
  have htmem : (t : GL (Fin 2 ⊕ Fin 2) K) ∈ glElat W := by
    have hsub : ∀ v, (spTransMat u (1 : K) - 1) *ᵥ v = (spForm 2 K v u) • u := by
      intro v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, spTransMat_mulVec, one_mul, add_sub_cancel_left]
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · change (spTransMat u (1 : K) - 1) *ᵥ v ∈ W
      rw [hsub]
      exact W.smul_mem _ huW
    · change (spTransMat u (1 : K) - 1) *ᵥ w = 0
      rw [hsub, hiso w hw u huW, zero_smul]
  refine ⟨spElatImage W, ?_, isPGroup_spElatImage W, fun x hx =>
    conjAut_mem_spElatImage A (fun w hw => mulVec_mem_orbI hA u hw)
      (fun w hw => inv_mulVec_mem_orbI hc hA u hw) hx⟩
  intro hbot
  have hx : proj 2 K t ∈ spElatImage W := Subgroup.mem_map_of_mem _ htmem
  rw [hbot, Subgroup.mem_bot] at hx
  exact proj_spTrans_ne_one hu0 hx

theorem spTransMat_map_basis (σ : K ≃+* K) :
    (spTransMat (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) (1 : K)).map σ =
      spTransMat (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) (1 : K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spTransMat, vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_rgroup_of_field {r : ℕ} [hr : Fact r.Prime] [CharP K r] (H : gsp 2 K)
    (σ : K ≃+* K) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧
      ∀ x ∈ E, (conjAut 2 K H * fieldAut 2 K σ * (conjAut 2 K H)⁻¹) x ∈ E := by
  set e : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inr 0) 1 with he
  have he0 : e ≠ 0 := by
    intro h
    have h3 := congrFun h (Sum.inr 0)
    simp [he] at h3
  set t : StatedSp 2 K := ⟨spTrans e 1, spTrans_mem_statedSp e 1⟩ with ht
  have htσ : fieldSp 2 K σ t = t := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp]
    exact spTransMat_map_basis σ
  have hinv : ∀ y, (conjAut 2 K H)⁻¹ (conjAut 2 K H y) = y := fun y => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  set x : StatedProj (StatedSp 2 K) := conjAut 2 K H (proj 2 K t) with hx
  have hfix : (conjAut 2 K H * fieldAut 2 K σ * (conjAut 2 K H)⁻¹) x = x := by
    rw [hx, MulAut.mul_apply, MulAut.mul_apply, hinv, fieldAut_proj, htσ]
  have htr : t ^ r = 1 := by
    have hmem : (t : GL (Fin 2 ⊕ Fin 2) K) ∈
        glElat (Submodule.span K {e} : Submodule K (Fin 2 ⊕ Fin 2 → K)) := by
      have hsub : ∀ v, (spTransMat e (1 : K) - 1) *ᵥ v = (spForm 2 K v e) • e := by
        intro v
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, spTransMat_mulVec, one_mul,
          add_sub_cancel_left]
      refine ⟨fun v => ?_, fun w hw => ?_⟩
      · change (spTransMat e (1 : K) - 1) *ᵥ v ∈ _
        rw [hsub]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
      · change (spTransMat e (1 : K) - 1) *ᵥ w = 0
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [hsub, map_smul, LinearMap.smul_apply, spForm_self, smul_zero, zero_smul]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_char_eq_one_of_mem_glElat hmem
  have hxr : x ^ r = 1 := by
    rw [hx, ← map_pow, ← map_pow, htr, map_one, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h4 : conjAut 2 K H (proj 2 K t) = conjAut 2 K H 1 := by rw [map_one, ← hx, h]
    exact proj_spTrans_ne_one he0 ((conjAut 2 K H).injective h4)
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

theorem ord3_psp4 {r : ℕ} [Fact r.Prime] [CharP K r] [Finite K] (hr2 : r ≠ 2)
    (α : MulAut (StatedProj (StatedSp 2 K))) (hα : α ^ 3 = 1) :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, α x ∈ E := by
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K r]; exact hr2
  by_cases hD : α ∈ (conjAut 2 K).range
  · obtain ⟨A, rfl⟩ := hD
    have h1 : conjAut 2 K (A ^ 3) * fieldAut 2 K 1 = 1 := by
      rw [map_one, mul_one, map_pow, hα]
    obtain ⟨-, c, hc⟩ := (conjAut_mul_fieldAut_eq_one_iff (by norm_num) _ _).mp h1
    have hA3 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 3 =
        (c : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      have h := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val] at h
      rw [h, smul_one_eq_diagonal]
      rfl
    exact exists_rgroup_of_inner A c.ne_zero hA3
  · obtain ⟨σ, -, H, rfl⟩ :=
      CFSG.RankThree.PartTwo.KFacts.psp4_odd_order_three_field_descent hodd α hα hD
    exact exists_rgroup_of_field H σ

end StepH3Sp

theorem ord3_fsp4d : Ord3 FSp4d := by
  intro r Y _ _ hr hr2 _ hY b hb
  obtain ⟨f, -, hLM⟩ := hY
  have hcm : StatedClassicalModel Y .PSp 2 r f := by
    rcases hLM with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact hc
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hcm
  have : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K r :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  change Ord3Concl r Y b
  apply Ord3Concl.of_mulEquiv e
  have hb3 : b ^ 3 = 1 := by
    rw [← hb]
    exact pow_orderOf_eq_one b
  have hα : (MulAut.congr e b) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  exact Or.inl (StepH3Sp.ord3_psp4 hr2 _ hα)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
