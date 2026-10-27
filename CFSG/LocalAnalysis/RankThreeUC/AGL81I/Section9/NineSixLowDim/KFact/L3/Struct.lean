module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.NineSixLowDim.KFact.L3.Defs
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact

open Matrix CFSG.RepresentationTheory
open scoped Pointwise

variable {F : Type} [Field F]

private lemma omega_facts {ω : F} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    1 + ω + ω ^ 2 = 0 ∧ ω ^ 2 ≠ 1 ∧ ω ^ 2 ≠ ω ∧ (3 : F) ≠ 0 := by
  have h1 : 1 + ω + ω ^ 2 = 0 := by
    have : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω)
  refine ⟨h1, fun h => hω ?_, fun h => hω ?_, fun h => hω ?_⟩
  · linear_combination hω3 - ω * h
  · linear_combination hω3 - (ω + 1) * h
  · have : (ω - 1) ^ 3 = 0 := by linear_combination hω3 - (ω ^ 2 - ω) * h
    exact sub_eq_zero.mp ((pow_eq_zero_iff (n := 3) (by norm_num)).mp this)

private lemma val_omega {ω : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    (ω : F) ≠ 1 ∧ (ω : F) ^ 3 = 1 :=
  ⟨fun h => hω (Units.val_eq_one.mp h), by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]⟩

private lemma val_diagOmega (ω : Fˣ) :
    ((diagOmega ω : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![1, (ω : F), (ω : F) ^ 2] := by
  change diagonal (fun i => ((![1, ω, ω ^ 2] i : Fˣ) : F)) = _
  congr 1; funext i; fin_cases i <;> simp

private lemma val_cycMat (μ : Fˣ) :
    ((cycMat μ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = !![0, 0, (μ : F); 1, 0, 0; 0, 1, 0] :=
  rfl

private lemma cycMatrix_mulVec (μ : F) (w : Fin 3 → F) :
    !![0, 0, μ; 1, 0, 0; 0, 1, 0] *ᵥ w = ![μ * w 2, w 0, w 1] := by
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private lemma smul_single_mem {ω : F} (h1 : 1 + ω + ω ^ 2 = 0) (hω3 : ω ^ 3 = 1)
    {W : Submodule F (Fin 3 → F)} (hA : ∀ w ∈ W, diagonal ![1, ω, ω ^ 2] *ᵥ w ∈ W)
    {v : Fin 3 → F} (hv : v ∈ W) : (3 * v 0) • (Pi.single 0 1 : Fin 3 → F) ∈ W := by
  have := W.add_mem (W.add_mem hv (hA v hv)) (hA _ (hA v hv))
  convert this using 1
  ext i; fin_cases i <;> simp [mulVec_diagonal]
  · ring
  · linear_combination (-v 1) * h1
  · linear_combination (-v 2) * h1 + (-v 2 * ω) * hω3

theorem isIrreducible_of_mem {ω μ : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {G : Subgroup (GL (Fin 3) F)} (ha : diagOmega ω ∈ G) (hb : cycMat μ ∈ G) :
    IsIrreducibleMatrixRep G.subtype := by
  intro W hW
  obtain ⟨hω', hω3'⟩ := val_omega hω hω3
  obtain ⟨h1, -, -, h3⟩ := omega_facts hω' hω3'
  have hA : ∀ w ∈ W, diagonal ![1, (ω : F), (ω : F) ^ 2] *ᵥ w ∈ W := fun w hw => by
    have h := hW ⟨_, ha⟩ w hw
    change ((diagOmega ω : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W at h
    rwa [val_diagOmega] at h
  have hB : ∀ w ∈ W, ![(μ : F) * w 2, w 0, w 1] ∈ W := fun w hw => by
    have h := hW ⟨_, hb⟩ w hw
    change ((cycMat μ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W at h
    rwa [val_cycMat, cycMatrix_mulVec] at h
  have he0 : ∀ v ∈ W, v 0 ≠ 0 → (Pi.single 0 1 : Fin 3 → F) ∈ W := fun v hv h0 => by
    have := W.smul_mem (3 * v 0)⁻¹ (smul_single_mem h1 hω3' hA hv)
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero h3 h0), one_smul] at this
  rcases eq_or_ne W ⊥ with hbot | hbot
  · exact Or.inl hbot
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  have hμ : (μ : F) ≠ 0 := μ.ne_zero
  have hE0 : (Pi.single 0 1 : Fin 3 → F) ∈ W := by
    by_cases h0 : w 0 = 0
    · by_cases h1' : w 1 = 0
      · have h2 : w 2 ≠ 0 := fun h2 => hw0 (by ext i; fin_cases i <;> simp [h0, h1', h2])
        exact he0 _ (hB w hw) (by simp [hμ, h2])
      · exact he0 _ (hB _ (hB w hw)) (by simp [hμ, h1'])
    · exact he0 w hw h0
  have hE1 : (Pi.single 1 1 : Fin 3 → F) ∈ W := by
    convert hB _ hE0 using 1; ext i; fin_cases i <;> simp
  have hE2 : (Pi.single 2 1 : Fin 3 → F) ∈ W := by
    convert hB _ hE1 using 1; ext i; fin_cases i <;> simp
  rw [eq_top_iff]
  intro x _
  convert W.add_mem (W.add_mem (W.smul_mem (x 0) hE0) (W.smul_mem (x 1) hE1))
    (W.smul_mem (x 2) hE2) using 1
  ext i; fin_cases i <;> simp

private lemma conj_mem_fixSetThree {p : ℕ} {A : Subgroup (GL (Fin 3) F)} {e : GL (Fin 3) F}
    (he : e ∈ A) {x : GL (Fin 3) F} (hx : x ∈ fixSetThree p A) :
    e * x * e⁻¹ ∈ fixSetThree p A := by
  obtain ⟨hdet, hord, g, hgA, hgZ, hgx⟩ := hx
  refine ⟨?_, ?_, e * g * e⁻¹, A.mul_mem (A.mul_mem he hgA) (A.inv_mem he), fun h => hgZ ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, det_one]
  · rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  · simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ h e⁻¹
  · calc e * g * e⁻¹ * (e * x * e⁻¹) = e * (g * x) * e⁻¹ := by group
      _ = e * (x * g) * e⁻¹ := by rw [hgx]
      _ = e * x * e⁻¹ * (e * g * e⁻¹) := by group

theorem conj_mem_closure_fixSetThree {p : ℕ} {A : Subgroup (GL (Fin 3) F)}
    (_hA : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center (GL (Fin 3) F)) {e : GL (Fin 3) F}
    (he : e ∈ A) {x : GL (Fin 3) F} (hx : x ∈ Subgroup.closure (fixSetThree p A)) :
    e * x * e⁻¹ ∈ Subgroup.closure (fixSetThree p A) := by
  have hle : Subgroup.closure (fixSetThree p A) ≤
      (Subgroup.closure (fixSetThree p A)).comap (MulAut.conj e).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun y hy => Subgroup.subset_closure (conj_mem_fixSetThree he hy)
  simpa using hle hx

private lemma le_ker_of_isPerfect {G Q : Type*} [Group G] [Group Q] [Group.IsSolvable Q]
    (H : Subgroup G) [Group.IsPerfect H] (f : G →* Q) : H ≤ f.ker := by
  have : Group.IsPerfect (H.map f) := Group.IsPerfect.map f
  have : Subsingleton (H.map f) := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    exact Group.IsPerfect.not_isSolvable (H.map f) inferInstance
  rw [← Subgroup.map_eq_bot_iff]
  exact Subgroup.eq_bot_of_subsingleton _

private lemma isSolvable_of_commutator_mem_center {G : Type*} [Group G] (A : Subgroup G)
    (hA : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center G) : Group.IsSolvable A := by
  let Z := (Subgroup.center G).subgroupOf A
  have : Group.IsSolvable Z := Group.isSolvable_of_comm fun a b => by
    ext; simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp b.2) _
  have : Group.IsSolvable (A ⧸ Z) := Group.isSolvable_of_comm fun a b => by
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    convert hA _ (A.inv_mem b.2) _ (A.inv_mem a.2) using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact Group.isSolvable_of_ker_le_range Z.subtype (QuotientGroup.mk' Z) (by simp)

theorem le_closure_fixSetThree_of_isPerfect {p : ℕ} {A : Subgroup (GL (Fin 3) F)}
    (hA : IsElemModScalars p A) {H : Subgroup (GL (Fin 3) F)} (hH : Group.IsPerfect H)
    (hle : H ≤ Subgroup.closure (fixSetThree p A) ⊔ A) :
    H ≤ Subgroup.closure (fixSetThree p A) := by
  set N := Subgroup.closure (fixSetThree p A)
  have hAN : A ≤ Subgroup.normalizer (N : Set (GL (Fin 3) F)) :=
    Subgroup.le_normalizer_iff.mpr fun e he _ hx =>
      conj_mem_closure_fixSetThree hA.commutator_mem he hx
  have : (N.subgroupOf (A ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  let π := QuotientGroup.mk' (N.subgroupOf (A ⊔ N))
  have hsurj : Function.Surjective (π.comp (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ N))) := by
    intro q
    induction q using QuotientGroup.induction_on with | H k => ?_
    have hk : (k : GL (Fin 3) F) ∈ (A : Set (GL (Fin 3) F)) * (N : Set (GL (Fin 3) F)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A N hAN]; exact k.2
    obtain ⟨a, ha, n, hn, hk⟩ := hk
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [MonoidHom.comp_apply, π, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [← hk] using hn
  have := isSolvable_of_commutator_mem_center A hA.commutator_mem
  have := hH
  have : Group.IsSolvable (↥(A ⊔ N) ⧸ N.subgroupOf (A ⊔ N)) := Group.isSolvable_of_surjective hsurj
  have hle' : H ≤ A ⊔ N := sup_comm N A ▸ hle
  have : Group.IsPerfect (H.subgroupOf (A ⊔ N)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hle').symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hker := le_ker_of_isPerfect (H.subgroupOf (A ⊔ N)) π
  rw [QuotientGroup.ker_mk'] at hker
  intro h hh
  exact Subgroup.mem_subgroupOf.mp
    (hker (show (⟨h, hle' hh⟩ : ↥(A ⊔ N)) ∈ H.subgroupOf (A ⊔ N) from hh))

private lemma eq_diagonal_of_mul_comm {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n F} {d : n → F} (hd : Function.Injective d)
    (h : M * diagonal d = diagonal d * M) : M = diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · have hij' := congrFun (congrFun h i) j
    simp only [mul_diagonal, diagonal_mul] at hij'
    rw [diagonal_apply_ne _ hij]
    have hne : d j - d i ≠ 0 := sub_ne_zero.mpr fun h' => hij (hd h').symm
    have : M i j * (d j - d i) = 0 := by linear_combination hij'
    exact (mul_eq_zero.mp this).resolve_right hne

private lemma commute_of_diagonal_injective {n : Type*} [Fintype n] [DecidableEq n]
    {e : n → F} (he : Function.Injective e) {x y : Matrix n n F}
    (hx : x * diagonal e = diagonal e * x) (hy : y * diagonal e = diagonal e * y) :
    x * y = y * x := by
  rw [eq_diagonal_of_mul_comm he hx, eq_diagonal_of_mul_comm he hy, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1; funext i; ring

private lemma injective_fin_three {α : Type*} {e : Fin 3 → α} (h01 : e 0 ≠ e 1)
    (h02 : e 0 ≠ e 2) (h12 : e 1 ≠ e 2) : Function.Injective e := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact absurd h h01 | exact absurd h h02 | exact absurd h h12 |
      exact absurd h.symm h01 | exact absurd h.symm h02 | exact absurd h.symm h12

private def polyThree (M : Matrix (Fin 3) (Fin 3) F) (c : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  c 0 • 1 + c 1 • M + c 2 • (M * M)

private lemma commute_of_cyclic {M x y : Matrix (Fin 3) (Fin 3) F} (v : Fin 3 → F)
    (hspan : ∀ w, ∃ c, w = polyThree M c *ᵥ v) (hx : x * M = M * x) (hy : y * M = M * y) :
    x * y = y * x := by
  have hP : ∀ N, Commute N M → ∀ c, Commute N (polyThree M c) := fun N hN c =>
    (((Commute.one_right N).smul_right _).add_right (hN.smul_right _)).add_right
      ((hN.mul_right hN).smul_right _)
  have hPP : ∀ c c', Commute (polyThree M c) (polyThree M c') := fun c c' =>
    hP _ (hP M (Commute.refl M) c).symm c'
  have key : ∀ N, N * M = M * N → ∃ c, N = polyThree M c := by
    intro N hN
    obtain ⟨c, hc⟩ := hspan (N *ᵥ v)
    refine ⟨c, Matrix.toLin'.injective (LinearMap.ext fun w => ?_)⟩
    obtain ⟨c', rfl⟩ := hspan w
    simp only [Matrix.toLin'_apply]
    rw [mulVec_mulVec, (hP N hN c').eq, ← mulVec_mulVec, hc, mulVec_mulVec, (hPP c' c).eq,
      ← mulVec_mulVec]
  obtain ⟨c, rfl⟩ := key x hx
  obtain ⟨c', rfl⟩ := key y hy
  exact (hPP c c').eq

private lemma commute_of_shift {ω : F} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {M x y : Matrix (Fin 3) (Fin 3) F} (hM : M.det ≠ 0)
    (hD : diagonal ![1, ω, ω ^ 2] * M = ω • (M * diagonal ![1, ω, ω ^ 2]))
    (hx : x * M = M * x) (hy : y * M = M * y) : x * y = y * x := by
  obtain ⟨_, hω2, hω21, _⟩ := omega_facts hω hω3
  have key : ∀ i j, (![1, ω, ω ^ 2] i - ω * ![1, ω, ω ^ 2] j) * M i j = 0 := fun i j => by
    have := congrFun (congrFun hD i) j
    simp only [diagonal_mul, mul_diagonal, Matrix.smul_apply, smul_eq_mul] at this
    linear_combination this
  have z : ∀ i j, ![1, ω, ω ^ 2] i - ω * ![1, ω, ω ^ 2] j ≠ 0 → M i j = 0 := fun i j h =>
    (mul_eq_zero.mp (key i j)).resolve_left h
  have h00 : M 0 0 = 0 := z 0 0 (by simpa [sub_eq_zero] using hω.symm)
  have h01 : M 0 1 = 0 := z 0 1 (by
    simpa [sub_eq_zero, ← pow_two] using hω2.symm)
  have h11 : M 1 1 = 0 := z 1 1 (by
    simpa [sub_eq_zero, ← pow_two] using hω21.symm)
  have h12 : M 1 2 = 0 := z 1 2 (by
    simpa [sub_eq_zero, ← pow_succ', hω3] using hω)
  have h20 : M 2 0 = 0 := z 2 0 (by simpa [sub_eq_zero] using hω21)
  have h22 : M 2 2 = 0 := z 2 2 (by
    simpa [sub_eq_zero, ← pow_succ', hω3] using hω2)
  have hdet : M.det = M 1 0 * M 2 1 * M 0 2 := by
    rw [det_fin_three, h00, h01, h11, h12, h20, h22]; ring
  rw [hdet] at hM
  have hα : M 1 0 ≠ 0 := fun h => hM (by rw [h]; ring)
  have hβ : M 2 1 ≠ 0 := fun h => hM (by rw [h]; ring)
  refine commute_of_cyclic (Pi.single 0 1) (fun w => ⟨![w 0, w 1 / M 1 0, w 2 / (M 2 1 * M 1 0)],
    ?_⟩) hx hy
  rw [mulVec_single_one]
  ext i; fin_cases i <;>
    simp [polyThree, Matrix.mul_apply, Fin.sum_univ_three, h00, h01, h11, h20] <;> field_simp

private lemma exists_mul_eq_smul {A : Subgroup (GL (Fin 3) F)}
    (hA : ∀ g ∈ A, ∀ h ∈ A, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.center (GL (Fin 3) F))
    {u g : GL (Fin 3) F} (hu : u ∈ A) (hg : g ∈ A) :
    ∃ c : F, (u : Matrix (Fin 3) (Fin 3) F) * g = c • ((g : Matrix (Fin 3) (Fin 3) F) * u) := by
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (hA u hu g hg)
  refine ⟨c, ?_⟩
  have h : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
  rw [← Units.val_mul, h, Units.val_mul, ← hc, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
    Units.val_mul]

private lemma commute_of_diag {ω μ : F} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (hμ : μ ≠ 0)
    {g x y : Matrix (Fin 3) (Fin 3) F} (hgdet : g.det ≠ 0)
    (hga : g * diagonal ![1, ω, ω ^ 2] = diagonal ![1, ω, ω ^ 2] * g) {c : F}
    (hc : !![0, 0, μ; 1, 0, 0; 0, 1, 0] * g = c • (g * !![0, 0, μ; 1, 0, 0; 0, 1, 0]))
    (hgs : ¬ ∃ s, g = diagonal fun _ => s) (hx : x * g = g * x) (hy : y * g = g * y) :
    x * y = y * x := by
  obtain ⟨_, hω2, hω21, _⟩ := omega_facts hω hω3
  have hd : Function.Injective ![1, ω, ω ^ 2] := injective_fin_three (by simpa using hω.symm)
    (by simpa using hω2.symm) (by simpa using hω21.symm)
  obtain ⟨e, rfl⟩ : ∃ e, g = diagonal e := ⟨_, eq_diagonal_of_mul_comm hd hga⟩
  have h10 : e 0 = c * e 1 := by simpa using congrFun (congrFun hc 1) 0
  have h21 : e 1 = c * e 2 := by simpa using congrFun (congrFun hc 2) 1
  have h02 : μ * e 2 = c * (e 0 * μ) := by simpa using congrFun (congrFun hc 0) 2
  rw [det_diagonal, Fin.prod_univ_three] at hgdet
  have he0 : e 0 ≠ 0 := fun h => hgdet (by rw [h]; ring)
  have he1 : e 1 ≠ 0 := fun h => hgdet (by rw [h]; ring)
  have he2 : e 2 ≠ 0 := fun h => hgdet (by rw [h]; ring)
  have hc1 : c - 1 ≠ 0 := by
    intro hc1
    refine hgs ⟨e 0, congrArg diagonal (funext fun i => ?_)⟩
    fin_cases i
    · rfl
    · simp; linear_combination -h10 - e 1 * hc1
    · simp; linear_combination -h21 - h10 - (e 1 + e 2) * hc1
  refine commute_of_diagonal_injective (injective_fin_three ?_ ?_ ?_) hx hy <;> intro h
  · exact mul_ne_zero hc1 he1 (by linear_combination h - h10)
  · exact mul_ne_zero hc1 (mul_ne_zero he0 hμ) (by linear_combination -h02 - μ * h)
  · exact mul_ne_zero hc1 he2 (by linear_combination h - h21)

private lemma commute_of_nondiag {ω : F} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    {g x y : Matrix (Fin 3) (Fin 3) F} (hgdet : g.det ≠ 0) {c : F} (hc1 : c ≠ 1)
    (hc : diagonal ![1, ω, ω ^ 2] * g = c • (g * diagonal ![1, ω, ω ^ 2]))
    (hx : x * g = g * x) (hy : y * g = g * y) : x * y = y * x := by
  obtain ⟨h1, -, -, -⟩ := omega_facts hω hω3
  set D := diagonal ![1, ω, ω ^ 2]
  have hD : D.det ≠ 0 := by
    have hω0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
    simp only [D, det_diagonal, Fin.prod_univ_three]
    simpa using hω0
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg det hc
    rw [det_mul, det_smul, det_mul, Fintype.card_fin] at h
    have : (c ^ 3 - 1) * (g.det * D.det) = 0 := by linear_combination -h
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero hgdet hD))
  have : (c - 1) * ((c - ω) * (c - ω ^ 2)) = 0 := by
    linear_combination hc3 - c ^ 2 * h1 + ω * c * h1 - hω3
  rcases mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)) with h | h
  · rw [sub_eq_zero.mp h] at hc
    exact commute_of_shift hω hω3 hgdet hc hx hy
  · have hgg : D * (g * g) = ω • (g * g * D) := by
      calc D * (g * g) = c • (g * (D * g)) := by rw [← mul_assoc, hc, smul_mul_assoc, mul_assoc, hc]
        _ = (c * c) • (g * g * D) := by rw [hc, mul_smul_comm, smul_smul, mul_assoc]
        _ = ω • (g * g * D) := by
          rw [sub_eq_zero.mp h]; congr 1; linear_combination ω * hω3
    refine commute_of_shift hω hω3 (by rw [det_mul]; exact mul_ne_zero hgdet hgdet) hgg ?_ ?_
    · rw [← mul_assoc, hx, mul_assoc, hx, mul_assoc]
    · rw [← mul_assoc, hy, mul_assoc, hy, mul_assoc]

theorem commute_of_commute_of_mem {A : Subgroup (GL (Fin 3) F)} (hA : IsElemModScalars 3 A)
    {ω μ : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (ha : diagOmega ω ∈ A) (hb : cycMat μ ∈ A)
    {g : GL (Fin 3) F} (hg : g ∈ A) (hgZ : g ∉ Subgroup.center (GL (Fin 3) F))
    {x y : GL (Fin 3) F} (hx : x * g = g * x) (hy : y * g = g * y) : x * y = y * x := by
  obtain ⟨hω', hω3'⟩ := val_omega hω hω3
  have hdet : ∀ u : GL (Fin 3) F, (u : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := fun u =>
    ((Matrix.isUnit_iff_isUnit_det _).mp u.isUnit).ne_zero
  have hx' : (x : Matrix (Fin 3) (Fin 3) F) * g = g * x := by
    rw [← Units.val_mul, hx, Units.val_mul]
  have hy' : (y : Matrix (Fin 3) (Fin 3) F) * g = g * y := by
    rw [← Units.val_mul, hy, Units.val_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  by_cases hga : (g : Matrix (Fin 3) (Fin 3) F) * (diagOmega ω : GL (Fin 3) F) =
      ((diagOmega ω : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * g
  · obtain ⟨c, hc⟩ := exists_mul_eq_smul hA.commutator_mem hb hg
    rw [val_diagOmega] at hga
    rw [val_cycMat] at hc
    refine commute_of_diag hω' hω3' μ.ne_zero (hdet g) hga hc ?_ hx' hy'
    rintro ⟨s, hs⟩
    exact hgZ (GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
      ⟨s, by rw [hs, Matrix.scalar_apply]⟩)
  · obtain ⟨c, hc⟩ := exists_mul_eq_smul hA.commutator_mem ha hg
    have hc1 : c ≠ 1 := fun h => hga (by rw [h, one_smul] at hc; exact hc.symm)
    rw [val_diagOmega] at hc
    exact commute_of_nondiag hω' hω3' (hdet g) hc1 hc hx' hy'

theorem exists_elemSq_mulAut [Finite F] {A : Subgroup (GL (Fin 3) F)} (hA : IsElemModScalars 3 A)
    {ω μ : Fˣ} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (ha : diagOmega ω ∈ A) (hb : cycMat μ ∈ A)
    {H : Subgroup (GL (Fin 3) F)} (hH : Group.IsPerfect H) (hHb : H ≠ ⊥)
    (hn : ∀ g ∈ A, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    ∃ E : Subgroup (MulAut H), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hAN : A ≤ Subgroup.normalizer (H : Set (GL (Fin 3) F)) := Subgroup.le_normalizer_iff.mpr hn
  let φ : A →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  have hφ : ∀ (a : A) (h : H), ((φ a h : H) : GL (Fin 3) F) = a * h * (a : GL (Fin 3) F)⁻¹ :=
    fun _ _ => rfl
  have hker : φ.ker = (Subgroup.center (GL (Fin 3) F)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      by_contra haZ
      have hc : ∀ h : H, (h : GL (Fin 3) F) * a = a * h := fun h => by
        have := congrArg (fun f : MulAut H => ((f h : H) : GL (Fin 3) F)) h1
        simp only [hφ, MulAut.one_apply] at this
        exact (mul_inv_eq_iff_eq_mul.mp this).symm
      apply hHb
      have := hH
      have : IsMulCommutative H := ⟨⟨fun u v => Subtype.ext
        (commute_of_commute_of_mem hA hω hω3 ha hb a.2 haZ (hc u) (hc v))⟩⟩
      exact Subgroup.eq_bot_of_subsingleton H
    · intro haZ
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hφ, MulAut.one_apply, ← Subgroup.mem_center_iff.mp haZ h, mul_inv_cancel_right]
  have hmem : ∀ a : A, (a : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) → φ a = 1 :=
    fun a h => (MonoidHom.mem_ker).mp (by rw [hker, Subgroup.mem_subgroupOf]; exact h)
  refine ⟨φ.range, ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩, ?_⟩
  · obtain ⟨a, ha'⟩ := u.2
    obtain ⟨b, hb'⟩ := v.2
    change (u : MulAut H) * v = v * u
    rw [← ha', ← hb', ← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def, ← map_inv,
      ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    exact hmem _ (by simpa using hA.commutator_mem a a.2 b b.2)
  · obtain ⟨a, rfl⟩ := hu
    rw [← map_pow]
    exact hmem _ (by simpa using hA.pow_mem a a.2)
  · rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker, hA.card_eq]
    norm_num

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixKFact
