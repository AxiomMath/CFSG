module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWAssembly
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWForm
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBCTwo
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWChart
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualTypeBWInvariant

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Module Subgroup CFSG.Assembly.LowTwoRank
open CFSG.Quasithin (perfectCore)
open LinearPilot (autFixSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus regular_coordinateQuadPlus)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (isometryConjugationHom)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n f : ℕ}

omit [Finite K] in
theorem projLift_mem_wallSing_of_core (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    {x : matrixProjectiveDerived (coordinateQuadPlus n K)}
    (hx : x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)))
    {u : Fin (2 * n) → K}
    (hu : u ∈ wallSing (sNil s.val) (polar_sNil_left s hss)
      (sNil_sNil (congrArg Subtype.val hss))) :
    projLift hQ x u ∈ wallSing (sNil s.val) (polar_sNil_left s hss)
      (sNil_sNil (congrArg Subtype.val hss)) := by
  rw [mem_wallSing] at hu ⊢
  refine ⟨mem_range_of_commute (fun v => projLift_sNil_of_mem_core hQ s hx v) u hu.1, ?_⟩
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (projLift_mem_orthogonalGroup hQ x)]
  exact hu.2

omit [Finite K] [CharP K 2] in
theorem quad_sub_of_mem_range {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hadj : ∀ x y, QuadraticMap.polarBilin Q (N x) y = QuadraticMap.polarBilin Q x (N y))
    (hNN : ∀ v, N (N v) = 0) {a b : Fin d → K} (ha : a ∈ LinearMap.range N)
    (hb : b ∈ LinearMap.range N) : Q (a - b) = Q a + Q b := by
  rw [sub_eq_add_neg, quad_add_of_mem_range N hadj hNN ha (neg_mem hb), QuadraticMap.map_neg]

omit [Finite K] in
theorem isPGroup_kerQuot_inf_of_flag {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
    (hQ : ∃ v, Q v ≠ 0) {X : Subgroup (matrixProjectiveDerived Q)}
    (N : (Fin d → K) →ₗ[K] (Fin d → K))
    (hXN : ∀ x ∈ X, ∀ v, projLift hQ x (N v) = N (projLift hQ x v)) (N₂ : Subgroup ↥X)
    (F : ℕ → Submodule K (Fin d → K)) (hF0 : F 0 = ⊥) (k : ℕ) (hFk : F k = LinearMap.range N)
    (hflag : ∀ x ∈ N₂, ∀ i < k, ∀ v ∈ F (i + 1),
      projLift hQ ((x : ↥X) : matrixProjectiveDerived Q) v - v ∈ F i) :
    IsPGroup 2 ↥((kerQuotHom hQ X N hXN).ker ⊓ N₂) := by
  refine isPGroup_of_sub_one_pow_eq_zero hQ _ (m := 2 * k + 1) fun x hx => ?_
  obtain ⟨h1, h2⟩ := hx
  have h1e : kerQuotHom hQ X N hXN x = 1 := h1
  refine sub_one_pow_eq_zero_of_commute_flag (N := N) (hXN x x.2) F hF0 k (hflag x h2) hFk
    fun v hv => ?_
  have h := congrArg (fun f : Module.End K (LinearMap.ker N ⧸ rangeInKer N) =>
    f (Submodule.Quotient.mk ⟨v, hv⟩)) h1e
  change kerQuotMap N _ (hXN x x.2) (Submodule.Quotient.mk ⟨v, hv⟩) =
    Submodule.Quotient.mk ⟨v, hv⟩ at h
  rw [kerQuotMap_mk'] at h
  have h' := (Submodule.Quotient.eq _).mp h
  simpa [rangeInKer] using h'

theorem spLeviData_typeB (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (hℓ : 3 ≤ finrank K (LinearMap.range (sNil s.val))) {z : Fin (2 * n) → K}
    (hz : ∀ w ∈ LinearMap.range (sNil s.val),
      QuadraticMap.polar (coordinateQuadPlus n K) w z = sqrtTwo K (coordinateQuadPlus n K w))
    (h1 : coordinateQuadPlus n K (sNil s.val z) = 1) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  classical
  have hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega)
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
  have hadj := polar_sNil_left s hss
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  have hQN : ∀ a, QuadraticMap.polar (coordinateQuadPlus n K) (sNil s.val a) a =
      coordinateQuadPlus n K (sNil s.val a) := polar_sNil_self s
  have hXN : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)), ∀ v,
      projLift hQ x (sNil s.val v) = sNil s.val (projLift hQ x v) :=
    fun x hx v => projLift_sNil_of_mem_core _ s hx v
  have hW₀W := wallSing_le_range (sNil s.val) hadj hNN
  have hQW₀ : ∀ u ∈ wallSing (sNil s.val) hadj hNN, coordinateQuadPlus n K u = 0 :=
    fun u hu => ((mem_wallSing (sNil s.val) hadj hNN).mp hu).2
  have hβ := wallRestrict_isAlt (sNil s.val) hadj hQN _ hW₀W hQW₀
  have hβn := wallRestrict_wallSing_nondegenerate (sNil s.val) hadj hNN hz h1 hB
  have hβU : ∀ (u u' : wallSing (sNil s.val) hadj hNN) (z' : Fin (2 * n) → K),
      sNil s.val z' = u' → wallRestrict (sNil s.val) hadj _ hW₀W u u' =
        QuadraticMap.polar (coordinateQuadPlus n K) u z' :=
    fun u u' z' hz' => wallRestrict_apply (sNil s.val) hadj _ hW₀W u u' hz'
  obtain ⟨C, hDC, hCK, hdisj, hsup, hCW⟩ := exists_kerCompl (sNil s.val) hNN
    (wallSing (sNil s.val) hadj hNN) (K ∙ sNil s.val z)
    (wallSing_inf_span_of_one (sNil s.val) hadj hNN h1)
    (wallSing_sup_span_of_one (sNil s.val) hadj hNN h1)
  have hD : ∀ u ∈ wallSing (sNil s.val) hadj hNN, ∀ z', sNil s.val z' ∈ C →
      QuadraticMap.polar (coordinateQuadPlus n K) u z' = 0 :=
    fun u hu z' hz' =>
      polar_eq_zero_of_mem_wallSing_of_mem_compl (sNil s.val) hadj hNN hz hCW hu hz'
  have hy₀ : sNil s.val z ∈ C := hDC (Submodule.mem_span_singleton_self _)
  have hdim := finrank_wallSing_add_one (sNil s.val) hadj hNN h1
  have hU0 : wallSing (sNil s.val) hadj hNN ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  have htor : ∀ u ∈ wallSing (sNil s.val) hadj hNN, u ≠ 0 → ∀ a : Kˣ,
      ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c :=
    fun u hu hu0 a => exists_core_torus hQ hB hq4 s hss hW₀W hQW₀ hCK hdisj hsup hD _ hβU hβ hβn
      hu hu0 a
  have hXW₀ : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      ∀ u ∈ wallSing (sNil s.val) hadj hNN, projLift hQ x u ∈ wallSing (sNil s.val) hadj hNN :=
    fun x hx u hu => projLift_mem_wallSing_of_core hQ s hss hx hu
  have hφ : ∀ x u u', wallRestrict (sNil s.val) hadj _ hW₀W
      (subRestrictHom hQ _ _ hXW₀ x u) (subRestrictHom hQ _ _ hXW₀ x u') =
        wallRestrict (sNil s.val) hadj _ hW₀W u u' := by
    intro x u u'
    obtain ⟨z', hz'⟩ := hW₀W u'.2
    have e : sNil s.val (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) z') =
        (subRestrictHom hQ _ _ hXW₀ x u' : Fin (2 * n) → K) := by
      rw [subRestrictHom_apply, ← hz', hXN x x.2]
    rw [hβU _ _ _ e, hβU _ _ _ hz', subRestrictHom_apply]
    exact polar_apply_of_mem_orth (projLift_mem_orthogonalGroup hQ _) u z'
  obtain ⟨r, b, hrdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by omega
  have hρ₁ : Function.Surjective (sympChart hβ hb _ hφ) :=
    sympChart_surjective hβ hb _ hφ fun g hg => by
      obtain ⟨x, hx, hxU, -⟩ :=
        exists_core_restrict_eq hQ hB hq4 s hss hW₀W hQW₀ hCK hdisj hsup hD _ hβU hβ hβn g hg
      exact ⟨⟨x, hx⟩, LinearMap.ext fun u => Subtype.ext (hxU u)⟩
  have hmem₁ : ∀ x, x ∈ (sympChart hβ hb _ hφ).ker ↔ ∀ u ∈ wallSing (sNil s.val) hadj hNN,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) u = u := fun x => by
    rw [sympChart_ker]
    exact mem_ker_subRestrictHom hQ _ _ hXW₀ x
  have hXxs : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      projLift hQ x (sNil s.val z) = sNil s.val z := fun x hx =>
    orth_apply_wallDual (sNil s.val) hadj hB hz (projLift_mem_orthogonalGroup hQ x) (hXN x hx)
  have hfixW : ∀ x ∈ (sympChart hβ hb _ hφ).ker, ∀ w ∈ LinearMap.range (sNil s.val),
      projLift hQ ((x : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) :
        matrixProjectiveDerived (coordinateQuadPlus n K)) w = w := by
    intro x hx w hw
    rw [← wallSing_sup_span_of_one (sNil s.val) hadj hNN h1] at hw
    obtain ⟨w₀, hw₀, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [map_add, (hmem₁ x).mp hx w₀ hw₀, map_smul, hXxs x x.2]
  have h12 : IsPGroup 2 ↥((kerQuotHom hQ _ (sNil s.val) hXN).ker ⊓ (sympChart hβ hb _ hφ).ker) :=
    isPGroup_kerQuot_inf_of_flag hQ (sNil s.val) hXN _
      (fun i => if i = 0 then ⊥ else LinearMap.range (sNil s.val)) (by simp) 1 (by simp)
      fun x hx i hi v hv => by
        obtain rfl : i = 0 := by omega
        simp only [zero_add, one_ne_zero, ite_false] at hv
        simp only [ite_true]
        rw [hfixW x hx v hv, sub_self]
        exact Submodule.zero_mem _
  obtain ⟨-, -, hNM⟩ := mSide_props hf hK hn hq4 s hss hW
  obtain ⟨-, hN₁⟩ := ker_props_of_surjective_sp hq4 hr _ hρ₁
  have hTU : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        matrixProjectiveConjugationHom _ g x ∈
          perfectCore (autFixSubgroup (isometryConjugationHom _ s))) →
      ∀ u ∈ wallSing (sNil s.val) hadj hNN,
        coordinateSemilinearMap g.val u ∈ wallSing (sNil s.val) hadj hNN := fun g hgX =>
    mapsTo_wallSing_of_core (by omega) hQ s hss hq4 _ C hW₀W hQW₀ hCK hdisj hsup hU0 hy₀ h1 htor
      _ (fun v => mem_wallSing (sNil s.val) hadj hNN) _ _ (by rw [inf_comm]; exact h12) hN₁ hNM
      (fun x hx => (hmem₁ x).mpr fun u hu => hx u (hW₀W hu))
      (fun x hx => MonoidHom.mem_ker.mpr (kerQuotHom_eq_one_of hQ (sNil s.val) hXN x hx))
      (fun r hr w hw x _ => by
        rw [(hmem₁ r).mp (Subgroup.mem_inf.mp hr).1 w hw, sub_self, map_zero])
      g hgX
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sympChart hβ hb _ hφ).ker :=
    spLeviSection_of_trace_restrict hQ _ (fun g => orthAutFieldPart_kappa _ _ g)
      (exists_kappa_eq_plus hn) _ hXW₀ hTU hr _ hρ₁ fun x => spMatTrace_sympChart hβ hb _ hφ x
  refine spLeviData_of_wallChart hf hK hn hq4 s hss hW hr _ hρ₁ h12 hs₁ fun β hβ m hm => ?_
  obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
  have hβ' := mapsTo_inv_of_mapsTo _ hβ
  have hTU' : ∀ u ∈ wallSing (sNil s.val) hadj hNN,
      (coordinateSemilinearMap g.val).symm u ∈ wallSing (sNil s.val) hadj hNN := by
    intro u hu
    have h := hTU g⁻¹ (by rw [map_inv]; exact hβ') u hu
    rwa [Subgroup.coe_inv, coordinateSemilinearMap_inv] at h
  rw [hmem₁, coe_restrictAutOfMapsTo]
  intro u hu
  have e := projLift_kappa_apply hQ g
    ((m : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) ((coordinateSemilinearMap g.val).symm u)
  rw [AddEquiv.apply_symm_apply] at e
  rw [e, (hmem₁ m).mp hm _ (hTU' u hu), AddEquiv.apply_symm_apply]

theorem spLeviData_typeC (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 5 ≤ n)
    (hq4 : 4 ≤ Nat.card K) (s : matrixIsometries (coordinateQuadPlus n K)) (hss : s * s = 1)
    (hW : ∃ w ∈ LinearMap.range (sNil s.val), coordinateQuadPlus n K w ≠ 0)
    (hℓ : 4 ≤ finrank K (LinearMap.range (sNil s.val))) {z zy : Fin (2 * n) → K}
    (hz : ∀ w ∈ LinearMap.range (sNil s.val),
      QuadraticMap.polar (coordinateQuadPlus n K) w z = sqrtTwo K (coordinateQuadPlus n K w))
    (h0 : coordinateQuadPlus n K (sNil s.val z) = 0)
    (hy : coordinateQuadPlus n K (sNil s.val zy) = 1) :
    SpLeviData (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) := by
  classical
  have hQ := exists_coordinateQuadPlus_ne_zero (K := K) (n := n) (by omega)
  have hB := (regular_coordinateQuadPlus n K (by omega)).1
  have hadj := polar_sNil_left s hss
  have hNN : ∀ v, sNil s.val (sNil s.val v) = 0 := sNil_sNil (congrArg Subtype.val hss)
  have hQN : ∀ a, QuadraticMap.polar (coordinateQuadPlus n K) (sNil s.val a) a =
      coordinateQuadPlus n K (sNil s.val a) := polar_sNil_self s
  have hXN : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)), ∀ v,
      projLift hQ x (sNil s.val v) = sNil s.val (projLift hQ x v) :=
    fun x hx v => projLift_sNil_of_mem_core _ s hx v
  have hW₀W := wallSing_le_range (sNil s.val) hadj hNN
  have hW₁W₀ := wallSingOne_le_wallSing (sNil s.val) hadj hNN zy
  have hW₁W := wallSingOne_le_range (sNil s.val) hadj hNN zy
  have hQW₁ : ∀ u ∈ wallSingOne (sNil s.val) hadj hNN zy, coordinateQuadPlus n K u = 0 :=
    fun u hu => ((mem_wallSingOne (sNil s.val) hadj hNN).mp hu).2.1
  have hβ := wallRestrict_isAlt (sNil s.val) hadj hQN _ hW₁W hQW₁
  have hβn := wallRestrict_wallSingOne_nondegenerate (sNil s.val) hadj hNN hz hQN h0 hy hB
  have hβU : ∀ (u u' : wallSingOne (sNil s.val) hadj hNN zy) (z' : Fin (2 * n) → K),
      sNil s.val z' = u' → wallRestrict (sNil s.val) hadj _ hW₁W u u' =
        QuadraticMap.polar (coordinateQuadPlus n K) u z' :=
    fun u u' z' hz' => wallRestrict_apply (sNil s.val) hadj _ hW₁W u u' hz'
  obtain ⟨C, hDC, hCK, hdisj, hsup, hCW⟩ := exists_kerCompl (sNil s.val) hNN
    (wallSingOne (sNil s.val) hadj hNN zy) (Submodule.span K {sNil s.val z, sNil s.val zy})
    (wallSingOne_inf_span_pair (sNil s.val) hadj hNN hz h0 hy)
    (wallSingOne_sup_span_pair (sNil s.val) hadj hNN hz hQN h0 hy)
  have hD : ∀ u ∈ wallSingOne (sNil s.val) hadj hNN zy, ∀ z', sNil s.val z' ∈ C →
      QuadraticMap.polar (coordinateQuadPlus n K) u z' = 0 :=
    fun u hu z' hz' =>
      polar_eq_zero_of_mem_wallSingOne_of_mem_compl (sNil s.val) hadj hNN hz hCW hu hz'
  have hy₀ : sNil s.val zy ∈ C := hDC (Submodule.subset_span (by simp))
  have hdim := finrank_wallSingOne_add_two (sNil s.val) hadj hNN hz hQN h0 hy
  have hU0 : wallSingOne (sNil s.val) hadj hNN zy ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  have htor : ∀ u ∈ wallSingOne (sNil s.val) hadj hNN zy, u ≠ 0 → ∀ a : Kˣ,
      ∃ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        projLift hQ x u = (a : K) • u ∧ ∀ c ∈ C, projLift hQ x c = c :=
    fun u hu hu0 a => exists_core_torus hQ hB hq4 s hss hW₁W hQW₁ hCK hdisj hsup hD _ hβU hβ hβn
      hu hu0 a
  have hXW₀ : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      ∀ u ∈ wallSing (sNil s.val) hadj hNN, projLift hQ x u ∈ wallSing (sNil s.val) hadj hNN :=
    fun x hx u hu => projLift_mem_wallSing_of_core hQ s hss hx hu
  have hXxs : ∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
      projLift hQ x (sNil s.val z) = sNil s.val z := fun x hx =>
    orth_apply_wallDual (sNil s.val) hadj hB hz (projLift_mem_orthogonalGroup hQ x) (hXN x hx)
  have hxsW₀ : sNil s.val z ∈ wallSing (sNil s.val) hadj hNN :=
    (mem_wallSing (sNil s.val) hadj hNN).mpr ⟨LinearMap.mem_range_self _ z, h0⟩
  have hxs0 : sNil s.val z ≠ 0 := wallDual_ne_zero_of_zero (sNil s.val) hadj hz hy
  have hBxs : QuadraticMap.polar (coordinateQuadPlus n K) (sNil s.val z) zy = 1 :=
    polar_wallDual_eq_one (sNil s.val) hadj hz hy
  have hπE : ∀ e ∈ wallSing (sNil s.val) hadj hNN,
      wallProj (Q := coordinateQuadPlus n K) (sNil s.val z) zy e ∈
        wallSingOne (sNil s.val) hadj hNN zy := by
    intro e he
    have he' := (mem_wallSing (sNil s.val) hadj hNN).mp he
    have hc : QuadraticMap.polar (coordinateQuadPlus n K) e zy • sNil s.val z ∈
        LinearMap.range (sNil s.val) := Submodule.smul_mem _ _ (LinearMap.mem_range_self _ z)
    rw [wallProj_apply, mem_wallSingOne]
    refine ⟨sub_mem he'.1 hc, ?_, ?_⟩
    · rw [quad_sub_of_mem_range (sNil s.val) hadj hNN he'.1 hc, he'.2, QuadraticMap.map_smul, h0,
        smul_zero, add_zero]
    · rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hBxs, smul_eq_mul, mul_one,
        sub_self]
  have hπU : ∀ u ∈ wallSingOne (sNil s.val) hadj hNN zy,
      wallProj (Q := coordinateQuadPlus n K) (sNil s.val z) zy u = u := by
    intro u hu
    rw [wallProj_apply, ((mem_wallSingOne (sNil s.val) hadj hNN).mp hu).2.2, zero_smul, sub_zero]
  have hπx : wallProj (Q := coordinateQuadPlus n K) (sNil s.val z) zy (sNil s.val z) = 0 := by
    rw [wallProj_apply, hBxs, one_smul, sub_self]
  have hφ : ∀ x u u', wallRestrict (sNil s.val) hadj _ hW₁W
      (projRestrictHom hQ _ _ _ _ _ hXW₀ hW₁W₀ hπE hπU hπx hXxs x u)
      (projRestrictHom hQ _ _ _ _ _ hXW₀ hW₁W₀ hπE hπU hπx hXxs x u') =
        wallRestrict (sNil s.val) hadj _ hW₁W u u' := by
    intro x u u'
    obtain ⟨z', hz'⟩ := hW₁W u'.2
    set c := QuadraticMap.polar (coordinateQuadPlus n K)
      (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) u') zy with hc
    set c₁ := QuadraticMap.polar (coordinateQuadPlus n K)
      (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) u) zy with hc₁
    have e : sNil s.val (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) z' -
        c • z) = (projRestrictHom hQ _ _ _ _ _ hXW₀ hW₁W₀ hπE hπU hπx hXxs x u' :
          Fin (2 * n) → K) := by
      rw [projRestrictHom_apply, wallProj_apply, map_sub, map_smul, ← hXN x x.2, hz']
    rw [hβU _ _ _ e, hβU _ _ _ hz', projRestrictHom_apply, wallProj_apply, ← hc₁]
    have hu₀ : (u : Fin (2 * n) → K) ∈ wallSing (sNil s.val) hadj hNN := hW₁W₀ u.2
    have hu'₀ : (u' : Fin (2 * n) → K) ∈ wallSing (sNil s.val) hadj hNN := hW₁W₀ u'.2
    have k1 : QuadraticMap.polar (coordinateQuadPlus n K)
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) u) z = 0 :=
      polar_wallDual_of_mem_wallSing (sNil s.val) hadj hNN hz (hXW₀ x x.2 _ hu₀)
    have k2 : QuadraticMap.polar (coordinateQuadPlus n K) (sNil s.val z)
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) z') = 0 := by
      rw [← hXxs x x.2, polar_apply_of_mem_orth (projLift_mem_orthogonalGroup hQ _),
        ← QuadraticMap.polarBilin_apply_apply, hadj, QuadraticMap.polarBilin_apply_apply, hz',
        QuadraticMap.polar_comm]
      exact polar_wallDual_of_mem_wallSing (sNil s.val) hadj hNN hz hu'₀
    have k3 : QuadraticMap.polar (coordinateQuadPlus n K) (sNil s.val z) z = 0 := by
      rw [hz _ (LinearMap.mem_range_self _ z), h0, map_zero]
    simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    rw [k1, k2, k3, polar_apply_of_mem_orth (projLift_mem_orthogonalGroup hQ _)]
    simp
  obtain ⟨r, b, hrdim, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hβ hβn
  have hr : 1 ≤ r := by omega
  have hρ₁ : Function.Surjective (sympChart hβ hb _ hφ) :=
    sympChart_surjective hβ hb _ hφ fun g hg => by
      obtain ⟨x, hx, hxU, -⟩ :=
        exists_core_restrict_eq hQ hB hq4 s hss hW₁W hQW₁ hCK hdisj hsup hD _ hβU hβ hβn g hg
      refine ⟨⟨x, hx⟩, LinearMap.ext fun u => Subtype.ext ?_⟩
      rw [projRestrictHom_apply, hxU u]
      exact hπU _ (g u).2
  have hmem₁ : ∀ x, x ∈ (sympChart hβ hb _ hφ).ker ↔ ∀ u ∈ wallSingOne (sNil s.val) hadj hNN zy,
      projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) u - u ∈
        K ∙ sNil s.val z := by
    intro x
    rw [sympChart_ker, MonoidHom.mem_ker]
    constructor
    · intro h u hu
      have h' := congrArg (fun f : Module.End K (wallSingOne (sNil s.val) hadj hNN zy) =>
        ((f ⟨u, hu⟩ : wallSingOne (sNil s.val) hadj hNN zy) : Fin (2 * n) → K)) h
      simp only [Module.End.one_apply] at h'
      rw [projRestrictHom_apply, wallProj_apply, sub_eq_iff_eq_add] at h'
      rw [h', add_sub_cancel_left]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · intro h
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (h u u.2)
      rw [Module.End.one_apply, projRestrictHom_apply, ← sub_add_cancel
        (projLift hQ (x : matrixProjectiveDerived (coordinateQuadPlus n K)) (u : Fin (2 * n) → K))
        (u : Fin (2 * n) → K), ← ht, map_add, map_smul, hπx, smul_zero, zero_add, hπU _ u.2]
  have hmem₀ : ∀ x ∈ (sympChart hβ hb _ hφ).ker, ∀ w ∈ wallSing (sNil s.val) hadj hNN,
      projLift hQ ((x : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) :
        matrixProjectiveDerived (coordinateQuadPlus n K)) w - w ∈ K ∙ sNil s.val z := by
    intro x hx w hw
    rw [← wallSingOne_sup_span (sNil s.val) hadj hNN hz h0 hy] at hw
    obtain ⟨w₁, hw₁, c, hc, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [map_add, map_smul, hXxs x x.2, add_sub_add_right_eq_sub]
    exact (hmem₁ x).mp hx w₁ hw₁
  have h12 : IsPGroup 2 ↥((kerQuotHom hQ _ (sNil s.val) hXN).ker ⊓ (sympChart hβ hb _ hφ).ker) :=
    isPGroup_kerQuot_inf_of_flag hQ (sNil s.val) hXN _
      (fun i => if i = 0 then ⊥ else if i = 1 then K ∙ sNil s.val z else
        if i = 2 then wallSing (sNil s.val) hadj hNN else LinearMap.range (sNil s.val))
      (by simp) 3 (by simp) fun x hx i hi v hv => by
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
        · simp only [zero_add, one_ne_zero, ite_false, ite_true] at hv ⊢
          obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
          rw [map_smul, hXxs x x.2, sub_self]
          exact Submodule.zero_mem _
        · simp only [show (1 : ℕ) + 1 = 2 from rfl, two_ne_zero, OfNat.ofNat_ne_one, ite_false,
            ite_true, one_ne_zero] at hv ⊢
          exact hmem₀ x hx v hv
        · simp only [show (2 : ℕ) + 1 = 3 from rfl, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
            ite_false, ite_true] at hv ⊢
          have hxv : projLift hQ ((x : ↥(perfectCore (autFixSubgroup
              (isometryConjugationHom _ s)))) : matrixProjectiveDerived (coordinateQuadPlus n K)) v ∈
              LinearMap.range (sNil s.val) := mem_range_of_commute (hXN x x.2) v hv
          rw [mem_wallSing]
          refine ⟨sub_mem hxv hv, ?_⟩
          rw [quad_sub_of_mem_range (sNil s.val) hadj hNN hxv hv,
            TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (projLift_mem_orthogonalGroup hQ _),
            CharTwo.add_self_eq_zero]
  obtain ⟨-, -, hNM⟩ := mSide_props hf hK hn hq4 s hss hW
  obtain ⟨-, hN₁⟩ := ker_props_of_surjective_sp hq4 hr _ hρ₁
  have hTU : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        matrixProjectiveConjugationHom _ g x ∈
          perfectCore (autFixSubgroup (isometryConjugationHom _ s))) →
      ∀ u ∈ wallSing (sNil s.val) hadj hNN,
        coordinateSemilinearMap g.val u ∈ wallSing (sNil s.val) hadj hNN := fun g hgX =>
    mapsTo_wallSing_of_core (by omega) hQ s hss hq4 _ C hW₁W hQW₁ hCK hdisj hsup hU0 hy₀ hy htor
      _ (fun v => mem_wallSing (sNil s.val) hadj hNN) _ _ (by rw [inf_comm]; exact h12) hN₁ hNM
      (fun x hx => (hmem₁ x).mpr fun u hu => by
        rw [hx u (hW₁W hu), sub_self]
        exact Submodule.zero_mem _)
      (fun x hx => MonoidHom.mem_ker.mpr (kerQuotHom_eq_one_of hQ (sNil s.val) hXN x hx))
      (fun r hr w hw x hx => by
        obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hmem₀ r (Subgroup.mem_inf.mp hr).1 w hw)
        rw [← ht, map_smul, hXxs x hx])
      g hgX
  have hTx : ∀ g : similarityPairs (coordinateQuadPlus n K),
      (∀ x ∈ perfectCore (autFixSubgroup (isometryConjugationHom _ s)),
        matrixProjectiveConjugationHom _ g x ∈
          perfectCore (autFixSubgroup (isometryConjugationHom _ s))) →
      coordinateSemilinearMap g.val (sNil s.val z) ∈ K ∙ sNil s.val z := fun g hgX =>
    mem_span_of_mem_compl_of_mem_wallSing (sNil s.val) hadj hNN h0 hy hCW
      (fixSpace_le_compl (by omega) hQ s hss hq4 _ C hW₁W hQW₁ hCK hdisj hsup hU0 hy₀ hy htor
        (mapsTo_fixSpace_of_normalizes hQ g hgX hXxs))
      (hTU g hgX _ hxsW₀)
  have hs₁ : SpLeviSection (plusFieldPart hf hK hn)
      (perfectCore (autFixSubgroup (isometryConjugationHom _ s))) (sympChart hβ hb _ hφ).ker :=
    spLeviSection_of_trace_restrict_add hQ _ (fun g => orthAutFieldPart_kappa _ _ g)
      (exists_kappa_eq_plus hn) _ hXW₀ hTU 1 (fun σ => map_one σ) hr _ hρ₁ fun x => by
        rw [spMatTrace_sympChart, trace_restrict_eq_one_add hxs0 hW₁W₀ hxsW₀
          (wallSingOne_inf_span (sNil s.val) hadj hNN hz hy)
          (wallSingOne_sup_span (sNil s.val) hadj hNN hz h0 hy) _ (hXW₀ x x.2) (hXxs x x.2)
          (projRestrictHom hQ _ _ _ _ _ hXW₀ hW₁W₀ hπE hπU hπx hXxs x) fun u => ?_, add_comm]
        rw [projRestrictHom_apply, wallProj_apply]
        simp only [LinearEquiv.coe_coe, sub_sub_cancel]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine spLeviData_of_wallChart hf hK hn hq4 s hss hW hr _ hρ₁ h12 hs₁ fun β hβ m hm => ?_
  obtain ⟨g, rfl⟩ := exists_kappa_eq_plus hn β
  have hβ' := mapsTo_inv_of_mapsTo _ hβ
  have hTU' : ∀ u ∈ wallSing (sNil s.val) hadj hNN,
      (coordinateSemilinearMap g.val).symm u ∈ wallSing (sNil s.val) hadj hNN := by
    intro u hu
    have h := hTU g⁻¹ (by rw [map_inv]; exact hβ') u hu
    rwa [Subgroup.coe_inv, coordinateSemilinearMap_inv] at h
  rw [hmem₁, coe_restrictAutOfMapsTo]
  intro u hu
  have e := projLift_kappa_apply hQ g
    ((m : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) ((coordinateSemilinearMap g.val).symm u)
  rw [AddEquiv.apply_symm_apply] at e
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hmem₀ m hm _ (hTU' u (hW₁W₀ hu)))
  obtain ⟨t', ht'⟩ := Submodule.mem_span_singleton.mp (hTx g hβ)
  have e2 : projLift hQ ((m : ↥(perfectCore (autFixSubgroup (isometryConjugationHom _ s)))) :
      matrixProjectiveDerived (coordinateQuadPlus n K)) ((coordinateSemilinearMap g.val).symm u) =
      (coordinateSemilinearMap g.val).symm u + t • sNil s.val z := by
    rw [ht]
    abel
  rw [e, e2, map_add, AddEquiv.apply_symm_apply, coordinateSemilinearMap_smul, ← ht',
    add_sub_cancel_left, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

end CFSG.SeitzReduction.OmegaPilot
