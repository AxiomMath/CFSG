module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Ruling
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus
public import CFSG.Monster.B.Geometry.ChamberSystem
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipFrame

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg
open CFSG.Monster.B.Geometry

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K} [CharP K 2]
variable {n m : ℕ}

omit [CharP K 2] in
theorem mem_stdLag {n : ℕ} {v : Fin n ⊕ Fin n → K} :
    v ∈ stdLag n K ↔ ∀ i, v (Sum.inr i) = 0 := by
  rw [stdLag, LinearMap.mem_ker]
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

omit [CharP K 2] in
theorem stdLag_eq_span_stdE (n : ℕ) :
    stdLag n K = Submodule.span K (Set.range (stdE (K := K) (n := n))) := by
  apply le_antisymm
  · intro v hv
    rw [mem_stdLag] at hv
    have hdecomp : v = ∑ i, v (Sum.inl i) • stdE (K := K) (n := n) i := by
      funext j
      cases j with
      | inl i =>
        rw [Finset.sum_apply, Finset.sum_eq_single i]
        · simp [stdE]
        · intro k _ hk
          simp [stdE, hk]
        · intro h
          exact absurd (Finset.mem_univ i) h
      | inr i =>
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, stdE_inr, smul_eq_mul, mul_zero]
        rw [Finset.sum_eq_zero fun k _ => by simp, hv i]
    rw [hdecomp]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change stdE i ∈ stdLag n K
    rw [mem_stdLag]
    exact fun j => stdE_inr_eq_zero_of_mem_span (Submodule.subset_span ⟨i, rfl⟩) j

theorem bcLin_eq_coe_bc (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) =
      (bc E n g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := by
  refine eq_of_eqOn_range_jEmb E n fun x => ?_
  change bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) (jEmb E n x) =
    bc E n g (jEmb E n x)
  rw [bcLin_jEmb, bc_apply_jEmb]
  rfl

theorem bcLin_apply_eq_bc (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) (v : Fin n ⊕ Fin n → K) :
    bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v = bc E n g v := by
  rw [bcLin_eq_coe_bc]
  rfl

private noncomputable def coordMap (σ : K ≃+* K) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (g : (Fin n → K) →ₗ[K] (Fin n → K)) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) where
  toFun v := Sum.elim (g (fun i => v (Sum.inl i)))
    (fun i => σ (g (fun j => σ (v (Sum.inr j))) i))
  map_add' u v := by
    ext p
    cases p with
    | inl i =>
      have h : (fun j => (u + v) (Sum.inl j)) =
          (fun j => u (Sum.inl j)) + (fun j => v (Sum.inl j)) := rfl
      simp only [Sum.elim_inl]
      rw [h, map_add]
      simp only [Sum.elim_inl, Pi.add_apply]
    | inr i =>
      have h : (fun j => σ ((u + v) (Sum.inr j))) =
          (fun j => σ (u (Sum.inr j))) + (fun j => σ (v (Sum.inr j))) := by
        funext j
        simp only [Pi.add_apply, map_add]
      simp only [Sum.elim_inr]
      rw [h, map_add]
      simp only [Sum.elim_inr, Pi.add_apply, map_add]
  map_smul' a u := by
    ext p
    cases p with
    | inl i =>
      have h : (fun j => (a • u) (Sum.inl j)) = a • (fun j => u (Sum.inl j)) := rfl
      rw [h, map_smul]
      rfl
    | inr i =>
      have h : (fun j => σ ((a • u) (Sum.inr j))) =
          σ a • (fun j => σ (u (Sum.inr j))) := by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      rw [h, map_smul]
      simp only [Sum.elim_inr, Pi.smul_apply, map_mul, hσ, RingHom.id_apply, smul_eq_mul]

omit [CharP K 2] in
private theorem coordMap_jEmb (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[K] (Fin n → K)) (x : Fin n → K) :
    coordMap σ E.isUnitary.invol g (jEmb E n x) = jEmb E n (g x) := by
  ext p
  cases p with
  | inl i => simp [coordMap, jEmb]
  | inr i => simp [coordMap, jEmb, E.isUnitary.invol]

theorem bcLin_restrictScalars_inl (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[K] (Fin n → K)) (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bcLin E n (g.restrictScalars F) v (Sum.inl i) = g (fun j => v (Sum.inl j)) i := by
  have h : bcLin E n (g.restrictScalars F) = coordMap σ E.isUnitary.invol g :=
    eq_of_eqOn_range_jEmb E n fun x => by rw [bcLin_jEmb, coordMap_jEmb]; rfl
  rw [h]
  rfl

theorem bcLin_restrictScalars_inr (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) →ₗ[K] (Fin n → K)) (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bcLin E n (g.restrictScalars F) v (Sum.inr i) =
      σ (g (fun j => σ (v (Sum.inr j))) i) := by
  have h : bcLin E n (g.restrictScalars F) = coordMap σ E.isUnitary.invol g :=
    eq_of_eqOn_range_jEmb E n fun x => by rw [bcLin_jEmb, coordMap_jEmb]; rfl
  rw [h]
  rfl

private noncomputable def diagLin (t : Fin n → normOne σ) :
    (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun x i := (((t i : normOne σ) : Kˣ) : K) * x i
  map_add' x y := by
    funext i
    simp [mul_add]
  map_smul' a x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [CharP K 2] in
private theorem diagLin_restrictScalars (t : Fin n → normOne σ) :
    (diagLin (σ := σ) t).restrictScalars F =
      (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K)) := by
  ext x i
  simp [diagLin, diagHom_apply]

theorem bc_diagHom_apply (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ)
    (v : Fin n ⊕ Fin n → K) :
    bc E n (diagHom F σ n t) v =
      Sum.elim (fun i => (((t i : normOne σ) : Kˣ) : K) * v (Sum.inl i))
        (fun i => σ ((((t i : normOne σ) : Kˣ) : K)) * v (Sum.inr i)) := by
  change (bc E n (diagHom F σ n t) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) v = _
  rw [← bcLin_eq_coe_bc, ← diagLin_restrictScalars]
  funext p
  cases p with
  | inl i => rw [bcLin_restrictScalars_inl]; rfl
  | inr i =>
    rw [bcLin_restrictScalars_inr]
    simp [diagLin, map_mul, E.isUnitary.invol]

theorem bc_diagHom_inl (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bc E n (diagHom F σ n t) v (Sum.inl i) =
      (((t i : normOne σ) : Kˣ) : K) * v (Sum.inl i) := by
  rw [bc_diagHom_apply]
  rfl

theorem bc_diagHom_inr (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bc E n (diagHom F σ n t) v (Sum.inr i) =
      σ ((((t i : normOne σ) : Kˣ) : K)) * v (Sum.inr i) := by
  rw [bc_diagHom_apply]
  rfl

theorem bcLin_diagHom_inl (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bcLin E n (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K)) v (Sum.inl i) =
      (((t i : normOne σ) : Kˣ) : K) * v (Sum.inl i) := by
  rw [bcLin_apply_eq_bc, bc_diagHom_inl]

theorem bcLin_diagHom_inr (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ)
    (v : Fin n ⊕ Fin n → K) (i : Fin n) :
    bcLin E n (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K)) v (Sum.inr i) =
      σ ((((t i : normOne σ) : Kˣ) : K)) * v (Sum.inr i) := by
  rw [bcLin_apply_eq_bc, bc_diagHom_inr]

theorem map_stdLag_diagHom (E : QuadExt F K σ) (n : ℕ) (t : Fin n → normOne σ) :
    (stdLag n K).map
        (bcLin E n (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K))) =
      stdLag n K := by
  rw [bcLin_eq_coe_bc]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe] at hx
    rw [mem_stdLag] at hx
    change (bc E n (diagHom F σ n t)) x ∈ stdLag n K
    rw [mem_stdLag]
    intro i
    have h := bc_diagHom_inr E n t x i
    change bc E n (diagHom F σ n t) x (Sum.inr i) = 0
    rw [h]
    simp [hx i]
  · intro y hy
    rw [mem_stdLag] at hy
    let w : Fin n ⊕ Fin n → K :=
      Sum.elim (fun i => ((((t i : normOne σ) : Kˣ) : K))⁻¹ * y (Sum.inl i)) 0
    have hw : w ∈ stdLag n K := by
      rw [mem_stdLag]
      intro i
      simp [w]
    refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
    funext p
    cases p with
    | inl i =>
      have h := bc_diagHom_inl E n t w i
      change bc E n (diagHom F σ n t) w (Sum.inl i) = y (Sum.inl i)
      rw [h]
      have ht : (((t i : normOne σ) : Kˣ) : K) ≠ 0 := Units.ne_zero _
      simp only [w, Sum.elim_inl]
      rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
    | inr i =>
      have h := bc_diagHom_inr E n t w i
      change bc E n (diagHom F σ n t) w (Sum.inr i) = y (Sum.inr i)
      rw [h]
      simp [w, hy i]


theorem IsFlipflopSub.map_bcLin (E : QuadExt F K σ) (n : ℕ)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    {U : Submodule K (Fin n ⊕ Fin n → K)} (hU : IsFlipflopSub σ U) :
    IsFlipflopSub σ (U.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) where
  total u hu := by
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    rw [quadPlus_bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
      (fun x => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg x) v]
    exact hU.total v hv
  nondeg u hu hper := by
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hu
    have hv0 : v = 0 := hU.nondeg v hv fun w hw => by
      have h1 := hper (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) w)
        (Submodule.mem_map_of_mem hw)
      rw [bcLin_apply_eq_bc E n g v, bcLin_apply_eq_bc E n g w,
        flipHerm_bc E n g hg] at h1
      exact h1
    rw [hv0, map_zero]

theorem IsFlipflopPt.map_bcLin (E : QuadExt F K σ) (n : ℕ)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n))
    {p : Submodule K (Fin n ⊕ Fin n → K)} (hp : IsFlipflopPt σ p) :
    IsFlipflopPt σ (p.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) := by
  change IsFlipflopSub σ (p.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) ∧
    Module.finrank K (p.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) = 1
  refine ⟨hp.1.map_bcLin E n hg, ?_⟩
  have hpne : p ≠ ⊥ := by
    intro hbot
    have h := hp.2
    rw [hbot, finrank_bot] at h
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpne
  have hpeq : p = K ∙ v :=
    eq_span_singleton_of_mem_of_finrank_eq_one hp.2 hv hv0
  have hinj : Function.Injective (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) := by
    intro a b hab
    apply (bc E n g).injective
    rw [← bcLin_apply_eq_bc E n g a, ← bcLin_apply_eq_bc E n g b]
    exact hab
  have hLv : bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) v ≠ 0 := by
    intro h
    exact hv0 (hinj (by rw [h, map_zero]))
  rw [hpeq, Submodule.map_span, Set.image_singleton]
  exact finrank_span_singleton hLv

theorem map_dFlipSub_bcLin (E : QuadExt F K σ) (n : ℕ)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
    (W : Submodule K (Fin n ⊕ Fin n → K)) :
    (dFlipSub σ W).map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) =
      dFlipSub σ (W.map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) := by
  rw [dFlipSub, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) w, ⟨w, hw, rfl⟩,
      (bcLin_dFlip E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) w).symm⟩
  · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨dFlip σ w, ⟨w, hw, rfl⟩,
      bcLin_dFlip E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) w⟩


variable (σ n) in
structure DChamber extends FlipFrame σ n where
  even_ruling : Even (n - Module.finrank K ↥(toFlipFrame.spanAt Finset.univ ⊓ stdLag n K))

namespace DChamber

omit [CharP K 2] in
@[ext] theorem ext {c d : DChamber σ n} (h : c.line = d.line) : c = d := by
  cases c
  cases d
  congr 1
  exact FlipFrame.ext h

end DChamber

@[expose] def stdDChamber (σ : K ≃+* K) (n : ℕ) : DChamber σ n where
  toFlipFrame := FlipFrame.stdFrame σ n
  even_ruling := by
    rw [FlipFrame.stdFrame_spanAt_univ, ← stdLag_eq_span_stdE, inf_idem, finrank_stdLag,
      Nat.sub_self]
    exact ⟨0, rfl⟩

omit [CharP K 2] in
@[simp] theorem stdDChamber_line (σ : K ≃+* K) (n : ℕ) (i : Fin n) :
    (stdDChamber σ n).line i = K ∙ stdE (K := K) i := by
  change (FlipFrame.stdFrame σ n).line i = K ∙ stdE (K := K) i
  rfl

omit [CharP K 2] in
theorem stdDChamber_spanAt_univ (σ : K ≃+* K) (n : ℕ) :
    (stdDChamber σ n).spanAt Finset.univ = stdLag n K := by
  change (FlipFrame.stdFrame σ n).spanAt Finset.univ = stdLag n K
  rw [FlipFrame.stdFrame_spanAt_univ, stdLag_eq_span_stdE]

theorem mem_orthogonalGroup_of_mem_orthDerived (E : QuadExt F K σ) (n : ℕ)
    {g : (Fin n → K) ≃ₗ[F] (Fin n → K)} (hg : g ∈ CFSG.RankThree.Classical2.orthDerived (Qn E n)) :
    g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) :=
  ((mem_rulingGroup E n g).mp (orthDerived_le_rulingGroup E n hg)).1

@[expose] noncomputable def smulDChamber (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) (c : DChamber σ n) :
    DChamber σ n where
  line i := (c.line i).map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))
  isFlipflopPt_line i :=
    (c.isFlipflopPt_line i).map_bcLin E n (mem_orthogonalGroup_of_mem_orthDerived E n g.2)
  polar_eq_zero i j hij u hu v hv := by
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
    rw [polar_bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
      (fun x => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (mem_orthogonalGroup_of_mem_orthDerived E n g.2) x) u₀ v₀]
    exact c.polar_eq_zero i j hij u₀ hu₀ v₀ hv₀
  flipHerm_eq_zero i j hij u hu v hv := by
    obtain ⟨u₀, hu₀, rfl⟩ := Submodule.mem_map.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Submodule.mem_map.mp hv
    rw [bcLin_apply_eq_bc E n g u₀, bcLin_apply_eq_bc E n g v₀,
      flipHerm_bc E n g (mem_orthogonalGroup_of_mem_orthDerived E n g.2)]
    exact c.flipHerm_eq_zero i j hij u₀ hu₀ v₀ hv₀
  even_ruling := by
    have hspan : (Finset.univ.sup fun i =>
          (c.line i).map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) =
        (c.toFlipFrame.spanAt Finset.univ).map
          (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) := by
      rw [FlipFrame.spanAt, Finset.sup_univ_eq_iSup, Finset.sup_univ_eq_iSup,
        Submodule.map_iSup]
    change Even (n - Module.finrank K ↥((Finset.univ.sup fun i =>
      (c.line i).map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))) ⊓ stdLag n K))
    rw [hspan]
    exact (even_ruling_map_iff E n (orthDerived_le_rulingGroup E n g.2)
      (c.toFlipFrame.isLagrangian_spanAt_univ E.isUnitary.invol)).mpr c.even_ruling

noncomputable instance smulDChamberInstance (E : QuadExt F K σ) (n : ℕ) :
    SMul ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n)) (DChamber σ n) where
  smul := smulDChamber E n

theorem smul_line (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) (c : DChamber σ n) (i : Fin n) :
    (g • c).line i = (c.line i).map (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) :=
  rfl

noncomputable instance mulActionDChamber (E : QuadExt F K σ) (n : ℕ) :
    MulAction ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n)) (DChamber σ n) where
  one_smul c := by
    apply DChamber.ext
    funext i
    rw [smul_line]
    show (c.line i).map (bcLin E n ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
      (Fin n → K) →ₗ[F] (Fin n → K))) = c.line i
    rw [show ((1 : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K)) = LinearMap.id from rfl, bcLin_id,
      Submodule.map_id]
  mul_smul g h c := by
    apply DChamber.ext
    funext i
    rw [smul_line, smul_line, smul_line]
    show (c.line i).map (bcLin E n
        ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
          (Fin n → K) →ₗ[F] (Fin n → K))) =
      ((c.line i).map (bcLin E n (h : (Fin n → K) →ₗ[F] (Fin n → K)))).map
        (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)))
    rw [show ((g * h : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
        (Fin n → K) →ₗ[F] (Fin n → K)) =
        ((g : (Fin n → K) →ₗ[F] (Fin n → K)).comp
          (h : (Fin n → K) →ₗ[F] (Fin n → K))) from rfl, bcLin_comp, Submodule.map_comp]


theorem smul_spanAt (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) (c : DChamber σ n)
    (S : Finset (Fin n)) :
    (g • c).spanAt S = (c.spanAt S).map
      (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) := by
  induction S using Finset.induction_on with
  | empty => rw [FlipFrame.spanAt_empty, FlipFrame.spanAt_empty, Submodule.map_bot]
  | insert i S hi ih =>
    rw [FlipFrame.spanAt_insert, FlipFrame.spanAt_insert, Submodule.map_sup, smul_line, ih]

theorem smul_sub (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) (c : DChamber σ n) (j : ℕ) :
    (g • c).sub j = (c.sub j).map
      (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) :=
  smul_spanAt E n g c _

theorem smul_alt (E : QuadExt F K σ) (m : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (c : DChamber σ (m + 1)) :
    (g • c).alt = (c.alt).map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by
  rw [FlipFrame.alt, FlipFrame.alt, Submodule.map_sup, smul_sub, smul_line,
    map_dFlipSub_bcLin]

theorem elt_smul (E : QuadExt F K σ) (m : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (c : DChamber σ (m + 1)) (i : Fin (m + 1)) :
    (g • c).elt i = (c.elt i).map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by
  rw [FlipFrame.elt, FlipFrame.elt]
  by_cases hlast : i = Fin.last m
  · rw [if_pos hlast, if_pos hlast, smul_sub]
  · rw [if_neg hlast, if_neg hlast]
    by_cases halt : (i : ℕ) + 1 = m
    · rw [if_pos halt, if_pos halt, smul_alt]
    · rw [if_neg halt, if_neg halt, smul_sub]

omit [CharP K 2] in
theorem FlipFrame.even_iff_not_even_alt (hσ : ∀ x, σ (σ x) = x) (c : FlipFrame σ (m + 1)) :
    Even ((m + 1) - Module.finrank K ↥(c.spanAt Finset.univ ⊓ stdLag (m + 1) K)) ↔
      ¬ Even ((m + 1) - Module.finrank K ↥(c.alt ⊓ stdLag (m + 1) K)) := by
  have hMA : (quadPlusForm (m + 1) K).IsLagrangian (c.spanAt Finset.univ) :=
    c.isLagrangian_spanAt_univ hσ
  have hMB : (quadPlusForm (m + 1) K).IsLagrangian c.alt :=
    c.isLagrangian_alt hσ
  have hZ : (quadPlusForm (m + 1) K).IsLagrangian (stdLag (m + 1) K) :=
    isLagrangian_stdLag (m + 1) K
  have hpar := QuadForm.IsLagrangian.even_add_add (Φ := quadPlusForm (m + 1) K)
    (finrank_flipSpace (m + 1) K) hMA hMB hZ
  have hcross : (m + 1) - Module.finrank K ↥(c.spanAt Finset.univ ⊓ c.alt) = 1 := by
    rw [inf_comm, c.alt_inf_spanAt_univ hσ, c.finrank_sub (by omega)]
    omega
  rw [hcross] at hpar
  rw [add_assoc, Nat.even_add] at hpar
  have h1odd : ¬ Even 1 := by decide
  have hnot : ¬ Even ((m + 1) - Module.finrank K ↥(c.alt ⊓ stdLag (m + 1) K) +
      ((m + 1) - Module.finrank K ↥(c.spanAt Finset.univ ⊓ stdLag (m + 1) K))) :=
    fun h => h1odd (hpar.mpr h)
  rw [Nat.even_add] at hnot
  constructor
  · intro hA
    by_contra hB
    exact hnot ⟨fun _ => hA, fun _ => hB⟩
  · intro hB
    by_contra hA
    exact hnot ⟨fun hb => absurd hb hB, fun ha => absurd ha hA⟩

omit [CharP K 2] in
theorem not_even_ruling_alt (hσ : ∀ x, σ (σ x) = x) (m : ℕ)
    (c : DChamber σ (m + 1)) :
    ¬ Even ((m + 1) - Module.finrank K ↥(c.alt ⊓ stdLag (m + 1) K)) :=
  (c.toFlipFrame.even_iff_not_even_alt hσ).1 c.even_ruling

def dChamberSystem (σ : K ≃+* K) (m : ℕ) :
    ChamberSystem (Fin (m + 1)) (DChamber σ (m + 1)) where
  adj i c d := ∀ j, j ≠ i → c.elt j = d.elt j
  equivalence _ :=
    { refl := fun _ _ _ => rfl
      symm := fun h j hj => (h j hj).symm
      trans := fun h h' j hj => (h j hj).trans (h' j hj) }

omit [CharP K 2] in
theorem dChamberSystem_adj_iff (σ : K ≃+* K) (m : ℕ) (i : Fin (m + 1))
    (c d : DChamber σ (m + 1)) :
    (dChamberSystem σ m).adj i c d ↔ ∀ j, j ≠ i → c.elt j = d.elt j :=
  Iff.rfl

theorem dChamberSystem_adj_smul_iff (E : QuadExt F K σ) (m : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
    (i : Fin (m + 1)) (c d : DChamber σ (m + 1)) :
    (dChamberSystem σ m).adj i (g • c) (g • d) ↔ (dChamberSystem σ m).adj i c d := by
  have hinj : Function.Injective
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K))) := by
    intro a b hab
    apply (bc E (m + 1) g).injective
    rw [← bcLin_apply_eq_bc E (m + 1) g a, ← bcLin_apply_eq_bc E (m + 1) g b]
    exact hab
  rw [dChamberSystem_adj_iff, dChamberSystem_adj_iff]
  constructor
  · intro h j hj
    have h1 := h j hj
    rw [elt_smul, elt_smul] at h1
    exact Submodule.map_injective_of_injective hinj h1
  · intro h j hj
    rw [elt_smul, elt_smul]
    exact congrArg (fun W => W.map
      (bcLin E (m + 1) (g : (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K)))) (h j hj)


omit [CharP K 2] in
theorem jEmb_eq_sum_stdE (E : QuadExt F K σ) (n : ℕ) (x : Fin n → K) :
    jEmb E n x = (∑ i, x i • stdE (K := K) (n := n) i) +
      ∑ i, σ (x i) • stdF (K := K) (n := n) i := by
  ext p
  cases p with
  | inl i =>
    simp only [jEmb_apply_inl, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, stdE_inl,
      stdF_inl, smul_eq_mul, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg (Ne.symm hj), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  | inr i =>
    simp only [jEmb_apply_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, stdE_inr,
      stdF_inr, smul_eq_mul, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem diagTorusV_le_orthDerived (E : QuadExt F K σ) [Finite K] (hn : 4 ≤ n) :
    diagTorusV F σ n ≤ CFSG.RankThree.Classical2.orthDerived (Qn E n) := by
  rintro g ⟨t, rfl⟩
  rw [← rulingGroup_eq_orthDerived E hn]
  exact mem_rulingGroup_of_map_stdLag E n (diagHom_mem_orthogonalGroup E n t)
    (map_stdLag_diagHom E n t)

theorem smul_stdDChamber_eq_iff (E : QuadExt F K σ) (n : ℕ)
    (g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))) :
    g • stdDChamber σ n = stdDChamber σ n ↔
      (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) ∈ diagTorusV F σ n := by
  constructor
  · intro h
    have hline : ∀ i, (K ∙ stdE (K := K) (n := n) i).map
        (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) =
        K ∙ stdE (K := K) (n := n) i := by
      intro i
      have h' := congrFun (congrArg (fun c : DChamber σ n => c.line) h) i
      rw [smul_line] at h'
      simpa [stdDChamber_line] using h'
    have hmem : ∀ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
        (stdE (K := K) (n := n) i) ∈ K ∙ stdE (K := K) (n := n) i := by
      intro i
      rw [← hline i]
      exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _)
    choose c hc using fun i => Submodule.mem_span_singleton.mp (hmem i)
    have hval : ∀ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
        (stdE (K := K) (n := n) i) = c i • stdE (K := K) (n := n) i :=
      fun i => (hc i).symm
    have hvalF : ∀ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
        (stdF (K := K) (n := n) i) = σ (c i) • stdF (K := K) (n := n) i := by
      intro i
      rw [← dFlip_stdE (σ := σ) i, bcLin_dFlip, hval i, dFlip_smul, dFlip_stdE]
    have hcomp : ∀ x : Fin n → K, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
        (jEmb E n x) = jEmb E n (fun i => x i * c i) := by
      intro x
      rw [jEmb_eq_sum_stdE, map_add, map_sum, map_sum]
      have h1 : (∑ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
          (x i • stdE (K := K) (n := n) i)) =
          ∑ i, x i • (c i • stdE (K := K) (n := n) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hval i]
      have h2 : (∑ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
          (σ (x i) • stdF (K := K) (n := n) i)) =
          ∑ i, σ (x i) • (σ (c i) • stdF (K := K) (n := n) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hvalF i]
      rw [h1, h2, jEmb_eq_sum_stdE]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
      · exact Finset.sum_congr rfl fun i _ => by rw [map_mul, smul_smul]
    have hgd : ∀ x : Fin n → K, (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) x =
        fun i => x i * c i := by
      intro x
      apply jEmb_injective E n
      change jEmb E n ((g : (Fin n → K) →ₗ[F] (Fin n → K)) x) =
        jEmb E n (fun i => x i * c i)
      rw [← bcLin_jEmb E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) x, hcomp x]
    have hnorm : ∀ i, σ (c i) * c i = 1 := by
      intro i
      have hx := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (mem_orthogonalGroup_of_mem_orthDerived E n g.2)
        (Pi.single i (1 : K) : Fin n → K)
      have hx' : (g : (Fin n → K) ≃ₗ[F] (Fin n → K))
          (Pi.single i (1 : K) : Fin n → K) =
          fun j => (Pi.single i (1 : K) : Fin n → K) j * c j := hgd _
      rw [hx', Qn_single_one E] at hx
      have h1 : algebraMap F K (Qn E n
          (fun j => (Pi.single i (1 : K) : Fin n → K) j * c j)) = 1 := by
        rw [hx, map_one]
      rw [algebraMap_Qn] at h1
      rw [Finset.sum_eq_single i] at h1
      · simpa [mul_comm] using h1
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hc0 : ∀ i, c i ≠ 0 := by
      intro i h0
      have h1 := hnorm i
      rw [h0, map_zero, zero_mul] at h1
      exact zero_ne_one h1
    let t : Fin n → normOne σ := fun i =>
      ⟨Units.mk0 (c i) (hc0 i), (mem_normOne σ).mpr (by simpa using hnorm i)⟩
    refine ⟨t, ?_⟩
    apply LinearEquiv.ext
    intro x
    funext i
    rw [diagHom_apply, hgd x]
    simp [t, mul_comm]
  · rintro ⟨t, ht⟩
    apply DChamber.ext
    funext i
    rw [smul_line, stdDChamber_line]
    have hval : bcLin E n (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K))
        (stdE (K := K) (n := n) i) =
        (((t i : normOne σ) : Kˣ) : K) • stdE (K := K) (n := n) i := by
      ext p
      cases p with
      | inl j =>
        by_cases hj : j = i
        · subst hj
          simp [bcLin_diagHom_inl, stdE]
        · simp [bcLin_diagHom_inl, stdE, hj]
      | inr j => simp [bcLin_diagHom_inr, stdE]
    have hline : (K ∙ stdE (K := K) (n := n) i).map
        (bcLin E n (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K))) =
        K ∙ stdE (K := K) (n := n) i := by
      rw [Submodule.map_span, Set.image_singleton, hval]
      exact Submodule.span_singleton_smul_eq
        (isUnit_iff_ne_zero.mpr (Units.ne_zero ((t i : normOne σ) : Kˣ))) _
    have hcoe : (g : (Fin n → K) →ₗ[F] (Fin n → K)) =
        (diagHom F σ n t : (Fin n → K) →ₗ[F] (Fin n → K)) := by
      rw [← ht]
    rw [hcoe]
    exact hline

theorem stabilizer_stdDChamber (E : QuadExt F K σ) :
    MulAction.stabilizer ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n))
        (stdDChamber σ n) =
      (diagTorusV F σ n).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived (Qn E n)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, smul_stdDChamber_eq_iff]


private noncomputable def frameMap {n : ℕ} (w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K)) :
    (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) where
  toFun y := ∑ p, y p • w p
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

omit [CharP K 2] in
private theorem frameMap_apply {n : ℕ} (w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K))
    (y : Fin n ⊕ Fin n → K) : frameMap w y = ∑ p, y p • w p := rfl

omit [CharP K 2] in
private theorem frameMap_stdE {n : ℕ} (w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K))
    (i : Fin n) :
    frameMap w (stdE (K := K) (n := n) i) = w (Sum.inl i) := by
  rw [frameMap_apply, Finset.sum_eq_single (Sum.inl i)]
  · simp
  · intro p _ hp
    cases p with
    | inl j =>
      have hji : j ≠ i := fun h => hp (by rw [h])
      simp [stdE, hji]
    | inr j => simp [stdE]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CharP K 2] in
private theorem dFlip_finset_sum {ι : Type*} {n : ℕ} (s : Finset ι) (a : ι → K)
    (u : ι → Fin n ⊕ Fin n → K) :
    dFlip σ (∑ i ∈ s, a i • u i) = ∑ i ∈ s, σ (a i) • dFlip σ (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    ext x
    cases x <;> simp [dFlip]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, dFlip_add, dFlip_smul, ih]

omit [CharP K 2] in
private theorem frameMap_dFlip {n : ℕ} (w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K))
    (hw : ∀ i, w (Sum.inr i) = dFlip σ (w (Sum.inl i)))
    (hσ : ∀ x, σ (σ x) = x) (y : Fin n ⊕ Fin n → K) :
    frameMap w (dFlip σ y) = dFlip σ (frameMap w y) := by
  rw [frameMap_apply, frameMap_apply, dFlip_finset_sum]
  conv_lhs => rw [Fintype.sum_sum_type]
  conv_rhs => rw [Fintype.sum_sum_type]
  simp only [dFlip_apply_inl, dFlip_apply_inr, hw, dFlip_dFlip hσ]
  rw [add_comm]

omit [CharP K 2] in
private theorem flipHerm_finset_sum_left {ι : Type*} {n : ℕ} (s : Finset ι)
    (a : ι → K) (u : ι → Fin n ⊕ Fin n → K) (v : Fin n ⊕ Fin n → K) :
    flipHerm σ (∑ i ∈ s, a i • u i) v =
      ∑ i ∈ s, a i * flipHerm σ (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, flipHerm_add_left, flipHerm_smul_left, ih]

omit [CharP K 2] in
private theorem flipHerm_finset_sum_right {ι : Type*} {n : ℕ} (s : Finset ι)
    (u : Fin n ⊕ Fin n → K) (a : ι → K) (v : ι → Fin n ⊕ Fin n → K) :
    flipHerm σ u (∑ i ∈ s, a i • v i) =
      ∑ i ∈ s, σ (a i) * flipHerm σ u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, flipHerm_add_right,
      flipHerm_smul_right, ih]

omit [CharP K 2] in
private theorem frameMap_preserves_Q {n : ℕ} (v : Fin n → (Fin n ⊕ Fin n → K))
    (M : Submodule K (Fin n ⊕ Fin n → K)) (hM : IsFlipflopSub σ M)
    (hvM : ∀ i, v i ∈ M)
    (hh : ∀ i, flipHerm σ (v i) (v i) = 1)
    (horth : ∀ i j, i ≠ j → flipHerm σ (v i) (v j) = 0)
    (hσ : ∀ x, σ (σ x) = x) (y : Fin n ⊕ Fin n → K) :
    quadPlus n K (frameMap (Sum.elim v (fun i => dFlip σ (v i))) y) = quadPlus n K y := by
  classical
  let w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K) := Sum.elim v (fun i => dFlip σ (v i))
  let a : Fin n → K := fun i => y (Sum.inl i)
  let b : Fin n → K := fun i => y (Sum.inr i)
  let A : Fin n ⊕ Fin n → K := ∑ i, a i • v i
  let A' : Fin n ⊕ Fin n → K := ∑ i, σ (b i) • v i
  have hw : ∀ i, w (Sum.inr i) = dFlip σ (w (Sum.inl i)) := by
    intro i
    simp [w]
  have hL : frameMap w y = A + dFlip σ A' := by
    rw [frameMap_apply, Fintype.sum_sum_type]
    have h1 : (∑ i, y (Sum.inl i) • w (Sum.inl i)) = A := rfl
    have h2 : (∑ i, y (Sum.inr i) • w (Sum.inr i)) = dFlip σ A' := by
      rw [dFlip_finset_sum]
      simp only [hσ, w, Sum.elim_inr, b]
    rw [h1, h2]
  have hA_mem : A ∈ M := by
    rw [show A = ∑ i, a i • v i from rfl]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvM i)
  have hA'_mem : A' ∈ M := by
    rw [show A' = ∑ i, σ (b i) • v i from rfl]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hvM i)
  have hQA : quadPlus n K A = 0 := hM.total A hA_mem
  have hQA' : quadPlus n K A' = 0 := hM.total A' hA'_mem
  have hQB : quadPlus n K (dFlip σ A') = 0 := by
    rw [quadPlus_dFlip, hQA', map_zero]
  have hAB : polar (quadPlus n K) A (dFlip σ A') = ∑ i, a i * b i := by
    show flipHerm σ A A' = ∑ i, a i * b i
    rw [show A' = ∑ i, σ (b i) • v i from rfl, flipHerm_finset_sum_right]
    have h1 : ∀ i, flipHerm σ A (v i) = a i := by
      intro i
      rw [show A = ∑ j, a j • v j from rfl, flipHerm_finset_sum_left]
      rw [Finset.sum_eq_single i]
      · simp [hh i]
      · intro j _ hji
        rw [horth j i hji, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [Finset.sum_congr rfl fun i _ => by rw [hσ, h1 i]]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hL, QuadraticMap.map_add (quadPlus n K), hQA, hQB, hAB, quadPlus_apply]
  simp [a, b]

omit [CharP K 2] in
theorem FlipFrame.exists_isometry (hσ : ∀ x, σ (σ x) = x)
    (hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a) (c : FlipFrame σ n) :
    ∃ L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K),
      (∀ y, quadPlus n K (L y) = quadPlus n K y) ∧ (∀ y, L (dFlip σ y) = dFlip σ (L y)) ∧
        ∀ i, (K ∙ stdE (K := K) i).map L.toLinearMap = c.line i := by
  choose v hv using fun i => c.exists_gen hσ hN i
  have hvmem : ∀ i, v i ∈ c.line i := fun i => (hv i).1
  have hvh : ∀ i, flipHerm σ (v i) (v i) = 1 := fun i => (hv i).2.2.1
  have hline : ∀ i, c.line i = K ∙ v i := fun i => (hv i).2.2.2
  let w : Fin n ⊕ Fin n → (Fin n ⊕ Fin n → K) := Sum.elim v (fun i => dFlip σ (v i))
  let Llin : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) := frameMap w
  have hL_flip : ∀ y, Llin (dFlip σ y) = dFlip σ (Llin y) := fun y =>
    frameMap_dFlip w (by intro i; simp [w]) hσ y
  have hL_Q : ∀ y, quadPlus n K (Llin y) = quadPlus n K y := fun y =>
    frameMap_preserves_Q v (c.spanAt Finset.univ)
      (c.isFlipflopSub_spanAt hσ Finset.univ)
      (fun i => c.line_le_spanAt (Finset.mem_univ i) (hvmem i))
      hvh
      (fun i j hij => c.flipHerm_eq_zero i j hij (v i) (hvmem i) (v j) (hvmem j)) hσ y
  have hinj : Function.Injective Llin := by
    apply QuadForm.injective_of_Q (Φ := quadPlusForm n K)
    intro y
    rw [quadPlusForm_Q, quadPlusForm_Q]
    exact hL_Q y
  let L : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
    LinearMap.linearEquivOfInjective Llin hinj rfl
  have hL_coe : (L : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = Llin :=
    LinearEquiv.coe_ofInjectiveOfFinrankEq Llin hinj rfl
  have hL_stdE : ∀ i, L (stdE (K := K) i) = v i := by
    intro i
    change (L : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) (stdE (K := K) i) = v i
    rw [hL_coe]
    simpa [w] using frameMap_stdE w i
  refine ⟨L, fun y => hL_Q y, fun y => hL_flip y, fun i => ?_⟩
  rw [Submodule.map_span, Set.image_singleton]
  change K ∙ L (stdE (K := K) i) = c.line i
  rw [hL_stdE i]
  exact (hline i).symm

theorem exists_smul_stdDChamber (E : QuadExt F K σ) [Finite K] (hn : 4 ≤ n)
    (c : DChamber σ n) :
    ∃ g : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E n)),
      g • stdDChamber σ n = c := by
  have hσ : ∀ x, σ (σ x) = x := E.isUnitary.invol
  have hN : ∀ a : K, σ a = a → a ≠ 0 → ∃ x : K, x * σ x = a := by
    intro a ha ha0
    obtain ⟨x, hx⟩ := E.isUnitary.norm_surj a ha ha0
    exact ⟨x, by rw [mul_comm]; exact hx⟩
  obtain ⟨L, hL_Q, hL_flip, hline⟩ := c.toFlipFrame.exists_isometry hσ hN
  obtain ⟨g, hg⟩ := exists_bc_eq E n L hL_flip
  have hLmem : L ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro y
    change quadPlus n K (L y) = quadPlus n K y
    exact hL_Q y
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
    apply (bc_mem_orthogonalGroup_iff E n g).mp
    rw [hg]
    exact hLmem
  have hbcL : bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K)) =
      (L : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) := by
    rw [bcLin_eq_coe_bc, hg]
  have hbc_stdE : ∀ i, bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))
      (stdE (K := K) (n := n) i) = L (stdE (K := K) i) := by
    intro i
    rw [hbcL]
    rfl
  have hline' : ∀ i, c.line i = K ∙ L (stdE (K := K) i) := by
    intro i
    rw [← hline i, Submodule.map_span, Set.image_singleton]
    rfl
  have hspan_eq : c.toFlipFrame.spanAt Finset.univ =
      Submodule.span K (Set.range fun i => L (stdE (K := K) i)) := by
    rw [FlipFrame.spanAt]
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      rw [hline' i]
      exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.subset_span ⟨i, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact c.toFlipFrame.line_le_spanAt (Finset.mem_univ i) (by
        rw [hline' i]
        exact Submodule.mem_span_singleton_self _)
  have hmap : (stdLag n K).map (bcLin E n g) = c.toFlipFrame.spanAt Finset.univ := by
    rw [hbcL, stdLag_eq_span_stdE, Submodule.map_span, hspan_eq]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨stdE (K := K) (n := n) i, ⟨i, rfl⟩, rfl⟩
  have hEven : Even (n - Module.finrank K
      ↥(stdLag n K ⊓ (stdLag n K).map (bcLin E n g))) := by
    rw [hmap, inf_comm]
    exact c.even_ruling
  have hgR : g ∈ rulingGroup E n := (mem_rulingGroup E n g).mpr ⟨hgO, hEven⟩
  have hgΩ : g ∈ CFSG.RankThree.Classical2.orthDerived (Qn E n) := by
    rw [← rulingGroup_eq_orthDerived E hn]
    exact hgR
  refine ⟨⟨g, hgΩ⟩, ?_⟩
  apply DChamber.ext
  funext i
  rw [smul_line, stdDChamber_line]
  change (K ∙ stdE (K := K) (n := n) i).map
    (bcLin E n (g : (Fin n → K) →ₗ[F] (Fin n → K))) = c.line i
  rw [Submodule.map_span, Set.image_singleton, hbc_stdE i, ← hline' i]

end CFSG.ClassicalInvolution.PhanDn

end
