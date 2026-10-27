module

public import CFSG.Blueprint.ChevalleySimpleRootOperators
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.LemmaR
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatUnique

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open RootWeightSpace RootSpace
open scoped RealInnerProductSpace Pointwise

variable {K : Type} [Field K]



open CFSG.Blueprint.Chevalley

theorem f4_raw_field_pow_eq_one
    (alpha : MulAut (adjointGroup Tag.F4 K))
    (sigma : K ≃+* K)
    (n : ℕ)
    (hact : ∀ (i : Fin Tag.F4.rank) (c : K), alpha (adjX Tag.F4 K i c) = adjX Tag.F4 K i (sigma c))
    (halpha : alpha ^ n = 1) :
    sigma ^ n = 1 := by
  have key : ∀ m : ℕ, ∀ (i : Fin Tag.F4.rank) (c : K),
      (alpha ^ m) (adjX Tag.F4 K i c) = adjX Tag.F4 K i ((sigma ^ m) c) := by
    intro m
    induction m with
    | zero =>
      intro i c
      simp
    | succ m ih =>
      intro i c
      rw [pow_succ', MulAut.mul_apply, ih, hact i ((sigma ^ m) c)]
      rw [pow_succ']
      rfl
  ext c
  have h1 := key n ⟨0, by decide⟩ c
  rw [halpha, MulAut.one_apply] at h1
  have h2 := adjX_injective ⟨0, by decide⟩ h1
  exact h2.symm


private theorem f4_exists_neighbor_cartan_natAbs (i : Fin Tag.F4.rank) :
    ∃ j : Fin Tag.F4.rank, (Tag.F4.cartan j i).natAbs = 1 := by
  fin_cases i
  · exact ⟨⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨0, by decide⟩, by decide⟩
  · exact ⟨⟨1, by decide⟩, by decide⟩
  · exact ⟨⟨2, by decide⟩, by decide⟩

private theorem f4_xOp_hVec_coeff (i j : Fin Tag.F4.rank) (c d : K) :
    ((xOp Tag.F4 K i d - xOp Tag.F4 K i c) (hVec Tag.F4 K j))
        (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) =
      (((Tag.F4.cartan j i).natAbs : K) * (d - c)) := by
  rw [LinearMap.sub_apply, xOp_apply_hVec, xOp_apply_hVec]
  simp [hVec, rootVec_eq_single_of_isRoot (isRoot_single Tag.F4 i),
    sub_eq_add_neg]
  try ring_nf


theorem f4_raw_inner_borel_local
    {g : adjointGroup Tag.F4 K}
    (hgB : (g : ModGL Tag.F4 K) ∈ borelGroup Tag.F4 K)
    (σ : K ≃+* K)
    (hσ : ∀ (i : Fin Tag.F4.rank) (c : K),
      MulAut.conj g (adjX Tag.F4 K i c) = adjX Tag.F4 K i (σ c)) :
    σ = 1 ∧ (g : ModGL Tag.F4 K) ∈ posUnipotent Tag.F4 K := by
  classical
  let gv : ModGL Tag.F4 K := (g : ModGL Tag.F4 K)
  have hTU : gv ∈ (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
      (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right
      (H := torusGroup Tag.F4 K) (N := posUnipotent Tag.F4 K)
      (torusGroup_le_normalizer_posUnipotent (τ := Tag.F4) (R := K))]
    exact hgB
  obtain ⟨t, ht, u, hu, hg_eq⟩ := hTU
  have hg_eq' : gv = t * u := hg_eq.symm
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := Tag.F4) (K := K) ht
  obtain ⟨κ, hκ, hinner⟩ := RootWeightSpace.exists_inner_toRootSpace Tag.F4
  let w : ℝ := κ⁻¹
  have hwpos : 0 < w := inv_pos.mpr hκ
  have hε : (0 : ℝ) ≤ w := hwpos.le
  let m : RootWeightSpace Tag.F4 := (RootWeightSpace.toRootSpace Tag.F4).symm (heightVector Tag.F4)
  have hm_toRootSpace : RootWeightSpace.toRootSpace Tag.F4 m = heightVector Tag.F4 := by
    dsimp [m]
    exact (RootWeightSpace.toRootSpace Tag.F4).apply_symm_apply _
  let wt : Label Tag.F4 → ℝ := latticeGrade m
  have hinner_lattice : ∀ α : Fin Tag.F4.rank → ℤ,
      ⟪RootWeightSpace.ofLattice α, m⟫ = w * (height α : ℝ) := by
    intro α
    have h := hinner (RootWeightSpace.ofLattice α) m
    rw [RootWeightSpace.toRootSpace_ofLattice, hm_toRootSpace,
      inner_ofLattice_heightVector] at h
    calc
      ⟪RootWeightSpace.ofLattice α, m⟫ = w * (κ * ⟪RootWeightSpace.ofLattice α, m⟫) := by
        rw [show w = κ⁻¹ from rfl, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
      _ = w * (height α : ℝ) := by rw [← h]
  have hm : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 α → 0 < height α →
      w ≤ ⟪RootWeightSpace.ofLattice α, m⟫ := by
    intro α _ hα
    rw [hinner_lattice]
    have h1 : (1 : ℝ) ≤ (height α : ℝ) := by exact_mod_cast hα
    nlinarith
  have hUraise : LabelRaises wt w ((u : Module.End K (RootModule Tag.F4 K)) - 1) :=
    ((mem_labelRaisingSubgroup (wt := wt) (ε := w) (hε := hε)).1
      ((posUnipotent_le_labelRaisingSubgroup (m := m) (ε := w) hε hm) hu)).1
  have hUinvraise : LabelRaises wt w
      (((u⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) - 1) :=
    ((mem_labelRaisingSubgroup (wt := wt) (ε := w) (hε := hε)).1
      ((posUnipotent_le_labelRaisingSubgroup (m := m) (ε := w) hε hm) hu)).2
  have hkey : ∀ (i : Fin Tag.F4.rank) (c : K),
      σ c = ((rootChar a (Pi.single i 1) : Kˣ) : K) * c := by
    intro i c
    obtain ⟨j, hj⟩ := f4_exists_neighbor_cartan_natAbs i
    let A : K := ((Tag.F4.cartan j i).natAbs : K)
    let ai : K := ((rootChar a (Pi.single i 1) : Kˣ) : K)
    let d : K := ai⁻¹ * σ c
    let xc : Module.End K (RootModule Tag.F4 K) := xOp Tag.F4 K i c
    have hxU : xUnit Tag.F4 K i c ∈ posUnipotent Tag.F4 K :=
      xUnit_mem_posUnipotent (τ := Tag.F4) (K := K) i c
    have hXraise : LabelRaises wt w (xc - 1) := by
      simpa [xc, coe_xUnit] using
        (((mem_labelRaisingSubgroup (wt := wt) (ε := w) (hε := hε)).1
          ((posUnipotent_le_labelRaisingSubgroup (m := m) (ε := w) hε hm) hxU)).1)
    have hraw : gv * xUnit Tag.F4 K i c * gv⁻¹ = xUnit Tag.F4 K i (σ c) := by
      simpa [gv, adjX, MulAut.conj_apply] using
        congrArg (fun x : adjointGroup Tag.F4 K => (x : ModGL Tag.F4 K)) (hσ i c)
    have hraw_tu : t * u * xUnit Tag.F4 K i c * u⁻¹ * t⁻¹ =
        xUnit Tag.F4 K i (σ c) := by
      have h := hraw
      rw [hg_eq', mul_inv_rev] at h
      simpa [mul_assoc] using h
    have hstep : u * xUnit Tag.F4 K i c * u⁻¹ =
        t⁻¹ * xUnit Tag.F4 K i (σ c) * t := by
      calc
        u * xUnit Tag.F4 K i c * u⁻¹ =
            t⁻¹ * (t * u * xUnit Tag.F4 K i c * u⁻¹ * t⁻¹) * t := by group
        _ = t⁻¹ * xUnit Tag.F4 K i (σ c) * t := by rw [hraw_tu]
    have hforward : rootDiagUnit Tag.F4 a * xUnit Tag.F4 K i (σ c) *
        (rootDiagUnit Tag.F4 a)⁻¹ = xUnit Tag.F4 K i (ai * σ c) := by
      simpa [ai, pinnedX_single] using
        rootDiagUnit_conj_pinnedX (a := a) (α := Pi.single i 1)
          (isRoot_single Tag.F4 i) (σ c)
    have hback : rootDiagUnit Tag.F4 a⁻¹ * xUnit Tag.F4 K i (σ c) *
        (rootDiagUnit Tag.F4 a⁻¹)⁻¹ = xUnit Tag.F4 K i (ai⁻¹ * σ c) := by
      have := rootDiagUnit_conj_pinnedX (a := a⁻¹) (α := Pi.single i 1)
        (isRoot_single Tag.F4 i) (σ c)
      simpa [ai, pinnedX_single, rootChar_inv_apply] using this
    have htconj : t⁻¹ * xUnit Tag.F4 K i (σ c) * t = xUnit Tag.F4 K i d := by
      rw [ha, rootDiagUnit_inv]
      have hright : rootDiagUnit Tag.F4 a = (rootDiagUnit Tag.F4 a⁻¹)⁻¹ := by
        rw [rootDiagUnit_inv]
        simp
      rw [hright]
      simpa [d] using hback
    have hUconj : (u : Module.End K (RootModule Tag.F4 K)) * xc *
        ((u⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) =
        xOp Tag.F4 K i d := by
      have h := congrArg (fun z : ModGL Tag.F4 K =>
        (z : Module.End K (RootModule Tag.F4 K))) (hstep.trans htconj)
      simpa [xc, Units.val_mul, coe_xUnit] using h
    let U : Module.End K (RootModule Tag.F4 K) :=
      (u : Module.End K (RootModule Tag.F4 K))
    let Uinv : Module.End K (RootModule Tag.F4 K) :=
      ((u⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))
    let X : Module.End K (RootModule Tag.F4 K) := xc
    let T : Module.End K (RootModule Tag.F4 K) :=
      (U - 1) * (X - 1) - (X - 1) * (U - 1)
    let D : Module.End K (RootModule Tag.F4 K) := T * Uinv
    have hT : LabelRaises wt (w + w) T := by
      have h1 : LabelRaises wt (w + w) ((U - 1) * (X - 1)) := by
        simpa [U, X, xc] using hUraise.mul hXraise
      have h2 : LabelRaises wt (w + w) ((X - 1) * (U - 1)) := by
        simpa [U, X, xc] using hXraise.mul hUraise
      simpa [T] using h1.sub h2
    have hUinv0 : LabelRaises wt 0 Uinv := by
      exact LabelRaises.of_sub_one
        (hUinvraise.mono hε)
    have hD : LabelRaises wt (w + w) D := by
      have := hT.mul hUinv0
      simpa [D] using this
    have hUUinv : U * Uinv = 1 := by
      dsimp [U, Uinv]
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hD_unit : D = U * X * Uinv - X := by
      dsimp [D, T]
      calc
        ((U - 1) * (X - 1) - (X - 1) * (U - 1)) * Uinv =
            (U * X - X * U) * Uinv := by noncomm_ring
        _ = U * X * Uinv - X * (U * Uinv) := by noncomm_ring
        _ = U * X * Uinv - X := by rw [hUUinv, mul_one]
    have hD_eq : D = xOp Tag.F4 K i d - xc := by
      rw [hD_unit, hUconj]
    have hzero : D (hVec Tag.F4 K j)
        (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) = 0 := by
      by_contra hne
      have hle := hD (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩)
        (Sum.inl j) (by
          simpa [hVec, rootVec_eq_single_of_isRoot (isRoot_single Tag.F4 i)] using hne)
      have hwh : wt (Sum.inl j) = 0 := by
        simp [wt, latticeGrade, Label.latticeWeight]
      have hwv : wt (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) = w := by
        dsimp only [wt, latticeGrade, Label.latticeWeight]
        simp [hinner_lattice, height_single]
      have : (0 : ℝ) + (w + w) ≤ w := by simpa [hwh, hwv] using hle
      nlinarith
    have hcoeff : (xOp Tag.F4 K i d - xc) (hVec Tag.F4 K j)
        (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) = A * (d - c) := by
      change ((xOp Tag.F4 K i d - xOp Tag.F4 K i c) (hVec Tag.F4 K j))
        (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) = A * (d - c)
      rw [f4_xOp_hVec_coeff]
    have hA : A = 1 := by
      dsimp [A]
      rw [hj]
      norm_num
    have hdc : d = c := by
      have hzero' : (xOp Tag.F4 K i d - xc) (hVec Tag.F4 K j)
          (Sum.inr ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩) = 0 := by
        simpa [hD_eq] using hzero
      have hzero2 : A * (d - c) = 0 := by
        rw [← hcoeff]
        exact hzero'
      rw [hA, one_mul] at hzero2
      exact sub_eq_zero.mp hzero2
    have hai_ne : ai ≠ 0 := by
      dsimp [ai]
      exact Units.ne_zero _
    have h := congrArg (fun x : K => ai * x) hdc
    dsimp [d] at h
    rw [← mul_assoc, mul_inv_cancel₀ hai_ne, one_mul] at h
    exact h
  have hai_one : ∀ i : Fin Tag.F4.rank,
      ((rootChar a (Pi.single i 1) : Kˣ) : K) = 1 := by
    intro i
    have := hkey i 1
    simpa using this.symm
  have ha_one : a = 1 := by
    funext i
    apply Units.ext
    have h := hai_one i
    have hsingle : ((rootChar a (Pi.single i 1) : Kˣ) : K) = ((a i : Kˣ) : K) := by
      simpa using congrArg (fun u : Kˣ => (u : K)) (rootChar_nsmul_single a i 1)
    rw [hsingle] at h
    simpa using h
  have ht_one : t = 1 := by
    rw [ha, ha_one, rootDiagUnit_one]
  have hsigma : σ = 1 := by
    ext c
    have := hkey ⟨0, by decide⟩ c
    rw [hai_one, one_mul] at this
    exact this
  refine ⟨hsigma, ?_⟩
  rw [show (g : ModGL Tag.F4 K) = gv from rfl, hg_eq', ht_one, one_mul]
  exact hu

section NativeCoordinates

open CFSG.SignalizerFunctorTheorem.NonLocalExc
open CFSG.StandardType.F4ExplicitPos.BruhatNo117
open CFSG.StandardType.F4ExplicitPos.BruhatUnique

theorem f4_exists_coord (i : Fin Tag.F4.rank) {y : ModGL Tag.F4 K}
    (hy : y ∈ posUnipotent Tag.F4 K) :
    ∃ c : K, HasCoord i y c := by
  obtain ⟨-, -, hUX, -, -, -, -⟩ := f4_simple_positive_root_complement (R := K) i
  have hy' : y ∈ (rootSubgroup Tag.F4 K (Pi.single i 1) : Set (ModGL Tag.F4 K)) *
      (rootSpan Tag.F4 K (simpleComplement Tag.F4 i) : Set (ModGL Tag.F4 K)) := by
    have hy1 : y ∈ (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := hy
    rw [hUX] at hy1
    exact hy1
  obtain ⟨a, ha, b, hb, rfl⟩ := hy'
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 ha
  exact ⟨c, b, hb, by rw [pinnedX_single]⟩

theorem f4_unipComplement_conj_mem (i : Fin Tag.F4.rank) {u : ModGL Tag.F4 K}
    (hu : u ∈ posUnipotent Tag.F4 K) {b : ModGL Tag.F4 K}
    (hb : b ∈ unipComplement Tag.F4 K i) :
    u * b * u⁻¹ ∈ unipComplement Tag.F4 K i := by
  obtain ⟨hNle, hNnormal, -, -, -, -, -⟩ := f4_simple_positive_root_complement (R := K) i
  have hbN : b ∈ rootSpan Tag.F4 K (simpleComplement Tag.F4 i) := by
    simpa [unipComplement] using hb
  have := hNnormal.conj_mem ⟨b, hNle hbN⟩ (Subgroup.mem_subgroupOf.2 hbN) ⟨u, hu⟩
  simpa [unipComplement, simpleComplement] using (Subgroup.mem_subgroupOf.1 this)

theorem f4_unipComplement_conj_mem' (i : Fin Tag.F4.rank) {u : ModGL Tag.F4 K}
    (hu : u ∈ posUnipotent Tag.F4 K) {b : ModGL Tag.F4 K}
    (hb : b ∈ unipComplement Tag.F4 K i) :
    u⁻¹ * b * u ∈ unipComplement Tag.F4 K i := by
  simpa using f4_unipComplement_conj_mem (K := K) i (inv_mem hu) hb

theorem f4_HasCoord_mul {i : Fin Tag.F4.rank} {y y' : ModGL Tag.F4 K} {c c' : K}
    (h : HasCoord i y c) (h' : HasCoord i y' c') :
    HasCoord i (y * y') (c + c') := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  refine ⟨(xUnit Tag.F4 K i c')⁻¹ * b * xUnit Tag.F4 K i c' * b', ?_, ?_⟩
  · exact mul_mem (f4_unipComplement_conj_mem' (K := K) i
      (CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent i c') hb) hb'
  · rw [xUnit_add]
    group

theorem f4_HasCoord_inv {i : Fin Tag.F4.rank} {y : ModGL Tag.F4 K} {c : K}
    (h : HasCoord i y c) : HasCoord i y⁻¹ (-c) := by
  obtain ⟨b, hb, rfl⟩ := h
  refine ⟨xUnit Tag.F4 K i c * b⁻¹ * (xUnit Tag.F4 K i c)⁻¹, ?_, ?_⟩
  · exact f4_unipComplement_conj_mem (K := K) i (CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent i c) (inv_mem hb)
  · have h1 : xUnit Tag.F4 K i (-c) = (xUnit Tag.F4 K i c)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← xUnit_add, neg_add_cancel, xUnit_zero]
    rw [h1]
    group

theorem f4_HasCoord_conj_posUnipotent {i : Fin Tag.F4.rank} {y : ModGL Tag.F4 K} {c : K}
    (h : HasCoord i y c) {u : ModGL Tag.F4 K} (hu : u ∈ posUnipotent Tag.F4 K) :
    HasCoord i (u⁻¹ * y * u) c := by
  obtain ⟨d, hd⟩ := f4_exists_coord (K := K) i hu
  have h1 : HasCoord i (u⁻¹ * y) (-d + c) :=
    f4_HasCoord_mul (K := K) (f4_HasCoord_inv (K := K) hd) h
  have h2 : HasCoord i ((u⁻¹ * y) * u) ((-d + c) + d) :=
    f4_HasCoord_mul (K := K) h1 hd
  have h3 : (-d + c) + d = c := by ring
  simpa [h3] using h2

theorem f4_pos_of_coord_of_conj_mem {i : Fin Tag.F4.rank} {w : WeylGroup Tag.F4}
    {y : ModGL Tag.F4 K} {c : K} (hc : c ≠ 0) (hy : HasCoord i y c)
    (hyU : y ∈ posUnipotent Tag.F4 K)
    (hconj : (canonicalRep (coxeterSystem Tag.F4) K w)⁻¹ * y *
      canonicalRep (coxeterSystem Tag.F4) K w ∈ posUnipotent Tag.F4 K) :
    0 < height (w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ)) := by
  by_contra hneg
  set n := canonicalRep (coxeterSystem Tag.F4) K w with hn
  have hu : n⁻¹ * y * n ∈ (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := hconj
  rw [f4_posUnipotent_eq_mul_rootSpan w] at hu
  obtain ⟨uJ, huJ, uI, huI, huu⟩ := hu
  have hUB : posUnipotent Tag.F4 K ≤ borelGroup Tag.F4 K := le_sup_right
  have hbij := f4_bijOn_bruhatCell (K := K) w
  have hmem1 : (y, (1 : ModGL Tag.F4 K)) ∈
      (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)) :=
    ⟨hUB hyU, one_mem _⟩
  have hmem2 : (n * uJ * n⁻¹, uI) ∈
      (borelGroup Tag.F4 K : Set (ModGL Tag.F4 K)) ×ˢ
        (rootSpan Tag.F4 K (inversionSet w) : Set (ModGL Tag.F4 K)) :=
    ⟨hUB (canonicalRep_conj_mem_posUnipotent huJ), huI⟩
  have heq : y * n * 1 = (n * uJ * n⁻¹) * n * uI := by
    have h1 : y * n = n * (n⁻¹ * y * n) := by group
    rw [mul_one, h1, ← huu]
    group
  have hpair := hbij.injOn hmem1 hmem2 heq
  have hyeq : y = n * uJ * n⁻¹ := congrArg Prod.fst hpair
  have hyspan : y ∈ rootSpan Tag.F4 K ((fun α => w • α) '' nonInversionSet w) := by
    rw [hyeq]
    exact canonicalRep_conj_mem_rootSpan
      (fun α (h : α ∈ nonInversionSet w) => h.1) huJ
  have hsub : (fun α => w • α) '' nonInversionSet w ⊆ simpleComplement Tag.F4 i := by
    rintro _ ⟨α, ⟨hα, hαpos, hwα⟩, rfl⟩
    refine ⟨IsRoot.smul hα w, hwα, fun h => hneg ?_⟩
    have : α = w⁻¹ • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
      rw [← h, inv_smul_smul]
    rw [← this]
    exact hαpos
  have hle : rootSpan Tag.F4 K ((fun α => w • α) '' nonInversionSet w) ≤
      unipComplement Tag.F4 K i := biSup_mono hsub
  have hyU' : y ∈ unipComplement Tag.F4 K i := hle hyspan
  obtain ⟨b, hb, hyb⟩ := hy
  have hxb : xUnit Tag.F4 K i c ∈ unipComplement Tag.F4 K i := by
    have : xUnit Tag.F4 K i c = y * b⁻¹ := by rw [hyb]; group
    rw [this]
    exact mul_mem hyU' (inv_mem hb)
  have hinf : rootSubgroup Tag.F4 K (Pi.single i 1) ⊓ unipComplement Tag.F4 K i = ⊥ := by
    obtain ⟨-, -, -, -, hinf, -, -⟩ := f4_simple_positive_root_complement (R := K) i
    simpa [unipComplement, simpleComplement] using hinf
  have hx1 : xUnit Tag.F4 K i c ∈
      rootSubgroup Tag.F4 K (Pi.single i 1) ⊓ unipComplement Tag.F4 K i :=
    Subgroup.mem_inf.2 ⟨CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_rootSubgroup i c, hxb⟩
  rw [hinf, Subgroup.mem_bot, ← xUnit_zero i] at hx1
  exact hc (xUnit_injective i hx1)

theorem f4_mem_borelGroup_of_fixed_simple {g : ModGL Tag.F4 K}
    (hg : g ∈ adjointGroup Tag.F4 K)
    (hfix : ∀ i : Fin Tag.F4.rank,
      MulAut.conj g (adjX Tag.F4 K i 1) = adjX Tag.F4 K i 1) :
    g ∈ borelGroup Tag.F4 K := by
  have h : ∀ i : Fin Tag.F4.rank,
      g⁻¹ * xUnit Tag.F4 K i 1 * g ∈ posUnipotent Tag.F4 K := by
    intro i
    have h2' : g * xUnit Tag.F4 K i 1 * g⁻¹ = xUnit Tag.F4 K i 1 := by
      simpa [MulAut.conj_apply, adjX] using hfix i
    have h4 : g⁻¹ * (g * xUnit Tag.F4 K i 1 * g⁻¹) * g =
        g⁻¹ * xUnit Tag.F4 K i 1 * g := by rw [h2']
    have h5 : g⁻¹ * (g * xUnit Tag.F4 K i 1 * g⁻¹) * g =
        xUnit Tag.F4 K i 1 := by group
    have hxeq : xUnit Tag.F4 K i 1 = g⁻¹ * xUnit Tag.F4 K i 1 * g :=
      h5.symm.trans h4
    rw [hxeq.symm]
    exact CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent i 1
  have hg' : g ∈ ⋃ w, bruhatCell Tag.F4 K w := by
    rw [← f4_adjointGroup_eq_iUnion_bruhatCell]
    exact hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hw
  by_cases hw1 : w = 1
  · subst hw1
    rw [canonicalRep_one, mul_one]
    exact mul_mem hb hb'
  · exfalso
    obtain ⟨i, hroot, hneg⟩ :=
      (weyl_exchange_condition Tag.F4).2.2.2 w⁻¹ (inv_ne_one.2 hw1)
    set n := canonicalRep (coxeterSystem Tag.F4) K w with hn
    have hx : xUnit Tag.F4 K i 1 ∈ posUnipotent Tag.F4 K := CFSG.SignalizerFunctorTheorem.NonLocalExc.xUnit_mem_posUnipotent i 1
    have hyU : b⁻¹ * xUnit Tag.F4 K i 1 * b ∈ posUnipotent Tag.F4 K := by
      simpa using conj_mem_posUnipotent_of_mem_borel (inv_mem hb) hx
    have hb2 : b ∈ (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) *
        (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) := by
      rw [← (triangular_borel_structure.{0, 0} Tag.F4 K).2.2.2.2.2.1]
      exact hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hb2
    have hcoord1 : HasCoord i (u⁻¹ * xUnit Tag.F4 K i 1 * u) 1 :=
      f4_HasCoord_conj_posUnipotent (K := K) (hasCoord_xUnit i 1) hu
    obtain ⟨s, hs, hcoord2⟩ := hcoord1.conj_torus (inv_mem ht)
    have hy : (u * t)⁻¹ * xUnit Tag.F4 K i 1 * (u * t) =
        t⁻¹ * (u⁻¹ * xUnit Tag.F4 K i 1 * u) * t⁻¹⁻¹ := by group
    have hconj : n⁻¹ * ((u * t)⁻¹ * xUnit Tag.F4 K i 1 * (u * t)) * n ∈
        posUnipotent Tag.F4 K := by
      have h1 := conj_mem_posUnipotent_of_mem_borel hb' (h i)
      have h2 : b' * ((u * t * n * b')⁻¹ * xUnit Tag.F4 K i 1 * (u * t * n * b')) *
          b'⁻¹ = n⁻¹ * ((u * t)⁻¹ * xUnit Tag.F4 K i 1 * (u * t)) * n := by group
      rwa [h2] at h1
    have hyU' : t⁻¹ * (u⁻¹ * xUnit Tag.F4 K i 1 * u) * t⁻¹⁻¹ ∈ posUnipotent Tag.F4 K := by
      rw [← hy]
      exact hyU
    rw [hy] at hconj
    rw [mul_one] at hcoord2
    have hpos := f4_pos_of_coord_of_conj_mem (K := K) hs hcoord2 hyU' hconj
    omega

theorem f4_mem_borelGroup_of_fixed_simple_adjoint
    {g : adjointGroup Tag.F4 K}
    (hfix : ∀ i : Fin Tag.F4.rank,
      MulAut.conj g (adjX Tag.F4 K i 1) = adjX Tag.F4 K i 1) :
    (g : ModGL Tag.F4 K) ∈ borelGroup Tag.F4 K := by
  have hfixM : ∀ i : Fin Tag.F4.rank,
      MulAut.conj (g : ModGL Tag.F4 K) (adjX Tag.F4 K i 1) = adjX Tag.F4 K i 1 := by
    intro i
    have h := congrArg (fun z : adjointGroup Tag.F4 K => (z : ModGL Tag.F4 K)) (hfix i)
    simpa [MulAut.conj_apply, adjX] using h
  exact f4_mem_borelGroup_of_fixed_simple (K := K) g.2 hfixM

theorem f4_mem_borelGroup_of_raw
    {g : adjointGroup Tag.F4 K} (σ : K ≃+* K)
    (hσ : ∀ (i : Fin Tag.F4.rank) (c : K),
      MulAut.conj g (adjX Tag.F4 K i c) = adjX Tag.F4 K i (σ c)) :
    σ = 1 ∧ (g : ModGL Tag.F4 K) ∈ posUnipotent Tag.F4 K := by
  have hfix : ∀ i : Fin Tag.F4.rank,
      MulAut.conj (g : ModGL Tag.F4 K) (adjX Tag.F4 K i 1) = adjX Tag.F4 K i 1 := by
    intro i
    exact congrArg (fun z : adjointGroup Tag.F4 K => (z : ModGL Tag.F4 K)) (by
      simpa using hσ i 1)
  have hgB : (g : ModGL Tag.F4 K) ∈ borelGroup Tag.F4 K :=
    f4_mem_borelGroup_of_fixed_simple (K := K) g.2 hfix
  exact f4_raw_inner_borel_local (K := K) hgB σ hσ


end NativeCoordinates

end CFSG.LieType.Chevalley
