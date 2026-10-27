module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCommonWitt
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRootTransport
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherRankOnePoint
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherBruhat
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerIndex
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvariant

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix Module Submodule CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise
open CFSG.LieType.Universal.SpecialLinear (signedPerm signedPerm_apply)

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] noncomputable def fullPosEquiv : HypIndex r ε ≃ Fin (2 * r + ε) :=
  Equiv.ofBijective (fun x => ⟨fullPos x, fullPos_lt x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y hxy => fullPos_injective (congrArg Fin.val hxy), by
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega⟩)

theorem fullPosEquiv_apply (x : HypIndex r ε) : (fullPosEquiv x : ℕ) = fullPos x :=
  rfl

theorem fullPos_fullPosEquiv_symm (a : Fin (2 * r + ε)) :
    fullPos (fullPosEquiv.symm a) = a := by
  have := congrArg Fin.val (fullPosEquiv.apply_symm_apply a)
  rwa [fullPosEquiv_apply] at this

theorem finrank_span_image_fin_lt {V : Type*} [AddCommGroup V] [Module K V] {n : ℕ}
    {u : Fin n → V} (hu : LinearIndependent K u) {i : ℕ} (hi : i ≤ n) :
    finrank K (span K (u '' {j : Fin n | (j : ℕ) < i})) = i := by
  have hset : {j : Fin n | (j : ℕ) < i} = Set.range (Fin.castLE hi) := by
    ext j
    constructor
    · intro hj
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2
  rw [hset, ← Set.range_comp, finrank_span_eq_card (hu.comp _ (Fin.castLE_injective hi)),
    Fintype.card_fin]

theorem posFlag_eq_span (i : ℕ) :
    posFlag r ε K i = span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) ''
      {x | fullPos x < i}) := by
  apply le_antisymm
  · intro v hv
    rw [← Finset.univ_sum_single v]
    refine sum_mem fun x _ => ?_
    by_cases hx : fullPos x < i
    · have : (Pi.single x (v x) : HypIndex r ε → K) = v x • Pi.single x 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this]
      exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)
    · rw [hv x (not_lt.mp hx), Pi.single_zero]
      exact zero_mem _
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine mem_posFlag.mpr fun y hy => ?_
    have hxy : y ≠ x := fun e => by
      rw [e] at hy
      exact absurd hx (not_lt.mpr hy)
    simp [hxy]

theorem finrank_posFlag' {i : ℕ} (hi : i ≤ 2 * r + ε) : finrank K (posFlag r ε K i) = i := by
  have hu : LinearIndependent K fun a : Fin (2 * r + ε) =>
      (Pi.single (fullPosEquiv.symm a) (1 : K) : HypIndex r ε → K) :=
    (Pi.linearIndependent_single_one (HypIndex r ε) K).comp _ fullPosEquiv.symm.injective
  have himage : (fun a : Fin (2 * r + ε) =>
      (Pi.single (fullPosEquiv.symm a) (1 : K) : HypIndex r ε → K)) '' {a | (a : ℕ) < i} =
      (fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' {x | fullPos x < i} := by
    ext v
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨fullPosEquiv.symm a, ?_, rfl⟩
      change fullPos (fullPosEquiv.symm a) < i
      rw [fullPos_fullPosEquiv_symm]
      exact ha
    · rintro ⟨x, hx, rfl⟩
      exact ⟨fullPosEquiv x, hx, by simp⟩
  rw [posFlag_eq_span, ← himage, finrank_span_image_fin_lt hu hi]

theorem posFlag_mono {i i' : ℕ} (hii' : i ≤ i') : posFlag r ε K i ≤ posFlag r ε K i' :=
  fun _ hv a ha => hv a (le_trans hii' ha)

theorem hypForm_single_left (h : UnitaryFieldData p f K) (x : HypIndex r ε)
    (v : HypIndex r ε → K) : hypForm h r ε (Pi.single x 1) v = v (hypPartner x) := by
  rw [hypForm_apply, Finset.sum_eq_single x]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem orthogonal_posFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {i : ℕ}
    (hi : i ≤ 2 * r + ε) :
    (posFlag r ε K i).orthogonalBilin (hypForm h r ε) = posFlag r ε K (2 * r + ε - i) := by
  ext v
  rw [mem_orthogonalBilin, mem_posFlag]
  constructor
  · intro hv a ha
    have hpa : fullPos (hypPartner a) < i := by
      rw [fullPos_hypPartner hε]
      have := fullPos_lt a
      omega
    rw [← hypPartner_hypPartner a, ← hypForm_single_left h (hypPartner a) v]
    refine hv _ (mem_posFlag.mpr fun b hb => ?_)
    have hb' : b ≠ hypPartner a := fun e => by
      rw [e] at hb
      omega
    simp [hb']
  · intro hv u hu
    rw [hypForm_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : i ≤ fullPos a
    · rw [hu a ha, map_zero, zero_mul]
    · rw [hv _ (by rw [fullPos_hypPartner hε]; have := fullPos_lt a; omega), mul_zero]

theorem isSelfDualFlag_posFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    IsSelfDualFlag (hypForm h r ε) (2 * r + ε) (posFlag r ε K) :=
  ⟨fun _ hi => finrank_posFlag' hi, fun _ _ => posFlag_mono (Nat.le_succ _),
    fun _ hi => orthogonal_posFlag h hε hi⟩

theorem smul_le_smul_of_le {h : UnitaryFieldData p f K} (g : hypSU h r ε)
    {W W' : Submodule K (HypIndex r ε → K)} (hWW' : W ≤ W') : g • W ≤ g • W' := fun x hx => by
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g W).mp hx
  exact (Submodule.mem_smul_pointwise_iff_exists _ g W').mpr ⟨y, hWW' hy, rfl⟩

theorem isSelfDualFlag_smul (h : UnitaryFieldData p f K) {n : ℕ}
    {F : ℕ → Submodule K (HypIndex r ε → K)} (hF : IsSelfDualFlag (hypForm h r ε) n F)
    (g : hypSU h r ε) : IsSelfDualFlag (hypForm h r ε) n fun i => g • F i := by
  refine ⟨fun i hi => (finrank_smul g (F i)).trans (hF.1 i hi), fun i hi =>
    smul_le_smul_of_le g (hF.2.1 i hi), fun i hi => ?_⟩
  ext v
  change v ∈ (g • F i).orthogonalBilin (hypForm h r ε) ↔ v ∈ g • F (n - i)
  rw [mem_orthogonalBilin, ← hF.2.2 i hi]
  constructor
  · intro hv
    refine (Submodule.mem_smul_pointwise_iff_exists v g _).mpr
      ⟨g⁻¹ • v, mem_orthogonalBilin.mpr fun u hu => ?_, smul_inv_smul g v⟩
    have := hv (g • u) ((Submodule.mem_smul_pointwise_iff_exists _ g _).mpr ⟨u, hu, rfl⟩)
    rw [← smul_inv_smul g v] at this
    exact (hypForm_smul_smul h g u (g⁻¹ • v)).symm.trans this
  · intro hv u hu
    obtain ⟨u', hu', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists u g _).mp hu
    obtain ⟨v', hv', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists v g _).mp hv
    exact (hypForm_smul_smul h g u' v').trans ((mem_orthogonalBilin.mp hv') u' hu')

theorem span_image_smul {ι V : Type*} [AddCommGroup V] [Module K V] {v : ι → V} {c : ι → K}
    (hc : ∀ x, c x ≠ 0) (s : Set ι) :
    span K ((fun x => c x • v x) '' s) = span K (v '' s) := by
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)
  · rw [span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : v x = (c x)⁻¹ • (c x • v x) := by rw [smul_smul, inv_mul_cancel₀ (hc x), one_smul]
    rw [SetLike.mem_coe, this]
    exact smul_mem _ _ (subset_span ⟨x, hx, rfl⟩)

theorem hypSU_smul_eq_map {h : UnitaryFieldData p f K} (g : hypSU h r ε)
    (W : Submodule K (HypIndex r ε → K)) :
    g • W = W.map (mulVecLin ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) :=
  rfl

theorem exists_partner_coeffs (h : UnitaryFieldData p f K) (hε : ε ≤ 1) {d : K}
    (hd : h.bar d * d = 1) (hV : 0 < r ∨ ε = 1 ∨ d = 1) :
    ∃ cc : HypIndex r ε → K, (∀ x, cc x ≠ 0) ∧
      (∀ x, h.bar (cc x) * cc (hypPartner x) = 1) ∧ ∏ x, cc x = d := by
  classical
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hd
    exact zero_ne_one hd
  rcases hV with hr0 | hε1 | hd1
  · have hnd : h.norm d = 1 := by rw [UnitaryFieldData.norm, mul_comm]; exact hd
    obtain ⟨μ, hμ0, hμ⟩ := h.exists_div_bar_eq hnd
    have hbμ : h.bar μ ≠ 0 := (map_ne_zero h.bar).mpr hμ0
    let i₀ : Fin r := ⟨0, hr0⟩
    refine ⟨fun x => match x with
      | .inl i => if i = i₀ then μ else 1
      | .inr (.inl _) => 1
      | .inr (.inr i) => if i = i₀ then (h.bar μ)⁻¹ else 1, fun x => ?_, fun x => ?_, ?_⟩
    · rcases x with i | l | i
      · change (if i = i₀ then μ else 1) ≠ 0
        split_ifs <;> simp [hμ0]
      · exact one_ne_zero
      · change (if i = i₀ then (h.bar μ)⁻¹ else 1) ≠ 0
        split_ifs <;> simp [hbμ]
    · rcases x with i | l | i
      · change h.bar (if i = i₀ then μ else 1) * (if i = i₀ then (h.bar μ)⁻¹ else 1) = 1
        split_ifs <;> simp [hbμ]
      · change h.bar 1 * 1 = 1
        simp
      · change h.bar (if i = i₀ then (h.bar μ)⁻¹ else 1) * (if i = i₀ then μ else 1) = 1
        split_ifs <;> simp [h.bar_bar, hμ0]
    · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp only [Finset.prod_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.prod_const_one,
        one_mul]
      rw [← hμ, div_eq_mul_inv]
  · subst hε1
    refine ⟨fun x => match x with
      | .inl _ => 1
      | .inr (.inl _) => d
      | .inr (.inr _) => 1, fun x => ?_, fun x => ?_, ?_⟩
    · rcases x with i | l | i <;> simp [hd0]
    · rcases x with i | l | i <;> simp only [hypPartner, map_one, one_mul]
      exact hd
    · rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
      simp
  · subst hd1
    exact ⟨fun _ => 1, fun _ => one_ne_zero, fun _ => by rw [map_one, one_mul],
      Finset.prod_const_one⟩

theorem exists_inl_of_fullPos_lt {i : ℕ} (hi : i ≤ r) {x : HypIndex r ε}
    (hx : fullPos x < i) : ∃ j : Fin r, x = .inl j ∧ (j : ℕ) < i := by
  rcases x with j | l | j
  · exact ⟨j, rfl, by rwa [fullPos_inl] at hx⟩
  · rw [fullPos_inr_inl] at hx
    omega
  · rw [fullPos_inr_inr] at hx
    have := j.2
    omega

theorem exists_lineCoord_of_ne {x : HypIndex r ε} (hx : hypPartner x ≠ x) :
    ∃ l : Fin r ⊕ Fin r, lineCoord l = x := by
  rcases x with i | l | i
  · exact ⟨.inl i, rfl⟩
  · exact absurd rfl hx
  · exact ⟨.inr i, rfl⟩

variable (h : UnitaryFieldData p f K)

@[expose] def uBruhatCell {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (w : hypWeyl r) :
    Set (hypSU h r ε) :=
  {g | ∃ b₁ ∈ hypBorel h r ε, ∃ b₂ ∈ hypBorel h r ε, g = b₁ * weylElt h hc hc0 w.2 * b₂}

theorem exists_mem_uBruhatCell (hε : ε ≤ 1) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0)
    (g : hypSU h r ε) : ∃ w : hypWeyl r, g ∈ uBruhatCell h hc hc0 w := by
  classical
  have hF := isSelfDualFlag_posFlag (K := K) (r := r) h hε
  have hG := isSelfDualFlag_smul h hF g
  obtain ⟨w', hw', hFw', hGw'⟩ := exists_common_witt_basis h ε hε r (hypForm_isSymm h)
    (hypForm_separatingLeft h) (by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega) _ _ hF hG
  set b : Matrix (HypIndex r ε) (HypIndex r ε) K := Matrix.of fun y x => w' x y with hbdef
  have hbcol : ∀ x, b *ᵥ Pi.single x 1 = w' x := fun x => by
    funext y
    rw [mulVec_single_one, col_apply]
    rfl
  have hbJ : (b.map h.bar)ᵀ * hypGram r ε K * b = hypGram r ε K := by
    ext x y
    rw [← gramForm_single h ((b.map h.bar)ᵀ * hypGram r ε K * b) x y, ← gramForm_mulVec,
      hbcol, hbcol]
    exact hw' x y
  have hδ : h.bar b.det * b.det = 1 := by
    have h1 := congrArg det hbJ
    rw [det_mul, det_mul, det_transpose,
      show (b.map h.bar).det = h.bar b.det from (RingHom.map_det h.bar b).symm] at h1
    refine mul_right_cancel₀ (det_hypGram_ne_zero (r := r) (ε := ε) (K := K)) ?_
    linear_combination h1
  have hbdet0 : b.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hδ
    exact zero_ne_one hδ
  have hV : 0 < r ∨ ε = 1 ∨ b.det⁻¹ = 1 := by
    by_cases hr0 : 0 < r
    · exact Or.inl hr0
    by_cases hε1 : ε = 1
    · exact Or.inr (Or.inl hε1)
    obtain rfl : r = 0 := by omega
    obtain rfl : ε = 0 := by omega
    refine Or.inr (Or.inr ?_)
    rw [det_isEmpty, inv_one]
  obtain ⟨cc, hcc0, hccp, hccprod⟩ := exists_partner_coeffs h hε (d := b.det⁻¹)
    (by rw [map_inv₀, ← mul_inv, hδ, inv_one]) hV
  set M := b * diagonal cc with hMdef
  have hMJ : (M.map h.bar)ᵀ * hypGram r ε K * M = hypGram r ε K := by
    rw [hMdef, conjTranspose_mul_mul, hbJ, diagonal_gram h cc hccp]
  have hMdet : M.det = 1 := by
    rw [hMdef, det_mul, det_diagonal, hccprod, mul_inv_cancel₀ hbdet0]
  set β : hypSU h r ε := mkHypSU h M hMJ hMdet with hβdef
  have hβmat : ((β : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) = M :=
    coe_mkHypSU h M hMJ hMdet
  have hβcol : ∀ x, M *ᵥ Pi.single x 1 = cc x • w' x := fun x => by
    have he : (Pi.single x (cc x * 1) : HypIndex r ε → K) = cc x • Pi.single x 1 := by
      rw [← Pi.single_smul, smul_eq_mul]
    rw [hMdef, ← mulVec_mulVec, diagonal_mulVec_single, he, mulVec_smul, hbcol]
  have hβinv : ∀ x, (((β⁻¹ : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w' x = (cc x)⁻¹ • Pi.single x 1 := by
    intro x
    have hwx : w' x = (cc x)⁻¹ • (M *ᵥ Pi.single x 1) := by
      rw [hβcol, smul_smul, inv_mul_cancel₀ (hcc0 x), one_smul]
    rw [hwx, mulVec_smul, ← hβmat, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, Units.val_one, one_mulVec]
  have hβF : ∀ i ≤ 2 * r + ε, β • posFlag r ε K i = posFlag r ε K i := by
    intro i hi
    rw [hypSU_smul_eq_map, hβmat]
    conv_lhs => rw [posFlag_eq_span, map_span, Set.image_image]
    simp only [mulVecLin_apply, hβcol]
    rw [span_image_smul hcc0, ← hFw' i hi]
  have hβB : β ∈ hypBorel h r ε := by
    rw [mem_hypBorel]
    intro i _ hir
    rw [hypFlag_eq_posFlag h hε (by omega)]
    exact hβF i (by omega)
  set C : ℕ → Set (HypIndex r ε) := fun i => {x | w' x ∈ g • posFlag r ε K i} with hCdef
  have hGC : ∀ i ≤ 2 * r + ε, g • posFlag r ε K i = span K (w' '' C i) := by
    intro i hi
    obtain ⟨s, hs⟩ := hGw' i hi
    have hs' : g • posFlag r ε K i = span K (w' '' s) := hs
    have hCs : C i = s := Set.ext fun x => by
      change w' x ∈ g • posFlag r ε K i ↔ x ∈ s
      rw [hs']
      exact w'.self_mem_span_image
    rw [hCs, hs']
  have hh : ∀ i ≤ 2 * r + ε, (β⁻¹ * g) • posFlag r ε K i =
      span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C i) := by
    intro i hi
    calc (β⁻¹ * g) • posFlag r ε K i = β⁻¹ • (g • posFlag r ε K i) := mul_smul _ _ _
      _ = β⁻¹ • span K (w' '' C i) := by rw [hGC i hi]
      _ = _ := by
        rw [hypSU_smul_eq_map, map_span, Set.image_image]
        simp only [mulVecLin_apply, hβinv]
        exact span_image_smul (fun x => inv_ne_zero (hcc0 x)) _
  have hfin : ∀ i ≤ 2 * r + ε,
      finrank K (span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C i)) = i := by
    intro i hi
    rw [← hh i hi]
    exact (finrank_smul _ _).trans (finrank_posFlag' hi)
  have hmemC : ∀ (i : ℕ) (x : HypIndex r ε), (Pi.single x (1 : K) : HypIndex r ε → K) ∈
      span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C i) ↔ x ∈ C i := by
    intro i x
    have := (Pi.basisFun K (HypIndex r ε)).self_mem_span_image (i := x) (s := C i)
    have hfun : ⇑(Pi.basisFun K (HypIndex r ε)) = fun x => (Pi.single x (1 : K) :
        HypIndex r ε → K) := funext fun x => Pi.basisFun_apply K _ x
    rwa [hfun] at this
  have hCmono : ∀ {i i' : ℕ}, i ≤ i' → C i ⊆ C i' := fun hii' x hx =>
    smul_le_smul_of_le g (posFlag_mono hii') hx
  have hiso : ∀ x ∈ C r, hypPartner x ∉ C r := by
    intro x hx hx'
    have htot : ∀ x ∈ span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C r),
        ∀ y ∈ span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C r),
          hypForm h r ε x y = 0 := by
      rw [← hh r (by omega)]
      exact smul_isotropic (β⁻¹ * g) (posFlag_isotropic (r := r) (ε := ε) h le_rfl)
    have h0 := htot _ ((hmemC r x).mpr hx) _ ((hmemC r _).mpr hx')
    change gramForm h (hypGram r ε K) _ _ = 0 at h0
    rw [gramForm_single, hypGram_apply, ite_eq_left rfl] at h0
    exact one_ne_zero h0
  have hnew : ∀ j : Fin r, ∃ x, x ∈ C (j + 1) ∧ x ∉ C j := by
    intro j
    by_contra! hsub
    have hle : span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C (j + 1)) ≤
        span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C j) :=
      span_mono (Set.image_mono fun x hx => hsub x hx)
    have := Submodule.finrank_mono hle
    rw [hfin (j + 1) (by omega), hfin j (by omega)] at this
    omega
  choose y hy using hnew
  have hyC : ∀ j : Fin r, y j ∈ C r := fun j => hCmono (by have := j.2; omega) (hy j).1
  have hyinj : Function.Injective y := by
    intro j j' hjj'
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h' := Fin.lt_def.mp hlt
      exact (hy j').2 (hjj' ▸ hCmono (i := j + 1) (i' := j') (by omega) (hy j).1)
    · have h' := Fin.lt_def.mp hgt
      exact (hy j).2 (hjj' ▸ hCmono (i := j' + 1) (i' := j) (by omega) (hy j').1)
  have hyl : ∀ j : Fin r, ∃ l : Fin r ⊕ Fin r, lineCoord (ε := ε) l = y j := fun j =>
    exists_lineCoord_of_ne fun e => hiso _ (hyC j) (by rw [e]; exact hyC j)
  choose l hl using hyl
  have hlinj : Function.Injective l := fun j j' e =>
    hyinj (by rw [← hl j, ← hl j', e])
  have hlswap : ∀ j j' : Fin r, l j ≠ (l j').swap := fun j j' e => by
    have : y j = hypPartner (y j') := by rw [← hl j, ← hl j', e, lineCoord_swap]
    exact hiso _ (hyC j') (this ▸ hyC j)
  set wf : Fin r ⊕ Fin r → Fin r ⊕ Fin r := Sum.elim l fun j => (l j).swap with hwf
  have hwfinj : Function.Injective wf := by
    rintro (j | j) (j' | j') e <;> simp only [hwf, Sum.elim_inl, Sum.elim_inr] at e
    · exact congrArg Sum.inl (hlinj e)
    · exact absurd e (hlswap j j')
    · exact absurd e.symm (hlswap j' j)
    · exact congrArg Sum.inr (hlinj (SymplecticHigher.swap_injective' e))
  set w : Equiv.Perm (Fin r ⊕ Fin r) :=
    Equiv.ofBijective wf (Finite.injective_iff_bijective.mp hwfinj) with hwdef
  have hw : w ∈ hypWeyl r := by
    rintro (j | j)
    · rfl
    · exact (Sum.swap_swap _).symm
  have hwl : ∀ j : Fin r, weylPerm (ε := ε) w (.inl j) = y j := fun j => by
    rw [weylPerm_inl, ← hl j]
    rfl
  have hwF : ∀ i ≤ r, weylElt (ε := ε) h hc hc0 hw • posFlag r ε K i =
      span K ((fun x => (Pi.single x (1 : K) : HypIndex r ε → K)) '' C i) := by
    intro i hi
    refine eq_of_le_of_finrank_eq ?_ ?_
    · rw [hypSU_smul_eq_map, posFlag_eq_span, map_span, span_le]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      obtain ⟨j, rfl, hj⟩ := exists_inl_of_fullPos_lt hi hx
      rw [mulVecLin_apply, coe_weylElt, weylMat_mulVec_single, hwl]
      exact smul_mem _ _ ((hmemC i _).mpr (hCmono (by omega) (hy j).1))
    · exact ((finrank_smul _ _).trans (finrank_posFlag' (by omega))).trans
        (hfin i (by omega)).symm
  have hrest : (weylElt (ε := ε) h hc hc0 hw)⁻¹ * (β⁻¹ * g) ∈ hypBorel h r ε := by
    rw [mem_hypBorel]
    intro i _ hir
    rw [hypFlag_eq_posFlag h hε (by omega)]
    calc ((weylElt (ε := ε) h hc hc0 hw)⁻¹ * (β⁻¹ * g)) • posFlag r ε K i =
        (weylElt (ε := ε) h hc hc0 hw)⁻¹ • ((β⁻¹ * g) • posFlag r ε K i) := mul_smul _ _ _
      _ = posFlag r ε K i := by rw [hh i (by omega), ← hwF i hir, inv_smul_smul]
  refine ⟨⟨w, hw⟩, β, hβB, _, hrest, ?_⟩
  group

@[expose] noncomputable def uFlagPerm (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    Equiv.Perm (Fin (2 * r + ε)) :=
  fullPosEquiv.symm.trans ((weylPerm w).trans fullPosEquiv)

theorem uFlagPerm_injective : Function.Injective (uFlagPerm (r := r) (ε := ε)) := by
  intro w w' hww'
  ext x
  have := congrArg (fun σ : Equiv.Perm (Fin (2 * r + ε)) => σ (fullPosEquiv (lineCoord x))) hww'
  simp only [uFlagPerm, Equiv.trans_apply, Equiv.symm_apply_apply, weylPerm_lineCoord] at this
  exact lineCoord_injective (fullPosEquiv.injective this)

theorem reindex_weylMat (c : K) (w : Equiv.Perm (Fin r ⊕ Fin r)) :
    reindex fullPosEquiv fullPosEquiv (weylMat (ε := ε) h c w) =
      LinearFlag.permMatrix (2 * r + ε) K (uFlagPerm w) *
        diagonal fun a => weylCoeff h c w (fullPosEquiv.symm a) := by
  ext a b
  rw [reindex_apply, submatrix_apply, weylMat, signedPerm_apply, mul_diagonal,
    LinearFlag.permMatrix_apply]
  have hiff : fullPosEquiv.symm a = weylPerm w (fullPosEquiv.symm b) ↔ a = uFlagPerm w b := by
    simp only [uFlagPerm, Equiv.trans_apply]
    constructor
    · intro e
      rw [← e, Equiv.apply_symm_apply]
    · rintro rfl
      rw [Equiv.symm_apply_apply]
  by_cases hab : a = uFlagPerm w b
  · rw [ite_eq_left (hiff.mpr hab), ite_eq_left hab, one_mul]
  · rw [ite_eq_right (mt hiff.mp hab), ite_eq_right hab, zero_mul]

theorem cornerRank_weylMat {c : K} (hc0 : c ≠ 0) (w : Equiv.Perm (Fin r ⊕ Fin r)) (i j : ℕ) :
    LinearFlag.cornerRank (reindex fullPosEquiv fullPosEquiv (weylMat (ε := ε) h c w)) i j =
      LinearFlag.cornerCount (uFlagPerm (ε := ε) w) i j := by
  rw [reindex_weylMat, LinearFlag.cornerRank_mul_right, LinearFlag.cornerRank_permMatrix]
  · exact fun a b hab => diagonal_apply_ne _ (ne_of_gt hab)
  · intro a
    rw [diagonal_apply_eq]
    have hbc : h.bar c ≠ 0 := (map_ne_zero h.bar).mpr hc0
    generalize fullPosEquiv.symm a = x
    rcases x with i | k | i
    · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hc0]
    · simp [weylCoeff]
    · rcases hwi : w (.inl i) with j | j <;> simp [weylCoeff, hwi, hbc]

theorem reindex_of_mem_hypBorel (hε : ε ≤ 1) {b : hypSU h r ε} (hb : b ∈ hypBorel h r ε) :
    (reindex fullPosEquiv fullPosEquiv ((b : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)).IsUpperTriangular ∧
    ∀ a, reindex fullPosEquiv fullPosEquiv ((b : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) a a ≠ 0 := by
  have hbt := (mem_hypBorel_iff_blockTriangular h hε b).mp hb
  have htri : (reindex fullPosEquiv fullPosEquiv ((b : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)).IsUpperTriangular := by
    intro a a' haa'
    rw [reindex_apply, submatrix_apply]
    apply hbt
    rw [fullPos_fullPosEquiv_symm, fullPos_fullPosEquiv_symm]
    exact haa'
  refine ⟨htri, fun a => ?_⟩
  have hdet : (reindex fullPosEquiv fullPosEquiv ((b : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)).det ≠ 0 := by
    rw [det_reindex_self]
    exact ((b : GL (HypIndex r ε) K).isUnit.map detMonoidHom).ne_zero
  rw [det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet a (Finset.mem_univ a)

theorem reindex_mul_reindex' {n : Type*} [Fintype n] [DecidableEq n]
    (e : HypIndex r ε ≃ n) (A B : Matrix (HypIndex r ε) (HypIndex r ε) K) :
    reindex e e (A * B) = reindex e e A * reindex e e B := by
  rw [reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]

theorem cornerRank_of_mem_uBruhatCell (hε : ε ≤ 1) {c : K} (hc : c ∈ h.traceZero)
    (hc0 : c ≠ 0) {g : hypSU h r ε} {w : hypWeyl r} (hg : g ∈ uBruhatCell h hc hc0 w)
    (i j : ℕ) :
    LinearFlag.cornerRank (reindex fullPosEquiv fullPosEquiv ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K)) i j =
      LinearFlag.cornerCount (uFlagPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r))) i j := by
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
  obtain ⟨h1, h1'⟩ := reindex_of_mem_hypBorel h hε hb₁
  obtain ⟨h2, h2'⟩ := reindex_of_mem_hypBorel h hε hb₂
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [reindex_mul_reindex', reindex_mul_reindex', LinearFlag.cornerRank_mul_right h2 h2',
    LinearFlag.cornerRank_mul_left h1 h1', coe_weylElt, cornerRank_weylMat h hc0]

theorem unitary_bruhat (hε : ε ≤ 1) {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    (∀ g : hypSU h r ε, ∃ w : hypWeyl r, g ∈ uBruhatCell h hc hc0 w) ∧
    (∀ (g : hypSU h r ε) (w w' : hypWeyl r), g ∈ uBruhatCell h hc hc0 w →
      g ∈ uBruhatCell h hc hc0 w' → w = w') ∧
    (∀ (g : hypSU h r ε) (w : hypWeyl r), g ∈ uBruhatCell h hc hc0 w ↔
      ∀ i j : ℕ, 1 ≤ i → i ≤ 2 * r + ε → 1 ≤ j → j ≤ 2 * r + ε →
        LinearFlag.cornerRank (reindex fullPosEquiv fullPosEquiv ((g : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) i j =
          LinearFlag.cornerCount (uFlagPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r))) i j) ∧
    ∀ {c' : K} (hc' : c' ∈ h.traceZero) (hc0' : c' ≠ 0) (g : hypSU h r ε) (w : hypWeyl r),
      g ∈ uBruhatCell h hc hc0 w ↔ g ∈ uBruhatCell h hc' hc0' w := by
  have hcrit : ∀ {c : K} (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) (g : hypSU h r ε)
      (w : hypWeyl r), g ∈ uBruhatCell h hc hc0 w ↔
      ∀ i j : ℕ, 1 ≤ i → i ≤ 2 * r + ε → 1 ≤ j → j ≤ 2 * r + ε →
        LinearFlag.cornerRank (reindex fullPosEquiv fullPosEquiv ((g : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K)) i j =
          LinearFlag.cornerCount (uFlagPerm (ε := ε) (w : Equiv.Perm (Fin r ⊕ Fin r))) i j := by
    intro c hc hc0 g w
    refine ⟨fun hg i j _ _ _ _ => cornerRank_of_mem_uBruhatCell h hε hc hc0 hg i j,
      fun hrank => ?_⟩
    obtain ⟨w', hw'⟩ := exists_mem_uBruhatCell h hε hc hc0 g
    have : w = w' := by
      apply Subtype.ext
      apply uFlagPerm_injective (ε := ε)
      exact LinearFlag.eq_of_cornerCount_eq fun i j hi hin hj hjn =>
        (hrank i j hi hin hj hjn).symm.trans
          (cornerRank_of_mem_uBruhatCell h hε hc hc0 hw' i j)
    rw [this]
    exact hw'
  refine ⟨exists_mem_uBruhatCell h hε hc hc0, fun g w w' hw hw' => ?_, hcrit hc hc0,
    fun hc' hc0' g w => (hcrit hc hc0 g w).trans (hcrit hc' hc0' g w).symm⟩
  apply Subtype.ext
  apply uFlagPerm_injective (ε := ε)
  exact LinearFlag.eq_of_cornerCount_eq fun i j _ _ _ _ =>
    (cornerRank_of_mem_uBruhatCell h hε hc hc0 hw i j).symm.trans
      (cornerRank_of_mem_uBruhatCell h hε hc hc0 hw' i j)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
