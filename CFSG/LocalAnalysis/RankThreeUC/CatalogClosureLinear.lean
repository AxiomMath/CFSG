module

public import CFSG.LocalAnalysis.RankThreeUC.CatalogClosure
public import CFSG.LargeExtraspecial.A2ModSL
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

namespace SLClosure

open Matrix Subgroup CFSG.LargeExtraspecial.A2Mod

variable {n : ℕ} {K : Type*} [Field K]

theorem coe_mul' (a b : SpecialLinearGroup (Fin n) K) :
    ((a * b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (a : Matrix (Fin n) (Fin n) K) * (b : Matrix (Fin n) (Fin n) K) := rfl

theorem coe_one' : ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := rfl

theorem smul_eq_mulVec' (s : SpecialLinearGroup (Fin n) K) (x : Fin n → K) :
    s • x = (s : Matrix (Fin n) (Fin n) K) *ᵥ x := rfl

theorem mulVec_inv_mulVec' (a : SpecialLinearGroup (Fin n) K) (x : Fin n → K) :
    (a : Matrix (Fin n) (Fin n) K) *ᵥ ((a⁻¹ : SpecialLinearGroup (Fin n) K) *ᵥ x) = x := by
  rw [mulVec_mulVec, sl_coe_mul_coe_inv, one_mulVec]

theorem inv_mulVec_mulVec' (a : SpecialLinearGroup (Fin n) K) (x : Fin n → K) :
    ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((a : Matrix (Fin n) (Fin n) K) *ᵥ x) = x := by
  rw [mulVec_mulVec, sl_coe_inv_mul_coe, one_mulVec]

@[expose] def stab (U : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ U ↔ x ∈ U}
  mul_mem' := by
    intro a b ha hb x
    rw [coe_mul', ← mulVec_mulVec, ha, hb]
  one_mem' := by intro x; simp
  inv_mem' := by
    intro a ha x
    have h := ha ((a⁻¹ : SpecialLinearGroup (Fin n) K) *ᵥ x)
    rw [mulVec_inv_mulVec'] at h
    exact h.symm

@[expose] def rad (U : Submodule K (Fin n → K)) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (∀ u ∈ U, (g : Matrix (Fin n) (Fin n) K) *ᵥ u = u) ∧
    ∀ x, (g : Matrix (Fin n) (Fin n) K) *ᵥ x - x ∈ U}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun u hu => ?_, fun x => ?_⟩
    · rw [coe_mul', ← mulVec_mulVec, hb1 u hu, ha1 u hu]
    · have h1 := ha2 ((b : Matrix (Fin n) (Fin n) K) *ᵥ x)
      have h2 := hb2 x
      have h3 := U.add_mem h1 h2
      rw [coe_mul', ← mulVec_mulVec]
      simpa [sub_add_sub_cancel] using h3
  one_mem' := ⟨fun u _ => by simp, fun x => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨fun u hu => ?_, fun x => ?_⟩
    · have := ha1 u hu
      calc ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u
          = ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            ((a : Matrix (Fin n) (Fin n) K) *ᵥ u) := by rw [this]
        _ = u := inv_mulVec_mulVec' a u
    · have h := ha2 ((a⁻¹ : SpecialLinearGroup (Fin n) K) *ᵥ x)
      rw [mulVec_inv_mulVec'] at h
      have := U.neg_mem h
      simpa using this

theorem mulVec_mul_eq (a b : SpecialLinearGroup (Fin n) K) (x : Fin n → K) :
    ((a * b : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      (a : Matrix (Fin n) (Fin n) K) *ᵥ ((b : Matrix (Fin n) (Fin n) K) *ᵥ x) := by
  rw [coe_mul', mulVec_mulVec]

theorem eq_of_mulVec_eq {a b : SpecialLinearGroup (Fin n) K}
    (h : ∀ x, (a : Matrix (Fin n) (Fin n) K) *ᵥ x = (b : Matrix (Fin n) (Fin n) K) *ᵥ x) :
    a = b := by
  refine Subtype.ext (Matrix.ext_of_mulVec_single fun i => h _)

theorem rad_mul_self [CharP K 2] {U : Submodule K (Fin n → K)} {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ rad U) : g * g = 1 := by
  obtain ⟨h1, h2⟩ := hg
  refine eq_of_mulVec_eq fun x => ?_
  rw [mulVec_mul_eq, coe_one', one_mulVec]
  have hd := h2 x
  have hgd := h1 _ hd
  have e1 : (g : Matrix (Fin n) (Fin n) K) *ᵥ x =
      x + ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) := by abel
  calc (g : Matrix (Fin n) (Fin n) K) *ᵥ ((g : Matrix (Fin n) (Fin n) K) *ᵥ x)
      = (g : Matrix (Fin n) (Fin n) K) *ᵥ (x + ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x)) := by
        rw [← e1]
    _ = (g : Matrix (Fin n) (Fin n) K) *ᵥ x + ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) := by
        rw [mulVec_add, hgd]
    _ = x := by
        have : ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) + ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x)
            = 0 := by
          ext i; simp [CharTwo.add_self_eq_zero]
        calc _ = x + (((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x) +
            ((g : Matrix (Fin n) (Fin n) K) *ᵥ x - x)) := by abel
          _ = x := by rw [this, add_zero]

theorem isPGroup_two_rad [CharP K 2] (U : Submodule K (Fin n → K)) : IsPGroup 2 (rad U) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simpa [pow_one, sq] using rad_mul_self g.2

theorem dual_apply_eq_dotProduct (f : Module.Dual K (Fin n → K)) (x : Fin n → K) :
    f x = (fun i => f (Pi.single i 1)) ⬝ᵥ x := by
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  simp only [dotProduct, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

theorem rad_ne_bot {U : Submodule K (Fin n → K)} (h0 : U ≠ ⊥) (h1 : U ≠ ⊤) : rad U ≠ ⊥ := by
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨f, hf0, hfU⟩ := Submodule.exists_le_ker_of_lt_top U (lt_top_iff_ne_top.2 h1)
  set φ : Fin n → K := fun i => f (Pi.single i 1) with hφ
  have hf : ∀ x, f x = φ ⬝ᵥ x := dual_apply_eq_dotProduct f
  have hφu : φ ⬝ᵥ u = 0 := by rw [← hf]; exact hfU huU
  have hφ0 : φ ≠ 0 := by
    intro h
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hf x, h]; simp
  obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (funext hcon)
  rw [Ne, Subgroup.eq_bot_iff_forall]
  intro hbot
  have hmem : tv u φ ∈ rad U := by
    refine ⟨fun u' hu' => ?_, fun x => ?_⟩
    · apply tv_mulVec_of_dotProduct_eq_zero
      rw [← hf]; exact hfU hu'
    · rw [tv_mulVec hφu x, add_sub_cancel_left]
      exact U.smul_mem _ huU
  have h1 := hbot _ hmem
  have h2 := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single i (1 : K))) h1
  simp only [tv_mulVec hφu, coe_one', one_mulVec] at h2
  have h3 : (φ ⬝ᵥ Pi.single i (1 : K)) • u = 0 := by
    have := h2; simpa using this
  simp [dotProduct_single] at h3
  rcases h3 with h3 | h3
  · exact hi h3
  · exact hu0 h3

theorem conj_mem_rad {U : Submodule K (Fin n → K)} {h g : SpecialLinearGroup (Fin n) K}
    (hh : h ∈ stab U) (hg : g ∈ rad U) : h * g * h⁻¹ ∈ rad U := by
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : h⁻¹ ∈ stab U := (stab U).inv_mem hh
  refine ⟨fun u hu => ?_, fun x => ?_⟩
  · have hu' : (h⁻¹ : SpecialLinearGroup (Fin n) K) *ᵥ u ∈ U := (hinv u).2 hu
    rw [mulVec_mul_eq, mulVec_mul_eq, hg1 _ hu', mulVec_inv_mulVec']
  · set y := ((h⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x with hy
    have e : (h : Matrix (Fin n) (Fin n) K) *ᵥ y = x := mulVec_inv_mulVec' h x
    have hmem : (h : Matrix (Fin n) (Fin n) K) *ᵥ
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ y - y) ∈ U := (hh _).2 (hg2 y)
    rw [mulVec_sub, e] at hmem
    rw [mulVec_mul_eq, mulVec_mul_eq]
    exact hmem

theorem stab_le_normalizer_rad (U : Submodule K (Fin n → K)) :
    stab U ≤ normalizer (rad U : Set (SpecialLinearGroup (Fin n) K)) := by
  intro h hh
  rw [mem_normalizer_iff]
  intro g
  refine ⟨conj_mem_rad hh, fun hg => ?_⟩
  have := conj_mem_rad ((stab U).inv_mem hh) hg
  simpa [mul_assoc] using this

theorem tv_mem_stab_of_mem {U : Submodule K (Fin n → K)} {v : Fin n → K} (hv : v ∈ U)
    (φ : Fin n → K) : tv v φ ∈ stab U := by
  intro x
  by_cases h : φ ⬝ᵥ v = 0
  · rw [tv_mulVec h]
    exact U.add_mem_iff_left (U.smul_mem _ hv)
  · rw [tv_of_dotProduct_ne_zero h, coe_one', one_mulVec]

theorem stab_sup_stab_eq_top {W W' : Submodule K (Fin n → K)} (hc : IsCompl W W') :
    stab W ⊔ stab W' = ⊤ := by
  set H := stab W ⊔ stab W' with hH
  rw [eq_top_iff, ← closure_transvectionSet (n := n) (F := K), Subgroup.closure_le]
  intro g hg
  obtain ⟨v, φ, hv, hφ, hφv, rfl⟩ := mem_transvectionSet.mp hg
  obtain ⟨v1, hv1, v2, hv2, hsum⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top : v ∈ W ⊔ W')
  by_cases h2 : v2 = 0
  ·
    subst h2
    rw [add_zero] at hsum
    subst hsum
    exact Subgroup.mem_sup_left (tv_mem_stab_of_mem hv1 φ)
  · have hv2W : v2 ∉ W := fun h => h2 (by
      have : v2 ∈ W ⊓ W' := ⟨h, hv2⟩
      rwa [hc.inf_eq_bot, Submodule.mem_bot] at this)
    obtain ⟨f, hf2, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv2W inferInstance
    set f' : Module.Dual K (Fin n → K) := (f v2)⁻¹ • f with hf'
    have hf'v2 : f' v2 = 1 := by simp [hf', hf2]
    have hf'W : ∀ w ∈ W, f' w = 0 := fun w hw => by
      have : f w = 0 := by
        have := Submodule.mem_map_of_mem (f := f) hw
        rwa [hfW, Submodule.mem_bot] at this
      simp [hf', this]
    set ψ : Fin n → K := fun i => f' (Pi.single i 1) with hψ
    have hψf : ∀ x, f' x = ψ ⬝ᵥ x := dual_apply_eq_dotProduct f'
    have hψv1 : ψ ⬝ᵥ (-v1) = 0 := by
      rw [dotProduct_neg, ← hψf, hf'W v1 hv1, neg_zero]
    set h : SpecialLinearGroup (Fin n) K := tv (-v1) ψ with hh
    have hhW : h ∈ stab W := tv_mem_stab_of_mem (W.neg_mem hv1) ψ
    have hhv : (h : Matrix (Fin n) (Fin n) K) *ᵥ v = v2 := by
      rw [hh, tv_mulVec hψv1, ← hsum, ← hψf, map_add, hf'W v1 hv1, hf'v2]
      simp
    have hconj := conj_tv h v φ
    rw [hhv] at hconj
    have hmem : h * tv v φ * h⁻¹ ∈ stab W' := by
      rw [hconj]; exact tv_mem_stab_of_mem hv2 _
    have hmemH : h * tv v φ * h⁻¹ ∈ H := Subgroup.mem_sup_right hmem
    have hhH : h ∈ H := Subgroup.mem_sup_left hhW
    have := H.mul_mem (H.mul_mem (H.inv_mem hhH) hmemH) hhH
    simpa [mul_assoc] using this

@[expose] def fixSub (S : Subgroup (SpecialLinearGroup (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {x | ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) K) *ᵥ x = x}
  add_mem' := by
    intro a b ha hb s hs
    rw [mulVec_add, ha s hs, hb s hs]
  zero_mem' := by intro s _; simp
  smul_mem' := by
    intro c a ha s hs
    rw [mulVec_smul, ha s hs]

theorem mem_fixSub {S : Subgroup (SpecialLinearGroup (Fin n) K)} {x : Fin n → K} :
    x ∈ fixSub S ↔ ∀ s ∈ S, (s : Matrix (Fin n) (Fin n) K) *ᵥ x = x := Iff.rfl

theorem fixSub_ne_top {S : Subgroup (SpecialLinearGroup (Fin n) K)} (hS : S ≠ ⊥) :
    fixSub S ≠ ⊤ := by
  intro htop
  apply hS
  rw [Subgroup.eq_bot_iff_forall]
  intro s hs
  refine eq_of_mulVec_eq fun x => ?_
  rw [(mem_fixSub.1 (htop ▸ Submodule.mem_top : x ∈ fixSub S)) s hs, coe_one',
    one_mulVec]

theorem fixSub_ne_bot [Finite K] [CharP K 2] {S : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hS : S ≠ ⊥) (hS2 : IsPGroup 2 S) : fixSub S ≠ ⊥ := by
  intro hbot
  have hn : n ≠ 0 := by
    rintro rfl
    apply hS
    have : Subsingleton (SpecialLinearGroup (Fin 0) K) := inferInstance
    exact Subgroup.eq_bot_of_subsingleton S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hS2.card_modEq_card_fixedPoints (Fin n → K)
  have hfix : MulAction.fixedPoints S (Fin n → K) = {0} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro h
      have : x ∈ fixSub S := fun s hs => by
        have := h ⟨s, hs⟩
        rwa [Subgroup.smul_def, smul_eq_mulVec'] at this
      rw [hbot] at this
      simpa using this
    · rintro rfl ⟨s, hs⟩
      rw [Subgroup.smul_def, smul_eq_mulVec', mulVec_zero]
  have hcard1 : Nat.card (MulAction.fixedPoints S (Fin n → K)) = 1 := by
    rw [hfix]; simp
  have heven : 2 ∣ Nat.card (Fin n → K) := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, hf, ← pow_mul]
    exact dvd_pow_self 2 (Nat.mul_ne_zero f.ne_zero hn)
  rw [hcard1] at hmod
  obtain ⟨k, hk⟩ := heven
  unfold Nat.ModEq at hmod
  omega

@[expose] def repOf (E : Subgroup (SpecialLinearGroup (Fin n) K)) : Representation K E (Fin n → K) where
  toFun e := Matrix.mulVecLin ((e : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  map_one' := by
    ext x; simp
  map_mul' := by
    intro a b
    ext x
    simp

theorem repOf_apply (E : Subgroup (SpecialLinearGroup (Fin n) K)) (e : E) (x : Fin n → K) :
    repOf E e x = ((e : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x := rfl

theorem exists_invariant_compl [Finite K] [CharP K 2]
    (E : Subgroup (SpecialLinearGroup (Fin n) K)) (hE : Odd (Nat.card E))
    (W : Submodule K (Fin n → K))
    (hW : ∀ e ∈ E, ∀ x ∈ W, (e : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W) :
    ∃ W' : Submodule K (Fin n → K), IsCompl W W' ∧
      ∀ e ∈ E, ∀ x ∈ W', (e : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ W' := by
  have : Finite E := inferInstance
  have : NeZero (Nat.card E : K) := ⟨by
    intro h
    have := (CharP.cast_eq_zero_iff K 2 (Nat.card E)).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)⟩
  let σ : Subrepresentation (repOf E) := ⟨W, fun g v hv => by
    rw [repOf_apply]; exact hW g g.2 v hv⟩
  obtain ⟨σ', hσ'⟩ := ComplementedLattice.exists_isCompl σ
  refine ⟨σ'.toSubmodule, ⟨?_, ?_⟩, fun e he x hx => ?_⟩
  ·
    have h := hσ'.1
    rw [disjoint_iff] at h ⊢
    have := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_inf] at this
    exact this
  · have h := hσ'.2
    rw [codisjoint_iff] at h ⊢
    have := congrArg Subrepresentation.toSubmodule h
    rw [Subrepresentation.toSubmodule_sup] at this
    exact this
  · have := σ'.apply_mem_toSubmodule ⟨e, he⟩ hx
    rwa [repOf_apply] at this

theorem stab_le_twoLocalClosure [CharP K 2] {E : Subgroup (SpecialLinearGroup (Fin n) K)}
    {U : Submodule K (Fin n → K)} (h0 : U ≠ ⊥) (h1 : U ≠ ⊤) (hE : E ≤ stab U) :
    stab U ≤ twoLocalClosure E :=
  le_iSup₂_of_le (normalizer (rad U : Set (SpecialLinearGroup (Fin n) K)))
    ⟨⟨rad U, rad_ne_bot h0 h1, isPGroup_two_rad U, rfl⟩, hE.trans (stab_le_normalizer_rad U)⟩
    (stab_le_normalizer_rad U)

theorem mem_stab_of_invariant {E : Subgroup (SpecialLinearGroup (Fin n) K)}
    {U : Submodule K (Fin n → K)}
    (hU : ∀ e ∈ E, ∀ x ∈ U, (e : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ U) : E ≤ stab U := by
  intro e he x
  refine ⟨fun hx => ?_, fun hx => hU e he x hx⟩
  have := hU (e⁻¹) (E.inv_mem he) _ hx
  rwa [inv_mulVec_mulVec'] at this

theorem twoLocalClosure_eq_top_of_normalizes [Finite K] [CharP K 2]
    (E S0 : Subgroup (SpecialLinearGroup (Fin n) K)) (hE : Odd (Nat.card E)) (hS0 : S0 ≠ ⊥)
    (hS02 : IsPGroup 2 S0) (hEN : E ≤ normalizer (S0 : Set (SpecialLinearGroup (Fin n) K))) :
    twoLocalClosure E = ⊤ := by
  have hWbot : fixSub S0 ≠ ⊥ := fixSub_ne_bot hS0 hS02
  have hWtop : fixSub S0 ≠ ⊤ := fixSub_ne_top hS0
  have hWinv : ∀ e ∈ E, ∀ x ∈ fixSub S0, (e : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ fixSub S0 := by
    intro e he x hx s hs
    have hn : e⁻¹ ∈ normalizer (S0 : Set (SpecialLinearGroup (Fin n) K)) :=
      (normalizer (S0 : Set (SpecialLinearGroup (Fin n) K))).inv_mem (hEN he)
    have hs' : e⁻¹ * s * e⁻¹⁻¹ ∈ S0 := (mem_normalizer_iff.1 hn s).1 hs
    have h1 := hx _ hs'
    simp only [inv_inv] at h1
    rw [mulVec_mul_eq, mulVec_mul_eq] at h1
    calc (s : Matrix (Fin n) (Fin n) K) *ᵥ ((e : Matrix (Fin n) (Fin n) K) *ᵥ x)
        = (e : Matrix (Fin n) (Fin n) K) *ᵥ (((e⁻¹ : SpecialLinearGroup (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ ((s : Matrix (Fin n) (Fin n) K) *ᵥ
              ((e : Matrix (Fin n) (Fin n) K) *ᵥ x))) := (mulVec_inv_mulVec' e _).symm
      _ = (e : Matrix (Fin n) (Fin n) K) *ᵥ x := by rw [h1]
  obtain ⟨W', hc, hW'⟩ := exists_invariant_compl E hE (fixSub S0) hWinv
  have hW'bot : W' ≠ ⊥ := fun h => hWtop (by
    have := hc.sup_eq_top; rwa [h, sup_bot_eq] at this)
  have hW'top : W' ≠ ⊤ := fun h => hWbot (by
    have := hc.inf_eq_bot; rwa [h, inf_top_eq] at this)
  have h1 := stab_le_twoLocalClosure hWbot hWtop (mem_stab_of_invariant hWinv)
  have h2 := stab_le_twoLocalClosure hW'bot hW'top (mem_stab_of_invariant hW')
  rw [eq_top_iff, ← stab_sup_stab_eq_top hc]
  exact sup_le h1 h2

end SLClosure

open Matrix in
theorem center_noInvolution {n : ℕ} {K : Type*} [Field K] [CharP K 2]
    (z : SpecialLinearGroup (Fin n) K) (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (h2 : z ^ 2 = 1) : z = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have h2' : (z : Matrix (Fin n) (Fin n) K) * (z : Matrix (Fin n) (Fin n) K) = 1 := by
    have := congrArg (fun w : SpecialLinearGroup (Fin n) K => (w : Matrix (Fin n) (Fin n) K)) h2
    simpa [pow_two] using this
  have hzm : (z : Matrix (Fin n) (Fin n) K) = Matrix.scalar (Fin n) r := hr.symm
  rw [hzm] at h2'
  have h3 := congrFun (congrFun h2' ⟨0, hn⟩) ⟨0, hn⟩
  simp [Matrix.scalar_apply] at h3
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (r - 1) ^ 2 = 0 := by linear_combination h3 + (1 - r) * h2K
  have h5 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4)
  apply Subtype.ext
  rw [hzm, h5]
  simp

theorem not_rankThreeUC_of_SL_quotient {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (φ : Matrix.SpecialLinearGroup (Fin n) K →* G) (hφ : Function.Surjective φ)
    (hc : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) : ¬ rankThreeUC G := by
  intro hUC
  obtain ⟨p, hp⟩ := sigmaA_nonempty_of_evenRank_three hS.rank
  have hprime : p.Prime := sigmaA_prime p hp
  have hp2 : p ≠ 2 := (sigmaA_odd p hp)
  have h3 : rankThreeLocalRank p G = 3 := sigmaA_local_rank_three hS.rank p hp
  obtain ⟨H, hH2, hHr⟩ := rankThreeLocalRank_attained p (by rw [h3]; norm_num)
  obtain ⟨E, hEH, hEab, hEcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_attained p hprime H
  rw [hHr, h3] at hEcard
  obtain ⟨S0, hS0bot, hS02, hHeq⟩ := hH2
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have := hEab.2 x x.2
    apply Subtype.ext
    simpa using this⟩
  have hE2 : 2 ≤ CFSG.Open.pRank p E := by
    have := CFSG.SectionRank.le_pRank hprime.one_lt (le_refl E) hEab hEcard
    omega
  refine twoLocalClosure_ne_top hS hUC hp hEp hE2 ?_
  have hker : ∀ z ∈ φ.ker, z ^ 2 = 1 → z = 1 := fun z hz h2 =>
    center_noInvolution z (hc hz) h2
  have hEodd : Odd (Nat.card E) := by
    rw [hEcard]
    exact (hprime.odd_of_ne_two hp2).pow
  have hEN : E ≤ normalizer (S0 : Set G) := hHeq ▸ hEH
  obtain ⟨P, hP, hP2, hEP⟩ := exists_normalized_two_subgroup φ hφ hc hS0bot hS02 hEN
  have hcl := SLClosure.twoLocalClosure_eq_top_of_normalizes (E.comap φ) P
    (odd_card_comap φ hker hEodd) hP hP2 hEP
  have hle := map_twoLocalClosure_le_of_ker φ hker (E.comap φ)
  rw [hcl, Subgroup.map_top, MonoidHom.range_eq_top.2 hφ,
    Subgroup.map_comap_eq_self_of_surjective hφ] at hle
  exact top_le_iff.mp hle

theorem not_rankThreeUC_of_PSL {G : Type} [Group G] [Finite G]
    (hS : Standing G) {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K) : ¬ rankThreeUC G := by
  refine not_rankThreeUC_of_SL_quotient hS
    (e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))))
    (e.symm.surjective.comp (QuotientGroup.mk'_surjective _)) ?_
  intro z hz
  have h1 : e.symm (QuotientGroup.mk z : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = 1 :=
    MonoidHom.mem_ker.mp hz
  have h2 : (QuotientGroup.mk z : Matrix.ProjectiveSpecialLinearGroup (Fin n) K) = 1 :=
    (map_eq_one_iff _ e.symm.injective).mp h1
  exact (QuotientGroup.eq_one_iff z).mp h2

end CFSG.LocalAnalysis.RankThreeUC
