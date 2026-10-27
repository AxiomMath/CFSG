module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AUniDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly Matrix
open scoped MatrixGroups commutatorElement


variable {p n d : ℕ} {F : Type} [Field F] [Finite F]

private def uniForm (n : ℕ) (u v : Fin d → F) : F := ∑ i, u i ^ (2 ^ n) * v i

private theorem charP_two_of_uniArith (h : UniArith p n d F) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hn : 1 ≤ n := h.2.2.2.2.1
  have hcard : Nat.card F = (2 ^ n) ^ 2 := h.2.2.2.1
  have hring : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hcard]
    have h2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by rw [← pow_mul]; ring_nf
    rw [h2]
    have hdvd : 2 ∣ 2 ^ (2 * n) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (show 2 * n ≠ 0 from
        Nat.mul_ne_zero (by norm_num) (Nat.pos_iff_ne_zero.mp hn))
      exact ⟨2 ^ k, by rw [hk, pow_succ, mul_comm]⟩
    exact Nat.dvd_iff_mod_eq_zero.mp hdvd
  rw [← hring]
  exact ringChar.charP F

private def unitaryPreservers (n d : ℕ) (F : Type) [Field F] : Subgroup (GL (Fin d) F) where
  carrier := {A | ∀ u v : Fin d → F,
    uniForm n ((A : Matrix (Fin d) (Fin d) F) *ᵥ u) ((A : Matrix (Fin d) (Fin d) F) *ᵥ v) =
      uniForm n u v}
  mul_mem' := by
    rintro A B hA hB u v
    rw [Units.val_mul]
    rw [show ((A : Matrix (Fin d) (Fin d) F) * (B : Matrix (Fin d) (Fin d) F)) *ᵥ u =
        (A : Matrix (Fin d) (Fin d) F) *ᵥ ((B : Matrix (Fin d) (Fin d) F) *ᵥ u) from
      (Matrix.mulVec_mulVec u (A : Matrix (Fin d) (Fin d) F) (B : Matrix (Fin d) (Fin d) F)).symm]
    rw [show ((A : Matrix (Fin d) (Fin d) F) * (B : Matrix (Fin d) (Fin d) F)) *ᵥ v =
        (A : Matrix (Fin d) (Fin d) F) *ᵥ ((B : Matrix (Fin d) (Fin d) F) *ᵥ v) from
      (Matrix.mulVec_mulVec v (A : Matrix (Fin d) (Fin d) F) (B : Matrix (Fin d) (Fin d) F)).symm]
    rw [hA, hB]
  one_mem' := by
    intro u v
    rw [Units.val_one]
    rw [Matrix.one_mulVec, Matrix.one_mulVec]
  inv_mem' := by
    intro A hA u v
    have h := hA ((((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ u)
      ((((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ v)
    rw [show (A : Matrix (Fin d) (Fin d) F) *ᵥ
          ((((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ u) = u by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]] at h
    rw [show (A : Matrix (Fin d) (Fin d) F) *ᵥ
          ((((A⁻¹ : GL (Fin d) F)) : Matrix (Fin d) (Fin d) F) *ᵥ v) = v by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.one_mulVec]] at h
    exact h.symm

private lemma vecMul_eq_transpose_mulVec (M : Matrix (Fin d) (Fin d) F) (y : Fin d → F) :
    y ᵥ* M = Mᵀ *ᵥ y := by
  conv_lhs => rw [← Matrix.transpose_transpose M]
  rw [Matrix.vecMul_transpose]

private theorem uniForm_eq_dotProduct [ExpChar F 2] (u v : Fin d → F) :
    uniForm n u v = ((iterateFrobenius F 2 n) ∘ u) ⬝ᵥ v := by
  simp only [uniForm, dotProduct, Function.comp_apply, iterateFrobenius_def]

private theorem unitary_mem_preservers [ExpChar F 2] {A : GL (Fin d) F}
    (hA : ((A : Matrix (Fin d) (Fin d) F).map (· ^ (2 ^ n)))ᵀ *
      (A : Matrix (Fin d) (Fin d) F) = 1) :
    A ∈ unitaryPreservers n d F := by
  intro u v
  have hf : ∀ x : F, (iterateFrobenius F 2 n) x = x ^ (2 ^ n) :=
    fun x => iterateFrobenius_def (p := 2) (n := n) x
  have hA' : ((A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n))ᵀ *
      (A : Matrix (Fin d) (Fin d) F) = 1 := by
    rw [show (A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n) =
        (A : Matrix (Fin d) (Fin d) F).map (· ^ (2 ^ n)) from by
      ext i j; exact hf _]
    exact hA
  have hmap : (iterateFrobenius F 2 n) ∘ ((A : Matrix (Fin d) (Fin d) F) *ᵥ u) =
      (A : Matrix (Fin d) (Fin d) F).map (iterateFrobenius F 2 n) *ᵥ
        ((iterateFrobenius F 2 n) ∘ u) := by
    ext i
    simpa only [Function.comp_def, Matrix.map_apply] using
      RingHom.map_mulVec (iterateFrobenius F 2 n) (A : Matrix (Fin d) (Fin d) F) u i
  rw [uniForm_eq_dotProduct, uniForm_eq_dotProduct, hmap]
  rw [dotProduct_comm, dotProduct_mulVec, vecMul_eq_transpose_mulVec, dotProduct_comm]
  rw [Matrix.mulVec_mulVec, hA', Matrix.one_mulVec]

private theorem uniSU_le_unitaryPreservers [ExpChar F 2] :
    UniSU n d F ≤ unitaryPreservers n d F := by
  rw [show UniSU n d F = StatedSU d (2 ^ n) F from rfl,
    CFSG.PGLModel.statedSU_eq_closure_det]
  refine (Subgroup.closure_le _).2 ?_
  rintro A ⟨hdet, hunit⟩
  exact unitary_mem_preservers (n := n) (d := d) (F := F) hunit

private noncomputable def vecSupport (v : Fin d → F) : Finset (Fin d) := by
  classical exact Finset.univ.filter (fun i => v i ≠ 0)

private lemma mem_vecSupport {v : Fin d → F} {i : Fin d} :
    i ∈ vecSupport v ↔ v i ≠ 0 := by
  classical simp [vecSupport]

private lemma mulVec_apply_of_diag {a : Matrix (Fin d) (Fin d) F}
    (ha : ∀ i j : Fin d, i ≠ j → a i j = 0) (w : Fin d → F) (i : Fin d) :
    (a *ᵥ w) i = a i i * w i := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_single i ?_ ?_
  · intro j _ hj; rw [ha i j (Ne.symm hj), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private theorem exists_single_mem_of_invariant
    {A : Subgroup (GL (Fin d) F)}
    (hdiag : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (hdist : ∀ i j : Fin d, i ≠ j → ∃ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i ≠ (a : Matrix (Fin d) (Fin d) F) j j)
    {W : Submodule F (Fin d → F)}
    (hW : ∀ a ∈ A, ∀ w ∈ W, (a : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) :
    ∀ w ∈ W, w ≠ 0 → ∃ k, w k ≠ 0 ∧ (Pi.single k (1 : F) : Fin d → F) ∈ W := by
  intro w
  suffices H : ∀ m, ∀ w ∈ W, (vecSupport w).card = m → w ≠ 0 →
      ∃ k, w k ≠ 0 ∧ (Pi.single k (1 : F) : Fin d → F) ∈ W by
    intro hw hw0; exact H _ w hw rfl hw0
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw hcard hw0
    have hex : ∃ i, w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hw0 (funext fun i => hcon i)
    obtain ⟨k0, hk0⟩ := hex
    have hcardpos : 0 < (vecSupport w).card :=
      Finset.card_pos.mpr ⟨k0, mem_vecSupport.mpr hk0⟩
    by_cases hcard1 : (vecSupport w).card = 1
    · obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard1
      have hwk : w k ≠ 0 := by
        have : k ∈ vecSupport w := by rw [hk]; exact Finset.mem_singleton_self k
        exact mem_vecSupport.mp this
      refine ⟨k, hwk, ?_⟩
      have hweq : w = w k • (Pi.single k (1 : F) : Fin d → F) := by
        funext j
        by_cases hjk : j = k
        · subst hjk; simp
        · have hwj : w j = 0 := by
            have hj : j ∉ vecSupport w := by rw [hk]; simp [hjk]
            simpa [mem_vecSupport] using hj
          rw [Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_eq_mul, mul_zero, hwj]
      have hsingle : (w k)⁻¹ • w = (Pi.single k (1 : F) : Fin d → F) := by
        funext j
        by_cases hjk : j = k
        · subst hjk; rw [Pi.smul_apply, Pi.single_eq_same]; exact inv_mul_cancel₀ hwk
        · have hwj : w j = 0 := by
            have hj : j ∉ vecSupport w := by rw [hk]; simp [hjk]
            simpa [mem_vecSupport] using hj
          rw [Pi.smul_apply, Pi.single_eq_of_ne hjk, hwj, smul_zero]
      rw [← hsingle]
      exact Submodule.smul_mem _ _ hw
    · have hcard2 : 1 < (vecSupport w).card := by omega
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard2
      obtain ⟨a, ha, hdiff⟩ := hdist i j hij
      let v : Fin d → F := (a : Matrix (Fin d) (Fin d) F) *ᵥ w -
        (a : Matrix (Fin d) (Fin d) F) i i • w
      have hvx : ∀ x : Fin d, v x = ((a : Matrix (Fin d) (Fin d) F) x x -
          (a : Matrix (Fin d) (Fin d) F) i i) * w x := by
        intro x
        show ((a : Matrix (Fin d) (Fin d) F) *ᵥ w -
          (a : Matrix (Fin d) (Fin d) F) i i • w) x = _
        rw [Pi.sub_apply, mulVec_apply_of_diag (hdiag a ha) w x, Pi.smul_apply,
          smul_eq_mul, ← sub_mul]
      have hvW : v ∈ W := Submodule.sub_mem _ (hW a ha w hw) (Submodule.smul_mem _ _ hw)
      have hvj : v j ≠ 0 := by
        rw [hvx j]
        exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hdiff)) (mem_vecSupport.mp hj)
      have hvi : v i = 0 := by rw [hvx i, sub_self, zero_mul]
      have hsub : vecSupport v ⊆ vecSupport w := by
        intro x hx
        rw [mem_vecSupport] at hx ⊢
        rw [hvx x] at hx
        exact fun hw => hx (by rw [hw, mul_zero])
      have hssub : vecSupport v ⊂ vecSupport w := by
        refine (Finset.ssubset_iff_subset_ne).mpr ⟨hsub, ?_⟩
        intro hEq
        have : i ∈ vecSupport v := by rw [hEq]; exact hi
        rw [mem_vecSupport] at this
        exact this hvi
      have hlt : (vecSupport v).card < m := by
        rw [← hcard]; exact Finset.card_lt_card hssub
      have hvne : v ≠ 0 := by intro hv; exact hvj (by rw [hv]; rfl)
      obtain ⟨k, hvk, hkW⟩ := ih _ hlt v hvW rfl hvne
      refine ⟨k, ?_, hkW⟩
      intro hwk
      exact hvk (by rw [hvx k, hwk, mul_zero])


private theorem mem_span_single_of_invariant
    {A : Subgroup (GL (Fin d) F)}
    (hdiag : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (hdist : ∀ i j : Fin d, i ≠ j → ∃ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i ≠ (a : Matrix (Fin d) (Fin d) F) j j)
    {W : Submodule F (Fin d → F)}
    (hW : ∀ a ∈ A, ∀ w ∈ W, (a : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) :
    W ≤ Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) ''
      {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}) := by
  intro w hw
  suffices H : ∀ m, ∀ w ∈ W, (vecSupport w).card = m →
      w ∈ Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) ''
        {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}) by
    exact H _ w hw rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro w hw hcard
    by_cases hw0 : w = 0
    · subst hw0; exact Submodule.zero_mem _
    · obtain ⟨k, hkne, hkW⟩ := exists_single_mem_of_invariant hdiag hdist hW w hw hw0
      set w' : Fin d → F := w - w k • (Pi.single k (1 : F) : Fin d → F) with hw'def
      have hvi : w' k = 0 := by
        rw [hw'def, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, sub_self]
      have hsup : vecSupport w' ⊆ vecSupport w := by
        intro x hx
        rw [mem_vecSupport] at hx ⊢
        have hxk : x ≠ k := by
          intro h; subst h; exact hx hvi
        rw [hw'def, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hxk, smul_eq_mul,
          mul_zero, sub_zero] at hx
        exact hx
      have hssub : vecSupport w' ⊂ vecSupport w := by
        refine (Finset.ssubset_iff_subset_ne).mpr ⟨hsup, ?_⟩
        intro hEq
        have : k ∈ vecSupport w' := by rw [hEq]; exact mem_vecSupport.mpr hkne
        rw [mem_vecSupport] at this
        exact this hvi
      have hlt : (vecSupport w').card < m := by
        rw [← hcard]; exact Finset.card_lt_card hssub
      have hw'W : w' ∈ W := by
        rw [hw'def]
        exact Submodule.sub_mem _ hw (Submodule.smul_mem _ _ hkW)
      have hmem : w' ∈ Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) ''
          {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}) := ih _ hlt w' hw'W rfl
      have hsum : w' + w k • (Pi.single k (1 : F) : Fin d → F) = w := by
        rw [hw'def, sub_add_cancel]
      rw [← hsum]
      exact Submodule.add_mem _ hmem (Submodule.smul_mem _ _
        (Submodule.subset_span ⟨k, hkW, rfl⟩))

private theorem invariant_eq_span_single
    {A : Subgroup (GL (Fin d) F)}
    (hdiag : ∀ a ∈ A, ∀ i j : Fin d, i ≠ j → (a : Matrix (Fin d) (Fin d) F) i j = 0)
    (hdist : ∀ i j : Fin d, i ≠ j → ∃ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i ≠ (a : Matrix (Fin d) (Fin d) F) j j)
    {W : Submodule F (Fin d → F)}
    (hW : ∀ a ∈ A, ∀ w ∈ W, (a : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) :
    W = Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) ''
      {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}) := by
  refine le_antisymm (mem_span_single_of_invariant hdiag hdist hW) ?_
  rw [Submodule.span_le]
  rintro x ⟨i, hi, rfl⟩
  exact hi


private def evalZeroSubmodule (i : Fin d) : Submodule F (Fin d → F) :=
  { carrier := {x : Fin d → F | x i = 0}
    add_mem' := by intro a b ha hb; show (a + b) i = 0; rw [Pi.add_apply, ha, hb, add_zero]
    zero_mem' := rfl
    smul_mem' := by intro c a ha; show (c • a) i = 0; rw [Pi.smul_apply, ha, smul_zero] }

private lemma uniForm_single (n : ℕ) (i : Fin d) (u : Fin d → F) :
    uniForm n (Pi.single i (1 : F) : Fin d → F) u = u i := by
  rw [uniForm]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, one_pow, one_mul]
  · intro j _ hj
    have h : (Pi.single i (1 : F) : Fin d → F) j = 0 :=
      Pi.single_eq_of_ne (M := fun _ => F) hj (1 : F)
    rw [h, show (0 : F) ^ (2 ^ n) = 0 from
        zero_pow (pow_ne_zero n (by norm_num : (2:ℕ) ≠ 0)), zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma sum_single_eq_self (v : Fin d → F) :
    (∑ i, v i • (Pi.single i (1 : F) : Fin d → F)) = v := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro i _ hij
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hij), smul_eq_mul, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

private lemma span_single_univ_eq_top :
    Submodule.span F ((fun i : Fin d => (Pi.single i (1 : F) : Fin d → F)) '' Set.univ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [← sum_single_eq_self v]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, Set.mem_univ i, rfl⟩))

theorem uni_repeated_weight {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : UniArith p n d F)
    {Q : Type} [Group Q] {ψ : Q ≃* UniPSU n d F} {Bbar : Subgroup Q}
    {A : Subgroup (GL (Fin d) F)} (hfr : UniDiagFrame p n d F ψ Bbar A)
    (hhb : ∃ T : Subgroup Q, IsPGroup 2 T ∧ Bbar ≤ Subgroup.normalizer (T : Set Q) ∧
      (⁅T, Bbar⁆ : Subgroup Q) ≠ ⊥) :
    ∃ i j : Fin d, i ≠ j ∧ ∀ a ∈ A,
      (a : Matrix (Fin d) (Fin d) F) i i = (a : Matrix (Fin d) (Fin d) F) j j := by
  by_contra hcon
  push Not at hcon
  haveI : CharP F 2 := charP_two_of_uniArith h
  obtain ⟨hASU, _hAb, hdiag, hframe⟩ := hfr
  obtain ⟨T, hT2, hTN, hTc⟩ := hhb
  let Tψ : Subgroup (UniPSU n d F) := T.map ψ.toMonoidHom
  let R : Subgroup ↥(UniSU n d F) := Tψ.comap (UniMk n d F)
  have hTψ2 : IsPGroup 2 Tψ := hT2.map ψ.toMonoidHom
  have hmapnorm : (A.subgroupOf (UniSU n d F)).map (UniMk n d F) ≤
      Subgroup.normalizer Tψ := by
    rw [← hframe]
    exact (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map ψ.toMonoidHom)
  have hANR : A.subgroupOf (UniSU n d F) ≤ Subgroup.normalizer R := by
    have h1 : A.subgroupOf (UniSU n d F) ≤ (Subgroup.normalizer Tψ).comap (UniMk n d F) := by
      intro a ha
      rw [Subgroup.mem_comap]
      exact hmapnorm (Subgroup.mem_map_of_mem _ ha)
    exact h1.trans (Subgroup.le_normalizer_comap _)
  let f : R →* Tψ := (UniMk n d F).comp R.subtype |>.codRestrict Tψ (fun x => x.2)
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F)) y
    refine ⟨⟨g, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap]; rw [hg]; exact y.2
    · apply Subtype.ext
      exact hg
  have hscalar : (LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F) ≤
      Subgroup.center ↥(UniSU n d F) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxGL : (x : GL (Fin d) F) ∈ Subgroup.center (GL (Fin d) F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_center_iff.mp hxGL (y : GL (Fin d) F)
  have hkerπ : (UniMk n d F).ker = (LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F) := by
    show (QuotientGroup.mk' ((LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F))).ker = _
    exact QuotientGroup.ker_mk' _
  have hker : f.ker ≤ Subgroup.center R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hx1 : UniMk n d F (x : R) = 1 := by
      have := MonoidHom.mem_ker.mp hx
      exact congrArg Subtype.val this
    have hxZ : R.subtype x ∈ (LargeEvenScalars (Fin d) F).subgroupOf (UniSU n d F) := by
      rw [← hkerπ]
      exact hx1
    have hxc : R.subtype x ∈ Subgroup.center ↥(UniSU n d F) := hscalar hxZ
    exact Subgroup.mem_center_iff.mp hxc (R.subtype y)
  have hnil : Group.IsNilpotent R := by
    haveI : Group.IsNilpotent Tψ := IsPGroup.isNilpotent hTψ2
    exact Subgroup.isNilpotent_of_ker_le_center f hker
  haveI : Nonempty (Sylow 2 R) := by infer_instance
  let P : Sylow 2 R := Classical.arbitrary _
  have hPnormal : (P : Subgroup R).Normal := inferInstance
  have hPchar : (P : Subgroup R).Characteristic := Sylow.characteristic_of_normal P hPnormal
  let Psub : Subgroup ↥(UniSU n d F) := (P : Subgroup R).map R.subtype
  have hAP : A.subgroupOf (UniSU n d F) ≤ Subgroup.normalizer Psub := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    let φ : MulAut R := (Subgroup.normalizerMonoidHom R) ⟨a, hANR ha⟩
    have hφ : (P : Subgroup R).map φ.toMonoidHom = P :=
      (Subgroup.characteristic_iff_map_eq.mp hPchar) φ
    calc Psub.map (MulAut.conj a)
        = ((P : Subgroup R).map R.subtype).map (MulAut.conj a) := rfl
      _ = (P : Subgroup R).map ((MulAut.conj a).toMonoidHom.comp R.subtype) :=
            Subgroup.map_map ..
      _ = (P : Subgroup R).map (R.subtype.comp φ.toMonoidHom) := by
            congr 1
      _ = ((P : Subgroup R).map φ.toMonoidHom).map R.subtype :=
            (Subgroup.map_map ..).symm
      _ = Psub := by rw [hφ]
  have hT_ne : T ≠ ⊥ := by
    intro hT
    exact hTc (by rw [hT, Subgroup.commutator_bot_left])
  have hTψ_ne : Tψ ≠ ⊥ := by
    intro hTψ
    apply hT_ne
    have hker' : ψ.toMonoidHom.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact ψ.injective
    have hle : T ≤ ψ.toMonoidHom.ker := (Subgroup.map_eq_bot_iff T).mp hTψ
    rw [hker'] at hle
    exact le_bot_iff.mp hle
  have hTψ2_dvd : 2 ∣ Nat.card Tψ := by
    rcases hTψ2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hTψ_ne
    · exact h2
  have h2R : 2 ∣ Nat.card R :=
    hTψ2_dvd.trans (Subgroup.card_dvd_of_surjective hf_surj)
  have hP_ne : (P : Subgroup R) ≠ ⊥ := by
    intro hPbot
    have hcardP : Nat.card (P : Subgroup R) = 1 := Subgroup.card_eq_one.mpr hPbot
    have hmul := Subgroup.card_mul_index (H := (P : Subgroup R))
    rw [hcardP, one_mul] at hmul
    exact Sylow.not_dvd_index P (by rw [hmul]; exact h2R)
  have hPsub2 : IsPGroup 2 Psub := P.isPGroup'.map R.subtype
  have hPsub_ne : Psub ≠ ⊥ := by
    intro hPsub
    apply hP_ne
    have hmap : (P : Subgroup R).map R.subtype = ⊥ := hPsub
    rw [Subgroup.map_eq_bot_iff] at hmap
    have hker' : R.subtype.ker = ⊥ := by
      rw [MonoidHom.ker_eq_bot_iff]
      exact R.subtype_injective
    rw [hker'] at hmap
    exact le_bot_iff.mp hmap
  let W : Submodule F (Fin d → F) :=
  { carrier := {v | ∀ p : Psub, (p : ↥(UniSU n d F)) • v = v}
    add_mem' := by
      intro u v hu hv p
      rw [smul_add, hu p, hv p]
    zero_mem' := by
      intro p
      rw [smul_zero]
    smul_mem' := by
      intro c v hv p
      rw [← smul_comm c, hv p] }
  have hAW : ∀ a ∈ A, ∀ w ∈ W, (a : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W := by
    intro a ha w hw
    intro p
    have haSU : (⟨a, hASU ha⟩ : ↥(UniSU n d F)) ∈ A.subgroupOf (UniSU n d F) :=
      Subgroup.mem_subgroupOf.mpr ha
    have hMP : (⟨a, hASU ha⟩ : ↥(UniSU n d F)) ∈ Subgroup.normalizer Psub := hAP haSU
    have hq : (⟨a, hASU ha⟩ : ↥(UniSU n d F))⁻¹ * (p : ↥(UniSU n d F)) *
        (⟨a, hASU ha⟩ : ↥(UniSU n d F)) ∈ Psub :=
      (Subgroup.mem_normalizer_iff''.mp hMP (p : ↥(UniSU n d F))).mp p.2
    let q : Psub := ⟨_, hq⟩
    have hvq : q • w = w := hw q
    change (p : ↥(UniSU n d F)) • ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) • w) =
      (⟨a, hASU ha⟩ : ↥(UniSU n d F)) • w
    calc (p : ↥(UniSU n d F)) • ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) • w)
        = ((p : ↥(UniSU n d F)) * (⟨a, hASU ha⟩ : ↥(UniSU n d F))) • w :=
            (mul_smul _ _ _).symm
      _ = ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) * q) • w := by
            congr 1
            apply Subtype.ext
            change ((p : ↥(UniSU n d F)) : GL (Fin d) F) *
                ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) : GL (Fin d) F) =
              ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) : GL (Fin d) F) * ((q : Psub) : GL (Fin d) F)
            rw [show ((q : Psub) : GL (Fin d) F) =
              ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) : GL (Fin d) F)⁻¹ *
                ((p : ↥(UniSU n d F)) : GL (Fin d) F) *
                ((⟨a, hASU ha⟩ : ↥(UniSU n d F)) : GL (Fin d) F) from rfl]
            group
      _ = (⟨a, hASU ha⟩ : ↥(UniSU n d F)) • (q • w) := mul_smul _ _ _
      _ = (⟨a, hASU ha⟩ : ↥(UniSU n d F)) • w := by rw [hvq]
  have hWspan : W = Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) ''
      {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}) :=
    invariant_eq_span_single hdiag hcon hAW
  let J : Set (Fin d) := {i | (Pi.single i (1 : F) : Fin d → F) ∈ W}
  have hWspanJ : W = Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) '' J) :=
    hWspan
  have hWchar : ∀ v ∈ W, ∀ i, i ∉ J → v i = 0 := by
    intro v hv i hi
    rw [hWspanJ] at hv
    have hle : Submodule.span F ((fun i => (Pi.single i (1 : F) : Fin d → F)) '' J) ≤
        evalZeroSubmodule i := by
      rw [Submodule.span_le]
      rintro x ⟨j, hj, rfl⟩
      exact Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := i)
        (by intro h; rw [← h] at hj; exact hi hj) (1 : F)
    exact hle hv
  let W' : Submodule F (Fin d → F) :=
  { carrier := {v | ∀ i ∈ J, v i = 0}
    add_mem' := by
      intro u v hu hv i hi
      rw [Pi.add_apply, hu i hi, hv i hi, add_zero]
    zero_mem' := by intro i hi; rfl
    smul_mem' := by
      intro c v hv i hi
      rw [Pi.smul_apply, hv i hi, smul_zero] }
  have hdisj : W ⊓ W' = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvW'⟩ := Submodule.mem_inf.mp hv
    funext i
    by_cases hi : i ∈ J
    · exact hvW' i hi
    · exact hWchar v hvW i hi
  have hW'P : ∀ p : Psub, ∀ v ∈ W', (p : ↥(UniSU n d F)) • v ∈ W' := by
    intro p v hv i hi
    have hp : ((p : ↥(UniSU n d F)) : GL (Fin d) F) ∈ unitaryPreservers n d F :=
      uniSU_le_unitaryPreservers (p : ↥(UniSU n d F)).2
    have hfix : ((p : ↥(UniSU n d F))⁻¹) • (Pi.single i (1 : F) : Fin d → F) =
        (Pi.single i (1 : F) : Fin d → F) := by
      have := ((show (Pi.single i (1 : F) : Fin d → F) ∈ W from hi) (p⁻¹))
      simpa using this
    calc ((p : ↥(UniSU n d F)) • v) i
        = uniForm n (Pi.single i (1 : F) : Fin d → F) ((p : ↥(UniSU n d F)) • v) :=
            (uniForm_single n i _).symm
      _ = uniForm n (((p : ↥(UniSU n d F))⁻¹) • (Pi.single i (1 : F) : Fin d → F)) v := by
            have hp' := hp (((p : ↥(UniSU n d F))⁻¹) • (Pi.single i (1 : F) : Fin d → F)) v
            have h1 : ((p : ↥(UniSU n d F)) : GL (Fin d) F) *ᵥ
                (((p : ↥(UniSU n d F))⁻¹) • (Pi.single i (1 : F) : Fin d → F)) =
                (Pi.single i (1 : F) : Fin d → F) := by
              rw [show (((p : ↥(UniSU n d F))⁻¹) • (Pi.single i (1 : F) : Fin d → F)) =
                  (((p : ↥(UniSU n d F))⁻¹) : GL (Fin d) F) *ᵥ
                    (Pi.single i (1 : F) : Fin d → F) from rfl]
              rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
                Matrix.one_mulVec]
            rw [h1] at hp'
            exact hp'
      _ = uniForm n (Pi.single i (1 : F) : Fin d → F) v := by rw [hfix]
      _ = v i := uniForm_single n i v
      _ = 0 := hv i hi
  letI : MulAction Psub W' :=
  { smul := fun p v => ⟨(p : ↥(UniSU n d F)) • (v : Fin d → F), hW'P p v v.2⟩
    one_smul v := by
      apply Subtype.ext
      show ((1 : Psub) : ↥(UniSU n d F)) • (v : Fin d → F) = (v : Fin d → F)
      rw [Subgroup.coe_one, one_smul]
    mul_smul p q v := by
      apply Subtype.ext
      show ((p * q : Psub) : ↥(UniSU n d F)) • (v : Fin d → F) =
        (p : ↥(UniSU n d F)) • ((q : ↥(UniSU n d F)) • (v : Fin d → F))
      rw [Subgroup.coe_mul, mul_smul] }
  rcases eq_or_ne W' ⊥ with hW'bot | hW'ne
  · have htop : W ⊔ W' = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← span_single_univ_eq_top]
      rw [Submodule.span_le]
      rintro x ⟨i, -, rfl⟩
      by_cases hi : i ∈ J
      · exact Submodule.mem_sup_left (by rw [hWspanJ]; exact Submodule.subset_span ⟨i, hi, rfl⟩)
      · exact Submodule.mem_sup_right (fun j hj =>
          Pi.single_eq_of_ne (M := fun _ => F) (i := i) (i' := j)
            (by intro h; rw [h] at hj; exact hi hj) (1 : F))
    have hWtop : W = ⊤ := by
      have := htop
      rw [hW'bot, sup_bot_eq] at this
      exact this
    have hPsub_bot : Psub = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro p hp
      apply Subtype.ext
      apply Units.ext
      ext i j
      have hfix : ((p : ↥(UniSU n d F)) • (Pi.single j (1 : F) : Fin d → F)) =
          (Pi.single j (1 : F) : Fin d → F) := by
        exact (show (Pi.single j (1 : F) : Fin d → F) ∈ W from by
          rw [hWtop]; exact Submodule.mem_top) ⟨p, hp⟩
      have := congrFun hfix i
      rw [show ((p : ↥(UniSU n d F)) • (Pi.single j (1 : F) : Fin d → F)) =
          (((p : ↥(UniSU n d F)) : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ
            (Pi.single j (1 : F) : Fin d → F) from rfl] at this
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single j] at this
      · rw [Pi.single_eq_same, mul_one] at this
        rw [this]
        change (Pi.single j (1 : F) : Fin d → F) i = (1 : Matrix (Fin d) (Fin d) F) i j
        by_cases h : i = j
        · subst h; simp
        · rw [Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := i) h (1 : F),
            Matrix.one_apply, if_neg h]
      · intro k _ hk
        rw [Pi.single_eq_of_ne (M := fun _ => F) (i := j) (i' := k) hk (1 : F), mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    exact hPsub_ne hPsub_bot
  · haveI : FiniteDimensional F (Fin d → F) := inferInstance
    haveI : Module.Finite F W' := FiniteDimensional.finiteDimensional_submodule W'
    have hcardW' : 2 ∣ Nat.card W' := by
      rw [Module.natCard_eq_pow_finrank (K := F), h.2.2.2.1]
      have hbase : 2 ∣ (2 ^ n) ^ 2 := by
        rw [← pow_mul]
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero
          (Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (show 1 ≤ n from h.2.2.2.2.1))
            (show (2:ℕ) ≠ 0 by norm_num))
        exact ⟨2 ^ m, by rw [hm, pow_succ, mul_comm]⟩
      have hk : Module.finrank F W' ≠ 0 := by
        haveI : Nontrivial W' := (Submodule.nontrivial_iff_ne_bot (p := W')).mpr hW'ne
        exact (Module.finrank_pos (R := F) (M := W')).ne'
      exact hbase.trans (dvd_pow_self ((2 ^ n) ^ 2) hk)
    have hfix := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (p := 2) (G := Psub) hPsub2 W' hcardW' (a := 0)
      (by
        rw [MulAction.mem_fixedPoints]
        intro g
        apply Subtype.ext
        show ((g : ↥(UniSU n d F)) • (0 : Fin d → F)) = 0
        rw [smul_zero])
    obtain ⟨b, hb, hb0⟩ := hfix
    have hbW : (b : Fin d → F) ∈ W := by
      intro p
      have := (MulAction.mem_fixedPoints.mp hb) p
      exact congrArg Subtype.val this
    have hbW' : (b : Fin d → F) ∈ W' := b.2
    have hb0' : (b : Fin d → F) = 0 := by
      have : (b : Fin d → F) ∈ W ⊓ W' := Submodule.mem_inf.mpr ⟨hbW, hbW'⟩
      rw [hdisj] at this
      exact this
    exact hb0 (Subtype.ext hb0'.symm)


end CFSG.LocalAnalysis.GLTheoremA.T173A

end
