module

public import CFSG.LieType.Steinberg.Basic
public import CFSG.Blueprint.ChevalleyStrings
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Steinberg

open CFSG.Blueprint.Chevalley

namespace TagRoots

variable {τ : Tag}

theorem isRoot_neg {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : IsRoot τ (-v) := by
  induction hv with
  | basis j => exact isRoot_neg_single τ j
  | @reflect i w _ ih =>
    have h : -reflect τ i w = reflect τ i (-w) := by
      rw [← reflectHom_apply, ← reflectHom_apply, map_neg]
    exact h ▸ IsRoot.reflect i ih

theorem eq_or_eq_neg_of_not_linIndepPair {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hδ : IsRoot τ δ) (h : ¬ LinIndepPair γ δ) : γ = δ ∨ γ = -δ := by
  simp only [LinIndepPair, not_forall] at h
  obtain ⟨a, b, hab, hne⟩ := h
  obtain ⟨j, f, hf⟩ := hδ.exists_addMonoidHom_eq_single
  obtain ⟨i, g, hg⟩ := hγ.exists_addMonoidHom_eq_single
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := fun hb => hne ⟨rfl, hb⟩
    have : b • δ = 0 := by simpa using hab
    exact hδ.ne_zero ((smul_eq_zero.1 this).resolve_left hb)
  have hb : b ≠ 0 := by
    rintro rfl
    have : a • γ = 0 := by simpa using hab
    exact hγ.ne_zero ((smul_eq_zero.1 this).resolve_left ha)
  have hfγ : a • f γ = -(b • Pi.single j 1) := by
    have := congrArg f hab
    rw [map_add, map_zsmul, map_zsmul, hf, map_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  have hgδ : b • g δ = -(a • Pi.single i 1) := by
    have := congrArg g hab
    rw [map_add, map_zsmul, map_zsmul, hg, map_zero] at this
    exact eq_neg_of_add_eq_zero_right this
  have hm : a * f γ j = -b := by simpa using congrFun hfγ j
  have hm' : b * g δ i = -a := by simpa using congrFun hgδ i
  have hmm : f γ j * g δ i = 1 := by
    have h1 : a * (f γ j * g δ i) = a := by
      calc a * (f γ j * g δ i) = (a * f γ j) * g δ i := by ring
        _ = -(b * g δ i) := by rw [hm]; ring
        _ = a := by rw [hm']; ring
    have := mul_left_cancel₀ ha (h1.trans (mul_one a).symm)
    exact this
  have hγδ : a • (γ - f γ j • δ) = 0 := by
    rw [smul_sub, smul_smul, hm, neg_smul, sub_neg_eq_add, add_comm]
    simpa [add_comm] using hab
  have hγeq : γ = f γ j • δ := sub_eq_zero.1 ((smul_eq_zero.1 hγδ).resolve_left ha)
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hmm with h1 | h1
  · left; rw [hγeq, h1, one_smul]
  · right; rw [hγeq, h1, neg_one_smul]

theorem exists_word {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ (w : List (Fin τ.rank)) (i : Fin τ.rank),
      γ = wordAct (reflectHom τ) w (Pi.single i 1) := by
  induction hγ with
  | basis j => exact ⟨[], j, rfl⟩
  | reflect i _ ih =>
    obtain ⟨w, j, hw⟩ := ih
    exact ⟨i :: w, j, by simp only [wordAct, hw, reflectHom_apply]⟩

@[expose] def checkMidpoints (S : StringData τ) (C : RootCertificate τ) : Bool :=
  (List.range C.roots.length).all fun k => (S.bucket (C.root k)).all fun l =>
    !(S.memDec C (2 • C.root k - C.root l)) || (List.ofFn (C.root l) == List.ofFn (C.root k))

theorem g2_checkMidpoints : checkMidpoints g2StringData g2Certificate = true := by decide +kernel
theorem f4_checkMidpoints : checkMidpoints f4StringData f4Certificate = true := by decide +kernel
theorem d4_checkMidpoints : checkMidpoints d4StringData d4Certificate = true := by decide +kernel
theorem e6_checkMidpoints : checkMidpoints e6StringData e6Certificate = true := by decide +kernel
theorem e7_checkMidpoints : checkMidpoints e7StringData e7Certificate = true := by decide +kernel
theorem e8_checkMidpoints : checkMidpoints e8StringData e8Certificate = true := by decide +kernel

theorem Tag.checkMidpoints_eq : ∀ τ : Tag, checkMidpoints τ.stringData τ.rootCertificate = true
  | .G2 => g2_checkMidpoints
  | .F4 => f4_checkMidpoints
  | .D4 => d4_checkMidpoints
  | .E6 => e6_checkMidpoints
  | .E7 => e7_checkMidpoints
  | .E8 => e8_checkMidpoints

theorem height_eq_ht (v : Fin τ.rank → ℤ) : height v = ht v := rfl

theorem add_ne_two_smul {δ δ' ε : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hδ' : IsRoot τ δ')
    (hε : IsRoot τ ε) (hht : ht δ = ht δ') (hne : δ ≠ δ') : δ + δ' ≠ 2 • ε := by
  intro hsum
  have hC := τ.rootCertificate_check
  have hS := τ.stringData_check
  have hM := Tag.checkMidpoints_eq τ
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hε
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq hC hδ
  have hhe : ht (τ.rootCertificate.root l) = ht (τ.rootCertificate.root k) := by
    have h2 := congrArg ht hsum
    simp only [ht, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, nsmul_eq_mul,
      ← Finset.mul_sum] at h2
    simp only [ht] at hht ⊢
    push_cast at h2
    omega
  have hbucket : τ.stringData.bucket (τ.rootCertificate.root l) =
      τ.stringData.bucket (τ.rootCertificate.root k) := by
    unfold StringData.bucket
    rw [height_eq_ht, height_eq_ht, hhe]
  have hlmem : l ∈ τ.stringData.bucket (τ.rootCertificate.root k) := by
    have hb := hS
    simp only [StringData.check, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨hb, -⟩, -⟩, -⟩ := hb
    simp only [StringData.checkBuckets, List.all_eq_true, List.mem_range,
      List.contains_iff_mem] at hb
    rw [← hbucket]
    exact hb l hl
  simp only [checkMidpoints, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq] at hM
  have hd' : δ' = 2 • τ.rootCertificate.root k - τ.rootCertificate.root l := by
    rw [← hsum]; abel
  rcases hM k hk l hlmem with hfalse | heq
  · rw [← hd', (StringData.memDec_iff hC hS).2 hδ'] at hfalse
    exact absurd hfalse (by simp)
  · have hlk : τ.rootCertificate.root l = τ.rootCertificate.root k :=
      List.ofFn_injective heq
    apply hne
    rw [hd', hlk, two_smul]
    abel

end TagRoots

@[expose] def tagRootSystem (τ : Tag) : RootSystem (Fin τ.rank) where
  roots := {v | IsRoot τ v}
  finite_roots := finite_setOf_isRoot τ
  zero_notMem h := IsRoot.ne_zero h rfl
  neg_mem _ h := TagRoots.isRoot_neg h
  sign _ h := h.nonneg_or_nonpos
  single_mem i := isRoot_single τ i
  proportional γ hγ δ hδ h := by
    rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  refl := reflectHom τ
  refl_apply_of_ne i v j hj := by
    simp [reflectHom_apply, reflect, Pi.single_eq_of_ne hj]
  refl_single i := reflect_single_self τ i
  refl_refl i v := reflect_reflect τ i v
  refl_mem i _ h := IsRoot.reflect i h
  exists_word γ hγ _ := TagRoots.exists_word hγ
  sum_ne_two_smul δ hδ δ' hδ' ε hε _ hht hne _ _ := TagRoots.add_ne_two_smul hδ hδ' hε hht hne

end CFSG.LieType.Steinberg
