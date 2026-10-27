module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Algebra.DirectSum.Decomposition

public section

open Module

namespace CFSG.ABGLocalTools

variable {E W I B : Type*} [Field E] [AddCommGroup W] [Module E W] [Group B] [MulAction B I]

theorem decompose_apply_of_maps [Fintype I] [DecidableEq I] (V : I → Submodule E W)
    [DirectSum.Decomposition V] (b : B) (f : W →ₗ[E] W)
    (hmaps : ∀ i, ∀ v ∈ V i, f v ∈ V (b • i)) (w : W) (i : I) :
    (DirectSum.decompose V (f w) (b • i) : W) = f (DirectSum.decompose V w i) := by
  have hw : w = ∑ j, (DirectSum.decompose V w j : W) := by
    conv_lhs => rw [← (DirectSum.decompose V).symm_apply_apply w,
      ← DirectSum.sum_univ_of (DirectSum.decompose V w)]
    rw [DirectSum.decompose_symm_sum]
    simp_rw [DirectSum.decompose_symm_of]
  conv_lhs => rw [hw, map_sum, DirectSum.decompose_sum]
  rw [DirectSum.sum_apply, Submodule.coe_sum]
  rw [Finset.sum_eq_single i]
  · exact DirectSum.decompose_of_mem_same V (hmaps i _ (DirectSum.decompose V w i).2)
  · intro j _ hji
    apply DirectSum.decompose_of_mem_ne V (hmaps j _ (DirectSum.decompose V w j).2)
    intro h
    exact hji (smul_left_cancel b h)
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem bijective_smul_out_of_free (hfree : ∀ (b : B) (i : I), b • i = i → b = 1) :
    Function.Bijective (fun p : B × MulAction.orbitRel.Quotient B I => p.1 • p.2.out) := by
  constructor
  · rintro ⟨b, q⟩ ⟨b', q'⟩ h
    simp only at h
    have hq : q = q' := by
      have h1 : (⟦b • q.out⟧ : MulAction.orbitRel.Quotient B I) = q :=
        (Quotient.sound (MulAction.mem_orbit _ b)).trans (Quotient.out_eq q)
      have h2 : (⟦b' • q'.out⟧ : MulAction.orbitRel.Quotient B I) = q' :=
        (Quotient.sound (MulAction.mem_orbit _ b')).trans (Quotient.out_eq q')
      rw [← h1, ← h2, h]
    subst hq
    have : (b'⁻¹ * b) • q.out = q.out := by rw [mul_smul, h, inv_smul_smul]
    have hb := hfree _ _ this
    rw [inv_mul_eq_one] at hb
    rw [hb]
  · intro i
    set q : MulAction.orbitRel.Quotient B I := ⟦i⟧
    have : q.out ∈ MulAction.orbit B i := Quotient.exact (Quotient.out_eq q)
    obtain ⟨b, hb⟩ := MulAction.mem_orbit_iff.mp this
    refine ⟨(b⁻¹, q), ?_⟩
    simp only
    rw [← hb, inv_smul_smul]

theorem finrank_invariants_mul_card_of_free [FiniteDimensional E W] [Finite B] [Finite I]
    (σ : Representation E B W) (hfree : ∀ (b : B) (i : I), b • i = i → b = 1)
    (V : I → Submodule E W) (hind : iSupIndep V) (htop : ⨆ i, V i = ⊤)
    (hmaps : ∀ (b : B) (i : I), ∀ v ∈ V i, σ b v ∈ V (b • i)) :
    finrank E (Representation.invariants σ) * Nat.card B = finrank E W := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite B
  have hint : DirectSum.IsInternal V :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let := hint.chooseDecomposition
  set Q := MulAction.orbitRel.Quotient B I
  let _ : Fintype Q := Fintype.ofFinite Q
  have hbij := bijective_smul_out_of_free hfree
  have hdec : ∀ w : W, w = ∑ j, (DirectSum.decompose V w j : W) := by
    intro w
    conv_lhs => rw [← (DirectSum.decompose V).symm_apply_apply w,
      ← DirectSum.sum_univ_of (DirectSum.decompose V w)]
    rw [DirectSum.decompose_symm_sum]
    simp_rw [DirectSum.decompose_symm_of]
  have hequi : ∀ (b : B) (w : W) (i : I),
      (DirectSum.decompose V (σ b w) (b • i) : W) = σ b (DirectSum.decompose V w i) :=
    fun b w i => decompose_apply_of_maps V b (σ b) (hmaps b) w i
  have hW : finrank E W = ∑ i, finrank E (V i) := by
    rw [(DirectSum.decomposeLinearEquiv V).finrank_eq, Module.finrank_directSum]
  have hdim : ∀ (b : B) (i : I), finrank E (V (b • i)) = finrank E (V i) := by
    have hle : ∀ (b : B) (i : I), finrank E (V i) ≤ finrank E (V (b • i)) := by
      intro b i
      let f : V i →ₗ[E] V (b • i) :=
        ((σ b).comp (V i).subtype).codRestrict (V (b • i)) (fun v => hmaps b i v v.2)
      apply LinearMap.finrank_le_finrank_of_injective (f := f)
      intro x y hxy
      have h1 : σ b (x : W) = σ b (y : W) := congrArg Subtype.val hxy
      have h2 := congrArg (σ b⁻¹) h1
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply, Module.End.one_apply] at h2
      exact Subtype.ext h2
    intro b i
    apply le_antisymm _ (hle b i)
    have := hle b⁻¹ (b • i)
    rwa [inv_smul_smul] at this
  have hsum : ∑ i, finrank E (V i) = Nat.card B * ∑ q : Q, finrank E (V q.out) := by
    rw [← hbij.sum_comp (fun i => finrank E (V i))]
    simp only [hdim]
    rw [Fintype.sum_prod_type]
    change ∑ _x : B, ∑ q : Q, finrank E (V q.out) = _
    rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  set Φ : Representation.invariants σ →ₗ[E] (∀ q : Q, V q.out) :=
    (LinearMap.pi fun q : Q => DirectSum.component E I (fun i => V i) q.out) ∘ₗ
      (DirectSum.decomposeLinearEquiv V).toLinearMap ∘ₗ (Representation.invariants σ).subtype
    with hΦ
  have hΦapply : ∀ (w : Representation.invariants σ) (q : Q),
      (Φ w q : W) = DirectSum.decompose V (w : W) q.out := by
    intro w q
    rfl
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have hzero : ∀ i, (DirectSum.decompose V (w : W) i : W) = 0 := by
      intro i
      obtain ⟨⟨b, q⟩, rfl⟩ := hbij.2 i
      have hq : (DirectSum.decompose V (w : W) q.out : W) = 0 := by
        have := congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hw) q)
        rw [hΦapply] at this
        exact this
      have hinv : σ b (w : W) = w := w.2 b
      have := hequi b w q.out
      rw [hinv] at this
      simp only
      rw [this, hq, map_zero]
    apply Subtype.ext
    rw [hdec (w : W)]
    simp [hzero]
  have hΨmem : ∀ v : ∀ q : Q, V q.out,
      (∑ q : Q, ∑ b : B, σ b (v q : W)) ∈ Representation.invariants σ := by
    intro v c
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro q _
    calc ∑ b : B, σ c (σ b (v q : W)) = ∑ b : B, σ (c * b) (v q : W) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ∑ b : B, σ b (v q : W) := Equiv.sum_comp (Equiv.mulLeft c) (fun b => σ b (v q : W))
  have hΦΨ : ∀ v : ∀ q : Q, V q.out,
      Φ ⟨∑ q : Q, ∑ b : B, σ b (v q : W), hΨmem v⟩ = v := by
    intro v
    funext q'
    apply Subtype.ext
    rw [hΦapply]
    simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum]
    rw [Finset.sum_eq_single q']
    · rw [Finset.sum_eq_single 1]
      · rw [map_one, Module.End.one_apply]
        exact DirectSum.decompose_of_mem_same V (v q').2
      · intro b _ hb
        apply DirectSum.decompose_of_mem_ne V (hmaps b q'.out _ (v q').2)
        intro h
        exact hb (hfree b _ h)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro q _ hq
      apply Finset.sum_eq_zero
      intro b _
      apply DirectSum.decompose_of_mem_ne V (hmaps b q.out _ (v q).2)
      intro h
      apply hq
      have := hbij.1 (a₁ := (b, q)) (a₂ := (1, q')) (by simp only [one_smul]; exact h)
      exact (Prod.mk.inj this).2
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hΦsurj : Function.Surjective Φ := fun v => ⟨_, hΦΨ v⟩
  have hinvdim : finrank E (Representation.invariants σ) = ∑ q : Q, finrank E (V q.out) := by
    rw [(LinearEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).finrank_eq, Module.finrank_pi_fintype]
  rw [hinvdim, hW, hsum, mul_comm]

end CFSG.ABGLocalTools
