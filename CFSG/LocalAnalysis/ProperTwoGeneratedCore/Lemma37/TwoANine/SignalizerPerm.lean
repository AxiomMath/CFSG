module

public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Equiv Subgroup

theorem smul_eq_self_of_odd_of_isPGroup {G X : Type*} [Group G] [Finite G] [MulAction G X]
    {K F : Subgroup G} (hK : Odd (Nat.card K)) (hF : IsPGroup 2 F)
    (hFK : F ≤ normalizer (K : Set G)) {x : X} (hfree : ∀ f ∈ F, f • x = x → f = 1)
    (hsurj : ∀ k ∈ K, ∃ f ∈ F, f • x = k • x) {k : G} (hk : k ∈ K) : k • x = x := by
  have hconj : ∀ f ∈ F, ∀ k ∈ K, f * k * f⁻¹ ∈ K := fun f hf k hk =>
    (Subgroup.mem_normalizer_iff.mp (hFK hf) k).mp hk
  let B : Subgroup G :=
    { carrier := {f | f ∈ F ∧ ∃ k ∈ K, f • x = k • x}
      mul_mem' := by
        rintro f g ⟨hf, k, hk, hfk⟩ ⟨hg, l, hl, hgl⟩
        refine ⟨F.mul_mem hf hg, f * l * f⁻¹ * k, K.mul_mem (hconj f hf l hl) hk, ?_⟩
        calc (f * g) • x = f • l • x := by rw [mul_smul, hgl]
          _ = (f * l * f⁻¹) • f • x := by rw [← mul_smul, ← mul_smul, inv_mul_cancel_right]
          _ = (f * l * f⁻¹ * k) • x := by rw [hfk, mul_smul (f * l * f⁻¹) k]
      one_mem' := ⟨F.one_mem, 1, K.one_mem, rfl⟩
      inv_mem' := by
        rintro f ⟨hf, k, hk, hfk⟩
        refine ⟨F.inv_mem hf, f⁻¹ * k⁻¹ * f, ?_, ?_⟩
        · simpa only [inv_inv] using hconj f⁻¹ (F.inv_mem hf) k⁻¹ (K.inv_mem hk)
        · rw [mul_smul, mul_smul, hfk, inv_smul_smul] }
  have hB2 : IsPGroup 2 B := hF.to_le fun f hf => hf.1
  let φ : B → MulAction.orbit K x := fun f => ⟨(f : G) • x, by
    obtain ⟨k, hk, h⟩ := f.2.2
    exact ⟨⟨k, hk⟩, h.symm⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun f g hfg => Subtype.ext ?_, fun y => ?_⟩
    · have h : (g : G) • x = (f : G) • x := (congrArg Subtype.val hfg).symm
      have h1 := hfree _ (F.mul_mem (F.inv_mem g.2.1) f.2.1) (by rw [mul_smul, ← h, inv_smul_smul])
      exact (inv_mul_eq_one.mp h1).symm
    · obtain ⟨⟨k, hk⟩, hy⟩ := y.2
      obtain ⟨f, hf, hfk⟩ := hsurj k hk
      exact ⟨⟨f, hf, k, hk, hfk⟩, Subtype.ext (hfk.trans hy)⟩
  have hcard : Nat.card B = (MulAction.orbit K x).ncard :=
    (Nat.card_congr (Equiv.ofBijective φ hφ)).trans (Nat.card_coe_set_eq _)
  have hdvd : Nat.card B ∣ Nat.card K := by
    rw [hcard, ← MulAction.index_stabilizer]
    exact Subgroup.index_dvd_card _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hB2
  have hn0 : n = 0 := by
    by_contra h0
    rw [hn] at hdvd
    exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr
      ((dvd_pow_self 2 h0).trans hdvd))
  rw [hn0, pow_zero] at hn
  have hbot : B = ⊥ := Subgroup.eq_bot_of_card_eq B hn
  obtain ⟨f, hf, hfk⟩ := hsurj k hk
  have hf1 : f = 1 := (Subgroup.eq_bot_iff_forall B).mp hbot f ⟨hf, k, hk, hfk⟩
  rw [← hfk, hf1, one_smul]

variable {F K : Subgroup (alternatingGroup (Fin 9))} {p : Fin 9}

theorem eq_one_of_odd_of_regular_of_apply_eq (hF2 : ∀ f ∈ F, f ^ 2 = 1)
    (hFp : ∀ f ∈ F, (f : Perm (Fin 9)) p = p)
    (hreg : ∀ i j, i ≠ p → j ≠ p → ∃! f, f ∈ F ∧ (f : Perm (Fin 9)) i = j)
    (hK : Odd (Nat.card K)) (hFK : F ≤ normalizer (K : Set (alternatingGroup (Fin 9))))
    {y : alternatingGroup (Fin 9)} (hy : y ∈ K) (hyp : (y : Perm (Fin 9)) p = p) : y = 1 := by
  let S := MulAction.stabilizer (alternatingGroup (Fin 9)) p
  have hFS : F ≤ S := fun f hf => hFp f hf
  have hKS : Odd (Nat.card (K ⊓ S : Subgroup _)) := Odd.of_dvd_nat hK (Subgroup.card_dvd_of_le
    inf_le_left)
  have hFKS : F ≤ normalizer ((K ⊓ S : Subgroup _) : Set (alternatingGroup (Fin 9))) :=
    (le_inf hFK (hFS.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hF : IsPGroup 2 F := fun f => ⟨1, Subtype.ext (by rw [pow_one]; exact hF2 f f.2)⟩
  refine Subtype.ext (Perm.ext fun i => ?_)
  rcases eq_or_ne i p with rfl | hi
  · exact hyp
  · refine smul_eq_self_of_odd_of_isPGroup (X := Fin 9) hKS hF hFKS (x := i) (fun f hf hfi => ?_)
      (fun k hk => ?_) (k := y) ⟨hy, hyp⟩
    · exact (hreg i i hi hi).unique ⟨hf, hfi⟩ ⟨F.one_mem, rfl⟩
    · have hkp : (k : Perm (Fin 9)) p = p := hk.2
      have hki : (k : Perm (Fin 9)) i ≠ p := fun h =>
        hi ((k : Perm (Fin 9)).injective (h.trans hkp.symm))
      obtain ⟨f, ⟨hf, hfi⟩, -⟩ := hreg i _ hi hki
      exact ⟨f, hf, hfi⟩

theorem eq_one_of_regular_of_conj_eq (hF2 : ∀ f ∈ F, f ^ 2 = 1)
    (hFp : ∀ f ∈ F, (f : Perm (Fin 9)) p = p)
    (hreg : ∀ i j, i ≠ p → j ≠ p → ∃! f, f ∈ F ∧ (f : Perm (Fin 9)) i = j)
    (hK : Odd (Nat.card K)) (hFK : F ≤ normalizer (K : Set (alternatingGroup (Fin 9))))
    {f : alternatingGroup (Fin 9)} (hf : f ∈ F) (hf1 : f ≠ 1) {y : alternatingGroup (Fin 9)}
    (hy : y ∈ K) (hfy : f * y * f⁻¹ = y) : y = 1 := by
  refine eq_one_of_odd_of_regular_of_apply_eq hF2 hFp hreg hK hFK hy ?_
  by_contra hyp
  have hfy' : (f : Perm (Fin 9)) ((y : Perm (Fin 9)) p) = (y : Perm (Fin 9)) p := by
    have h := congrArg (fun g : alternatingGroup (Fin 9) => (g : Perm (Fin 9)) p)
      (mul_inv_eq_iff_eq_mul.mp hfy)
    simp only [Subgroup.coe_mul, Perm.mul_apply, hFp f hf] at h
    exact h
  exact hf1 ((hreg _ _ hyp hyp).unique ⟨hf, hfy'⟩ ⟨F.one_mem, rfl⟩)

private def conjEnd {f : alternatingGroup (Fin 9)}
    (hf : f ∈ normalizer (K : Set (alternatingGroup (Fin 9)))) : K →* K :=
  ((MulAut.conj f).toMonoidHom.comp K.subtype).codRestrict K fun y =>
    (Subgroup.mem_normalizer_iff.mp hf y).mp y.2

theorem eq_bot_of_odd_of_regular_le_normalizer (hF2 : ∀ f ∈ F, f ^ 2 = 1)
    (hFp : ∀ f ∈ F, (f : Perm (Fin 9)) p = p)
    (hreg : ∀ i j, i ≠ p → j ≠ p → ∃! f, f ∈ F ∧ (f : Perm (Fin 9)) i = j)
    (hK : Odd (Nat.card K)) (hFK : F ≤ normalizer (K : Set (alternatingGroup (Fin 9)))) :
    K = ⊥ := by
  have hinv : ∀ f ∈ F, f ≠ 1 → ∀ y ∈ K, f * y * f⁻¹ = y⁻¹ := fun f hf hf1 y hy => by
    have hfix : MonoidHom.FixedPointFree (conjEnd (hFK hf)) := fun z hz =>
      Subtype.ext
        (eq_one_of_regular_of_conj_eq hF2 hFp hreg hK hFK hf hf1 z.2 (congrArg Subtype.val hz))
    have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_left (by rw [← sq, hF2 f hf])
    have hinvol : Function.Involutive (conjEnd (hFK hf)) := fun z => Subtype.ext (by
      change f * (f * z * f⁻¹) * f⁻¹ = z
      rw [hfinv, ← mul_assoc, ← mul_assoc, ← sq, hF2 f hf, one_mul, mul_assoc, ← sq, hF2 f hf,
        mul_one])
    exact congrArg Subtype.val (congrFun (hfix.coe_eq_inv_of_involutive hinvol) ⟨y, hy⟩)
  obtain ⟨i, hi⟩ := exists_ne p
  obtain ⟨j₁, j₂, hj₁, hj₂, hij₁, hij₂, hj₁₂⟩ : ∃ j₁ j₂ : Fin 9, j₁ ≠ p ∧ j₂ ≠ p ∧ i ≠ j₁ ∧
      i ≠ j₂ ∧ j₁ ≠ j₂ := by
    have h7 : 2 < ((Finset.univ.erase p).erase i).card := by
      rw [Finset.card_erase_of_mem (by simp [hi]), Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
      norm_num
    obtain ⟨a, ha, b, hb, -, -, hab, -, -⟩ := Finset.two_lt_card.mp h7
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at ha hb
    exact ⟨a, b, ha.2, hb.2, Ne.symm ha.1, Ne.symm hb.1, hab⟩
  obtain ⟨f₁, ⟨hf₁, hf₁i⟩, -⟩ := hreg i j₁ hi hj₁
  obtain ⟨f₂, ⟨hf₂, hf₂i⟩, -⟩ := hreg i j₂ hi hj₂
  have hne : ∀ {f : alternatingGroup (Fin 9)} {j : Fin 9}, (f : Perm (Fin 9)) i = j → i ≠ j →
      f ≠ 1 := fun hfi hij h => hij (by rw [← hfi, h]; rfl)
  have hf₁₂ : f₁ * f₂ ≠ 1 := by
    intro h
    have h' : f₁ = f₂ := by
      rw [mul_eq_one_iff_eq_inv.mp h]
      exact inv_eq_of_mul_eq_one_left (by rw [← sq, hF2 f₂ hf₂])
    exact hj₁₂ (by rw [← hf₁i, ← hf₂i, h'])
  refine (Subgroup.eq_bot_iff_forall K).mpr fun y hy => ?_
  refine eq_one_of_regular_of_conj_eq hF2 hFp hreg hK hFK (F.mul_mem hf₁ hf₂) hf₁₂ hy ?_
  have h2 := hinv f₂ hf₂ (hne hf₂i hij₂) y hy
  have h1 := hinv f₁ hf₁ (hne hf₁i hij₁) y⁻¹ (K.inv_mem hy)
  calc f₁ * f₂ * y * (f₁ * f₂)⁻¹ = f₁ * (f₂ * y * f₂⁻¹) * f₁⁻¹ := by group
    _ = y := by rw [h2, h1, inv_inv]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
