module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootMono
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralHVec

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Cartan

private theorem fg_cartan_self (i : Fin Tag.E6.rank) : Tag.E6.cartan i i = 2 := by
  fin_cases i <;> rfl

private theorem fg_exists_cartanPair_unit : ∀ β ∈ rootFinset Tag.E6,
    ∃ k, cartanPair Tag.E6 β k = 1 ∨ cartanPair Tag.E6 β k = -1 := by
  decide +kernel

variable {L : Type} [Field L]

private theorem fg_step (i : Fin Tag.E6.rank) (γ : Fin Tag.E6.rank → ℤ)
    (t : Fin Tag.E6.rank → L) :
    ∃ t' : Fin Tag.E6.rank → L,
      (weylElt Tag.E6 L i 1 : Module.End L (RootModule Tag.E6 L)) (∑ m, t m • hVec Tag.E6 L m) =
        ∑ m, t' m • hVec Tag.E6 L m ∧
      ∑ m, t' m * ((e6Sgn m * cartanPair Tag.E6 (reflect Tag.E6 i γ) m : ℤ) : L) =
        ∑ m, t m * ((e6Sgn m * cartanPair Tag.E6 γ m : ℤ) : L) := by
  set C : L := ∑ m, t m * ((Tag.E6.cartan m i).natAbs : L) with hC
  refine ⟨fun m => t m - if m = i then C else 0, ?_, ?_⟩
  · simp only [map_sum, map_smul, weylElt_hVec, smul_sub, Finset.sum_sub_distrib, sub_smul,
      ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    rw [hC, Finset.sum_smul]
    exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
  · have hs : ((e6Sgn i : ℤ) : L) * ((e6Sgn i : ℤ) : L) = 1 := by
      rcases e6Sgn_sign i with h | h <;> rw [h] <;> norm_num
    have hCs : C * ((e6Sgn i : ℤ) : L) =
        ∑ m, t m * ((e6Sgn m : ℤ) : L) * ((Tag.E6.cartan m i : ℤ) : L) := by
      rw [hC, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h := congrArg (Int.cast : ℤ → L) (e6Sgn_abs m i)
      rw [Int.cast_natCast] at h
      rw [mul_assoc, h]
      push_cast
      linear_combination (t m * ((e6Sgn m : ℤ) : L) * ((Tag.E6.cartan m i : ℤ) : L)) * hs
    have e1 : ∑ m, t m * ((e6Sgn m * cartanPair Tag.E6 (reflect Tag.E6 i γ) m : ℤ) : L) =
        ∑ m, t m * ((e6Sgn m * cartanPair Tag.E6 γ m : ℤ) : L) -
          ((cartanPair Tag.E6 γ i : ℤ) : L) *
            ∑ m, t m * ((e6Sgn m : ℤ) : L) * ((Tag.E6.cartan m i : ℤ) : L) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [cartanPair_reflect]
      push_cast
      ring
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [e1, cartanPair_reflect, fg_cartan_self]
    push_cast
    linear_combination ((cartanPair Tag.E6 γ i : ℤ) : L) * hCs

private theorem fg_word (ω : List (Fin Tag.E6.rank)) (δ : Fin Tag.E6.rank → ℤ)
    (t : Fin Tag.E6.rank → L) :
    ∃ t' : Fin Tag.E6.rank → L,
      (((ω.map fun i => weylElt Tag.E6 L i 1).prod : ModGL Tag.E6 L) :
          Module.End L (RootModule Tag.E6 L)) (∑ m, t m • hVec Tag.E6 L m) =
        ∑ m, t' m • hVec Tag.E6 L m ∧
      ∑ m, t' m *
          ((e6Sgn m * cartanPair Tag.E6 ((coxeterSystem Tag.E6).wordProd ω • δ) m : ℤ) : L) =
        ∑ m, t m * ((e6Sgn m * cartanPair Tag.E6 δ m : ℤ) : L) := by
  induction ω with
  | nil => exact ⟨t, by simp, by simp⟩
  | cons i ω ih =>
    obtain ⟨t', h1, h2⟩ := ih
    obtain ⟨t'', h3, h4⟩ := fg_step i ((coxeterSystem Tag.E6).wordProd ω • δ) t'
    refine ⟨t'', ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, Units.val_mul, Module.End.mul_apply, h1, h3]
    · have e : (coxeterSystem Tag.E6).wordProd (i :: ω) • δ =
          reflect Tag.E6 i ((coxeterSystem Tag.E6).wordProd ω • δ) := by
        rw [CoxeterSystem.wordProd_cons, mul_smul]
        exact simple_smul i _
      rw [e, h4, h2]

end Cartan

section Generic


theorem exists_pinnedX_sign_of_rootVec_fixed {τ : Tag} (hτ : τ = Tag.E6) {L : Type} [Field L]
    {a : Fin τ.rank → Lˣ} {w : WeylGroup τ} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hwβ : w • β = β)
    (hfix : ((rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w : ModGL τ L) :
      Module.End L (RootModule τ L)) (rootVec τ L β) = rootVec τ L β) :
    ∃ ε : L, (∀ c : L, canonicalRep (coxeterSystem τ) L w * pinnedX τ L β c *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L β (ε * c)) ∧
      (rootChar a β : L) * ε = 1 := by
  subst hτ
  obtain ⟨ε, -, hX⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hβ
  rw [hwβ] at hX
  refine ⟨ε, hX, ?_⟩
  have hconj : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w *
      pinnedX Tag.E6 L β 1 = pinnedX Tag.E6 L β ((rootChar a β : L) * ε) *
        (rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w) := by
    have h : rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w *
        pinnedX Tag.E6 L β 1 *
          (rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ =
        pinnedX Tag.E6 L β ((rootChar a β : L) * ε) := by
      calc rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w *
            pinnedX Tag.E6 L β 1 *
              (rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L w)⁻¹ =
          rootDiagUnit Tag.E6 a * (canonicalRep (coxeterSystem Tag.E6) L w *
            pinnedX Tag.E6 L β 1 * (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) *
              (rootDiagUnit Tag.E6 a)⁻¹ := by group
        _ = pinnedX Tag.E6 L β ((rootChar a β : L) * ε) := by
          rw [hX, rootDiagUnit_conj_pinnedX a hβ, mul_one]
    rw [← h, inv_mul_cancel_right]
  obtain ⟨k, hk⟩ := fg_exists_cartanPair_unit β (mem_rootFinset.2 hβ)
  obtain ⟨S, hS, hXh⟩ := pinnedX_hVec_e6 (K := L) hβ
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  obtain ⟨t, ht1, ht2⟩ := fg_word (L := L) ω β (Pi.single k 1)
  rw [hwβ] at ht2
  have hsk : ∑ m, (Pi.single k (1 : L) : Fin Tag.E6.rank → L) m • hVec Tag.E6 L m =
      hVec Tag.E6 L k := by
    rw [Finset.sum_eq_single k (fun m _ hm => by rw [Pi.single_eq_of_ne hm, zero_smul])
      (by simp), Pi.single_eq_same, one_smul]
  have hlam : ∑ m, (Pi.single k (1 : L) : Fin Tag.E6.rank → L) m *
      ((e6Sgn m * cartanPair Tag.E6 β m : ℤ) : L) =
        ((e6Sgn k * cartanPair Tag.E6 β k : ℤ) : L) := by
    rw [Finset.sum_eq_single k (fun m _ hm => by rw [Pi.single_eq_of_ne hm, zero_mul])
      (by simp), Pi.single_eq_same, one_mul]
  rw [hsk] at ht1
  rw [hlam] at ht2
  rw [← canonicalRep_wordProd hω] at ht1
  have hyh : ((rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L
      ((coxeterSystem Tag.E6).wordProd ω) : ModGL Tag.E6 L) : Module.End L (RootModule Tag.E6 L))
        (hVec Tag.E6 L k) = ∑ m, t m • hVec Tag.E6 L m := by
    rw [Units.val_mul, Module.End.mul_apply, ht1]
    change rootDiag a (∑ m, t m • hVec Tag.E6 L m) = _
    simp only [map_sum, map_smul, rootDiag_hVec]
  have hXsum : ∀ c : L, (pinnedX Tag.E6 L β c : Module.End L (RootModule Tag.E6 L))
      (∑ m, t m • hVec Tag.E6 L m) = ∑ m, t m • hVec Tag.E6 L m +
        (S * c * ∑ m, t m * ((e6Sgn m * cartanPair Tag.E6 β m : ℤ) : L)) •
          rootVec Tag.E6 L β := by
    intro c
    simp only [map_sum, map_smul, hXh c, smul_add, Finset.sum_add_distrib, smul_smul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_smul]
    exact Finset.sum_congr rfl fun m _ => by congr 1; ring
  generalize rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) L
    ((coxeterSystem Tag.E6).wordProd ω) = y at hconj hfix hyh
  have key := congrArg (fun g : ModGL Tag.E6 L => (g : Module.End L (RootModule Tag.E6 L))
    (hVec Tag.E6 L k)) hconj
  simp only [Units.val_mul, Module.End.mul_apply] at key
  rw [hXh 1 k, map_add, map_smul, hfix, hyh, hXsum, ht2] at key
  have hne : rootVec Tag.E6 L β ≠ 0 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootVec_eq_single hβ]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h2 := smul_left_injective L hne (add_left_cancel key)
  have hS0 : S ≠ 0 := by rcases hS with rfl | rfl <;> norm_num
  have hl0 : ((e6Sgn k * cartanPair Tag.E6 β k : ℤ) : L) ≠ 0 := by
    rcases e6Sgn_sign k with h | h <;> rcases hk with h' | h' <;> rw [h, h'] <;> norm_num
  have h3 : (S * ((e6Sgn k * cartanPair Tag.E6 β k : ℤ) : L)) * ((rootChar a β : L) * ε - 1) =
      0 := by
    linear_combination -h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (mul_ne_zero hS0 hl0))

end Generic

section FixedRoot


theorem normalizesRGroup_of_monomial_fixed_rootVec (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hvβ : v • permLattice TwistTag.E6.perm β = -β)
    (hmono : ∀ x ∈ E₀, ∃ (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ)
        (w : WeylGroup TwistTag.E6.tag),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 =
        rootDiagUnit TwistTag.E6.tag a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∧
      w • β = β ∧
      ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) β) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) β ∧
      ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) (-β)) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) (-β)) :
    NormalizesRGroup (ringChar K) E₀ := by
  refine normalizesRGroup_of_monomial_fixed_root q K σ hK hσ hr E₀ Fr hFr v g0 hg0C hg0 hβ hvβ
    fun x hx => ?_
  obtain ⟨a, w, hm, hwβ, hfix, hfix'⟩ := hmono x hx
  rw [hm] at hfix hfix'
  exact ⟨a, w, hm, exists_pinnedX_sign_of_rootVec_fixed (τ := TwistTag.E6.tag) rfl hβ hwβ hfix,
    exists_pinnedX_sign_of_rootVec_fixed (τ := TwistTag.E6.tag) rfl (IsRoot.neg hβ)
      (by rw [smul_neg, hwβ]) hfix'⟩

end FixedRoot

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
