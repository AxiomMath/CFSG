module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCases
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsCompFamOut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutOrth
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.TwistedConfig
import CFSG.RankThree.PartOne.K159.RowFourType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt
  QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Module
open CFSG.GroupTheory.WeirSylow (IsPlusType isPlusType_congr)
open scoped IsMulCommutative

variable {K : Type} [Field K] {m p : ℕ}

section Weights

variable (Q : QuadraticForm K (Fin m → K)) {Aε : Subgroup (GL (Fin m) K)} [IsMulCommutative Aε]
variable [Finite K]

theorem quad_glRep_apply_of_le (h2 : (2 : K) ≠ 0) (hAεβ : Aε ≤ isomGL (polarBilin Q))
    (a : ↥Aε) (v : Fin m → K) : Q (glRep Aε a v) = Q v := by
  have h1 := mem_isomGL.1 (hAεβ a.2) v v
  rw [polarBilin_apply_apply, polarBilin_apply_apply, polar_self, polar_self, glRep_apply] at *
  rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h1
  exact mul_left_cancel₀ h2 h1

private theorem glRep_mem_wf (a : ↥Aε) (i : Option (Hyperplane ↥Aε p)) {v : Fin m → K}
    (hv : v ∈ weightFamily (p := p) (glRep Aε) i) :
    (glRep Aε a).toAddMonoidHom v ∈ weightFamily (p := p) (glRep Aε) i :=
  preserves_weightFamily_of_semilinear (glRep Aε) (RingHom.id K) (glRep Aε a).toAddMonoidHom
    (fun c v => map_smul (glRep Aε a) c v)
    (fun a' v => by
      show glRep Aε a (glRep Aε a' v) = glRep Aε a' (glRep Aε a v)
      rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]) i hv

variable (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem polar_wtU_wtW (hAεβ : Aε ≤ isomGL (polarBilin Q)) (I : Finset (Hyperplane ↥Aε p))
    {u w : Fin m → K} (hu : u ∈ wtU Aε I) (hw : w ∈ wtW Aε I) : polar Q u w = 0 := by
  obtain ⟨v, rfl⟩ := hw
  have h := projI_left (glRep Aε) (polarBilin Q) (isIsomRep_glRep hAεβ) I u v
  rw [LinearMap.mem_ker.1 hu, map_zero, LinearMap.zero_apply] at h
  rw [← polarBilin_apply_apply]
  exact h.symm

theorem nondeg_wtU (hQ : (polarBilin Q).Nondegenerate) (hAεβ : Aε ≤ isomGL (polarBilin Q))
    (I : Finset (Hyperplane ↥Aε p)) {u : Fin m → K} (hu : u ∈ wtU Aε I)
    (h : ∀ u' ∈ wtU Aε I, polar Q u u' = 0) : u = 0 := by
  refine hQ.1 u fun v => ?_
  rw [polarBilin_apply_apply]
  have hdec : v = (v - projI (glRep Aε) I v) + projI (glRep Aε) I v := by abel
  have hker : v - projI (glRep Aε) I v ∈ wtU Aε I := by
    rw [LinearMap.mem_ker, map_sub, projI_projI (glRep Aε) hp hA hpK, sub_self]
  rw [hdec, polar_add_right, h _ hker,
    polar_wtU_wtW Q hp hA hpK hAεβ I hu ⟨v, rfl⟩, add_zero]

theorem wtU_eq_fixedSpace [DecidableEq (Hyperplane ↥Aε p)] {T : Finset (Hyperplane ↥Aε p)}
    (hT : ∀ H : Hyperplane ↥Aε p, H ∈ T ↔ weightSpace (glRep Aε) H.1 ≠ ⊥) :
    wtU Aε T = fixedSpace (glRep Aε) ⊤ := by
  classical
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  ext v
  constructor
  · intro hv
    have h0 := (projI_eq_zero_iff (glRep Aε) hp hA hpK T v).1 hv
    rw [← sum_eps_apply (glRep Aε) hp hA hpK v, Fintype.sum_option, Finset.sum_eq_zero, add_zero]
    · rw [← weightFamily_none (glRep Aε) hp hA hpK]
      exact ⟨v, rfl⟩
    · intro H _
      by_cases hH : H ∈ T
      · exact h0 H hH
      · have hbot : weightSpace (glRep Aε) H.1 = ⊥ := by
          by_contra hne
          exact hH ((hT H).2 hne)
        have hmem : (glRep Aε).asAlgebraHom (eps K ↥Aε p (some H)) v ∈
            weightSpace (glRep Aε) H.1 := ⟨v, rfl⟩
        rw [hbot, Submodule.mem_bot] at hmem
        exact hmem
  · intro hv
    rw [← weightFamily_none (glRep Aε) hp hA hpK] at hv
    exact projI_apply_of_not_mem (glRep Aε) hp hA hpK (fun H _ h => Option.some_ne_none H h.symm)
      hv

end Weights


section Types

variable {V : Type} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

private theorem nondeg_comp_of {X : Submodule K V}
    (hX : ∀ v ∈ X, (∀ w ∈ X, polar Q v w = 0) → v = 0) :
    (polarBilin (Q.comp X.subtype)).Nondegenerate := by
  have key : ∀ u : X, (∀ w : X, polar Q (u : V) (w : V) = 0) → u = 0 := fun u hu =>
    Subtype.ext (hX u u.2 fun w hw => hu ⟨w, hw⟩)
  have hpc : ∀ u w : X, polar (Q.comp X.subtype) u w = polar Q (u : V) (w : V) := fun u w => by
    simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
    rfl
  refine ⟨fun u hu => key u fun w => ?_, fun u hu => key u fun w => ?_⟩
  · have := hu w
    rwa [polarBilin_apply_apply, hpc] at this
  · have := hu w
    rwa [polarBilin_apply_apply, hpc, polar_comm] at this

private theorem nondeg_sup {X Y : Submodule K V} (horth : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hX : ∀ v ∈ X, (∀ w ∈ X, polar Q v w = 0) → v = 0)
    (hY : ∀ v ∈ Y, (∀ w ∈ Y, polar Q v w = 0) → v = 0) :
    ∀ v ∈ X ⊔ Y, (∀ w ∈ X ⊔ Y, polar Q v w = 0) → v = 0 := by
  intro v hv h
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
  have hx0 : x = 0 := hX x hx fun w hw => by
    have := h w (Submodule.mem_sup_left hw)
    rwa [polar_add_left, polar_comm Q y w, horth w hw y hy, add_zero] at this
  have hy0 : y = 0 := hY y hy fun w hw => by
    have := h w (Submodule.mem_sup_right hw)
    rwa [polar_add_left, horth x hx w hw, zero_add] at this
  rw [hx0, hy0, add_zero]

private theorem disjoint_of_orth {X Y : Submodule K V}
    (horth : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hX : ∀ v ∈ X, (∀ w ∈ X, polar Q v w = 0) → v = 0) : Disjoint X Y := by
  rw [Submodule.disjoint_def]
  intro v hvX hvY
  exact hX v hvX fun w hw => by rw [polar_comm]; exact horth w hw v hvY

private theorem orth_sup {X Y Z : Submodule K V} (hXY : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hXZ : ∀ x ∈ X, ∀ z ∈ Z, polar Q x z = 0) : ∀ x ∈ X, ∀ w ∈ Y ⊔ Z, polar Q x w = 0 := by
  intro x hx w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
  rw [polar_add_right, hXY x hx y hy, hXZ x hx z hz, add_zero]

private theorem finrank_sup_of_orth [FiniteDimensional K V] {X Y : Submodule K V}
    (horth : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hX : ∀ v ∈ X, (∀ w ∈ X, polar Q v w = 0) → v = 0) :
    finrank K ↥(X ⊔ Y) = finrank K X + finrank K Y := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
  rw [(disjoint_of_orth Q horth hX).eq_bot, finrank_bot, add_zero] at h
  exact h

private theorem isPlusType_sup_iff_of [Finite K] [FiniteDimensional K V] {X Y : Submodule K V}
    (horth : ∀ x ∈ X, ∀ y ∈ Y, polar Q x y = 0)
    (hX : ∀ v ∈ X, (∀ w ∈ X, polar Q v w = 0) → v = 0)
    (hY : ∀ v ∈ Y, (∀ w ∈ Y, polar Q v w = 0) → v = 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hXd : finrank K X = 2 * a) (hYd : finrank K Y = 2 * b) :
    IsPlusType (Q.comp (X ⊔ Y).subtype) ↔
      (IsPlusType (Q.comp X.subtype) ↔ IsPlusType (Q.comp Y.subtype)) := by
  rw [isPlusType_congr (CFSG.RankThree.PartOne.K159.isometryEquivSup Q X Y
    (disjoint_of_orth Q horth hX) horth)]
  exact CFSG.RankThree.PartOne.K159.isPlusType_prod_iff (nondeg_comp_of Q hX) (nondeg_comp_of Q hY)
    ha hb hXd hYd

private def topIsometry : (Q.comp (⊤ : Submodule K V).subtype).IsometryEquiv Q where
  toLinearEquiv := Submodule.topEquiv
  map_app' _ := rfl

end Types

section ThreePlanes

variable [Finite K] (Q : QuadraticForm K (Fin m → K)) {Aε : Subgroup (GL (Fin m) K)}
  [IsMulCommutative Aε] (hp : p.Prime) (hA : ∀ a : ↥Aε, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK in
theorem not_isPlusType_of_three_planes (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    (hp2 : p ≠ 2) (hAεβ : Aε ≤ isomGL (polarBilin Q))
    (hmax : IsMaxElem (polarBilin Q) (glRep Aε) p ∅) [DecidableEq (Hyperplane ↥Aε p)]
    {T : Finset (Hyperplane ↥Aε p)}
    (hT : ∀ H : Hyperplane ↥Aε p, H ∈ T ↔ weightSpace (glRep Aε) H.1 ≠ ⊥) (hTc : T.card = 3)
    (hd : ∀ H ∈ T, finrank K (weightSpace (glRep Aε) H.1) = 2) (hm : m = 8) :
    ¬ IsPlusType Q := by
  classical
  intro hplus
  haveI : Fintype (Hyperplane ↥Aε p) := Fintype.ofFinite _
  set ρ := glRep Aε with hρdef
  have hρ : IsIsomRep (polarBilin Q) ρ := isIsomRep_glRep hAεβ
  have hρQ : ∀ (a : ↥Aε) (v : Fin m → K), Q (ρ a v) = Q v := quad_glRep_apply_of_le Q h2 hAεβ
  have hnd : ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      (∀ w ∈ weightFamily (p := p) ρ i, polar Q v w = 0) → v = 0 :=
    fun i v hv h => nondegenerate_weightFamily ρ hp hA hpK Q hQ hρQ i hv h
  have horthF : ∀ i j : Option (Hyperplane ↥Aε p), i ≠ j → ∀ v ∈ weightFamily (p := p) ρ i,
      ∀ w ∈ weightFamily (p := p) ρ j, polar Q v w = 0 :=
    fun i j hij v hv w hw => polar_eq_zero_of_mem_weightFamily ρ hp hA hpK Q hρQ hij hv hw
  obtain ⟨H₁, H₂, H₃, h12, h13, h23, hTeq⟩ := Finset.card_eq_three.1 hTc
  have hH₁ : H₁ ∈ T := by rw [hTeq]; simp
  have hH₂ : H₂ ∈ T := by rw [hTeq]; simp
  have hH₃ : H₃ ∈ T := by rw [hTeq]; simp
  set W₀ := fixedSpace ρ ⊤ with hW₀def
  have hW₀F : W₀ = weightFamily (p := p) ρ none := (weightFamily_none ρ hp hA hpK).symm
  have hsum : ∑ H : Hyperplane ↥Aε p, finrank K (weightSpace ρ H.1) = 6 := by
    rw [← Finset.sum_subset (Finset.subset_univ T) (fun H _ hH => by
      have hbot : weightSpace ρ H.1 = ⊥ := by
        by_contra hne
        exact hH ((hT H).2 hne)
      rw [hbot, finrank_bot]), hTeq, Finset.sum_insert (by simp [h12, h13]),
      Finset.sum_pair h23, hd H₁ hH₁, hd H₂ hH₂, hd H₃ hH₃]
    norm_num
  have hW₀d : finrank K W₀ = 2 := by
    have h : finrank K (Fin m → K) = finrank K W₀ +
        ∑ H : Hyperplane ↥Aε p, finrank K (weightSpace ρ H.1) :=
      finrank_eq_fixedSpace_add_sum ρ hp hA hpK
    rw [hsum, Module.finrank_fin_fun] at h
    omega
  have hty : ∀ H ∈ T, (IsPlusType (Q.comp (weightSpace ρ H.1).subtype) →
      (p : ℤ) ∣ (Nat.card K : ℤ) - 1) ∧ (¬ IsPlusType (Q.comp (weightSpace ρ H.1).subtype) →
      (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := fun H hH =>
    CFSG.LocalAnalysis.GLTheoremA.H81Orth.int_dvd_of_weightPlane ρ hp hA hpK Q hQ hρQ hp2
      ((hT H).1 hH) (hd H hH)
  have hboth : ¬ ((p : ℤ) ∣ (Nat.card K : ℤ) - 1 ∧ (p : ℤ) ∣ (Nat.card K : ℤ) + 1) := by
    rintro ⟨h1, h1'⟩
    have h3 : (p : ℤ) ∣ ((Nat.card K : ℤ) + 1) - ((Nat.card K : ℤ) - 1) := dvd_sub h1' h1
    rw [show ((Nat.card K : ℤ) + 1) - ((Nat.card K : ℤ) - 1) = 2 by ring] at h3
    have h4 : p ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  have hsame : ∀ H ∈ T, (IsPlusType (Q.comp (weightSpace ρ H.1).subtype) ↔
      IsPlusType (Q.comp (weightSpace ρ H₁.1).subtype)) := by
    intro H hH
    obtain ⟨a1, a2⟩ := hty H hH
    obtain ⟨b1, b2⟩ := hty H₁ hH₁
    by_cases hx : IsPlusType (Q.comp (weightSpace ρ H.1).subtype) <;>
      by_cases hy : IsPlusType (Q.comp (weightSpace ρ H₁.1).subtype)
    · exact iff_of_true hx hy
    · exact absurd ⟨a1 hx, b2 hy⟩ hboth
    · exact absurd ⟨b1 hy, a2 hx⟩ hboth
    · exact iff_of_false hx hy
  have hndW₀ : ∀ v ∈ W₀, (∀ w ∈ W₀, polar Q v w = 0) → v = 0 := by
    rw [hW₀F]; exact hnd none
  have hndV : ∀ H : Hyperplane ↥Aε p, ∀ v ∈ weightSpace ρ H.1,
      (∀ w ∈ weightSpace ρ H.1, polar Q v w = 0) → v = 0 := fun H => hnd (some H)
  have hoV : ∀ H H' : Hyperplane ↥Aε p, H ≠ H' → ∀ v ∈ weightSpace ρ H.1,
      ∀ w ∈ weightSpace ρ H'.1, polar Q v w = 0 := fun H H' h =>
    horthF (some H) (some H') (fun e => h (Option.some_injective _ e))
  have hoW₀ : ∀ H : Hyperplane ↥Aε p, ∀ v ∈ W₀, ∀ w ∈ weightSpace ρ H.1, polar Q v w = 0 := by
    intro H
    rw [hW₀F]
    exact horthF none (some H) (Option.some_ne_none H).symm
  have hX23 := isPlusType_sup_iff_of Q (hoV H₂ H₃ h23) (hndV H₂) (hndV H₃) le_rfl le_rfl
    (by rw [hd H₂ hH₂]) (by rw [hd H₃ hH₃])
  have h23plus : IsPlusType (Q.comp (weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1).subtype) :=
    hX23.2 ((hsame H₂ hH₂).trans (hsame H₃ hH₃).symm)
  have ho1 := orth_sup Q (hoV H₁ H₂ h12) (hoV H₁ H₃ h13)
  have hnd23 := nondeg_sup Q (hoV H₂ H₃ h23) (hndV H₂) (hndV H₃)
  have hd23 : finrank K ↥(weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1) = 2 * 2 := by
    rw [finrank_sup_of_orth Q (hoV H₂ H₃ h23) (hndV H₂), hd H₂ hH₂, hd H₃ hH₃]
  have hX123 := isPlusType_sup_iff_of Q ho1 (hndV H₁) hnd23 (le_rfl : 1 ≤ 1)
    (by norm_num : 1 ≤ 2) (by rw [hd H₁ hH₁]) hd23
  have h123 : IsPlusType (Q.comp (weightSpace ρ H₁.1 ⊔
      (weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1)).subtype) ↔
      IsPlusType (Q.comp (weightSpace ρ H₁.1).subtype) := by
    rw [hX123]
    exact ⟨fun h => h.2 h23plus, fun h => ⟨fun _ => h23plus, fun _ => h⟩⟩
  have ho0 := orth_sup Q (hoW₀ H₁) (orth_sup Q (hoW₀ H₂) (hoW₀ H₃))
  have hnd123 := nondeg_sup Q ho1 (hndV H₁) hnd23
  have hd123 : finrank K ↥(weightSpace ρ H₁.1 ⊔ (weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1)) =
      2 * 3 := by
    rw [finrank_sup_of_orth Q ho1 (hndV H₁), hd H₁ hH₁, hd23]
  have hX0 := isPlusType_sup_iff_of Q ho0 hndW₀ hnd123 (le_rfl : 1 ≤ 1) (by norm_num : 1 ≤ 3)
    (by rw [hW₀d]) hd123
  have htop : W₀ ⊔ (weightSpace ρ H₁.1 ⊔ (weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1)) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_sup_of_orth Q ho0 hndW₀, hW₀d, hd123, Module.finrank_fin_fun]
    omega
  have hplus' : IsPlusType (Q.comp (W₀ ⊔ (weightSpace ρ H₁.1 ⊔
      (weightSpace ρ H₂.1 ⊔ weightSpace ρ H₃.1))).subtype) := by
    rw [htop]
    exact (isPlusType_congr (topIsometry Q)).2 hplus
  have hW₀type : IsPlusType (Q.comp W₀.subtype) ↔
      IsPlusType (Q.comp (weightSpace ρ H₁.1).subtype) := by
    rw [← h123]
    exact hX0.1 hplus'
  set QW := Q.comp W₀.subtype with hQWdef
  have hQW : (polarBilin QW).Nondegenerate := nondeg_comp_of Q hndW₀
  have hpO : (p : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup QW) : ℤ) := by
    obtain ⟨b1, b2⟩ := hty H₁ hH₁
    have hd0 : finrank K W₀ = 2 * (0 + 1) := by rw [hW₀d]
    by_cases h1 : IsPlusType (Q.comp (weightSpace ρ H₁.1).subtype)
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQW hd0
        (Or.inl ⟨rfl, hW₀type.2 h1⟩)]
      simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one,
        Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty]
      exact dvd_mul_of_dvd_right (b1 h1) 2
    · rw [CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hQW hd0
        (Or.inr ⟨rfl, fun h => h1 (hW₀type.1 h)⟩)]
      simp only [zero_mul, pow_zero, mul_one, zero_add, pow_one,
        Finset.Icc_eq_empty_of_lt zero_lt_one, Finset.prod_empty, sub_neg_eq_add]
      exact dvd_mul_of_dvd_right (b2 h1) 2
  have hpO' : p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup QW) := by exact_mod_cast hpO
  haveI : Finite (W₀ ≃ₗ[K] W₀) :=
    Finite.of_injective (fun g : W₀ ≃ₗ[K] W₀ => (g : W₀ → W₀)) DFunLike.coe_injective
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpO'
  set g' : W₀ ≃ₗ[K] W₀ := (g : W₀ ≃ₗ[K] W₀) with hg'def
  have hg'Q : ∀ w, QW (g' w) = QW w := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 g.2
  have hg'p : g' ^ p = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    exact congrArg Subtype.val h
  have hg'1 : g' ≠ 1 := by
    intro h
    have : g = 1 := Subtype.ext h
    rw [this, orderOf_one] at hg
    exact hp.one_lt.ne hg
  set U := wtW Aε T with hUdef
  have hker : wtU Aε T = W₀ := wtU_eq_fixedSpace hp hA hpK hT
  have hc : IsCompl W₀ U := hker ▸ isCompl_ker_range_projI ρ hp hA hpK T
  set e := Submodule.prodEquivOfIsCompl W₀ U hc with hedef
  set G : (Fin m → K) ≃ₗ[K] (Fin m → K) :=
    e.symm.trans ((g'.prodCongr (LinearEquiv.refl K U)).trans e) with hGdef
  have hGw : ∀ (w : Fin m → K) (hw : w ∈ W₀), G w = (g' ⟨w, hw⟩ : Fin m → K) := by
    intro w hw
    have h1 : e.symm w = (⟨w, hw⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left W₀ U hc ⟨w, hw⟩
    rw [hGdef, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
    simp [hedef, Submodule.coe_prodEquivOfIsCompl']
  have hGw' : ∀ w : W₀, G w = (g' w : Fin m → K) := fun w => hGw w w.2
  have hGu : ∀ u ∈ U, G u = u := by
    intro u hu
    have h1 : e.symm u = (0, ⟨u, hu⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right W₀ U hc ⟨u, hu⟩
    rw [hGdef, LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
    simp [hedef, Submodule.coe_prodEquivOfIsCompl']
  have hdec : ∀ x : Fin m → K, ∃ w : W₀, ∃ u : U, x = (w : Fin m → K) + u := by
    intro x
    obtain ⟨⟨w, u⟩, rfl⟩ := e.surjective x
    exact ⟨w, u, by simp [hedef, Submodule.coe_prodEquivOfIsCompl']⟩
  have hGwu : ∀ (w : W₀) (u : U), G ((w : Fin m → K) + u) = (g' w : Fin m → K) + u := by
    intro w u
    rw [map_add, hGw w w.2, hGu u u.2]
  have hoWU : ∀ w ∈ W₀, ∀ u ∈ U, polar Q w u = 0 := fun w hw u hu =>
    polar_wtU_wtW Q hp hA hpK hAεβ T (hker ▸ hw) hu
  have hsplit : ∀ a ∈ W₀, ∀ a' ∈ W₀, ∀ b ∈ U, ∀ b' ∈ U,
      polar Q (a + b) (a' + b') = polar Q a a' + polar Q b b' := by
    intro a ha a' ha' b hb b' hb'
    rw [polar_add_left, polar_add_right, polar_add_right, hoWU a ha b' hb',
      polar_comm Q b a', hoWU a' ha' b hb]
    ring
  have hGiso : ∀ x y, polarBilin Q (G x) (G y) = polarBilin Q x y := by
    intro x y
    obtain ⟨w, u, rfl⟩ := hdec x
    obtain ⟨w', u', rfl⟩ := hdec y
    have hpc : ∀ a b : W₀, polar QW a b = polar Q (a : Fin m → K) (b : Fin m → K) := fun a b => by
      simp only [hQWdef, QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
      rfl
    have hg'pol : polar Q (g' w : Fin m → K) (g' w' : Fin m → K) =
        polar Q (w : Fin m → K) (w' : Fin m → K) := by
      rw [← hpc, ← hpc]
      simp only [QuadraticMap.polar, ← map_add, hg'Q]
    rw [hGwu, hGwu, polarBilin_apply_apply, polarBilin_apply_apply,
      hsplit _ (g' w).2 _ (g' w').2 _ u.2 _ u'.2, hsplit _ w.2 _ w'.2 _ u.2 _ u'.2, hg'pol]
  have hρU : ∀ (a : ↥Aε), ∀ u ∈ U, ρ a u ∈ U := by
    rintro a _ ⟨v, rfl⟩
    refine ⟨ρ a v, ?_⟩
    have := projI_comm_of_preserves ρ hp hA hpK T (ρ a).toAddMonoidHom
      (fun i v hv => glRep_mem_wf a i hv) v
    simpa only [LinearMap.toAddMonoidHom_coe] using this
  have hρW₀ : ∀ (a : ↥Aε), ∀ w ∈ W₀, ρ a w = w := fun a w hw =>
    (mem_fixedSpace ρ).1 hw a (Subgroup.mem_top a)
  have hGρ : ∀ (a : ↥Aε) (v : Fin m → K), G (ρ a v) = ρ a (G v) := by
    intro a v
    obtain ⟨w, u, rfl⟩ := hdec v
    have h1 : G (ρ a u) = ρ a u := hGu _ (hρU a u u.2)
    calc G (ρ a ((w : Fin m → K) + u)) = G w + G (ρ a u) := by
          rw [map_add, hρW₀ a w w.2, map_add]
      _ = (g' w : Fin m → K) + ρ a u := by rw [hGw' w, h1]
      _ = ρ a (G ((w : Fin m → K) + u)) := by rw [hGwu, map_add, hρW₀ a _ (g' w).2]
  have hGpow : ∀ n : ℕ, ∀ (w : W₀) (u : U),
      (G ^ n) ((w : Fin m → K) + u) = ((g' ^ n) w : Fin m → K) + u := by
    intro n
    induction n with
    | zero => intro w u; simp
    | succ n ih =>
      intro w u
      rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', LinearEquiv.mul_apply]
      exact hGwu _ u
  have hGp : ∀ v, (G ^ p) v = v := by
    intro v
    obtain ⟨w, u, rfl⟩ := hdec v
    rw [hGpow, hg'p, LinearEquiv.coe_one, id]
  have hGW : ∀ H : Hyperplane ↥Aε p, ∀ v ∈ weightSpace ρ H.1, G v = v := by
    intro H v hv
    by_cases hH : H ∈ T
    · exact hGu v ⟨v, projI_apply_of_mem ρ hp hA hpK hH hv⟩
    · have hbot : weightSpace ρ H.1 = ⊥ := by
        by_contra hne
        exact hH ((hT H).2 hne)
      rw [hbot, Submodule.mem_bot] at hv
      rw [hv, map_zero]
  have hG1 := fixed_of_supported (polarBilin Q) ρ hp hA hpK hρ hQ.1 hmax G hGiso hGp
    (fun s hs => absurd hs (Set.notMem_empty s)) hGW
  apply hg'1
  refine LinearEquiv.ext fun w => Subtype.ext ?_
  have hw := hGw' w
  rw [hG1] at hw
  exact hw.symm

end ThreePlanes

section Pair

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem concA_of_pair_orth [Fintype K] (hp : p.Prime) (hp2 : p ≠ 2) [hSn : S.Normal]
    (hB : IsElemAbelian p B) (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hodd : Odd (Nat.card K)) (h2 : (2 : K) ≠ 0)
    (hpK : (p : K) ≠ 0) (Q : QuadraticForm K (Fin m → K)) (hQ : (polarBilin Q).Nondegenerate)
    (Dat : ClsInner p S B (matrixDerived Q) (polarBilin Q)) {Aε : Subgroup (GL (Fin m) K)}
    [IsMulCommutative Aε] (hA : ∀ a : ↥Aε, a ^ p = 1) (hAεL : Aε = liftGroup Dat)
    (hAεβ : Aε ≤ isomGL (polarBilin Q)) (hAε𝒮 : Aε ≤ centGL (fieldSet Dat))
    (hmaxE : IsMaxElem (polarBilin Q) (glRep Aε) p (fieldSet Dat))
    [DecidableEq (Hyperplane ↥Aε p)] {Ha Hb H₀ : Hyperplane ↥Aε p} (hab : Ha ≠ Hb)
    (ha0 : Ha ≠ H₀) (hb0 : Hb ≠ H₀) (hWa : weightSpace (glRep Aε) Ha.1 ≠ ⊥)
    (hWb : weightSpace (glRep Aε) Hb.1 ≠ ⊥) (hW₀ : weightSpace (glRep Aε) H₀.1 ≠ ⊥)
    (hcardA : p ^ 3 ≤ Nat.card ↥Aε) (hrank : p ^ 5 ≤ Nat.card B)
    (hzH : glEquiv.symm (invol (glRep Aε) hp hA hpK {Ha, Hb}) ∈ matrixDerived Q)
    (hdim : 5 ≤ finrank K (wtU Aε {Ha, Hb})) : S267ConcA p S B := by
  classical
  set ρ := glRep Aε with hρdef
  set I : Finset (Hyperplane ↥Aε p) := {Ha, Hb} with hIdef
  set U := wtU Aε I with hUdef
  set W := wtW Aε I with hWdef
  have hρ : IsIsomRep (polarBilin Q) ρ := isIsomRep_glRep hAεβ
  have hρQ : ∀ (a : ↥Aε) (v : Fin m → K), Q (ρ a v) = Q v := quad_glRep_apply_of_le Q h2 hAεβ
  have h𝒮 : ∀ s ∈ fieldSet Dat, ∀ a v, s (ρ a v) = ρ a (s v) := by
    intro s hs a v
    rw [glRep_apply_eq_glEquiv, glRep_apply_eq_glEquiv]
    exact ((mem_centGL.mp (hAε𝒮 a.2)) s hs v).symm
  have h𝒮W : ∀ s ∈ fieldSet Dat, ∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      s v ∈ weightFamily (p := p) ρ i := by
    rintro s ⟨hF, rfl⟩ i v hv
    exact preserves_weightFamily_of_semilinear ρ (Dat.σ : K →+* K) _
      (fun c v => ModelGen.semiMap_smul Dat.A Dat.σ c v) (h𝒮 _ ⟨hF, rfl⟩) i hv
  have hUW : IsCompl U W := isCompl_ker_range_projI ρ hp hA hpK I
  have horth : ∀ u ∈ U, ∀ w ∈ W, polarBilin Q u w = 0 ∧ polarBilin Q w u = 0 := by
    intro u hu w hw
    have h := polar_wtU_wtW Q hp hA hpK hAεβ I hu hw
    refine ⟨by rw [polarBilin_apply_apply]; exact h, ?_⟩
    rw [polarBilin_apply_apply, polar_comm]
    exact h
  have hnd : ∀ u ∈ U, (∀ u' ∈ U, polarBilin Q u u' = 0) → u = 0 := fun u hu h =>
    nondeg_wtU Q hp hA hpK hQ hAεβ I hu fun u' hu' => by
      rw [← polarBilin_apply_apply]; exact h u' hu'
  have h0I : H₀ ∉ I := by
    simp only [hIdef, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha0, Ne.symm hb0⟩
  have hpresU : ∀ f : (Fin m → K) →+ (Fin m → K), (∀ i, ∀ v ∈ weightFamily (p := p) ρ i,
      f v ∈ weightFamily (p := p) ρ i) → ∀ u ∈ U, f u ∈ U := by
    intro f hf u hu
    rw [hUdef, LinearMap.mem_ker] at hu ⊢
    rw [projI_comm_of_preserves ρ hp hA hpK I f hf, hu, map_zero]
  have hidx : (⨅ H ∈ I, H.1).index = p ^ I.card :=
    index_biInf_eq (polarBilin Q) ρ hp hA hpK hρ hmaxE h𝒮 h𝒮W I (by
      intro H hH
      simp only [hIdef, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact hWa
      · exact hWb)
  rw [Finset.card_pair hab] at hidx
  obtain ⟨x, hxI, hx1⟩ : ∃ x ∈ ⨅ H ∈ I, H.1, x ≠ 1 := by
    have hcard := Subgroup.card_mul_index (⨅ H ∈ I, H.1)
    rw [hidx] at hcard
    by_contra hcon
    push Not at hcon
    have hbot : (⨅ H ∈ I, H.1) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    rw [hbot, Subgroup.card_bot, one_mul] at hcard
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hxH : ∀ H ∈ I, x ∈ H.1 := fun H hH => by
    have := hxI
    rw [Subgroup.mem_iInf] at this
    exact (Subgroup.mem_iInf.1 (this H)) hH
  have hxW : ∀ w ∈ W, glEquiv (x : GL (Fin m) K) w = w := by
    rintro _ ⟨v, rfl⟩
    rw [← glRep_apply_eq_glEquiv, projI_apply, map_sum]
    refine Finset.sum_congr rfl fun H hH => ?_
    exact apply_eq_of_mem_weightSpace ρ (hxH H hH) ⟨v, rfl⟩
  have hxblk : (x : GL (Fin m) K) ∈ blkSub (polarBilin Q) U W := by
    refine ⟨hAεβ x.2, fun u hu => ?_, hxW⟩
    have := hpresU (ρ x).toAddMonoidHom (fun i v hv => glRep_mem_wf x i hv) u hu
    simpa only [LinearMap.toAddMonoidHom_coe, hρdef, glRep_apply_eq_glEquiv] using this
  have hxord : orderOf (x : GL (Fin m) K) = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (by rw [← Subgroup.coe_pow, hA x, Subgroup.coe_one])
      (fun h => hx1 (Subtype.ext h))
  have h3 : 3 ≤ finrank K U := by omega
  have hscal : ∀ y ∈ Aε, ∀ c : K, (∀ u ∈ U, glEquiv y u = c • u) → c = 1 := by
    intro y hy c hc
    obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₀
    have hw₀U : w₀ ∈ U := by
      rw [hUdef, LinearMap.mem_ker]
      refine projI_apply_of_not_mem ρ hp hA hpK (fun H hH h => h0I ?_) (by
        rw [weightFamily_some]; exact hw₀)
      rw [Option.some.inj h]
      exact hH
    obtain ⟨u, huU, hQu⟩ : ∃ u ∈ U, Q u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hw₀0
      refine hnd w₀ hw₀U fun u' hu' => ?_
      rw [polarBilin_apply_apply, polar, hcon _ (U.add_mem hw₀U hu'), hcon _ hw₀U,
        hcon _ hu', sub_zero, sub_zero]
    have hyQ : Q (glEquiv y u) = Q u := quad_glRep_apply_of_le Q h2 hAεβ ⟨y, hy⟩ u
    rw [hc u huU, QuadraticMap.map_smul, smul_eq_mul] at hyQ
    have hc2 : c * c = 1 := by
      have := mul_right_cancel₀ hQu (hyQ.trans (one_mul _).symm)
      exact this
    have hcp : c ^ p = 1 := by
      have hu0 : u ≠ 0 := fun h => hQu (by rw [h, QuadraticMap.map_zero])
      have hpow : ∀ n : ℕ, glEquiv (y ^ n) u = c ^ n • u := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, map_mul, LinearEquiv.mul_apply, hc u huU, map_smul, ih, smul_smul,
            pow_succ, mul_comm]
      have hyp : y ^ p = 1 := by
        have := hA ⟨y, hy⟩
        exact congrArg Subtype.val this
      have h1 := hpow p
      rw [hyp, map_one, LinearEquiv.coe_one, id] at h1
      by_contra hne
      apply hu0
      have : (1 - c ^ p) • u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm hne))
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rw [hk, pow_succ, pow_mul, _root_.sq, hc2, one_pow, one_mul] at hcp
    exact hcp
  refine concA_of_weights hp hB hBC hcore h2 hpK Dat (ModelGen.matrixDerived_le_isomGL Q) hA hAεL
    hAεβ hAε𝒮 hmaxE I (by
      intro H hH
      simp only [hIdef, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact hWa
      · exact hWb) (by rw [Finset.card_pair hab]; norm_num) h0I hW₀
    (by rw [Finset.card_pair hab]; exact hrank) hzH (blkI_le_matrixDerived h2 Q U W)
    (isQuasisimple_blkI_polarBilin hodd Q hUW horth hnd (Or.inl hdim))
    (dvd_card_blkI_polarBilin hodd Q hUW horth hnd hp hp2 hxblk hxord)
    (fun y hyU hy => exists_smul_of_commute_blkI_polarBilin hodd Q hUW horth hnd h3 hyU hy)
    (fun hF y hyU _ k hk0 hkp => not_forall_semiConj_pow_polarBilin hodd Q hUW horth hnd h3
      hF.2.2.2.2.1.1 (fun u hu => hpresU (ModelGen.semiMap Dat.A Dat.σ).toAddMonoidHom
        (h𝒮W _ ⟨hF, rfl⟩) u hu) hyU hk0 hkp)
    hscal (fun h => absurd h (by rw [Finset.card_pair hab]; norm_num))

end Pair

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
