module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

@[expose] noncomputable def projLiftHom (hQ' : ∃ v, Q v ≠ 0) :
    matrixProjectiveDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (orthDerived Q).subtype.comp
    (MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ', projHom_surjective Q⟩).symm.toMonoidHom

omit [Finite K] in
theorem projLiftHom_apply (hQ' : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    projLiftHom hQ' x = projLift hQ' x := rfl

omit [Finite K] in
theorem projLiftHom_injective (hQ' : ∃ v, Q v ≠ 0) : Function.Injective (projLiftHom hQ') :=
  (orthDerived Q).subtype_injective.comp (MulEquiv.injective _)

omit [Finite K] in
theorem projLift_mem_orthDerived (hQ' : ∃ v, Q v ≠ 0) (x : matrixProjectiveDerived Q) :
    projLift hQ' x ∈ orthDerived Q :=
  ((MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ', projHom_surjective Q⟩).symm x).2

theorem fixW_of_mem_rootLeviBar_of_commute (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hZ : center (stabPairsBar Q a a' b b') = ⊥) {m : matrixProjectiveDerived Q}
    (hm : m ∈ rootLeviBar Q ha.hypPair hb.hypPair)
    (hmB : m ∈ centralizer (stabPairsBar Q a a' b b' : Set (matrixProjectiveDerived Q))) :
    ∀ x, InW ha.hypPair hb.hypPair x → projLift ha.exists_ne_zero m x = x := by
  have h₁₂ := ha.orth hb hd
  have hQ' := ha.exists_ne_zero
  set M := projLift hQ' m with hMdef
  have hML : M ∈ rootLevi Q ha.hypPair hb.hypPair := projLift_mem_of_mem_map hQ' hm
  have hMΩ : M ∈ orthDerived Q := projLift_mem_orthDerived hQ' m
  have hMc := mem_centralizer_singleton_iff.mp hML.1.2
  obtain ⟨g1, g2⟩ := apply_e_eq_coeff h₁₂ hMc
  have hdet := det_coeff_eq_one h₁₂ hML.1.1 hMc
  set H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
    orthDerived Q ⊓ rootLevi Q ha.hypPair hb.hypPair ⊓
      fixPtSub K {x | InW ha.hypPair hb.hypPair x} with hH
  have hx : ∀ t : K, eichler Q ha.hypPair.e (t • hb.hypPair.f) ∈ H := fun t =>
    ⟨⟨eichler_mem_orthDerived hQ hT _ _, eichler_smul_f_mem_rootLevi h₁₂ t⟩,
      mem_fixPtSub.mpr fun x hx => eichler_apply_of_polar_eq_zero
        (by rw [polar_comm]; exact hx.1)
        (by rw [polar_smul_right_eq, polar_comm, hx.2.2.2, mul_zero])⟩
  have hy : ∀ t : K, eichler Q hb.hypPair.e (t • ha.hypPair.f) ∈ H := fun t =>
    ⟨⟨eichler_mem_orthDerived hQ hT _ _, eichler_smul_f_mem_rootLevi' h₁₂ t⟩,
      mem_fixPtSub.mpr fun x hx => eichler_apply_of_polar_eq_zero
        (by rw [polar_comm]; exact hx.2.2.1)
        (by rw [polar_smul_right_eq, polar_comm, hx.2.1, mul_zero])⟩
  obtain ⟨m₁, hm₁, hm₁1, hm₁2⟩ := exists_word h₁₂ H hx hy hdet
  have hm₁Ω : m₁ ∈ orthDerived Q := hm₁.1.1
  have hm₁L : m₁ ∈ rootLevi Q ha.hypPair hb.hypPair := hm₁.1.2
  have hm₁W : ∀ x, InW ha.hypPair hb.hypPair x → m₁ x = x := fun x hx => mem_fixPtSub.mp hm₁.2 x hx
  set n := m₁⁻¹ * M with hn
  have hnL : n ∈ rootLevi Q ha.hypPair hb.hypPair := mul_mem (inv_mem hm₁L) hML
  have hnΩ : n ∈ orthDerived Q := mul_mem (inv_mem hm₁Ω) hMΩ
  have n1 : n ha.hypPair.e = ha.hypPair.e := by
    rw [hn, LinearEquiv.mul_apply, g1, ← hm₁1, LinearEquiv.inv_apply_apply']
  have n2 : n hb.hypPair.e = hb.hypPair.e := by
    rw [hn, LinearEquiv.mul_apply, g2, ← hm₁2, LinearEquiv.inv_apply_apply']
  obtain ⟨n3, n4⟩ := apply_f_of_mem_rootLevi h₁₂ hnL n1 n2
  have hnB : projHom Q ⟨n, hnΩ⟩ ∈ stabPairsBar Q a a' b b' :=
    ⟨⟨n, hnΩ⟩, mem_subgroupOf.mpr ⟨⟨n1, n3⟩, n2, n4⟩, rfl⟩
  have hm₁c : ∀ x ∈ stabPairsBar Q a a' b b',
      projHom Q ⟨m₁, hm₁Ω⟩ * x = x * projHom Q ⟨m₁, hm₁Ω⟩ := by
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨⟨x1, x3⟩, x2, x4⟩ := mem_subgroupOf.mp hX
    have hXO : (X : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      Subgroup.commutator_le_self _ X.2
    have hf := orth_flipPair_flipPair h₁₂
    obtain ⟨k1, k2⟩ := apply_e_eq_coeff h₁₂ (mem_centralizer_singleton_iff.mp hm₁L.1.2)
    obtain ⟨l1, l2⟩ := apply_e_eq_coeff hf (mem_centralizer_singleton_iff.mp hm₁L.2)
    simp only [flipPair_e, flipPair_f] at l1 l2
    have hXU : ∀ α β γ δ : K, (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
        (α • ha.hypPair.e + β • hb.hypPair.e + (γ • ha.hypPair.f + δ • hb.hypPair.f)) =
        α • ha.hypPair.e + β • hb.hypPair.e + (γ • ha.hypPair.f + δ • hb.hypPair.f) := by
      intro α β γ δ
      simp only [map_add, map_smul, IsHypCoord.hypPair_e, IsHypCoord.hypPair_f, x1, x2, x3, x4]
    have hXP : ∀ α β : K, (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
        (α • ha.hypPair.e + β • hb.hypPair.e) = α • ha.hypPair.e + β • hb.hypPair.e := by
      intro α β
      simp only [map_add, map_smul, IsHypCoord.hypPair_e, x1, x2]
    have hXP' : ∀ α β : K, (X : (Fin d → K) ≃ₗ[K] (Fin d → K))
        (α • ha.hypPair.f + β • hb.hypPair.f) = α • ha.hypPair.f + β • hb.hypPair.f := by
      intro α β
      simp only [map_add, map_smul, IsHypCoord.hypPair_f, x3, x4]
    have hcomm := commute_of_fixW_of_fix (g := m₁) (h := (X : (Fin d → K) ≃ₗ[K] (Fin d → K)))
      h₁₂ hm₁W hXO ⟨x1, x3, x2, x4⟩
      ⟨by rw [k1]; exact hXP _ _, by rw [l1]; exact hXP' _ _, by rw [k2]; exact hXP _ _,
        by rw [l2]; exact hXP' _ _⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hρn : projHom Q ⟨n, hnΩ⟩ = (projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ * m := by
    have : (⟨n, hnΩ⟩ : orthDerived Q) = (⟨m₁, hm₁Ω⟩ : orthDerived Q)⁻¹ * ⟨M, hMΩ⟩ := rfl
    rw [this, map_mul, map_inv]
    congr 1
    exact projHom_projLift hQ' m
  have hcen : (⟨projHom Q ⟨n, hnΩ⟩, hnB⟩ : stabPairsBar Q a a' b b') ∈
      center (stabPairsBar Q a a' b b') := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hρn]
    have h1 := hm₁c x x.2
    have h2 := mem_centralizer_iff.mp hmB x x.2
    have h1' : (projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ * (x : matrixProjectiveDerived Q) =
        (x : matrixProjectiveDerived Q) * (projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_assoc, mul_inv_cancel, mul_one]
    calc (x : matrixProjectiveDerived Q) * ((projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ * m)
        = (projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ * (x * m) := by rw [← mul_assoc, ← h1', mul_assoc]
      _ = (projHom Q ⟨m₁, hm₁Ω⟩)⁻¹ * m * x := by rw [h2, mul_assoc]
  rw [hZ, mem_bot] at hcen
  have hn1 : projHom Q ⟨n, hnΩ⟩ = 1 := congrArg Subtype.val hcen
  have hn1' : n = 1 := by
    have := projHom_injective hQ' (hn1.trans (map_one (projHom Q)).symm)
    exact congrArg Subtype.val this
  have hMm : M = m₁ := by
    rw [hn] at hn1'
    exact (inv_mul_eq_one.mp hn1').symm
  intro x hx
  rw [hMm]
  exact hm₁W x hx

theorem le_centralizer_of_model (ha : IsHypCoord Q a a') (hb : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') (hQ : (polarBilin Q).Nondegenerate) {P₃ : HypPair Q}
    (h₁₃ : ha.hypPair.Orth P₃) (h₂₃ : hb.hypPair.Orth P₃)
    (hZ : center (stabPairsBar Q a a' b b') = ⊥) {y : matrixProjectiveDerived Q}
    (hyM : y ∈ rootLeviBar Q ha.hypPair hb.hypPair)
    (hyB : y ∈ centralizer (stabPairsBar Q a a' b b' : Set (matrixProjectiveDerived Q)))
    (hy1 : y ≠ 1) (hyo : Odd (orderOf y)) {S R : Subgroup (matrixProjectiveDerived Q)}
    (hSy : S ≤ centralizer {y})
    (hSgen : ∀ N : Subgroup (matrixProjectiveDerived Q),
      rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃ ∈ N → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) → S ≤ N)
    (hRz : R ≤ centralizer {rootPairElt hQ (ha.orth hb hd) h₁₃ h₂₃})
    (hRy : R ≤ centralizer {y}) (hRperf : ⁅R, R⁆ = R) :
    S ≤ centralizer (R : Set (matrixProjectiveDerived Q)) := by
  have h₁₂ := ha.orth hb hd
  have hT := exists_totallySingular_of_hypPairs h₁₂ h₁₃ h₂₃
  have hQ' := ha.exists_ne_zero
  set φ := projLiftHom hQ' with hφ
  have hφi := projLiftHom_injective hQ'
  have hgL : φ y ∈ rootLevi Q ha.hypPair hb.hypPair := projLift_mem_of_mem_map hQ' hyM
  have hgW := fixW_of_mem_rootLeviBar_of_commute ha hb hd hQ hT hZ hyM hyB
  have hgm : φ y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hg1 : φ y ≠ 1 := fun h => hy1 (hφi (h.trans (map_one φ).symm))
  have hz : φ (rootPairElt hQ h₁₂ h₁₃ h₂₃) = eichler Q ha.hypPair.e hb.hypPair.e := by
    rw [projLiftHom_apply, rootPairElt, projLift_projHom]
  have hcomm : ∀ {u v : matrixProjectiveDerived Q}, u * v = v * u → φ u * φ v = φ v * φ u :=
    fun h => by rw [← map_mul, ← map_mul, h]
  intro s hs
  rw [mem_centralizer_iff]
  intro r hr
  have key := commute_of_model h₁₂ hgL hgW hyo hgm hg1 (S := S.map φ) (R := R.map φ)
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hSy hu))))
    (by
      intro N hzN hN
      rw [Subgroup.map_le_iff_le_comap]
      refine hSgen _ (by rw [Subgroup.mem_comap, hz]; exact hzN) ?_
      intro u hu n hn
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hN _ ⟨u, hu, rfl⟩ _ hn)
    (by
      rintro _ ⟨u, -, rfl⟩
      exact Subgroup.commutator_le_self _ (projLift_mem_orthDerived hQ' u))
    (by
      rintro _ ⟨u, hu, rfl⟩
      rw [← hz]
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hRz hu))))
    (by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_centralizer_singleton_iff.mpr (hcomm (mem_centralizer_singleton_iff.mp (hRy hu))))
    (by rw [← Subgroup.map_commutator, hRperf]) ⟨s, hs, rfl⟩ ⟨r, hr, rfl⟩
  rw [← map_mul, ← map_mul] at key
  exact (hφi key).symm

end Model

end CFSG.SeitzReduction.OmegaPilot
