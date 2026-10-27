module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

abbrev D4Mat : Type := Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ

@[expose] def d4MatShort : D4Mat :=
  !![-1, 0, 1, 0; 0, -1, 1, 0; 0, 0, 1, 0; 0, 0, 1, -1]

@[expose] def d4MatLong : D4Mat :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 1, 1, -1, 1; 0, 0, 0, 1]

@[expose] def d4MatThreeA : D4Mat :=
  !![0, -1, 1, -1; -1, 0, 1, -1; -1, -1, 1, -1; -1, -1, 1, 0]

@[expose] def d4MatThreeB : D4Mat :=
  !![1, 0, -1, 0; 0, 1, -1, 0; 1, 1, -2, 1; 0, 0, -1, 1]

@[expose] def d4MatGroup : List D4Mat :=
  [1, d4MatShort, d4MatLong,
   !![-1, 0, 1, 0; 0, -1, 1, 0; -1, -1, 2, -1; 0, 0, 1, -1],
   !![0, 1, -1, 1; 1, 0, -1, 1; 1, 1, -1, 1; 1, 1, -1, 0],
   !![0, -1, 1, -1; -1, 0, 1, -1; -1, -1, 2, -1; -1, -1, 1, 0],
   !![0, 1, -1, 1; 1, 0, -1, 1; 1, 1, -2, 1; 1, 1, -1, 0],
   d4MatThreeA, d4MatThreeB,
   !![-1, 0, 0, 0; 0, -1, 0, 0; -1, -1, 1, -1; 0, 0, 0, -1],
   !![1, 0, -1, 0; 0, 1, -1, 0; 0, 0, -1, 0; 0, 0, -1, 1],
   -1]

theorem d4MatGroup_closed :
    ∀ M ∈ d4MatGroup, ∀ G ∈ [d4MatShort, d4MatLong], G * M ∈ d4MatGroup := by
  decide +kernel

theorem d4MatGroup_cube : ∀ M ∈ d4MatGroup,
    (∀ j : Fin TwistTag.D4.tag.rank, (M * M * M).mulVec (Pi.single j 1) = Pi.single j 1) →
      M = 1 ∨ M = d4MatThreeA ∨ M = d4MatThreeB := by
  decide +kernel

theorem d4MatThree_rows : ∀ M : D4Mat, (M = 1 ∨ M = d4MatThreeA ∨ M = d4MatThreeB) →
    (M - 1) (0 : Fin 4) = (M - 1) (1 : Fin 4) ∧ (M - 1) (1 : Fin 4) = (M - 1) (3 : Fin 4) := by
  rintro M (rfl | rfl | rfl) <;> decide +kernel

@[expose] def d4LatVec (a b c d : ℤ) : Fin TwistTag.D4.tag.rank → ℤ := ![a, b, c, d]

theorem rootChar_d4_apply {K : Type} [Field K] (a : Fin TwistTag.D4.tag.rank → Kˣ)
    (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a v = a (0 : Fin 4) ^ v (0 : Fin 4) * a (1 : Fin 4) ^ v (1 : Fin 4) *
      a (2 : Fin 4) ^ v (2 : Fin 4) * a (3 : Fin 4) ^ v (3 : Fin 4) :=
  Fin.prod_univ_four (fun i => a i ^ v i)

theorem weyl_smul_eq_mulVec {τ : Tag} {w : WeylGroup τ} {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (h : ∀ j, w • (Pi.single j 1 : Fin τ.rank → ℤ) = M.mulVec (Pi.single j 1))
    (v : Fin τ.rank → ℤ) : w • v = M.mulVec v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  conv_rhs => rw [hv]
  rw [Finset.smul_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm w (v i) _, h i, Matrix.mulVec_smul]

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4_orbitReflection_zero_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    TwistTag.D4.orbitReflection ⟨0, by decide⟩ • v = d4MatShort.mulVec v := by
  refine weyl_smul_eq_mulVec (fun j => ?_) v
  rw [TwistTag.orbitReflection_smul]
  revert j
  decide +kernel

theorem d4_orbitReflection_one_smul (v : Fin TwistTag.D4.tag.rank → ℤ) :
    TwistTag.D4.orbitReflection ⟨1, by decide⟩ • v = d4MatLong.mulVec v := by
  refine weyl_smul_eq_mulVec (fun j => ?_) v
  rw [TwistTag.orbitReflection_smul]
  revert j
  decide +kernel

theorem d4_orbitReflection_smul (a : Fin TwistTag.D4.foldedTag.rank) :
    ∃ G ∈ [d4MatShort, d4MatLong], ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      TwistTag.D4.orbitReflection a • v = G.mulVec v := by
  fin_cases a
  · exact ⟨d4MatShort, by simp, d4_orbitReflection_zero_smul⟩
  · exact ⟨d4MatLong, by simp, d4_orbitReflection_one_smul⟩

theorem d4_relWeylTwist_smul {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) :
    ∃ M ∈ d4MatGroup, ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = M.mulVec v := by
  rw [relWeylTwist_eq_closure] at hw
  induction hw using Subgroup.closure_induction_left with
  | one => exact ⟨1, by decide +kernel, fun v => by rw [one_smul]; exact (Matrix.one_mulVec v).symm⟩
  | mul_left x hx y hy ih =>
    obtain ⟨M, hM, h⟩ := ih
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨G, hG, hGv⟩ := d4_orbitReflection_smul a
    exact ⟨G * M, d4MatGroup_closed M hM G hG, fun v => by
      rw [mul_smul, h, hGv, Matrix.mulVec_mulVec]⟩
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨M, hM, h⟩ := ih
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨G, hG, hGv⟩ := d4_orbitReflection_smul a
    rw [TwistTag.orbitReflection_inv]
    exact ⟨G * M, d4MatGroup_closed M hM G hG, fun v => by
      rw [mul_smul, h, hGv, Matrix.mulVec_mulVec]⟩

theorem d4_relWeylTwist_order_three_smul {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hw3 : w ^ 3 = 1) :
    ∃ M, (M = 1 ∨ M = d4MatThreeA ∨ M = d4MatThreeB) ∧
      ∀ v : Fin TwistTag.D4.tag.rank → ℤ, w • v = M.mulVec v := by
  obtain ⟨M, hM, h⟩ := d4_relWeylTwist_smul hw
  refine ⟨M, d4MatGroup_cube M hM fun j => ?_, h⟩
  have h3 : (M * M * M).mulVec (Pi.single j 1) =
      w • w • w • (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← h, ← h, ← h]
  rw [h3, smul_smul, smul_smul, ← pow_three', hw3, one_smul]

theorem d4_weyl_order_three_mod_fixed (w : WeylGroup TwistTag.D4.tag)
    (hw : w ∈ relWeylTwist TwistTag.D4) (hw3 : w ^ 3 = 1)
    (γ : Fin TwistTag.D4.tag.rank → ℤ) :
    (w • γ - γ) (0 : Fin 4) = (w • γ - γ) (1 : Fin 4) ∧
      (w • γ - γ) (1 : Fin 4) = (w • γ - γ) (3 : Fin 4) := by
  obtain ⟨M, hM, h⟩ := d4_relWeylTwist_order_three_smul hw hw3
  have e : w • γ - γ = (M - 1).mulVec γ := by
    rw [h γ, Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [e]
  obtain ⟨h1, h2⟩ := d4MatThree_rows M hM
  exact ⟨congrArg (fun r => dotProduct r γ) h1, congrArg (fun r => dotProduct r γ) h2⟩

theorem d4_order_three_smul_single_zero {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1) :
    w • d4LatVec 1 0 0 0 = d4LatVec 1 0 1 0 ∨ w • d4LatVec 1 0 0 0 = d4LatVec 0 (-1) (-1) (-1) := by
  obtain ⟨M, hM, h⟩ := d4_relWeylTwist_order_three_smul hw hw3
  rcases hM with rfl | rfl | rfl
  · exact absurd (ext_single fun j => by rw [h, one_smul]; exact Matrix.one_mulVec _) hw1
  · right
    rw [h]
    decide +kernel
  · left
    rw [h]
    decide +kernel

theorem graphFixedRootWeylHom_mem_rootCharStabilizer (t : TwistTag) {K : Type} [Field K]
    (σ : K →+* K) (n : graphFixedRootMonomial t K σ) (a : Fin t.tag.rank → Kˣ)
    (hcomm : rootDiagUnit t.tag a * (n : ModGL t.tag K) * (rootDiagUnit t.tag a)⁻¹ = n) :
    graphFixedRootWeylHom t K σ n ∈ rootCharStabilizer a := by
  set w := graphFixedRootWeylHom t K σ n with hw
  have hwmem : w ∈ relWeylTwist t := by
    rw [← graphFixedRootWeylHom_range t K σ]
    exact ⟨n, rfl⟩
  set m : graphFixedRootMonomial t K σ :=
    ⟨canonicalRep (coxeterSystem t.tag) K w, canonicalRep_mem_graphFixedRootMonomial t K σ hwmem⟩
    with hm
  have hmw : graphFixedRootWeylHom t K σ m = w := graphFixedRootWeylHom_canonicalRep t K σ hwmem
  have hker : m⁻¹ * n ∈ (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmw, inv_mul_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  have ht : ((m⁻¹ * n : graphFixedRootMonomial t K σ) : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hker).1).1
  set s : ModGL t.tag K := ((m⁻¹ * n : graphFixedRootMonomial t K σ) : ModGL t.tag K) with hs
  have hn : (n : ModGL t.tag K) = canonicalRep (coxeterSystem t.tag) K w * s :=
    congrArg Subtype.val (mul_inv_cancel_left m n).symm
  rw [← conj_canonicalRep_eq_iff (K := K)]
  have hds : rootDiagUnit t.tag a * s * (rootDiagUnit t.tag a)⁻¹ = s :=
    conj_rootDiagUnit_of_mem_torusGroup a ht
  have h1 : (rootDiagUnit t.tag a * canonicalRep (coxeterSystem t.tag) K w *
      (rootDiagUnit t.tag a)⁻¹) * s = canonicalRep (coxeterSystem t.tag) K w * s := by
    calc _ = (rootDiagUnit t.tag a * canonicalRep (coxeterSystem t.tag) K w *
          (rootDiagUnit t.tag a)⁻¹) * (rootDiagUnit t.tag a * s * (rootDiagUnit t.tag a)⁻¹) := by
          rw [hds]
      _ = rootDiagUnit t.tag a * (canonicalRep (coxeterSystem t.tag) K w * s) *
          (rootDiagUnit t.tag a)⁻¹ := by group
      _ = canonicalRep (coxeterSystem t.tag) K w * s := by rw [← hn]; exact hcomm
  exact mul_right_cancel h1

theorem d4_fixed_line {p f : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) (_hf : 1 ≤ f)
    (hq : (p ^ f) % 3 = 1) (K : Type) [Field K] [Finite K] (_hK : Nat.card K = (p ^ f) ^ 3)
    (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (v n : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (δ : K ≃+* K)
    (hv : (v : ModGL TwistTag.D4.tag K) ∈ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hv1 : v ≠ 1) (hv3 : v ^ 3 = 1)
    (hnmono : (n : ModGL TwistTag.D4.tag K) ∈ graphFixedMonomial TwistTag.D4 K σ.toRingHom)
    (hnT : (n : ModGL TwistTag.D4.tag K) ∉ graphFixedTorus TwistTag.D4 K σ.toRingHom)
    (hW3 : (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom
      ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩) ^ 3 = 1)
    (hδ : δ = σ ∨ δ = σ⁻¹)
    (hfix : (MulAut.conj n * fieldActor (t := TwistTag.D4) σ δ) v = v) :
    ∃ ω : Kˣ, Units.map σ.toRingHom.toMonoidHom ω = ω ∧ ω ^ 3 = 1 ∧ ω ≠ 1 ∧
      (v : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![ω, ω, 1, ω] := by
  classical
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 hv).1
  have hΓ : (v : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le _ _ _ v.2
  have hcompat : ∀ i, a (TwistTag.D4.perm i) = Units.map σ.toRingHom.toMonoidHom (a i) := by
    apply compat_of_twistHom_rootDiagUnit
    rw [← ha]
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).2
  set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hσU
  have hσUpow : ∀ x : Kˣ, σU x = x ^ (p ^ f) := fun x => Units.ext (by simp [σU, hσ])
  have hcube : ∀ i, a i ^ 3 = 1 := by
    intro i
    have h := congrArg Subtype.val hv3
    rw [Subgroup.coe_pow, Subgroup.coe_one, ha, rootDiagUnit_pow,
      ← rootDiagUnit_one (τ := TwistTag.D4.tag) (K := K)] at h
    have := congrFun (rootDiagUnit_injective h) i
    simpa using this
  have hσfix : ∀ i, σU (a i) = a i := by
    intro i
    rw [hσUpow]
    have hq' : p ^ f = 3 * ((p ^ f) / 3) + 1 := by omega
    rw [hq', pow_succ, pow_mul, hcube i, one_pow, one_mul]
  have h10 : a (1 : Fin 4) = a (0 : Fin 4) := (hcompat (0 : Fin 4)).trans (hσfix _)
  have h30 : a (3 : Fin 4) = a (0 : Fin 4) :=
    (hcompat (1 : Fin 4)).trans ((hσfix _).trans h10)
  have hδfix : ∀ i, Units.map δ.toRingHom.toMonoidHom (a i) = a i := by
    intro i
    rcases hδ with rfl | rfl
    · exact hσfix i
    · refine Units.ext ?_
      have h1 : σ (a i : K) = (a i : K) := congrArg Units.val (hσfix i)
      change (σ⁻¹ : K ≃+* K) (a i : K) = (a i : K)
      rw [RingAut.inv_apply, RingEquiv.symm_apply_eq]
      exact h1.symm
  have hfa : fieldActor (t := TwistTag.D4) σ δ v = v := by
    refine Subtype.ext ?_
    rw [coe_fieldActor, ha, units_map_entrywiseHom_rootDiagUnit]
    exact congrArg _ (funext hδfix)
  have hfix' : (n : ModGL TwistTag.D4.tag K) * (v : ModGL TwistTag.D4.tag K) *
      (n : ModGL TwistTag.D4.tag K)⁻¹ = (v : ModGL TwistTag.D4.tag K) := by
    rw [MulAut.mul_apply, hfa, MulAut.conj_apply] at hfix
    exact congrArg Subtype.val hfix
  have hcomm : rootDiagUnit TwistTag.D4.tag a * (n : ModGL TwistTag.D4.tag K) *
      (rootDiagUnit TwistTag.D4.tag a)⁻¹ = n := by
    rw [ha] at hfix'
    rw [mul_inv_eq_iff_eq_mul]
    exact (mul_inv_eq_iff_eq_mul.1 hfix').symm
  set g : graphFixedRootMonomial TwistTag.D4 K σ.toRingHom :=
    ⟨(n : ModGL TwistTag.D4.tag K), Subgroup.mem_inf.2 ⟨hnmono, n.2⟩⟩ with hg
  have hst : ∀ u, rootChar a (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g • u) =
      rootChar a u :=
    graphFixedRootWeylHom_mem_rootCharStabilizer TwistTag.D4 σ.toRingHom g a hcomm
  have hwmem : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g ∈ relWeylTwist TwistTag.D4 := by
    rw [← graphFixedRootWeylHom_range TwistTag.D4 K σ.toRingHom]
    exact ⟨g, rfl⟩
  have hw1 : graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom g ≠ 1 := by
    intro h
    have h' : g ∈ (graphFixedRootWeylHom TwistTag.D4 K σ.toRingHom).ker := h
    rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at h'
    exact hnT (Subgroup.mem_inf.1 h').1
  have hb : a (2 : Fin 4) = 1 := by
    have h0 := hst (d4LatVec 1 0 0 0)
    rcases d4_order_three_smul_single_zero hwmem hw1 hW3 with hk | hk
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      exact h0
    · rw [hk, rootChar_d4_apply, rootChar_d4_apply] at h0
      simp [d4LatVec] at h0
      rw [h10, h30] at h0
      have h2 : (a (2 : Fin 4))⁻¹ = 1 := by
        calc (a (2 : Fin 4))⁻¹ = a (0 : Fin 4) * ((a (0 : Fin 4))⁻¹ * (a (2 : Fin 4))⁻¹ *
              (a (0 : Fin 4))⁻¹) * a (0 : Fin 4) := by group
          _ = a (0 : Fin 4) * a (0 : Fin 4) * a (0 : Fin 4) := by rw [h0]
          _ = a (0 : Fin 4) ^ 3 := (pow_three' _).symm
          _ = 1 := hcube _
      exact inv_eq_one.1 h2
  have hω1 : a (0 : Fin 4) ≠ 1 := by
    intro h0
    apply hv1
    refine Subtype.ext ?_
    have h1 : a = 1 := by
      funext i
      fin_cases i
      · exact h0
      · exact h10.trans h0
      · exact hb
      · exact h30.trans h0
    rw [ha, h1, rootDiagUnit_one]
    rfl
  refine ⟨a (0 : Fin 4), hσfix _, hcube _, hω1, ?_⟩
  rw [ha]
  congr 1
  funext i
  fin_cases i
  · rfl
  · exact h10
  · exact hb
  · exact h30

end CFSG.GH74.GLS.Stage2.Bender.Thm1
