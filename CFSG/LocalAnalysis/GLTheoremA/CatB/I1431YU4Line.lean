module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Res
public import CFSG.RankThree.PartTwo.Sec8.Item82ProofPSL3
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4Ord

public section

set_option maxHeartbeats 1000000

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.Open
open scoped Pointwise

theorem center_sl2_eq_bot {K : Type} [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hAeq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    exact_mod_cast this
  have h1 : r = 1 := by
    have h3 : (r - 1) ^ 2 = 0 := by
      linear_combination hr2 - r * h2 + h2
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h3)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hAeq, h1, Matrix.SpecialLinearGroup.coe_one, map_one]

theorem isCyclic_of_three_sl2 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 64)
    (P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) (hP : IsPGroup 3 P) : IsCyclic P := by
  let π : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    QuotientGroup.mk' _
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_sl2_eq_bot]
  have hPm : IsPGroup 3 (P.map π) := hP.map π
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow (P := P.map π) hPm
  have hringChar : ringChar K ≠ 3 := by
    rw [ringChar.eq K 2]
    norm_num
  have hQc : IsCyclic ↥(↑Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
    CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2 hringChar (by rw [hK]; norm_num) Q
  haveI := hQc
  have h1 : IsCyclic ↥((P.map π).subgroupOf (↑Q : Subgroup _)) := Subgroup.isCyclic _
  have h2 : IsCyclic ↥(P.map π) := (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hPQ)).mp h1
  exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective P π hπ)).mpr h2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

noncomputable def act (g : GL (HypIndex 2 0) K) : Module.End K (HypIndex 2 0 → K) :=
  Matrix.toLinAlgEquiv' (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K)

theorem act_apply (g : GL (HypIndex 2 0) K) (v : HypIndex 2 0 → K) :
    act g v = (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v := by
  simp [act]

theorem act_one : act (1 : GL (HypIndex 2 0) K) = 1 := by
  simp [act]

theorem act_pow (g : GL (HypIndex 2 0) K) (n : ℕ) : act (g ^ n) = act g ^ n := by
  simp [act, Units.val_pow_eq_pow_val, map_pow]

theorem hyp_isometry4 (h : UnitaryFieldData 2 3 K) (g : GL (HypIndex 2 0) K)
    (hg : g ∈ hypSU h 2 0) (x y : HypIndex 2 0 → K) :
    hypForm h 2 0 ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x)
      ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ y) = hypForm h 2 0 x y := by
  have hg' : ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K).map h.bar)ᵀ * hypGram 2 0 K *
      (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) = hypGram 2 0 K :=
    (show _ ∧ _ from hg).1
  exact (gramForm_isometry_iff h (hypGram 2 0 K) _).mpr hg' x y

theorem mem_perp_iff4 {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    {y : HypIndex 2 0 → K} : y ∈ W.orthogonalBilin (hypForm h 2 0) ↔ ∀ n ∈ W, hypForm h 2 0 n y = 0 :=
  Iff.rfl

theorem shift_mem_perp4 (h : UnitaryFieldData 2 3 K) {W : Submodule K (HypIndex 2 0 → K)}
    {g : GL (HypIndex 2 0) K} (hg : g ∈ hypSU h 2 0) (hfix : FixesPt W g) (x : HypIndex 2 0 → K) :
    (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x - x ∈ W.orthogonalBilin (hypForm h 2 0) := by
  rw [mem_perp_iff4]
  intro n hn
  have hgn := hfix n hn
  rw [map_sub, sub_eq_zero]
  calc hypForm h 2 0 n ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x)
      = hypForm h 2 0 ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ n)
          ((g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ x) := by rw [hgn]
    _ = hypForm h 2 0 n x := hyp_isometry4 h g hg n x

theorem perp_eq_of_finrank_two' (h : UnitaryFieldData 2 3 K) (W : Submodule K (HypIndex 2 0 → K))
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (hk : Module.finrank K W = 2) :
    W.orthogonalBilin (hypForm h 2 0) = W :=
  perp_eq_of_finrank_two h W hW hk

theorem sq_eq_one_of_fixes (h : UnitaryFieldData 2 3 K) {W : Submodule K (HypIndex 2 0 → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (hk : Module.finrank K W = 2)
    {g : GL (HypIndex 2 0) K} (hg : g ∈ hypSU h 2 0) (hfix : FixesPt W g) : g ^ 2 = 1 := by
  set N : Module.End K (HypIndex 2 0 → K) := act g - 1 with hNdef
  have hNv : ∀ v, N v = (g : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v - v := by
    intro v
    simp [hNdef, act_apply]
  have hN_fix : ∀ w ∈ W, N w = 0 := by
    intro w hw
    rw [hNv, hfix w hw, sub_self]
  have hN_perp : ∀ v, N v ∈ W := by
    intro v
    have := shift_mem_perp4 h hg hfix v
    rw [perp_eq_of_finrank_two' h W hW hk] at this
    rw [hNv]
    exact this
  have hN2 : N ^ 2 = 0 := by
    apply LinearMap.ext
    intro v
    rw [pow_two, Module.End.mul_apply]
    simp only [LinearMap.zero_apply]
    exact hN_fix _ (hN_perp v)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (Module.End K (HypIndex 2 0 → K)) 2 :=
    charP_of_injective_algebraMap (algebraMap K (Module.End K (HypIndex 2 0 → K))).injective 2
  have hact : act g = 1 + N := by
    rw [hNdef]
    abel
  have hact2 : act g ^ 2 = 1 := by
    rw [hact, add_pow_char_of_commute 2 (Commute.one_left N), one_pow, hN2, add_zero]
  have h2 : act (g ^ 2) = act 1 := by
    rw [act_pow, hact2, act_one]
  exact Units.ext (Matrix.toLinAlgEquiv'.injective h2)

theorem restrMat_det_ne_zero {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x : X) : (restrMat b X hX x).det ≠ 0 := by
  intro h0
  have h1 : restrMat b X hX x * restrMat b X hX x⁻¹ = 1 := by
    rw [← restrMat_mul, mul_inv_cancel, restrMat_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
  exact zero_ne_one h2

noncomputable def detRes {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W) :
    X →* Kˣ where
  toFun x := Units.mk0 (restrMat b X hX x).det (restrMat_det_ne_zero b X hX x)
  map_one' := Units.ext (by simp [restrMat_one])
  map_mul' x y := Units.ext (by simp [restrMat_mul, Matrix.det_mul])

theorem card_units_sixtyfour (hK : Nat.card K = 64) : Nat.card Kˣ = 63 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]

theorem surj_ker_det {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (hK : Nat.card K = 64)
    (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : Nat.card T = 360)
    (φ : X →* T) (hφ : Function.Surjective φ) :
    Function.Surjective (φ.comp (detRes b X hX).ker.subtype) := by
  set X0 := (detRes b X hX).ker with hX0
  have hN : (X0.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X0.map φ) with hbot | htop
  · exfalso
    have hle : X0 ≤ φ.ker := by
      intro x hx
      have hmem : φ x ∈ X0.map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have h1 : φ.ker.index ∣ X0.index := Subgroup.index_dvd_of_le hle
    have h2 : φ.ker.index = Nat.card T := by
      rw [Subgroup.index_ker φ, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    have h3 : X0.index = Nat.card (detRes b X hX).range := Subgroup.index_ker _
    have h4 : Nat.card (detRes b X hX).range ∣ 63 := by
      rw [← card_units_sixtyfour hK]
      exact Subgroup.card_subgroup_dvd_card _
    rw [h2, h3] at h1
    have h5 := h1.trans h4
    rw [hT] at h5
    norm_num at h5
  · intro t
    have htm : t ∈ X0.map φ := by
      rw [htop]
      exact Subgroup.mem_top t
    obtain ⟨x, hx, hxt⟩ := Subgroup.mem_map.mp htm
    exact ⟨⟨x, hx⟩, hxt⟩

theorem restrMat_det_one {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (x : X) (hx : x ∈ (detRes b X hX).ker) : (restrMat b X hX x).det = 1 := by
  have h1 : detRes b X hX x = 1 := MonoidHom.mem_ker.mp hx
  have h2 : ((detRes b X hX x : Kˣ) : K) = (restrMat b X hX x).det := rfl
  rw [h1, Units.val_one] at h2
  exact h2.symm

noncomputable def restrSL {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (b : Module.Basis (Fin 2) K W) (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W) :
    (detRes b X hX).ker →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun x := ⟨restrMat b X hX x.1, restrMat_det_one b X hX x.1 x.2⟩
  map_one' := Subtype.ext (restrMat_one b X hX)
  map_mul' x y := Subtype.ext (restrMat_mul b X hX x.1 y.1)

theorem three_subgroup_cyclic {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (hk : Module.finrank K W = 2)
    (b : Module.Basis (Fin 2) K W) (hK : Nat.card K = 64)
    (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (R : Subgroup (detRes b X hX).ker) (hR : IsPGroup 3 R) : IsCyclic R := by
  let f : R →* Matrix.SpecialLinearGroup (Fin 2) K := (restrSL b X hX).comp R.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hxR⟩ hr
    have hx1 : restrSL b X hX x = 1 := hr
    have hrestr : restrHom b X hX x.1 = 1 := by
      apply Units.ext
      rw [restrHom_apply, Units.val_one]
      have := congrArg Subtype.val hx1
      exact this
    have hfix := fixesPt_of_restrHom_eq_one b X hX x.1 hrestr
    have hsq := sq_eq_one_of_fixes h hW hk (x.1 : hypSU h 2 0).2 hfix
    obtain ⟨k, hk3⟩ := hR ⟨x, hxR⟩
    have hk3' : ((x.1 : hypSU h 2 0) : GL (HypIndex 2 0) K) ^ (3 ^ k) = 1 := by
      have := congrArg (fun z : R => (((z.1.1 : X) : hypSU h 2 0) : GL (HypIndex 2 0) K)) hk3
      simpa using this
    have hcop : Nat.Coprime 2 (3 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    have hg1 : ((x.1 : hypSU h 2 0) : GL (HypIndex 2 0) K) = 1 := by
      have := pow_gcd_eq_one.mpr ⟨hsq, hk3'⟩
      rw [hcop.gcd_eq_one, pow_one] at this
      exact this
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    simpa using hg1
  have hP : IsPGroup 3 (R.map (restrSL b X hX)) := hR.map _
  have hc := isCyclic_of_three_sl2 hK (R.map (restrSL b X hX)) hP
  have hrange : f.range = R.map (restrSL b X hX) := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r.1, r.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  have h2 : IsCyclic ↥f.range := by
    rw [hrange]
    exact hc
  exact (MulEquiv.isCyclic (MonoidHom.ofInjective hf)).mpr h2

theorem no_surj_line {h : UnitaryFieldData 2 3 K} {W : Submodule K (HypIndex 2 0 → K)}
    (hW : ∀ x ∈ W, ∀ y ∈ W, hypForm h 2 0 x y = 0) (hk : Module.finrank K W = 2) (hK : Nat.card K = 64)
    (X : Subgroup (hypSU h 2 0)) (hX : X ≤ isoStabilizer h 2 0 W)
    (T : Type) [Group T] [Finite T] [IsSimpleGroup T] (hT : Nat.card T = 360)
    (hT3 : ¬ ∀ Q : Sylow 3 T, IsCyclic ↥(↑Q : Subgroup T)) :
    ¬ ∃ φ : X →* T, Function.Surjective φ := by
  rintro ⟨φ, hφ⟩
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply hT3
  intro Q
  exact CFSG.RankThree.PartTwo.Sec8.Item82Proof.isCyclic_sylow_of_surjective
    (surj_ker_det b hK X hX T hT φ hφ)
    (fun R => three_subgroup_cyclic hW hk b hK X hX R R.isPGroup') Q

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

end
