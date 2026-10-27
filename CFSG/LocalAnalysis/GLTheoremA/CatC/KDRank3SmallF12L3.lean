module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Klein
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Red
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSLDescent
public import CFSG.RankThree.PartOne.CTP.SeitzLinearOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallL3
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12L3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Core CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Klein
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Red
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs (SmallF1 SmallF2)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open Matrix CFSG.Open CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

noncomputable abbrev OI (T : Type) [Group T] : Subgroup (MulAut T) :=
  CFSG.ComponentClassification.OuterAutomorphisms.inner T

variable {K : Type} [Field K]

theorem scalars_three_eq_bot (h3 : (3 : K) = 0) : scalars 3 K = ⊥ := by
  ext A
  rw [mem_scalars, Subgroup.mem_bot]
  constructor
  · rintro ⟨c, hc, hA⟩
    have hc1 : (c : K) = 1 := by
      apply eq_one_of_pow_three h3
      have := congrArg (fun u : Kˣ => (u : K)) hc
      simpa using this
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one, hA, hc1]
    simp [scalar]
  · rintro rfl
    refine ⟨1, by simp, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_one]
    simp [scalar]

theorem proj_injective_three (h3 : (3 : K) = 0) : Function.Injective (proj 3 K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  rw [proj_eq_one_iff, scalars_three_eq_bot h3, Subgroup.mem_bot] at *
  exact hA

theorem eq_one_of_conj_eq_one (h3 : (3 : K) = 0) {x : projectiveSL 3 K}
    (hx : MulAut.conj x = 1) : x = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  have hcomm : ∀ h : SpecialLinearGroup (Fin 3) K, g * h = h * g := by
    intro h
    have hy := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K h)) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at hy
    have e : proj 3 K (g * h * g⁻¹) = proj 3 K h := by
      rw [map_mul, map_mul, map_inv]
      exact hy
    have e2 := (proj_eq_proj_iff).1 e
    rw [scalars_three_eq_bot h3, Subgroup.mem_bot, inv_mul_eq_one] at e2
    exact mul_inv_eq_iff_eq_mul.1 e2
  have hz : g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    Subgroup.mem_center_iff.2 (fun h => (hcomm h).symm)
  rw [← scalars_eq_center, scalars_three_eq_bot h3, Subgroup.mem_bot] at hz
  rw [hz, map_one]

theorem conj_injective (h3 : (3 : K) = 0) : Function.Injective (MulAut.conj : projectiveSL 3 K →* _) := by
  rw [injective_iff_map_eq_one]
  exact fun x hx => eq_one_of_conj_eq_one h3 hx

theorem proj_eq_iff_eq (h3 : (3 : K) = 0) {A B : SpecialLinearGroup (Fin 3) K} :
    proj 3 K A = proj 3 K B ↔ A = B :=
  ⟨fun h => proj_injective_three h3 h, fun h => h ▸ rfl⟩

theorem klein_T (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0) :
    KleinFour3 (inner (projectiveSL 3 K)) := by
  intro g₁ g₂ k hg₁ hg₂ hg₁2 hg₂2 hg₁1 hg₂1 hne hcomm hk hk3 hkg₁ hkg₂
  obtain ⟨x₁, rfl⟩ := hg₁
  obtain ⟨x₂, rfl⟩ := hg₂
  obtain ⟨x₃, rfl⟩ := hk
  have hpow : ∀ (x : projectiveSL 3 K) (n : ℕ), MulAut.conj x ^ n = 1 → x ^ n = 1 := by
    intro x n hx
    rw [← map_pow] at hx
    exact eq_one_of_conj_eq_one h3 hx
  obtain ⟨G₁, rfl⟩ := proj_surjective 3 K x₁
  obtain ⟨G₂, rfl⟩ := proj_surjective 3 K x₂
  obtain ⟨Gk, rfl⟩ := proj_surjective 3 K x₃
  have hlift : ∀ (A : SpecialLinearGroup (Fin 3) K) (n : ℕ), proj 3 K A ^ n = 1 → A ^ n = 1 := by
    intro A n hA
    rw [← map_pow, proj_eq_one_iff, scalars_three_eq_bot h3, Subgroup.mem_bot] at hA
    exact hA
  have hG₁2 : G₁ ^ 2 = 1 := hlift G₁ 2 (hpow _ 2 hg₁2)
  have hG₂2 : G₂ ^ 2 = 1 := hlift G₂ 2 (hpow _ 2 hg₂2)
  have hGk3 : Gk ^ 3 = 1 := hlift Gk 3 (hpow _ 3 hk3)
  have hG₁1 : G₁ ≠ 1 := fun h => hg₁1 (by rw [h, map_one, map_one])
  have hG₂1 : G₂ ≠ 1 := fun h => hg₂1 (by rw [h, map_one, map_one])
  have hG12 : G₁ ≠ G₂ := fun h => hne (by rw [h])
  have hcomm' : G₁ * G₂ = G₂ * G₁ := by
    rw [← proj_eq_iff_eq h3, map_mul, map_mul]
    apply conj_injective h3
    rw [map_mul, map_mul]
    exact hcomm
  have hkG₁ : Gk * G₁ = G₁ * Gk := by
    rw [← proj_eq_iff_eq h3, map_mul, map_mul]
    apply conj_injective h3
    rw [map_mul, map_mul]
    exact hkg₁
  have hkG₂ : Gk * G₂ = G₂ * Gk := by
    rw [← proj_eq_iff_eq h3, map_mul, map_mul]
    apply conj_injective h3
    rw [map_mul, map_mul]
    exact hkg₂
  have key := klein_core hK h3 (g₁ := (G₁ : Matrix (Fin 3) (Fin 3) K))
    (g₂ := (G₂ : Matrix (Fin 3) (Fin 3) K)) (k := (Gk : Matrix (Fin 3) (Fin 3) K))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hG₁2, Matrix.SpecialLinearGroup.coe_one])
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, hG₂2, Matrix.SpecialLinearGroup.coe_one])
    (Matrix.SpecialLinearGroup.det_coe G₁) (Matrix.SpecialLinearGroup.det_coe G₂)
    (fun h => hG₁1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])))
    (fun h => hG₂1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one])))
    (fun h => hG12 (Subtype.ext h))
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hcomm', Matrix.SpecialLinearGroup.coe_mul])
    (by rw [← Matrix.SpecialLinearGroup.coe_pow, hGk3, Matrix.SpecialLinearGroup.coe_one])
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hkG₁, Matrix.SpecialLinearGroup.coe_mul])
    (by rw [← Matrix.SpecialLinearGroup.coe_mul, hkG₂, Matrix.SpecialLinearGroup.coe_mul])
  have hGk1 : Gk = 1 := Subtype.ext (by rw [key, Matrix.SpecialLinearGroup.coe_one])
  rw [hGk1, map_one, map_one]

theorem exists_cube_root (h3 : (3 : K) = 0) [Finite K] (d : K) : ∃ l : K, l ^ 3 = d := by
  have hinj : Function.Injective (fun x : K => x ^ 3) := by
    intro x y hxy
    have : (x - y) ^ 3 = 0 := by
      have h' : x ^ 3 = y ^ 3 := hxy
      calc (x - y) ^ 3 = x ^ 3 - 3 * x ^ 2 * y + 3 * x * y ^ 2 - y ^ 3 := by ring
        _ = 0 := by rw [h3, h']; ring
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  exact Finite.surjective_of_injective hinj d

theorem conjAut_mem_inner (h3 : (3 : K) = 0) [Finite K] (A : GL (Fin 3) K) :
    conjAut 3 K A ∈ inner (projectiveSL 3 K) := by
  have hd : (A : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit |>.ne_zero
  obtain ⟨l, hl⟩ := exists_cube_root h3 (A : Matrix (Fin 3) (Fin 3) K).det
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hd
    rw [← hl]
    simp
  have hdet : (l⁻¹ • (A : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← hl]
    field_simp
  let g : SpecialLinearGroup (Fin 3) K := ⟨l⁻¹ • (A : Matrix (Fin 3) (Fin 3) K), hdet⟩
  have key : ∀ k : SpecialLinearGroup (Fin 3) K,
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A k
        * g = g * k := by
    intro k
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slConjugation]
    simp only [g, Matrix.mul_smul, Matrix.smul_mul, mul_assoc, Units.inv_mul, mul_one]
  refine ⟨proj 3 K g, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨k, rfl⟩ := proj_surjective 3 K y
  rw [conjAut_proj, MulAut.conj_apply]
  have hk := eq_mul_inv_of_mul_eq (key k)
  rw [hk, map_mul, map_mul, map_inv]

theorem linearAutGroup_le_inner (h3 : (3 : K) = 0) [Finite K] :
    linearAutGroup 3 K ≤ inner (projectiveSL 3 K) := by
  unfold linearAutGroup
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨A, rfl⟩
  exact conjAut_mem_inner h3 A

theorem lift_pow_eq_one (h3 : (3 : K) = 0) (A : SpecialLinearGroup (Fin 3) K) (n : ℕ)
    (hA : proj 3 K A ^ n = 1) : A ^ n = 1 := by
  rw [← map_pow, proj_eq_one_iff, scalars_three_eq_bot h3, Subgroup.mem_bot] at hA
  exact hA

theorem mul_conj_mul_inv {G : Type} [Group G] (φ : MulAut G) (x : G) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  apply MulEquiv.ext
  intro z
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem matrix_of_inner (h3 : (3 : K) = 0) :
    ∀ y : MulAut (projectiveSL 3 K), ∃ M : SpecialLinearGroup (Fin 3) K,
      y ∈ inner (projectiveSL 3 K) → MulAut.conj (proj 3 K M) = y := by
  intro y
  by_cases hy : y ∈ inner (projectiveSL 3 K)
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨M, rfl⟩ := proj_surjective 3 K x
    exact ⟨M, fun _ => rfl⟩
  · exact ⟨1, fun h => absurd h hy⟩


theorem map_entry (τ : K ≃+* K) (A : SpecialLinearGroup (Fin 3) K) (i j : Fin 3) :
    (SpecialLinearGroup.map τ.toRingHom A : Matrix (Fin 3) (Fin 3) K) i j =
      τ ((A : Matrix (Fin 3) (Fin 3) K) i j) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem conj_pow_eq {G : Type} [Group G] (x h : G) (n : ℕ) :
    (h⁻¹ * x * h) ^ n = h⁻¹ * x ^ n * h := by
  induction n with
  | zero => group
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    group

theorem f2_T [Finite K] [CharP K 3] (hcard : Nat.card K = 3 ^ 3)
    (E : Subgroup (MulAut (projectiveSL 3 K))) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hnot : ¬ E ≤ OI (projectiveSL 3 K))
    (hE0 : Nat.card ↥(E ⊓ OI (projectiveSL 3 K)) = 3 ^ 2) :
    ∀ W : Subgroup (MulAut (projectiveSL 3 K)), IsPGroup 2 W → W ≤ OI (projectiveSL 3 K) →
      E ⊓ OI (projectiveSL 3 K) ≤ Subgroup.centralizer (W : Set (MulAut (projectiveSL 3 K))) →
      W = ⊥ := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro W hW hWI hWC
  by_contra hW0
  obtain ⟨b, hbE, hbI⟩ : ∃ b ∈ E, b ∉ OI (projectiveSL 3 K) := by
    obtain ⟨b, hb, hbn⟩ := SetLike.not_le_iff_exists.1 hnot
    exact ⟨b, hb, hbn⟩
  have hb3 : b ^ 3 = 1 := hE.2 b hbE
  have hb1 : b ≠ 1 := fun h => hbI (h ▸ (OI (projectiveSL 3 K)).one_mem)
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hbS := CFSG.RankThree.PartOne.CTP.mem_semilinearAutGroup_of_pow_eq_one (n := 3) (F := K)
    (by norm_num) Nat.prime_three (by norm_num) hb3
  have hbL : b ∉ linearAutGroup 3 K := fun h => hbI (linearAutGroup_le_inner h3 h)
  obtain ⟨-, σ, -, ⟨h, -, hbh⟩, hσc⟩ :=
    higher_linear_prime_semilinear_field_descent' (ℓ := 3) (f := 3) Nat.prime_three (by norm_num)
      (by norm_num) hcard Nat.prime_three b hbS hbL hbord
  set f := fieldAut 3 K σ with hfdef
  set F₀ := CFSG.GroupTheory.SteinbergBK.semilinearFixedSubfield σ with hF₀def
  have hF₀ : Nat.card F₀ = 3 := by rw [hσc]; norm_num
  have hbh' : h⁻¹ * b * h = f := by rw [hbh]; group
  have hcf : ∀ x ∈ E, f * (h⁻¹ * x * h) = (h⁻¹ * x * h) * f := by
    intro x hx
    have hxb : x * b = b * x := isElemAbelian_commute hE hx hbE
    calc f * (h⁻¹ * x * h) = (h⁻¹ * b * h) * (h⁻¹ * x * h) := by rw [hbh']
      _ = h⁻¹ * (b * x) * h := by group
      _ = h⁻¹ * (x * b) * h := by rw [hxb]
      _ = (h⁻¹ * x * h) * (h⁻¹ * b * h) := by group
      _ = (h⁻¹ * x * h) * f := by rw [hbh']
  have hcinner : ∀ x ∈ OI (projectiveSL 3 K), h⁻¹ * x * h ∈ OI (projectiveSL 3 K) := by
    intro x hx
    have := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (projectiveSL 3 K)).conj_mem x hx h⁻¹
    rwa [inv_inv] at this
  choose Mof hMof using matrix_of_inner (K := K) h3
  haveI : Fintype ↥(E ⊓ OI (projectiveSL 3 K)) := Fintype.ofFinite _
  classical
  set Pm : Finset (Matrix (Fin 3) (Fin 3) K) := Finset.univ.image (fun x : ↥(E ⊓ OI (projectiveSL 3 K)) =>
    ((Mof (h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) with hPmdef
  have hMc : ∀ x : ↥(E ⊓ OI (projectiveSL 3 K)),
      MulAut.conj (proj 3 K (Mof (h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h))) =
        h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h := fun x =>
    hMof _ (hcinner _ x.2.2)
  have hMinj : Function.Injective (fun x : ↥(E ⊓ OI (projectiveSL 3 K)) =>
      ((Mof (h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K)) := by
    intro x y hxy
    have hSL : Mof (h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h) =
        Mof (h⁻¹ * (y : MulAut (projectiveSL 3 K)) * h) := Subtype.ext hxy
    have h1 : h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h = h⁻¹ * (y : MulAut (projectiveSL 3 K)) * h := by
      rw [← hMc x, ← hMc y, hSL]
    apply Subtype.ext
    calc (x : MulAut (projectiveSL 3 K)) = h * (h⁻¹ * (x : MulAut (projectiveSL 3 K)) * h) * h⁻¹ := by
          group
      _ = h * (h⁻¹ * (y : MulAut (projectiveSL 3 K)) * h) * h⁻¹ := by rw [h1]
      _ = (y : MulAut (projectiveSL 3 K)) := by group
  have hPmcard : Pm.card = 9 := by
    rw [hPmdef, Finset.card_image_of_injective _ hMinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hE0]
    norm_num
  have hPc : ∀ x ∈ Pm, ∀ y ∈ Pm, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x1, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y1, -, rfl⟩ := Finset.mem_image.1 hy
    have key : Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) *
        Mof (h⁻¹ * (y1 : MulAut (projectiveSL 3 K)) * h) =
        Mof (h⁻¹ * (y1 : MulAut (projectiveSL 3 K)) * h) *
        Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) := by
      apply (proj_eq_iff_eq h3).1
      apply conj_injective h3
      simp only [map_mul]
      rw [hMc x1, hMc y1]
      have hc := isElemAbelian_commute hE x1.2.1 y1.2.1
      calc h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h * (h⁻¹ * (y1 : MulAut (projectiveSL 3 K)) * h)
          = h⁻¹ * ((x1 : MulAut (projectiveSL 3 K)) * (y1 : MulAut (projectiveSL 3 K))) * h := by group
        _ = h⁻¹ * ((y1 : MulAut (projectiveSL 3 K)) * (x1 : MulAut (projectiveSL 3 K))) * h := by rw [hc]
        _ = h⁻¹ * (y1 : MulAut (projectiveSL 3 K)) * h * (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) := by
          group
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, key]
  have hP3 : ∀ x ∈ Pm, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x1, -, rfl⟩ := Finset.mem_image.1 hx
    have hx3 : (x1 : MulAut (projectiveSL 3 K)) ^ 3 = 1 := hE.2 _ x1.2.1
    have hc3 : (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) ^ 3 = 1 := by
      rw [conj_pow_eq, hx3]
      group
    have hM3 : proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h)) ^ 3 = 1 := by
      apply eq_one_of_conj_eq_one h3
      rw [map_pow, hMc x1, hc3]
    have := lift_pow_eq_one h3 _ 3 hM3
    rw [← Matrix.SpecialLinearGroup.coe_pow, this, Matrix.SpecialLinearGroup.coe_one]
  have hPF : ∀ x ∈ Pm, ∀ i j, x i j ∈ F₀ := by
    intro x hx i j
    obtain ⟨x1, -, rfl⟩ := Finset.mem_image.1 hx
    have hfM : f * MulAut.conj (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h))) =
        MulAut.conj (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h))) * f := by
      rw [hMc x1]
      exact hcf x1 x1.2.1
    have h1 : MulAut.conj (f (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h)))) =
        MulAut.conj (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h))) := by
      rw [← mul_conj_mul_inv]
      have : f * MulAut.conj (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h))) * f⁻¹ =
          MulAut.conj (proj 3 K (Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h))) := by
        rw [hfM, mul_assoc, mul_inv_cancel, mul_one]
      exact this
    have h2 := conj_injective h3 h1
    rw [hfdef, fieldAut_proj] at h2
    have h4 := (proj_eq_iff_eq h3).1 h2
    have h5 := congrArg (fun A : SpecialLinearGroup (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i j) h4
    rw [map_entry] at h5
    exact RingHom.mem_eqLocusField.2 (by simpa using h5)
  have hW2 : 2 ∣ Nat.card W := by
    obtain ⟨n, hn⟩ := hW.exists_card_eq
    have hne : Nat.card W ≠ 1 := fun h1 => hW0 (Subgroup.eq_bot_of_card_eq W h1)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by rw [hn]; norm_num)
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 2 hW2
  have htW : (t : MulAut (projectiveSL 3 K)) ∈ W := t.2
  have ht0sq : (t : MulAut (projectiveSL 3 K)) ^ 2 = 1 := by
    have h := congrArg (fun x : ↥W => (x : MulAut (projectiveSL 3 K)))
      (show t ^ 2 = 1 by rw [← ht]; exact pow_orderOf_eq_one t)
    simpa using h
  have ht0ne : (t : MulAut (projectiveSL 3 K)) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    norm_num at ht
  set tp := h⁻¹ * (t : MulAut (projectiveSL 3 K)) * h with htp
  have htp_in : tp ∈ OI (projectiveSL 3 K) := hcinner _ (hWI htW)
  set B := Mof tp with hBdef
  have hBconj : MulAut.conj (proj 3 K B) = tp := hMof tp htp_in
  have htpsq : tp ^ 2 = 1 := by
    rw [htp, conj_pow_eq, ht0sq]
    group
  have hB2 : ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    have h1 : proj 3 K B ^ 2 = 1 := by
      apply eq_one_of_conj_eq_one h3
      rw [map_pow, hBconj, htpsq]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← sq, lift_pow_eq_one h3 B 2 h1,
      Matrix.SpecialLinearGroup.coe_one]
  have hBne1 : ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ 1 := by
    intro hm
    apply ht0ne
    have hB1 : B = 1 := Subtype.ext hm
    have : tp = 1 := by rw [← hBconj, hB1, map_one, map_one]
    rw [htp] at this
    have hx : (t : MulAut (projectiveSL 3 K)) = 1 := by
      calc (t : MulAut (projectiveSL 3 K)) = h * (h⁻¹ * (t : MulAut (projectiveSL 3 K)) * h) * h⁻¹ := by
            group
        _ = 1 := by rw [this]; group
    exact hx
  have hBneg : ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ -1 := by
    intro hm
    have hd := (B : SpecialLinearGroup (Fin 3) K).2
    rw [hm, Matrix.det_neg, Matrix.det_one] at hd
    have : (2 : K) = 0 := by
      norm_num at hd
      linear_combination -hd
    exact (Ring.two_ne_zero hK) this
  have hBP : ∀ x ∈ Pm, ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x =
      x * ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx
    obtain ⟨x1, -, rfl⟩ := Finset.mem_image.1 hx
    have hcen : (t : MulAut (projectiveSL 3 K)) * (x1 : MulAut (projectiveSL 3 K)) =
        (x1 : MulAut (projectiveSL 3 K)) * (t : MulAut (projectiveSL 3 K)) :=
      Subgroup.mem_centralizer_iff.1 (hWC x1.2) _ htW
    have hcomm' : tp * (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) =
        (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) * tp := by
      rw [htp]
      calc h⁻¹ * (t : MulAut (projectiveSL 3 K)) * h * (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h)
          = h⁻¹ * ((t : MulAut (projectiveSL 3 K)) * (x1 : MulAut (projectiveSL 3 K))) * h := by group
        _ = h⁻¹ * ((x1 : MulAut (projectiveSL 3 K)) * (t : MulAut (projectiveSL 3 K))) * h := by rw [hcen]
        _ = (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) * (h⁻¹ * (t : MulAut (projectiveSL 3 K)) * h) := by
          group
    have hBM : B * Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) =
        Mof (h⁻¹ * (x1 : MulAut (projectiveSL 3 K)) * h) * B := by
      apply (proj_eq_iff_eq h3).1
      apply conj_injective h3
      simp only [map_mul]
      rw [hBconj, hMc x1]
      exact hcomm'
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hBM]
  exact f2_core hK h3 F₀ hF₀ Pm hPc hP3 hPF (by rw [hPmcard]; norm_num)
    ((B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) hB2 hBne1 hBneg hBP

theorem f2_S [Finite K] [CharP K 3] (hcard : Nat.card K = 3 ^ 3) (S : Type) [Group S] [Finite S]
    (e : S ≃* projectiveSL 3 K) (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ 3) (hnot : ¬ E ≤ inner S)
    (hE0 : Nat.card ↥(E ⊓ inner S) = 3 ^ 2) : SmallF2 S E := by
  intro W hW hWI hWC
  set φ : MulAut S →* MulAut (projectiveSL 3 K) := (MulAut.congr e).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.congr e).injective
  have hin : (inner S).map φ = inner (projectiveSL 3 K) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e
  have hE' : IsElemAbelian 3 (E.map φ) := CFSG.SectionRank.isElemAbelian_map hE φ
  have hcard' : Nat.card (E.map φ) = 3 ^ 3 := by rw [Subgroup.card_map_of_injective hφi, hEcard]
  have hnot' : ¬ E.map φ ≤ inner (projectiveSL 3 K) := by
    intro h
    apply hnot
    intro x hx
    have hx' : φ x ∈ inner (projectiveSL 3 K) := h (Subgroup.mem_map_of_mem φ hx)
    rw [← hin] at hx'
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
    rw [← hφi hyx]
    exact hy
  have hmap : E.map φ ⊓ inner (projectiveSL 3 K) = (E ⊓ inner S).map φ := by
    rw [← hin, Subgroup.map_inf_eq _ _ _ hφi]
  have hE0' : Nat.card ↥(E.map φ ⊓ inner (projectiveSL 3 K)) = 3 ^ 2 := by
    rw [hmap, Subgroup.card_map_of_injective hφi, hE0]
  have hW' : W.map φ = ⊥ := by
    apply f2_T hcard (E.map φ) hE' hcard' hnot' hE0' (W.map φ) (hW.map φ)
    · exact (Subgroup.map_mono hWI).trans hin.le
    · intro y hy
      rw [hmap] at hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hw'
      have hcw := Subgroup.mem_centralizer_iff.1 (hWC hx) w hw
      rw [← map_mul, ← map_mul, hcw]
  ext x
  constructor
  · intro hx
    have hmem : φ x ∈ W.map φ := Subgroup.mem_map_of_mem φ hx
    rw [hW', Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (hφi (by rw [hmem, map_one]))
  · intro hx
    rw [Subgroup.mem_bot] at hx
    rw [hx]
    exact W.one_mem

theorem klein_S (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0) (S : Type) [Group S]
    (e : S ≃* projectiveSL 3 K) : KleinFour3 (inner S) := by
  intro g₁ g₂ k hg₁ hg₂ hg1 hg2 hne1 hne2 hne hcomm hk hk3 hkg1 hkg2
  set φ : MulAut S →* MulAut (projectiveSL 3 K) := (MulAut.congr e).toMonoidHom with hφ
  have hφi : Function.Injective φ := (MulAut.congr e).injective
  have hin : ∀ x ∈ inner S, φ x ∈ inner (projectiveSL 3 K) := fun x hx => by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e]
    exact Subgroup.mem_map_of_mem _ hx
  have hk' := klein_T hK h3 (φ g₁) (φ g₂) (φ k) (hin g₁ hg₁) (hin g₂ hg₂)
    (by rw [← map_pow, hg1, map_one]) (by rw [← map_pow, hg2, map_one])
    (fun h => hne1 (hφi (by rw [h, map_one]))) (fun h => hne2 (hφi (by rw [h, map_one])))
    (fun h => hne (hφi h)) (by rw [← map_mul, ← map_mul, hcomm]) (hin k hk)
    (by rw [← map_pow, hk3, map_one]) (by rw [← map_mul, ← map_mul, hkg1])
    (by rw [← map_mul, ← map_mul, hkg2])
  exact hφi (by rw [hk', map_one])

theorem smallF2_smallF1_A2 (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 27)
    (e0 : S ≃* (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩))
    (E : Subgroup (MulAut S)) (hE : IsElemAbelian 3 E) (hEcard : Nat.card E = 3 ^ 3)
    (hnot : ¬ E ≤ inner S) (hE0 : Nat.card ↥(E ⊓ inner S) = 3 ^ 2) :
    SmallF2 S E ∧ SmallF1 S E := by
  have hp3 : q.p = 3 := CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallL3.prime_eq_three_of_card_eq_27 q hq
  have hpow : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← TauCeti.PrimePower.card_def, hq]
    norm_num
  have hf3 : q.exponent = 3 := by
    rw [hp3] at hpow
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP (GaloisField q.p q.exponent) 3 := by
    rw [← hp3]
    infer_instance
  have hK : Nat.card (GaloisField q.p q.exponent) = 3 ^ 3 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hp3, hf3]
  let e : S ≃* projectiveSL 3 (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 (GaloisField q.p q.exponent))
  have h2 := f2_S hK S e E hE hEcard hnot hE0
  have hr : (3 : GaloisField q.p q.exponent) = 0 := CharP.cast_eq_zero _ 3
  have hk := klein_S (K := GaloisField q.p q.exponent) (by rw [ringChar.eq _ 3]; norm_num) hr S e
  exact ⟨h2, smallF1_of_f2_klein S E hE hEcard hE0 h2 hk⟩

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12L3
