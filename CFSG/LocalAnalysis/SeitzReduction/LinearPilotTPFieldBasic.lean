module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
public import CFSG.RankThree.PartOne.KC.LinearSubfieldInclusion

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartOne (linearSubfieldInclusion linearSubfieldInclusion_proj
  linearSubfieldInclusion_injective)

section Sylow

variable {p : ℕ}

@[expose] def CentralizesSylow (p : ℕ) {X : Type*} [Group X] (x : X) : Prop :=
  ∃ S : Sylow p X, ∀ s ∈ (S : Subgroup X), s * x = x * s

theorem CentralizesSylow.map_mulEquiv [Fact p.Prime] {X Y : Type*} [Group X] [Group Y]
    [Finite X] (e : X ≃* Y) {x : X} (h : CentralizesSylow p x) : CentralizesSylow p (e x) := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective, fun s hs => ?_⟩
  have hs' : s ∈ (S : Subgroup X).map e.toMonoidHom := hs
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs'
  change e t * e x = e x * e t
  rw [← map_mul, ← map_mul, hS t ht]

theorem exists_centralizesSylow_of_range_eq [Fact p.Prime] {C₁ C₂ Γ : Type*} [Group C₁]
    [Group C₂] [Group Γ] [Finite C₁] {ψ₁ : C₁ →* Γ} {ψ₂ : C₂ →* Γ}
    (h₁ : Function.Injective ψ₁) (h₂ : Function.Injective ψ₂) (h : ψ₁.range = ψ₂.range)
    {c₁ : C₁} (hc : CentralizesSylow p c₁) :
    ∃ c₂ : C₂, ψ₂ c₂ = ψ₁ c₁ ∧ CentralizesSylow p c₂ := by
  set e : C₁ ≃* C₂ := (MonoidHom.ofInjective h₁).trans
    ((MulEquiv.subgroupCongr h).trans (MonoidHom.ofInjective h₂).symm) with he
  refine ⟨e c₁, ?_, hc.map_mulEquiv e⟩
  have h3 : MonoidHom.ofInjective h₂ (e c₁) =
      MulEquiv.subgroupCongr h (MonoidHom.ofInjective h₁ c₁) := by
    rw [he, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have h4 := congrArg (fun x : ψ₂.range => (x : Γ)) h3
  simpa [MonoidHom.ofInjective_apply] using h4

end Sylow

section Center

variable {n : ℕ} {K : Type*} [Field K]

theorem xab_first_last_mul_comm (hn : 2 ≤ n) (c : K) {u : projectiveSL n K}
    (hu : u ∈ projUnitriangular n K) :
    u * xab (firstIdx_ne_lastIdx hn) c = xab (firstIdx_ne_lastIdx hn) c * u := by
  obtain ⟨U, hU, rfl⟩ := hu
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hU
  rw [xab, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul, add_right_inj]
  set i₀ := firstIdx hn with hi₀
  set l := lastIdx hn with hl
  ext i j
  by_cases hj : j = l
  · subst hj
    rw [Matrix.mul_single_apply_same]
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.single_mul_apply_same, hdiag, hdiag, one_mul, mul_one]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi,
        hlow i i₀ (firstIdx_lt_of_ne hn hi), zero_mul]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hj]
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.single_mul_apply_same, hlow l j (lt_lastIdx_of_ne hn hj), mul_zero]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi]

theorem centralizesSylow_of_isInvolutionClass_one [Finite K] [CharP K 2] (hn : 2 ≤ n)
    {z : projectiveSL n K} (hz : IsInvolutionClass 1 z) : CentralizesSylow 2 z := by
  obtain ⟨c, hc⟩ := exists_conj_eq_xab (firstIdx_ne_lastIdx hn) hz
  obtain ⟨U₀, hU₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (by omega : 1 ≤ n)
  have h0 : CentralizesSylow 2 (xab (K := K) (firstIdx_ne_lastIdx hn) 1) :=
    ⟨U₀, fun s hs => xab_first_last_mul_comm hn 1 (hU₀ ▸ hs)⟩
  have h1 := h0.map_mulEquiv (MulAut.conj c⁻¹)
  have h2 : MulAut.conj c⁻¹ (xab (K := K) (firstIdx_ne_lastIdx hn) 1) = z := by
    rw [← hc, MulAut.conj_apply]
    group
  rwa [h2] at h1

theorem isInvolutionClass_one_of_centralizesSylow [Finite K] [CharP K 2] (hn : 2 ≤ n)
    {z : projectiveSL n K} (hz1 : z ≠ 1) (hz : CentralizesSylow 2 z) : IsInvolutionClass 1 z := by
  obtain ⟨U, hU⟩ := hz
  exact isInvolutionClass_one_of_mem_centralizer_sylow hn U hz1 hU

end Center

section Subfield

variable {n : ℕ} {K : Type*} [Field K]

theorem linearSubfieldInclusion_xab (k : Subfield K) {a b : Fin n} (hab : a ≠ b) (c : k) :
    linearSubfieldInclusion n k (xab hab c) = xab hab (c : K) := by
  rw [xab, xab, linearSubfieldInclusion_proj]
  congr 1
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe, map_add, map_one]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, single_apply]
  split_ifs <;> simp

theorem isInvolutionClass_one_linearSubfieldInclusion [Finite K] [CharP K 2] (hn : 2 ≤ n)
    {k : Subfield K} {z : projectiveSL n k} (hz : IsInvolutionClass 1 z) :
    IsInvolutionClass 1 (linearSubfieldInclusion n k z) := by
  obtain ⟨c, hc⟩ := exists_conj_eq_xab (firstIdx_ne_lastIdx hn) hz
  set j := linearSubfieldInclusion n k with hj
  have h1 : j (c * z * c⁻¹) = xab (K := K) (firstIdx_ne_lastIdx hn) 1 := by
    rw [hc, hj, linearSubfieldInclusion_xab, OneMemClass.coe_one]
  have h2 : j z = (j c)⁻¹ * j (c * z * c⁻¹) * ((j c)⁻¹)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    group
  rw [h2, h1]
  exact (isInvolutionClass_one_xab (K := K) (firstIdx_ne_lastIdx hn)).conj (j c)⁻¹

theorem isInvolutionClass_one_of_linearSubfieldInclusion [Finite K] [CharP K 2] (hn : 0 < n)
    {k : Subfield K} {z : projectiveSL n k}
    (hz : IsInvolutionClass 1 (linearSubfieldInclusion n k z)) : IsInvolutionClass 1 z := by
  obtain ⟨g, hgz, hgg, hrk⟩ := hz
  obtain ⟨g₀, rfl⟩ := proj_surjective n k z
  rw [linearSubfieldInclusion_proj] at hgz
  set ι : SpecialLinearGroup (Fin n) k →* SpecialLinearGroup (Fin n) K :=
    SpecialLinearGroup.map k.subtype with hι
  have hιapp : ∀ (x : SpecialLinearGroup (Fin n) k) (i j : Fin n),
      ((ι x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
        (((x : Matrix (Fin n) (Fin n) k) i j : k) : K) := fun _ _ _ => rfl
  have hιinj : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    ext i j
    exact congrFun (congrFun (congrArg Subtype.val hxy) i) j
  obtain ⟨c, hcn, hc⟩ := proj_eq_proj_iff.1 hgz
  have hg₀ : ((ι g₀ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K) • (g : Matrix (Fin n) (Fin n) K) := by
    have e1 : ι g₀ = g * (g⁻¹ * ι g₀) := by group
    rw [e1, Matrix.SpecialLinearGroup.coe_mul, hc, scalar_apply, ← smul_one_eq_diagonal,
      Matrix.mul_smul, Matrix.mul_one]
  have hgg' : (g : Matrix (Fin n) (Fin n) K) * g = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hgg, Matrix.SpecialLinearGroup.coe_one]
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  set d : k := ((g₀ * g₀ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) i₀ i₀
    with hd
  have hcd : (c : K) ^ 2 = (d : K) := by
    have h1 : ((ι (g₀ * g₀) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((c : K) ^ 2) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hg₀, Matrix.smul_mul, Matrix.mul_smul,
        hgg', smul_smul, sq]
    have h2 := congrFun (congrFun h1 i₀) i₀
    rw [hιapp, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
    rw [hd, h2]
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) d
  have hrc : (r : K) = c := by
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have hr' : (r : K) * r = (c : K) ^ 2 := by
      rw [hcd, hr, Subfield.coe_mul]
    have h1 : ((r : K) - c) ^ 2 = 0 := by
      linear_combination hr' + ((c : K) ^ 2 - (r : K) * c) * h2K
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1)
  have hr0 : r ≠ 0 := by
    intro h0
    apply c.ne_zero
    rw [← hrc, h0, ZeroMemClass.coe_zero]
  set e : kˣ := Units.mk0 r hr0 with he
  have hcn' : (c : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hcn, Units.val_one]
  have hen : e ^ n = 1 := by
    apply Units.ext
    apply Subtype.ext
    rw [Units.val_pow_eq_pow_val, he, Units.val_mk0, SubmonoidClass.coe_pow, hrc, hcn',
      Units.val_one, OneMemClass.coe_one]
  have hen' : e⁻¹ ^ n = 1 := by rw [inv_pow, hen, inv_one]
  set s : SpecialLinearGroup (Fin n) k := scalarElement e⁻¹ hen' with hs
  set g₁ := g₀ * s with hg₁
  have hs1 : proj n k s = 1 := proj_eq_one_iff.2 ⟨e⁻¹, hen', rfl⟩
  have hproj : proj n k g₁ = proj n k g₀ := by rw [hg₁, map_mul, hs1, mul_one]
  have hιs : ((ι s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (c : K)⁻¹ • (1 : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rw [hιapp, Matrix.smul_apply, smul_eq_mul]
    have hes : (((e⁻¹ : kˣ) : k) : K) = (c : K)⁻¹ := by
      rw [Units.val_inv_eq_inv_val, he, Units.val_mk0, Subfield.coe_inv, hrc]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_one, ← hes]
      change (((scalar (Fin n) ((e⁻¹ : kˣ) : k)) i i : k) : K) = _
      rw [scalar_apply, diagonal_apply_eq]
    · rw [Matrix.one_apply_ne hij, mul_zero]
      change (((scalar (Fin n) ((e⁻¹ : kˣ) : k)) i j : k) : K) = 0
      rw [scalar_apply, diagonal_apply_ne _ hij, ZeroMemClass.coe_zero]
  have hιg₁ : ι g₁ = g := by
    apply Subtype.ext
    change ((ι (g₀ * s) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = g
    rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hg₀, hιs, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, inv_mul_cancel₀ c.ne_zero, one_smul]
  have hg₁g₁ : g₁ * g₁ = 1 := hιinj (by rw [map_mul, hιg₁, hgg, map_one])
  obtain ⟨m, u, w, hu, hw, huw, h, hh⟩ := exists_conj_eq_one_add_nilOf (K := k) hg₁g₁
  have hdetk : ∀ A : SpecialLinearGroup (Fin n) k, IsUnit (A : Matrix (Fin n) (Fin n) k).det :=
    fun A => by rw [A.2]; exact isUnit_one
  have hdetK : ∀ A : SpecialLinearGroup (Fin n) K, IsUnit (A : Matrix (Fin n) (Fin n) K).det :=
    fun A => by rw [A.2]; exact isUnit_one
  have hhk : (h : Matrix (Fin n) (Fin n) k) * ((h⁻¹ : SpecialLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hNk : nilOf k u w = (h : Matrix (Fin n) (Fin n) k) * ((g₁ : Matrix (Fin n) (Fin n) k) - 1) *
      ((h⁻¹ : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hhk, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hh, add_sub_cancel_left]
  have hrkk : ((g₁ : Matrix (Fin n) (Fin n) k) - 1).rank = m := by
    rw [← rank_nilOf (K := k) hu hw, hNk, rank_mul_eq_left_of_isUnit_det _ _ (hdetk _),
      rank_mul_eq_right_of_isUnit_det _ _ (hdetk _)]
  have hhK : ((ι h * g * (ι h)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + nilOf K u w := by
    rw [← hιg₁, ← map_inv, ← map_mul, ← map_mul]
    ext i j
    rw [hιapp, hh]
    simp only [Matrix.add_apply, Matrix.one_apply, nilOf_apply]
    split_ifs <;> simp
  have hhK' : (ι h : Matrix (Fin n) (Fin n) K) * (((ι h)⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hNK : nilOf K u w = (ι h : Matrix (Fin n) (Fin n) K) * ((g : Matrix (Fin n) (Fin n) K) - 1) *
      (((ι h)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hhK', ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, hhK, add_sub_cancel_left]
  have hm : m = 1 := by
    rw [← rank_nilOf (K := K) hu hw, hNK, rank_mul_eq_left_of_isUnit_det _ _ (hdetK _),
      rank_mul_eq_right_of_isUnit_det _ _ (hdetK _), hrk]
  exact ⟨g₁, hproj, hg₁g₁, hrkk.trans hm⟩

end Subfield

end CFSG.SeitzReduction.LinearPilot
