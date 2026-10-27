module

public import CFSG.LocalAnalysis.EvenBN.U5.LinModelDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped Pointwise
open CFSG.ABGLocalTools (IsSylowOf)

namespace LinCase

theorem l3syl_two_eq_zero {K : Type*} [Field K] [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

theorem l3syl_unit_entries {K : Type*} [Field K] {u : Matrix.SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) :
    (u : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (u : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧ (u : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 ∧
      (u : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 ∧ (u : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.mp hu
  exact ⟨hlow 1 0 (by decide), hlow 2 0 (by decide), hlow 2 1 (by decide),
    hdiag 0, hdiag 1, hdiag 2⟩

theorem l3syl_sq_eq_one {K : Type*} [Field K] [CharP K 2] {u : Matrix.SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K)
    (hab : (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    u * u = 1 := by
  obtain ⟨h10, h20, h21, h00, h11, h22⟩ := l3syl_unit_entries hu
  have h2 : (2 : K) = 0 := l3syl_two_eq_zero
  have hx : ∀ x : K, x + x = 0 := fun x => by linear_combination x * h2
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, h10, h20, h21, h00, h11, h22] <;>
    first
      | exact hx _
      | linear_combination hx ((u : Matrix (Fin 3) (Fin 3) K) 0 2) + hab

theorem l3syl_upper_of_mul_eq {K : Type*} [Field K] {g u u' : Matrix.SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hu' : u' ∈ unitriangular 3 K)
    (ha : (u : Matrix (Fin 3) (Fin 3) K) 0 1 ≠ 0) (hb : (u : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0)
    (h : (g : Matrix (Fin 3) (Fin 3) K) * (u' : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K)) :
    g ∈ upperTriangular 3 K := by
  obtain ⟨h10, h20, h21, h00, h11, h22⟩ := l3syl_unit_entries hu
  obtain ⟨h'10, h'20, h'21, h'00, h'11, h'22⟩ := l3syl_unit_entries hu'
  have e00 := congrFun (congrFun h 0) 0
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h00, h11, h22, h'10, h'20,
    h'21, h'00, h'11, h'22] at e00 e10 e11
  have hg20 : (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    have : (u : Matrix (Fin 3) (Fin 3) K) 1 2 * (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
      linear_combination (-1 : K) * e10
    exact (mul_eq_zero.mp this).resolve_left hb
  have hg10 : (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    have : (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
      linear_combination (-1 : K) * e00 - (u : Matrix (Fin 3) (Fin 3) K) 0 2 * hg20
    exact (mul_eq_zero.mp this).resolve_left ha
  have hg21 : (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    have : (u : Matrix (Fin 3) (Fin 3) K) 1 2 * (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
      linear_combination (-1 : K) * e11 + (u' : Matrix (Fin 3) (Fin 3) K) 0 1 * hg10
    exact (mul_eq_zero.mp this).resolve_left hb
  rw [mem_upperTriangular]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem l3syl_mul_eq_of_conj_mem {K : Type*} [Field K] [CharP K 2]
    {g u u' : Matrix.SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hu' : u' ∈ unitriangular 3 K)
    (h : u⁻¹ * (g * u' * g⁻¹) ∈ scalars 3 K) :
    (g : Matrix (Fin 3) (Fin 3) K) * (u' : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h
  have h2 : (2 : K) = 0 := l3syl_two_eq_zero
  obtain ⟨h10, h20, h21, h00, h11, h22⟩ := l3syl_unit_entries hu
  obtain ⟨h'10, h'20, h'21, h'00, h'11, h'22⟩ := l3syl_unit_entries hu'
  have hMA : g * u' * g⁻¹ = u * (u⁻¹ * (g * u' * g⁻¹)) := (mul_inv_cancel_left u _).symm
  have hcoe : ((g * u' * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (u : Matrix (Fin 3) (Fin 3) K) * scalar (Fin 3) (c : K) := by
    rw [← hc, ← Matrix.SpecialLinearGroup.coe_mul, ← hMA]
  have htr1 : Matrix.trace ((g * u' * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = Matrix.trace (u' : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
      LinearFlag.coe_inv_mul_coe, Matrix.one_mul]
  have htr2 : Matrix.trace ((g * u' * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = (c : K) + c + c := by
    rw [hcoe, Matrix.trace, Fin.sum_univ_three]
    simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, h00, h11, h22]
  have htr3 : Matrix.trace (u' : Matrix (Fin 3) (Fin 3) K) = 1 + 1 + 1 := by
    rw [Matrix.trace_fin_three, h'00, h'11, h'22]
  have hc1 : (c : K) = 1 := by
    have htr : (c : K) + c + c = 1 + 1 + 1 := by rw [← htr2, htr1, htr3]
    linear_combination htr - ((c : K) - 1) * h2
  have hA1 : u⁻¹ * (g * u' * g⁻¹) = 1 := by
    apply Subtype.ext
    rw [hc, hc1, Matrix.SpecialLinearGroup.coe_one, Matrix.scalar_apply, Matrix.diagonal_one]
  have hgu : g * u' * g⁻¹ = u := by
    calc g * u' * g⁻¹ = u * (u⁻¹ * (g * u' * g⁻¹)) := hMA
      _ = u := by rw [hA1, mul_one]
  have hgu' : g * u' = u * g := by
    rw [← hgu]
    exact (inv_mul_cancel_right (g * u') g).symm
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hgu']

theorem l3syl_conj_mem_unitriangular {K : Type*} [Field K] {g u : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ upperTriangular 3 K) (hu : u ∈ unitriangular 3 K) :
    g * u * g⁻¹ ∈ unitriangular 3 K := by
  have hgU : (g : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp hg
  have huB : u ∈ upperTriangular 3 K := unitriangular_le_upperTriangular 3 K hu
  have huU : (u : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    mem_upperTriangular_iff_isUpperTriangular.mp huB
  have hgi : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular :=
    coe_inv_isUpperTriangular hgU
  have hprod : ((g : Matrix (Fin 3) (Fin 3) K) * (u : Matrix (Fin 3) (Fin 3) K)).IsUpperTriangular := by
    have h := (upperTriangular 3 K).mul_mem hg huB
    rw [mem_upperTriangular_iff_isUpperTriangular, Matrix.SpecialLinearGroup.coe_mul] at h
    exact h
  have hmem : g * u * g⁻¹ ∈ upperTriangular 3 K :=
    (upperTriangular 3 K).mul_mem ((upperTriangular 3 K).mul_mem hg huB)
      ((upperTriangular 3 K).inv_mem hg)
  rw [mem_unitriangular]
  refine ⟨mem_upperTriangular.mp hmem, fun i => ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mul_apply_self_of_isUpperTriangular hprod hgi, mul_apply_self_of_isUpperTriangular hgU huU,
    (mem_unitriangular.mp hu).2 i, mul_one]
  exact coe_inv_apply_self_of_isUpperTriangular hgU i

theorem l3syl_conj_projUnitriangular {K : Type*} [Field K] {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ upperTriangular 3 K) :
    (projUnitriangular 3 K).map (MulAut.conj (proj 3 K g)).toMonoidHom =
      projUnitriangular 3 K := by
  have hginv : g⁻¹ ∈ upperTriangular 3 K := (upperTriangular 3 K).inv_mem hg
  apply le_antisymm
  · rintro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨g * u * g⁻¹, l3syl_conj_mem_unitriangular hg hu, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  · rintro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨proj 3 K (g⁻¹ * u * g⁻¹⁻¹),
      Subgroup.mem_map.mpr ⟨g⁻¹ * u * g⁻¹⁻¹, l3syl_conj_mem_unitriangular hginv hu, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

theorem l3syl_core {K : Type*} [Field K] [CharP K 2] (k : projectiveSL 3 K)
    (hne : projUnitriangular 3 K ≠ (projUnitriangular 3 K).map (MulAut.conj k).toMonoidHom)
    (x : projectiveSL 3 K) (hx1 : x ∈ projUnitriangular 3 K)
    (hx2 : x ∈ (projUnitriangular 3 K).map (MulAut.conj k).toMonoidHom) : x * x = 1 := by
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 K k
  obtain ⟨u, hu, hxu⟩ := Subgroup.mem_map.mp hx1
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx2
  obtain ⟨u', hu', rfl⟩ := Subgroup.mem_map.mp hy
  have hxeq : x = proj 3 K (g * u' * g⁻¹) := by
    rw [← hyx]
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
  have hrel : proj 3 K u = proj 3 K (g * u' * g⁻¹) := by rw [hxu, hxeq]
  have hscal := proj_eq_proj_iff.mp hrel
  have hmat := l3syl_mul_eq_of_conj_mem hu hu' hscal
  by_contra hxx
  have hab : (u : Matrix (Fin 3) (Fin 3) K) 0 1 * (u : Matrix (Fin 3) (Fin 3) K) 1 2 ≠ 0 :=
    fun h => hxx (by rw [← hxu, ← map_mul, l3syl_sq_eq_one hu h, map_one])
  have hg : g ∈ upperTriangular 3 K :=
    l3syl_upper_of_mul_eq hu hu' (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab) hmat
  exact hne (l3syl_conj_projUnitriangular hg).symm

theorem l3syl_sylow_of_isSylowOf {H : Type*} [Group H] [Finite H] {T : Subgroup H}
    (h : IsSylowOf 2 T ⊤) : ∃ S : Sylow 2 H, (S : Subgroup H) = T := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h
  obtain ⟨-, hP, hdvd⟩ := h
  rw [Subgroup.relIndex_top_right] at hdvd
  exact ⟨hP.toSylow hdvd, by simp⟩

theorem l3syl_isSylowOf_map {X H : Type*} [Group X] [Finite X] [Group H] [Finite H] (e : X ≃* H)
    {T : Subgroup X} (h : IsSylowOf 2 T ⊤) : IsSylowOf 2 (T.map e.toMonoidHom) ⊤ := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at h ⊢
  obtain ⟨-, hP, hdvd⟩ := h
  rw [Subgroup.relIndex_top_right] at hdvd ⊢
  have hidx : (T.map e.toMonoidHom).index = T.index := Subgroup.index_map_equiv (H := T) e
  refine ⟨le_top, hP.map _, ?_⟩
  rw [hidx]
  exact hdvd

theorem l3syl_mem_map_conj_iff {H : Type*} [Group H] {S : Subgroup H} {k x : H} :
    x ∈ S.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    exact ⟨k⁻¹ * x * k, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem l3syl_mem_conj_smul_iff {H : Type*} [Group H] {S : Subgroup H} {g x : H} :
    x ∈ MulAut.conj g • S ↔ g⁻¹ * x * g ∈ S := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.conj_inv_apply]

theorem l3syl_reduce {H : Type*} [Group H] [Finite H] (Ū : Subgroup H) (S₀ : Sylow 2 H)
    (hS₀ : (S₀ : Subgroup H) = Ū)
    (hcore : ∀ k : H, Ū ≠ Ū.map (MulAut.conj k).toMonoidHom →
      ∀ x ∈ Ū, x ∈ Ū.map (MulAut.conj k).toMonoidHom → x * x = 1)
    (T₁ T₂ : Subgroup H) (h₁ : IsSylowOf 2 T₁ ⊤) (h₂ : IsSylowOf 2 T₂ ⊤) (hne : T₁ ≠ T₂) :
    ∀ x ∈ T₁ ⊓ T₂, x * x = 1 := by
  subst hS₀
  obtain ⟨S₁, rfl⟩ := l3syl_sylow_of_isSylowOf h₁
  obtain ⟨S₂, rfl⟩ := l3syl_sylow_of_isSylowOf h₂
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₀ S₁
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H S₀ S₂
  have e1 : (S₁ : Subgroup H) = MulAut.conj g • (S₀ : Subgroup H) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have e2 : (S₂ : Subgroup H) = MulAut.conj h • (S₀ : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul]
  have m1 : ∀ y : H, y ∈ (S₁ : Subgroup H) ↔ g⁻¹ * y * g ∈ (S₀ : Subgroup H) := fun y => by
    rw [e1, l3syl_mem_conj_smul_iff]
  have m2 : ∀ y : H, y ∈ (S₂ : Subgroup H) ↔ h⁻¹ * y * h ∈ (S₀ : Subgroup H) := fun y => by
    rw [e2, l3syl_mem_conj_smul_iff]
  have hkz : ∀ y : H, (g⁻¹ * h)⁻¹ * (g⁻¹ * y * g) * (g⁻¹ * h) = h⁻¹ * y * h := fun y => by
    group
  have hne' : (S₀ : Subgroup H) ≠ (S₀ : Subgroup H).map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
    intro heq
    apply hne
    ext y
    have key : ∀ z : H, z ∈ (S₀ : Subgroup H) ↔
        (g⁻¹ * h)⁻¹ * z * (g⁻¹ * h) ∈ (S₀ : Subgroup H) := fun z => by
      rw [← l3syl_mem_map_conj_iff, ← heq]
    rw [m1 y, m2 y, ← hkz y]
    exact key _
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have hz1 : g⁻¹ * x * g ∈ (S₀ : Subgroup H) := (m1 x).mp hx1
  have hz2 : g⁻¹ * x * g ∈ (S₀ : Subgroup H).map (MulAut.conj (g⁻¹ * h)).toMonoidHom := by
    rw [l3syl_mem_map_conj_iff, hkz x]
    exact (m2 x).mp hx2
  have hzz := hcore (g⁻¹ * h) hne' (g⁻¹ * x * g) hz1 hz2
  calc x * x = g * ((g⁻¹ * x * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = 1 := by rw [hzz]; group

theorem l3syl_projective {K : Type*} [Field K] [Finite K] [CharP K 2]
    (T₁ T₂ : Subgroup (projectiveSL 3 K))
    (h₁ : IsSylowOf 2 T₁ ⊤) (h₂ : IsSylowOf 2 T₂ ⊤) (hne : T₁ ≠ T₂) :
    ∀ x ∈ T₁ ⊓ T₂, x * x = 1 := by
  obtain ⟨S₀, hS₀⟩ := LinearFlag.exists_sylow_projUnitriangular (K := K) (n := 3) 2
    (by norm_num)
  exact l3syl_reduce (projUnitriangular 3 K) S₀ hS₀
    (fun k hk x hx1 hx2 => l3syl_core k hk x hx1 hx2) T₁ T₂ h₁ h₂ hne

theorem l3SylowInt : L3SylowIntStatement := by
  intro n hn X _ hfin hX P Q hP hQ hPQ x hx
  obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ :=
    LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hX
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hKcard
  have key := l3syl_projective (K := K) (P.map e.toMonoidHom) (Q.map e.toMonoidHom)
    (l3syl_isSylowOf_map e hP) (l3syl_isSylowOf_map e hQ)
    (fun h => hPQ (Subgroup.map_injective (f := e.toMonoidHom) e.injective h))
    (e x) ⟨Subgroup.mem_map_of_mem _ hx.1, Subgroup.mem_map_of_mem _ hx.2⟩
  apply e.injective
  rw [map_mul, map_one]
  exact key

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
