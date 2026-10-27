module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRadSub
public import CFSG.LocalAnalysis.ComponentClassification.AS81Cover
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS81

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ComponentClassification.RankTwoL3Even
open scoped Pointwise

section Matrix

variable {k : Type} [Field k] [Finite k]

theorem mem_projUnip_of_commute_projCenterW (hk : Nat.card k = 4) {c : k} (hc : c ≠ 0)
    {y : projectiveSL 3 k}
    (hy : y * proj 3 k (unipU k 0 0 c) = proj 3 k (unipU k 0 0 c) * y) : y ∈ projUnip k := by
  have : CharP k 2 := charP_two_of_card hk
  have := Fintype.ofFinite k
  obtain ⟨g', rfl⟩ := proj_surjective 3 k y
  have h' : conjAut 3 k (SpecialLinearGroup.toGL g') (proj 3 k (unipU k 0 0 c)) =
      proj 3 k (unipU k 0 0 c) := by
    rw [conjAut_toGL, MulAut.conj_apply, hy, mul_inv_cancel_right]
  have hm := mul_eq_mul_of_conjAut_proj_eq rfl (trace_unipU_ne_zero 0 0 c) h'
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at hm
  set M := (g' : Matrix (Fin 3) (Fin 3) k) with hMdef
  have e : ∀ i j, (M * (unipU k 0 0 c : Matrix (Fin 3) (Fin 3) k)) i j =
      ((unipU k 0 0 c : Matrix (Fin 3) (Fin 3) k) * M) i j := fun i j =>
    congrFun (congrFun hm i) j
  have e' : ∀ i j, (if j = 2 then c * M i 0 else 0) = if i = 0 then c * M 2 j else 0 := by
    intro i j
    have h := e i j
    rw [mul_unipU_zero_apply, unipU_zero_mul_apply] at h
    simp only [zero_mul, ite_self, add_zero, zero_add] at h
    exact add_left_cancel h
  have h10 : M 1 0 = 0 := by
    have h := e' 1 2
    rw [ite_eq_left rfl, ite_eq_right (by decide)] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  have h20 : M 2 0 = 0 := by
    have h := e' 2 2
    rw [ite_eq_left rfl, ite_eq_right (by decide)] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  have h21 : M 2 1 = 0 := by
    have h := e' 0 1
    rw [ite_eq_right (by decide), ite_eq_left rfl] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hc
  have h22 : M 2 2 = M 0 0 := by
    have h := e' 0 2
    rw [ite_eq_left rfl, ite_eq_left rfl] at h
    exact (mul_left_cancel₀ hc h).symm
  set s := M 0 0 with hs
  have hdet : s * M 1 1 * s = 1 := by
    have h := g'.2
    rw [← hMdef, Matrix.det_fin_three, h10, h20, h21, h22] at h
    rw [← h]
    ring
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have hs3 : s ^ 3 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one s hs0
    rwa [← Nat.card_eq_fintype_card, hk] at h
  have h11 : M 1 1 = s := by
    calc M 1 1 = s ^ 3 * M 1 1 := by rw [hs3, one_mul]
      _ = s * (s * M 1 1 * s) := by ring
      _ = s := by rw [hdet, mul_one]
  have hsu : (Units.mk0 s hs0) ^ 3 = 1 := Units.ext (by simp [hs3])
  set σ := scalarElement (Units.mk0 s hs0) hsu
  set u := unipU k (M 0 1 * s⁻¹) (M 1 2 * s⁻¹) (M 0 2 * s⁻¹)
  have hg : g' = u * σ := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hMdef]
    simp only [σ, u, scalarElement, coe_unipU, Units.val_mk0, Matrix.mul_apply,
      Fin.sum_univ_three, scalar_apply, diagonal_apply]
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h21, h22, h11, hs0, ← hs]
  rw [mem_projUnip]
  refine ⟨M 0 1 * s⁻¹, M 1 2 * s⁻¹, M 0 2 * s⁻¹, ?_⟩
  rw [hg, map_mul]
  have hσ : proj 3 k σ = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact ⟨Units.mk0 s hs0, hsu, rfl⟩
  rw [hσ, mul_one]

end Matrix

section Cover

variable {A : Type} [Group A] [Finite A]

theorem exists_std_cover (c : L34Cover A) (T : Sylow 2 A) :
    ∃ π' : A ⧸ standardComponentOddCore A →* projectiveSL 3 c.k, Function.Surjective π' ∧
      π'.ker = c.π.ker ∧
      (projUnip c.k).comap π' =
        (T : Subgroup A).map (QuotientGroup.mk' (standardComponentOddCore A)) := by
  set N := standardComponentOddCore A
  set p := QuotientGroup.mk' N
  set S : Sylow 2 (A ⧸ N) := T.mapSurjective (QuotientGroup.mk'_surjective N)
  have hS : (S : Subgroup (A ⧸ N)) = (T : Subgroup A).map p := Sylow.coe_mapSurjective _ _
  obtain ⟨-, -, ⟨S₀, hS₀⟩, -⟩ := field_four_central_two_cover_parabolic_normalizers
    c.card_k c.π c.surj c.ker_le_center c.elem
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (A ⧸ N) S₀ S
  set π' := c.π.comp (MulAut.conj x⁻¹).toMonoidHom
  have hker' : π'.ker = c.π.ker := by
    ext y
    simp only [π', MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← MonoidHom.mem_ker, ← MonoidHom.mem_ker]
    constructor
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x
      simpa [mul_assoc] using this
    · intro h
      have := (MonoidHom.normal_ker c.π).conj_mem _ h x⁻¹
      simpa [mul_assoc] using this
  have hT' : (projUnip c.k).comap π' = (S : Subgroup (A ⧸ N)) := by
    rw [← hx, Sylow.coe_subgroup_smul, hS₀]
    ext y
    rw [mem_pointwise_smul_iff_inv_smul_mem, mem_comap, mem_comap]
    simp [π', MulAut.smul_def]
  exact ⟨π', c.surj.comp (MulAut.conj x⁻¹).surjective, hker', hT'.trans hS⟩

theorem centralizer_le_sup_center (c : L34Cover A) (hNZ : standardComponentOddCore A ≤ center A)
    (T : Sylow 2 A) {h : A} (hh : h ∈ centerIn (T : Subgroup A)) (hhZ : h ∉ center A) :
    centralizer ({h} : Set A) ≤ (T : Subgroup A) ⊔ center A := by
  set N := standardComponentOddCore A
  set p := QuotientGroup.mk' N
  obtain ⟨π', hsurj', hker', hTb⟩ := exists_std_cover c T
  have hCZ' : π'.ker ≤ center (A ⧸ N) := hker' ▸ c.ker_le_center
  have helem' : CFSG.IsElementaryAbelian 2 π'.ker := hker' ▸ c.elem
  obtain ⟨-, -, -, -, -, hcenter, -, -⟩ :=
    field_four_central_two_cover_parabolic_normalizers c.card_k π' hsurj' hCZ' helem'
  set Tb := (projUnip c.k).comap π'
  have hpZ : p h ∈ (projCenterW c.k).comap π' := by
    rw [← hcenter]
    refine ⟨⟨p h, hTb ▸ ⟨h, hh.1, rfl⟩⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rintro ⟨y, hy⟩
    obtain ⟨s, hs, rfl⟩ : y ∈ (T : Subgroup A).map p := hTb ▸ hy
    apply Subtype.ext
    simp only [coe_mul]
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hh.2 s hs]
  obtain ⟨c₀, hc₀⟩ := mem_projCenterW.mp hpZ
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    apply hhZ
    have h1 : π' (p h) = 1 := by
      rw [← hc₀, unipU_zero, map_one]
    have h2 : p h ∈ c.π.ker := hker' ▸ h1
    rw [c.ker_eq] at h2
    obtain ⟨w, hw, hwh⟩ := h2
    have hwN : w⁻¹ * h ∈ N := QuotientGroup.eq.mp hwh
    rw [show h = w * (w⁻¹ * h) by group]
    exact mul_mem hw (hNZ hwN)
  intro y hy
  rw [mem_centralizer_singleton_iff] at hy
  have hpy : π' (p y) ∈ projUnip c.k := by
    apply mem_projUnip_of_commute_projCenterW c.card_k hc₀0
    rw [hc₀, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hy]
  have hyT : p y ∈ (T : Subgroup A).map p := hTb ▸ hpy
  obtain ⟨t, htT, hty⟩ := hyT
  have hN : t⁻¹ * y ∈ N := QuotientGroup.eq.mp hty
  rw [show y = t * (t⁻¹ * y) by group]
  exact mul_mem_sup htT (hNZ hN)

end Cover

end CFSG.ComponentClassification.AS81
