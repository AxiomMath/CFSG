module

public import CFSG.LargeExtraspecial.DWTrans
public import CFSG.LargeExtraspecial.S3Qa

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G]

@[expose] def conjSub (A : Subgroup G) (h : G) : Subgroup G := A.map (MulAut.conj h).toMonoidHom

theorem mem_conjSub {A : Subgroup G} {h b : G} : b ∈ conjSub A h ↔ h⁻¹ * b * h ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro hb
    exact ⟨h⁻¹ * b * h, hb, by simp [mul_assoc]⟩

theorem conj_mem_conjSub {A : Subgroup G} {h a : G} (ha : a ∈ A) : h * a * h⁻¹ ∈ conjSub A h :=
  mem_conjSub.mpr (by simpa [mul_assoc] using ha)

theorem conj_mem_conjSub_mul {A : Subgroup G} {h u b : G} (hb : b ∈ conjSub A h) :
    u * b * u⁻¹ ∈ conjSub A (u * h) :=
  mem_conjSub.mpr (by simpa [mul_assoc] using mem_conjSub.mp hb)

theorem conjSub_one (A : Subgroup G) : conjSub A 1 = A := by
  ext b
  rw [mem_conjSub, inv_one, one_mul, mul_one]

instance isElementaryAbelian_conjSub (A : Subgroup G) [IsElementaryAbelian 2 A] (h : G) :
    IsElementaryAbelian 2 (conjSub A h) :=
  IsElementaryAbelian.map (A := A) _

variable {S : Setting G} {A : Subgroup G}

theorem conjSub_eq_of_conj_eq (hM : S.M ≤ normalizer (A : Set G)) {h h' : G}
    (hhh : h * S.z * h⁻¹ = h' * S.z * h'⁻¹) : conjSub A h = conjSub A h' := by
  have hm : h'⁻¹ * h ∈ S.M := by
    rw [S.mem_M_iff]
    calc h'⁻¹ * h * S.z = h'⁻¹ * (h * S.z * h⁻¹) * h := by group
      _ = h'⁻¹ * (h' * S.z * h'⁻¹) * h := by rw [hhh]
      _ = S.z * (h'⁻¹ * h) := by group
  ext b
  rw [mem_conjSub, mem_conjSub]
  have key := mem_normalizer_iff.mp (hM hm) (h⁻¹ * b * h)
  have e : h'⁻¹ * h * (h⁻¹ * b * h) * (h'⁻¹ * h)⁻¹ = h'⁻¹ * b * h' := by group
  rw [e] at key
  exact key

theorem conjBy_M_le_normalizer (hM : S.M ≤ normalizer (A : Set G)) (h : G) :
    (S.conjBy h).M ≤ normalizer (conjSub A h : Set G) := by
  intro m hm
  have hm' : h⁻¹ * m * h ∈ S.M := by
    rw [S.mem_M_iff]
    have := (S.conjBy h).mem_M_iff.mp hm
    rw [Setting.conjBy_z] at this
    calc h⁻¹ * m * h * S.z = h⁻¹ * (m * (h * S.z * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * S.z * h⁻¹) * m) * h := by rw [this]
      _ = S.z * (h⁻¹ * m * h) := by group
  rw [mem_normalizer_iff]
  intro b
  rw [mem_conjSub, mem_conjSub]
  have key := mem_normalizer_iff.mp (hM hm') (h⁻¹ * b * h)
  have e : h⁻¹ * m * h * (h⁻¹ * b * h) * (h⁻¹ * m * h)⁻¹ = h⁻¹ * (m * b * m⁻¹) * h := by group
  rw [e] at key
  exact key

variable [Finite G]

theorem eq_of_forall_conj_mem {T : Setting G} {w : G} (hw : w ∈ T.QG) (hw0 : T.cl w ≠ 0)
    {J : Subgroup G} (hJ : J ≤ T.QG) (hzJ : T.z ∉ J)
    (hnorm : ∀ q ∈ T.QG, q * w = w * q → ∀ j ∈ J, q * j * q⁻¹ ∈ J) {j : G} (hj : j ∈ J) :
    j = 1 ∨ j = w ∨ j = w * T.z := by
  have hjQ := hJ hj
  by_contra hne
  push Not at hne
  obtain ⟨hj1, hjw, hjwz⟩ := hne
  have hspan : T.cl j ∉ Submodule.span (ZMod 2) {T.cl w} := by
    rw [CFSG.GroupTheory.GLnTwoSplitting.mem_span_singleton_iff_two]
    rintro (h0 | h0)
    · rcases (T.cl_eq_zero_iff hjQ).mp h0 with h | h
      · exact hj1 h
      · exact hzJ (h ▸ hj)
    · rcases (T.cl_eq_cl_iff hw hjQ).mp h0.symm with h | h
      · exact hjw h
      · exact hjwz h
  set W := LinearMap.BilinForm.orthogonal T.q.polarBilin (Submodule.span (ZMod 2) {T.cl w})
  have hdouble : LinearMap.BilinForm.orthogonal T.q.polarBilin W =
      Submodule.span (ZMod 2) {T.cl w} := by
    have hle : Submodule.span (ZMod 2) {T.cl w} ≤
        LinearMap.BilinForm.orthogonal T.q.polarBilin W := by
      rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
        LinearMap.BilinForm.mem_orthogonal_iff]
      intro v hv
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv
      have := hv (T.cl w) (Submodule.mem_span_singleton_self _)
      change polar T.q v (T.cl w) = 0
      rw [polar_comm]
      exact this
    have h1 := LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate W
    have h2 : finrank (ZMod 2) W = finrank (ZMod 2) T.Qt -
        finrank (ZMod 2) (Submodule.span (ZMod 2) {T.cl w}) :=
      LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate _
    have h3 : finrank (ZMod 2) (Submodule.span (ZMod 2) {T.cl w}) = 1 :=
      finrank_span_singleton hw0
    have h5 := Submodule.finrank_le (Submodule.span (ZMod 2) {T.cl w})
    exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  have hnot : T.cl j ∉ LinearMap.BilinForm.orthogonal T.q.polarBilin W := by
    rw [hdouble]
    exact hspan
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hnot
  push Not at hnot
  obtain ⟨v, hvW, hv⟩ := hnot
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hvW
  obtain ⟨q, hq, rfl⟩ := T.exists_cl v
  have hqw : q * w = w * q := by
    have := hvW (T.cl w) (Submodule.mem_span_singleton_self _)
    exact ((T.polar_cl_eq_zero_iff hw hq).mp this).symm
  have hqj : j * q ≠ q * j := by
    intro hc
    exact hv ((T.polar_cl_eq_zero_iff hq hjQ).mpr hc.symm)
  have hmem := hnorm q hq hqw j hj
  rcases T.mul_comm_or hq hjQ with hc | hc
  · exact hqj hc.symm
  · apply hzJ
    have : q * j * q⁻¹ = T.z * j := by rw [hc]; group
    rw [this] at hmem
    simpa using J.mul_mem hmem (J.inv_mem hj)

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A)
include hA

omit [IsElementaryAbelian 2 A] in
theorem conj (h : G) : MaxEA (S.conjBy h) (conjSub A h) := by
  refine ⟨?_, ?_⟩
  · rw [show (S.conjBy h).QG = S.Qa h from rfl, Setting.Qa_eq_map, conjSub]
    exact Subgroup.map_mono hA.le_QG
  · rw [S.width_conjBy, conjSub, Subgroup.card_map_of_injective (MulAut.conj h).injective,
      hA.card_eq]

variable (hM : S.M ≤ normalizer (A : Set G)) {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG)
  (hxA : h * S.z * h⁻¹ ∉ A)
include hM hxQ hxA

omit hM hxQ in
theorem conj_ne_z : h * S.z * h⁻¹ ≠ S.z := fun e => hxA (by rw [e]; exact hA.z_mem)

theorem z_not_mem_conjSub : S.z ∉ conjSub A h := by
  intro hz
  obtain ⟨u, -, huz, hux⟩ := S.exists_swap rfl hxQ (hA.conj_ne_z hxA)
  have h1 : u * S.z * u⁻¹ ∈ conjSub A (u * h) := conj_mem_conjSub_mul hz
  have h2 : conjSub A (u * h) = A := by
    rw [conjSub_eq_of_conj_eq hM (h' := 1)
      (by rw [show u * h * S.z * (u * h)⁻¹ = u * (h * S.z * h⁻¹) * u⁻¹ by group, hux]; group),
      conjSub_one]
  rw [h2, huz] at h1
  exact hxA h1

omit hM in
theorem cl_conj_ne_zero : S.cl (h * S.z * h⁻¹) ≠ 0 := by
  rw [Ne, S.cl_eq_zero_iff hxQ, not_or]
  refine ⟨fun e => S.z_ne_one ?_, hA.conj_ne_z hxA⟩
  have : h⁻¹ * (h * S.z * h⁻¹) * h = h⁻¹ * 1 * h := by rw [e]
  simpa [mul_assoc] using this

theorem eq_of_mem_conjSub_of_mem_QG {b : G} (hb : b ∈ conjSub A h) (hbQ : b ∈ S.QG) :
    b = 1 ∨ b = h * S.z * h⁻¹ := by
  have hx_mem : h * S.z * h⁻¹ ∈ conjSub A h := conj_mem_conjSub hA.z_mem
  have hzJ : S.z ∉ conjSub A h ⊓ S.QG := fun hz => hA.z_not_mem_conjSub hM hxQ hxA hz.1
  have hnorm : ∀ q ∈ S.QG, q * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * q →
      ∀ j ∈ conjSub A h ⊓ S.QG, q * j * q⁻¹ ∈ conjSub A h ⊓ S.QG := by
    intro q hq hqx j hj
    have hqM : q ∈ (S.conjBy h).M := by
      rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
      exact hqx
    exact ⟨(mem_normalizer_iff.mp (conjBy_M_le_normalizer hM h hqM) j).mp hj.1,
      S.conj_mem_QG (S.QG_le_M hq) hj.2⟩
  rcases eq_of_forall_conj_mem (T := S) hxQ (hA.cl_conj_ne_zero hxQ hxA) inf_le_right hzJ
    hnorm ⟨hb, hbQ⟩ with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · refine absurd ?_ (hA.z_not_mem_conjSub hM hxQ hxA)
    have := (conjSub A h).mul_mem ((conjSub A h).inv_mem hx_mem) (h1 ▸ hb)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem eq_of_mem_Qa {b : G} (hb : b ∈ A) (hbQ : b ∈ S.Qa h) : b = 1 ∨ b = S.z := by
  have hne := hA.conj_ne_z hxA
  set T := S.conjBy h
  have hzT : S.z ∈ T.QG := S.z_mem_Qa_of_mem_QG rfl hxQ hne
  have hTz : T.z = h * S.z * h⁻¹ := rfl
  have hz0 : T.cl S.z ≠ 0 := by
    rw [Ne, T.cl_eq_zero_iff hzT, not_or, hTz]
    exact ⟨S.z_ne_one, hne.symm⟩
  have hzJ : T.z ∉ A ⊓ T.QG := fun hz => hxA hz.1
  have hnorm : ∀ q ∈ T.QG, q * S.z = S.z * q → ∀ j ∈ A ⊓ T.QG, q * j * q⁻¹ ∈ A ⊓ T.QG :=
    fun q hq hqz j hj => ⟨(mem_normalizer_iff.mp (hM (S.mem_M_iff.mpr hqz)) j).mp hj.1,
      T.conj_mem_QG (T.QG_le_M hq) hj.2⟩
  rcases eq_of_forall_conj_mem (T := T) hzT hz0 inf_le_right hzJ hnorm ⟨hb, hbQ⟩
    with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1
  · refine absurd ?_ hxA
    have := A.mul_mem (A.inv_mem hA.z_mem) (h1 ▸ hb)
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this

theorem eq_one_of_mem_conjSub {b : G} (hb : b ∈ A) (hb' : b ∈ conjSub A h) : b = 1 :=
  (hA.eq_of_mem_conjSub_of_mem_QG hM hxQ hxA hb' (hA.le_QG hb)).resolve_right
    fun e => hxA (e ▸ hb)

theorem commute_of_commute {a b : G} (ha : a ∈ A) (hax : a * (h * S.z * h⁻¹) =
    (h * S.z * h⁻¹) * a) (hb : b ∈ conjSub A h) (hbz : b * S.z = S.z * b) : a * b = b * a := by
  have hbM : b ∈ S.M := S.mem_M_iff.mpr hbz
  have haM : a ∈ (S.conjBy h).M := by
    rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
    exact hax
  have hc1 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have := (mem_normalizer_iff.mp (hM hbM) a⁻¹).mp (A.inv_mem ha)
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact A.mul_mem ha this
  have hc2 : a * b * a⁻¹ * b⁻¹ ∈ conjSub A h :=
    (conjSub A h).mul_mem ((mem_normalizer_iff.mp (conjBy_M_le_normalizer hM h haM) b).mp hb)
      ((conjSub A h).inv_mem hb)
  have := hA.eq_one_of_mem_conjSub hM hxQ hxA hc1 hc2
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [this, one_mul]

end MaxEA

end CFSG.LargeExtraspecial.DW
