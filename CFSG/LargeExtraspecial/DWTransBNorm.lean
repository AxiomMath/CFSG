module

public import CFSG.LargeExtraspecial.DWTransB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}

namespace MaxEA

variable [IsElementaryAbelian 2 A] (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G)) {h : G}
  (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
include hA hM hxQ hxA

theorem maxEA_inf : MaxEA S (S.QG ⊓ S.Qa h) :=
  ⟨inf_le_left, hA.card_QG_inf_Qa hM hxQ hxA⟩

theorem eq_zero_of_mem_clSub_inf {v : S.Qt} (hvB : v ∈ S.clSub (S.QG ⊓ S.Qa h))
    (hvA : v ∈ S.clSub A) : v = 0 := by
  obtain ⟨b, hb, hbQ, rfl⟩ := S.mem_clSub_iff.mp hvB
  have hbA : b ∈ A := by
    rw [← hA.clPre_clSub]
    exact ⟨hbQ, hvA⟩
  rcases hA.eq_of_mem_Qa hM hxQ hxA hbA hb.2 with rfl | rfl
  · exact S.cl_one
  · exact S.cl_z

theorem exists_sub_mem (v : S.Qt) : ∃ b ∈ S.clSub (S.QG ⊓ S.Qa h), v - b ∈ S.clSub A := by
  have := S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  have hB := hA.maxEA_inf hM hxQ hxA
  have : Finite (Additive S.Q) := inferInstanceAs (Finite S.Q)
  have : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hdisj : S.clSub A ⊓ S.clSub (S.QG ⊓ S.Qa h) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    exact hA.eq_zero_of_mem_clSub_inf hM hxQ hxA hv.2 hv.1
  have hsup : S.clSub A ⊔ S.clSub (S.QG ⊓ S.Qa h) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub A) (S.clSub (S.QG ⊓ S.Qa h))
    rw [hdisj, finrank_bot, add_zero, hA.finrank_clSub, hB.finrank_clSub] at h1
    rw [h1, S.finrank_Qt_eq_two_mul_width]
    ring
  have hv : v ∈ S.clSub A ⊔ S.clSub (S.QG ⊓ S.Qa h) := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  exact ⟨b, hb, by rwa [add_sub_cancel_right]⟩

theorem eq_zero_of_forall_polar {b : S.Qt} (hb : b ∈ S.clSub (S.QG ⊓ S.Qa h))
    (h0 : ∀ v ∈ S.clSub A, polar S.q v b = 0) : b = 0 := by
  refine hA.eq_zero_of_mem_clSub_inf hM hxQ hxA hb ?_
  rw [← hA.orthogonal_clSub, LinearMap.BilinForm.mem_orthogonal_iff]
  exact fun v hv => h0 v hv

omit [Finite G] [IsElementaryAbelian 2 A] hA hM hxQ hxA in
theorem conj_mem_QG_of_M {m : G} (hm : m ∈ S.M) (hxQ : h * S.z * h⁻¹ ∈ S.QG) :
    (m * h) * S.z * (m * h)⁻¹ ∈ S.QG := by
  rw [show (m * h) * S.z * (m * h)⁻¹ = m * (h * S.z * h⁻¹) * m⁻¹ by group]
  exact S.conj_mem_QG hm hxQ

omit [Finite G] [IsElementaryAbelian 2 A] hA hxQ in
theorem conj_not_mem_of_M {m : G} (hm : m ∈ S.M) : (m * h) * S.z * (m * h)⁻¹ ∉ A := by
  intro hmem
  apply hxA
  have := (mem_normalizer_iff.mp (hM (S.M.inv_mem hm)) _).mp hmem
  rwa [show m⁻¹ * ((m * h) * S.z * (m * h)⁻¹) * m⁻¹⁻¹ = h * S.z * h⁻¹ by group] at this

theorem cl_conj_mem_clSub_inf (hn : 4 ≤ S.width) {m : G} (hm : m ∈ S.M) :
    S.cl ((m * h) * S.z * (m * h)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa h) := by
  have := finite_clSub (S := S) (A := A)
  have : FiniteDimensional (ZMod 2) (S.clSub A) := Module.Finite.of_finite
  have hx'Q := conj_mem_QG_of_M hm hxQ
  have hx'A := conj_not_mem_of_M hM hxA hm
  obtain ⟨b, hb, hab⟩ := hA.exists_sub_mem hM hxQ hxA (S.cl ((m * h) * S.z * (m * h)⁻¹))
  set a := S.cl ((m * h) * S.z * (m * h)⁻¹) - b with ha_def
  have hfixa : ∀ (ψ : Dual (ZMod 2) (S.clSub A)) (c : S.clSub A) (hc : ψ c = 0),
      axisForm S A (h * S.z * h⁻¹) c = 0 → axisForm S A ((m * h) * S.z * (m * h)⁻¹) c = 0 →
      ψ ⟨a, hab⟩ • (c : S.Qt) = 0 := by
    intro ψ c hc hc1 hc2
    obtain ⟨y, hy⟩ := hA.resAt_surjective_of_mem hM hxQ hxA (LinearEquiv.transvection hc)
    have hres : ∀ w : S.clSub A, resAt S A hM y w = w + ψ w • c := fun w => by
      rw [hy, transvection_apply]
    have hfx := hA.fix_of_resAt_mem_ker hM hxQ hxA (by omega) y.2 fun w hw => by
      change axisForm S A (h * S.z * h⁻¹) (resAt S A hM y w) = 0
      rw [hres, map_add, map_smul, hw, hc1, smul_zero, add_zero]
    have hfx' := hA.fix_of_resAt_mem_ker hM hx'Q hx'A (by omega) y.2 fun w hw => by
      change axisForm S A ((m * h) * S.z * (m * h)⁻¹) (resAt S A hM y w) = 0
      rw [hres, map_add, map_smul, hw, hc2, smul_zero, add_zero]
    set Y := ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
    have hyb := hA.apply_mem_clSub_inf_of_fix hxQ hxA y.2 hfx hb
    have hya_mem : Y a ∈ S.clSub A := apply_mem_clSub hM y.2 hab
    have hyb' : Y b = b := by
      have h1 : Y b - b ∈ S.clSub (S.QG ⊓ S.Qa h) := Submodule.sub_mem _ hyb hb
      have h2 : Y b - b ∈ S.clSub A := by
        have e : Y b - b = a - Y a := by
          rw [ha_def, map_sub, hfx']
          abel
        rw [e]
        exact Submodule.sub_mem _ hab hya_mem
      exact sub_eq_zero.mp (hA.eq_zero_of_mem_clSub_inf hM hxQ hxA h1 h2)
    have hya : Y a = a := by rw [ha_def, map_sub, hfx', hyb']
    have h3 := congrArg Subtype.val (hres ⟨a, hab⟩)
    rw [coe_resAt_apply, Submodule.coe_add, Submodule.coe_smul] at h3
    change Y a = a + ψ ⟨a, hab⟩ • (c : S.Qt) at h3
    rw [hya] at h3
    have := congrArg (· - a) h3
    simpa using this.symm
  by_contra hne
  have ha0 : (⟨a, hab⟩ : S.clSub A) ≠ 0 := by
    intro h0
    apply hne
    have : a = 0 := congrArg Subtype.val h0
    rw [ha_def, sub_eq_zero] at this
    rw [this]
    exact hb
  set K := LinearMap.ker (axisForm S A (h * S.z * h⁻¹)) ⊓
    LinearMap.ker (axisForm S A ((m * h) * S.z * (m * h)⁻¹))
  have hK : finrank (ZMod 2) (S.clSub A) ≤ finrank (ZMod 2) K + 2 :=
    finrank_ker_inf_ker_add_two_ge _ _
  rw [hA.finrank_clSub] at hK
  have hspan := finrank_span_singleton (K := ZMod 2) ha0
  obtain ⟨c, hcK, hca⟩ := exists_mem_notMem_of_finrank_lt (U := K)
    (S := Submodule.span (ZMod 2) {(⟨a, hab⟩ : S.clSub A)}) (by omega)
  have hac : (⟨a, hab⟩ : S.clSub A) ∉ Submodule.span (ZMod 2) {c} := by
    rw [mem_span_singleton_iff_two]
    rintro (h0 | h0)
    · exact ha0 h0
    · exact hca (h0 ▸ Submodule.mem_span_singleton_self _)
  obtain ⟨ψ, hψc, hψa⟩ := exists_dual_eq_one_of_notMem hac
  have h4 := hfixa ψ c (hψc c (Submodule.mem_span_singleton_self c)) hcK.1 hcK.2
  rw [hψa, one_smul] at h4
  exact hca (by rw [show c = 0 from Subtype.ext h4]; exact Submodule.zero_mem _)

theorem exists_cl_conj_eq (hn : 4 ≤ S.width) {b : S.Qt} (hb : b ∈ S.clSub (S.QG ⊓ S.Qa h))
    (hb0 : b ≠ 0) : ∃ m ∈ S.M, S.cl ((m * h) * S.z * (m * h)⁻¹) = b := by
  set φb : Dual (ZMod 2) (S.clSub A) := (S.q.polarBilin.flip b) ∘ₗ (S.clSub A).subtype
  have hφb : φb ≠ 0 := fun h0 => hb0 (hA.eq_zero_of_forall_polar hM hxQ hxA hb fun v hv => by
    have := LinearMap.congr_fun h0 ⟨v, hv⟩
    exact this)
  obtain ⟨g₀, -, hg₀⟩ := exists_comp_eq_of_apply_eq_zero (e₀ := (0 : S.clSub A))
    (hA.axisForm_ne_zero hxQ hxA) hφb (map_zero _) (map_zero _)
  obtain ⟨y, hy⟩ := hA.resAt_surjective_of_mem hM hxQ hxA g₀⁻¹
  obtain ⟨m, hmy⟩ := y.2
  refine ⟨m, m.2, ?_⟩
  have hcl := hA.cl_conj_mem_clSub_inf hM hxQ hxA hn m.2
  have hx'cl : S.cl ((m * h) * S.z * (m * h)⁻¹) =
      ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) := by
    rw [← hmy, S.ρ_cl m hxQ]
    congr 1
    group
  have hdiff := hA.eq_zero_of_forall_polar hM hxQ hxA (Submodule.sub_mem _ hb hcl) fun v hv => by
    rw [polar_sub_right, hx'cl]
    have hv' : ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm v =
        ((resAt S A hM y)⁻¹ ⟨v, hv⟩ : S.clSub A) := by
      rw [← map_inv]
      rfl
    have e1 : polar S.q v (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹))) =
        polar S.q (((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).symm v) (S.cl (h * S.z * h⁻¹)) := by
      conv_lhs => rw [← LinearEquiv.apply_symm_apply ((y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v]
      exact polar_apply_apply (y : S.O) _ _
    rw [e1, hv', hy, inv_inv]
    have e2 : polar S.q v b = φb ⟨v, hv⟩ := rfl
    rw [e2, ← hg₀]
    exact sub_self _
  exact (sub_eq_zero.mp hdiff).symm

theorem conj_mem_inf (hn : 4 ≤ S.width) {m b : G} (hm : m ∈ S.M) (hb : b ∈ S.QG ⊓ S.Qa h) :
    m * b * m⁻¹ ∈ S.QG ⊓ S.Qa h := by
  have := S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  have hB := hA.maxEA_inf hM hxQ hxA
  rw [← hB.clPre_clSub]
  refine ⟨S.conj_mem_QG hm hb.1, ?_⟩
  rw [show S.cl (m * b * m⁻¹) = ((S.ρ ⟨m, hm⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) from
    (S.ρ_cl ⟨m, hm⟩ hb.1).symm]
  by_cases hb0 : S.cl b = 0
  · rw [hb0, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨m', hm', hcl⟩ := hA.exists_cl_conj_eq hM hxQ hxA hn (S.cl_mem_clSub hb hb.1) hb0
  rw [← hcl, S.ρ_cl ⟨m, hm⟩ (conj_mem_QG_of_M hm' hxQ)]
  rw [show (m : G) * ((m' * h) * S.z * (m' * h)⁻¹) * (m : G)⁻¹ =
    ((m * m') * h) * S.z * ((m * m') * h)⁻¹ by group]
  exact hA.cl_conj_mem_clSub_inf hM hxQ hxA hn (S.M.mul_mem hm hm')

theorem M_le_normalizer_inf (hn : 4 ≤ S.width) :
    S.M ≤ normalizer ((S.QG ⊓ S.Qa h : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro b
  refine ⟨fun hb => hA.conj_mem_inf hM hxQ hxA hn hm hb, fun hb => ?_⟩
  have := hA.conj_mem_inf hM hxQ hxA hn (S.M.inv_mem hm) hb
  rwa [show m⁻¹ * (m * b * m⁻¹) * m⁻¹⁻¹ = b by group] at this

theorem exists_conj_eq_of_mem_inf (hn : 4 ≤ S.width) {b : G} (hb : b ∈ S.QG ⊓ S.Qa h)
    (hb1 : b ≠ 1) : ∃ g : G, g * S.z * g⁻¹ = b := by
  by_cases hcl : S.cl b = 0
  · rcases (S.cl_eq_zero_iff hb.1).mp hcl with h1 | h1
    · exact absurd h1 hb1
    · exact ⟨1, by rw [h1]; group⟩
  obtain ⟨m', hm', hcl'⟩ := hA.exists_cl_conj_eq hM hxQ hxA hn (S.cl_mem_clSub hb hb.1) hcl
  have hx'Q := conj_mem_QG_of_M hm' hxQ
  rcases (S.cl_eq_cl_iff hx'Q hb.1).mp hcl' with e | e
  · exact ⟨m' * h, e.symm⟩
  · have hx'1 : (m' * h) * S.z * (m' * h)⁻¹ ≠ 1 := fun e1 => S.z_ne_one (by
      have : (m' * h)⁻¹ * ((m' * h) * S.z * (m' * h)⁻¹) * (m' * h) = 1 := by rw [e1]; group
      simpa [mul_assoc] using this)
    have hx'z : (m' * h) * S.z * (m' * h)⁻¹ ≠ S.z := fun e1 =>
      conj_not_mem_of_M hM hxA hm' (by rw [e1]; exact hA.z_mem)
    obtain ⟨q, hq, hqx⟩ := S.exists_conj_eq_mul_z hx'Q hx'1 hx'z
    refine ⟨q * (m' * h), ?_⟩
    rw [e, ← hqx]
    group

omit [Finite G] [IsElementaryAbelian 2 A] hA hM hxQ hxA in
theorem Qa_mul_eq_map (k : G) : S.Qa (k * h) = (S.Qa h).map (MulAut.conj k).toMonoidHom := by
  rw [Setting.Qa_eq_map, Setting.Qa_eq_map, Subgroup.map_map]
  congr 1
  ext b
  simp [mul_assoc]

theorem le_Qa_mul (hn : 4 ≤ S.width) {k : G} (hk : k ∈ S.M) :
    S.QG ⊓ S.Qa h ≤ S.Qa (k * h) := by
  intro b hb
  rw [Qa_mul_eq_map]
  have := hA.conj_mem_inf hM hxQ hxA hn (S.M.inv_mem hk) hb
  exact ⟨k⁻¹ * b * k⁻¹⁻¹, this.2, by simp [mul_assoc]⟩

theorem inf_le_Qa (hn : 4 ≤ S.width) {g : G} (hg : g * S.z * g⁻¹ ∈ S.QG ⊓ S.Qa h) :
    S.QG ⊓ S.Qa h ≤ S.Qa g := by
  by_cases hcl : S.cl (g * S.z * g⁻¹) = 0
  · rcases (S.cl_eq_zero_iff hg.1).mp hcl with h1 | h1
    · exact absurd (by simpa [mul_assoc] using congrArg (fun t => g⁻¹ * t * g) h1)
        S.z_ne_one
    · rw [S.Qa_eq_of_conj_eq (g := g) (h := 1) (by rw [h1]; group), S.Qa_one]
      exact inf_le_left
  obtain ⟨m', hm', hcl'⟩ := hA.exists_cl_conj_eq hM hxQ hxA hn (S.cl_mem_clSub hg hg.1) hcl
  have hx'Q := conj_mem_QG_of_M hm' hxQ
  rcases (S.cl_eq_cl_iff hx'Q hg.1).mp hcl' with e | e
  · rw [S.Qa_eq_of_conj_eq (g := g) (h := m' * h) e]
    exact hA.le_Qa_mul hM hxQ hxA hn hm'
  · have hx'1 : (m' * h) * S.z * (m' * h)⁻¹ ≠ 1 := fun e1 => S.z_ne_one (by
      have : (m' * h)⁻¹ * ((m' * h) * S.z * (m' * h)⁻¹) * (m' * h) = 1 := by rw [e1]; group
      simpa [mul_assoc] using this)
    have hx'z : (m' * h) * S.z * (m' * h)⁻¹ ≠ S.z := fun e1 =>
      conj_not_mem_of_M hM hxA hm' (by rw [e1]; exact hA.z_mem)
    obtain ⟨q, hq, hqx⟩ := S.exists_conj_eq_mul_z hx'Q hx'1 hx'z
    rw [S.Qa_eq_of_conj_eq (g := g) (h := (q * m') * h) (by rw [e, ← hqx]; group)]
    exact hA.le_Qa_mul hM hxQ hxA hn (S.M.mul_mem (S.QG_le_M hq) hm')

theorem inf_le_closure (hn : 4 ≤ S.width) :
    S.QG ⊓ S.Qa h ≤
      closure {d : G | d ∈ S.QG ⊓ S.Qa h ∧ ∃ g : G, g * S.z * g⁻¹ = d} := by
  intro b hb
  by_cases hb1 : b = 1
  · rw [hb1]
    exact one_mem _
  · exact subset_closure ⟨hb, hA.exists_conj_eq_of_mem_inf hM hxQ hxA hn hb hb1⟩

end MaxEA

end CFSG.LargeExtraspecial.DW
