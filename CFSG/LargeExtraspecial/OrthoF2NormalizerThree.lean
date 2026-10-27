module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
import CFSG.LargeExtraspecial.AS35QCoLin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open CFSG.RankThree.OrthogonalInvolutions Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem apply_apply_add_apply_add_self_eq_zero {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    {u : V} (hu : u ∈ commSpace ω) : ω (ω u) + ω u + u = 0 := by
  have h : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  have hfree : commSpace ω ⊓ fixSpace ω = ⊥ := by
    rw [inf_comm]
    exact AS35QCo.fixSpace_inf_commSpace (show Odd 3 by decide) h
  have hUinv : ∀ u ∈ commSpace ω, ω u ∈ commSpace ω :=
    fun u hu => AS35QCo.apply_mem_commSpace (rfl) hu
  exact AS35QCo.sq_add_add_eq_zero h hUinv hfree hu

theorem apply_apply_eq_add_apply {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    {u : V} (hu : u ∈ commSpace ω) : ω (ω u) = u + ω u := by
  have h := apply_apply_add_apply_add_self_eq_zero hω3 hu
  have h1 : ω (ω u) + (ω u + u) = 0 := by rw [← add_assoc]; exact h
  have h2 : ω (ω u) = -(ω u + u) := eq_neg_of_add_eq_zero_left h1
  rw [neg_add, AS35QCo.neg_eq_self', AS35QCo.neg_eq_self', add_comm] at h2
  exact h2

theorem finrank_span_apply_eq_two {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    {u : V} (hu : u ∈ commSpace ω) (hu0 : u ≠ 0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {u, ω u}) = 2 := by
  have h : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  have hfree : commSpace ω ⊓ fixSpace ω = ⊥ := by
    rw [inf_comm]
    exact AS35QCo.fixSpace_inf_commSpace (show Odd 3 by decide) h
  have huω : ω u ≠ u := by
    intro h
    have hmem : u ∈ commSpace ω ⊓ fixSpace ω := ⟨hu, mem_fixSpace.mpr h⟩
    rw [hfree, Submodule.mem_bot] at hmem
    exact hu0 hmem
  have hωu0 : ω u ≠ 0 := by
    intro h
    apply hu0
    have := congrArg (ω.symm : V → V) h
    simpa using this
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hli : LinearIndependent (ZMod 2) ![u, ω u] := by
    rw [linearIndependent_fin2]
    refine ⟨hωu0, ?_⟩
    intro a
    rcases h01 a with rfl | rfl
    · rw [zero_smul]
      exact fun h => hu0 h.symm
    · rw [one_smul]
      exact huω
  rw [← Matrix.range_cons_cons_empty u (ω u) ![], finrank_span_eq_card hli, Fintype.card_fin]

theorem quadraticForm_eq_zero_of_mem_span_pair {ω : V ≃ₗ[ZMod 2] V}
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3) {c : V}
    (hc : c ∈ commSpace ω) (hqc : q c = 0) {x : V}
    (hx : x ∈ Submodule.span (ZMod 2) {c, ω c}) : q x = 0 := by
  have hcω : c + ω c = ω (ω c) := (apply_apply_eq_add_apply hω3 hc).symm
  have hqωc : q (ω c) = 0 := by rw [hωq c, hqc]
  have hqcω : q (c + ω c) = 0 := by rw [hcω, hωq (ω c), hqωc]
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;>
    simp [hqc, hqωc, hqcω]

theorem span_pair_le_orthogonal {ω : V ≃ₗ[ZMod 2] V}
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3) {c : V}
    (hc : c ∈ commSpace ω) (hqc : q c = 0) :
    Submodule.span (ZMod 2) {c, ω c} ≤
      LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {c, ω c}) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [QuadraticMap.polarBilin_apply_apply]
  have hxq := quadraticForm_eq_zero_of_mem_span_pair hωq hω3 hc hqc hx
  have hyq := quadraticForm_eq_zero_of_mem_span_pair hωq hω3 hc hqc hy
  have hxyq := quadraticForm_eq_zero_of_mem_span_pair hωq hω3 hc hqc (Submodule.add_mem _ hx hy)
  rw [QuadraticMap.polar, add_comm y x, hxyq, hyq, hxq]
  simp

theorem isCompl_commSpace_fixSpace {ω : V ≃ₗ[ZMod 2] V} (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3) :
    IsCompl (commSpace ω) (fixSpace ω) := by
  have h : ω ^ 3 = 1 := by rw [← hω3]; exact pow_orderOf_eq_one ω
  have hbot : commSpace ω ⊓ fixSpace ω = ⊥ := by
    rw [inf_comm]
    exact AS35QCo.fixSpace_inf_commSpace (show Odd 3 by decide) h
  have hC : fixSpace ω = LinearMap.BilinForm.orthogonal q.polarBilin (commSpace ω) :=
    AS35QCo.fixSpace_eq_orthogonal hq hωq
  have hrefl : (q.polarBilin).IsRefl := AS35QCo.polarBilin_isRefl q
  have hdisj : Disjoint (commSpace ω)
      (LinearMap.BilinForm.orthogonal q.polarBilin (commSpace ω)) := by
    rw [disjoint_iff_inf_le, ← hC]
    exact le_of_eq hbot
  have hnd : (LinearMap.BilinForm.restrict q.polarBilin (commSpace ω)).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hrefl hdisj
  have h := LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (B := q.polarBilin) (W := commSpace ω) hrefl hnd
  rwa [← hC] at h

theorem finrank_orthogonal_span_pair_inf {ω : V ≃ₗ[ZMod 2] V} (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) :
    finrank (ZMod 2) ↥(LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {c, ω c}) ⊓ commSpace ω) = 2 := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  let perp : Submodule (ZMod 2) V := LinearMap.BilinForm.orthogonal q.polarBilin ℓ
  change finrank (ZMod 2) ↥(perp ⊓ commSpace ω) = 2
  have hℓleU : ℓ ≤ commSpace ω := by
    rw [show ℓ = Submodule.span (ZMod 2) {c, ω c} from rfl, Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hc
    · exact AS35QCo.apply_mem_commSpace rfl hc
  have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
  have hcompl : IsCompl (commSpace ω) (fixSpace ω) :=
    isCompl_commSpace_fixSpace hq hωq hω3
  have hC : fixSpace ω = LinearMap.BilinForm.orthogonal q.polarBilin (commSpace ω) :=
    AS35QCo.fixSpace_eq_orthogonal hq hωq
  have hCle : fixSpace ω ≤ perp := by
    rw [hC]
    exact LinearMap.BilinForm.orthogonal_le hℓleU
  have hsup : perp = (perp ⊓ commSpace ω) ⊔ fixSpace ω := by
    calc perp = perp ⊓ (commSpace ω ⊔ fixSpace ω) := by
          rw [hcompl.sup_eq_top, inf_top_eq]
      _ = (perp ⊓ commSpace ω) ⊔ fixSpace ω :=
            (inf_sup_assoc_of_le (y := commSpace ω) hCle).symm
  have hdisj : (perp ⊓ commSpace ω) ⊓ fixSpace ω = ⊥ := by
    have hle : (perp ⊓ commSpace ω) ⊓ fixSpace ω ≤ commSpace ω ⊓ fixSpace ω :=
      fun x hx => ⟨hx.1.2, hx.2⟩
    exact le_bot_iff.mp (hle.trans (le_of_eq hcompl.inf_eq_bot))
  have hdim : finrank (ZMod 2) perp =
      finrank (ZMod 2) ↥(perp ⊓ commSpace ω) + finrank (ZMod 2) (fixSpace ω) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (perp ⊓ commSpace ω) (fixSpace ω)
    rw [← hsup, hdisj, finrank_bot, add_zero] at h
    exact h
  have hVdim : finrank (ZMod 2) V = 4 + finrank (ZMod 2) (fixSpace ω) := by
    have h := finrank_commSpace_add_finrank_fixSpace (K := ZMod 2) ω
    rw [h4] at h
    omega
  have hperp : finrank (ZMod 2) perp = finrank (ZMod 2) (fixSpace ω) + 2 := by
    have h : finrank (ZMod 2) perp = finrank (ZMod 2) V - finrank (ZMod 2) ℓ :=
      LinearMap.BilinForm.finrank_orthogonal hq ℓ
    rw [h, hℓdim]
    omega
  rw [hperp] at hdim
  omega

theorem orthogonal_span_pair_inf_eq {ω : V ≃ₗ[ZMod 2] V} (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hqc : q c = 0) :
    LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {c, ω c}) ⊓
        commSpace ω = Submodule.span (ZMod 2) {c, ω c} := by
  have hdim : finrank (ZMod 2) ↥(LinearMap.BilinForm.orthogonal q.polarBilin
      (Submodule.span (ZMod 2) {c, ω c}) ⊓ commSpace ω) = 2 :=
    finrank_orthogonal_span_pair_inf hq hωq hω3 h4 hc hc0
  have hdimℓ : finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {c, ω c}) = 2 :=
    finrank_span_apply_eq_two hω3 hc hc0
  have hle : Submodule.span (ZMod 2) {c, ω c} ≤
      LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {c, ω c}) ⊓
        commSpace ω := by
    refine le_inf (span_pair_le_orthogonal hωq hω3 hc hqc) ?_
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hc
    · exact AS35QCo.apply_mem_commSpace rfl hc
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hdimℓ])).symm

theorem map_omega_le_span_pair {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    {x : V} (hx : x ∈ commSpace ω) :
    Submodule.map (ω : V →ₗ[ZMod 2] V) (Submodule.span (ZMod 2) {x, ω x}) ≤
      Submodule.span (ZMod 2) {x, ω x} := by
  rw [Submodule.map_span, Submodule.span_le]
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · exact Submodule.subset_span (by simp)
  · change (ω : V → V) (ω x) ∈ Submodule.span (ZMod 2) {x, ω x}
    have h : (ω : V → V) (ω x) = x + ω x := by
      simpa using apply_apply_eq_add_apply hω3 hx
    rw [h]
    exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))

theorem span_pair_inf_span_pair_eq_bot {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    {c u₀ : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c}) :
    Submodule.span (ZMod 2) {c, ω c} ⊓ Submodule.span (ZMod 2) {u₀, ω u₀} = ⊥ := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  let W := Submodule.span (ZMod 2) {u₀, ω u₀}
  have hℓU : ℓ ≤ commSpace ω := by
    rw [show ℓ = Submodule.span (ZMod 2) {c, ω c} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hc
    · exact AS35QCo.apply_mem_commSpace rfl hc
  have hWU : W ≤ commSpace ω := by
    rw [show W = Submodule.span (ZMod 2) {u₀, ω u₀} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hu₀
    · exact AS35QCo.apply_mem_commSpace rfl hu₀
  have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    exact hu₀not (by rw [h]; exact ℓ.zero_mem)
  have hWdim : finrank (ZMod 2) W = 2 := finrank_span_apply_eq_two hω3 hu₀ hu₀0
  have hℓinv : ∀ y ∈ ℓ, ω y ∈ ℓ := by
    intro y hy
    exact map_omega_le_span_pair hω3 hc (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
  have hWinv : ∀ y ∈ W, ω y ∈ W := by
    intro y hy
    exact map_omega_le_span_pair hω3 hu₀ (Submodule.mem_map.mpr ⟨y, hy, rfl⟩)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  have hxU : x ∈ commSpace ω := hℓU hx.1
  have hspan2 : finrank (ZMod 2) (Submodule.span (ZMod 2) {x, ω x}) = 2 :=
    finrank_span_apply_eq_two hω3 hxU hx0
  have hspanℓ : Submodule.span (ZMod 2) {x, ω x} ≤ ℓ := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hx.1
    · exact hℓinv x hx.1
  have hspanW : Submodule.span (ZMod 2) {x, ω x} ≤ W := by
    rw [Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hx.2
    · exact hWinv x hx.2
  have heqℓ : Submodule.span (ZMod 2) {x, ω x} = ℓ :=
    Submodule.eq_of_le_of_finrank_eq hspanℓ (by rw [hspan2, hℓdim])
  have heqW : Submodule.span (ZMod 2) {x, ω x} = W :=
    Submodule.eq_of_le_of_finrank_eq hspanW (by rw [hspan2, hWdim])
  have hmem : u₀ ∈ ℓ := by
    rw [← heqℓ, heqW]
    exact Submodule.subset_span (by simp)
  exact hu₀not hmem

theorem commSpace_eq_sup_span_pair {ω : V ≃ₗ[ZMod 2] V} (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0)
    {u₀ : V} (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c}) :
    commSpace ω = Submodule.span (ZMod 2) {c, ω c} ⊔
      Submodule.span (ZMod 2) {u₀, ω u₀} := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  let W := Submodule.span (ZMod 2) {u₀, ω u₀}
  have hℓU : ℓ ≤ commSpace ω := by
    rw [show ℓ = Submodule.span (ZMod 2) {c, ω c} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hc
    · exact AS35QCo.apply_mem_commSpace rfl hc
  have hWU : W ≤ commSpace ω := by
    rw [show W = Submodule.span (ZMod 2) {u₀, ω u₀} from rfl, Submodule.span_le]
    intro y hy
    rcases hy with rfl | rfl
    · exact hu₀
    · exact AS35QCo.apply_mem_commSpace rfl hu₀
  have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
  have hu₀0 : u₀ ≠ 0 := by
    intro h
    exact hu₀not (by rw [h]; exact ℓ.zero_mem)
  have hWdim : finrank (ZMod 2) W = 2 := finrank_span_apply_eq_two hω3 hu₀ hu₀0
  have hℓWbot : ℓ ⊓ W = ⊥ := span_pair_inf_span_pair_eq_bot hω3 hc hc0 hu₀ hu₀not
  have hdimsup : finrank (ZMod 2) ↥(ℓ ⊔ W) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq ℓ W
    rw [hℓWbot, finrank_bot, add_zero, hℓdim, hWdim] at h
    exact h
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hℓU hWU) (by rw [hdimsup, h4])).symm

theorem sub_apply_mem_span_pair_of_commute {ω : V ≃ₗ[ZMod 2] V}
    (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hqc : q c = 0)
    {u₀ : V} (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c})
    {p : V ≃ₗ[ZMod 2] V} (hpω : p * ω = ω * p) (hpq : ∀ v, q (p v) = q v)
    (hpc : p c = c) :
    p u₀ - u₀ ∈ Submodule.span (ZMod 2) {c, ω c} ∧
      p u₀ - u₀ ∈ LinearMap.ker (q.polarBilin u₀) := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  have hpO : p ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hpq
  have hmU : p u₀ - u₀ ∈ commSpace ω :=
    (commSpace ω).sub_mem (AS35QCo.apply_mem_commSpace hpω hu₀) hu₀
  have hpωc : p (ω c) = ω c := by
    rw [← LinearEquiv.mul_apply, hpω, LinearEquiv.mul_apply, hpc]
  have hmorth : p u₀ - u₀ ∈ LinearMap.BilinForm.orthogonal q.polarBilin ℓ := by
    have hc0' : (q.polarBilin) c (p u₀ - u₀) = 0 := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hpO c u₀
      rw [hpc] at h
      change QuadraticMap.polar q c (p u₀ - u₀) = 0
      rw [QuadraticMap.polar_sub_right, h, sub_self]
    have hωc0 : (q.polarBilin) (ω c) (p u₀ - u₀) = 0 := by
      have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hpO (ω c) u₀
      rw [hpωc] at h
      change QuadraticMap.polar q (ω c) (p u₀ - u₀) = 0
      rw [QuadraticMap.polar_sub_right, h, sub_self]
    have hker : ℓ ≤ LinearMap.ker ((q.polarBilin).flip (p u₀ - u₀)) := by
      rw [show ℓ = Submodule.span (ZMod 2) {c, ω c} from rfl, Submodule.span_le]
      intro y hy
      change ((q.polarBilin).flip (p u₀ - u₀)) y = 0
      rcases hy with rfl | rfl
      · simpa [LinearMap.BilinForm.flip_apply] using hc0'
      · simpa [LinearMap.BilinForm.flip_apply] using hωc0
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    simpa [LinearMap.BilinForm.flip_apply] using hker hy
  have hℓeq := orthogonal_span_pair_inf_eq hq hωq hω3 h4 hc hc0 hqc
  have hmℓ : p u₀ - u₀ ∈ ℓ := by
    change p u₀ - u₀ ∈ Submodule.span (ZMod 2) {c, ω c}
    rw [← hℓeq]
    exact ⟨hmorth, hmU⟩
  refine ⟨hmℓ, ?_⟩
  change (q.polarBilin u₀) (p u₀ - u₀) = 0
  have hmq : q (p u₀ - u₀) = 0 :=
    quadraticForm_eq_zero_of_mem_span_pair hωq hω3 hc hqc hmℓ
  have hsum : u₀ + (p u₀ - u₀) = p u₀ := by abel
  have hqadd : q (u₀ + (p u₀ - u₀)) =
      q u₀ + q (p u₀ - u₀) + QuadraticMap.polar q u₀ (p u₀ - u₀) :=
    map_add_eq q u₀ (p u₀ - u₀)
  have hpolar : QuadraticMap.polar q u₀ (p u₀ - u₀) = 0 := by
    rw [hsum, hpq u₀, hmq, add_zero] at hqadd
    have h : q u₀ + QuadraticMap.polar q u₀ (p u₀ - u₀) = q u₀ + 0 := by
      rw [add_zero]
      exact hqadd.symm
    exact add_left_cancel h
  simpa [QuadraticMap.polarBilin_apply_apply] using hpolar

theorem eq_of_apply_eq_of_mem_centralizer {ω : V ≃ₗ[ZMod 2] V}
    (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0)
    {u₀ : V} (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c})
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (htriv : ∀ p ∈ P, ∀ v ∈ fixSpace ω, p v = v)
    (hfix : ∀ p ∈ P, p c = c)
    {p r : V ≃ₗ[ZMod 2] V} (hpP : p ∈ P) (hrP : r ∈ P)
    (hpω : p * ω = ω * p) (hrω : r * ω = ω * r) (hpr : p u₀ = r u₀) : p = r := by
  have hUeq := commSpace_eq_sup_span_pair hω3 h4 hc hc0 hu₀ hu₀not
  have hcompl : IsCompl (commSpace ω) (fixSpace ω) :=
    isCompl_commSpace_fixSpace hq hωq hω3
  let d : V →ₗ[ZMod 2] V := (p : V →ₗ[ZMod 2] V) - (r : V →ₗ[ZMod 2] V)
  have hpωc : p (ω c) = ω c := by
    rw [← LinearEquiv.mul_apply, hpω, LinearEquiv.mul_apply, hfix p hpP]
  have hrωc : r (ω c) = ω c := by
    rw [← LinearEquiv.mul_apply, hrω, LinearEquiv.mul_apply, hfix r hrP]
  have hpωu : p (ω u₀) = ω (p u₀) := by
    rw [← LinearEquiv.mul_apply, hpω, LinearEquiv.mul_apply]
  have hrωu : r (ω u₀) = ω (r u₀) := by
    rw [← LinearEquiv.mul_apply, hrω, LinearEquiv.mul_apply]
  have hkerC : fixSpace ω ≤ LinearMap.ker d := by
    intro v hv
    change p v - r v = 0
    rw [htriv p hpP v hv, htriv r hrP v hv, sub_self]
  have hkerℓ : Submodule.span (ZMod 2) {c, ω c} ≤ LinearMap.ker d := by
    rw [Submodule.span_le]
    intro x hx
    change p x - r x = 0
    rcases hx with rfl | rfl
    · rw [hfix p hpP, hfix r hrP, sub_self]
    · rw [hpωc, hrωc, sub_self]
  have hkerW : Submodule.span (ZMod 2) {u₀, ω u₀} ≤ LinearMap.ker d := by
    rw [Submodule.span_le]
    intro x hx
    change p x - r x = 0
    rcases hx with rfl | rfl
    · rw [hpr, sub_self]
    · rw [hpωu, hrωu, hpr, sub_self]
  have hkerU : commSpace ω ≤ LinearMap.ker d := by
    rw [hUeq]
    exact sup_le hkerℓ hkerW
  have hkerTop : (⊤ : Submodule (ZMod 2) V) ≤ LinearMap.ker d := by
    rw [← hcompl.sup_eq_top]
    exact sup_le hkerU hkerC
  have hd : (p : V →ₗ[ZMod 2] V) - (r : V →ₗ[ZMod 2] V) = 0 := by
    have h : LinearMap.ker d = ⊤ := le_antisymm le_top hkerTop
    exact LinearMap.ker_eq_top.mp h
  have hpmap : (p : V →ₗ[ZMod 2] V) = (r : V →ₗ[ZMod 2] V) := sub_eq_zero.mp hd
  exact LinearEquiv.ext fun v => congrArg (fun f : V →ₗ[ZMod 2] V => f v) hpmap

theorem finrank_span_pair_inf_ker_le_one {ω : V ≃ₗ[ZMod 2] V}
    (hq : q.polarBilin.Nondegenerate) (hωq : ∀ v, q (ω v) = q v)
    (hω3 : orderOf ω = 3) (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hqc : q c = 0)
    {u₀ : V} (hu₀ : u₀ ∈ commSpace ω)
    (hu₀not : u₀ ∉ Submodule.span (ZMod 2) {c, ω c}) :
    finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {c, ω c} ⊓
      LinearMap.ker (q.polarBilin u₀)) ≤ 1 := by
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  let L : Submodule (ZMod 2) V := ℓ ⊓ LinearMap.ker (q.polarBilin u₀)
  have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
  have hℓeq : LinearMap.BilinForm.orthogonal q.polarBilin ℓ ⊓ commSpace ω = ℓ :=
    orthogonal_span_pair_inf_eq hq hωq hω3 h4 hc hc0 hqc
  have hu₀notperp : u₀ ∉ LinearMap.BilinForm.orthogonal q.polarBilin ℓ := by
    intro hmem
    exact hu₀not (by
      change u₀ ∈ ℓ
      rw [← hℓeq]
      exact ⟨hmem, hu₀⟩)
  have hLne : L ≠ ℓ := by
    intro h
    have hker : ℓ ≤ LinearMap.ker (q.polarBilin u₀) := by
      rw [← h]
      exact inf_le_right
    apply hu₀notperp
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hsymm : (q.polarBilin) u₀ y = (q.polarBilin) y u₀ :=
      LinearMap.BilinForm.IsSymm.eq (QuadraticMap.isSymm_polarBilin q) u₀ y
    rw [← hsymm]
    exact hker hy
  have hlt : finrank (ZMod 2) L < finrank (ZMod 2) ℓ := by
    refine lt_of_le_of_ne (Submodule.finrank_mono (inf_le_left : L ≤ ℓ)) ?_
    intro hEq
    exact hLne (Submodule.eq_of_le_of_finrank_eq inf_le_left hEq)
  change finrank (ZMod 2) ↥L ≤ 1
  omega

theorem card_centralizer_le_two {ω : V ≃ₗ[ZMod 2] V} (hq : q.polarBilin.Nondegenerate)
    (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPq : ∀ p ∈ P, ∀ v, q (p v) = q v)
    (htriv : ∀ p ∈ P, ∀ v ∈ fixSpace ω, p v = v)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hqc : q c = 0)
    (hfix : ∀ p ∈ P, p c = c) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))) ≤ 2 := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let P₀ := P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))
  let ℓ := Submodule.span (ZMod 2) {c, ω c}
  have hnotle : ¬ commSpace ω ≤ ℓ := by
    intro h
    have := Submodule.finrank_mono h
    have hℓdim : finrank (ZMod 2) ℓ = 2 := finrank_span_apply_eq_two hω3 hc hc0
    omega
  obtain ⟨u₀, hu₀, hu₀not⟩ := SetLike.not_le_iff_exists.mp hnotle
  let L : Submodule (ZMod 2) V := ℓ ⊓ LinearMap.ker (q.polarBilin u₀)
  have hLdim : finrank (ZMod 2) L ≤ 1 :=
    finrank_span_pair_inf_ker_le_one hq hωq hω3 h4 hc hc0 hqc hu₀ hu₀not
  have hmL : ∀ p : P₀, p.1 u₀ - u₀ ∈ L := by
    intro p
    obtain ⟨hpP, hpc⟩ := Subgroup.mem_inf.mp p.2
    have hpω : p.1 * ω = ω * p.1 :=
      Subgroup.mem_centralizer_singleton_iff.mp hpc
    exact sub_apply_mem_span_pair_of_commute hq hωq hω3 h4 hc hc0 hqc hu₀ hu₀not
      hpω (hPq p.1 hpP) (hfix p.1 hpP)
  let f : P₀ → L := fun p => ⟨p.1 u₀ - u₀, hmL p⟩
  have hf : Function.Injective f := by
    intro p r hpr
    apply Subtype.ext
    have hval : p.1 u₀ = r.1 u₀ := by
      exact sub_left_inj.mp (congrArg Subtype.val hpr)
    obtain ⟨hpP, hpc⟩ := Subgroup.mem_inf.mp p.2
    obtain ⟨hrP, hrc⟩ := Subgroup.mem_inf.mp r.2
    exact eq_of_apply_eq_of_mem_centralizer hq hωq hω3 h4 hc hc0 hu₀ hu₀not htriv hfix
      hpP hrP (Subgroup.mem_centralizer_singleton_iff.mp hpc)
      (Subgroup.mem_centralizer_singleton_iff.mp hrc) hval
  have hcard : Nat.card P₀ ≤ Nat.card L := Nat.card_le_card_of_injective f hf
  have hLcard : Nat.card L ≤ 2 := by
    rw [AS35QCo.natCard_submodule]
    calc 2 ^ finrank (ZMod 2) L ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hLdim
      _ = 2 := by norm_num
  exact le_trans hcard hLcard

theorem exists_injective_to_bool_prod_centralizer {ω : V ≃ₗ[ZMod 2] V}
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hnorm : ∀ p ∈ P, p * ω * p⁻¹ = ω ∨ p * ω * p⁻¹ = ω⁻¹)
    {p₁ : V ≃ₗ[ZMod 2] V} (hp₁P : p₁ ∈ P) (hp₁inv : p₁ * ω * p₁⁻¹ = ω⁻¹) :
    ∃ f : P → Bool × ↥(P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))),
      Function.Injective f := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let P₀ := P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))
  have hconv : ∀ p ∈ P, ¬ p * ω * p⁻¹ = ω → p * ω * p⁻¹ = ω⁻¹ := by
    intro p hpP hp
    rcases hnorm p hpP with h | h
    · exact absurd h hp
    · exact h
  have hp₁inverse : p₁⁻¹ * ω⁻¹ * p₁ = ω := by
    have h := congrArg (fun x => p₁⁻¹ * x * p₁) hp₁inv
    simpa [mul_assoc] using h.symm
  have hprod : ∀ p ∈ P, p * ω * p⁻¹ = ω⁻¹ → p₁⁻¹ * p ∈ P₀ := by
    intro p hpP hp
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨P.mul_mem (P.inv_mem hp₁P) hpP, ?_⟩
    have hconj : (p₁⁻¹ * p) * ω * (p₁⁻¹ * p)⁻¹ = ω := by
      calc (p₁⁻¹ * p) * ω * (p₁⁻¹ * p)⁻¹
          = p₁⁻¹ * (p * ω * p⁻¹) * p₁ := by group
        _ = p₁⁻¹ * ω⁻¹ * p₁ := by rw [hp]
        _ = ω := hp₁inverse
    have hcomm : (p₁⁻¹ * p) * ω = ω * (p₁⁻¹ * p) := by
      calc (p₁⁻¹ * p) * ω
          = (p₁⁻¹ * p) * ω * (p₁⁻¹ * p)⁻¹ * (p₁⁻¹ * p) := by group
        _ = ω * (p₁⁻¹ * p) := by rw [hconj]
    exact hcomm
  let f : P → Bool × P₀ := fun p =>
    if hp : (p : V ≃ₗ[ZMod 2] V) * ω * (p : V ≃ₗ[ZMod 2] V)⁻¹ = ω then
      (true, ⟨p.1, Subgroup.mem_inf.mpr
        ⟨p.2, Subgroup.mem_centralizer_singleton_iff.mpr (by
          have h := congrArg (fun x => x * (p : V ≃ₗ[ZMod 2] V)) hp
          simpa [mul_assoc] using h)⟩⟩)
    else
      (false, ⟨p₁⁻¹ * p.1, hprod p.1 p.2 (hconv p.1 p.2 hp)⟩)
  have hf : Function.Injective f := by
    intro p r hpr
    have hbool : (f p).1 = (f r).1 := congrArg (fun z : Bool × P₀ => z.1) hpr
    have hval : ((f p).2 : V ≃ₗ[ZMod 2] V) = ((f r).2 : V ≃ₗ[ZMod 2] V) :=
      congrArg (fun z : Bool × P₀ => (z.2 : V ≃ₗ[ZMod 2] V)) hpr
    dsimp only [f] at hbool hval
    by_cases hp : (p : V ≃ₗ[ZMod 2] V) * ω * (p : V ≃ₗ[ZMod 2] V)⁻¹ = ω
    · have hr : (r : V ≃ₗ[ZMod 2] V) * ω * (r : V ≃ₗ[ZMod 2] V)⁻¹ = ω := by
        by_contra hr
        rw [dif_pos hp, dif_neg hr] at hbool
        simp at hbool
      rw [dif_pos hp, dif_pos hr] at hval
      exact Subtype.ext (by simpa using hval)
    · have hr : ¬(r : V ≃ₗ[ZMod 2] V) * ω * (r : V ≃ₗ[ZMod 2] V)⁻¹ = ω := by
        intro hr
        rw [dif_neg hp, dif_pos hr] at hbool
        simp at hbool
      rw [dif_neg hp, dif_neg hr] at hval
      have hval' : p₁⁻¹ * (p : V ≃ₗ[ZMod 2] V) =
          p₁⁻¹ * (r : V ≃ₗ[ZMod 2] V) := by simpa using hval
      exact Subtype.ext (mul_left_cancel hval')
  exact ⟨f, hf⟩

theorem card_le_two_mul_card_centralizer {ω : V ≃ₗ[ZMod 2] V}
    {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hnorm : ∀ p ∈ P, p * ω * p⁻¹ = ω ∨ p * ω * p⁻¹ = ω⁻¹) :
    Nat.card P ≤ 2 * Nat.card ↥(P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))) := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  let P₀ := P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))
  by_cases hex : ∃ p₁ ∈ P, p₁ * ω * p₁⁻¹ = ω⁻¹
  · obtain ⟨p₁, hp₁P, hp₁inv⟩ := hex
    obtain ⟨f, hf⟩ := exists_injective_to_bool_prod_centralizer hnorm hp₁P hp₁inv
    have hcard : Nat.card P ≤ 2 * Nat.card P₀ := by
      have h := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod] at h
      have hb : Nat.card Bool = 2 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_bool]
      rw [hb] at h
      exact h
    exact hcard
  · have hcomm : ∀ p ∈ P, p * ω * p⁻¹ = ω := by
      intro p hpP
      rcases hnorm p hpP with h | h
      · exact h
      · exact absurd ⟨p, hpP, h⟩ hex
    have hle : P ≤ P₀ := by
      intro p hpP
      refine Subgroup.mem_inf.mpr ⟨hpP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := congrArg (fun x => x * (p : V ≃ₗ[ZMod 2] V)) (hcomm p hpP)
      simpa [mul_assoc] using h
    have hcard : Nat.card P ≤ Nat.card P₀ := by
      refine Nat.card_le_card_of_injective (fun p : P => (⟨p.1, hle p.2⟩ : P₀)) ?_
      intro p r hpr
      exact Subtype.ext (congrArg (fun z : P₀ => (z : V ≃ₗ[ZMod 2] V)) hpr)
    have : Nat.card P₀ ≤ 2 * Nat.card P₀ := by omega
    exact le_trans hcard this

theorem card_le_four_of_normalizes_of_apply_eq (hq : q.polarBilin.Nondegenerate)
    {ω : V ≃ₗ[ZMod 2] V} (hωq : ∀ v, q (ω v) = q v) (hω3 : orderOf ω = 3)
    (h4 : finrank (ZMod 2) (commSpace ω) = 4)
    {P : Subgroup (V ≃ₗ[ZMod 2] V)} (hPq : ∀ p ∈ P, ∀ v, q (p v) = q v)
    (hnorm : ∀ p ∈ P, p * ω * p⁻¹ = ω ∨ p * ω * p⁻¹ = ω⁻¹)
    (htriv : ∀ p ∈ P, ∀ v ∈ fixSpace ω, p v = v)
    {c : V} (hc : c ∈ commSpace ω) (hc0 : c ≠ 0) (hcq : q c = 0)
    (hfix : ∀ p ∈ P, p c = c) : Nat.card P ≤ 4 := by
  have hP₀ := card_centralizer_le_two hq hωq hω3 h4 hPq htriv hc hc0 hcq hfix
  have hP := card_le_two_mul_card_centralizer hnorm
  calc Nat.card P ≤ 2 * Nat.card ↥(P ⊓ Subgroup.centralizer ({ω} : Set (V ≃ₗ[ZMod 2] V))) := hP
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 hP₀
    _ = 4 := by norm_num

end CFSG.LargeExtraspecial
