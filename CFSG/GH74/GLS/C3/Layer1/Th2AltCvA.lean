module

public import CFSG.GH74.GLS.C3.Layer1.Th2AltStd
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltSE
public import CFSG.GH74.GLS.C3.Layer1.BkL114TI

public section

namespace CFSG.GH74.GLS.Th2.AltCv

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer1.Bk

variable {G : Type} [Group G] [Finite G] {M K : Subgroup G}

omit [Finite G] in
theorem exists_std_iso {n : ℕ} (hn : 5 ≤ n) (e₀ : Mb M ≃* alternatingGroup (Fin (n + 4))) {x : Mb M}
    (hKperf : Group.IsPerfect ↥(imgM M K))
    (hKcard : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card ↥(imgM M K))
    (hKx : ∀ w ∈ imgM M K, w * x = x * w)
    (hx4 : numMoved ((e₀ x : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) = 4) :
    ∃ e : Mb M ≃* alternatingGroup (Fin (n + 4)), (imgM M K).map e.toMonoidHom = stdAlt n ∧
      ∀ t : Mb M, numMoved ((e t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) =
        numMoved ((e₀ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) := by
  set K' : Subgroup (alternatingGroup (Fin (n + 4))) := (imgM M K).map e₀.toMonoidHom with hK'
  have hperf0 : Group.IsPerfect ↥(imgM M K) := hKperf
  have hperf : Group.IsPerfect ↥K' := Group.IsPerfect.map (H := imgM M K) e₀.toMonoidHom
  have hcard : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card ↥K' := by
    rw [hK', Subgroup.card_map_of_injective e₀.injective]
    exact hKcard
  have hx0 : x = e₀.symm (e₀ x) := (e₀.symm_apply_apply x).symm
  have hKu : ∀ k ∈ K', k * e₀ x = e₀ x * k := by
    rintro _ ⟨w, hw, rfl⟩
    show e₀ w * e₀ x = e₀ x * e₀ w
    rw [← map_mul, ← map_mul, hKx w hw]
  obtain ⟨σ, hσ⟩ := Th2.AltStd.exists_conj_stdAlt_of_perfect hn K' hcard hx4 hKu
  refine ⟨e₀.trans (conjA σ), ?_, ?_⟩
  · rw [← hσ, hK', Subgroup.map_map]
    rfl
  · intro t
    show numMoved (σ * ((e₀ t : alternatingGroup (Fin (n + 4))) : Perm (Fin (n + 4))) * σ⁻¹) = _
    exact numMoved_conj _ σ

theorem exists_conj_pair {n : ℕ} (hAM : AModel (n + 4)) (e : Mb M ≃* alternatingGroup (Fin (n + 4)))
    {x v : G} (hxM : x ∈ M) (hvM : v ∈ M) (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    {W : Subgroup G} (hW : IsSylowOf 2 W M) (hvW : v ∈ W) (hvc : ∀ w ∈ W, w * v = v * w)
    (hx4 : numMoved ((e (barMk ↥M ⟨x, hxM⟩) : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))) = 4)
    (hv8 : numMoved ((e (barMk ↥M ⟨v, hvM⟩) : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))) = 8) :
    ∃ (W' : Subgroup G) (v' : G), v' ∈ M ∧ IsSylowOf 2 W' M ∧ x ∈ W' ∧ v' ∈ W' ∧
      orderOf v' = 2 ∧ (∀ w ∈ W', w * v' = v' * w) ∧
      (∃ c ∈ M, c * v' = v' * c ∧ c * x * c⁻¹ = x * v') ∧ ∃ m ∈ M, m * v' * m⁻¹ = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMM : imgM M M = ⊤ := by
    unfold imgM
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ barMk_surjective
  have hWb := isSylowOf_imgM_of_le (le_refl M) hW
  set S : Subgroup (alternatingGroup (Fin (n + 4))) := (imgM M W).map e.toMonoidHom with hS
  have hSsyl : IsSylowOf 2 S ⊤ := by
    refine isSylowOf_of_card le_top ?_
    rw [hS, Subgroup.card_map_of_injective e.injective, hWb.card_eq, hMM, Subgroup.card_top,
      Subgroup.card_top, Nat.card_congr e.toEquiv]
  set x' : ↥M := ⟨x, hxM⟩ with hx'
  set v' : ↥M := ⟨v, hvM⟩ with hv'
  have hx'2 : orderOf x' = 2 := (Subgroup.orderOf_mk x hxM).trans hx2
  have hv'2 : orderOf v' = 2 := (Subgroup.orderOf_mk v hvM).trans hv2
  have hvS : e (barMk ↥M v') ∈ S := ⟨barMk ↥M v', mem_imgM_iff.2 ⟨v', hvW, rfl⟩, rfl⟩
  have hvcS : ∀ s ∈ S, s * e (barMk ↥M v') = e (barMk ↥M v') * s := by
    rintro _ ⟨wb, hwb, rfl⟩
    obtain ⟨w, hwW, rfl⟩ := mem_imgM_iff.1 hwb
    show e (barMk ↥M w) * e (barMk ↥M v') = e (barMk ↥M v') * e (barMk ↥M w)
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hvc _ hwW)
  have hvord : orderOf (e (barMk ↥M v')) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_barMk hv'2
  obtain ⟨E, hES, hvE, hEcard, hEcomm, hEsq, hEconj, hEchar, hEnm, hEtrans, hEZ, hEex⟩ :=
    hAM S (e (barMk ↥M v')) hSsyl hvS hvcS hvord hv8
  obtain ⟨y, hyE, hy1, hyv⟩ : ∃ y ∈ E, y ≠ 1 ∧ y ≠ e (barMk ↥M v') := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set (alternatingGroup (Fin (n + 4)))) ⊆ {1, e (barMk ↥M v')} := by
      intro y hy
      by_cases h1 : y = 1
      · simp [h1]
      · simp [hcon y hy h1]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({1, e (barMk ↥M v')} : Set (alternatingGroup (Fin (n + 4)))).ncard ≤ 2 := by
      refine (Set.ncard_insert_le _ _).trans ?_
      rw [Set.ncard_singleton]
    have h3 : Nat.card E ≤ 2 := by
      have := Nat.card_coe_set_eq (E : Set (alternatingGroup (Fin (n + 4))))
      rw [← this] at hle
      exact hle.trans h2
    omega
  obtain ⟨yb, hyb, rfl⟩ := hES hyE
  obtain ⟨w, hwW, hwyb⟩ := mem_imgM_iff.1 hyb
  have hy2 : e yb * e yb = 1 := hEsq _ hyE
  have hyb2 : yb * yb = 1 := by
    apply e.injective
    rw [map_mul, hy2, map_one]
  have hv'sq : v' * v' = 1 := by
    have := pow_orderOf_eq_one v'
    rwa [hv'2, sq] at this
  have hww : (w * w : ↥M) = 1 := by
    have hker : barMk ↥M (w * w) = 1 := by rw [map_mul, hwyb]; exact hyb2
    have h1 := (barMk_eq_one_iff_mem_pPrimeCoreOf (w * w)).1 hker
    have h2 : ((w * w : ↥M) : G) ∈ W := W.mul_mem hwW hwW
    have h3 : ((w * w : ↥M) : G) ∈ W ⊓ pPrimeCoreOf 2 M := ⟨h2, h1⟩
    rw [C3.Layer1.Back.Setup91.inf_pPrimeCoreOf_eq_bot M hW.isPGroup, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hw1 : w ≠ 1 := by
    intro h1
    apply hy1
    show e yb = 1
    rw [← hwyb, h1, map_one, map_one]
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
  have hynm := hEnm _ hyE hy1 hyv
  have hyord : orderOf (e yb) = 2 := orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hxy : IsConj (e (barMk ↥M x')) (e yb) :=
    isConj_alternating_of_numMoved_eq (n + 4) _ _
      (by rw [MulEquiv.orderOf_eq]; exact orderOf_barMk hx'2) hyord (hx4.trans hynm.1.symm)
  have hxy' : IsConj (barMk ↥M w) (barMk ↥M x') := by
    rw [hwyb]
    exact ((Th2.AltInv.isConj_equiv_iff' e).1 hxy).symm
  obtain ⟨m, hm⟩ := exists_conj_of_barMk_conj hw2 hx'2 hxy'
  have hwv_comm : w * v' = v' * w := Subtype.ext (hvc _ hwW)
  have hwv2 : orderOf (w * v') = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq]
      calc (w * v') * (w * v') = w * (v' * w) * v' := by group
        _ = w * (w * v') * v' := by rw [← hwv_comm]
        _ = (w * w) * (v' * v') := by group
        _ = 1 := by rw [hww, hv'sq, one_mul]
    · intro h1
      apply hyv
      have h2 : e yb * e (barMk ↥M v') = 1 := by
        rw [← map_mul, ← hwyb, ← map_mul, h1, map_one, map_one]
      have h3 : e (barMk ↥M v') * e (barMk ↥M v') = 1 := by
        rw [← map_mul, ← map_mul, hv'sq, map_one, map_one]
      exact (eq_inv_of_mul_eq_one_left h2).trans (inv_eq_of_mul_eq_one_right h3)
  have hvbsq : e (barMk ↥M v') * e (barMk ↥M v') = 1 := by
    rw [← map_mul, ← map_mul, hv'sq, map_one, map_one]
  have hyvE : e yb * e (barMk ↥M v') ∈ E := E.mul_mem hyE hvE
  have hyv1 : e yb * e (barMk ↥M v') ≠ 1 := by
    intro h1
    exact hyv ((eq_inv_of_mul_eq_one_left h1).trans (inv_eq_of_mul_eq_one_right hvbsq))
  have hyvv : e yb * e (barMk ↥M v') ≠ e (barMk ↥M v') := by
    intro h1
    exact hy1 (mul_right_cancel (h1.trans (one_mul _).symm))
  obtain ⟨cA, hcA1, hcA2⟩ := hEtrans _ hyE _ hyvE hy1 hyv hyv1 hyvv
  have hcb1 : e.symm cA * barMk ↥M v' = barMk ↥M v' * e.symm cA := by
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcA1
  obtain ⟨c₁, hc₁v, hc₁π⟩ := exists_lift_centralizer hv'2 hcb1
  have hu2 : orderOf (c₁ * w * c₁⁻¹) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj c₁) w
    simpa [MulAut.conj_apply] using this.trans hw2
  have hu_comm : (c₁ * w * c₁⁻¹) * v' = v' * (c₁ * w * c₁⁻¹) := by
    calc (c₁ * w * c₁⁻¹) * v' = c₁ * w * (c₁⁻¹ * v') := by group
      _ = c₁ * w * (v' * c₁⁻¹) := by
          congr 1
          rw [inv_mul_eq_iff_eq_mul]
          calc v' = (v' * c₁) * c₁⁻¹ := by group
            _ = (c₁ * v') * c₁⁻¹ := by rw [hc₁v]
            _ = c₁ * (v' * c₁⁻¹) := by group
      _ = c₁ * (w * v') * c₁⁻¹ := by group
      _ = c₁ * (v' * w) * c₁⁻¹ := by rw [hwv_comm]
      _ = (c₁ * v') * w * c₁⁻¹ := by group
      _ = (v' * c₁) * w * c₁⁻¹ := by rw [hc₁v]
      _ = v' * (c₁ * w * c₁⁻¹) := by group
  have hπ : barMk ↥M (w * v') = barMk ↥M (c₁ * w * c₁⁻¹) := by
    have h1 : barMk ↥M (c₁ * w * c₁⁻¹) = e.symm cA * yb * (e.symm cA)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      have : barMk ↥M c₁ = e.symm cA := hc₁π
      rw [this, hwyb]
    have h2 : e.symm cA * yb * (e.symm cA)⁻¹ = yb * barMk ↥M v' := by
      apply e.injective
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hcA2
    rw [h1, h2, map_mul, hwyb]
  have hsv : (w * v') * v' = v' * (w * v') := by
    calc (w * v') * v' = w * (v' * v') := by group
      _ = w := by rw [hv'sq, mul_one]
      _ = (v' * v') * w := by rw [hv'sq, one_mul]
      _ = v' * (v' * w) := by group
      _ = v' * (w * v') := by rw [hwv_comm]
  obtain ⟨g, hgv, hgu⟩ := exists_centralizer_conj_of_mk_eq (v := v') hwv2 hu2 hsv hu_comm hπ
  have hc'v : (g * c₁) * v' = v' * (g * c₁) := by
    calc (g * c₁) * v' = g * (c₁ * v') := by group
      _ = g * (v' * c₁) := by rw [hc₁v]
      _ = (g * v') * c₁ := by group
      _ = (v' * g) * c₁ := by rw [hgv]
      _ = v' * (g * c₁) := by group
  have hc'w : (g * c₁) * w * (g * c₁)⁻¹ = w * v' := by
    calc (g * c₁) * w * (g * c₁)⁻¹ = g * (c₁ * w * c₁⁻¹) * g⁻¹ := by group
      _ = w * v' := hgu
  have hmG : (m : G) * x * (m : G)⁻¹ = (w : G) := congrArg Subtype.val hm
  have hx'm : x' = m⁻¹ * w * m := by
    calc x' = m⁻¹ * (m * x' * m⁻¹) * m := by group
      _ = m⁻¹ * w * m := by rw [hm]
  have hv'M : (m : G)⁻¹ * v * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem m.2) hvM) m.2
  have hconjW : ∀ a ∈ W, (m : G)⁻¹ * a * m ∈ W.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom := by
    intro a ha
    refine ⟨a, ha, ?_⟩
    simp
  have hW'M : W.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom ≤ M := by
    rintro _ ⟨a, ha, rfl⟩
    show (m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹ ∈ M
    exact M.mul_mem (M.mul_mem (M.inv_mem m.2) (hW.le ha)) (M.inv_mem (M.inv_mem m.2))
  refine ⟨W.map (MulAut.conj ((m : G)⁻¹)).toMonoidHom, (m : G)⁻¹ * v * m, hv'M, ?_, ?_, ?_, ?_, ?_,
    ?_, ⟨m, m.2, by group⟩⟩
  · refine isSylowOf_of_card hW'M ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj ((m : G)⁻¹)).injective, hW.card_eq]
  · have : x = (m : G)⁻¹ * (w : G) * m := by
      calc x = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * m := by group
        _ = (m : G)⁻¹ * (w : G) * m := by rw [hmG]
    rw [this]
    exact hconjW _ hwW
  · exact hconjW v hvW
  · have := MulEquiv.orderOf_eq (MulAut.conj ((m : G)⁻¹)) v
    simpa [MulAut.conj_apply] using this.trans hv2
  · rintro _ ⟨a, ha, rfl⟩
    show ((m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹) * ((m : G)⁻¹ * v * m) =
      ((m : G)⁻¹ * v * m) * ((m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹)
    have h1 := hvc a ha
    calc ((m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹) * ((m : G)⁻¹ * v * m) = (m : G)⁻¹ * (a * v) * m := by group
      _ = (m : G)⁻¹ * (v * a) * m := by rw [h1]
      _ = ((m : G)⁻¹ * v * m) * ((m : G)⁻¹ * a * ((m : G)⁻¹)⁻¹) := by group
  · refine ⟨((m⁻¹ * (g * c₁) * m : ↥M) : G), (m⁻¹ * (g * c₁) * m).2, ?_, ?_⟩
    · have h1 : ((g * c₁ : ↥M) : G) * v = v * ((g * c₁ : ↥M) : G) := congrArg Subtype.val hc'v
      show (m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m * ((m : G)⁻¹ * v * m) =
        ((m : G)⁻¹ * v * m) * ((m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m)
      calc (m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m * ((m : G)⁻¹ * v * m)
          = (m : G)⁻¹ * (((g * c₁ : ↥M) : G) * v) * m := by group
        _ = (m : G)⁻¹ * (v * ((g * c₁ : ↥M) : G)) * m := by rw [h1]
        _ = ((m : G)⁻¹ * v * m) * ((m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m) := by group
    · have h2 : ((g * c₁ : ↥M) : G) * (w : G) * ((g * c₁ : ↥M) : G)⁻¹ = (w : G) * v :=
        congrArg Subtype.val hc'w
      have hxG : x = (m : G)⁻¹ * (w : G) * m := by
        calc x = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * m := by group
          _ = (m : G)⁻¹ * (w : G) * m := by rw [hmG]
      show (m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m * x * ((m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m)⁻¹ =
        x * ((m : G)⁻¹ * v * m)
      rw [hxG]
      calc (m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m * ((m : G)⁻¹ * (w : G) * m) *
            ((m : G)⁻¹ * ((g * c₁ : ↥M) : G) * m)⁻¹
          = (m : G)⁻¹ * (((g * c₁ : ↥M) : G) * (w : G) * ((g * c₁ : ↥M) : G)⁻¹) * m := by group
        _ = (m : G)⁻¹ * ((w : G) * v) * m := by rw [h2]
        _ = ((m : G)⁻¹ * (w : G) * m) * ((m : G)⁻¹ * v * m) := by group

end CFSG.GH74.GLS.Th2.AltCv
