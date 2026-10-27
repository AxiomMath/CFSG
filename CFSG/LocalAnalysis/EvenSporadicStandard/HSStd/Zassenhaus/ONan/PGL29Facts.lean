module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21GenA6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.QuasithinUnique

theorem orderOf_tMul : orderOf A6Models.tMul = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := A6Models.tMul)
    (by decide +kernel) (by decide +kernel)
  simpa using h

theorem tAdd_tInv_tMul_mem_pgl29 :
    A6Models.tAdd * A6Models.tInv * A6Models.tMul ∈ A6Models.pgl29 := by
  exact mul_mem (mul_mem (Out21.A6.psl29_le_pgl29 Out21.A6.tAdd_mem_psl29)
    (Out21.A6.psl29_le_pgl29 Out21.A6.tInv_mem_psl29)) Out21.A6.tMul_mem_pgl29

theorem orderOf_tAdd_tInv_tMul : orderOf (A6Models.tAdd * A6Models.tInv * A6Models.tMul) = 10 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (n := 10)
  · norm_num
  · decide +kernel
  · intro p hp hpdvd
    have hp2 : 2 ≤ p := hp.two_le
    have hp_le : p ≤ 10 := Nat.le_of_dvd (by norm_num) hpdvd
    interval_cases p <;> decide +kernel

theorem center_pgl29_eq_bot : center ↥A6Models.pgl29 = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hA : A6Models.tAdd ∈ A6Models.pgl29 :=
    Out21.A6.psl29_le_pgl29 Out21.A6.tAdd_mem_psl29
  have hI : A6Models.tInv ∈ A6Models.pgl29 :=
    Out21.A6.psl29_le_pgl29 Out21.A6.tInv_mem_psl29
  have hM : A6Models.tMul ∈ A6Models.pgl29 := Out21.A6.tMul_mem_pgl29
  have key : ∀ g ∈ A6Models.pgl29, ∀ x : Fin 10, (z : Equiv.Perm (Fin 10)) (g x) =
      g ((z : Equiv.Perm (Fin 10)) x) := by
    intro g hg x
    have := congrArg (fun p : ↥A6Models.pgl29 => (p : Equiv.Perm (Fin 10)) x) (hz ⟨g, hg⟩)
    simpa using this.symm
  have hs2 : A6Models.tInv * A6Models.tAdd * A6Models.tInv ∈ A6Models.pgl29 :=
    mul_mem (mul_mem hI hA) hI
  have h0 : (z : Equiv.Perm (Fin 10)) 0 = 0 := by
    have e1 := key _ hM 0
    have e2 := key _ hs2 0
    have c1 : A6Models.tMul 0 = 0 := by decide
    have c2 : (A6Models.tInv * A6Models.tAdd * A6Models.tInv) 0 = 0 := by decide
    rw [c1] at e1
    rw [c2] at e2
    have d1 : ∀ j : Fin 10, j = A6Models.tMul j → j = 0 ∨ j = 9 := by decide
    have d2 : ∀ j : Fin 10, j = (A6Models.tInv * A6Models.tAdd * A6Models.tInv) j → j ≠ 9 := by
      decide
    rcases d1 _ e1 with h | h
    · exact h
    · exact absurd h (d2 _ e2)
  have hw : ∀ i : Fin 10, ∃ w ∈ A6Models.pgl29, w 0 = i := by
    have hM2 := mul_mem hM hM
    have hM3 := mul_mem hM2 hM
    have hM4 := mul_mem hM3 hM
    have hM5 := mul_mem hM4 hM
    have hM6 := mul_mem hM5 hM
    have hM7 := mul_mem hM6 hM
    have hA2 := mul_mem hA hA
    have l : ∀ i : Fin 10, ∃ w ∈ [(1 : Equiv.Perm (Fin 10)), A6Models.tAdd,
        A6Models.tAdd * A6Models.tAdd, A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tMul * A6Models.tAdd,
        A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul * A6Models.tMul *
          A6Models.tMul * A6Models.tMul * A6Models.tAdd, A6Models.tInv], w 0 = i := by decide
    intro i
    obtain ⟨w, hw, hwi⟩ := l i
    refine ⟨w, ?_, hwi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hA
    · exact hA2
    · exact mul_mem hM hA
    · exact mul_mem hM2 hA
    · exact mul_mem hM3 hA
    · exact mul_mem hM5 hA
    · exact mul_mem hM6 hA
    · exact mul_mem hM7 hA
    · exact hI
  apply Subtype.ext
  refine Equiv.ext fun i => ?_
  obtain ⟨w, hwm, rfl⟩ := hw i
  have := key w hwm 0
  rw [h0] at this
  simpa using this

theorem isSimpleGroup_psl29 : IsSimpleGroup ↥A6Models.psl29 := by
  obtain ⟨ψ⟩ := Out21.A6.exists_psl29_equiv
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : Nontrivial ↥A6Models.psl29 := ψ.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective ψ.symm.toMonoidHom ψ.symm.surjective

theorem commutator_psl29_eq_self : ⁅A6Models.psl29, A6Models.psl29⁆ = A6Models.psl29 := by
  have hperf : Group.IsPerfect ↥A6Models.psl29 := by
    obtain ⟨ψ⟩ := Out21.A6.exists_psl29_equiv
    haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
    exact Group.IsPerfect.ofSurjective (f := ψ.symm.toMonoidHom) ψ.symm.surjective
  exact Subgroup.isPerfect_iff.mp hperf

theorem sq_mem_psl29 {x : Equiv.Perm (Fin 10)} (hx : x ∈ A6Models.pgl29) :
    x ^ 2 ∈ A6Models.psl29 := by
  let K : Subgroup ↥A6Models.pgl29 := A6Models.psl29.subgroupOf A6Models.pgl29
  have hindex : K.index = 2 := by
    have hcardK : Nat.card ↥K = 360 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Out21.A6.psl29_le_pgl29).toEquiv,
        A6Facts.card_psl29]
    have hcardpgl : Nat.card ↥A6Models.pgl29 = 720 := Out21.A6.card_pgl29
    have := K.card_mul_index
    rw [hcardK, hcardpgl] at this
    omega
  have h2 : (⟨x, hx⟩ : ↥A6Models.pgl29) ^ 2 ∈ K :=
    Subgroup.sq_mem_of_index_two hindex ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf] at h2
  simpa using h2

theorem pgl29_copy_facts {Y : Type*} [Group Y] {H : Subgroup Y} (e : ↥H ≃* ↥A6Models.pgl29)
    {w : Y} (hw : orderOf w = 2) (hH : H ≤ centralizer ({w} : Set Y)) :
    w ∉ H ∧ (∃ h ∈ H, orderOf h = 8) ∧ (∃ d ∈ H, orderOf d = 10) ∧
      ∃ A : Subgroup Y, A ≤ H ∧ Nat.card A = 360 ∧ IsSimpleGroup ↥A ∧ ⁅A, A⁆ = A ∧
        ∀ x ∈ H, x ^ 2 ∈ A := by
  classical
  let K : Subgroup ↥A6Models.pgl29 := A6Models.psl29.subgroupOf A6Models.pgl29
  let B : Subgroup ↥H := K.map (e.symm : ↥A6Models.pgl29 →* ↥H)
  let A : Subgroup Y := B.map H.subtype
  have isoA : ↥A ≃* ↥A6Models.psl29 :=
    (Subgroup.equivMapOfInjective B H.subtype H.subtype_injective).symm.trans
      (((e.symm).subgroupMap K).symm.trans
        (Subgroup.subgroupOfEquivOfLe Out21.A6.psl29_le_pgl29))
  have hAle : A ≤ H := Subgroup.map_subtype_le B
  have hcardA : Nat.card A = 360 := by
    rw [Nat.card_congr isoA.toEquiv, A6Facts.card_psl29]
  have hsimpleA : IsSimpleGroup ↥A := by
    haveI : IsSimpleGroup ↥A6Models.psl29 := isSimpleGroup_psl29
    exact isoA.isSimpleGroup
  have hcommA : ⁅A, A⁆ = A := by
    haveI : Group.IsPerfect ↥A6Models.psl29 :=
      Subgroup.isPerfect_iff.mpr commutator_psl29_eq_self
    haveI : Group.IsPerfect ↥A :=
      Group.IsPerfect.ofSurjective (f := isoA.symm.toMonoidHom) isoA.symm.surjective
    exact Subgroup.isPerfect_iff.mp inferInstance
  have hsqA : ∀ x ∈ H, x ^ 2 ∈ A := by
    intro x hx
    let xh : ↥H := ⟨x, hx⟩
    have hK : (e xh) ^ 2 ∈ K := by
      rw [Subgroup.mem_subgroupOf]
      exact sq_mem_psl29 (e xh).2
    have hB : xh ^ 2 ∈ B := by
      change xh ^ 2 ∈ K.map (e.symm : ↥A6Models.pgl29 →* ↥H)
      exact Subgroup.mem_map.mpr ⟨e xh ^ 2, hK, by simp⟩
    have hsub : H.subtype (xh ^ 2) ∈ B.map H.subtype :=
      Subgroup.mem_map.mpr ⟨xh ^ 2, hB, rfl⟩
    change x ^ 2 ∈ B.map H.subtype
    simpa using hsub
  refine ⟨?_, ?_, ?_, A, hAle, hcardA, hsimpleA, hcommA, hsqA⟩
  · intro hwH
    let wh : ↥H := ⟨w, hwH⟩
    have hcenter : e wh ∈ Subgroup.center ↥A6Models.pgl29 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := e.surjective g
      have hxw : x * wh = wh * x := by
        have hcomm : (x : Y) * w = w * (x : Y) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hH x.2)
        apply Subtype.ext
        simpa using hcomm
      calc e x * e wh = e (x * wh) := (e.map_mul x wh).symm
        _ = e (wh * x) := by rw [hxw]
        _ = e wh * e x := e.map_mul wh x
    have he1 : e wh = 1 := by
      have := hcenter
      rw [center_pgl29_eq_bot, Subgroup.mem_bot] at this
      exact this
    have hwh1 : wh = 1 := e.injective (by simpa using he1)
    have hw1 : w = 1 := Subtype.ext_iff.mp hwh1
    rw [hw1, orderOf_one] at hw
    omega
  · refine ⟨((e.symm ⟨A6Models.tMul, Out21.A6.tMul_mem_pgl29⟩ : ↥H) : Y),
      (e.symm ⟨A6Models.tMul, Out21.A6.tMul_mem_pgl29⟩ : ↥H).2, ?_⟩
    calc orderOf ((e.symm ⟨A6Models.tMul, Out21.A6.tMul_mem_pgl29⟩ : ↥H) : Y)
        = orderOf (e.symm ⟨A6Models.tMul, Out21.A6.tMul_mem_pgl29⟩ : ↥H) :=
          Subgroup.orderOf_coe _
      _ = orderOf (⟨A6Models.tMul, Out21.A6.tMul_mem_pgl29⟩ : ↥A6Models.pgl29) :=
          MulEquiv.orderOf_eq e.symm _
      _ = orderOf A6Models.tMul := Subgroup.orderOf_mk A6Models.tMul Out21.A6.tMul_mem_pgl29
      _ = 8 := orderOf_tMul
  · refine ⟨((e.symm ⟨A6Models.tAdd * A6Models.tInv * A6Models.tMul,
        tAdd_tInv_tMul_mem_pgl29⟩ : ↥H) : Y),
      (e.symm ⟨A6Models.tAdd * A6Models.tInv * A6Models.tMul, tAdd_tInv_tMul_mem_pgl29⟩ : ↥H).2, ?_⟩
    calc orderOf ((e.symm ⟨A6Models.tAdd * A6Models.tInv * A6Models.tMul,
            tAdd_tInv_tMul_mem_pgl29⟩ : ↥H) : Y)
        = orderOf (e.symm ⟨A6Models.tAdd * A6Models.tInv * A6Models.tMul,
            tAdd_tInv_tMul_mem_pgl29⟩ : ↥H) := Subgroup.orderOf_coe _
      _ = orderOf (⟨A6Models.tAdd * A6Models.tInv * A6Models.tMul,
            tAdd_tInv_tMul_mem_pgl29⟩ : ↥A6Models.pgl29) := MulEquiv.orderOf_eq e.symm _
      _ = orderOf (A6Models.tAdd * A6Models.tInv * A6Models.tMul) :=
          Subgroup.orderOf_mk _ tAdd_tInv_tMul_mem_pgl29
      _ = 10 := orderOf_tAdd_tInv_tMul

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
