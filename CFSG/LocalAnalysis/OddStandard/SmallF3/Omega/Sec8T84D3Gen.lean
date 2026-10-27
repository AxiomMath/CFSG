module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Odd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D3Comm

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 E1 E2 : Subgroup G}

private lemma sec8t84d3_comm_mul_right (a x y : G) :
    a * (x * y) * a⁻¹ * (x * y)⁻¹ =
      (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) := by
  group

private lemma sec8t84d3_comm_mul_left (x y b : G) :
    (x * y) * b * (x * y)⁻¹ * b⁻¹ =
      (x * (y * b * y⁻¹ * b⁻¹) * x⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
  group

private lemma sec8t84d3_comm_inv_right (a x : G) :
    a * x⁻¹ * a⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by
  group

private lemma sec8t84d3_comm_inv_left (x b : G) :
    x⁻¹ * b * (x⁻¹)⁻¹ * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * x := by
  group

theorem sec8t84d3_O_le_Y (h : Sec8T84DCtx G t E X1 X2) :
    oddCoreIn (normalizer (E : Set G)) ≤ Sec8T84Y X1 := by
  intro o ho
  exact sec8t84y_mem_of_odd (h.hX.c_le1 (h.hO ho)) (odd_orderOf_of_mem_oddCoreIn ho)

theorem sec8t84d3_comm_onto {V : Subgroup G} (hV : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u) {x : G}
    (hx : ∀ v ∈ V, x * v * x⁻¹ ∈ V) (hfix : ∀ v ∈ V, x * v * x⁻¹ = v → v = 1) {e : G}
    (he : e ∈ V) : ∃ v ∈ V, x * v * x⁻¹ * v⁻¹ = e := by
  haveI : Finite V := inferInstance
  let f : V →* V :=
    { toFun := fun v => ⟨x * (v : G) * x⁻¹, hx v v.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro u v
        apply Subtype.ext
        change x * ((u : G) * (v : G)) * x⁻¹ =
          (x * (u : G) * x⁻¹) * (x * (v : G) * x⁻¹)
        group }
  have hf_inj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    have h : x * (u : G) * x⁻¹ = x * (v : G) * x⁻¹ := congrArg Subtype.val huv
    exact mul_left_cancel (mul_right_cancel h)
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, Finite.surjective_of_injective hf_inj⟩
  let φ : V ≃* V := MulEquiv.ofBijective f hf_bij
  have hφval : ∀ v : V, ((φ v : V) : G) = x * (v : G) * x⁻¹ := fun v => rfl
  have hFF : MonoidHom.FixedPointFree φ := fun v hv => by
    apply Subtype.ext
    exact hfix (v : G) v.2 (by simpa [hφval v] using congrArg Subtype.val hv)
  let e' : V := ⟨e, he⟩
  obtain ⟨v, hv⟩ := MonoidHom.FixedPointFree.commutatorMap_surjective hFF (e'⁻¹)
  refine ⟨v, v.2, ?_⟩
  have hval : ((MonoidHom.commutatorMap φ v : V) : G)⁻¹ = e := by
    have h1 : (MonoidHom.commutatorMap φ v)⁻¹ = e' := by rw [hv, inv_inv]
    simpa [e'] using congrArg Subtype.val h1
  rw [← hval, MonoidHom.commutatorMap_apply]
  show x * (v : G) * x⁻¹ * (v : G)⁻¹ = ((v / φ v : V) : G)⁻¹
  rw [Subgroup.coe_div, hφval v, div_eq_mul_inv, mul_inv_rev, inv_inv]

theorem sec8t84d3_E1_le_Y (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2) :
    E1 ≤ Sec8T84Y X1 := by
  intro e he
  obtain ⟨x, hxX1, hx5, hxC⟩ := hd.ex5_1
  obtain ⟨y, hyX1, hyodd, hy5, hyC⟩ := sec8t84y_odd_five hxX1 hx5 hxC
  haveI : IsMulCommutative E := h.elem.1.1
  have hV : ∀ u ∈ E1, ∀ v ∈ E1, u * v = v * u := by
    intro u hu v hv
    exact Subgroup.mul_comm_of_mem_isMulCommutative E (hd.le1 hu) (hd.le1 hv)
  obtain ⟨v, hvE1, hveq⟩ :=
    sec8t84d3_comm_onto hV (hd.inv1 y hyX1) (hd.fpf1 y hyX1 hy5 hyC) he
  have hvX1 : v ∈ X1 := by
    apply h.hX.c_le1
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mul_comm_of_mem_isMulCommutative E hw (hd.le1 hvE1)
  have hyY : y ∈ Sec8T84Y X1 := sec8t84y_mem_of_odd hyX1 hyodd
  have hconj : v * y * v⁻¹ ∈ Sec8T84Y X1 :=
    sec8t84y_conj (H := X1) (H' := X1) (g := v)
      (fun w hw => X1.mul_mem (X1.mul_mem hvX1 hw) (X1.inv_mem hvX1)) hyY
  have hmem : y * (v * y * v⁻¹)⁻¹ ∈ Sec8T84Y X1 :=
    (Sec8T84Y X1).mul_mem hyY ((Sec8T84Y X1).inv_mem hconj)
  convert hmem using 1
  rw [← hveq]
  group

theorem sec8t84d3_comm_Y (h : Sec8T84DCtx G t E X1 X2) (hd : Sec8T84DDec G t E X1 X2 E1 E2)
    {a b : G} (ha : a ∈ Sec8T84Y X1) (hb : b ∈ Sec8T84Y X2) :
    a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
  have hA : ∀ a ∈ X1, Odd (orderOf a) → ∀ b ∈ Sec8T84Y X2,
      a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)) := by
    intro a ha hao b hb
    change b ∈ closure {x | x ∈ X2 ∧ Odd (orderOf x)} at hb
    refine Subgroup.closure_induction
      (k := {x | x ∈ X2 ∧ Odd (orderOf x)})
      (p := fun b _ => a * b * a⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)))
      ?_ ?_ ?_ ?_ hb
    · intro x hx
      exact sec8t84d3_comm_odd h hd ha hao hx.1 hx.2
    · simp
    · intro x y hx hy ihx ihy
      rw [sec8t84d3_comm_mul_right]
      have hxX : x ∈ normalizer (E : Set G) := h.hX.le2 (sec8t84y_le X2 hx)
      exact mul_mem ihx (conj_mem_oddCoreIn (Subgroup.le_normalizer hxX) ihy)
    · intro x hx ihx
      rw [sec8t84d3_comm_inv_right]
      have hxX : x ∈ normalizer (E : Set G) := h.hX.le2 (sec8t84y_le X2 hx)
      have hconj : x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * (x⁻¹)⁻¹ ∈
          oddCoreIn (normalizer (E : Set G)) :=
        conj_mem_oddCoreIn (K := normalizer (E : Set G))
          (Subgroup.le_normalizer ((normalizer (E : Set G)).inv_mem hxX)) (inv_mem ihx)
      simpa using hconj
  change a ∈ closure {x | x ∈ X1 ∧ Odd (orderOf x)} at ha
  refine Subgroup.closure_induction
    (k := {x | x ∈ X1 ∧ Odd (orderOf x)})
    (p := fun x _ => x * b * x⁻¹ * b⁻¹ ∈ oddCoreIn (normalizer (E : Set G)))
    ?_ ?_ ?_ ?_ ha
  · intro x hx
    exact hA x hx.1 hx.2 b hb
  · simp
  · intro x y hx hy ihx ihy
    rw [sec8t84d3_comm_mul_left]
    have hxX : x ∈ normalizer (E : Set G) := h.hX.le1 (sec8t84y_le X1 hx)
    exact mul_mem (conj_mem_oddCoreIn (Subgroup.le_normalizer hxX) ihy) ihx
  · intro x hx ihx
    rw [sec8t84d3_comm_inv_left]
    have hxX : x ∈ normalizer (E : Set G) := h.hX.le1 (sec8t84y_le X1 hx)
    have hconj : x⁻¹ * (x * b * x⁻¹ * b⁻¹)⁻¹ * (x⁻¹)⁻¹ ∈
        oddCoreIn (normalizer (E : Set G)) :=
      conj_mem_oddCoreIn (K := normalizer (E : Set G))
        (Subgroup.le_normalizer ((normalizer (E : Set G)).inv_mem hxX)) (inv_mem ihx)
    simpa using hconj

end CFSG.OddStandard.SmallF3.Omega
