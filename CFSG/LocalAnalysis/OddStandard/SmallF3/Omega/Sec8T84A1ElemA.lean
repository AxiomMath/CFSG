module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Pre

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B K : Subgroup G}

private theorem sec8t84a1_E_centralizes_B (hK : Sec8T84A1Pre G t L S z g B K) {x : G}
    (hx : x ∈ K) {b : G} (hb : b ∈ B) : x * b = b * x :=
  (Subgroup.mem_centralizer_iff.mp (hK.le_C hx).2 b hb).symm

theorem sec8t84a1_E_comm_t (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K) {x : G}
    (hx : x ∈ K) : x * t * x⁻¹ * t⁻¹ ∈ B := by
  exact sec8t84a1_comm_mem h8B hK.ctx (hK.le_C hx).1

theorem sec8t84a1_E_tau_mul (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) :
    (x * y) * t * (x * y)⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) := by
  have hu : x * t * x⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hx
  have hw : y * t * y⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hy
  have hxw : x * (y * t * y⁻¹ * t⁻¹) * x⁻¹ = y * t * y⁻¹ * t⁻¹ := by
    rw [sec8t84a1_E_centralizes_B hK hx hw]
    group
  have hyt : y * t * y⁻¹ = (y * t * y⁻¹ * t⁻¹) * t := by group
  have hxt : x * t * x⁻¹ = (x * t * x⁻¹ * t⁻¹) * t := by group
  calc
    (x * y) * t * (x * y)⁻¹ * t⁻¹
        = x * (y * t * y⁻¹) * x⁻¹ * t⁻¹ := by group
      _ = x * ((y * t * y⁻¹ * t⁻¹) * t) * x⁻¹ * t⁻¹ := by rw [hyt]; group
      _ = (x * (y * t * y⁻¹ * t⁻¹) * x⁻¹) * (x * t * x⁻¹) * t⁻¹ := by group
      _ = (y * t * y⁻¹ * t⁻¹) * ((x * t * x⁻¹ * t⁻¹) * t) * t⁻¹ := by rw [hxw, hxt]; group
      _ = (y * t * y⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹) := by group
      _ = (x * t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) :=
            (sec8t84a1_B_comm hK.ctx hu hw).symm

private theorem sec8t84a1_E_tau_inv (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K)
    {x : G} (hx : x ∈ K) : x⁻¹ * t * x * t⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by
  have h := sec8t84a1_E_tau_mul h8B hK hx (K.inv_mem hx)
  have h1 : (x * x⁻¹) * t * (x * x⁻¹)⁻¹ * t⁻¹ = 1 := by
    rw [mul_inv_cancel]
    group
  rw [h1] at h
  simpa using eq_inv_of_mul_eq_one_right h.symm

theorem sec8t84a1_E_mem_A_iff (hK : Sec8T84A1Pre G t L S z g B K) {x : G} (hx : x ∈ K) :
    x ∈ Asub8 t B ↔ x * t * x⁻¹ * t⁻¹ = 1 := by
  rw [← hK.cent_t]
  constructor
  · intro h
    have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp h.2
    rw [hcomm]
    group
  · intro h
    refine ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h' : x * t * x⁻¹ = t := by
      have h2 := mul_eq_one_iff_eq_inv.mp h
      simpa using h2
    calc x * t = (x * t * x⁻¹) * x := by group
      _ = t * x := by rw [h']

theorem sec8t84a1_E_comm_A (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K) {x a : G}
    (hx : x ∈ K) (ha : a ∈ Asub8 t B) : x * a * x⁻¹ * a⁻¹ ∈ B := by
  rcases sec8t84a1_mem_A hK.ctx ha with haB | ⟨b, hb, rfl⟩
  · have hxa : x * a * x⁻¹ = a := by
      rw [sec8t84a1_E_centralizes_B hK hx haB]
      group
    rw [hxa, mul_inv_cancel]
    exact B.one_mem
  · have hxb : x * b * x⁻¹ = b := by
      rw [sec8t84a1_E_centralizes_B hK hx hb]
      group
    have hkey : x * (t * b) * x⁻¹ * (t * b)⁻¹ = x * t * x⁻¹ * t⁻¹ := by
      rw [show x * (t * b) * x⁻¹ * (t * b)⁻¹ =
        (x * t * x⁻¹) * (x * b * x⁻¹) * b⁻¹ * t⁻¹ by group]
      rw [hxb]
      group
    rw [hkey]
    exact sec8t84a1_E_comm_t h8B hK hx

theorem sec8t84a1_E_sq_A (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K) {x : G}
    (hx : x ∈ K) : x * x ∈ Asub8 t B := by
  rw [sec8t84a1_E_mem_A_iff hK (K.mul_mem hx hx)]
  rw [sec8t84a1_E_tau_mul h8B hK hx hx]
  exact sec8t84a1_B_sq hK.ctx (sec8t84a1_E_comm_t h8B hK hx)

theorem sec8t84a1_E_comm_in_A (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K)
    {x y : G} (hx : x ∈ K) (hy : y ∈ K) : x * y * x⁻¹ * y⁻¹ ∈ Asub8 t B := by
  have hcK : x * y * x⁻¹ * y⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  rw [sec8t84a1_E_mem_A_iff hK hcK]
  have hu : x * t * x⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hx
  have hv : y * t * y⁻¹ * t⁻¹ ∈ B := sec8t84a1_E_comm_t h8B hK hy
  have hmain : (x * y * x⁻¹ * y⁻¹) * t * (x * y * x⁻¹ * y⁻¹)⁻¹ * t⁻¹ =
      (x * t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) *
        ((x * t * x⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * t⁻¹)⁻¹) := by
    have h1 := sec8t84a1_E_tau_mul h8B hK (K.mul_mem hx hy)
      (K.mul_mem (K.inv_mem hx) (K.inv_mem hy))
    have h2 := sec8t84a1_E_tau_mul h8B hK hx hy
    have h3 := sec8t84a1_E_tau_mul h8B hK (K.inv_mem hx) (K.inv_mem hy)
    have hux : x⁻¹ * t * (x⁻¹)⁻¹ * t⁻¹ = (x * t * x⁻¹ * t⁻¹)⁻¹ := by
      simpa only [inv_inv] using sec8t84a1_E_tau_inv h8B hK hx
    have huy : y⁻¹ * t * (y⁻¹)⁻¹ * t⁻¹ = (y * t * y⁻¹ * t⁻¹)⁻¹ := by
      simpa only [inv_inv] using sec8t84a1_E_tau_inv h8B hK hy
    rw [h2, h3, hux, huy] at h1
    calc
      (x * y * x⁻¹ * y⁻¹) * t * (x * y * x⁻¹ * y⁻¹)⁻¹ * t⁻¹
          = ((x * y) * (x⁻¹ * y⁻¹)) * t * ((x * y) * (x⁻¹ * y⁻¹))⁻¹ * t⁻¹ := by group
        _ = (x * t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) *
              ((x * t * x⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * t⁻¹)⁻¹) := h1
  rw [hmain]
  have hcomm : (y * t * y⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹)⁻¹ =
      (x * t * x⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * t⁻¹) :=
    sec8t84a1_B_comm hK.ctx hv (B.inv_mem hu)
  calc
    (x * t * x⁻¹ * t⁻¹) * (y * t * y⁻¹ * t⁻¹) *
        ((x * t * x⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * t⁻¹)⁻¹)
        = (x * t * x⁻¹ * t⁻¹) * ((y * t * y⁻¹ * t⁻¹) * (x * t * x⁻¹ * t⁻¹)⁻¹) *
            (y * t * y⁻¹ * t⁻¹)⁻¹ := by group
      _ = (x * t * x⁻¹ * t⁻¹) * ((x * t * x⁻¹ * t⁻¹)⁻¹ * (y * t * y⁻¹ * t⁻¹)) *
            (y * t * y⁻¹ * t⁻¹)⁻¹ := by rw [hcomm]
      _ = 1 := by group

theorem sec8t84a1_E_sq_mul (h8B : Asc82Lemma8B) (hK : Sec8T84A1Pre G t L S z g B K) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) :
    ∃ b ∈ B, (x * y) * (x * y) = b * (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * x) * (y * y) := by
  have hcA : x * y * x⁻¹ * y⁻¹ ∈ Asub8 t B := sec8t84a1_E_comm_in_A h8B hK hx hy
  have hcA_inv : (x * y * x⁻¹ * y⁻¹)⁻¹ ∈ Asub8 t B := (Asub8 t B).inv_mem hcA
  have hb : x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹ * (x * y * x⁻¹ * y⁻¹) ∈ B := by
    have h := sec8t84a1_E_comm_A h8B hK hx hcA_inv
    simpa using h
  refine ⟨x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹ * (x * y * x⁻¹ * y⁻¹), hb, ?_⟩
  group

theorem sec8t84a1_E_indep (hctx : Sec8Ctx G t L S z g B) :
    ∃ v₁ ∈ B, ∃ v₂ ∈ B, ∃ v₃ ∈ B, v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₃ ≠ 1 ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
      v₃ ≠ v₁ * v₂ := by
  classical
  have hcard : Nat.card B = 16 := sec8t84a1_B_card hctx
  letI : Fintype B := Fintype.ofFinite B
  have hcard' : Fintype.card B = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨v1, -, hv1⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset B)) (t := Finset.univ)
    (by rw [Finset.card_univ, hcard']; simp)
  simp only [Finset.mem_singleton] at hv1
  obtain ⟨v2, -, hv2⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (insert v1 ({1} : Finset B))) (t := Finset.univ)
    (by
      rw [Finset.card_univ, hcard']
      have hC := Finset.card_insert_le v1 ({1} : Finset B)
      have hD : ({1} : Finset B).card = 1 := Finset.card_singleton 1
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv2
  obtain ⟨v3, -, hv3⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := (insert (v1 * v2) (insert v2 (insert v1 ({1} : Finset B))))) (t := Finset.univ)
    (by
      rw [Finset.card_univ, hcard']
      have hA := Finset.card_insert_le (v1 * v2) (insert v2 (insert v1 ({1} : Finset B)))
      have hB := Finset.card_insert_le v2 (insert v1 ({1} : Finset B))
      have hC := Finset.card_insert_le v1 ({1} : Finset B)
      have hD : ({1} : Finset B).card = 1 := Finset.card_singleton 1
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv3
  refine ⟨(v1 : G), v1.2, (v2 : G), v2.2, (v3 : G), v3.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hv1 (Subtype.coe_injective h)
  · exact fun h => hv2.2 (Subtype.coe_injective h)
  · exact fun h => hv3.2.2.2 (Subtype.coe_injective h)
  · exact fun h => hv2.1 (Subtype.coe_injective h).symm
  · exact fun h => hv3.2.2.1 (Subtype.coe_injective h).symm
  · exact fun h => hv3.2.1 (Subtype.coe_injective h).symm
  · intro h
    exact hv3.1 (Subtype.ext (by simpa using h))

end CFSG.OddStandard.SmallF3.Omega
