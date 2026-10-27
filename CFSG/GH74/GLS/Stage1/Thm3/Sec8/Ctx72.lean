module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx63

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Fused8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem exists_pre8_dec (hII : II4_4_4_center) (hq : II4_4_quat) (h31 : IVK_3_1a_lifted)
    (hf : Fused8 G z S K₁ K₂) :
    ∃ (W₁ W₂ U : Subgroup G) (u : G), Pre8 G z S K₁ K₂ W₁ W₂ U u ∧
      ∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, k₁ * k₁ = z ∧ k₂ * k₂ = z ∧ u = k₁ * k₂ := by
  obtain ⟨W₁, W₂, hW₁, hW₂, hN₁, hN₂, hc₁, hc₂, hsw⟩ := hf.exists_W hII
  obtain ⟨⟨w₁, hw₁, h4₁⟩, ⟨w₂, hw₂, h4₂⟩⟩ := hf.exists_w hII hq hW₁ hW₂ hc₁ hc₂
  have hQ₁ := hf.gq_Q₁ hII
  have hQ₂ := hf.gq_Q₂ hII
  have hz2 := hf.z_sq
  have hz1 := hf.z_ne
  have hw₁Q : w₁ ∈ Qof S K₁ := hW₁.1 hw₁.1
  have hw₂Q : w₂ ∈ Qof S K₂ := hW₂.1 hw₂.1
  have hsq₁ : w₁ * w₁ = z := hQ₁.sq_of_orderOf_four hw₁Q h4₁
  have hsq₂ : w₂ * w₂ = z := hQ₂.sq_of_orderOf_four hw₂Q h4₂
  have hw₁S : w₁ ∈ S := hw₁.2.1
  have hw₂S : w₂ ∈ S := hw₂.2.1
  have hcomm : w₁ * w₂ = w₂ * w₁ := (hf.P_comm hII w₂ hw₂.2 w₁ hw₁.2).symm
  have hzw₁ : z * w₁ = w₁ * z := (hf.z_comm hII hw₁S).symm
  have hzw₂ : z * w₂ = w₂ * z := (hf.z_comm hII hw₂S).symm
  have hPinf := hf.P_inf hII
  have hord_not : ∀ w : G, orderOf w = 4 → w ∉ zpowers z := by
    intro w hw hwz
    rcases (Basic.mem_zpowers_of_sq' hz2).1 hwz with h | h
    · rw [h, orderOf_one] at hw; omega
    · rw [h, hf.std.orderOf_z] at hw; omega
  have hw₁P₁ : w₁ ∈ Pof S K₁ → False := fun h =>
    hord_not w₁ h4₁ (by rw [← hPinf]; exact ⟨h, hw₁.2⟩)
  have hw₂P₂ : w₂ ∈ Pof S K₂ → False := fun h =>
    hord_not w₂ h4₂ (by rw [← hPinf]; exact ⟨hw₂.2, h⟩)
  obtain ⟨u, hu⟩ : ∃ u : G, u = w₁ * w₂ := ⟨_, rfl⟩
  have hu2 : u * u = 1 := by
    calc u * u = w₁ * (w₂ * w₁) * w₂ := by rw [hu]; group
      _ = w₁ * (w₁ * w₂) * w₂ := by rw [← hcomm]
      _ = (w₁ * w₁) * (w₂ * w₂) := by group
      _ = 1 := by rw [hsq₁, hsq₂, hz2]
  have hu1 : u ≠ 1 := by
    intro h
    apply hw₁P₁
    have h' : w₁ * w₂ = 1 := by rw [← hu]; exact h
    have : w₁ = w₂⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [this]
    exact inv_mem hw₂.2
  have huz : u ≠ z := by
    intro h
    have : w₁ = w₂ := by
      have h' : w₁ * w₂ = w₂ * w₂ := by rw [hsq₂, ← hu]; exact h
      exact mul_right_cancel h'
    apply hw₁P₁
    rw [this]; exact hw₂.2
  have huP : u ∈ Pz S z := by
    rw [hf.Pz_eq_sup hII]
    rw [hu]
    exact mul_mem (Subgroup.mem_sup_right hw₁.2) (Subgroup.mem_sup_left hw₂.2)
  have hu_ord : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu2) hu1
  have hconj : IsConj z u := hf.invol_P_conj hII h31 u huP hu_ord
  have hzu : z * u = u * z := by
    rw [hu]
    calc z * (w₁ * w₂) = (z * w₁) * w₂ := by group
      _ = (w₁ * z) * w₂ := by rw [hzw₁]
      _ = w₁ * (z * w₂) := by group
      _ = w₁ * (w₂ * z) := by rw [hzw₂]
      _ = w₁ * w₂ * z := by group
  obtain ⟨hUcard, hUelems⟩ := Basic.four_of_comm_invol hz2 hu2 hz1 hu1 huz hzu
  set U : Subgroup G := zpowers z ⊔ zpowers u with hU
  have hzU : z ∈ U := Subgroup.mem_sup_left (mem_zpowers z)
  have huU : u ∈ U := Subgroup.mem_sup_right (mem_zpowers u)
  have hUsq : ∀ y ∈ U, y * y = 1 := by
    intro y hy
    rcases hUelems y hy with h | h | h | h
    · rw [h, one_mul]
    · rw [h]; exact hz2
    · rw [h]; exact hu2
    · rw [h]
      calc u * z * (u * z) = u * (z * u) * z := by group
        _ = u * (u * z) * z := by rw [hzu]
        _ = (u * u) * (z * z) := by group
        _ = 1 := by rw [hu2, hz2, one_mul]
  have hU4 : IVK.IsFourSubgroup U := ⟨Basic.isElemAbelian2_of_sq_one hUsq, hUcard⟩
  have hzW : z ∈ W₁ := by rw [← hsq₁]; exact mul_mem hw₁.1 hw₁.1
  have hULe : U ≤ W₁ ⊔ W₂ := by
    refine sup_le (zpowers_le.2 (Subgroup.mem_sup_left hzW)) (zpowers_le.2 ?_)
    rw [hu]
    exact mul_mem (Subgroup.mem_sup_left hw₁.1) (Subgroup.mem_sup_right hw₂.1)
  have hSu : ∀ s ∈ S, s * u * s⁻¹ = u ∨ s * u * s⁻¹ = u * z := by
    intro s hsS
    have hord_conj : ∀ w : G, orderOf w = 4 → orderOf (s * w * s⁻¹) = 4 := by
      intro w hw
      have := (MulAut.conj s).orderOf_eq w
      rw [MulAut.conj_apply] at this
      rw [this, hw]
    have hcyc₂ : IsCyclic ↥(W₁ ⊓ Pof S K₂) := Basic.isCyclic_of_le inf_le_left hW₁.2.1
    have hcyc₁ : IsCyclic ↥(W₂ ⊓ Pof S K₁) := Basic.isCyclic_of_le inf_le_left hW₂.2.1
    by_cases hs1 : s ∈ S1 S K₁
    · have h1 : s * w₁ * s⁻¹ ∈ W₁ ⊓ Pof S K₂ :=
        ⟨hN₁ s hs1 w₁ hw₁.1, hf.S1_normalizes_P hII (Or.inr rfl) s hs1 w₁ hw₁.2⟩
      have h2 : s * w₂ * s⁻¹ ∈ W₂ ⊓ Pof S K₁ :=
        ⟨hN₂ s hs1 w₂ hw₂.1, hf.S1_normalizes_P hII (Or.inl rfl) s hs1 w₂ hw₂.2⟩
      rw [hu]
      exact conj_u_alg hz2 hsq₁ hsq₂ hcomm hzw₁ hzw₂ (Or.inl
        ⟨Basic.eq_or_inv_of_cyc hcyc₂ hw₁ h1 h4₁ (hord_conj w₁ h4₁),
          Basic.eq_or_inv_of_cyc hcyc₁ hw₂ h2 h4₂ (hord_conj w₂ h4₂)⟩)
    · have h1 : s * w₁ * s⁻¹ ∈ W₂ ⊓ Pof S K₁ :=
        ⟨(hsw s hsS hs1).1 w₁ hw₁.1, hf.swap_P₂ hII hsS hs1 hw₁.2⟩
      have h2 : s * w₂ * s⁻¹ ∈ W₁ ⊓ Pof S K₂ :=
        ⟨(hsw s hsS hs1).2 w₂ hw₂.1, hf.swap_P₁ hII hsS hs1 hw₂.2⟩
      rw [hu]
      exact conj_u_alg hz2 hsq₁ hsq₂ hcomm hzw₁ hzw₂ (Or.inr
        ⟨Basic.eq_or_inv_of_cyc hcyc₁ hw₂ h1 h4₂ (hord_conj w₁ h4₁),
          Basic.eq_or_inv_of_cyc hcyc₂ hw₁ h2 h4₁ (hord_conj w₂ h4₂)⟩)
  have hUn : NormedBy U S := by
    intro s hsS v hv
    have hsz : s * z * s⁻¹ = z := by rw [hf.z_comm hII hsS]; group
    rcases hUelems v hv with h | h | h | h
    · rw [h]; simp
    · rw [h, hsz]; exact hzU
    · rw [h]
      rcases hSu s hsS with h' | h'
      · rw [h']; exact huU
      · rw [h']; exact mul_mem huU hzU
    · rw [h]
      have e : s * (u * z) * s⁻¹ = (s * u * s⁻¹) * (s * z * s⁻¹) := by group
      rw [e, hsz]
      rcases hSu s hsS with h' | h'
      · rw [h']; exact mul_mem huU hzU
      · rw [h', mul_assoc, hz2, mul_one]; exact huU
  refine ⟨W₁, W₂, U, u, ⟨hf, hW₁, hW₂, hN₁, hN₂, hULe, hU4, hUn, hzU, huU, ?_, hconj⟩,
    w₂, hw₂.2.2, w₁, hw₁.2.2, hsq₂, hsq₁, hu.trans hcomm⟩
  intro hmem
  rcases (Basic.mem_zpowers_of_sq' hz2).1 hmem with h | h
  · exact hu1 h
  · exact huz h

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
