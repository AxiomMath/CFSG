module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKDBase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KDCong
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2KFacts

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer GorensteinWalter
open CFSG.ComponentClassification.AutL2Facts CFSG.ComponentClassification.CatalogueSchreierLinearTwo

namespace L2KD

open L2K

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
variable {F : Type} [Field F] [Finite F]

theorem mem_normalizer_of_cycle (C : A.CaseKD) (S : Gens A) {κ w d : X}
    (hκ : κ = C.k ∨ κ = S.z * C.k) (hdL : d ∈ L) (hdκ : d * κ = κ * d)
    (hdz : d * S.z * d⁻¹ = w) (hdw : d * w * d⁻¹ = S.z * w) :
    d ∈ normalizer (L2E S.z w t C.k : Set X) := by
  have hdC := L_le_C (A := A) hdL
  have hk : d * C.k * d⁻¹ ∈ L2E S.z w t C.k := by
    rcases hκ with rfl | rfl
    · rw [hdκ, mul_inv_cancel_right]
      exact mem_L2E_four S.z w t C.k
    · have h : d * C.k * d⁻¹ = (d * S.z * d⁻¹)⁻¹ * (d * (S.z * C.k) * d⁻¹) := by group
      rw [h, hdκ, mul_inv_cancel_right, hdz]
      exact mul_mem (inv_mem (mem_L2E_two S.z w t C.k))
        (mul_mem (mem_L2E_one S.z w t C.k) (mem_L2E_four S.z w t C.k))
  refine mem_normalizer_L2E ?_ ?_ ?_ hk
  · rw [hdz]
    exact mem_L2E_two S.z w t C.k
  · rw [hdw]
    exact mul_mem (mem_L2E_one S.z w t C.k) (mem_L2E_two S.z w t C.k)
  · rw [commute_t_of_mem_C hdC, mul_inv_cancel_right]
    exact mem_L2E_three S.z w t C.k

@[expose] def kdBase_of_frames (C : A.CaseKD) (S : Gens A)
    (Fr₁ : Frame A F C.k) (Fr₂ : Frame A F (S.z * C.k)) {w₁ w₂ x : X}
    (hw₁V : w₁ ∈ Fr₁.V) (hw₂V : w₂ ∈ Fr₂.V) (hw₁2 : w₁ ^ 2 = 1) (hw₂2 : w₂ ^ 2 = 1)
    (hw₁1 : w₁ ≠ 1) (hw₁z : w₁ ≠ S.z) (hw₂1 : w₂ ≠ 1) (hw₂z : w₂ ≠ S.z)
    (hV₁ : ∀ v, v ∈ Fr₁.V ↔ v = 1 ∨ v = S.z ∨ v = w₁ ∨ v = S.z * w₁)
    (hV₂ : ∀ v, v ∈ Fr₂.V ↔ v = 1 ∨ v = S.z ∨ v = w₂ ∨ v = S.z * w₂)
    (hxR : x ∈ A.R) (hx2 : x ^ 2 = S.z) (hx4 : orderOf x = 4) (hxy : x * w₁ = w₂)
    (hinv : w₁ * x * w₁⁻¹ = x⁻¹) : KDBase A C where
  x := x
  y := w₁
  x_mem := hxR
  y_mem := Fr₁.V_le_R hw₁V
  orderOf_x := hx4
  y_sq := hw₁2
  y_inv := hinv
  d_y := by
    rw [hx2]
    obtain ⟨d₁, hd₁L, hd₁κ, hd₁z, hd₁w⟩ :=
      Fr₁.exists_cycle S hV₁ hw₁1 hw₁z (S.z_comm_R (Fr₁.V_le_R hw₁V))
    refine ⟨d₁, L_le_C (A := A) hd₁L,
      mem_normalizer_of_cycle C S (Or.inl rfl) hd₁L hd₁κ hd₁z hd₁w, hd₁z, hd₁w, ?_⟩
    rw [hd₁κ, mul_inv_cancel_right]
  d_xy := by
    rw [hx2, hxy]
    obtain ⟨d₂, hd₂L, hd₂κ, hd₂z, hd₂w⟩ :=
      Fr₂.exists_cycle S hV₂ hw₂1 hw₂z (S.z_comm_R (Fr₂.V_le_R hw₂V))
    refine ⟨d₂, L_le_C (A := A) hd₂L,
      mem_normalizer_of_cycle C S (Or.inr rfl) hd₂L hd₂κ hd₂z hd₂w, hd₂z, hd₂w, ?_⟩
    rw [hd₂κ, mul_inv_cancel_right]
  k_fixed := by
    rw [hx2]
    exact fun n hn => Frame.conj_eq_of_mem_normalizer_kd Fr₁ S C (Or.inl rfl) hw₁V hw₁2 hw₁1
      hw₁z hn
  zk_fixed := by
    rw [hx2, hxy]
    exact fun n hn => Frame.conj_eq_of_mem_normalizer_kd Fr₂ S C (Or.inr rfl) hw₂V hw₂2 hw₂1
      hw₂z hn
  card_conj_z := by
    rw [hx2]
    exact card_conj_z_modEq_kd C S Fr₁
  card_conj_k := card_conj_k_modEq C S Fr₁
  card_conj_d := fun _ => card_conj_d_modEq C S Fr₁

end L2KD

open L2K L2KD in
theorem fritzL2KDFacts : FritzL2KDFacts := by
  intro X _ _ t L F _ _ he A C
  obtain ⟨e₀⟩ := he
  obtain ⟨S⟩ := nonempty_gens (A := A)
  have hzk : S.z * C.k ∈ A.T := mul_mem S.z_mem.1 C.k_mem
  have hzkc : S.z * C.k = C.k * S.z := (L2KD.commute_k C S.z_mem).symm
  have hzk2 : (S.z * C.k) ^ 2 = 1 := by
    rw [(show Commute S.z C.k from hzkc).mul_pow, S.z_sq, C.k_sq, one_mul]
  have hzkR : ∀ r ∈ A.R, S.z * C.k * r = r * (S.z * C.k) := by
    intro r hr
    rw [mul_assoc, L2KD.commute_k C hr, ← mul_assoc, S.z_comm_R hr, mul_assoc]
  have hψk : ψX A C.k ∉ R8 := by
    rw [L2KD.ψX_k C]
    exact k8_not_mem_R8
  have hψzk : ψX A (S.z * C.k) ∉ R8 := by
    rw [ψX_mul S.z_mem.1 C.k_mem, S.ψ_z, L2KD.ψX_k C]
    exact z8_mul_k8_not_mem_R8
  obtain ⟨Fr₁⟩ := nonempty_frame e₀ S C.k_mem C.k_sq (fun r hr => L2KD.commute_k C hr) hψk
  obtain ⟨Fr₂⟩ := nonempty_frame e₀ S hzk hzk2 hzkR hψzk
  obtain ⟨w₁, hw₁, hw₁V, -, hV₁⟩ := Fr₁.V_eq S
  obtain ⟨w₂, hw₂, hw₂V, -, hV₂⟩ := Fr₂.V_eq S
  have hy1 : S.y₀ ≠ 1 := fun h => by
    have := S.ψ_y₀
    rw [h, ψX_one] at this
    exact y8_ne_one this.symm
  have hyz : S.y₀ ≠ S.z := fun h => by
    have := S.ψ_y₀
    rw [h, S.ψ_z] at this
    exact y8_ne_z8 this.symm
  have hxy1 : S.x₀ * S.y₀ ≠ 1 := fun h => by
    have := S.ψ_xy
    rw [h, ψX_one] at this
    exact x8_mul_y8_ne_one this.symm
  have hxyz : S.x₀ * S.y₀ ≠ S.z := fun h => by
    have := S.ψ_xy
    rw [h, S.ψ_z] at this
    exact x8_mul_y8_ne_z8 this.symm
  have hw₁2 : w₁ ^ 2 = 1 := by
    rcases hw₁ with rfl | rfl
    exacts [S.y₀_sq, S.xy_sq]
  have hw₁1 : w₁ ≠ 1 := by
    rcases hw₁ with rfl | rfl
    exacts [hy1, hxy1]
  have hw₁z : w₁ ≠ S.z := by
    rcases hw₁ with rfl | rfl
    exacts [hyz, hxyz]
  have hne : w₁ ≠ w₂ := by
    intro hw
    have hzw₁ : S.z * w₁ = w₁ * S.z := S.z_comm_R (Fr₁.V_le_R hw₁V)
    obtain ⟨d, hdL, hdk, hdz, hdw⟩ := Fr₁.exists_cycle S hV₁ hw₁1 hw₁z hzw₁
    have hdC := L_le_C (A := A) hdL
    have hdN := L2KD.mem_normalizer_of_cycle C S (Or.inl rfl) hdL hdk hdz hdw
    have hw₁V₂ : w₁ ∈ Fr₂.V := hw ▸ hw₂V
    have hfix := L2KD.Frame.conj_eq_of_mem_normalizer_kd Fr₂ S C (Or.inr rfl) hw₁V₂ hw₁2 hw₁1
      hw₁z (Subgroup.mem_inf.mpr ⟨hdN, hdC⟩)
    apply hw₁z
    have hk : d * C.k * d⁻¹ = C.k := by rw [hdk, mul_inv_cancel_right]
    calc w₁ = d * (S.z * C.k) * d⁻¹ * (d * C.k * d⁻¹)⁻¹ := by
          rw [← hdz]
          group
      _ = S.z := by rw [hfix, hk, mul_inv_cancel_right]
  rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl
  · exact absurd rfl hne
  ·
    exact ⟨L2KD.kdBase_of_frames C S Fr₁ Fr₂ hw₁V hw₂V S.y₀_sq S.xy_sq hy1 hyz hxy1 hxyz hV₁ hV₂
      S.x₀_mem rfl S.orderOf_x₀ rfl S.y₀_x₀_y₀⟩
  ·
    have hx2 : S.x₀⁻¹ ^ 2 = S.z := by
      rw [inv_pow, Gens.z, inv_eq_iff_mul_eq_one, ← pow_add, show 2 + 2 = 4 by rfl,
        S.x₀_pow_four]
    have hinv : S.x₀ * S.y₀ * S.x₀⁻¹ * (S.x₀ * S.y₀)⁻¹ = S.x₀⁻¹⁻¹ := by
      have h := S.y₀_x₀_y₀
      calc S.x₀ * S.y₀ * S.x₀⁻¹ * (S.x₀ * S.y₀)⁻¹ = S.x₀ * (S.y₀ * S.x₀ * S.y₀⁻¹)⁻¹ * S.x₀⁻¹ := by
            group
        _ = S.x₀⁻¹⁻¹ := by rw [h]; group
    exact ⟨L2KD.kdBase_of_frames C S Fr₁ Fr₂ hw₁V hw₂V S.xy_sq S.y₀_sq hxy1 hxyz hy1 hyz hV₁ hV₂
      (inv_mem S.x₀_mem) hx2 (by rw [orderOf_inv, S.orderOf_x₀]) (by group) hinv⟩
  · exact absurd rfl hne

end CFSG.ComponentClassification.HSFLit
