module

public import CFSG.HardMathSupport.Foote.E27.Lie
public import CFSG.HardMathSupport.Foote.E27.LocalBound
public import CFSG.HardMathSupport.Foote.E27.Split

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}

omit [Finite X] in
theorem fixed_map_le_centralizer [K.Normal] {D : Subgroup ↥K}
    (hD : ∀ x ∈ D, (MulAut.conjNormal z : MulAut ↥K) x = x) :
    D.map K.subtype ≤ centralizer ({z} : Set X) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_singleton_iff]
  have h1 := congrArg Subtype.val (hD x hx)
  simp only [MulAut.conjNormal_apply] at h1
  show (x : X) * z = z * x
  calc (x : X) * z = (z * x * z⁻¹) * z := by rw [h1]
    _ = z * x := by group

theorem e27LieOut_of_aut (hAut : E27LieOuterAut) : E27LieOut := by
  intro X _ _ K R T z hc hz d ⟨e⟩
  have := hc.normal
  have hD3 := three_pow_five_dvd_card_mulAut K hc.faithful R T z hc.elem hc.card_R hc.T_le_R
    hc.card_T hc.z_mem hc.z_not_mem hc.fus hc.sylow hc.central hc.dvd81
  have hu3 : ((MulAut.conjNormal z : MulAut ↥K)) ^ 3 = 1 := by
    rw [← map_pow, hc.elem.2 z hc.z_mem, map_one]
  have hout : ∀ k : ↥K, (MulAut.conjNormal z : MulAut ↥K) ≠ MulAut.conj k := by
    intro k hk
    apply hz
    have hcent : (k : X)⁻¹ * z ∈ centralizer (K : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥K => Subtype.val (f ⟨x, hx⟩)) hk
      simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
      have h2 : z * x * z⁻¹ = k * x * (k : X)⁻¹ := h1
      have h3 : (k : X)⁻¹ * (z * x * z⁻¹) * k = x := by rw [h2]; group
      calc x * ((k : X)⁻¹ * z) = ((k : X)⁻¹ * (z * x * z⁻¹) * k) * ((k : X)⁻¹ * z) := by rw [h3]
        _ = ((k : X)⁻¹ * z) * x := by group
    rw [hc.faithful] at hcent
    have : (k : X)⁻¹ * z = 1 := hcent
    have hkz : (k : X) = z := inv_mul_eq_one.mp this
    exact hkz ▸ k.2
  have hperf : ∀ D : Subgroup ↥K, (∀ x ∈ D, (MulAut.conjNormal z : MulAut ↥K) x = x) →
      ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D := by
    intro D hD hDD
    have hcomm : ⁅D.map K.subtype, D.map K.subtype⁆ = D.map K.subtype := by
      rw [← Subgroup.map_commutator, hDD]
    have := hc.perfect (D.map K.subtype) (fixed_map_le_centralizer hD) hcomm
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at this
  have hp3 : ∀ Q : Subgroup ↥K, (∀ x ∈ Q, (MulAut.conjNormal z : MulAut ↥K) x = x) →
      IsPGroup 3 Q → Nat.card Q ≤ 9 := by
    intro Q hQ hQ3
    have := hc.card_le_nine_of_isPGroup hz
      (Q := Q.map K.subtype)
      (le_inf (fixed_map_le_centralizer hQ) (by rintro _ ⟨x, -, rfl⟩; exact x.2)) (hQ3.map _)
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at this
  have hT : ∃ T' : Subgroup ↥K, (∀ x ∈ T', (MulAut.conjNormal z : MulAut ↥K) x = x) ∧
      IsElemAbelian 3 T' ∧ Nat.card T' = 9 := by
    refine ⟨T.subgroupOf K, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · intro x hx
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply]
      have hxR : (x : X) ∈ R := hc.T_le_R hx
      have := congrArg Subtype.val
        (hc.elem.1.is_comm.comm (⟨x, hxR⟩ : R) ⟨z, hc.z_mem⟩)
      have h5 : (x : X) * z = z * x := this
      calc z * (x : X) * z⁻¹ = (x * z) * z⁻¹ := by rw [h5]
        _ = x := by group
    · have key : (a.1.1 : X) * b.1.1 = b.1.1 * a.1.1 :=
        congrArg Subtype.val
          (hc.elem.1.is_comm.comm (⟨a.1.1, hc.T_le_R a.2⟩ : R) ⟨b.1.1, hc.T_le_R b.2⟩)
      exact Subtype.ext (Subtype.ext key)
    · apply Subtype.ext
      have := hc.elem.2 (x : X) (hc.T_le_R hx)
      simpa using this
    · rw [← hc.card_T]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.T_le_K).toEquiv
  exact hAut ↥K d ⟨e⟩ hD3 (MulAut.conjNormal z) hu3 hout hperf hp3 hT

end CFSG.HardMathSupport.Foote.E27
