module

public import CFSG.LargeExtraspecial.S5OneD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S5

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open CFSG.ComponentClassification

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem norm_map_conj {X : Subgroup S.O}
    (hX : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X : Set S.O)) (k h : S.M) :
    S.Lbar ((h : G) * g) ≤
      normalizer ((X.map (MulAut.conj (S.ρ k)).toMonoidHom : Subgroup S.O) : Set S.O) := by
  intro l hl
  have hl' : (S.ρ k)⁻¹ * l * S.ρ k ∈ S.Lbar (((k⁻¹ * h : S.M) : G) * g) := by
    have e : (S.ρ (k⁻¹ * h))⁻¹ * ((S.ρ k)⁻¹ * l * S.ρ k) * S.ρ (k⁻¹ * h) =
        (S.ρ h)⁻¹ * l * S.ρ h := by
      simp only [map_mul, map_inv]
      group
    rw [mem_Lbar_mul_iff, e]
    exact (mem_Lbar_mul_iff S h g).mp hl
  have hN := mem_normalizer_iff.mp (hX _ hl')
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff, mem_map_conj_iff]
  have e2 : ((S.ρ k)⁻¹ * l * S.ρ k) * ((S.ρ k)⁻¹ * y * S.ρ k) * ((S.ρ k)⁻¹ * l * S.ρ k)⁻¹ =
      (S.ρ k)⁻¹ * (l * y * l⁻¹) * S.ρ k := by group
  rw [← e2]
  exact hN _

namespace PairData

variable (P : PairData S g)

theorem exists_conj_fix (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {x : S.O} (hx : x ∈ P.X₁) :
    ∃ s ∈ S.Lbar g ⊓ P.X₁, x * s * x⁻¹ ≠ 1 ∧
      ((x * s * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
        S.cl (g * S.z * g⁻¹) := by
  classical
  have haQ := H.conj_mem
  have hL : LinCase S g P.τ_mem_Lbar := P.A₂.linCase hIrr H hNo C hVτ
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g P.τ) := ((P.A₂.hyp45q hIrr H hNo C Q).2 hVτ).2
  have hxR : x ∈ Rbar S g P.τ := P.A₂.le_Rbar hIrr H hx
  obtain ⟨c, hc⟩ : ∃ c, c = resV haQ P.τ ⟨x, hxR⟩ := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = c⁻¹ (aV P.τ_mem_Lbar) := ⟨_, rfl⟩
  obtain ⟨φ, hφ0, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Vt S g P.τ), φ ≠ 0 ∧
      Submodule.span (ZMod 2) ({aV P.τ_mem_Lbar, w} : Set (Vt S g P.τ)) ≤ LinearMap.ker φ := by
    apply Submodule.exists_le_ker_of_lt_top
    rw [lt_top_iff_ne_top]
    intro htop
    have h1 := finrank_span_finset_le_card (R := ZMod 2)
      ({aV P.τ_mem_Lbar, w} : Finset (Vt S g P.τ))
    rw [Finset.coe_insert, Finset.coe_singleton] at h1
    change finrank (ZMod 2) (Submodule.span (ZMod 2) _) ≤ _ at h1
    rw [htop, finrank_top] at h1
    have h2 := Finset.card_le_two (a := aV P.τ_mem_Lbar) (b := w)
    omega
  have hφa : φ (aV P.τ_mem_Lbar) = 0 := hφ (Submodule.subset_span (Set.mem_insert _ _))
  have hφw : φ w = 0 := hφ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  have heL : LinearEquiv.transvection hφa ∈ LmodN S g P.τ := by
    rw [hL.LmodN_eq]
    exact transvection_mem_centreGroup hφa
  obtain ⟨s, hs, hse⟩ := heL
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := P.exists_mul hCE hIrr H hNo C Q hn hVt hVτ hs
  have hs₂N : s₂ ∈ Nbar S g P.τ :=
    P.A₂.mem_Nbar_of_commute hIrr H hNo C Q hs₂.1 fun y hy => (P.comm hy hs₂.2).symm
  have hs₁v : ∀ v : Vt S g P.τ, ((LinearEquiv.transvection hφa v : Vt S g P.τ) : S.Qt) =
      (s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v := by
    intro v
    rw [hse v, coe_mul_apply, hs₂N.2 v v.2]
  have hxw : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = (w : S.Qt) := by
    rw [hw, hc, ← map_inv, coe_resV_apply]
    rfl
  refine ⟨s₁, hs₁, ?_, ?_⟩
  · intro h1
    have hs1 : s₁ = 1 := by
      have e : s₁ = x⁻¹ * (x * s₁ * x⁻¹) * x := by group
      rw [e, h1, mul_one, inv_mul_cancel]
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφ0 (LinearMap.ext hcon)
    have hv1 : φ v = 1 := (CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one _).resolve_left hv
    have := hs₁v v
    rw [hs1, LinearEquiv.transvection.apply, hv1, one_smul] at this
    have h0 : ((aV P.τ_mem_Lbar : Vt S g P.τ) : S.Qt) = 0 := by
      have h2 : ((v : S.Qt) + (aV P.τ_mem_Lbar : S.Qt)) = v := this
      calc ((aV P.τ_mem_Lbar : Vt S g P.τ) : S.Qt) = (v + aV P.τ_mem_Lbar : S.Qt) - v := by abel
        _ = 0 := by rw [h2, sub_self]
    exact aV_ne_zero H P.τ_mem_Lbar (Subtype.ext h0)
  · calc ((x * s₁ * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹))
        = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)))) := by
          rw [coe_mul_apply, coe_mul_apply]
      _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) ((LinearEquiv.transvection hφa w : Vt S g P.τ) : S.Qt) := by
          rw [hxw, hs₁v w]
      _ = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (S.cl (g * S.z * g⁻¹))) := by
          rw [LinearEquiv.transvection.apply, hφw, zero_smul, add_zero, hxw]
      _ = S.cl (g * S.z * g⁻¹) := apply_inv_apply_O x _

theorem commute_of_mem_sup (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M)
    (hk : S.ρ k ∈ P.X₁ ⊔ P.X₂) :
    (g * S.z * g⁻¹) * ((k : G) * g * S.z * ((k : G) * g)⁻¹) =
      ((k : G) * g * S.z * ((k : G) * g)⁻¹) * (g * S.z * g⁻¹) := by
  have hN : P.X₁ ≤ normalizer (P.X₂ : Set S.O) := fun x hx =>
    mem_normalizer_of_forall_commute fun y hy => P.comm hx hy
  obtain ⟨x₁, hx₁, x₂, hx₂, hk'⟩ := exists_mul_of_mem_sup hN hk
  obtain ⟨s, hs, hs1, hfix⟩ := P.exists_conj_fix hCE hIrr H hNo C Q hn hVt hVτ hx₁
  have he : S.ρ k * s * (S.ρ k)⁻¹ = x₁ * s * x₁⁻¹ := by
    rw [hk']
    have h2 : x₂ * s = s * x₂ := (P.comm hs.2 hx₂).symm
    calc x₁ * x₂ * s * (x₁ * x₂)⁻¹ = x₁ * (x₂ * s) * x₂⁻¹ * x₁⁻¹ := by group
      _ = x₁ * (s * x₂) * x₂⁻¹ * x₁⁻¹ := by rw [h2]
      _ = x₁ * s * x₁⁻¹ := by group
  have hmem : x₁ * s * x₁⁻¹ ∈ S.Lbar ((k : G) * g) := he ▸ conj_mem_Lbar_mul S k hs.1
  have hM : x₁ * s * x₁⁻¹ ∈ S.Mbar :=
    P.comp₁.1 (P.X₁.mul_mem (P.X₁.mul_mem hx₁ hs.2) (P.X₁.inv_mem hx₁))
  have hnorm : x₁ * s * x₁⁻¹ ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hM (by simpa using hfix)
    simpa using this
  exact S4.lemma_4_1 H k ⟨_, hmem, hnorm, hs1⟩

theorem eq_or_eq_of_norm (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) {X₃ : Subgroup S.O}
    (h₃ : IsComponentOf X₃ S.Mbar)
    (hn₃ : ∀ h : S.M, S.Lbar ((h : G) * g) ≤ normalizer (X₃ : Set S.O)) :
    X₃ = P.X₁ ∨ X₃ = P.X₂ := by
  by_contra hne
  push Not at hne
  obtain ⟨hne₁, hne₂⟩ := hne
  obtain ⟨⟨s, hs⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Lbar_inf_ne_bot hIrr H C h₃ hn₃)
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hsL : s ∈ S.Lbar g := (Subgroup.mem_inf.mp hs).1
  have hsX : s ∈ X₃ := (Subgroup.mem_inf.mp hs).2
  obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := P.exists_mul hCE hIrr H hNo C Q hn hVt hVτ hsL
  have hcomm : ∀ z ∈ X₃, s * z = z * s := by
    intro z hz
    have c₁ : s₁ * z = z * s₁ := mul_comm_of_isComponentOf_ne P.comp₁ h₃ (Ne.symm hne₁) hs₁.2 hz
    have c₂ : s₂ * z = z * s₂ := mul_comm_of_isComponentOf_ne P.comp₂ h₃ (Ne.symm hne₂) hs₂.2 hz
    rw [hss]
    calc s₁ * s₂ * z = s₁ * (s₂ * z) := mul_assoc _ _ _
      _ = s₁ * (z * s₂) := by rw [c₂]
      _ = (s₁ * z) * s₂ := (mul_assoc _ _ _).symm
      _ = z * s₁ * s₂ := by rw [c₁]
      _ = z * (s₁ * s₂) := mul_assoc _ _ _
  have hss2 : s ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact S4.mul_self_of_mem_Lbar S H.conj_mem hsL
  exact hs1' (eq_one_of_mem_center_of_pow S h₃.2.1 hsX hcomm hss2)

theorem map_sup_eq (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M) :
    (P.X₁ ⊔ P.X₂).map (MulAut.conj (S.ρ k)).toMonoidHom = P.X₁ ⊔ P.X₂ := by
  have hkM : (S.ρ k : S.O) ∈ S.Mbar := ⟨k, rfl⟩
  have hinj : Function.Injective (Subgroup.map (MulAut.conj (S.ρ k)).toMonoidHom) :=
    map_injective fun _ _ h => (MulAut.conj (S.ρ k)).injective h
  have hne : P.X₁.map (MulAut.conj (S.ρ k)).toMonoidHom ≠
      P.X₂.map (MulAut.conj (S.ρ k)).toMonoidHom := fun h => P.ne (hinj h)
  rw [Subgroup.map_sup]
  rcases P.eq_or_eq_of_norm hCE hIrr H hNo C Q hn hVt hVτ (isComponentOf_map_conj P.comp₁ hkM)
      (norm_map_conj P.norm₁ k) with h₁ | h₁ <;>
    rcases P.eq_or_eq_of_norm hCE hIrr H hNo C Q hn hVt hVτ (isComponentOf_map_conj P.comp₂ hkM)
      (norm_map_conj P.norm₂ k) with h₂ | h₂
  · exact absurd (h₁.trans h₂.symm) hne
  · rw [h₁, h₂]
  · rw [h₁, h₂, sup_comm]
  · exact absurd (h₁.trans h₂.symm) hne

theorem exists_cl_eq (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width)
    (hVt : V S g P.t ≤ S.Qa g) (hVτ : V S g P.τ ≤ S.Qa g) (k : S.M) :
    ∃ j : S.M, S.ρ j ∈ P.X₁ ⊔ P.X₂ ∧
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) = S.cl ((j : G) * g * S.z * ((j : G) * g)⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haQ := H.conj_mem
  have hYM : P.X₁ ⊔ P.X₂ ≤ S.Mbar := sup_le P.comp₁.1 P.comp₂.1
  have hLY : S.Lbar g ≤ P.X₁ ⊔ P.X₂ := by
    intro s hs
    obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := P.exists_mul hCE hIrr H hNo C Q hn hVt hVτ hs
    exact mul_mem (mem_sup_left hs₁.2) (mem_sup_right hs₂.2)
  obtain ⟨T, hT, hLT⟩ := exists_isSylowTwoIn_ge hLY (S4.isPGroup_Lbar S haQ)
  have hTN : T ≤ normalizer (S.Lbar g : Set S.O) :=
    S4.le_normalizer_of_weaklyClosed C.weaklyClosed hT.isPGroup (hT.le.trans hYM) hLT
  have hT' : IsSylowTwoIn (T.map (MulAut.conj (S.ρ k)).toMonoidHom) (P.X₁ ⊔ P.X₂) := by
    have := hT.map (MulAut.conj (S.ρ k)).toMonoidHom
    rwa [P.map_sup_eq hCE hIrr H hNo C Q hn hVt hVτ k] at this
  obtain ⟨c, hcY, hc⟩ := hT.exists_conj hT'
  obtain ⟨j, hj⟩ := MonoidHom.mem_range.mp (hYM hcY)
  have hjk : S.Lbar (((j⁻¹ * k : S.M) : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    intro l hl
    apply hTN
    have hl' : (S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k) ∈ S.Lbar g := (mem_Lbar_mul_iff S _ g).mp hl
    have hmem : S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹ ∈
        T.map (MulAut.conj (S.ρ k)).toMonoidHom := by
      rw [mem_map_conj_iff]
      have e : (S.ρ k)⁻¹ * (S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹) *
          S.ρ k = (S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k) := by group
      rw [e]
      exact hLT hl'
    have h2 := (hc _).mp hmem
    rw [← hj] at h2
    have e : (S.ρ j)⁻¹ * (S.ρ k * ((S.ρ (j⁻¹ * k))⁻¹ * l * S.ρ (j⁻¹ * k)) * (S.ρ k)⁻¹) *
        S.ρ j = l := by
      simp only [map_mul, map_inv]
      group
    rwa [e] at h2
  have heq := C.weaklyClosed _ (j⁻¹ * k).2 hjk
  have hnorm : S.ρ (j⁻¹ * k) ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [Lbar_mul S (j⁻¹ * k)] at heq
    exact mem_normalizer_of_map_conj_eq heq
  have hfix := fix_of_mem_normalizer H hnorm
  refine ⟨j, hj ▸ hcY, ?_⟩
  rw [← ρ_cl_conj_z S k haQ, ← ρ_cl_conj_z S j haQ]
  have e : S.ρ k = S.ρ j * S.ρ (j⁻¹ * k) := by
    rw [map_mul, map_inv, mul_inv_cancel_left]
  rw [e, coe_mul_apply, hfix]

include P in
theorem false (hCE : CentralExtInput.{u}) (hIrr : Irr S) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) (Q : Hyp45Q H C) (hn : 4 < S.width) : False := by
  have hVτ : V S g P.τ ≤ S.Qa g := by
    by_contra h
    exact P.false_of_not_le hCE hIrr H hNo C Q hn h
  have hVt : V S g P.t ≤ S.Qa g := by
    by_contra h
    exact P.swap.false_of_not_le hCE hIrr H hNo C Q hn h
  have hpol : ∀ v ∈ conjCl S g, QuadraticMap.polar S.q (S.cl (g * S.z * g⁻¹)) v = 0 := by
    rintro _ ⟨k, rfl⟩
    obtain ⟨j, hjY, hj⟩ := P.exists_cl_eq hCE hIrr H hNo C Q hn hVt hVτ k
    rw [hj, S.polar_cl_eq_zero_iff H.conj_mem (conj_mem_QG' S j.2 H.conj_mem)]
    exact P.commute_of_mem_sup hCE hIrr H hNo C Q hn hVt hVτ j hjY
  apply cl_conj_z_ne_zero S H.conj_mem H.conj_ne
  refine S.q_nondegenerate.1 _ fun v => ?_
  rw [QuadraticMap.polarBilin_apply_apply]
  have hv : v ∈ Submodule.span (ZMod 2) (conjCl S g) := by
    rw [span_conjCl_eq_top hIrr H]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv => exact hpol v hv
  | zero => exact QuadraticMap.polar_zero_right _ _
  | add u w _ _ hu hw => rw [QuadraticMap.polar_add_right, hu, hw, add_zero]
  | smul c u _ hu => rw [QuadraticMap.polar_smul_right, hu, smul_zero]

end PairData

end CFSG.LargeExtraspecial.S5
