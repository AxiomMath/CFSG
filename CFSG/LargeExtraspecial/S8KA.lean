module

public import CFSG.LargeExtraspecial.S8ThreeF
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8ThreeD
public import CFSG.LargeExtraspecial.S9GenA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem comm_mem_Abar_and_commute (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ) (hττ : τ * τ = 1)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {α : S.O}
    (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    α * τ * α⁻¹ * τ⁻¹ ∈ S.Lbar g ⊓ Nbar S g t ∧
      (α * τ * α⁻¹ * τ⁻¹) * τ = τ * (α * τ * α⁻¹ * τ⁻¹) := by
  have haQ := H.conj_mem
  have hN := mem_normalizer_Abar_of_fix H ht hτM hτt hτV
  have hβ : τ * α⁻¹ * τ⁻¹ ∈ S.Lbar g ⊓ Nbar S g t :=
    (mem_normalizer_iff.mp hN _).mp (inv_mem hα)
  refine ⟨?_, ?_⟩
  · rw [show α * τ * α⁻¹ * τ⁻¹ = α * (τ * α⁻¹ * τ⁻¹) by group]
    exact mul_mem hα hβ
  · have hcomm : α * (τ * α⁻¹ * τ⁻¹) = (τ * α⁻¹ * τ⁻¹) * α := Lbar_comm S haQ hα.1 hβ.1
    have e1 : α⁻¹ = α := inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S haQ hα.1)
    have e2 : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
    rw [e1, e2] at hcomm ⊢
    have hc' : α * τ * α * τ = τ * α * τ * α := by
      calc α * τ * α * τ = α * (τ * α * τ) := by group
        _ = τ * α * τ * α := by rw [hcomm]
    symm
    calc τ * (α * τ * α * τ) = (τ * α * τ * α) * τ := by group
      _ = (α * τ * α * τ) * τ := by rw [← hc']

theorem exists_conj_of_mem_conj_Nbar (hNo : NoA2 S g) (hΩ : OmegaCase H C ht ht1 hVQ)
    (D : Std H C ht ht1 hVQ) {x τ α : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτN : τ ∉ Nbar S g t) (hα : α ∈ S.Lbar g ⊓ Nbar S g t)
    (hcN : α * τ * α⁻¹ * τ⁻¹ ∈ Nbar S g t) (hc1 : α * τ * α⁻¹ * τ⁻¹ ≠ 1)
    (hgood : x⁻¹ * (α * τ * α⁻¹) * x ∈ Nbar S g t) :
    ∃ γ ∈ S.Mbar, α * τ * α⁻¹ * τ⁻¹ = γ * t * γ⁻¹ := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htN := self_mem_Nbar H ht
  obtain ⟨c, hc⟩ : ∃ c, c = α * τ * α⁻¹ * τ⁻¹ := ⟨_, rfl⟩
  rw [← hc] at hcN hc1 ⊢
  obtain ⟨c', hc'⟩ : ∃ c', c' = x⁻¹ * c * x := ⟨_, rfl⟩
  have hσ' : x⁻¹ * (α * τ * α⁻¹) * x = c' * t := by
    rw [hc', hc, hxτ]; group
  have hc'N : c' ∈ Nbar S g t := by
    have := mul_mem hgood (inv_mem htN)
    rwa [hσ', mul_inv_cancel_right] at this
  have hc'1 : c' ≠ 1 := by
    intro h
    apply hc1
    rw [hc'] at h
    calc c = x * (x⁻¹ * c * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hc't : c' ≠ t := by
    intro h
    apply hτN
    have hcτ : c = τ := by
      rw [hxτ, ← h, hc']; group
    rw [← hcτ]
    exact hcN
  have hnc : ¬ ∀ n ∈ Nbar S g t, n * c' = c' * n := by
    intro hcen
    have hz : c' ∈ Zbar S g t := mem_Zbar.mpr ⟨hc'N, hcen⟩
    rcases eq_one_or_eq_of_mem_zpowers htt (Zbar_le_zpowers hNo hΩ D hz) with h | h
    · exact hc'1 h
    · exact hc't h
  push Not at hnc
  obtain ⟨n, hn, hnc'⟩ := hnc
  have hcomm := D.hNc n hn c' hc'N
  have hnc't : n * c' * n⁻¹ * c'⁻¹ = t := by
    rcases eq_one_or_eq_of_mem_zpowers htt hcomm with h | h
    · exfalso
      apply hnc'
      calc n * c' = (n * c' * n⁻¹ * c'⁻¹) * (c' * n) := by group
        _ = c' * n := by rw [h, one_mul]
    · exact h
  have hnt : n * t = t * n := commute_of_mem_Rbar haQ (Nbar_le_Rbar hn)
  have hc't' : c' * t = t * c' := commute_of_mem_Rbar haQ (Nbar_le_Rbar hc'N)
  have hconj : n * (c' * t) * n⁻¹ = c' := by
    have e1 : n * c' * n⁻¹ = t * c' := by
      calc n * c' * n⁻¹ = (n * c' * n⁻¹ * c'⁻¹) * c' := by group
        _ = t * c' := by rw [hnc't]
    calc n * (c' * t) * n⁻¹ = (n * c' * n⁻¹) * (n * t * n⁻¹) := by group
      _ = t * c' * t := by rw [e1, hnt, mul_inv_cancel_right]
      _ = c' * (t * t) := by rw [← hc't']; group
      _ = c' := by rw [htt, mul_one]
  have hnM : n ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar hn)
  have hαM : α ∈ S.Mbar := S.Lbar_le_Mbar g hα.1
  refine ⟨x * n * x⁻¹ * α * x, ?_, ?_⟩
  · exact S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.mul_mem (S.Mbar.mul_mem hxM hnM)
      (inv_mem hxM)) hαM) hxM
  · calc c = x * c' * x⁻¹ := by rw [hc']; group
      _ = x * (n * (x⁻¹ * (α * τ * α⁻¹) * x) * n⁻¹) * x⁻¹ := by rw [hσ', hconj]
      _ = (x * n * x⁻¹ * α * x) * t * (x * n * x⁻¹ * α * x)⁻¹ := by rw [hxτ]; group

theorem three_le_finrank_commSpace_inf_ker (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm : D.m = 3 ∨ D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hk : D.m = 3 → finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2)
    {α : S.O} (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    3 ≤ finrank (ZMod 2) ↥(commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      LinearMap.ker ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) := by
  have haQ := H.conj_mem
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  have hnf : ¬ ∀ w ∈ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t := fun hfl =>
    hτN (mem_Nbar_of_flag hCE hNo hΩ D (by omega) hfus hsub hxM hxτ hτt hτV hfl)
  set f := (α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1 with hf
  set K := (Wt S g t).map ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) with hK
  set U := K ⊔ Vt S g t with hU
  set Xa := S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t ⊔ Vt S g t with hXa
  set T := commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hT
  have hVW := Vt_le_Wt H ht1
  have hUW : U ≤ Wt S g t := by
    refine sup_le ?_ hVW
    rintro _ ⟨w, hw, rfl⟩
    exact (Wt S g t).sub_mem (apply_mem_Wt_of_commute H C ht ht1 hVQ hτt hw) hw
  have hVU : Vt S g t ≤ U := le_sup_right
  obtain ⟨-, -, hhalf⟩ := finrank_map_mkQ_of_invariant hCE hNo hΩ D hVU hUW
    (comm_sup_Vt_invariant D hτM hτt hτV)
  rw [← hXa] at hhalf
  have hd3 : D.m = 3 → finrank (ZMod 2) (U.map (Vt S g t).mkQ) = 4 := fun h3 =>
    (finrank_inf_of_three hCE hNo hΩ D h3 hxM hxτ hτt hτV hnf).1
  have hd4 : D.m = 4 → finrank (ZMod 2) (U.map (Vt S g t).mkQ) = 8 ∧
      finrank (ZMod 2) ↥(Vt S g t ⊓ T) = 0 := fun h4 => by
    obtain ⟨h8, hbot⟩ := finrank_inf_of_four hCE hNo hΩ D h4 hxM hxτ hτt hτV hnf
    refine ⟨h8, ?_⟩
    rw [hT, hbot, finrank_bot]
  have eU := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ U
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVU] at eU
  have hVUX : Vt S g t ≤ U ⊓ Xa := le_inf hVU le_sup_right
  have eUX := finrank_map_add_finrank_inf_ker (Vt S g t).mkQ (U ⊓ Xa)
  rw [Submodule.ker_mkQ, inf_eq_right.mpr hVUX] at eUX
  have hfV : ∀ v ∈ Vt S g t, f v = 0 := fun v hv => by
    rw [hf, LinearMap.sub_apply, Module.End.one_apply, LinearEquiv.coe_coe,
      (mem_Nbar.mp hα.2).2 v hv, sub_self]
  have hUXa : (U ⊓ Xa).map f ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hu.2
    rw [map_add, hfV v hv, add_zero]
    exact Lbar_apply_sub_mem_span' haQ hp.1 hα.1
  have i1 : finrank (ZMod 2) ((U ⊓ Xa).map f) ≤ 1 :=
    (Submodule.finrank_mono hUXa).trans
      (finrank_span_singleton (cl_conj_z_ne_zero S haQ H.conj_ne)).le
  have e1 := finrank_map_add_finrank_inf_ker f U
  have e2 := finrank_map_add_finrank_inf_ker f (U ⊓ Xa)
  have i2 : finrank (ZMod 2) ↥(U ⊓ Xa ⊓ LinearMap.ker f) ≤
      finrank (ZMod 2) ↥(U ⊓ LinearMap.ker f) :=
    Submodule.finrank_mono (inf_le_inf_right _ inf_le_left)
  have hdimT : finrank (ZMod 2) T = finrank (ZMod 2) (Vt S g t) := by
    rw [hT, hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have eK := finrank_map_Wt_add (S := S) (g := g) (t := t) τ
  rw [← hK, ← hT] at eK
  have hKT : K ≤ T := by
    rintro _ ⟨w, -, rfl⟩
    exact sub_mem_commSpace _ w
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq K (Vt S g t)
  rw [← hU] at e3
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq K (Vt S g t ⊓ T)
  have i3 : finrank (ZMod 2) ↥(K ⊓ (Vt S g t ⊓ T)) ≤ finrank (ZMod 2) ↥(K ⊓ Vt S g t) :=
    Submodule.finrank_mono (inf_le_inf_left _ inf_le_left)
  have hle1 : K ⊔ (Vt S g t ⊓ T) ≤ T ⊓ U :=
    sup_le (le_inf hKT le_sup_left) (le_inf inf_le_right (inf_le_left.trans le_sup_right))
  have i4 := Submodule.finrank_mono hle1
  have e5 := finrank_map_add_finrank_inf_ker f (T ⊓ U)
  have i5 : finrank (ZMod 2) ((T ⊓ U).map f) ≤ finrank (ZMod 2) (U.map f) :=
    Submodule.finrank_mono (Submodule.map_mono inf_le_right)
  have i6 : finrank (ZMod 2) ↥(T ⊓ U ⊓ LinearMap.ker f) ≤
      finrank (ZMod 2) ↥(T ⊓ LinearMap.ker f) :=
    Submodule.finrank_mono (inf_le_inf_right _ inf_le_left)
  have hdimV := D.hdim
  rcases hm with h3 | h4
  · have := hk h3
    have := hd3 h3
    rw [h3] at hdimV
    omega
  · obtain ⟨h8, hk0⟩ := hd4 h4
    rw [h4] at hdimV
    omega

theorem mem_conj_Nbar_of_mem_Abar (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm : D.m = 3 ∨ D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hk : D.m = 3 → finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2)
    {α : S.O} (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    x⁻¹ * (α * τ * α⁻¹) * x ∈ Nbar S g t := by
  have h6 : 6 ≤ finrank (ZMod 2) (Vt S g t) := by rw [D.hdim]; omega
  have hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t :=
    fun k hk => cl_mem_orbit_of_omegaCase hCE H hNo C hΩ h6 hk
  have h3 := three_le_finrank_commSpace_inf_ker hCE hNo hΩ D hm hsub hxM hxτ hτt hτV hτN hk hα
  have hαM : α ∈ S.Mbar := S.Lbar_le_Mbar g hα.1
  have hyM : x⁻¹ * α * x ∈ S.Mbar :=
    S.Mbar.mul_mem (S.Mbar.mul_mem (inv_mem hxM) hαM) hxM
  have hσ : x⁻¹ * (α * τ * α⁻¹) * x = (x⁻¹ * α * x) * t * (x⁻¹ * α * x)⁻¹ := by
    rw [hxτ]; group
  by_contra hσN
  have hle := finrank_Vt_inf_le_two D hfus hsub hyM hσ hσN
  set e := ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with he
  have hmap : (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ⊓
      LinearMap.ker ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map e.toLinearMap ≤
      Vt S g t ⊓ commSpace ((x⁻¹ * (α * τ * α⁻¹) * x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rintro _ ⟨v, ⟨hvT, hvk⟩, rfl⟩
    have hαv : (α : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
      have := LinearMap.mem_ker.mp hvk
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
      exact this
    refine ⟨?_, ?_⟩
    · rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1] at hvT
      obtain ⟨w, hw, rfl⟩ := hvT
      change ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ _
      rw [inv_apply_apply_O]
      exact hw
    · have e1 : x⁻¹ * (α * τ * α⁻¹) * x = x⁻¹ * (α * τ * α⁻¹) * x⁻¹⁻¹ := by rw [inv_inv]
      rw [e1, commSpace_conj, commSpace_conj]
      refine ⟨v, ⟨v, hvT, hαv⟩, rfl⟩
  have hfin := Submodule.finrank_mono hmap
  rw [LinearEquiv.finrank_map_eq] at hfin
  omega

theorem comm_mem_conjL_of_mem_Abar (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm : D.m = 3 ∨ D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hk : D.m = 3 → finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2)
    {α : S.O} (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    α * τ * α⁻¹ * τ⁻¹ = 1 ∨ α * τ * α⁻¹ * τ⁻¹ ∈ S9.conjL S g t := by
  have hτM : τ ∈ S.Mbar := by
    rw [hxτ]; exact S.Mbar.mul_mem (S.Mbar.mul_mem hxM (S.Lbar_le_Mbar g ht)) (inv_mem hxM)
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hττ : τ * τ = 1 := by
    rw [hxτ]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [htt]; group
  obtain ⟨hcA, -⟩ := comm_mem_Abar_and_commute H ht hτM hτt hττ hτV hα
  by_cases hc1 : α * τ * α⁻¹ * τ⁻¹ = 1
  · exact Or.inl hc1
  right
  obtain ⟨γ, hγM, hγ⟩ := exists_conj_of_mem_conj_Nbar hNo hΩ D hxM hxτ hτN hα hcA.2 hc1
    (mem_conj_Nbar_of_mem_Abar hCE hNo hΩ D hm hsub hxM hxτ hτt hτV hτN hk hα)
  exact ⟨hcA.1, γ, hγM, hγ⟩

theorem comm_mem_Fbar_of_mem_Abar (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm : D.m = 3 ∨ D.m = 4)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hk : D.m = 3 → finrank (ZMod 2) ↥(Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) = 2)
    {α : S.O} (hα : α ∈ S.Lbar g ⊓ Nbar S g t) :
    α * τ * α⁻¹ * τ⁻¹ ∈ S9.Fbar S g t := by
  rcases comm_mem_conjL_of_mem_Abar hCE hNo hΩ D hm hsub hxM hxτ hτt hτV hτN hk hα with h | h
  · rw [h]
    exact one_mem _
  · exact subset_closure h

end CFSG.LargeExtraspecial.S8
