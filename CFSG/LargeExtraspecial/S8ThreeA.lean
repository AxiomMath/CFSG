module

public import CFSG.LargeExtraspecial.S7Lin
public import CFSG.LargeExtraspecial.S8DimA
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Rad
public import CFSG.LargeExtraspecial.S8Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

section Lin

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_commSpace_mul_ge (f g : V ≃ₗ[K] V) (hfg : commSpace g ≤ fixSpace f) :
    finrank K (commSpace f) + finrank K ((fixSpace f).map ((g : V →ₗ[K] V) - 1)) ≤
      finrank K (commSpace (f * g)) +
        finrank K (commSpace f ⊓ commSpace g : Submodule K V) := by
  obtain ⟨A, hA⟩ : ∃ A : V →ₗ[K] V, A = (f : V →ₗ[K] V) - 1 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : V →ₗ[K] V, B = (g : V →ₗ[K] V) - 1 := ⟨_, rfl⟩
  have hAB : (((f * g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) = A + B := by
    ext v
    have h1 : g v - v ∈ fixSpace f := hfg (sub_mem_commSpace g v)
    rw [mem_fixSpace, map_sub] at h1
    rw [hA, hB]
    change f (g v) - v = (f v - v) + (g v - v)
    calc f (g v) - v = (f (g v) - f v) + (f v - v) := by abel
      _ = (g v - v) + (f v - v) := by rw [h1]
      _ = (f v - v) + (g v - v) := by abel
  have hcf : commSpace f = LinearMap.range A := by rw [hA]
  have hcg : commSpace g = LinearMap.range B := by rw [hB]
  have hff : fixSpace f = LinearMap.ker A := by rw [hA]
  have hcfg : commSpace (f * g) = LinearMap.range (A + B) := by
    change LinearMap.range (((f * g : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) = _
    rw [hAB]
  rw [hcf, hcg, hff, hcfg, ← hB]
  have hk1 : LinearMap.ker (A + B) ⊓ LinearMap.ker A ≤ LinearMap.ker A ⊓ LinearMap.ker B := by
    intro v hv
    rw [Submodule.mem_inf] at hv ⊢
    obtain ⟨h1, h2⟩ := hv
    refine ⟨h2, ?_⟩
    have h1' : (A + B) v = 0 := h1
    have h2' : A v = 0 := h2
    rw [LinearMap.add_apply, h2', zero_add] at h1'
    exact h1'
  have hk2 : (LinearMap.ker (A + B)).map A ≤ LinearMap.range A ⊓ LinearMap.range B := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨⟨v, rfl⟩, ⟨-v, ?_⟩⟩
    have hv' : (A + B) v = 0 := hv
    rw [LinearMap.add_apply] at hv'
    rw [map_neg, eq_neg_of_add_eq_zero_right hv', neg_neg]
  have e1 := finrank_map_add_finrank_inf_ker A (LinearMap.ker (A + B))
  have e2 := finrank_map_add_finrank_inf_ker B (LinearMap.ker A)
  have e3 := LinearMap.finrank_range_add_finrank_ker A
  have e4 := LinearMap.finrank_range_add_finrank_ker (A + B)
  have i1 := Submodule.finrank_mono hk1
  have i2 := Submodule.finrank_mono hk2
  have e5 : LinearMap.ker A ⊓ LinearMap.ker B = (LinearMap.ker A ⊓ LinearMap.ker B :
      Submodule K V) := rfl
  omega

end Lin

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem finrank_map_Wt_add {t : S.O} (τ : S.O) :
    finrank (ZMod 2) ((Wt S g t).map (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) +
      finrank (ZMod 2) (Vt S g t ⊓ commSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
        Submodule (ZMod 2) S.Qt) =
      finrank (ZMod 2) (commSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  have hfix := fixSpace_eq_orthogonal_commSpace_of_mem S.q_nondegenerate τ.2
  have e1 := finrank_map_add_finrank_inf_ker
    (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) (Wt S g t)
  have e2 : Wt S g t ⊓ LinearMap.ker (((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
      S2.perp S.q (Vt S g t ⊔ commSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    rw [perp_sup]
    change Wt S g t ⊓ fixSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) = _
    rw [hfix]
    rfl
  rw [e2] at e1
  have e3 := finrank_perp S.q_nondegenerate
    (Vt S g t ⊔ commSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have e4 := finrank_perp S.q_nondegenerate (Vt S g t)
  have e5 := Submodule.finrank_sup_add_finrank_inf_eq (Vt S g t)
    (commSpace ((τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
  have e6 : Wt S g t = S2.perp S.q (Vt S g t) := rfl
  rw [← e6] at e4
  omega

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem ne_conj_mul_of_fix (H : Hyp4 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hVQ : ¬ V S g t ≤ S.Qa g) {τ : S.O}
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hdim : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t))
    (hk : 2 * finrank (ZMod 2) (Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :
      Submodule (ZMod 2) S.Qt) < finrank (ZMod 2) (Vt S g t)) (y : S.O) :
    y * t * y⁻¹ ≠ t * τ := by
  intro hy
  obtain ⟨hct, hft⟩ := commSpace_t_eq H C ht ht1 hVQ
  have hle : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [hft]; exact commSpace_le_Wt_of_fix hτV
  have h1 := finrank_commSpace_mul_ge (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) hle
  rw [hct, hft] at h1
  have h2 := finrank_map_Wt_add (g := g) (t := t) τ
  have h3 : finrank (ZMod 2) (commSpace ((t * τ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [← hy, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj', hct]
  rw [Subgroup.coe_mul] at h3
  omega

theorem finrank_Vt_inf_le_two (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹) (hτN : τ ∉ Nbar S g t) :
    finrank (ZMod 2) (Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) :
      Submodule (ZMod 2) S.Qt) ≤ 2 := by
  have hanis := not_mem_orbit_of_not_mem_Nbar H C ht ht1 hVQ hfus hsub hxM hxτ hτN
  obtain ⟨W', hW'⟩ : ∃ W' : Submodule (ZMod 2) (Vt S g t),
      W' = (Vt S g t ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).comap (Vt S g t).subtype :=
    ⟨_, rfl⟩
  have hfin : finrank (ZMod 2) W' = finrank (ZMod 2) (Vt S g t ⊓
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) : Submodule (ZMod 2) S.Qt) := by
    rw [hW']
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe inf_le_left)
  rw [← hfin]
  refine S7.finrank_le_two_of_anisotropic D.Q fun w hw hQw => ?_
  by_contra hw0
  rw [hW'] at hw
  have horb := (D.hsing w hw0).mp hQw
  rw [mem_orbitOf_RmodN_iff H.conj_mem ht] at horb
  exact hanis _ hw horb

theorem mem_normalizer_Lbar_of_fix (H : Hyp4 S g) (ht : t ∈ S.Lbar g) {τ : S.O}
    (hτM : τ ∈ S.Mbar) (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    τ ∈ normalizer (S.Lbar g : Set S.O) := by
  have h := mem_normalizer_of_fix H.conj_mem H.conj_ne (h := 1) hτM (by
    simp only [OneMemClass.coe_one, one_mul]
    exact hτV _ (cl_a_mem_Vt ht))
  simpa only [OneMemClass.coe_one, one_mul] using h

theorem false_of_comm_Nbar (D : Std H C ht ht1 hVQ)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hcN : ∀ n ∈ Nbar S g t, n * τ = τ * n) : False := by
  have hconjN : ∀ {k : S.M}, S.ρ k ∈ Rbar S g t → ∀ n ∈ Nbar S g t,
      S.ρ k * n * (S.ρ k)⁻¹ ∈ Nbar S g t := fun {k} hk n hn =>
    conj_mem_Nbar H.conj_mem (commute_of_mem_Rbar H.conj_mem hk) hn
  have hα : ∀ k : S.M, S.ρ k ∈ Rbar S g t → τ ∉ S.Lbar ((k : G) * g) ⊓ Nbar S g t :=
    fun _ _ h => hτN h.2
  have hV1W := commSpace_le_Wt_of_fix (g := g) hτV
  have hanis := not_mem_orbit_of_fusion_beta H C ht ht1 hVQ hfus hxM hxτ hτV hα
  obtain ⟨d₀, hd₀, hd⟩ := exists_center_of_fusion_beta H C ht ht1 hVQ D.hQ D.hsing hfus D.hN
    D.hNsq hxM hxτ hcN hV1W hanis
  obtain ⟨k, hk, hkfix⟩ := exists_Abar_fix_of_fusion_beta H C ht ht1 hVQ hV1W hd₀ hd
  obtain ⟨r, hr⟩ : ∃ r, r = S.ρ k := ⟨_, rfl⟩
  have hkR : r ∈ Rbar S g t := hr ▸ hk
  have hV1eq : commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (Vt S g t).map (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [hxτ, commSpace_conj, (commSpace_t_eq H C ht ht1 hVQ).1]
  have hV1' : commSpace ((r⁻¹ * τ * r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)).map
        ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap := by
    rw [← commSpace_conj, inv_inv]
  refine false_of_fusion_beta H C ht ht1 hVQ D.hA D.hN D.hh D.hb D.hPab (τ := r⁻¹ * τ * r)
    (fun v hv => ?_) ?_ (fun n hn => ?_) ?_ ?_
  · change ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((τ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v)) = v
    rw [hτV _ (apply_mem_Vt_of_mem_Rbar H.conj_mem hkR hv), inv_apply_apply_O]
  · rw [hV1', LinearEquiv.finrank_map_eq, hV1eq, LinearEquiv.finrank_map_eq]
  · have h1 := hcN _ (hr ▸ hconjN hk n hn)
    calc n * (r⁻¹ * τ * r) = r⁻¹ * ((r * n * r⁻¹) * τ) * r := by group
      _ = r⁻¹ * (τ * (r * n * r⁻¹)) * r := by rw [h1]
      _ = r⁻¹ * τ * r * n := by group
  · rintro d ⟨hdV, hdτ⟩ hdorb
    rw [hV1'] at hdτ
    obtain ⟨w, hw, rfl⟩ := hdτ
    have hrw : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = w :=
      apply_inv_apply_O r w
    have h1 := apply_mem_Vt_of_mem_Rbar H.conj_mem hkR hdV
    have h2 := apply_mem_orbit hkR hdorb
    change (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) ∈ _ at h1 h2
    rw [hrw] at h1 h2
    exact hanis w ⟨h1, hw⟩ h2
  · intro α hα w hw
    rw [hV1'] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have hα' : r * α * r⁻¹ ∈ S.Lbar ((k : G) * g) ⊓ Nbar S g t := by
      refine ⟨?_, hr ▸ hconjN hk α hα.2⟩
      rw [hr]
      exact conj_mem_Lbar_mul S k hα.1
    have h1 := hkfix _ hα' w' hw'
    change ((r * α * r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w' = w' at h1
    change (α : S.Qt ≃ₗ[ZMod 2] S.Qt) (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w') =
      ((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w'
    have e : ((r * α * r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w' =
        (r : S.Qt ≃ₗ[ZMod 2] S.Qt) ((α : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w')) := rfl
    rw [e] at h1
    have h2 := congrArg (((r⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h1
    rwa [inv_apply_apply_O] at h2

theorem false_of_comm_mem_zpowers (D : Std H C ht ht1 hVQ) (hm3 : 3 ≤ D.m)
    (hfus : ∀ k : S.M, S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ Vt S g t →
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ orbit S g t)
    (hsub : ∀ x ∈ S.Mbar, x * t * x⁻¹ ∈ S.Lbar g → x * t * x⁻¹ ∈ Nbar S g t)
    {x τ : S.O} (hxM : x ∈ S.Mbar) (hxτ : τ = x * t * x⁻¹)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) (hτN : τ ∉ Nbar S g t)
    (hcomm : ∀ n ∈ Nbar S g t, n * τ * n⁻¹ * τ⁻¹ ∈ zpowers t) : False := by
  have htt : t * t = 1 := mul_self_of_mem_Lbar S H.conj_mem ht
  have hk := finrank_Vt_inf_le_two D hfus hsub hxM hxτ hτN
  have hdimV := D.hdim
  have hdimτ : finrank (ZMod 2) (commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      finrank (ZMod 2) (Vt S g t) := by
    rw [hxτ, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj',
      (commSpace_t_eq H C ht ht1 hVQ).1]
  have hne := ne_conj_mul_of_fix H C ht ht1 hVQ hτV hdimτ (by omega)
  refine false_of_comm_Nbar D hfus hxM hxτ hτV hτN fun n hn => ?_
  rcases eq_one_or_eq_of_mem_zpowers htt (hcomm n hn) with h | h
  · calc n * τ = (n * τ * n⁻¹ * τ⁻¹) * (τ * n) := by group
      _ = τ * n := by rw [h, one_mul]
  · exfalso
    apply hne (n * x)
    calc n * x * t * (n * x)⁻¹ = n * τ * n⁻¹ := by rw [hxτ]; group
      _ = (n * τ * n⁻¹ * τ⁻¹) * τ := by group
      _ = t * τ := by rw [h]

end CFSG.LargeExtraspecial.S8
