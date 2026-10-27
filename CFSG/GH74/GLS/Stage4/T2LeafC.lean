module

public import CFSG.GH74.GLS.Stage4.T2LeafX
public import CFSG.GH74.GLS.Stage4.T2Rodd
public import CFSG.GH74.GLS.IVK.Lifted.Out

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Hex
  CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Lifted

section Comm

variable {G : Type} [Group G]

theorem t2L_comm_cent {f f' s : G} (h : f * s = s * f) (h' : f' * s = s * f') :
    (f * f' * f⁻¹ * f'⁻¹) * s = s * (f * f' * f⁻¹ * f'⁻¹) := by
  have h1 : Commute s f := (Commute.eq h).symm
  have h2 : Commute s f' := (Commute.eq h').symm
  exact (((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right).eq.symm

end Comm

section Factor

variable {G : Type} [Group G] [Finite G]

theorem t2L_comm_factor (hC3 : T2C3) {K S : Subgroup G} {z : G} {F : Type} [Field F] [Finite F]
    (hFodd : Odd (Nat.card F)) (hF3 : 3 ≤ Nat.card F) (e : ↥K ≃* SL2 F) (hzK : z ∈ K)
    (hze : e ⟨z, hzK⟩ = negOne F) (hzc : ∀ x ∈ K, x * z = z * x) (hP : IsPGroup 2 ↥(S ⊓ K))
    (hPidx : ¬ 2 ∣ (S ⊓ K).relIndex K) {f f' : G} (hfK : ∀ x ∈ K, f * x * f⁻¹ ∈ K)
    (hfK' : ∀ x ∈ K, f' * x * f'⁻¹ ∈ K) (hfS : ∀ s ∈ S, f * s = s * f)
    (hfS' : ∀ s ∈ S, f' * s = s * f') :
    ∀ x ∈ K, (f * f' * f⁻¹ * f'⁻¹) * x = x * (f * f' * f⁻¹ * f'⁻¹) := by
  have hfn : f ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_fintype hfK
  have hfn' : f' ∈ normalizer (K : Set G) := Subgroup.mem_normalizer_fintype hfK'
  by_cases h3 : Nat.card F = 3
  · have hP' : IsPGroup 2 ↥((S ⊓ K).subgroupOf K) := hP.comap_subtype
    have hc := t2L_cent_of_q3 hC3 h3 e hP' hPidx hfK hfS
    have hc' := t2L_cent_of_q3 hC3 h3 e hP' hPidx hfK' hfS'
    intro x hx
    have h1 : Commute x f := by
      have := hc x hx
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    have h2 : Commute x f' := by
      have := hc' x hx
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    exact (((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right).eq.symm
  · have h3' : 3 < Nat.card F := lt_of_le_of_ne hF3 (Ne.symm h3)
    let c : G := f * f' * f⁻¹ * f'⁻¹
    have hcn : c ∈ normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hfn hfn') (Subgroup.inv_mem _ hfn))
        (Subgroup.inv_mem _ hfn')
    let ρ : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨f, hfn⟩
    let ρ' : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨f', hfn'⟩
    let ρc : MulAut ↥K := Subgroup.normalizerMonoidHom K ⟨c, hcn⟩
    have hρc : ρc = ρ * ρ' * ρ⁻¹ * ρ'⁻¹ := by
      have : (⟨c, hcn⟩ : ↥(normalizer (K : Set G))) =
          ⟨f, hfn⟩ * ⟨f', hfn'⟩ * ⟨f, hfn⟩⁻¹ * ⟨f', hfn'⟩⁻¹ := rfl
      show Subgroup.normalizerMonoidHom K ⟨c, hcn⟩ = _
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hρc_apply : ∀ y : ↥K, ((ρc y : ↥K) : G) = c * y * c⁻¹ := fun y => rfl
    obtain ⟨s, hs⟩ := out_abelian_sl hFodd h3' (MulAut.congr e ρ) (MulAut.congr e ρ')
    have hk : ρc = MulAut.conj (e.symm s) := by
      apply (MulAut.congr e).injective
      rw [congr_conj, MulEquiv.apply_symm_apply, hs, hρc]
      simp only [map_mul, map_inv]
    set k : ↥K := e.symm s with hkdef
    have hcS : ∀ s ∈ S, c * s = s * c := fun s hs => t2L_comm_cent (hfS s hs) (hfS' s hs)
    have hkz : (k : G) ∈ Subgroup.zpowers z := by
      refine t2C_cent_sylow_K hFodd e hP hPidx hzK hze (k : G) k.2 (fun p hp => ?_)
      have h1 : ρc ⟨p, hp.2⟩ = ⟨p, hp.2⟩ := by
        apply Subtype.ext
        rw [hρc_apply]
        have := hcS p hp.1
        calc c * p * c⁻¹ = p * c * c⁻¹ := by rw [this]
          _ = p := by group
      rw [hk] at h1
      have h2 : ((MulAut.conj k ⟨p, hp.2⟩ : ↥K) : G) = (k : G) * p * (k : G)⁻¹ := by
        simp [MulAut.conj_apply]
      have h3 := congrArg Subtype.val h1
      rw [h2] at h3
      calc (k : G) * p = ((k : G) * p * (k : G)⁻¹) * (k : G) := by group
        _ = p * (k : G) := by rw [h3]
    intro x hx
    have hkx : ∀ y : ↥K, (k : G) * (y : G) = (y : G) * (k : G) := by
      intro y
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hkz
      rw [← hn]
      have hzy : Commute z (y : G) := (hzc y y.2).symm
      exact (hzy.zpow_left n).eq
    have h4 : c * x * c⁻¹ = (k : G) * x * (k : G)⁻¹ := by
      have := congrArg (fun r : MulAut ↥K => ((r ⟨x, hx⟩ : ↥K) : G)) hk
      simpa [hρc_apply, MulAut.conj_apply] using this
    have h5 : (k : G) * x * (k : G)⁻¹ = x := by
      have := hkx ⟨x, hx⟩
      calc (k : G) * x * (k : G)⁻¹ = (x * (k : G)) * (k : G)⁻¹ := by
            rw [show (k : G) * x = x * (k : G) from this]
        _ = x := by group
    rw [h5] at h4
    calc c * x = (c * x * c⁻¹) * c := by group
      _ = x * c := by rw [h4]

end Factor

theorem ch6T2FComm_of (hC3 : T2C3) : Ch6T2FComm := by
  intro G _ _ Gs _ q₁ q₂ z K₁ K₂ F₁ F₂ _ _ t hSet hRem N u hz hK₁ hK₂ hq₁ hq₂ hLoc hCoord f f' hodd hodd'
    hfS hfS'
  have ctx := t2Ctx_of hSet hRem hLoc hz hK₁ hK₂ hq₁ hq₂
  subst hz hK₁ hK₂ hq₁ hq₂
  have := hSet.finite₁
  have := hSet.finite₂
  obtain ⟨hs₁, hs₂⟩ := t2C_sylow_inf_K hSet hRem ctx.Sctx
  obtain ⟨⟨e₁, hze₁⟩, ⟨e₂, hze₂⟩⟩ := t2C_coords hSet
  have hfz : f * N.z = N.z * f := hfS N.z hLoc.z_mem_S
  have hfz' : f' * N.z = N.z * f' := hfS' N.z hLoc.z_mem_S
  obtain ⟨hfn₁, hfn₂⟩ := t2Ctx_odd_normK ctx hfz hodd
  obtain ⟨hfn₁', hfn₂'⟩ := t2Ctx_odd_normK ctx hfz' hodd'
  obtain ⟨hFodd, hFall, -⟩ := t2C_cent_structure ctx.Sctx.S2 ctx.Sctx.Sidx ctx.Sctx.Sz ctx.Sctx.zS
    ctx.zz ctx.ZS
    (F := (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map (centralizer (N.S : Set G)).subtype) rfl
  set F : Subgroup G := (pPrimeCore 2 ↥(centralizer (N.S : Set G))).map
    (centralizer (N.S : Set G)).subtype with hFdef
  have hfF : f ∈ F := hFall f (Subgroup.mem_centralizer_iff.2 (fun s hs => (hfS s hs).symm)) hodd
  have hfF' : f' ∈ F := hFall f' (Subgroup.mem_centralizer_iff.2 (fun s hs => (hfS' s hs).symm)) hodd'
  have hcF : f * f' * f⁻¹ * f'⁻¹ ∈ F :=
    F.mul_mem (F.mul_mem (F.mul_mem hfF hfF') (F.inv_mem hfF)) (F.inv_mem hfF')
  have hcodd : Odd (orderOf (f * f' * f⁻¹ * f'⁻¹)) := (hFodd _ hcF).1
  have hcz : (f * f' * f⁻¹ * f'⁻¹) * N.z = N.z * (f * f' * f⁻¹ * f'⁻¹) :=
    t2L_comm_cent (hfS _ hLoc.z_mem_S) (hfS' _ hLoc.z_mem_S)
  have hcC : f * f' * f⁻¹ * f'⁻¹ ∈ centralizer ({N.z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcz
  have hP₁ : IsPGroup 2 ↥(N.S ⊓ N.K₁) := ctx.Sctx.S2.to_le inf_le_left
  have hP₂ : IsPGroup 2 ↥(N.S ⊓ N.K₂) := ctx.Sctx.S2.to_le inf_le_left
  have hc₁ := t2L_comm_factor hC3 (F := F₁) (by rw [hSet.card₁]; exact hSet.odd₁)
    (by rw [hSet.card₁]; have := hSet.five; omega) e₁ hSet.z_mem₁ hze₁ ctx.C.zc₁ hP₁ hs₁ hfn₁
    hfn₁' hfS hfS'
  have hc₂ := t2L_comm_factor hC3 (F := F₂) (by rw [hSet.card₂]; exact hSet.odd₂)
    (by rw [hSet.card₂]; have := hLoc.q₂_ge; omega) e₂ hSet.z_mem₂ hze₂ ctx.C.zc₂ hP₂ hs₂ hfn₂
    hfn₂' hfS hfS'
  have hcK : ∀ x ∈ N.K₁ ⊔ N.K₂, (f * f' * f⁻¹ * f'⁻¹) * x = x * (f * f' * f⁻¹ * f'⁻¹) := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_comm hSet.comm x).1 hx
    have h1 := hc₁ a ha
    have h2 := hc₂ b hb
    calc (f * f' * f⁻¹ * f'⁻¹) * (a * b) = ((f * f' * f⁻¹ * f'⁻¹) * a) * b := by group
      _ = (a * (f * f' * f⁻¹ * f'⁻¹)) * b := by rw [h1]
      _ = a * ((f * f' * f⁻¹ * f'⁻¹) * b) := by group
      _ = a * (b * (f * f' * f⁻¹ * f'⁻¹)) := by rw [h2]
      _ = (a * b) * (f * f' * f⁻¹ * f'⁻¹) := by group
  have hc1 : f * f' * f⁻¹ * f'⁻¹ = 1 := t2C_R_odd_trivial hSet hRem ctx _ hcC hcodd hcK
  calc f * f' = (f * f' * f⁻¹ * f'⁻¹) * f' * f := by group
    _ = f' * f := by rw [hc1]; group

end CFSG.GH74.GLS.Stage4.Rest
