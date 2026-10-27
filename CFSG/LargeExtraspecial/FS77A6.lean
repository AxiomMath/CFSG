module

public import CFSG.LargeExtraspecial.FS77A5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.FS77

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace CaseA

structure Good (D : CaseA S) where
  y : G
  hy : D.IsCycle y
  e : ℕ
  he : orderOf y = 3 ^ e
  hcen : ∀ m : D.X, D.ρN (hy.isTwist.σ m) = D.ρN m

theorem exists_good (D : CaseA S) : Nonempty D.Good := by
  obtain ⟨y, hy, ⟨e, he⟩, hc⟩ := D.exists_cycle_centralizing
  refine ⟨⟨y, hy, e, he, fun m => ?_⟩⟩
  obtain ⟨h, hm⟩ := hc m
  exact hm

variable {D : CaseA S} (Y : D.Good)

namespace Good

theorem phiLin_eq_id {w : G} (hw : D.IsTwist w) (hc : ∀ m : D.X, D.ρN (hw.σ m) = D.ρN m) :
    hw.phiLin = LinearMap.id := by
  rcases D.eq_zero_or_id hw.phiLin (fun m v => by rw [hw.phi_ρN, hc]) with h | h
  · exfalso
    have := D.nontrivial_N
    obtain ⟨v, hv⟩ := exists_ne (0 : D.N)
    exact hv (hw.phiLin_injective (by rw [h, map_zero]; rfl))
  · exact h

theorem ψ_conj_of {w : G} (hw : D.IsTwist w) (hc : ∀ m : D.X, D.ρN (hw.σ m) = D.ρN m)
    (c : D.CQa) : D.ψ (D.L0toX hw.isAorAZ (hw.conjHom c)) = D.projN (S.cl c) := by
  rw [← hw.Φ_apply, hw.Φ_eq_phi, ← hw.phiLin_apply, phiLin_eq_id hw hc, LinearMap.id_apply]

theorem hcen_inv (m : D.X) : D.ρN (Y.hy.inv_isTwist.σ m) = D.ρN m := by
  have h := Y.hcen (Y.hy.inv_isTwist.σ m)
  have e : Y.hy.isTwist.σ (Y.hy.inv_isTwist.σ m) = m := Subtype.ext (by
    change Y.y * (Y.y⁻¹ * m * Y.y⁻¹⁻¹) * Y.y⁻¹ = m
    group)
  rw [e] at h
  exact h.symm

theorem ψ_conj_y (c : D.CQa) :
    D.ψ (D.L0toX Y.hy.isTwist.isAorAZ (Y.hy.isTwist.conjHom c)) = D.projN (S.cl c) :=
  ψ_conj_of Y.hy.isTwist Y.hcen c

theorem ψ_conj_yinv (c : D.CQa) :
    D.ψ (D.L0toX Y.hy.inv_isTwist.isAorAZ (Y.hy.inv_isTwist.conjHom c)) =
      D.projN (S.cl c) :=
  ψ_conj_of Y.hy.inv_isTwist Y.hcen_inv c

theorem y_pow_three : Y.y ^ 3 = 1 := by
  set y3 : D.X := ⟨Y.y ^ 3, Y.hy.pow_three_mem_X D⟩ with hy3
  have hcomm : ∀ m : D.X, D.ρN y3 * D.ρN m = D.ρN m * D.ρN y3 := by
    intro m
    obtain ⟨h, hm⟩ := Y.hy.pow_centralizing Y.hcen 3 m
    have e : (⟨Y.y ^ 3 * m * (Y.y ^ 3)⁻¹, h⟩ : D.X) = y3 * m * y3⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hm
    exact mul_inv_eq_iff_eq_mul.mp hm
  have hθ : ∀ m : D.X, ∀ v, ((D.ρN y3 : D.N ≃ₗ[ZMod 2] D.N) : D.N →ₗ[ZMod 2] D.N) (D.ρN m v) =
      D.ρN m (((D.ρN y3 : D.N ≃ₗ[ZMod 2] D.N) : D.N →ₗ[ZMod 2] D.N) v) := fun m v => by
    have := congrArg (fun f : D.N ≃ₗ[ZMod 2] D.N => f v) (hcomm m)
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_coe] using this
  have hK : y3 ∈ D.K := by
    rcases D.eq_zero_or_id _ hθ with h | h
    · exfalso
      have := D.nontrivial_N
      obtain ⟨v, hv⟩ := exists_ne (0 : D.N)
      apply hv
      apply (D.ρN y3).injective
      have h1 := LinearMap.congr_fun h v
      rw [LinearEquiv.coe_coe] at h1
      rw [h1, map_zero]
      rfl
    · exact D.mem_K.mpr (LinearEquiv.ext fun v => LinearMap.congr_fun h v)
  obtain ⟨n, hn⟩ := D.isPGroup_K ⟨y3, hK⟩
  have hn' : (Y.y ^ 3) ^ 2 ^ n = 1 := by
    have := congrArg (fun x : D.K => ((x : D.X) : G)) hn
    simpa using this
  have h1 : orderOf (Y.y ^ 3) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have h2 : orderOf (Y.y ^ 3) ∣ 3 ^ Y.e := by
    rw [← Y.he]
    exact orderOf_pow_dvd 3
  have h3 : Nat.Coprime (2 ^ n) (3 ^ Y.e) := Nat.Coprime.pow _ _ (by norm_num)
  have h4 : orderOf (Y.y ^ 3) = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.mp h4

theorem y_sq : Y.y ^ 2 = Y.y⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, Y.y_pow_three]

@[expose] noncomputable def KG (D : CaseA S) : Subgroup G := D.K.map D.X.subtype

theorem mem_KG {x : G} : x ∈ KG D ↔ ∃ h : x ∈ D.X, (⟨x, h⟩ : D.X) ∈ D.K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hk⟩
    exact ⟨⟨x, h⟩, hk, rfl⟩

theorem isPGroup_KG (D : CaseA S) : IsPGroup 2 (KG D) := by
  intro k
  obtain ⟨h, hk⟩ := mem_KG.mp k.2
  obtain ⟨n, hn⟩ := D.isPGroup_K ⟨⟨k, h⟩, hk⟩
  refine ⟨n, Subtype.ext ?_⟩
  have := congrArg (fun x : D.K => ((x : D.X) : G)) hn
  simpa using this

theorem exists_lift (m : D.X) : ∃ l : D.X, Y.y * l * Y.y⁻¹ = l ∧ D.ρN l = D.ρN m := by
  have hyK : ∀ k ∈ KG D, Y.y * k * Y.y⁻¹ ∈ KG D := by
    intro k hk
    obtain ⟨h, hk⟩ := mem_KG.mp hk
    refine mem_KG.mpr ⟨Y.hy.isTwist.conj_mem_X h, ?_⟩
    have := Y.hcen ⟨k, h⟩
    rw [D.mem_K] at hk ⊢
    rw [← hk, ← this]
    rfl
  have hym : Y.y * m * Y.y⁻¹ * (m : G)⁻¹ ∈ KG D := by
    refine mem_KG.mpr ⟨mul_mem (Y.hy.isTwist.conj_mem_X m.2) (inv_mem m.2), ?_⟩
    rw [D.mem_K]
    have e : (⟨Y.y * m * Y.y⁻¹ * (m : G)⁻¹, mul_mem (Y.hy.isTwist.conj_mem_X m.2)
        (inv_mem m.2)⟩ : D.X) = Y.hy.isTwist.σ m * m⁻¹ := rfl
    rw [e, map_mul, Y.hcen, map_inv, mul_inv_cancel]
  obtain ⟨k, hk, hkm⟩ := exists_commute_mul_of_isPGroup (isPGroup_KG D) Y.he hyK hym
  obtain ⟨h, hkK⟩ := mem_KG.mp hk
  refine ⟨⟨k, h⟩ * m, hkm, ?_⟩
  rw [map_mul, D.mem_K.mp hkK, one_mul]

omit [Finite G] in
theorem conj_mem_QG_of_mem_Qa {w x : G} (hx : x ∈ S.Qa w) : w⁻¹ * x * w ∈ S.QG := by
  rw [Setting.Qa_eq_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have e : w⁻¹ * ((MulAut.conj w).toMonoidHom q) * w = q := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hq

theorem eq_one_of_mem_K {f : D.X} (hf : f ∈ D.K) (hfy : Y.y * f * Y.y⁻¹ = f) : f = 1 := by
  have hT := Y.hy.isTwist
  have hT' := Y.hy.inv_isTwist
  set v := D.ψ f with hv
  set c := D.liftN v with hc
  have hpc : D.projN (S.cl (c : G)) = v := Subtype.ext (D.proj_cl_liftN v)
  set d : D.X := D.L0toX hT.isAorAZ (hT.conjHom c) with hd
  have hdK : d ∈ D.K := D.L0toX_mem_K _ _
  have hψd : D.ψ d = v := by rw [hd, ψ_conj_y, hpc]
  set d' : D.X := D.L0toX hT'.isAorAZ (hT'.conjHom c) with hd'
  have hd'K : d' ∈ D.K := D.L0toX_mem_K _ _
  have hψd' : D.ψ d' = v := by rw [hd', ψ_conj_yinv, hpc]
  set k : D.X := f * d⁻¹ with hk
  have hkK : k ∈ D.K := mul_mem hf (inv_mem hdK)
  have hψk : D.ψ k = 0 := by
    have h1 := D.ψ_mul hkK hdK
    rw [hk, inv_mul_cancel_right, ← hv, hψd] at h1
    exact (add_eq_right.mp h1.symm)
  have hkQ : (k : G) ∈ S.QG := (D.ψ_eq_zero_iff hkK).mp hψk
  have hσk : hT.σ k = f * d'⁻¹ := by
    apply Subtype.ext
    change Y.y * ((f : G) * (d : G)⁻¹) * Y.y⁻¹ = (f : G) * (d' : G)⁻¹
    have e1 : (d : G) = Y.y * c * Y.y⁻¹ := rfl
    have e2 : (d' : G) = Y.y⁻¹ * c * Y.y⁻¹⁻¹ := rfl
    have hy2 := Y.y_sq
    calc Y.y * ((f : G) * (d : G)⁻¹) * Y.y⁻¹
        = (Y.y * f * Y.y⁻¹) * (Y.y ^ 2 * c * (Y.y ^ 2)⁻¹)⁻¹ := by rw [e1]; group
      _ = (f : G) * (d' : G)⁻¹ := by rw [hfy, hy2, e2]
  have hσkK : f * d'⁻¹ ∈ D.K := mul_mem hf (inv_mem hd'K)
  have hψσk : D.ψ (f * d'⁻¹) = 0 := by
    have h1 := D.ψ_mul hσkK hd'K
    rw [inv_mul_cancel_right, ← hv, hψd'] at h1
    exact (add_eq_right.mp h1.symm)
  have hykQ : Y.y * (k : G) * Y.y⁻¹ ∈ S.QG := by
    have := (D.ψ_eq_zero_iff hσkK).mp hψσk
    rw [← hσk] at this
    exact this
  have hkW : (k : G) ∈ S.QG ⊓ S.Qa Y.y⁻¹ := by
    refine ⟨hkQ, ?_⟩
    rw [Setting.Qa_eq_map]
    exact ⟨_, hykQ, by simp; group⟩
  rw [D.mem_QG_inf_Qa_iff hT'.isAorAZ] at hkW
  obtain ⟨hz, ha, haz⟩ := D.four_mem_QG_inf_Qa hT.isAorAZ
  have hkQa : (k : G) ∈ S.Qa Y.y := by
    rcases hkW with h | h | h | h <;> rw [h]
    exacts [one_mem _, hz.2, ha.2, haz.2]
  have hdQa : (d : G) ∈ S.Qa Y.y := (hT.conj_mem_L0 c.2).1
  have hfQa : (f : G) ∈ S.Qa Y.y := by
    have : (f : G) = k * d := by rw [hk]; simp
    rw [this]
    exact mul_mem hkQa hdQa
  have hfQ : (f : G) ∈ S.QG := by
    have e : (f : G) = Y.y⁻¹ * f * Y.y := by
      calc (f : G) = Y.y⁻¹ * (Y.y * f * Y.y⁻¹) * Y.y := by group
        _ = Y.y⁻¹ * f * Y.y := by rw [hfy]
    rw [e]
    exact conj_mem_QG_of_mem_Qa hfQa
  have hfW : (f : G) ∈ S.QG ⊓ S.Qa Y.y := ⟨hfQ, hfQa⟩
  rw [D.mem_QG_inf_Qa_iff hT.isAorAZ] at hfW
  apply Subtype.ext
  rcases hfW with h | h | h | h
  · exact h
  · exfalso
    rw [h, Y.hy.1] at hfy
    exact D.az_ne_z hfy
  · exfalso
    rw [h, Y.hy.2] at hfy
    exact D.a_ne_z hfy.symm
  · exfalso
    rw [h, Y.hy.conj_az D] at hfy
    exact D.az_ne_a hfy.symm

theorem eq_of_ρN_eq {l₁ l₂ : D.X} (h₁ : Y.y * l₁ * Y.y⁻¹ = l₁) (h₂ : Y.y * l₂ * Y.y⁻¹ = l₂)
    (h : D.ρN l₁ = D.ρN l₂) : l₁ = l₂ := by
  have hK : l₁⁻¹ * l₂ ∈ D.K := by
    rw [D.mem_K, map_mul, map_inv, h, inv_mul_cancel]
  have hy : Y.y * ((l₁⁻¹ * l₂ : D.X) : G) * Y.y⁻¹ = ((l₁⁻¹ * l₂ : D.X) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc Y.y * ((l₁ : G)⁻¹ * l₂) * Y.y⁻¹ = (Y.y * l₁ * Y.y⁻¹)⁻¹ * (Y.y * l₂ * Y.y⁻¹) := by group
      _ = (l₁ : G)⁻¹ * l₂ := by rw [h₁, h₂]
  have := Y.eq_one_of_mem_K hK hy
  rw [inv_mul_eq_one] at this
  exact this

end Good

end CaseA

end CFSG.LargeExtraspecial.FS77
