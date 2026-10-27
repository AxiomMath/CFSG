module

public import CFSG.Holt.H78.Data
import CFSG.Holt.H78.Conjugacy
import CFSG.Holt.H78.SEModelFive
public import CFSG.Holt.H78.Dihedral

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General Equiv
open scoped Pointwise

section Dihedral

variable {X : Type*} [Group X]

theorem conj_eq_inv_of_mem_zpowers_mul {τ ξ z : X} (hτ : τ * τ = 1) (hξ : ξ * ξ = 1)
    (hz : z ∈ Subgroup.zpowers (τ * ξ)) : τ * z * τ⁻¹ = z⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ
  have h1 : MulAut.conj τ (τ * ξ) = (τ * ξ)⁻¹ := by
    rw [MulAut.conj_apply, mul_inv_rev, hτi, hξi, ← mul_assoc, hτ, one_mul]
  calc τ * (τ * ξ) ^ k * τ⁻¹ = MulAut.conj τ ((τ * ξ) ^ k) := rfl
    _ = ((τ * ξ) ^ k)⁻¹ := by rw [map_zpow, h1, inv_zpow]

theorem mem_zpowers_or_mul_mem_zpowers_of_mem_closure {τ ξ g : X} (hτ : τ * τ = 1)
    (hξ : ξ * ξ = 1) (hg : g ∈ Subgroup.closure {τ, ξ}) :
    g ∈ Subgroup.zpowers (τ * ξ) ∨ g * τ ∈ Subgroup.zpowers (τ * ξ) := by
  set Z := Subgroup.zpowers (τ * ξ)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hconj : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z := fun z hz => by
    rw [conj_eq_inv_of_mem_zpowers_mul hτ hξ hz]
    exact inv_mem hz
  have hconj' : ∀ z ∈ Z, τ⁻¹ * z * τ ∈ Z := fun z hz => by
    simpa only [hτi] using hconj z hz
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (by rw [hτ]; exact one_mem Z)
    · refine Or.inr ?_
      have : x * τ = (τ * x)⁻¹ := by
        rw [mul_inv_rev, hτi, inv_eq_of_mul_eq_one_right hξ]
      rw [this]
      exact inv_mem (Subgroup.mem_zpowers _)
  | one => exact Or.inl (one_mem Z)
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (mul_mem hx hy)
    · exact Or.inr (by rw [mul_assoc]; exact mul_mem hx hy)
    · refine Or.inr ?_
      have : x * y * τ = x * τ * (τ⁻¹ * y * τ) := by group
      rw [this]
      exact mul_mem hx (hconj' y hy)
    · refine Or.inl ?_
      have : x * y = x * τ * (τ⁻¹ * (y * τ) * τ) := by
        calc x * y = x * y * (τ * τ) := by rw [hτ, mul_one]
          _ = x * τ * (τ⁻¹ * (y * τ) * τ) := by group
      rw [this]
      exact mul_mem hx (hconj' _ hy)
  | inv x _ hx =>
    rcases hx with hx | hx
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ?_
      have : x⁻¹ * τ = τ * (x * τ)⁻¹ * τ⁻¹ := by
        rw [mul_inv_rev, hτi, ← mul_assoc, hτ, one_mul]
      rw [this]
      exact hconj _ (inv_mem hx)

theorem mul_conj_mem_zpowers_of_mem_closure {τ ξ g : X} (hτ : τ * τ = 1) (hξ : ξ * ξ = 1)
    (hg : g ∈ Subgroup.closure {τ, ξ}) : ξ * (g * τ * g⁻¹) ∈ Subgroup.zpowers (τ * ξ) := by
  set Z := Subgroup.zpowers (τ * ξ)
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have key : ∀ w ∈ Z, ξ * (w * w * τ) ∈ Z := fun w hw => by
    have h1 : ξ * (w * w * τ) = τ * ((τ * ξ) * w * w) * τ⁻¹ := by
      rw [hτi]
      calc ξ * (w * w * τ) = (τ * τ) * ξ * (w * w * τ) := by rw [hτ, one_mul]
        _ = τ * ((τ * ξ) * w * w) * τ := by group
    rw [h1, conj_eq_inv_of_mem_zpowers_mul hτ hξ
      (mul_mem (mul_mem (Subgroup.mem_zpowers _) hw) hw)]
    exact inv_mem (mul_mem (mul_mem (Subgroup.mem_zpowers _) hw) hw)
  rcases mem_zpowers_or_mul_mem_zpowers_of_mem_closure hτ hξ hg with h | h
  · have h1 : g * τ * g⁻¹ = g * g * τ := by
      have h2 := conj_eq_inv_of_mem_zpowers_mul hτ hξ (inv_mem h)
      rw [inv_inv] at h2
      calc g * τ * g⁻¹ = g * (τ * g⁻¹ * τ⁻¹) * τ := by group
        _ = g * g * τ := by rw [h2]
    rw [h1]
    exact key g h
  · have h1 : g * τ * g⁻¹ = (g * τ) * (g * τ) * τ := by
      have h2 := conj_eq_inv_of_mem_zpowers_mul hτ hξ (inv_mem h)
      rw [inv_inv] at h2
      calc g * τ * g⁻¹ = (g * τ) * (τ * (g * τ)⁻¹ * τ⁻¹) * τ := by group
        _ = (g * τ) * (g * τ) * τ := by rw [h2]
    rw [h1]
    exact key _ h

end Dihedral

section Factor

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {M N : Subgroup (Perm Δ)}

theorem IsHoltFactor.exists_mem_conj_eq (hM : IsHoltFactor M) (hNM : ¬ IsOuterFactor M → N ≤ M)
    {σ τ : Perm Δ} (hσN : σ ∈ N) (hσ : σ ∈ longInv (Perm Δ) Δ) (hτN : τ ∈ N)
    (hτ : τ ∈ longInv (Perm Δ) Δ) : ∃ g ∈ M, g * σ * g⁻¹ = τ := by
  by_cases hAlt : M = alternatingGroup Δ
  · obtain ⟨g, hg, hgστ⟩ := exists_mem_alternatingGroup_conj_eq hσ hτ
    exact ⟨g, hAlt ▸ hg, hgστ⟩
  have hNM' := hNM fun h => hAlt h.1
  have hSE : IsNaturalSE M := hM.resolve_left fun h => hAlt h.1
  obtain ⟨c, hc⟩ := isConj_iff.mp (hSE.isConj (x := ⟨σ, hNM' hσN⟩) (y := ⟨τ, hNM' hτN⟩)
    (by rw [Subgroup.orderOf_mk]; exact hσ.1) (by rw [Subgroup.orderOf_mk]; exact hτ.1))
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

omit [Fintype Δ] in
theorem conj_swap_mul_eq_swap_mul_swap {ξ : Perm Δ} {a C : Δ} (hξ2 : ξ * ξ = 1) (hC : ξ C = C) :
    swap a C * ξ * (swap a C)⁻¹ * ξ = swap a C * swap (ξ a) C := by
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ2
  calc swap a C * ξ * (swap a C)⁻¹ * ξ = swap a C * (ξ * swap a C * ξ⁻¹) := by
        rw [swap_inv, hξi]; group
    _ = swap a C * swap (ξ a) C := by rw [← swap_apply_apply, hC]

theorem IsHoltFactor.exists_mem_longInvAt_zpowers_eq_one (hM : IsHoltFactor M) (hMN : M ≤ N)
    (hNM : ¬ IsOuterFactor M → N ≤ M) {ξ : Perm Δ} (hξN : ξ ∈ N) (hξ : ξ ∈ longInv (Perm Δ) Δ)
    (a : Δ) : ∃ τ ∈ N, τ ∈ longInvAt (Perm Δ) Δ a ∧
      ∀ g ∈ Subgroup.zpowers (τ * ξ), g a = a → g = 1 := by
  have hξ2 : ξ * ξ = 1 := mul_self_eq_one_of_mem_longInv hξ
  by_cases hξa : ξ a = a
  · refine ⟨ξ, hξN, ⟨hξ, hξa⟩, fun g hg _ => ?_⟩
    rwa [hξ2, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hg
  obtain ⟨C, hC, -⟩ := hξ.2
  have hC' : ξ C = C := hC
  have hCa : C ≠ a := fun h => hξa (h ▸ hC')
  have hξb : ξ (ξ a) = a := by rw [← Perm.mul_apply, hξ2, Perm.one_apply]
  have hCb : C ≠ ξ a := by
    intro h
    apply hξa
    calc ξ a = C := h.symm
      _ = ξ C := hC'.symm
      _ = ξ (ξ a) := by rw [h]
      _ = a := hξb
  by_cases hAlt : M = alternatingGroup Δ
  · have hτ : swap a C * ξ * (swap a C)⁻¹ ∈ longInvAt (Perm Δ) Δ a := by
      have := conj_mem_longInvAt_perm (⟨hξ, hC⟩ : ξ ∈ longInvAt (Perm Δ) Δ C) (swap a C)
      rwa [swap_apply_right] at this
    have h3 : (swap a C * swap (ξ a) C).IsThreeCycle := by
      rw [swap_comm a C, swap_comm (ξ a) C]
      exact Perm.isThreeCycle_swap_mul_swap_same hCa hCb (Ne.symm hξa)
    have hτξ := conj_swap_mul_eq_swap_mul_swap (a := a) hξ2 hC'
    refine ⟨swap a C * ξ * (swap a C)⁻¹, ?_, hτ, fun g hg hga => ?_⟩
    · rw [eq_mul_inv_of_mul_eq hτξ, inv_eq_of_mul_eq_one_right hξ2]
      exact N.mul_mem (hMN (hAlt ▸ h3.mem_alternatingGroup)) hξN
    rw [hτξ] at hg
    have hσa : (swap a C * swap (ξ a) C) a = C := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hξa) (Ne.symm hCa), swap_apply_left]
    have hσC : (swap a C * swap (ξ a) C) C = ξ a := by
      rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hξa hCb.symm]
    rw [(isOfFinOrder_of_finite _).mem_zpowers_iff_mem_range_orderOf, h3.orderOf] at hg
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hg
    rw [Finset.mem_range] at hk
    interval_cases k
    · exact pow_zero _
    · rw [pow_one, hσa] at hga
      exact absurd hga hCa
    · rw [sq, Perm.mul_apply, hσa, hσC] at hga
      exact absurd hga hξa
  have hNM' := hNM fun h => hAlt h.1
  have hSE : IsNaturalSE M := hM.resolve_left fun h => hAlt h.1
  have hξM : ξ ∈ M := hNM' hξN
  obtain ⟨n, i, e, hA⟩ := hSE.exists_isBenderAction
  obtain ⟨g, hg⟩ := hM.isPretransitive.exists_smul_eq C a
  have hgC : (g : Perm Δ) C = a := hg
  have hτ : (g : Perm Δ) * ξ * (g : Perm Δ)⁻¹ ∈ longInvAt (Perm Δ) Δ a := by
    have := conj_mem_longInvAt_perm (⟨hξ, hC⟩ : ξ ∈ longInvAt (Perm Δ) Δ C) (g : Perm Δ)
    rwa [hgC] at this
  have hτM : (g : Perm Δ) * ξ * (g : Perm Δ)⁻¹ ∈ M := M.mul_mem (M.mul_mem g.2 hξM) (M.inv_mem g.2)
  refine ⟨_, hMN hτM, hτ, fun x hx hxa => ?_⟩
  set τ' : M := ⟨_, hτM⟩
  set ξ' : M := ⟨ξ, hξM⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hx'v : (((τ' * ξ') ^ k : M) : Perm Δ) = x := by
    rw [Subgroup.coe_zpow, Subgroup.coe_mul]
    exact hk
  have hτ'2 : τ' * τ' = 1 := Subtype.ext (mul_self_eq_one_of_mem_longInv hτ.1)
  have hξ'2 : ξ' * ξ' = 1 := Subtype.ext hξ2
  have hτ'o : orderOf τ' = 2 := by rw [Subgroup.orderOf_mk]; exact hτ.1.1
  have hξ'o : orderOf ξ' = 2 := by rw [Subgroup.orderOf_mk]; exact hξ.1
  have hodd : Odd (orderOf (τ' * ξ')) :=
    hA.odd_orderOf_mul hτ'o hξ'o (α := a) (β := C) hτ.2 hC hCa.symm
  have hx'z : (τ' * ξ') ^ k ∈ Subgroup.zpowers (τ' * ξ') := Subgroup.zpow_mem_zpowers _ _
  have hx'odd : Odd (orderOf ((τ' * ξ') ^ k)) := hodd.of_dvd_nat (orderOf_dvd_of_mem_zpowers hx'z)
  have hx'a : (τ' * ξ') ^ k • a = a := by
    rw [Subgroup.smul_def, hx'v]
    exact hxa
  have h1 := hA.eq_one_of_mul_mul_inv_eq_inv hx'a hx'odd hτ.2 hτ'o
    (conj_eq_inv_of_mem_zpowers_mul hτ'2 hξ'2 hx'z)
  rw [← hx'v, h1, Subgroup.coe_one]

end Factor

namespace HoltData

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] (D : HoltData G Ω)

theorem exists_mem_M_conj_rho_tHull_eq {i : D.ι} {y : Perm (D.Ψc i)} (hy : y ∈ (D.ρ i).range)
    (hyJ : y ∈ longInv (Perm (D.Ψc i)) (D.Ψc i)) : ∃ g ∈ D.M i, g * D.ρ i D.tHull * g⁻¹ = y :=
  (D.factor i).exists_mem_conj_eq (fun h => (D.range_rho_of_not_isOuterFactor h).le)
    ⟨D.tHull, rfl⟩ (D.rho_mem_longInv D.t_mem i) hy hyJ

theorem exists_mem_longInv_rho_eq (y : ∀ i, Perm (D.Ψc i)) (hy : ∀ i, y i ∈ (D.ρ i).range)
    (hyJ : ∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i)) :
    ∃ u : jHull G Ω, (u : G) ∈ longInv G Ω ∧ ∀ i, D.ρ i u = y i := by
  choose g hgM hg using fun i => D.exists_mem_M_conj_rho_tHull_eq (hy i) (hyJ i)
  choose l hlL hl using fun i => D.mem_M.mp (hgM i)
  obtain ⟨h, -, hρ⟩ := D.exists_mem_iSup_rho_eq l hlL
  refine ⟨h * D.tHull * h⁻¹, conj_mem_longInv D.t_mem (h : G), fun i => ?_⟩
  rw [map_mul, map_mul, map_inv, hρ i, hl i, hg i]

theorem exists_mem_longInv_rho_eq_iff (y : ∀ i, Perm (D.Ψc i)) :
    (∃ u : jHull G Ω, (u : G) ∈ longInv G Ω ∧ ∀ i, D.ρ i u = y i) ↔
      ∀ i, y i ∈ (D.ρ i).range ∧ y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i) := by
  refine ⟨fun ⟨u, hu, hρ⟩ i => ?_, fun h => D.exists_mem_longInv_rho_eq y (fun i => (h i).1)
    fun i => (h i).2⟩
  rw [← hρ i]
  exact ⟨⟨u, rfl⟩, D.rho_mem_longInv hu i⟩

theorem exists_mem_longInvAt_rho_eq (α : Ω) (y : ∀ i, Perm (D.Ψc i))
    (hy : ∀ i, y i ∈ (D.ρ i).range)
    (hyJ : ∀ i, y i ∈ longInvAt (Perm (D.Ψc i)) (D.Ψc i) (D.coord α i)) :
    ∃ t : jHull G Ω, (t : G) ∈ longInvAt G Ω α ∧ ∀ i, D.ρ i t = y i := by
  obtain ⟨u, hu, hρ⟩ := D.exists_mem_longInv_rho_eq y hy fun i => (hyJ i).1
  obtain ⟨α', hα'⟩ := exists_mem_longInvAt hu
  have hfix : D.coord ((u : G) • α) = D.coord α := funext fun i => by
    rw [D.coord_smul, hρ]
    exact (hyJ i).2
  obtain ⟨o, ho⟩ := (D.coord_eq_iff α' α).mp ((D.coord_smul_eq_iff hα' α).mp hfix).symm
  let oH : jHull G Ω := ⟨(o : G), jOddCore_le_jHull o.2⟩
  refine ⟨oH * u * oH⁻¹, ?_, fun i => ?_⟩
  · have := conj_mem_longInvAt hα' (o : G)
    rwa [show (o : G) • α' = α from ho] at this
  · rw [map_mul, map_mul, map_inv, rho_eq_one_of_mem_jOddCore (h := oH) o.2 i, one_mul, inv_one,
      mul_one, hρ]

theorem exists_mem_longInvSwap_rho_eq_rho {α β : Ω} {u' : jHull G Ω}
    (hu' : (u' : G) ∈ longInv G Ω) (hβ : D.coord ((u' : G) • α) = D.coord β) :
    ∃ u : jHull G Ω, (u : G) ∈ longInvSwap G Ω α β ∧ ∀ i, D.ρ i u = D.ρ i u' := by
  have hξ : ∀ i, D.ρ i u' ∈ longInv (Perm (D.Ψc i)) (D.Ψc i) := fun i => D.rho_mem_longInv hu' i
  choose τ hτN hτ hP using fun i => (D.factor i).exists_mem_longInvAt_zpowers_eq_one
    (Subgroup.map_le_range _ _) (fun h => (D.range_rho_of_not_isOuterFactor h).le)
    (⟨u', rfl⟩ : D.ρ i u' ∈ (D.ρ i).range) (hξ i) (D.coord α i)
  obtain ⟨t, htα, hρt⟩ := D.exists_mem_longInvAt_rho_eq α τ hτN hτ
  obtain ⟨o, ho⟩ := (D.coord_eq_iff _ _).mp hβ
  let oH : jHull G Ω := ⟨(o : G), jOddCore_le_jHull o.2⟩
  have hx' : ((oH * u' : jHull G Ω) : G) • α = β := by
    rw [Subgroup.coe_mul, mul_smul]
    exact ho
  have hv := conj_mem_longInvAt htα ((oH * u' : jHull G Ω) : G)
  rw [hx'] at hv
  obtain ⟨x, hx, hxt⟩ := exists_conj_mem_longInvSwap (G := jHull G Ω) (Ω := Ω)
    (t := t) (u := oH * u' * t * (oH * u')⁻¹) (mem_longInvAt_subgroup_iff.mpr htα)
    (mem_longInvAt_subgroup_iff.mpr hv)
  refine ⟨x * t * x⁻¹, ⟨mem_longInv_subgroup_iff.mp hxt.1, hxt.2⟩, fun i => ?_⟩
  have hτ2 : τ i * τ i = 1 := mul_self_eq_one_of_mem_longInv (hτ i).1
  have hξ2 : D.ρ i u' * D.ρ i u' = 1 := mul_self_eq_one_of_mem_longInv (hξ i)
  have hρv : D.ρ i (oH * u' * t * (oH * u')⁻¹) = D.ρ i u' * τ i * (D.ρ i u')⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_mul, hρt, rho_eq_one_of_mem_jOddCore (h := oH) o.2 i,
      one_mul]
  have hcl : D.ρ i x ∈ Subgroup.closure ({τ i, D.ρ i u'} : Set (Perm (D.Ψc i))) := by
    have h1 : D.ρ i x ∈ (Subgroup.closure ({t, oH * u' * t * (oH * u')⁻¹} :
        Set (jHull G Ω))).map (D.ρ i) := ⟨x, hx, rfl⟩
    rw [MonoidHom.map_closure, Set.image_pair, hρt, hρv] at h1
    refine (Subgroup.closure_le _).mpr ?_ h1
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · have hm : D.ρ i u' ∈ Subgroup.closure ({τ i, D.ρ i u'} : Set (Perm (D.Ψc i))) :=
        Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
      exact mul_mem (mul_mem hm (Subgroup.subset_closure (Set.mem_insert _ _))) (inv_mem hm)
  have hkey := mul_conj_mem_zpowers_of_mem_closure hτ2 hξ2 hcl
  have hρu : D.ρ i (x * t * x⁻¹) = D.ρ i x * τ i * (D.ρ i x)⁻¹ := by
    rw [map_mul, map_mul, map_inv, hρt]
  have hfix : (D.ρ i u' * D.ρ i (x * t * x⁻¹)) (D.coord α i) = D.coord α i := by
    rw [Perm.mul_apply, ← D.coord_smul, show ((x * t * x⁻¹ : jHull G Ω) : G) • α = β from hxt.2,
      ← congrFun hβ i, D.coord_smul, ← Perm.mul_apply, hξ2, Perm.one_apply]
  have h1 := hP i _ (hρu ▸ hkey) hfix
  exact (eq_inv_of_mul_eq_one_right h1).trans (inv_eq_of_mul_eq_one_right hξ2)

theorem exists_mem_longInvSwap_rho_eq {α β : Ω} (y : ∀ i, Perm (D.Ψc i))
    (hy : ∀ i, y i ∈ (D.ρ i).range) (hyJ : ∀ i, y i ∈ longInv (Perm (D.Ψc i)) (D.Ψc i))
    (hyαβ : ∀ i, y i (D.coord α i) = D.coord β i) :
    ∃ u : jHull G Ω, (u : G) ∈ longInvSwap G Ω α β ∧ ∀ i, D.ρ i u = y i := by
  obtain ⟨u', hu', hρ⟩ := D.exists_mem_longInv_rho_eq y hy hyJ
  obtain ⟨u, hu, hρu⟩ := D.exists_mem_longInvSwap_rho_eq_rho (β := β) hu'
    (funext fun i => by rw [D.coord_smul, hρ, hyαβ])
  exact ⟨u, hu, fun i => (hρu i).trans (hρ i)⟩

end HoltData

end CFSG.Holt.H78
