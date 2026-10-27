module

public import CFSG.LargeExtraspecial.AS35CS63J2
public import CFSG.LargeExtraspecial.FS65Wall
public import CFSG.LargeExtraspecial.AS35CS63F
public import CFSG.LargeExtraspecial.AS35CS63Res

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open scoped commutatorElement

namespace S63

namespace Six


variable {G : Type} [Group G] {S : Setting G} (K : Six S)

theorem false_of_J2_gen [Finite G] (hn : 3 ≤ S.width) (hJ : J2SchurInput)
    {h : G} (hxM : h * S.z * h⁻¹ ∈ S.M) (hxz : h * S.z * h⁻¹ ≠ S.z) (hta : K.t ∈ S.Qa h)
    (hJ2 : Blueprint.NativeSporadic.IsSporadic
      (↥(normalClosure ({K.zeta} : Set (Cbar K.t))) ⧸
        center ↥(normalClosure ({K.zeta} : Set (Cbar K.t)))) .J2)
    (hFU : K.Fbar ≤ normalClosure ({K.zeta} : Set (Cbar K.t)))
    (hZ : center ↥(normalClosure ({K.zeta} : Set (Cbar K.t))) ≠ ⊥) : False := by
  set C := centralizer ({K.t} : Set G) with hC
  set UC : Subgroup C := normalClosure ({K.zC} : Set C) with hUC
  set Ub : Subgroup (Cbar K.t) := normalClosure ({K.zeta} : Set (Cbar K.t)) with hUb
  have hmap : UC.map (piC K.t) = Ub := by
    rw [hUC, map_normalClosure _ _ (piC_surjective K.t), Set.image_singleton]
    rfl
  have hzU : K.zC ∈ UC := subset_normalClosure (Set.mem_singleton _)
  have hUn : UC.Normal := normalClosure_normal
  set P : Pair S := ⟨h, K.t, K.hW, hxM, hxz, K.htQ, hta, K.ht1⟩ with hP
  obtain ⟨c₁, -, hc₁t, hc₁⟩ := P.exists_conj_eq_gen hn
  obtain ⟨c₂, -, hc₂t, hc₂⟩ := P.exists_conj_z_eq_gen hn
  set c₁C : C := ⟨c₁, mem_centralizer_singleton_iff.mpr hc₁t⟩
  set c₂C : C := ⟨c₂, mem_centralizer_singleton_iff.mpr hc₂t⟩
  set xC : C := ⟨P.x, mem_centralizer_singleton_iff.mpr P.t_comm_x.symm⟩
  have hy₂ : ((c₂C * K.zC * c₂C⁻¹ : C) : G) = K.t * P.x * S.z := hc₂
  have hy₂U : c₂C * K.zC * c₂C⁻¹ ∈ UC := hUn.conj_mem _ hzU _
  have hxtz : P.t * S.z * P.x = K.t * P.x * S.z := by
    change K.t * S.z * P.x = K.t * P.x * S.z
    rw [mul_assoc, ← P.x_comm_z, ← mul_assoc]
  have hxU : xC ∈ UC := by
    have : xC = c₁C⁻¹ * (c₂C * K.zC * c₂C⁻¹) * c₁C := by
      refine Subtype.ext ?_
      change P.x = c₁⁻¹ * ((c₂C * K.zC * c₂C⁻¹ : C) : G) * c₁
      rw [hy₂, ← hxtz, ← hc₁]
      group
    rw [this]
    simpa using hUn.conj_mem _ hy₂U c₁C⁻¹
  have htU : tC K.t ∈ UC := by
    have : tC K.t = K.zC * xC * (c₂C * K.zC * c₂C⁻¹) := by
      refine Subtype.ext ?_
      change K.t = S.z * P.x * ((c₂C * K.zC * c₂C⁻¹ : C) : G)
      rw [hy₂]
      have h1 : P.x * K.t = K.t * P.x := P.t_comm_x.symm
      have h2 : S.z * K.t = K.t * S.z := (S.z_comm_QG K.htQ).symm
      symm
      calc S.z * P.x * (K.t * P.x * S.z) = S.z * (P.x * K.t) * P.x * S.z := by group
        _ = S.z * (K.t * P.x) * P.x * S.z := by rw [h1]
        _ = S.z * K.t * (P.x * P.x) * S.z := by group
        _ = S.z * K.t * S.z := by rw [P.x_mul_x]; group
        _ = (K.t * S.z) * S.z := by rw [h2]
        _ = K.t := by rw [mul_assoc, S.z_mul_z, mul_one]
    rw [this]
    exact mul_mem (mul_mem hzU hxU) hy₂U
  have hQU : ∀ e : C, (e : G) ∈ S.QG → e ∈ UC := by
    intro e he
    have h1 : piC K.t e ∈ Ub := hFU (K.mem_Fbar_of he)
    rw [← hmap] at h1
    obtain ⟨u, hu, hue⟩ := h1
    rcases (piC_eq_iff K.ht2).mp hue with h2 | h2
    · rw [show e = u from Subtype.ext h2]
      exact hu
    · rw [show e = u * tC K.t from Subtype.ext h2]
      exact mul_mem hu htU
  have hperf : ⁅UC, UC⁆ = UC := by
    refine le_antisymm (commutator_le_left UC UC) (normalClosure_le_normal ?_)
    rw [Set.singleton_subset_iff]
    obtain ⟨e₁, ⟨he₁Q, he₁t⟩, e₂, ⟨he₂Q, he₂t⟩, he⟩ := K.exists_not_comm_CQ (by omega)
    set e₁C : C := ⟨e₁, he₁t⟩
    set e₂C : C := ⟨e₂, he₂t⟩
    have hcz : ⁅e₁C, e₂C⁆ = K.zC := by
      refine Subtype.ext ?_
      change e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = S.z
      rcases S.commutator_eq_one_or_z he₁Q he₂Q with h1 | h1
      · exact absurd (by
          calc e₁ * e₂ = e₁ * e₂ * e₁⁻¹ * e₂⁻¹ * (e₂ * e₁) := by group
            _ = e₂ * e₁ := by rw [h1, one_mul]) he
      · exact h1
    rw [← hcz]
    exact commutator_mem_commutator (hQU e₁C he₁Q) (hQU e₂C he₂Q)
  have hperfY : Group.IsPerfect ↥UC := Subgroup.isPerfect_iff.mpr hperf
  set ψ : ↥UC →* ↥Ub := (MulEquiv.subgroupCongr hmap).toMonoidHom.comp
    ((piC K.t).subgroupMap UC) with hψ
  have hψs : Function.Surjective ψ := by
    rw [hψ, MonoidHom.coe_comp]
    exact (MulEquiv.subgroupCongr hmap).surjective.comp ((piC K.t).subgroupMap_surjective UC)
  have hψv : ∀ u : ↥UC, ((ψ u : ↥Ub) : Cbar K.t) = piC K.t u := fun u => rfl
  have htZ : ∀ u : ↥UC, ψ u = 1 → (u : C) = 1 ∨ (u : C) = tC K.t := by
    intro u hu
    have h1 : piC K.t u = 1 := by rw [← hψv, hu]; rfl
    rcases (piC_eq_one_iff K.ht2).mp h1 with h2 | h2
    · exact Or.inl (Subtype.ext h2)
    · exact Or.inr (Subtype.ext h2)
  have htcen : (⟨tC K.t, htU⟩ : ↥UC) ∈ center ↥UC :=
    mem_center_iff.mpr fun u => Subtype.ext (mem_center_iff.mp (tC_mem_center K.t) u)
  have hcen : ∀ w : ↥UC, ψ w ∈ center ↥Ub → w ∈ center ↥UC := by
    intro w hw
    refine mem_center_of_commutator_mem_center fun u => ?_
    have h1 : ψ (u⁻¹ * (w * u * w⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← mem_center_iff.mp hw (ψ u)]
      group
    rcases htZ _ h1 with h2 | h2
    · rw [show u⁻¹ * (w * u * w⁻¹) = 1 from Subtype.ext h2]
      exact one_mem _
    · rw [show u⁻¹ * (w * u * w⁻¹) = ⟨tC K.t, htU⟩ from Subtype.ext h2]
      exact htcen
  have hcen' : ∀ w : ↥UC, w ∈ center ↥UC → ψ w ∈ center ↥Ub := by
    intro w hw
    rw [mem_center_iff]
    intro v
    obtain ⟨u, rfl⟩ := hψs v
    rw [← map_mul, ← map_mul, mem_center_iff.mp hw u]
  set π := (QuotientGroup.mk' (center ↥Ub)).comp ψ with hπ
  have hπs : Function.Surjective π := by
    rw [hπ, MonoidHom.coe_comp]
    exact (QuotientGroup.mk'_surjective _).comp hψs
  have hker : π.ker = center ↥UC := by
    ext w
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact ⟨hcen w, hcen' w⟩
  have hJ2U : Blueprint.NativeSporadic.IsSporadic (↥UC ⧸ center ↥UC) .J2 := by
    obtain ⟨e⟩ := hJ2
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)).trans e⟩
  have hle := hJ (↥UC) (Group.isPerfect_def.mp hperfY) hJ2U
  obtain ⟨wb, hwb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ
  obtain ⟨w, hw⟩ := hψs (wb : ↥Ub)
  have hwZ : w ∈ center ↥UC := hcen w (by rw [hw]; exact wb.2)
  have hw1 : w ≠ 1 := fun h' => hwb1 (Subtype.ext (by rw [← hw, h', map_one]; rfl))
  set τ : ↥UC := ⟨tC K.t, htU⟩ with hτ
  have hτ1 : τ ≠ 1 := fun h' => K.ht1 (congrArg (fun v : ↥UC => ((v : C) : G)) h')
  have hψτ : ψ τ = 1 := by
    apply Subtype.ext
    rw [hψv]
    exact piC_tC
  have hwτ : w ≠ τ := fun h' => by
    have : ψ w = 1 := by rw [h', hψτ]
    exact hwb1 (Subtype.ext (by rw [← hw, this]; rfl))
  have hwτ1 : w * τ ≠ 1 := fun h' => hwτ (by
    have : w = τ⁻¹ := eq_inv_of_mul_eq_one_left h'
    rw [this]
    exact Subtype.ext (Subtype.ext (inv_eq_of_mul_eq_one_right K.ht2)))
  let f : Fin 4 → center ↥UC := ![1, ⟨τ, htcen⟩, ⟨w, hwZ⟩, ⟨w * τ, mul_mem hwZ htcen⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : ((f i : ↥UC)) = (f j : ↥UC) := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;>
      first
      | exact absurd hij'.symm hτ1
      | exact absurd hij' hτ1
      | exact absurd hij'.symm hw1
      | exact absurd hij' hw1
      | exact absurd hij'.symm hwτ1
      | exact absurd hij' hwτ1
      | exact absurd hij'.symm hwτ
      | exact absurd hij' hwτ
  have h4 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h4
  omega


end Six

end S63

end CFSG.LargeExtraspecial
