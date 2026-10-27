module

public import CFSG.GH74.Uniqueness.SU.KI1r4LyFour
public import CFSG.Sporadic.Schreier.LyOuter
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.LyPerm

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier

theorem exists_fixed_involution_of_odd {G : Type*} [Group G] [Finite G] (β : G →* G)
    (hβ : ∀ x, β (β x) = x) (hodd : Odd (Nat.card {t : G // orderOf t = 2})) :
    ∃ t : G, orderOf t = 2 ∧ β t = t := by
  classical
  have : Fintype {t : G // orderOf t = 2} := Fintype.ofFinite _
  let f : Perm G := ⟨β, β, hβ, hβ⟩
  have hinj : Function.Injective β := fun a b h => by rw [← hβ a, ← hβ b, h]
  have hf : ∀ t : G, orderOf (f t) = 2 ↔ orderOf t = 2 := fun t => by
    show orderOf (β t) = 2 ↔ orderOf t = 2
    rw [orderOf_injective β hinj t]
  let σ : Perm {t : G // orderOf t = 2} := f.subtypePerm hf
  have hσ : σ ^ 2 ^ 1 = 1 := by
    refine Equiv.ext fun t => Subtype.ext ?_
    simp only [pow_one, pow_two, Perm.mul_apply, Perm.one_apply]
    exact hβ t
  have hcard : ¬ 2 ∣ Fintype.card {t : G // orderOf t = 2} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.not_even_iff_odd.2 hodd |> fun h => by simpa [even_iff_two_dvd] using h
  obtain ⟨t, ht⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hcard hσ
  exact ⟨t.1, t.2, congrArg Subtype.val ht⟩

theorem card_involutions_J :
    Nat.card {t : J // orderOf t = 2} = 1296826875 := by
  have hconj : conjugatesOf lyz = {t : J | orderOf t = 2} := by
    ext t
    constructor
    · intro ht
      obtain ⟨c, hc⟩ := isConj_iff.1 (show IsConj lyz t from ht)
      show orderOf t = 2
      rw [← hc, ← orderOf_lyz]
      exact (MulAut.conj c).orderOf_eq lyz
    · intro ht
      obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 t ht
      exact isConj_iff.2 ⟨x, hx⟩
  have h1 := Subgroup.index_centralizer_eq_ncard (lyz : J)
  rw [hconj, index_centralizer_lyz] at h1
  rw [← Nat.card_coe_set_eq] at h1
  exact h1.symm

theorem exists_sigma_of_aut {K : Type} [Group K] [Group.IsPerfect K]
    (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 11)) (y : MulAut K) (hy2 : y * y = 1) :
    ∃ σ : Perm (Fin 11), σ * σ = 1 ∧ ∀ k : K,
      ((CFSG.GH74.Generic.S45.LAlt.projAlt e (y k) : alternatingGroup (Fin 11)) : Perm (Fin 11)) =
        σ * ((CFSG.GH74.Generic.S45.LAlt.projAlt e k : alternatingGroup (Fin 11)) : Perm (Fin 11)) *
          σ⁻¹ := by
  set yb : MulAut (alternatingGroup (Fin 11)) :=
    MulAut.congr e (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K y) with hyb
  have hπy : ∀ k : K, CFSG.GH74.Generic.S45.LAlt.projAlt e (y k) =
      yb (CFSG.GH74.Generic.S45.LAlt.projAlt e k) := fun k => by
    show e (QuotientGroup.mk' (Subgroup.center K) (y k)) =
      (MulAut.congr e (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K y))
        (e (QuotientGroup.mk' (Subgroup.center K) k))
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
  have hyb2 : yb * yb = 1 := by
    rw [hyb, ← map_mul, ← map_mul, hy2, map_one, map_one]
  by_cases hyb1 : yb = 1
  · refine ⟨1, by simp, fun k => ?_⟩
    rw [hπy, hyb1]
    simp
  · obtain ⟨σ, hσ2, -, hσyb⟩ :=
      CFSG.GH74.Generic.S45.LAlt.exists_sigma (by omega : 11 = 5 ∨ 7 ≤ 11) yb hyb1 hyb2
    exact ⟨σ, hσ2, fun k => by rw [hπy, hσyb]⟩

theorem exists_four_pair_of_fixes_z
    (β : MulAut J) (hβ : β * β = 1) (hz : β lyz = lyz) :
    ∃ a b : J, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧ β a = a ∧ β b = b := by
  classical
  have hβ0 : (restrictC ⟨β, mem_autZ.2 hz⟩ : MulAut lyC) * restrictC ⟨β, mem_autZ.2 hz⟩ = 1 := by
    rw [← map_mul]
    have : (⟨β, mem_autZ.2 hz⟩ : autZ) * ⟨β, mem_autZ.2 hz⟩ = 1 := Subtype.ext hβ
    rw [this, map_one]
  obtain ⟨σ, hσ, hy⟩ := exists_sigma_of_aut lyCenterEquiv (restrictC ⟨β, mem_autZ.2 hz⟩) hβ0
  set π := CFSG.GH74.Generic.S45.LAlt.projAlt lyCenterEquiv with hπdef
  have hπ : Function.Surjective π := CFSG.GH74.Generic.S45.LAlt.projAlt_surjective _
  have hkerz : π.ker = zGroup :=
    (CFSG.GH74.Generic.S45.LAlt.ker_projAlt lyCenterEquiv).trans center_lyC
  have hker : π.ker ≤ Subgroup.center lyC := by rw [hkerz, center_lyC]
  have hK2 : IsPGroup 2 π.ker := by
    rw [hkerz]
    exact IsPGroup.of_card (n := 1) (by rw [zGroup, Nat.card_zpowers, orderOf_zC]; norm_num)
  have hne : π.ker ≠ ⊥ := by
    intro h
    have : zC ∈ π.ker := by rw [hkerz]; exact mem_zGroup.2 (Or.inr rfl)
    rw [h, Subgroup.mem_bot] at this
    have h2 := orderOf_zC
    rw [this, orderOf_one] at h2
    omega
  obtain ⟨u, hπu, hu2, hβu⟩ :=
    exists_fixed_involution_lift π hπ hker hK2 hne (restrictC ⟨β, mem_autZ.2 hz⟩) σ hσ hy
  have hu1 : u ≠ 1 := fun h => hπu (by rw [h, map_one])
  have huz : u ≠ zC := fun h => hπu (by
    have : zC ∈ π.ker := by rw [hkerz]; exact mem_zGroup.2 (Or.inr rfl)
    rw [h]
    exact MonoidHom.mem_ker.1 this)
  have hβu' : β (u : J) = u := by
    have := congrArg Subtype.val hβu
    rwa [restrictC_apply] at this
  have hu2' : (u : J) ^ 2 = 1 := by
    have := congrArg Subtype.val hu2
    rw [sq]
    exact this
  have hcomm : lyz * (u : J) = (u : J) * lyz := by
    have h : (u : J) ∈ Subgroup.centralizer ({lyz} : Set J) := by
      rw [← lyC_eq_centralizer]
      exact u.2
    exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm
  have hz2 : lyz ^ 2 = 1 := by
    have := pow_orderOf_eq_one lyz
    rwa [orderOf_lyz] at this
  have hz1 : lyz ≠ 1 := fun h => by
    have := orderOf_lyz
    rw [h, orderOf_one] at this
    omega
  have hzC : ((zC : lyC) : J) = lyz := rfl
  have hu1' : (u : J) ≠ 1 := fun h => hu1 (Subtype.ext (h.trans (Subgroup.coe_one lyC).symm))
  have huz' : lyz ≠ (u : J) := fun h => huz (Subtype.ext (h.symm.trans hzC.symm))
  exact ⟨lyz, (u : J), hz2, hu2', hz1, hu1', huz', hcomm, hz, hβu'⟩

theorem exists_four_pair_J
    (β : MulAut J) (hβ : β * β = 1) :
    ∃ a b : J, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧ β a = a ∧ β b = b := by
  have hβ' : ∀ x : J, (β : J →* J) ((β : J →* J) x) = x := fun x => by
    have h := congrArg (fun γ : MulAut J => γ x) hβ
    simpa using h
  obtain ⟨t, ht2, hβt⟩ := exists_fixed_involution_of_odd (β : J →* J) hβ'
    (by rw [card_involutions_J]; exact ⟨648413437, by norm_num⟩)
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 t ht2
  set β' : MulAut J := MulAut.conj x⁻¹ * β * MulAut.conj x with hβ'def
  have hconj : ∀ v : J, β' v = x⁻¹ * β (x * v * x⁻¹) * x := fun v => by
    rw [hβ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
    simp
  have hβ'z : β' lyz = lyz := by
    rw [hconj, hx]
    have : β t = t := hβt
    rw [this, ← hx]
    group
  have hβ'2 : β' * β' = 1 := by
    ext v
    rw [MulAut.mul_apply, MulAut.one_apply, hconj, hconj]
    have h1 : x * (x⁻¹ * β (x * v * x⁻¹) * x) * x⁻¹ = β (x * v * x⁻¹) := by group
    rw [h1]
    have h2 : β (β (x * v * x⁻¹)) = x * v * x⁻¹ := hβ' _
    rw [h2]
    group
  obtain ⟨a, b, ha2, hb2, ha1, hb1, hab, hcomm, hfa, hfb⟩ :=
    exists_four_pair_of_fixes_z β' hβ'2 hβ'z
  have hfix : ∀ v : J, β' v = v → β (x * v * x⁻¹) = x * v * x⁻¹ := fun v h => by
    rw [hconj] at h
    calc β (x * v * x⁻¹) = x * (x⁻¹ * β (x * v * x⁻¹) * x) * x⁻¹ := by group
      _ = x * v * x⁻¹ := by rw [h]
  refine ⟨x * a * x⁻¹, x * b * x⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, hfix a hfa, hfix b hfb⟩
  · rw [conj_pow, ha2]
    group
  · rw [conj_pow, hb2]
    group
  · intro h
    apply ha1
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hb1
    calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · intro h
    apply hab
    calc a = x⁻¹ * (x * a * x⁻¹) * x := by group
      _ = x⁻¹ * (x * b * x⁻¹) * x := by rw [h]
      _ = b := by group
  · calc x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ := by group
      _ = x * (b * a) * x⁻¹ := by rw [hcomm]
      _ = x * b * x⁻¹ * (x * a * x⁻¹) := by group

end CFSG.GH74.Uniqueness.SU.K.R4.LyPerm
