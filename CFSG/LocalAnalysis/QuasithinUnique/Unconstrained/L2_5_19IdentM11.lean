module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdGen
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.GH74.KGroups.M11

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Ch1

section Fixed

variable {G : Type} [Group G] [Finite G] {X K : Subgroup G} {t : G}

theorem IdentSetting.false_of_fixed_solvable
    {Q : Type} [Group Q] (hs : IdentSetting X K t)
    (e0 : (↥X ⧸ Subgroup.center ↥X) ≃* Q)
    (hfix : ∀ α : MulAut Q, α * α = 1 → α ≠ 1 → ∀ L : Subgroup Q, (∀ x ∈ L, α x = x) →
      Group.IsSolvable ↥L) : False := by
  have hπ := Tab.quotProj_surjective e0
  have hker := Tab.quotProj_ker e0
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := hs.comp.1
  have hKX : K ≤ X := hs.K_le
  have hα2 := Tab.quotAct_mul_self (Tab.quotProj e0) hπ hker hs.tN hs.sq
  have hα1 := Tab.quotAct_ne_one (Tab.quotProj e0) hπ hker hs.tN hs.quasi hs.comm
  let ρ : ↥K →* Q := (Tab.quotProj e0).comp (Subgroup.inclusion hKX)
  obtain ⟨hKsimple, a, b, hab⟩ := isKType_simple hs.ktype
  have hKcenter : Subgroup.center ↥K = ⊥ := center_eq_bot_of_simple_nonab ⟨a, b, hab⟩
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hz : Subgroup.inclusion hKX k ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hk
    have hzk : k ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k'
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hKX k'))
    rw [hKcenter] at hzk
    exact Subgroup.mem_bot.mp hzk
  have hρfix : ∀ k : ↥K, Tab.quotAct (Tab.quotProj e0) hπ hker hs.tN (ρ k) = ρ k := by
    intro k
    have hkt : (k : G) * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp (hKXt k.2).2
    have hy : ((Subgroup.inclusion hKX k : X) : G) =
        t * ((Subgroup.inclusion hKX k : X) : G) * t⁻¹ := by
      rw [Subgroup.coe_inclusion]
      calc (k : G) = (k * t) * t⁻¹ := by group
        _ = (t * k) * t⁻¹ := by rw [hkt]
    exact Tab.quotAct_apply (Tab.quotProj e0) hπ hker hs.tN _ _ hy
  have hsolv := hfix _ hα2 hα1 ρ.range (by
    rintro _ ⟨k, rfl⟩
    exact hρfix k)
  have hsolvK : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := ρ.rangeRestrict) (by
      intro x y hxy
      exact hρinj (congrArg Subtype.val hxy))
  have := hKsimple
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolvK a b)

end Fixed

theorem tabIdentFor_m11 :
    TabIdentFor (@Ident.FamSporadic .M11) := by
  intro G _ _ X K t hs hX
  exfalso
  obtain ⟨e⟩ := hX
  have hsimple : IsSimpleGroup (NativeSporadic.Carrier .M11) :=
    CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
  have hs' : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := e.isSimpleGroup
  have hncM : ∃ a b : NativeSporadic.Carrier .M11, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup (NativeSporadic.Carrier .M11) :=
      { (inferInstance : Group (NativeSporadic.Carrier .M11)) with
        mul_comm := fun a b => hcon a b }
    have : Finite (NativeSporadic.Carrier .M11) := CFSG.Sporadic.Mathieu.fam_m11_simplicity.1
    have hp := IsSimpleGroup.prime_card (α := NativeSporadic.Carrier .M11)
    rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from
      CFSG.Sporadic.Mathieu.card_M11] at hp
    exact absurd hp (by norm_num)
  have hnc : ∃ a b : ↥X ⧸ CFSG.pCore 2 ↥X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hncM
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hpc := pCore_eq_center_of_simple_quotient hs.quasi hs' hnc
  have e' : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.Carrier .M11 :=
    (QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e
  have hM : NativeSporadic.IsSporadic (NativeSporadic.Carrier .M11) .M11 := ⟨MulEquiv.refl _⟩
  have := CFSG.GH74.KGroups.M11.finite_K hM
  exact hs.false_of_fixed_solvable e' fun α hα2 hα1 L hL =>
    CFSG.GH74.KGroups.M11.fixed_solvable hM α (by rw [pow_two]; exact hα2) hα1 L hL

end CFSG.QuasithinUnique.Id2519
