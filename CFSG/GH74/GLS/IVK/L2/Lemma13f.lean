module

public import CFSG.GH74.GLS.IVK.L2.DihedralAux3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.GH74.GLS.IVK.L2.TStruct

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

theorem isFourSubgroup_props {G : Type} [Group G] {U : Subgroup G} (h : IsFourSubgroup U) :
    (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧ (∀ x ∈ U, x * x = 1) := by
  obtain ⟨hE, -⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    exact congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : U) ⟨y, hy⟩)
  · intro x hx
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) x hx
    rwa [pow_two] at this

theorem exponent_of_isFourSubgroup {G : Type} [Group G] {U : Subgroup G} (h : IsFourSubgroup U) :
    Monoid.exponent ↥U = 2 := by
  obtain ⟨hE, hcard⟩ := h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite ↥U := Nat.finite_of_card_ne_zero (by omega)
  have hnt : Nontrivial ↥U := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  exact IsElementaryAbelian.exponent_eq_prime

section

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

include e in
omit [Finite K] in
theorem centralizer_four_inf_innDiagSub
    (hF : L2Field F) (U : Subgroup (MulAut K))
    (hU : U ≤ innAut K) (h4 : IsFourSubgroup U) :
    centralizer (U : Set (MulAut K)) ⊓ innDiagSub e = U := by
  have hUD : U ≤ innDiagSub e := hU.trans (innAut_le_innDiagSub e)
  have hodd := isOddPrimePower_of_L2Field hF
  obtain ⟨hcomm, -⟩ := isFourSubgroup_props h4
  let ι : ↥(innDiagSub e) ≃* PGL2 F := innDiagEquiv e
  let V : Subgroup (PGL2 F) := (U.subgroupOf (innDiagSub e)).map ι.toMonoidHom
  let ψ : ↥V ≃* ↥U :=
    (Subgroup.equivMapOfInjective (U.subgroupOf (innDiagSub e)) ι.toMonoidHom ι.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hUD)
  have hV : IsKleinFour V :=
    { card_four := (Nat.card_congr ψ.toEquiv).trans h4.2
      exponent_two := (Monoid.exponent_eq_of_mulEquiv ψ).trans (exponent_of_isFourSubgroup h4) }
  have hcent := pgl2_kleinFour_centralizer_eq_self F hodd V hV
  ext g
  constructor
  · rintro ⟨hgC, hgD⟩
    have hmem : ι ⟨g, hgD⟩ ∈ Subgroup.centralizer (V : Set (PGL2 F)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hgC (u : MulAut K) hu
    rw [hcent] at hmem
    obtain ⟨u, hu, hue⟩ := Subgroup.mem_map.mp hmem
    have : u = ⟨g, hgD⟩ := ι.injective hue
    have hu' : (u : MulAut K) ∈ U := hu
    rw [this] at hu'
    exact hu'
  · intro hgU
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, hUD hgU⟩
    intro y hy
    exact hcomm y hy g hgU

end

theorem ivk_1_3f_a : IVK_1_3f_a := by
  intro F _ _ hF K _ _ e N U₁ U₂ h₁ h₂ f₁ f₂
  obtain ⟨n, -, k, hk, hk2, ⟨φP⟩⟩ := ivk_1_2c F hF K e N
  have hcardP : Nat.card N.P = 2 ^ n := by
    rw [Nat.card_congr φP.toEquiv, DihedralGroup.nat_card, ← hk]
  obtain ⟨φ⟩ := Pt_dihedral_model hF N n hcardP
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨c₁, s₁⟩ := isFourSubgroup_props f₁
  obtain ⟨c₂, s₂⟩ := isFourSubgroup_props f₂
  exact DihedralAux.exists_conj_of_four_subgroups N.Pt N.P (P_le_Pt N) φ (P_index_two hF N)
    U₁ U₂ h₁ h₂ c₁ s₁ f₁.2 c₂ s₂ f₂.2

theorem ivk_1_3f_b : IVK_1_3f_b := by
  intro F _ _ hF K _ _ e N
  obtain ⟨U, hUle, hU4, hUcent⟩ := N.four_cent
  have hUP : U ≤ N.P := hUle
  have hUinn : U ≤ innAut K := hUle.trans inf_le_right
  obtain ⟨hcomm, -⟩ := isFourSubgroup_props hU4
  refine ⟨U, hUP, hU4, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨g, hg, hxg⟩ := fieldAutHom_fieldProj_mul e x
      generalize hφdef : fieldAutHom e (fieldProj e x) = φ at hxg
      have hφF : φ ∈ fieldAutSub e := hφdef ▸ ⟨fieldProj e x, rfl⟩
      have hφC : φ ∈ centralizer (U : Set (MulAut K)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (hUcent _ hφF u hu).symm
      have hgC : g ∈ centralizer (U : Set (MulAut K)) := by
        have : g = x * φ⁻¹ := by rw [hxg]; group
        rw [this]
        exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hφC)
      have hgU : g ∈ U := by
        have := centralizer_four_inf_innDiagSub e hF U hUinn hU4
        rw [← this]
        exact ⟨hgC, hg⟩
      rw [hxg]
      exact Subgroup.mul_mem_sup hgU hφF
    · apply sup_le
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hcomm y hy u hu
      · intro φ hφ
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        exact (hUcent φ hφ u hu).symm
  · rw [eq_bot_iff]
    rintro x ⟨hxU, hxF⟩
    have : x ∈ innDiagSub e ⊓ fieldAutSub e := ⟨(innAut_le_innDiagSub e) (hUinn hxU), hxF⟩
    rw [innDiagSub_inf_fieldAutSub e] at this
    exact this

end CFSG.GH74.GLS.IVK
