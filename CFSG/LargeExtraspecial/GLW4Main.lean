module

public import CFSG.LargeExtraspecial.S14C8Cases
public import CFSG.LargeExtraspecial.GLW4DWR
public import CFSG.LargeExtraspecial.GLW4Lat2
public import CFSG.LargeExtraspecial.S14W4LocInst

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.LargeExtraspecial.GLR

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O} {c : Config}

theorem exists_lat4 (h : W4Hyp S g t c) [IsSimpleGroup G] (hNQ6 : NQPlus6Stmt)
    (hp : c = .omegaPlus6) :
    ∃ W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt, W4DW.Lat4 h.S₀ h.R₀ W₁ W₂ := by
  have hlat := h.lattice hNQ6 hp
  obtain ⟨W₁, W₂, h1, h2, h12, hc1, hc2, hall⟩ := hlat
  exact ⟨W₁, W₂, ⟨h1, h2, h12, hc1, hc2, hall⟩⟩

theorem surj_of (h : W4Hyp S g t c) {W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt}
    (hl : W4DW.Lat4 h.S₀ h.R₀ W₁ W₂) :
    ∀ f : W₁ ≃ₗ[ZMod 2] W₁, ∃ r : h.S₀.M, (r : ↥(Mbar0 S)) ∈ h.R₀ ∧
      ∀ w : W₁, ((f w : W₁) : h.S₀.Qt) = ((h.S₀.ρ r : h.S₀.O) : h.S₀.Qt ≃ₗ[ZMod 2] h.S₀.Qt) w := by
  have : FiniteDimensional (ZMod 2) (Vt S g t) := Module.Finite.of_finite
  have h1 : IsSimpleGroup ↥((h.R₀.subgroupOf h.S₀.M).map h.π) := by
    rw [h.π_R₀]
    exact isSimpleGroup_RmodN_of_occurs h.occ
  have h2 : Nat.card ↥((h.R₀.subgroupOf h.S₀.M).map h.π) = 20160 ∨
      Nat.card ↥((h.R₀.subgroupOf h.S₀.M).map h.π) = 25920 := by
    rw [h.π_R₀, h.RmodN_eq]
    exact O62.card_omegaGroup h.finrank_Vt h.qf_nondeg
  exact Lat4.surjective_res_R hl h.act h.card_Qt h1 h2

theorem sup_eq_top_of_finrank {X : Type*} [Group X] [Finite X] {T : Setting X} (hw : T.width = 4)
    {W₁ W₂ : Submodule (ZMod 2) T.Qt} (hinf : W₁ ⊓ W₂ = ⊥) (h₁ : finrank (ZMod 2) W₁ = 4)
    (h₂ : finrank (ZMod 2) W₂ = 4) : W₁ ⊔ W₂ = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W₁ W₂
  rw [hinf, finrank_bot, h₁, h₂, add_zero] at hsum
  rw [hsum, T.finrank_Qt_eq_two_mul_width, hw]

theorem latData_of (h : W4Hyp S g t c) {W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt}
    (hl : W4DW.Lat4 h.S₀ h.R₀ W₁ W₂) : LatData h.S₀ h.R₀ W₁ W₂ := by
  have hs₁ := surj_of h hl
  have hs₂ := surj_of h hl.symm
  exact ⟨fun k r hr => h.act.conj_mem k r hr, hl.inv₁, hl.inv₂, hl.inf,
    sup_eq_top_of_finrank h.width_S₀ hl.inf hl.finrank₁ hl.symm.finrank₁, hl.finrank₁,
    hl.symm.finrank₁, ts_of_surjective_R hl.finrank₁ fun f => (hs₁ f).imp fun _ hr => hr.2,
    ts_of_surjective_R hl.symm.finrank₁ fun f => (hs₂ f).imp fun _ hr => hr.2, hl.all⟩

theorem swap_of_outer (h : W4Hyp S g t c) {W₁ W₂ : Submodule (ZMod 2) h.S₀.Qt}
    (hl : W4DW.Lat4 h.S₀ h.R₀ W₁ W₂) {k : h.S₀.M}
    (hk : ∀ r : h.S₀.M, (r : ↥(Mbar0 S)) ∈ h.R₀ → h.π (r⁻¹ * k) ≠ 1) :
    W₁.map ((h.S₀.ρ k : h.S₀.O) : h.S₀.Qt →ₗ[ZMod 2] h.S₀.Qt) = W₂ := by
  have L := latData_of h hl
  have hm := L.map_eq k
  rcases hm with ⟨h1, h2⟩ | ⟨h1, -⟩
  · exfalso
    have hR := L.exists_R_of_preserve (surj_of h hl) h1 h2
    obtain ⟨r, hr, hρ⟩ := hR
    apply hk r hr
    have hQG := h.S₀.mem_QG_iff.mp ((h.S₀.ρ_eq_one_iff _).mp hρ)
    obtain ⟨hM, hQ⟩ := hQG
    exact h.π_eq_one_of_mem_Q hQ
  · exact h1

end CFSG.LargeExtraspecial.GLW4
