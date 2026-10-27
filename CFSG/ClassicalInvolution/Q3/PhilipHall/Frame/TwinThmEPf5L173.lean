module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinStruct
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmE

section L173


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lemma17_3_twoGroup (hΩ : HypOmegaGen Ω)
    (hq8 : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧ Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hO : classicalInvolutionOddCore G = ⊥)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (hgen : (⨆ J ∈ Ω, J) = ⊤)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    {K : Subgroup G} (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥ := by
  have hquat : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (3 - 2))) := by
    intro J hJ P hP
    obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hq8 J hJ
    obtain ⟨k, -, hk⟩ := exists_conjSub_eq_of_isSylow2In hP₀ hP
    subst hk
    exact ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective).symm.trans e⟩
  have hT : Thm4Twin.TwinT4Hyp 3 G Ω := ⟨hΩ, h2, hquat, hA, hO⟩
  have hno : TL4.NoInvO2 Ω := by
    rintro J hJ u hu ⟨P, hPn, hP2, huP⟩
    have : Group.IsNilpotent ↥P := hP2.isNilpotent
    have hP1 := hsolv P hPn inferInstance
    rw [hP1, Subgroup.mem_bot] at huP
    exact hu.ne_one huP
  obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
  obtain ⟨L, hL, hLn, hzL⟩ := hT.exists_component thm4TwinThmA_three hgen hno hK hz
  have hmem : ∀ J ∈ Ω, ∀ u : G, IsUniqueInvolution J u → u ∈ L := by
    intro J hJ u hu
    obtain ⟨g, rfl⟩ := htrans J hJ
    have : u = g * z * g⁻¹ := (hz.conj g).eq hu |>.symm
    rw [this]
    exact hLn.conj_mem z hzL g
  have hZG : Subgroup.center G = ⊥ := hsolv _ inferInstance inferInstance
  have hC : Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [hT.centralizer_eq_center_of_inv_mem thm4TwinThmA_three hgen hno hL hmem, hZG]
  have hLZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) ⟨y, hy⟩)
    rw [hC, Subgroup.mem_bot] at hxC
    exact Subgroup.mem_bot.mpr (Subtype.ext hxC)
  refine ⟨L, hLn, CFSG.LieType.Chevalley.isSimpleGroup_of_isQuasisimple_of_center_eq_bot hL.1 hLZ, ?_, hC⟩
  obtain ⟨-, -, a, b, hab⟩ := hL.1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨x, x.2, y, y.2, fun h => hab ?_⟩
  have : x * y = y * x := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

end L173

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
