module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmECent
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEQuotOdd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEQuotCentMain
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThm4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace ThmE

section Six


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem lemma17_3 (hΩ : HypOmegaGen Ω)
    (hq : ∀ L ∈ Ω, ∃ P : Subgroup G, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hO : classicalInvolutionOddCore G = ⊥)
    (hsolv : ∀ N : Subgroup G, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    (hgen : (⨆ J ∈ Ω, J) = ⊤)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    {K : Subgroup G} (hK : K ∈ Ω) (htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) :
    ∃ F : Subgroup G, F.Normal ∧ IsSimpleGroup ↥F ∧ (∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) ∧
      Subgroup.centralizer (F : Set G) = ⊥ := by
  have hquat : ∀ J ∈ Ω, ∀ P : Subgroup G, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    intro J hJ P hP
    obtain ⟨P₀, hP₀, ⟨e⟩⟩ := hq J hJ
    obtain ⟨k, -, hk⟩ := exists_conjSub_eq_of_isSylow2In hP₀ hP
    subst hk
    exact ⟨(Subgroup.equivMapOfInjective P₀ (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective).symm.trans e⟩
  have hT : Thm4Twin.TwinT4Hyp r G Ω := ⟨hΩ, h2, hquat, hA, hO⟩
  have hno : TL4.NoInvO2 Ω := by
    rintro J hJ u hu ⟨P, hPn, hP2, huP⟩
    have : Group.IsNilpotent ↥P := hP2.isNilpotent
    have hP1 := hsolv P hPn inferInstance
    rw [hP1, Subgroup.mem_bot] at huP
    exact hu.ne_one huP
  obtain ⟨z, hz⟩ := (hΩ.omega1 K hK).1
  obtain ⟨L, hL, hLn, hzL⟩ := hT.exists_component (thm4TwinThmA_all r) hgen hno hK hz
  have hmem : ∀ J ∈ Ω, ∀ u : G, IsUniqueInvolution J u → u ∈ L := by
    intro J hJ u hu
    obtain ⟨g, rfl⟩ := htrans J hJ
    have : u = g * z * g⁻¹ := (hz.conj g).eq hu |>.symm
    rw [this]
    exact hLn.conj_mem z hzL g
  have hZG : Subgroup.center G = ⊥ := hsolv _ inferInstance inferInstance
  have hC : Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [hT.centralizer_eq_center_of_inv_mem (thm4TwinThmA_all r) hgen hno hL hmem, hZG]
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

theorem e18_6_of (hr : 3 ≤ r) (h5 : E18_5 r) (hO2 : E18_6O2 r) : E18_6 r := by
  intro G _ _ Ω K S R W H c
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hO : classicalInvolutionOddCore G = ⊥ := c.oddCore_eq_bot
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := h5 G Ω K S R W H c
  have htrans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J := e18_3 G Ω K S R W H c
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant htrans c.stand.aEmpty
  have hZ2 : IsPGroup 2 ↥(Subgroup.center G) := center_isPGroup_two hO
  have hZH : Subgroup.center G ≤ H := by
    obtain ⟨z', -, hcz'⟩ := c.exists_centralizer_le
    intro x hx
    apply hcz'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_center_iff.mp hx z').symm
  have hZbot : Subgroup.center G = ⊥ :=
    c.eq_bot_of_central hr le_rfl hZ2 hZH
      (fun J hJ => (hO2 G Ω K S R W H c _ inferInstance hZ2).2 J hJ)
  have h2triv : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 ↥Q → Q = ⊥ := by
    intro Q hQn hQ2
    have := (hO2 G Ω K S R W H c Q hQn hQ2).1
    rw [hZbot] at this
    exact le_bot_iff.mp this
  have hsolv := AscThmA.solvable_normal_eq_bot_of_oddCore hO h2triv
  exact ⟨hO, lemma17_3 hΩ c.stand.quat hAΩ hO hsolv hgen c.stand.two c.stand.mem htrans⟩

end Six

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
