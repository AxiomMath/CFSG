module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE1
public import CFSG.ClassicalInvolution.Asc77.AscC22G2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL


namespace CaseB

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem false_of_rLayer_te_le_centralizer_ue (hc : P23Cfg n Y R S t K' W u e g)
    (h : rLayer (Om R) (t * e) ≤ Subgroup.centralizer ({u * e} : Set Y)) : False := by
  obtain ⟨R₁, R₁', b₁, b', hR₁syl, -, hR₁D, -, hcomm, hb₁R, hb'R, hb₁sq, _, hub, _⟩ :=
    e_decomp hc
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hR₁RSet : R₁ ∈ RSet (Om R) := mem_RSet_of_isSylow2In hK hR₁syl
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) :=
    hR₁D.2.trans (normalizer_le_centralizer_e hc.data)
  have hKt : tightCore R ≤ Subgroup.centralizer ({t} : Set Y) := le_centralizer_of_unique hz
  have hR₁te : R₁ ≤ Subgroup.centralizer ({t * e} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxt : x * t = t * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKt (hR₁syl.1 hx))
    have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hx)
    calc x * (t * e) = (x * t) * e := by group
      _ = (t * x) * e := by rw [hxt]
      _ = t * (x * e) := by group
      _ = t * (e * x) := by rw [hxe]
      _ = (t * e) * x := by group
  have hle : R₁ ≤ rLayer (Om R) (t * e) := C22G.le_rLayer_of_le_centralizer hR₁RSet hR₁te
  have hcent : ∀ y ∈ R₁, b₁ * y = y * b₁ := by
    intro y hy
    have hyue : Commute y (u * e) := Subgroup.mem_centralizer_singleton_iff.mp (h (hle hy))
    have hye : Commute y e := Subgroup.mem_centralizer_singleton_iff.mp (hR₁e hy)
    have hyu : Commute y u := by
      have h1 : u = (u * e) * e⁻¹ := by group
      rw [h1]
      exact hyue.mul_right hye.inv_right
    have hyb' : Commute y b' := hcomm y hy b' hb'R
    have hb₁eq : b₁ = u * b'⁻¹ := by rw [hub]; group
    rw [hb₁eq]
    exact (hyu.mul_right hyb'.inv_right).symm
  have hquat : IsQuatSub R₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₁RSet
  have h1 : b₁ * b₁ = 1 := hquat.sq_eq_one_of_central hb₁R hcent
  rw [hb₁sq] at h1
  exact hz.ne_one h1

end CaseB

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
