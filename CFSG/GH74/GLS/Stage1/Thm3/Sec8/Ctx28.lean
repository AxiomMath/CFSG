module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx27

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem exists_a_mem_D (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {w : G} (hw : w ∈ Wsub S U)
    (hc : (h⁻¹ * w * h) * w⁻¹ ∈ Aof S K₁ W₂ h) :
    ∃ a ∈ Aof S K₁ W₂ h, w * a ∈ Dsub S U h := by
  have hc' : w⁻¹ * ((h⁻¹ * w * h) * w⁻¹) * w ∈ Aof S K₁ W₂ h := by
    have := hs.A_normS hII hq hrec (inv_mem hw.1) hc
    rwa [inv_inv] at this
  obtain ⟨a, ha, hθ⟩ := hs.theta_surj hII hq hrec hk _ (inv_mem hc')
  refine ⟨a, ha, mem_Dsub_iff.2 ⟨mul_mem hw (hs.A_le_W hII hq hrec hk2 hk ha), ?_⟩⟩
  have e1 : h⁻¹ * a * h = (w⁻¹ * ((h⁻¹ * w * h) * w⁻¹) * w)⁻¹ * a := by
    calc h⁻¹ * a * h = ((h⁻¹ * a * h) * a⁻¹) * a := by group
      _ = (w⁻¹ * ((h⁻¹ * w * h) * w⁻¹) * w)⁻¹ * a := by rw [hθ]
  have e2 : h⁻¹ * (w * a) * h = w * a := by
    calc h⁻¹ * (w * a) * h = (h⁻¹ * w * h) * (h⁻¹ * a * h) := by group
      _ = (h⁻¹ * w * h) * ((w⁻¹ * ((h⁻¹ * w * h) * w⁻¹) * w)⁻¹ * a) := by rw [e1]
      _ = w * a := by group
  calc (w * a) * h = h * (h⁻¹ * (w * a) * h) := by group
    _ = h * (w * a) := by rw [e2]

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
