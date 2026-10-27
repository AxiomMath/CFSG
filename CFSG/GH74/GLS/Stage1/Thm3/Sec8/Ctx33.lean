module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx30
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem swap_P (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {d : G} (hdS : d ∈ S)
    (hdn : d ∉ S1 S K₁) (hd2 : d * d = 1) : ∀ q ∈ Pof S K₁, d * q * d⁻¹ ∈ Pof S K₂ := by
  intro q hqP
  obtain ⟨hswap, -⟩ := hs.swap_of_not_mem hII hdS hdn
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hdS hqP.1) (inv_mem hdS), ?_⟩
  have hmem : d * (d * q * d⁻¹) * d⁻¹ ∈ K₁ := by
    have e : d * (d * q * d⁻¹) * d⁻¹ = q := by
      calc d * (d * q * d⁻¹) * d⁻¹ = (d * d) * q * (d * d)⁻¹ := by group
        _ = q := by rw [hd2]; group
    rw [e]
    exact hqP.2
  rw [← hswap]
  exact mem_conjugate_iff.2 hmem

theorem rank_ge_four_of_swap (hII : II4_4_4_center) (hq : II4_4_quat)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8) {d : G} (hdS : d ∈ S)
    (hdn : d ∉ S1 S K₁) (hd2 : d * d = 1) : 4 ≤ CFSG.pRank 2 G := by
  have hdC : d ∈ centralizer ({z} : Set G) := hs.S_le_C hII hdS
  have hzd : z * d = d * z := (Subgroup.mem_centralizer_iff.1 hdC) z (Set.mem_singleton z)
  have hdz : d * z * d⁻¹ = z := by
    rw [← hzd]
    group
  obtain ⟨E, hEsq, hEc⟩ := Basic.exists_swap_elemAb (P₁ := Pof S K₁) (P₂ := Pof S K₂)
    (X := S1 S K₁) (z := z) (d := d) (hs.P_comm hII) (hs.P_inf hII) hs.z_sq hs.z_ne hd2 hdz
    (hs.swap_P hII hdS hdn hd2)
    (fun q hq' => Basic.GQ.sq_mem_of_card_eight (hs.gq_P hII hq (Or.inl rfl)) hP8 hq') hP8
    (hs.P_le_S1 hII (Or.inl rfl)) (hs.P_le_S1 hII (Or.inr rfl)) hdn
  exact le_pRank_of_elem (isElemAb_of_sq_one hEsq) (by rw [hEc]; norm_num)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
