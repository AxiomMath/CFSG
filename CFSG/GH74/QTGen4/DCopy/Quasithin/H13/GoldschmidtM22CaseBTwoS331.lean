module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.E3Defs

public section
namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem false_of_index_two_F4 (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {S T₀ : Subgroup G} (hS2 : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (hQS : T₀ ≤ S)
    (hQidx : T₀.relIndex S = 2) {u : G} (hu : orderOf u = 2)
    (hQu : ∀ g : G, g⁻¹ * u * g ∉ T₀) : False := by
  obtain ⟨N, -, hNn, hsq, huN⟩ := thompson_transfer_exists_normal_subgroup (X := ⊤) le_top hS2
    (by rw [Subgroup.relIndex_top_right]; exact hSi) hQS hQidx (Subgroup.mem_top u) hu
    (fun x _ => hQu x)
  have hN : N.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hNn))
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · obtain ⟨g, h, hgh⟩ := hnab
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by
      have := hsq x (Subgroup.mem_top x)
      rwa [hbot, Subgroup.mem_bot, pow_two] at this)
    apply hgh
    calc g * h = (g * h)⁻¹ := (hinv _).symm
      _ = h * g := by rw [mul_inv_rev, hinv, hinv]
  · exact huN (htop ▸ Subgroup.mem_top u)

end CFSG.Quasithin.H13.GM22
