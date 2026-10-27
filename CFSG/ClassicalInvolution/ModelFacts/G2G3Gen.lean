module

public import CFSG.ClassicalInvolution.ModelFacts.G2G3Partner
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToral
public import CFSG.ClassicalInvolution.ModelFacts.G2G3Weyl

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank Matrix
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Field3

variable {F : Type} [Field F] [Finite F]

theorem three_eq_zero_of_card_eq_three (h : Nat.card F = 3) : (3 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h0 := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, h] at h0
  exact_mod_cast h0

theorem unit_eq_one_or_neg_one_of_card_three (h : Nat.card F = 3) (u : Fˣ) : u = 1 ∨ u = -1 := by
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card]; exact h
  have h1 : (u : F) ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
  rw [hF] at h1
  exact unit_eq_one_or_neg_one_of_sq_eq_one (Units.ext (by simpa using h1))

end Field3

section Generate

variable {F : Type} [Field F] [Finite F]


theorem adjointGroup_le_sup_t_m0_three (hodd : Odd (Nat.card F)) (h3 : Nat.card F = 3)
    (b : Fin Tag.G2.rank → Fˣ) :
    adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
      (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer
        ({rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL)} : Set (ModGL Tag.G2 F))) := by
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  have h30 : (3 : F) = 0 := three_eq_zero_of_card_eq_three h3
  obtain ⟨η, hη, hcommη⟩ := exists_sign_comm_e0 (F := F) hK2
  have key : ∀ b' : Fin Tag.G2.rank → Fˣ, ((b' g2i0 : Fˣ) : F) * η = -1 →
      adjointGroup Tag.G2 F ≤ toralCentralizer Tag.G2 F ![-1, 1] ⊔
        (adjointGroup Tag.G2 F ⊓ Subgroup.centralizer
          ({rootDiagUnit Tag.G2 b' * (g2ChartA F WSL * g2ChartB F WSL)} :
            Set (ModGL Tag.G2 F))) := by
    intro b' hb'
    refine adjointGroup_le_of_weyl_e0 hodd le_sup_left ?_
    refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨rootChart_mem_adjointGroup 1 g2i0 WSL, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcommη b' hb').symm
  have hη1 : η = 1 ∨ η = -1 := by
    rcases mul_self_eq_one_iff.mp hη with h | h
    exacts [Or.inl h, Or.inr h]
  have hb0 : b g2i0 = 1 ∨ b g2i0 = -1 := unit_eq_one_or_neg_one_of_card_three h3 _
  have hb1 : b g2i1 = 1 ∨ b g2i1 = -1 := unit_eq_one_or_neg_one_of_card_three h3 _
  by_cases hbη : ((b g2i0 : Fˣ) : F) * η = -1
  · exact key b hbη
  ·
    have hbη1 : ((b g2i0 : Fˣ) : F) * η = 1 := by
      rcases hb0 with h | h <;> rcases hη1 with h' | h'
      · rw [h, h']
        simp
      · exact absurd (by rw [h, h']; simp) hbη
      · exact absurd (by rw [h, h']; simp) hbη
      · rw [h, h']
        simp
    obtain ⟨x, hxX, hx⟩ := exists_partner_m0 hodd h30 b hb1
    refine adjointGroup_le_sup_of_conj hxX ?_
    rw [hx]
    refine key _ ?_
    rw [g2tup_0, Units.val_neg, neg_mul, hbη1]

theorem centralizer_sup_eq_top_g2_three (hodd : Odd (Nat.card F)) (h3 : Nat.card F = 3)
    {z z' : ↥(adjointGroup Tag.G2 F)} (hz : z * z = 1) (hz' : z' * z' = 1) (hz1 : z ≠ 1)
    (hz1' : z' ≠ 1) (hne : z ≠ z') (hcomm : z * z' = z' * z) :
    Subgroup.centralizer ({z} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({z'} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  obtain ⟨hasq, hane, -⟩ := g2_toral_data_a1 (F := F) hodd ha
  have hda : rootDiagUnit Tag.G2 a ∈ torusGroup Tag.G2 F := g2_rootDiagUnit_mem_torusGroup a
  have hdK : rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a hda)).1
  set d₁ : ↥(adjointGroup Tag.G2 F) := ⟨_, hdK⟩ with hd₁
  have hd₁2 : d₁ * d₁ = 1 := by
    apply Subtype.ext
    show rootDiagUnit Tag.G2 a * rootDiagUnit Tag.G2 a = 1
    rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
    congr 1
    funext i
    rcases hasq i with h | h <;> simp [h]
  have hd₁1 : d₁ ≠ 1 := by
    intro h
    have h' : rootDiagUnit Tag.G2 a = 1 := congrArg Subtype.val h
    rw [← rootDiagUnit_one] at h'
    exact hane (rootDiagUnit_injective h')
  obtain ⟨h, hh⟩ := g2_involutions_conj hodd hz hd₁2 hz1 hd₁1
  set w : ↥(adjointGroup Tag.G2 F) := h * z' * h⁻¹ with hw
  have hw2 : w * w = 1 := by
    calc w * w = h * (z' * z') * h⁻¹ := by rw [hw]; group
      _ = 1 := by rw [hz']; group
  have hw1 : w ≠ 1 := by
    intro h0
    apply hz1'
    calc z' = h⁻¹ * (h * z' * h⁻¹) * h := by group
      _ = 1 := by rw [← hw, h0]; group
  have hwd : w ≠ d₁ := by
    intro h0
    apply hne
    rw [← hh] at h0
    have : h * z' * h⁻¹ = h * z * h⁻¹ := h0
    calc z = h⁻¹ * (h * z * h⁻¹) * h := by group
      _ = h⁻¹ * (h * z' * h⁻¹) * h := by rw [this]
      _ = z' := by group
  have hdw : d₁ * w = w * d₁ := by
    rw [← hh, hw]
    calc h * z * h⁻¹ * (h * z' * h⁻¹) = h * (z * z') * h⁻¹ := by group
      _ = h * (z' * z) * h⁻¹ := by rw [hcomm]
      _ = h * z' * h⁻¹ * (h * z * h⁻¹) := by group
  have hwX : (w : ModGL Tag.G2 F) ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨w.2, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact congrArg Subtype.val hdw
  obtain ⟨x, hxX, t, ht, hx⟩ := exists_conj_to_torus_mul hodd ha hwX
    (congrArg Subtype.val hw2) (fun h0 => hw1 (Subtype.ext h0))
    (fun h0 => hwd (Subtype.ext h0))
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have htK : rootDiagUnit Tag.G2 b ∈ adjointGroup Tag.G2 F :=
    (mem_toralCentralizer.mp (torusGroup_le_toralCentralizer a ht)).1
  have hm₀K : g2ChartA F WSL * g2ChartB F WSL ∈ adjointGroup Tag.G2 F :=
    mul_mem (g2ChartA_mem WSL) (g2ChartB_mem WSL)
  set y : ↥(adjointGroup Tag.G2 F) := ⟨rootDiagUnit Tag.G2 b * (g2ChartA F WSL * g2ChartB F WSL),
    mul_mem htK hm₀K⟩ with hy
  set x' : ↥(adjointGroup Tag.G2 F) := ⟨x, (mem_toralCentralizer.mp hxX).1⟩ with hx'
  have hyx : x' * w * x'⁻¹ = y := by
    apply Subtype.ext
    exact hx
  have hxd : x' * d₁ * x'⁻¹ = d₁ := by
    apply Subtype.ext
    have h1 := (mem_toralCentralizer.mp hxX).2
    rw [mul_inv_eq_iff_eq_mul] at h1
    show x * rootDiagUnit Tag.G2 a * x⁻¹ = rootDiagUnit Tag.G2 a
    rw [mul_inv_eq_iff_eq_mul]
    exact h1.symm
  have hd₁val : (d₁ : ModGL Tag.G2 F) = rootDiagUnit Tag.G2 ![-1, 1] := by
    show rootDiagUnit Tag.G2 a = _
    rw [ha]
  have hgen : Subgroup.centralizer ({d₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({y} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
    apply Subgroup.map_injective (adjointGroup Tag.G2 F).subtype_injective
    rw [Subgroup.map_sup, map_centralizer_g2_eq_toralCentralizer hd₁val,
      map_centralizer_g2_eq_inf, Subgroup.map_top, Subgroup.range_subtype]
    refine le_antisymm (sup_le (fun x hx => (mem_toralCentralizer.mp hx).1) inf_le_left) ?_
    exact adjointGroup_le_sup_t_m0_three hodd h3 b
  have hX : Subgroup.centralizer ({d₁} : Set ↥(adjointGroup Tag.G2 F)) ⊔
      Subgroup.centralizer ({w} : Set ↥(adjointGroup Tag.G2 F)) = ⊤ := by
    apply (sup_centralizer_conj_eq_top_iff x' d₁ w).mp
    rw [hxd, hyx]
    exact hgen
  apply (sup_centralizer_conj_eq_top_iff h z z').mp
  rw [hh]
  exact hX

end Generate

end CFSG.ClassicalInvolution.G2D4Models
