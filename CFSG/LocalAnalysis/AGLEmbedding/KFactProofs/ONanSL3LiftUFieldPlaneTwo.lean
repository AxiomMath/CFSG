module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlanePrim
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlaneSL2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3LiftUFieldPlaneSub
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped MatrixGroups

theorem eq_top_of_subfield_diag_two {p f f₀ : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData p f K) (hf : f = 3 * f₀) (hq₀ : 4 ≤ p ^ f₀)
    (K₀ : Subfield K) (hK₀ : Nat.card K₀ = p ^ (2 * f₀)) (H₂ : Subgroup (unitarySU p f K 2))
    (hK : ∀ g : unitarySU p f K 2,
      (∀ i j, ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j ∈ K₀) → g ∈ H₂)
    (hD : ∀ g : unitarySU p f K 2,
      ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).IsDiag → g ∈ H₂) :
    H₂ = ⊤ := by
  classical
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two (r := p) (f := f)
    h.card_eq_sq
  have hF : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  obtain ⟨r, hr, hrq, hrk⟩ := exists_primitive_prime_three h.prime hq₀
  rw [← hf] at hrq hrk
  have : Fact r.Prime := ⟨hr⟩
  have hf0 : 3 ≤ f := by
    have : 1 ≤ f₀ := by
      rcases Nat.eq_zero_or_pos f₀ with rfl | hpos
      · simp at hq₀
      · exact hpos
    omega
  have hcardU : Nat.card Kˣ = p ^ (2 * f) - 1 := by rw [Nat.card_units, h.card]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' r (hcardU ▸ hrq)
  have hrq1 : r ∣ p ^ f + 1 := by
    have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hprod : (p ^ f - 1) * (p ^ f + 1) = p ^ (2 * f) - 1 := by
      zify [hq1, Nat.one_le_pow _ _ h.prime.pos, Nat.one_le_pow (2 * f) p h.prime.pos]
      ring
    rcases (Nat.Prime.dvd_mul hr).1 (hprod ▸ hrq) with h1 | h1
    · exact absurd h1 (hrk f (by omega) (by omega))
    · exact h1
  have ha1 : a ^ (p ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (ha ▸ hrq1)
  let g : unitarySU p f K 2 := ⟨diagInvTwo a, diagInvTwo_mem_unitarySU h ha1⟩
  have hgH : g ∈ H₂ := hD g (isDiag_diagInvTwo a)
  have hgord : orderOf g = r := by
    rw [← Subgroup.orderOf_coe g]
    exact (orderOf_diagInvTwo a).trans ha
  let H' : Subgroup SL(2, CFSG.LieType.Steinberg.fixedSubfield K p f) :=
    H₂.comap e.toMonoidHom
  have hx : e.symm g ∈ H' := by
    show e (e.symm g) ∈ H₂
    rw [MulEquiv.apply_symm_apply]
    exact hgH
  have hxr : orderOf (e.symm g) = r := by rw [MulEquiv.orderOf_eq]; exact hgord
  have hns : ¬ Group.IsSolvable H' := by
    intro hs
    refine not_isSolvable_of_subfield h hf hq₀ hK₀ H₂ hK ?_
    refine Group.isSolvable_of_surjective (f := e.toMonoidHom.subgroupComap H₂) ?_
    intro y
    exact ⟨⟨e.symm y, by show e (e.symm y) ∈ H₂; rw [MulEquiv.apply_symm_apply]; exact y.2⟩,
      Subtype.ext (MulEquiv.apply_symm_apply e y)⟩
  have htop : H' = ⊤ := eq_top_of_primitive_prime hF hf0 hr hrq hrk H' hns hx hxr
  rw [eq_top_iff]
  intro y _
  have hy : e.symm y ∈ H' := htop ▸ Subgroup.mem_top _
  have hy' : e (e.symm y) ∈ H₂ := hy
  rwa [MulEquiv.apply_symm_apply] at hy'

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3LiftUnitaryField
