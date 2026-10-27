module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzLocalQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONLocalQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.MultThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.Blueprint.NativeSporadic Cover

section Suz

theorem excExcluded_suz : ExcExcluded .Suz (fun _ _ _ => False) SuzQ := by
  intro H _ _ N L K t u hcov hset hQ u₁ hN _ _ _ h
  exact h

theorem solomonCoreP_suz : SolomonCoreP .Suz SuzQ :=
  solomonCoreP_of_fusion .Suz (fun _ _ _ => False) SuzQ suzQ_inL suz_fusionRowData excExcluded_suz

end Suz

section ON

theorem onQ_avoids (hmult : OddMultThree .ONan) :
    PairClass.AvoidsPrimeCentralizer ONQ .ONan 11 := by
  intro H _ _ L K u hcov hQ hdvd
  obtain ⟨hu, hu2, -, -, -, -⟩ := hQ
  have hsq : (⟨u, hu⟩ : ↥L) * ⟨u, hu⟩ = 1 := Subtype.ext (mul_self_eq_one_of_orderOf hu2)
  have h1 : (L ⊓ centralizer ({u} : Set H)).subgroupOf L =
      centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨x.2, congrArg Subtype.val h⟩⟩
  have h2 : centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L) =
      (centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))).comap (q ↥L) := by
    ext x
    exact mem_centralizer_singleton_iff_mk hcov.2.1 hsq
  have h3 : Nat.card ↥((centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))).comap (q ↥L)) =
      Nat.card ↥(center ↥L) *
        Nat.card ↥(centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))) :=
    QuotientGroup.card_preimage_mk (center ↥L)
      ((centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L)) : Subgroup _) :
        Set (↥L ⧸ center ↥L))
  have hcard : Nat.card ↥(L ⊓ centralizer ({u} : Set H)) = Nat.card ↥(center ↥L) *
      Nat.card ↥(centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))) := by
    calc Nat.card ↥(L ⊓ centralizer ({u} : Set H))
        = Nat.card ↥((L ⊓ centralizer ({u} : Set H)).subgroupOf L) :=
          (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (inf_le_left : L ⊓ centralizer ({u} : Set H) ≤ L)).toEquiv).symm
      _ = Nat.card ↥(centralizer ({(⟨u, hu⟩ : ↥L)} : Set ↥L)) := by rw [h1]
      _ = Nat.card ↥((centralizer ({q ↥L ⟨u, hu⟩} : Set (↥L ⧸ center ↥L))).comap (q ↥L)) := by
          rw [h2]
      _ = _ := h3
  rw [hcard] at hdvd
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 11)).1 hdvd with h | h
  · have := Nat.le_of_dvd (by norm_num) (h.trans (hcov.card_center_dvd_three hmult))
    omega
  · exact on_not_dvd_card_centralizer hcov.2.2 (hcov.orderOf_q_involution hu hu2) h

theorem excExcluded_on (hmult : OddMultThree .ONan) :
    ExcExcluded .ONan (ExcPerfect 11) ONQ :=
  excExcluded_of_perfect_fixed onQ_inL (onQ_avoids hmult) fun _ _ h => on_outTwo h

theorem solomonCoreP_on (hmult : OddMultThree .ONan) (hF : ONOuterFixedPerfect) :
    SolomonCoreP .ONan ONQ :=
  solomonCoreP_of_fusion .ONan (ExcPerfect 11) ONQ onQ_inL (on_fusionRowData hF)
    (excExcluded_on hmult)

end ON

end CFSG.EvenSporadicStandard.Induction
