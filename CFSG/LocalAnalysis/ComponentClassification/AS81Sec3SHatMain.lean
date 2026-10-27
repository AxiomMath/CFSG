module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHat
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddA
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddSuz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools Sec3

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem exists_sec38Hyp_SHat
    (h17 : Step17G24Odd) (hQ : Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    ∃ H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀,
      omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range ∧
      Q₀ ⊔ Q ≤ sec3F (Q₀ ⊔ Q) ∧ Zs ≤ Q ∧
      AS76b.oddCoreIn (sec3F (Q₀ ⊔ Q) ⊓ centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
        centralizer (sec3F (Q₀ ⊔ Q) : Set G) := by
  obtain ⟨H, -, hΩ⟩ := exists_sec38Hyp_omega h17 hQ
  have hS := hQ.dData.suz
  have hQF := (step38_of h17 G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀ hQ).1
  have hTx : T ≤ centralizer ({x} : Set G) :=
    hS.T_le.trans (map_subtype_le _ : sec3B A₁ x ≤ centralizer ({x} : Set G))
  have hTC : Nat.card ↥(T ⊓ centralizer (Q : Set G)) ≤ 2 :=
    card_le_two_of_le_centralizer_Q hS (hS.T_two.to_le inf_le_left) inf_le_right
      (inf_le_left.trans hTx)
  obtain ⟨τ, v₀, -, hV⟩ := exists_tau_sec38V hQ (T_le_normalizer_V hQ) hTC
  have hOB : AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ≤
      centralizer (B₀ : Set G) := by
    intro w hw
    have hwx := H.oddCoreIn_le_centralizer_x h17 hw
    have hwQ : w ∈ centralizer (Q : Set G) :=
      Subgroup.centralizer_le (le_sup_right : Q ≤ Q₀ ⊔ Q) (AS76b.oddCoreIn_le _ hw)
    have hodd : Odd (orderOf w) :=
      (AS76b.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hw)
    exact Subgroup.centralizer_le H.B₀_le_B
      (mem_centralizer_sec3B_of_odd hS (centralizer_le_normalizer_sec3B A₁ x hwx) hwQ hodd)
  exact ⟨H, hΩ, hQF, H.Zs_le_Q hV.T_V hV.Zs_eq hV.card_TC,
    H.oddCoreIn_le_centralizer_F hΩ hQF hOB⟩

end CFSG.ComponentClassification.AS81
