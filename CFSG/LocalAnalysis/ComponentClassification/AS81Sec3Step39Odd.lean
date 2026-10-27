module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddA
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddCore
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step39OddSuz

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open
open CFSG.ABGLocalTools Sec3

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}

theorem range_eq_omega
    (h17 : Step17G24Odd) (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀) :
    H.ρG.range = omegaGroup H.xsub.q H.xsub.q_nondegenerate := by
  obtain ⟨H', ⟨τ, hτ⟩, hΩ'⟩ := exists_sec38Hyp_omega h17 H.q0
  have hΩ : omegaGroup H.xsub.q H.xsub.q_nondegenerate ≤ H.ρG.range := hΩ'
  have hS := H.q0.dData.suz
  have hzB : z ∈ sec3B A₁ x := hS.T_le (hS.Q_le H.z_mem_Q)
  have hzZ : z ∉ centerIn (sec3B A₁ x) := by
    rw [hS.B_center]
    intro hz
    have h3 : orderOf z ∣ 3 := hS.setting.order_x ▸ orderOf_dvd_of_mem_zpowers hz
    have h2 : orderOf z = 2 := H.xsub.orderOf_z
    rw [h2] at h3
    norm_num at h3
  refine le_antisymm (H.range_le_omega_of_odd hΩ
    (fun w hw => exists_mem_sec3B_of_comm hS hτ.normB hτ.inv_x hw)
    (fun k hk => exists_mem_B₀_of_mem_centralizer hS hk) (fun w hw => ?_)
    (fun h hh hhz => mem_normalizer_sec3B_of_conj hS hh hzB hhz hzZ)) hΩ
  have hwx := H.oddCoreIn_le_centralizer_x h17 hw
  have hwQ : w ∈ centralizer (Q : Set G) :=
    Subgroup.centralizer_le (le_sup_right : Q ≤ Q₀ ⊔ Q) (AS76b.oddCoreIn_le _ hw)
  have hodd : Odd (orderOf w) :=
    (AS76b.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hw)
  exact mem_centralizer_sec3B_of_odd hS (centralizer_le_normalizer_sec3B A₁ x hwx) hwQ hodd

end Sec38Hyp

end CFSG.ComponentClassification.AS81
