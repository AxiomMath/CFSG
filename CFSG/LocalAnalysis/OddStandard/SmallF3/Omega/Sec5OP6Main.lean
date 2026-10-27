module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OP6Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ZSub
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PkBasic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec5op6_pocket [Finite G] {t z : G} {K Y : Subgroup G} (ht : orderOf t = 2)
    (hK : Sl23PocketIn (centralizer ({t} : Set G)) z K)
    (hY : Y ≤ centralizer ({z} : Set G))
    (hYn : ∀ h ∈ centralizer ({z} : Set G), ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) (htY : t ∈ Y)
    (hKY : ⁅K, Y⁆ ≤ oddCoreIn Y) :
    Sl23PocketIn (⊤ : Subgroup G) z (K ⊔ oddCoreIn (centralizer ({z} : Set G))) := by
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht, pow_two] at h
    exact h
  set H : Subgroup G := centralizer ({z} : Set G) with hH
  have hYnorm : (Y.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hY]
    intro y h hy hh
    exact hYn h hh y hy
  have hOY : oddCoreIn Y ≤ oddCoreIn H := oddCoreIn_le_of_normal hY hYnorm
  have hNH : oddCoreIn H ≤ H := (oddCoreIn_normal H).1
  have hNn : ∀ h ∈ H, ∀ n ∈ oddCoreIn H, h * n * h⁻¹ ∈ oddCoreIn H :=
    fun h hh n hn => conj_mem_oddCoreIn (Subgroup.le_normalizer hh) hn
  have hodd : Odd (Nat.card (oddCoreIn H)) := odd_card_oddCoreIn H
  have hsub := sec5op6_isSubnormal_sup ht2 hK hY hYn htY hNH hNn hodd (hKY.trans hOY)
  obtain ⟨hzK, hKle, -, hSL⟩ := hK
  have hKH : K ≤ H := hKle.trans inf_le_right
  refine ⟨Subgroup.mem_sup_left hzK, le_inf le_top (sup_le hKH hNH), ?_, ?_⟩
  · rw [top_inf_eq]
    exact hsub
  · exact isSL23Mod_sup_odd hSL (fun k hk n hn => hNn k (hKH hk) n hn) hodd

theorem sec5op6_pocket_of_L [Finite G] {t z : G} {L K Y : Subgroup G} (ht : orderOf t = 2)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLn : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L)
    (hK : Sl23PocketIn L z K) (hY : Y ≤ centralizer ({z} : Set G))
    (hYn : ∀ h ∈ centralizer ({z} : Set G), ∀ y ∈ Y, h * y * h⁻¹ ∈ Y) (htY : t ∈ Y)
    (hKY : ⁅K, Y⁆ ≤ oddCoreIn Y) :
    Sl23PocketIn (⊤ : Subgroup G) z (K ⊔ oddCoreIn (centralizer ({z} : Set G))) :=
  sec5op6_pocket ht (hK.of_normal_centralizer hLt (fun c hc => hLn c hc.1)) hY hYn htY hKY

end CFSG.OddStandard.SmallF3.Omega
