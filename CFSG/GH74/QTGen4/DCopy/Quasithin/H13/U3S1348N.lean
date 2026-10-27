module

public import CFSG.Quasithin.H13.U3S1348N
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1343

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V : Subgroup G}

theorem s134_centralizer_U_le_F4 (h1332 : Stmt13_3_2_F4) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V) {z : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G)) {H VH I : Subgroup G} (hHz : InHz T L V z H)
    (hred : IsTwoReducedIn H VH) {J : Subgroup (MulAut (IntMod VH hred.2.2.1))}
    {𝓗 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))} (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hK : K ∈ 𝓗)
    (hIK : autI hred.2.2.1 I = K) (hIH : I ≤ H)
    (hHK : ∀ g ∈ autI hred.2.2.1 H, B1.conjAut g K = K) :
    H ⊓ centralizer
      (C124.toG hred.2.2.1 (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) : Set G) ≤
      normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := C124.toG hred.2.2.1 (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) with hU
  obtain ⟨hTsyl, -, hHzC, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hVT : VH ≤ T := (le_pCoreOf_of_reduced hred).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  obtain ⟨u, huU, hu1, huZ⟩ := s134_exists_U_Z hred.2.2.1 hb hK hred.2.1 hHK hTH hT2 hVT
  set Z := quasithinOmegaOneCenter T with hZdef
  set ZL := Z ⊓ centralizer (L : Set G) with hZLdef
  have hzZ : z ∈ Z := (mem_inf.1 hz).2
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hzU : z ∉ U := s134_not_mem_U hred.2.2.1 hb hK hIK hIH hHzC hz1
  have huz : u ≠ z := fun h => hzU (h ▸ huU)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hzZ).2.2

  have hcard := s134_card_Z_F4 h1332 hC58 h317 h56 S ⟨H, ⟨hTH, hO2H⟩, hHM⟩
  have hidx : (ZL.subgroupOf Z).index = 2 := by
    have h1 := (ZL.subgroupOf Z).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : ZL ≤ Z)).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card ↥ZL := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1

  have hw : ∃ w ∈ ZL, w ≠ 1 ∧ ∀ x ∈ H ⊓ centralizer (U : Set G), x * w = w * x := by
    have hcu : ∀ x ∈ H ⊓ centralizer (U : Set G), x * u = u * x := fun x hx =>
      (mem_centralizer_iff.1 (mem_inf.1 hx).2 u huU).symm
    have hcz : ∀ x ∈ H ⊓ centralizer (U : Set G), x * z = z * x := fun x hx =>
      mem_centralizer_singleton_iff.1 (hHzC (mem_inf.1 hx).1)
    by_cases hu : u ∈ ZL
    · exact ⟨u, hu, hu1, hcu⟩
    by_cases hz' : z ∈ ZL
    · exact ⟨z, hz', hz1, hcz⟩
    have hm := (mul_mem_iff_of_index_two hidx (a := ⟨u, huZ⟩) (b := ⟨z, hzZ⟩)).2 (by
      simp only [mem_subgroupOf]
      exact ⟨fun h => absurd h hu, fun h => absurd h hz'⟩)
    rw [mem_subgroupOf, Subgroup.coe_mul] at hm
    refine ⟨u * z, hm, fun h => huz ?_, fun x hx => ?_⟩
    · calc u = u * z * z := by rw [mul_assoc, ← pow_two, hz2, mul_one]
        _ = z := by rw [h, one_mul]
    · calc x * (u * z) = (x * u) * z := by group
        _ = (u * x) * z := by rw [hcu x hx]
        _ = u * (x * z) := by group
        _ = u * (z * x) := by rw [hcz x hx]
        _ = u * z * x := by group
  obtain ⟨w, hwZL, hw1, hwc⟩ := hw
  obtain ⟨hwZ, hwL⟩ := mem_inf.1 hwZL
  have hwT : w ∈ T := (mem_quasithinOmegaOneCenter_iff.1 hwZ).1
  have hwCT : w ∈ centralizer (T : Set G) := (mem_quasithinOmegaOneCenter_iff.1 hwZ).2.1

  have hcent : ∀ X : Subgroup G, (∀ x ∈ X, x * w = w * x) →
      X ≤ normalizer ((zpowers w : Subgroup G) : Set G) := by
    intro X hX x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (hX x hx) k).eq).symm
  have hNM := s134_normalizer_le_M S (X := zpowers w)
    (fun h => hw1 (zpowers_eq_bot.1 h))
    (hT2.to_le (zpowers_le.2 hwT))
    (sup_le (hcent L fun x hx => mem_centralizer_iff.1 hwL x hx)
      (hcent T fun x hx => mem_centralizer_iff.1 hwCT x hx))
  exact (hcent _ hwc).trans hNM

end CFSG.Quasithin.H13.U3
