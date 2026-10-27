module

public import CFSG.Quasithin.H13.A6S1516c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1516b

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth

namespace A6

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4) (hTL : ¬ T ≤ L)
include hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL

theorem relIndex_TL_F4 : (T ⊓ L).relIndex T = 2 := by
  let f : ↥T →* ℤˣ := Perm.sign.comp (S.frame.ρ.comp (Subgroup.inclusion S.frame.T_le))
  have hker : f.ker = (T ⊓ L).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨t.2, S.mem_L_of_sign_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk
        (g := ⟨t, S.frame.T_le t.2⟩) (S.T_le_NL t.2) h⟩
    · rintro ⟨-, htL⟩
      exact Perm.mem_alternatingGroup.1
        ((S.frame.image_L _).1 ⟨⟨t, S.frame.T_le t.2⟩, htL, rfl⟩)
  have hrange : f.range = ⊤ := by
    obtain ⟨t₀, ht₀T, ht₀⟩ := S.exists_odd_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
    rw [eq_top_iff]
    intro s _
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact f.range.one_mem
    · refine ⟨⟨t₀, ht₀T⟩, ?_⟩
      rcases Int.units_eq_one_or (Perm.sign (S.frame.ρ t₀)) with h | h
      · exact absurd h ht₀
      · exact h
  show ((T ⊓ L).subgroupOf T).index = 2
  rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

theorem false_of_not_conj_F4 {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxz : ∀ g : G, g * S.z * g⁻¹ ≠ x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup2 hxp S.h13.sylow
  set x' := g * x * g⁻¹ with hx'
  have hx'T : x' ∈ T := hg x (Subgroup.mem_zpowers x)

  have hnotL : ∀ k : G, k⁻¹ * x' * k ∉ L := by
    intro k hk
    have hk2 : k⁻¹ * x' * k * (k⁻¹ * x' * k) = 1 := by
      calc k⁻¹ * x' * k * (k⁻¹ * x' * k) = k⁻¹ * g * (x * x) * g⁻¹ * k := by rw [hx']; group
        _ = 1 := by rw [hx2]; group
    have hk1 : k⁻¹ * x' * k ≠ 1 := by
      intro h
      apply hx1
      calc x = g⁻¹ * k * (k⁻¹ * x' * k) * k⁻¹ * g := by rw [hx']; group
        _ = 1 := by rw [h]; group
    obtain ⟨g', hg'⟩ := S.exists_conj_z_of_L_F4 hNS h13315 h1356two hH hna hhat hn hlL hl hobl hctk
      hk hk2 hk1
    apply hxz (g⁻¹ * k * g')
    calc g⁻¹ * k * g' * S.z * (g⁻¹ * k * g')⁻¹ = g⁻¹ * k * (g' * S.z * g'⁻¹) * k⁻¹ * g := by group
      _ = x := by rw [hg', hx']; group
  have hTsyl := S.h13.sylow
  obtain ⟨N, hNn, hN⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson hTsyl.1 hTsyl.2
    inf_le_left (S.relIndex_TL_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL) hx'T
    (fun h => hnotL 1 (by simpa using h.2))
    (fun y hyT hyU => by
      have hord' : orderOf x' = 2 := by
        refine orderOf_eq_prime ?_ ?_
        · rw [hx', pow_two]
          calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
            _ = 1 := by rw [hx2]; group
        · intro h
          apply hx1
          calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = 1 := by rw [← hx', h]; group
      rw [hord']
      have hy1 : y ≠ 1 := fun h => hyU (h ▸ (T ⊓ L).one_mem)
      have := orderOf_pos y
      have hne : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
      omega)
    (fun k hk => hnotL k hk.2)

  have hsimp := S.h13.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · rw [h, Subgroup.index_bot] at hN
    have hT : Nat.card T ∣ Nat.card G := Subgroup.card_subgroup_dvd_card T
    rw [S.card_T_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL, hN] at hT
    norm_num at hT
  · rw [h, Subgroup.index_top] at hN
    omega

end Data

end Setting4

end A6

end CFSG.Quasithin.H13
