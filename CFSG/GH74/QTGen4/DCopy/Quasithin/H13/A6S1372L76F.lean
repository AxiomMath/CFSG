module

public import CFSG.Quasithin.H13.A6S1372L76F
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1355

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pRank_three_NV3_le_one_F4 (h13315 : Stmt13_3_15_F4) (h1337 : Stmt13_3_7_F4)
    (hhat : ¬ IsHatA6 L) {H : Subgroup G} (hH : H ∈ S.Hz) :
    CFSG.Open.pRank 3 (H ⊓ Subgroup.normalizer (S.V3 : Set G)) ≤ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : H ⊓ Subgroup.normalizer (S.V3 : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_inf_right _ hH.2.1).trans (S.G1_inf_G3_le_F4 h13315)
  set N := Subgroup.normalizer (V : Set G) with hN
  set X' := (H ⊓ Subgroup.normalizer (S.V3 : Set G)).subgroupOf N with hX'

  have h3V : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G)) :=
    (h1337 G T L V S.h13 S.irr S.a6).resolve_right fun h => hhat h.1
  have hker : ¬ 3 ∣ Nat.card S.frame.ρ.ker := by
    have e : S.frame.ρ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf N := by
      ext g
      rw [MonoidHom.mem_ker, S.rho_eq_one_iff, Subgroup.mem_subgroupOf]
    rw [e]
    intro h
    apply h3V
    refine h.trans ?_
    have h1 : Nat.card ((Subgroup.centralizer (V : Set G)).subgroupOf N) =
        Nat.card (Subgroup.centralizer (V : Set G) ⊓ N : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective N.subtype_injective]
    rw [h1]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h1 := A6L76F.pRank_le_map_of_not_dvd S.frame.ρ hker X'
  have h2 : X'.map S.frame.ρ ≤ A6L76F.stabE := by
    rintro _ ⟨g, hg, rfl⟩
    have hgH : (g : G) ∈ H := (Subgroup.mem_subgroupOf.mp hg).1
    have hgz : (g : G) * S.z * (g : G)⁻¹ = S.z := by
      have h1 : (g : G) ∈ S.G1 := hH.2.1 hgH
      rw [Setting4.G1, Subgroup.mem_centralizer_singleton_iff] at h1
      rw [h1, mul_inv_cancel_right]
    exact S.fix_e0123 g hgz
  have h3 := A6L76F.pRank_three_le_one h2
  have h4 : X'.map N.subtype = H ⊓ Subgroup.normalizer (S.V3 : Set G) := by
    rw [hX', Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hX]
  have h5 := A6L76B.pRank_map_le N.subtype (p := 3) (by
    rw [(MonoidHom.ker_eq_bot_iff _).2 N.subtype_injective, Subgroup.card_bot]
    norm_num) X'
  rw [h4] at h5
  omega

end Setting4

end CFSG.Quasithin.H13.A6
