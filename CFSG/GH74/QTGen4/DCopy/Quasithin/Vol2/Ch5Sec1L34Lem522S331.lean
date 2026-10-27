module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Basic
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise commutatorElement

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem card_B_dvd_three_F4 (h510 : Stmt5_1_10_F4) (hBor : L34BorelFact) : Nat.card B ∣ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hBK' : B ≤ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [← hMK]; exact hBK.1
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf h.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hker : π.ker ≤ (T ⊓ K).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := ⟨x, by assumption, rfl⟩
    exact CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK hx'
  have hS : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map π) ⊤ := by
    refine ⟨le_top, IsPGroup.map (A4.isPGroup_subgroupOf_of_le hTK.1 hTK.2.1) _, ?_⟩
    have h1 : ((((T ⊓ K).subgroupOf K).map π).subgroupOf ⊤).index =
        (((T ⊓ K).subgroupOf K).map π).index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
    exact hTK.2.2
  have hY : (B.subgroupOf K).map π ≤
      Subgroup.normalizer ((((T ⊓ K).subgroupOf K).map π : Subgroup (O2Q K)) : Set (O2Q K)) :=
    (Subgroup.map_mono (le_normalizer_subgroupOf (hBK'.trans inf_le_right))).trans
      (Subgroup.le_normalizer_map π)
  set ψ := π.comp (B.subgroupOf K).subtype with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hb
    have hb' : ((b : ↥K) : G) ∈ pCoreOf 2 K := ⟨b, by assumption, rfl⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 K) ⟨_, hb'⟩
    have hk' : ((b : ↥K) : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hbB : ((b : ↥K) : G) ∈ B := b.2
    have hodd : Odd (orderOf ((b : ↥K) : G)) := by
      have h1 : orderOf ((b : ↥K) : G) ∣ Nat.card B := by
        have := orderOf_dvd_natCard (⟨((b : ↥K) : G), hbB⟩ : ↥B)
        rwa [Subgroup.orderOf_mk] at this
      exact Odd.of_dvd_nat hBK.2.1 h1
    have hg : orderOf ((b : ↥K) : G) ∣ Nat.gcd (2 ^ k) (orderOf ((b : ↥K) : G)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') dvd_rfl
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)),
      Nat.dvd_one, orderOf_eq_one_iff] at hg
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext hg)
  have hcard : Nat.card ↥((B.subgroupOf K).map π) = Nat.card B := by
    have hr : ψ.range = (B.subgroupOf K).map π := by
      rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hBK'.trans inf_le_left)).toEquiv
  have hodd : Odd (Nat.card ↥((B.subgroupOf K).map π)) := by rw [hcard]; exact hBK.2.1
  have := hBor (O2Q K) h.l34 _ _ hS hY hodd
  rwa [hcard] at this

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13
