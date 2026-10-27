module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208P2
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Main

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6.L208Key

section Aux

theorem mem_of_twoElt_of_normal_card {Y : Type*} [Group Y] [Finite Y] {L N : Subgroup Y} [N.Normal]
    (hNL : N ≤ L) (hL : Nat.card ↥L = 24) (hN : Nat.card ↥N = 8) {b : Y} (hb : b ∈ L)
    (hb2 : ∃ k : ℕ, b ^ (2 ^ k) = 1) : b ∈ N := by
  have hn : (N.subgroupOf L).Normal := Subgroup.Normal.subgroupOf inferInstance L
  have hNc : Nat.card ↥(N.subgroupOf L) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNL).toEquiv]
    exact hN
  have hq : Nat.card (↥L ⧸ N.subgroupOf L) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf L)
    rw [hL, hNc] at h
    omega
  obtain ⟨k, hk⟩ := hb2
  set q : ↥L ⧸ N.subgroupOf L := QuotientGroup.mk (⟨b, hb⟩ : ↥L) with hqdef
  have h1 : q ^ (2 ^ k) = 1 := by
    rw [hqdef, ← QuotientGroup.mk_pow]
    have : (⟨b, hb⟩ : ↥L) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    rw [this]
    rfl
  have h2 : q ^ 3 = 1 := by
    rw [← hq]
    exact pow_card_eq_one'
  have hd1 : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ k) := (by norm_num : Nat.Coprime 3 2).pow_right k
  have h3 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes hcop hd2 hd1
  have h4 : q = 1 := orderOf_eq_one_iff.mp h3
  have h5 : (⟨b, hb⟩ : ↥L) ∈ N.subgroupOf L := (QuotientGroup.eq_one_iff _).mp h4
  exact Subgroup.mem_subgroupOf.mp h5

end Aux

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem g2_toBar_mem_Nfrak (hctx : Stage2Ctx G z Kind.g2 S) (h4a : Thm4a (Cen z))
    (h4c : Thm4c z (Cen z)) {x : ↥(Cen z)} (hx : ∃ a : ℕ, orderOf x = 2 ^ a)
    (hL : toBar z x ∈ LBar z) : toBar z x ∈ (Nfrak z).map (toBar z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hg := L26.g2_data hctx
  obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, h3, -, -, -, -⟩ := hsh
  obtain ⟨hsup, hcomm, hcard⟩ := hprod
  have hcomm' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have hc₁ : IsComponent L₁ :=
    L26.isComponent_of_sl2_pair hsup hcomm (LBar_normal z) hodd₁ (by omega) hm₁
  have hlay := map_layer_toBar h4a
  have hNle : (layer ↥(Cen z)).map (toBar z) ≤ (Nfrak z).map (toBar z) :=
    Subgroup.map_mono le_sup_left
  have hcomp : ∀ L : Subgroup (CentralizerBar z), IsComponent L → L ≤ (Nfrak z).map (toBar z) :=
    fun L hL' => by
      calc L ≤ layer (CentralizerBar z) := le_sSup hL'
        _ = (layer ↥(Cen z)).map (toBar z) := hlay.symm
        _ ≤ (Nfrak z).map (toBar z) := hNle
  have hL₁ : L₁ ≤ (Nfrak z).map (toBar z) := hcomp L₁ hc₁
  have hr₂ : 3 ≤ r₂ := by
    obtain ⟨F, hF, hFin, hq, -⟩ := hm₂
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h2 : Nat.card F = r₂ := hq
    obtain ⟨m, hm⟩ := hodd₂
    omega
  rcases Nat.lt_or_ge 3 r₂ with h | h
  · have hc₂ : IsComponent L₂ :=
      L26.isComponent_of_sl2_pair (by rw [sup_comm]; exact hsup) hcomm' (LBar_normal z) hodd₂
        (by omega) hm₂
    have hLb : LBar z ≤ (Nfrak z).map (toBar z) := by
      rw [← hsup]
      exact sup_le hL₁ (hcomp L₂ hc₂)
    exact hLb hL
  · obtain rfl : r₂ = 3 := by omega
    obtain ⟨⟨eW⟩, hFR⟩ := h3 rfl
    have hZ₁ : Nat.card (center ↥L₁) = 2 := (sl2_model_facts hodd₁ (by omega) hm₁).2.1
    have hcen₁ : ∀ a ∈ L₁, (∀ c ∈ L₁, c * a = a * c) → a ∈ L₂ := fun a ha hc =>
      central_mem_of_card_inf hcomm hZ₁ hcard ha hc
    have hFΦ : generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ L₂ := by
      rw [hFR, hsup]
      exact Subgroup.map_subtype_le _
    have hWn := L26.WBar_normal z
    have hWL₂ : WBar z ≤ L₂ :=
      L26.le_of_normal_twoGroup_of_two_comps hc₁.1 hcomm hcen₁ (L26.WBar_two_pow z)
        ((L26.WBar_le_generalizedFitting z).trans hFΦ)
    have hWcard : Nat.card ↥(WBar z) = 8 := by
      rw [Nat.card_congr eW.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hL₂card : Nat.card ↥L₂ = 24 := L26.card_eq_of_hasSL2Model_three hm₂
    have hLsup : toBar z x ∈ L₁ ⊔ L₂ := by rw [hsup]; exact hL
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hcomm hLsup
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (toBar z x) ^ (2 ^ k) = 1 := by
      obtain ⟨a', ha'⟩ := hx
      exact ⟨a', by rw [← map_pow, ← ha', pow_orderOf_eq_one, map_one]⟩
    have hcab : Commute a b := hcomm a ha b hb
    have hpow : a ^ (2 ^ k) * b ^ (2 ^ k) = 1 := by
      rw [← hcab.mul_pow, ← hab]
      exact hk
    have hmemL₁ : b ^ (2 ^ k) ∈ L₁ := by
      have : b ^ (2 ^ k) = (a ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_right hpow
      rw [this]
      exact L₁.inv_mem (L₁.pow_mem ha _)
    have hmemI : b ^ (2 ^ k) ∈ L₁ ⊓ L₂ := ⟨hmemL₁, L₂.pow_mem hb _⟩
    have hsq : (b ^ (2 ^ k)) ^ 2 = 1 := by
      have h1 : orderOf (⟨b ^ (2 ^ k), hmemI⟩ : ↥(L₁ ⊓ L₂)) ∣ Nat.card ↥(L₁ ⊓ L₂) :=
        orderOf_dvd_natCard _
      rw [hcard] at h1
      have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
      exact congrArg Subtype.val h2
    have hb2 : ∃ j : ℕ, b ^ (2 ^ j) = 1 := by
      refine ⟨k + 1, ?_⟩
      rw [pow_succ, pow_mul]
      exact hsq
    have hbW : b ∈ WBar z :=
      mem_of_twoElt_of_normal_card hWL₂ hL₂card hWcard hb hb2
    have hbN : b ∈ (Nfrak z).map (toBar z) := by
      have : WBar z ≤ (Nfrak z).map (toBar z) := by
        rw [WBar_eq_map h4c]
        exact Subgroup.map_mono le_sup_right
      exact this hbW
    rw [hab]
    exact mul_mem (hL₁ ha) hbN

theorem g2_U_centralizes_oddCore (hctx : Stage2Ctx G z Kind.g2 S) (h4a : Thm4a (Cen z))
    (h4c : Thm4c z (Cen z)) {U : Subgroup G} (hUS : U ≤ S) (hU4 : IVK.IsFourSubgroup U)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U) :
    ∀ a ∈ OddCore z, ∀ u ∈ U, a * u = u * a := by
  have hg := L26.g2_data hctx
  have hLU : U ≤ LC z := hg.base.four_le U hUS hU4 hUn
  have hUC : U ≤ Cen z := hUS.trans hctx.S_le_Cen
  refine comm_oddCore_of_le hUC h4c (fun u hu => orderOf_mem_S hctx (hUS hu)) fun u hu => ?_
  have hx : ∃ a : ℕ, orderOf (⟨u, hUC hu⟩ : ↥(Cen z)) = 2 ^ a := by
    obtain ⟨k, hk⟩ := orderOf_mem_S hctx (hUS hu)
    exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  exact g2_toBar_mem_Nfrak hctx h4a h4c hx
    ⟨⟨u, hUC hu⟩, Subgroup.mem_subgroupOf.mpr (hLU hu), rfl⟩

theorem g2_R_centralizes_oddCore (hctx : Stage2Ctx G z Kind.g2 S) (h4a : Thm4a (Cen z))
    (h4c : Thm4c z (Cen z)) : ∀ a ∈ OddCore z, ∀ r ∈ RC S z, a * r = r * a := by
  have hRS : RC S z ≤ S := inf_le_left
  have hRC : RC S z ≤ Cen z := hRS.trans hctx.S_le_Cen
  refine comm_oddCore_of_le hRC h4c (fun u hu => orderOf_mem_S hctx (hRS hu)) fun u hu => ?_
  have hx : ∃ a : ℕ, orderOf (⟨u, hRC hu⟩ : ↥(Cen z)) = 2 ^ a := by
    obtain ⟨k, hk⟩ := orderOf_mem_S hctx (hRS hu)
    exact ⟨k, by rw [Subgroup.orderOf_mk]; exact hk⟩
  exact g2_toBar_mem_Nfrak hctx h4a h4c hx
    ⟨⟨u, hRC hu⟩, Subgroup.mem_subgroupOf.mpr hu.2, rfl⟩

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
