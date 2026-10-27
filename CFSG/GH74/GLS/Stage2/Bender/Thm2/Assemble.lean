module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Defs
public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Assemble

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem z_ne_one_of_ctx (ctx : Stage2Ctx G z k S) : z ≠ 1 := fun h => by
  have := ctx.orderOf_z
  rw [h, orderOf_one] at this
  omega

theorem cen_ne_top (ctx : Stage2Ctx G z k S) : Cen z ≠ ⊤ := by
  intro htop
  have hzc : z ∈ center G := Subgroup.mem_center_iff.mpr fun g => by
    have : g ∈ Cen z := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  have hs : IsSimpleGroup G := ctx.std.kps.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hb | ht
  · exact z_ne_one_of_ctx ctx (by rw [hb] at hzc; exact Subgroup.mem_bot.mp hzc)
  · obtain ⟨a, b, hab⟩ := ctx.std.kps.2.1
    apply hab
    have : b ∈ center G := ht ▸ Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp this a

theorem exists_mem_maximalOverCentralizer (ctx : Stage2Ctx G z k S) : ∃ M, M ∈ maximalOverCentralizer z := by
  obtain ⟨M, hM, hle⟩ := (IsCoatomic.eq_top_or_exists_le_coatom (Cen z)).resolve_left (cen_ne_top ctx)
  exact ⟨M, hM, hle⟩

theorem Fs_ne_bot_of_mem (ctx : Stage2Ctx G z k S) {M : Subgroup G} (hM : M ∈ maximalOverCentralizer z) :
    Fs M ≠ ⊥ := by
  intro hb
  have hzM : z ∈ M := hM.2 (mem_Cen_self z)
  have hgf : generalizedFitting ↥M = ⊥ := Subgroup.map_injective M.subtype_injective (by
    rw [← Fs_eq_map, hb, Subgroup.map_bot])
  have hz : (⟨z, hzM⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [hgf]
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have : h = 1 := hh
    rw [this]
    simp
  have h1 := centralizer_generalizedFitting_le_fitting'' ↥M hz
  have h2 : fittingSubgroup ↥M ≤ generalizedFitting ↥M := le_sup_left
  have h3 := h2 h1
  rw [hgf, Subgroup.mem_bot] at h3
  exact z_ne_one_of_ctx ctx (congrArg Subtype.val h3)

theorem Fs_eq_Op_of_pgroup {N : Subgroup G} {p : ℕ} (hp : p.Prime) (hpg : IsPGroup p ↥(generalizedFitting ↥N)) :
    Fs N = Op p N := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Fs_eq_Op_iff]
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.LocalCores.generalized_fitting_characteristic (G := ↥N)).2, hpg⟩
  · exact (CFSG.pCore_le_fitting ↥N p).trans le_sup_left

theorem hyp9A_of_odd (ctx : Stage2Ctx G z k S)
    (hodd : ∀ M ∈ maximalOverCentralizer z, Odd (Nat.card ↥(generalizedFitting ↥M)))
    (hpp : ∀ M ∈ maximalOverCentralizer z, ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(generalizedFitting ↥M)) :
    Hyp9A z := by
  intro N hN
  obtain ⟨p, hp, hpg⟩ := hpp N hN
  refine ⟨p, hp, ?_, Fs_eq_Op_of_pgroup hp hpg⟩
  rintro rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  have h1 : n = 0 := by
    by_contra hn0
    have h2 : Even (Nat.card ↥(generalizedFitting ↥N)) := hn ▸ (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    exact (Nat.not_even_iff_odd.mpr (hodd N hN)) h2
  have hone : Nat.card ↥(generalizedFitting ↥N) = 1 := by rw [hn, h1]; rfl
  apply Fs_ne_bot_of_mem ctx hN
  rw [Fs_eq_map]
  have : generalizedFitting ↥N = ⊥ := (Subgroup.card_eq_one).mp (by simpa using hone)
  rw [this, Subgroup.map_bot]

theorem not_Op_le_Cen (ctx : Stage2Ctx G z k S) {M : Subgroup G} (hzM : z ∈ M) {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) (hF : Fs M = Op p M) : ¬ Op p M ≤ Cen z := by
  intro hle
  have hD : generalizedFitting ↥M = pCore p ↥M := (Fs_eq_Op_iff M p).mp hF
  have hz : (⟨z, hzM⟩ : ↥M) ∈ centralizer ((generalizedFitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hD] at hh
    have hmem : (h : G) ∈ Op p M := ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hle hmem)
    exact Subtype.ext this
  have h1 := centralizer_generalizedFitting_le_fitting'' ↥M hz
  have h2 : fittingSubgroup ↥M ≤ generalizedFitting ↥M := le_sup_left
  have h3 := h2 h1
  rw [hD] at h3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := p) (G := ↥(pCore p ↥M))).mp
    CFSG.pCore_isPGroup ⟨_, h3⟩
  have hk' : orderOf z = p ^ k := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hk
    exact hk
  rw [ctx.orderOf_z] at hk'
  have hpk : p ∣ 2 ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk' ▸ dvd_pow_self p (Nat.pos_iff_ne_zero.mp h0))
  rcases hpk with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h
    exact hodd this
  · rw [h, pow_zero] at hk'
    omega

end Assemble

end CFSG.GH74.GLS.Stage2.Bender.Thm2
