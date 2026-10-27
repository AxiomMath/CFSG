module


public import Mathlib.GroupTheory.Nilpotent
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosedPrimeCentralized

open CFSG.Quasithin

theorem centralizes {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P P₀ : Subgroup G} (hP : IsPGroup p P) (h0 : P₀ ≤ P) (hcard : Nat.card P₀ = p)
    (hweak : IsWeaklyClosedIn P₀ P) : P ≤ Subgroup.centralizer (P₀ : Set G) := by
  have hconj : ∀ g ∈ P, ∀ x ∈ P₀, g * x * g⁻¹ ∈ P₀ := by
    intro g hg x hx
    have hle : conjSubgroup P₀ g ≤ P := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have : y = g⁻¹ * (g * y * g⁻¹) * g := by group
      rw [this]
      exact P.mul_mem (P.mul_mem (P.inv_mem hg) (h0 hy)) hg
    have heq := hweak g hle
    have : x ∈ conjSubgroup P₀ g := by rw [heq]; exact hx
    rwa [mem_conjSubgroup_iff] at this
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent P := hP.isNilpotent
  let Q : Subgroup P := P₀.subgroupOf P
  haveI : Q.Normal := ⟨fun x hx g => by
    have := hconj g g.2 x (by simpa [Q, Subgroup.mem_subgroupOf] using hx)
    simpa [Q, Subgroup.mem_subgroupOf] using this⟩
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have hc : Nat.card Q = p := by
      rw [← hcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h0).toEquiv
    rw [hbot, Subgroup.card_bot] at hc
    exact hp.one_lt.ne hc
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hQ
  obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hzQ : (z : P) ∈ Q := (Subgroup.mem_inf.1 z.2).1
  have hzC : (z : P) ∈ Subgroup.center P := (Subgroup.mem_inf.1 z.2).2
  set a : G := ((z : P) : G) with ha
  have haP0 : a ∈ P₀ := by simpa [Q, Subgroup.mem_subgroupOf] using hzQ
  have ha1 : a ≠ 1 := by
    intro h
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hord : orderOf a = p := by
    have hd : orderOf a ∣ p := by
      rw [← hcard]
      exact (orderOf_submonoid ⟨a, haP0⟩ ▸ orderOf_dvd_natCard (⟨a, haP0⟩ : P₀))
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  have hzp : Subgroup.zpowers a = P₀ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le]; exact haP0
    · rw [hcard, Nat.card_zpowers, hord]
  intro g hg x hx
  rw [← hzp] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hc : Commute (g : G) a := by
    have := Subgroup.mem_center_iff.1 hzC ⟨g, hg⟩
    have h2 := congrArg Subtype.val this
    exact (by simpa using h2 : ((g : G) * a = a * g))
  exact (hc.zpow_right k).eq.symm

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.WeakClosedPrimeCentralized
