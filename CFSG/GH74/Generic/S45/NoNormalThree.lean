module

public import CFSG.GH74.Generic.S45.AutE8
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SubnormalPSubgroupLeQCore

public section

namespace CFSG.GH74.Generic.S45

open Subgroup MulAction

theorem not_normal_zpowers_of_fix {H X : Type*} [Group H] [Finite H] [MulAction H X] (c : H)
    (hc : orderOf c = 3) (hH : Nat.card H = 24) (x y : X) (S : Set X)
    (hS : ∀ g : H, ∀ s ∈ S, g • s ∈ S) (hx : x ∈ S) (hcx : c • x = x)
    (hfix : ∀ s ∈ S, c • s = s → s = x ∨ s = y)
    (hstab : Nat.card (MulAction.stabilizer H x) ≤ 3) : ¬ (zpowers c).Normal := by
  intro hN
  have hcard3 : Nat.card ↥(zpowers c) = 3 := by rw [Nat.card_zpowers, hc]
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcyc : IsCyclic ↥(zpowers c) := isCyclic_of_prime_card hcard3
  have hmul : Nat.card (MulAut ↥(zpowers c)) = 2 := by
    rw [IsCyclic.card_mulAut, hcard3]
    decide +kernel
  let φ : H →* MulAut ↥(zpowers c) := MulAut.conjNormal
  have hker : φ.ker ≤ centralizer ({c} : Set H) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg
      (fun f : MulAut ↥(zpowers c) => ((f ⟨c, mem_zpowers c⟩ : ↥(zpowers c)) : H)) hg
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hrange : Nat.card ↥φ.range ≤ 2 := by
    rw [← hmul]
    exact Nat.card_le_card_of_injective (fun a : ↥φ.range => (a : MulAut ↥(zpowers c)))
      Subtype.val_injective
  have hkerc : 12 ≤ Nat.card ↥(centralizer ({c} : Set H)) := by
    have h1 : Nat.card ↥φ.range * Nat.card ↥φ.ker = 24 := (card_range_mul_card_ker φ).trans hH
    have h2 : Nat.card ↥φ.ker ≤ Nat.card ↥(centralizer ({c} : Set H)) :=
      Subgroup.card_le_of_le hker
    have hpos : 0 < Nat.card ↥φ.range := Nat.card_pos
    have hr : Nat.card ↥φ.range = 1 ∨ Nat.card ↥φ.range = 2 := by omega
    rcases hr with hr | hr <;> rw [hr] at h1 <;> omega
  set CS : Subgroup H := centralizer ({c} : Set H) with hCS
  have horb : (MulAction.orbit ↥CS x : Set X) ⊆ {x, y} := by
    rintro _ ⟨g, rfl⟩
    have hg : (g : H) * c = c * (g : H) := by
      have := Subgroup.mem_centralizer_iff.1 g.2 c (Set.mem_singleton c)
      exact this.symm
    have h1 : (g • x : X) = (g : H) • x := rfl
    have h2 : (g : H) • x ∈ S := hS g x hx
    have h3 : c • ((g : H) • x) = (g : H) • x := by
      rw [← mul_smul, ← hg, mul_smul, hcx]
    rcases hfix _ h2 h3 with h4 | h4
    · exact Or.inl (h1.trans h4)
    · exact Or.inr (h1.trans h4)
  have horbcard : (MulAction.orbit ↥CS x).ncard ≤ 2 := by
    have h1 := Set.ncard_le_ncard horb (Set.toFinite _)
    have h2 : ({x, y} : Set X).ncard ≤ 2 := by
      calc ({x, y} : Set X).ncard ≤ ({y} : Set X).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hstabCS : Nat.card ↥(MulAction.stabilizer ↥CS x) ≤ 3 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun g : ↥(MulAction.stabilizer ↥CS x) =>
        (⟨((g : ↥CS) : H), MulAction.mem_stabilizer_iff.2 (MulAction.mem_stabilizer_iff.1 g.2)⟩ :
          ↥(MulAction.stabilizer H x))) ?_) hstab
    intro g g' hgg
    have h1 := congrArg (fun u : ↥(MulAction.stabilizer H x) => (u : H)) hgg
    exact Subtype.ext (Subtype.ext h1)
  have hmul2 := Subgroup.card_mul_index (MulAction.stabilizer ↥CS x)
  rw [MulAction.index_stabilizer] at hmul2
  have hle6 : Nat.card ↥CS ≤ 6 := by
    rw [← hmul2]
    calc Nat.card ↥(MulAction.stabilizer ↥CS x) * (MulAction.orbit ↥CS x).ncard
        ≤ 3 * 2 := Nat.mul_le_mul hstabCS horbcard
      _ = 6 := by norm_num
  omega

theorem no_subnormal_three_of_fix {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (hH : Nat.card H = 24) (x y : X) (S : Set X)
    (hS : ∀ g : H, ∀ s ∈ S, g • s ∈ S) (hx : x ∈ S)
    (hfix : ∀ c : H, c ≠ 1 → c • x = x → ∀ s ∈ S, c • s = s → s = x ∨ s = y)
    (hstab : Nat.card (MulAction.stabilizer H x) = 3)
    (M : Subgroup H) (hM : M.IsSubnormal) (hM1 : M ≠ ⊥) (hMx : ∀ m ∈ M, m • x = x) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hMle : M ≤ MulAction.stabilizer H x := fun m hm => MulAction.mem_stabilizer_iff.2 (hMx m hm)
  have hMdvd : Nat.card M ∣ 3 := hstab ▸ Subgroup.card_dvd_of_le hMle
  have hM3 : Nat.card M = 3 := by
    rcases (Nat.dvd_prime Fact.out).1 hMdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hM1
    · exact h
  have hMp : IsPGroup 3 M := IsPGroup.of_card (n := 1) (by rw [hM3, pow_one])
  have hMq := CFSG.GorensteinWalter.le_qCoreOf_of_isSubnormal_isPGroup (⊤ : Subgroup H) M 3 le_top
    hM.subgroupOf hMp
  set N : Subgroup H := CFSG.GorensteinWalter.qCoreOf (⊤ : Subgroup H) 3 with hN
  have hNnormal : N.Normal := by
    have h1 : (pCore 3 ↥(⊤ : Subgroup H)).Normal := pCore_normal
    exact h1.map (⊤ : Subgroup H).subtype (fun h => ⟨⟨h, trivial⟩, rfl⟩)
  have hNp : IsPGroup 3 N := (pCore_isPGroup (p := 3) (G := ↥(⊤ : Subgroup H))).map _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hNp
  have hk1 : k ≤ 1 := by
    by_contra hk2
    have h9 : 3 ^ 2 ∣ Nat.card N := by rw [hk]; exact Nat.pow_dvd_pow 3 (by omega)
    have h24 : Nat.card N ∣ 24 := hH ▸ Subgroup.card_subgroup_dvd_card N
    have := h9.trans h24
    norm_num at this
  have hNle : Nat.card N ≤ 3 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hMN : M = N := Subgroup.eq_of_le_of_card_ge hMq (by omega)
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hM1
  have hc : orderOf (c : H) = 3 := by
    have h1 : orderOf (c : H) ∣ 3 := hM3 ▸ Subgroup.orderOf_dvd_natCard M c.2
    rcases (Nat.dvd_prime Fact.out).1 h1 with h | h
    · exact absurd (Subtype.ext (by simpa using orderOf_eq_one_iff.1 h)) hc1
    · exact h
  have hzp : zpowers (c : H) = M := by
    apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).2 c.2)
    rw [Nat.card_zpowers, hc, hM3]
  have hcx : (c : H) • x = x := hMx c c.2
  exact not_normal_zpowers_of_fix (c : H) hc hH x y S hS hx hcx
    (hfix c (fun h => hc1 (Subtype.ext h)) hcx) (by omega) (by rw [hzp, hMN]; exact hNnormal)

end CFSG.GH74.Generic.S45
