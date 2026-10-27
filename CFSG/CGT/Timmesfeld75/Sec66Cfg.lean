module

public import CFSG.CGT.Timmesfeld75.Sec57YAlg

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

structure Sec66Cfg (U Tb P : Subgroup G) (y y' : G) (q : ℕ) : Prop where
  wc : IsWC U
  glob : Sec3Global U
  iso : Sec3IsoGlobal U
  hq : 2 ≤ q
  cardU : Nat.card ↥U = q ^ 3
  conjB : ∃ g : G, Tb = conjSubgroup g U
  conjP : ∃ g : G, P = conjSubgroup g U
  neUB : U ≠ Tb
  neUP : U ≠ P
  neBP : Tb ≠ P
  yB : y ∈ Tb
  y'P : y' ∈ P
  y1 : y ≠ 1
  y'1 : y' ≠ 1
  comm : y * y' = y' * y
  yU : y ∈ Subgroup.normalizer (U : Set G)
  y'U : y' ∈ Subgroup.normalizer (U : Set G)
  cardNB : Nat.card ↥(normIn U Tb) = q ^ 2
  cardNP : Nat.card ↥(normIn U P) = q ^ 2
  cardA : Nat.card ↥(normIn U Tb ⊓ normIn U P) ≤ q

section Basic

variable {U Tb P : Subgroup G} {y y' : G} {q : ℕ}

theorem Sec66Cfg.wcB (c : Sec66Cfg U Tb P y y' q) : IsWC Tb := by
  obtain ⟨g, hg⟩ := c.conjB
  exact hg ▸ c.wc.conj g

theorem Sec66Cfg.wcP (c : Sec66Cfg U Tb P y y' q) : IsWC P := by
  obtain ⟨g, hg⟩ := c.conjP
  exact hg ▸ c.wc.conj g

theorem Sec66Cfg.yP (c : Sec66Cfg U Tb P y y' q) : y ∈ Subgroup.normalizer (P : Set G) :=
  c.wcP.centralizer_le_normalizer c.y'P c.y'1 (Subgroup.mem_centralizer_singleton_iff.2 c.comm)

theorem Sec66Cfg.y'B (c : Sec66Cfg U Tb P y y' q) : y' ∈ Subgroup.normalizer (Tb : Set G) :=
  c.wcB.centralizer_le_normalizer c.yB c.y1
    (Subgroup.mem_centralizer_singleton_iff.2 c.comm.symm)

theorem Sec66Cfg.four_le (c : Sec66Cfg U Tb P y y' q) : 4 ≤ q ^ 2 := by
  have := c.hq
  nlinarith

omit [Group G] in
theorem inf_eq_bot_of_conj_conj {G : Type} [Group G] {U A B : Subgroup G} (hU : IsWC U) {a b : G}
    (hA : A = conjSubgroup a U) (hB : B = conjSubgroup b U) (hne : A ≠ B) : A ⊓ B = ⊥ := by
  have hwc : IsWC A := hA ▸ hU.conj a
  have hB' : B = conjSubgroup (b * a⁻¹) A := by
    rw [hA, conjSubgroup_conjSubgroup, mul_assoc, inv_mul_cancel, mul_one, hB]
  have hne' : conjSubgroup (b * a⁻¹) A ≠ A := fun h => hne ((hB'.trans h).symm)
  rw [hB']
  exact hwc.inf_conj_eq_bot hne'

theorem Sec66Cfg.inf_BP (c : Sec66Cfg U Tb P y y' q) : Tb ⊓ P = ⊥ := by
  obtain ⟨g, hg⟩ := c.conjB
  obtain ⟨g', hg'⟩ := c.conjP
  exact inf_eq_bot_of_conj_conj c.wc hg hg' c.neBP

theorem Sec66Cfg.mul_ne_one (c : Sec66Cfg U Tb P y y' q) : y * y' ≠ 1 := by
  intro h
  have hy' : y' = y⁻¹ := eq_inv_of_mul_eq_one_right h
  have : y' ∈ Tb ⊓ P := ⟨hy' ▸ Tb.inv_mem c.yB, c.y'P⟩
  rw [c.inf_BP, Subgroup.mem_bot] at this
  exact c.y'1 this

theorem Sec66Cfg.sec3_B [Finite G] (c : Sec66Cfg U Tb P y y' q) : Sec3 U Tb := by
  obtain ⟨g, hg⟩ := c.conjB
  have hne : conjSubgroup g U ≠ U := by
    rw [← hg]
    exact c.neUB.symm
  have hbot : normIn U (conjSubgroup g U) ≠ ⊥ := by
    rw [← hg]
    intro h
    have h1 := c.cardNB
    rw [h, Subgroup.card_bot] at h1
    have := c.four_le
    omega
  rw [hg]
  exact c.glob g hne hbot

theorem Sec66Cfg.sec3_P [Finite G] (c : Sec66Cfg U Tb P y y' q) : Sec3 U P := by
  obtain ⟨g, hg⟩ := c.conjP
  have hne : conjSubgroup g U ≠ U := by
    rw [← hg]
    exact c.neUP.symm
  have hbot : normIn U (conjSubgroup g U) ≠ ⊥ := by
    rw [← hg]
    intro h
    have h1 := c.cardNP
    rw [h, Subgroup.card_bot] at h1
    have := c.four_le
    omega
  rw [hg]
  exact c.glob g hne hbot

theorem Sec66Cfg.A_ne_bot [Finite G] (c : Sec66Cfg U Tb P y y' q) :
    normIn U Tb ⊓ normIn U P ≠ ⊥ := by
  intro hbot
  have hcomm : ∀ a ∈ normIn U Tb, ∀ b ∈ normIn U P, a * b = b * a := fun a ha b hb =>
    elemAbelian_mul_comm c.wc.1 (normIn_le _ _ ha) (normIn_le _ _ hb)
  have h1 := card_sup_eq_mul_of_commute hcomm hbot
  have h2 : Nat.card ↥(normIn U Tb ⊔ normIn U P) ≤ Nat.card ↥U :=
    Subgroup.card_le_of_le (sup_le (normIn_le _ _) (normIn_le _ _))
  rw [h1, c.cardNB, c.cardNP, c.cardU] at h2
  have hq := c.hq
  have h3 : q ^ 3 < q ^ 2 * q ^ 2 := by
    calc q ^ 3 = q ^ 2 * q := by ring
      _ < q ^ 2 * q ^ 2 := Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
  omega

theorem Sec66Cfg.not_le_sup [Finite G] (c : Sec66Cfg U Tb P y y' q) : ¬ P ≤ U ⊔ Tb := by
  intro hP
  have hS := c.sec3_B
  obtain ⟨s, hs, hsP⟩ := c.sec3_P.conj
  have hsY : s ∈ U ⊔ Tb := (sup_le le_sup_left hP) hs
  have hNn : cfgM U Tb ≤ Subgroup.normalizer (P : Set G) := by
    rw [hsP]
    exact hS.cfgM_le_normalizer_conj hsY
  have hle : normIn U Tb ≤ normIn U P := fun z hz =>
    mem_normIn.2 ⟨normIn_le U Tb hz, hNn (Cfg.normIn_le_cfgM_left U Tb hz)⟩
  have h1 := c.cardA
  rw [inf_eq_left.2 hle, c.cardNB] at h1
  have hq := c.hq
  nlinarith

end Basic

end CFSG.CGT.Timmesfeld75
