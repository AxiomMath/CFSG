module

public import CFSG.CGT.Timmesfeld75.Sec5FiveBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Cfg

variable {G : Type} [Group G] {T T₁ : Subgroup G} {g : G}

structure Sec57Cfg (T T₁ : Subgroup G) (g : G) : Prop where
  hy : StepHyp T T₁
  hS : Sec3Global T
  hI : Sec3IsoGlobal T
  hA : secA T T₁ ≠ ⊥
  hab : ∀ x ∈ secR₁ T T₁, ∀ y ∈ secR₁ T T₁, x * y = y * x
  hg : conjSubgroup g (secA T T₁) ≤ Subgroup.normalizer (T : Set G)
  hgT : conjSubgroup g T ≠ T
  hnu : ¬ IsUIdx T T₁ g
  hcard : Nat.card T < Nat.card (secA T T₁) * Nat.card (normIn T T₁)
  hcomm : ∀ h : G, IsUIdx T T₁ h → ∀ a ∈ conjSubgroup h (secA T T₁),
    ∀ x ∈ conjSubgroup g (secA T T₁), a * x = x * a

variable [Finite G]

omit [Finite G] in
theorem Sec57Cfg.conj_secA_ne_bot (c : Sec57Cfg T T₁ g) : conjSubgroup g (secA T T₁) ≠ ⊥ :=
  fun h => c.hA (conjSubgroup_eq_bot_iff.1 h)

omit [Finite G] in
theorem Sec57Cfg.normIn_ne_bot (c : Sec57Cfg T T₁ g) : normIn (conjSubgroup g T) T ≠ ⊥ := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.conj_secA_ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨a, mem_normIn.2 ⟨conjSubgroup_mono secA_le_left ha,
    c.hg ha⟩⟩, fun h => ha1' (congrArg Subtype.val h)⟩

theorem Sec57Cfg.sec3₃ (c : Sec57Cfg T T₁ g) : Sec3 T (conjSubgroup g T) :=
  c.hS g c.hgT (normIn_ne_bot_of_conj c.hy.pair.wc c.hgT c.normIn_ne_bot)

theorem Sec57Cfg.secA_le_normIn₃ (c : Sec57Cfg T T₁ g) :
    secA T T₁ ≤ normIn T (conjSubgroup g T) := by
  intro x hx
  have hxC := secA_le_centralizer_normD c.hy.pair c.hS hx
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.conj_secA_ne_bot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haT₃ : a ∈ conjSubgroup g T := conjSubgroup_mono secA_le_left ha
  have haD : a ∈ normD T := ⟨mem_classD_of_mem_conjSubgroup haT₃ ha1', c.hg ha⟩
  have hcomm : a * x = x * a := Subgroup.mem_centralizer_iff.1 hxC a haD
  exact mem_normIn.2 ⟨secA_le_left hx, (c.hy.pair.wc.conj g).centralizer_le_normalizer haT₃ ha1'
    (Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm)⟩

theorem Sec57Cfg.card_normIn_lt (c : Sec57Cfg T T₁ g) :
    Nat.card ↥(normIn (conjSubgroup g T) T) < Nat.card ↥(normIn T T₁) := by
  have hle : Nat.card ↥(normIn T (conjSubgroup g T)) ≤ Nat.card ↥(normIn T T₁) :=
    c.hy.pair.maximal g c.hgT
  rw [← c.sec3₃.card_normIn_swap] at hle
  exact lt_of_le_of_ne hle fun h => c.hnu ⟨c.hgT, h⟩

theorem Sec57Cfg.ne_mid (c : Sec57Cfg T T₁ g) : conjSubgroup g T ≠ T₁ := by
  intro h
  have h1 := c.card_normIn_lt
  rw [h, c.hy.pair.sec3 c.hS |>.card_normIn_swap] at h1
  exact lt_irrefl _ h1

theorem two_mul_card_normIn_le_of_maxPair (hP : MaxPair T T₁) :
    2 * Nat.card ↥(normIn T T₁) ≤ Nat.card T := by
  have hlt : Nat.card ↥(normIn T T₁) < Nat.card T := by
    obtain ⟨x, hx⟩ := hP.conj
    have hc : Cfg T T₁ := by
      subst hx
      exact Cfg.of_conj hP.wc hP.ne hP.nontriv
    exact Subgroup.card_lt_of_lt (hc.normIn_lt ⟨x, hx⟩)
  have hdvd : Nat.card ↥(normIn T T₁) ∣ Nat.card T := Subgroup.card_dvd_of_le (normIn_le T T₁)
  have hpos : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  rcases k with _ | _ | k
  · simp at hk
    omega
  · simp at hk
    omega
  · rw [hk]
    nlinarith

@[expose] def sec57Fam (T T₁ T₃ : Subgroup G) : Fin 3 → Subgroup G := ![T, T₁, T₃]

end Cfg

end CFSG.CGT.Timmesfeld75
