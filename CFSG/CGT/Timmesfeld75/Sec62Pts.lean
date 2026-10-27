module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.Sec6Ctx

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G]

structure Sec62Ctx (T T₁ Y : Subgroup G) (n m : ℕ) : Prop where
  ctx : Sec6Ctx T T₁ n m
  hXY : T ⊔ T₁ ≤ Y
  hY : Y ≤ Subgroup.normalizer (cfgM T T₁ : Set G)

section Basic

variable {T T₁ Y : Subgroup G} {n m : ℕ}

theorem Sec62Ctx.conj_cfgM (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y) :
    conjSubgroup y (cfgM T T₁) = cfgM T T₁ :=
  mem_normalizer_iff_conjSubgroup_eq.1 (P.hY hy)

theorem Sec62Ctx.cfgM_le_normalizer (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y) :
    cfgM T T₁ ≤ Subgroup.normalizer (conjSubgroup y T : Set G) := by
  have e := P.conj_cfgM hy
  unfold cfgM at e ⊢
  rw [conjSubgroup_sup_eq_sup] at e
  rw [← e]
  refine sup_le ((conjSubgroup_mono (normIn_le T T₁)).trans Subgroup.le_normalizer) ?_
  rw [← normIn_conj]
  exact inf_le_right

end Basic

section Card

variable [Finite G] {T T₁ Y : Subgroup G} {n m : ℕ}

theorem Sec3.card_sup_eq (hS : Sec3 T T₁) (hI : Sec3Iso T T₁) :
    Nat.card ↥(T ⊔ T₁) = Nat.card ↥(cfgM T T₁) *
      ((Nat.card T / Nat.card ↥(normIn T T₁)) *
        ((Nat.card T / Nat.card ↥(normIn T T₁)) ^ 2 - 1)) := by
  obtain ⟨hN, f, hf, hiso⟩ := hI
  have hX := hS.isL2Pair_quotient hf hiso
  have hcardT := hS.card_eq_mul hf hiso
  have hq : Nat.card T / Nat.card ↥(normIn T T₁) = 2 ^ f := by
    rw [hcardT]
    exact Nat.mul_div_cancel_left _ Nat.card_pos
  rw [hq]
  have hN2 : Nat.card ((cfgM T T₁).subgroupOf (T ⊔ T₁)) = Nat.card ↥(cfgM T T₁) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cfgM_le_sup T T₁)).toEquiv
  have h1 := Subgroup.card_mul_index ((cfgM T T₁).subgroupOf (T ⊔ T₁))
  rw [Subgroup.index_eq_card, hX.card_eq_mul, hN2] at h1
  exact h1.symm

theorem Sec62Ctx.normIn_conj_eq (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y)
    (hne : conjSubgroup y T ≠ T) : normIn T (conjSubgroup y T) = normIn T T₁ :=
  (Subgroup.eq_of_le_of_card_ge (fun _ hz => mem_normIn.2 ⟨normIn_le T T₁ hz,
    P.cfgM_le_normalizer hy (Cfg.normIn_le_cfgM_left T T₁ hz)⟩)
    (P.ctx.hy.pair.maximal y hne)).symm

theorem Sec62Ctx.sec3_conj (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y)
    (hne : conjSubgroup y T ≠ T) : Sec3 T (conjSubgroup y T) :=
  P.ctx.hS y hne (by rw [P.normIn_conj_eq hy hne]; exact P.ctx.sec3.cfg.ne)

theorem Sec62Ctx.sec3Iso_conj (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y)
    (hne : conjSubgroup y T ≠ T) : Sec3Iso T (conjSubgroup y T) :=
  P.ctx.hI y hne (by rw [P.normIn_conj_eq hy hne]; exact P.ctx.sec3.cfg.ne)

theorem Sec62Ctx.cfgM_conj_eq (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y)
    (hne : conjSubgroup y T ≠ T) : cfgM T (conjSubgroup y T) = cfgM T T₁ := by
  have hS := P.sec3_conj hy hne
  have hnei : conjSubgroup y⁻¹ T ≠ T := fun h => hne (by
    have := congrArg (conjSubgroup y) h
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] at this
    exact this.symm)
  have h1 : normIn (conjSubgroup y T) T = conjSubgroup y (normIn T T₁) := by
    have := normIn_conj y T (conjSubgroup y⁻¹ T)
    rwa [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one,
      P.normIn_conj_eq (Y.inv_mem hy) hnei] at this
  have hle : cfgM T (conjSubgroup y T) ≤ cfgM T T₁ := by
    refine sup_le ?_ ?_
    · rw [P.normIn_conj_eq hy hne]
      exact Cfg.normIn_le_cfgM_left T T₁
    · rw [h1]
      exact (conjSubgroup_mono (Cfg.normIn_le_cfgM_left T T₁)).trans (P.conj_cfgM hy).le
  have hcard : Nat.card (cfgM T T₁) ≤ Nat.card (cfgM T (conjSubgroup y T)) := by
    rw [P.ctx.sec3.card_cfgM_eq_sq, hS.card_cfgM_eq_sq, P.normIn_conj_eq hy hne]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem Sec62Ctx.card_sup_conj (P : Sec62Ctx T T₁ Y n m) {y : G} (hy : y ∈ Y)
    (hne : conjSubgroup y T ≠ T) :
    Nat.card ↥(T ⊔ conjSubgroup y T) =
      Nat.card ↥(cfgM T T₁) * (2 ^ m * ((2 ^ m) ^ 2 - 1)) := by
  rw [(P.sec3_conj hy hne).card_sup_eq (P.sec3Iso_conj hy hne), P.cfgM_conj_eq hy hne,
    P.normIn_conj_eq hy hne, P.ctx.hq]

end Card

end CFSG.CGT.Timmesfeld75
