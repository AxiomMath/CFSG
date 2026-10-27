module

public import CFSG.LieType.SeitzGeneration.SpAnisoBlocks
public import CFSG.LieType.SeitzGeneration.SpSubEmb
public import CFSG.LieType.SeitzGeneration.HyperPlaneCube
public import CFSG.LieType.SeitzGeneration.SpFourThree
public import CFSG.RankThree.PartOne.CTP.SeitzSpGeneration

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.CTP CFSG.Open Module

variable {p r : ℕ} {K : Type} [Field K] {A : Subgroup (StatedSp r K)}

namespace SpAnisoSetup

variable (S : SpAnisoSetup p r K A)
include S

theorem isElemAbelian : IsElemAbelian p A :=
  ⟨⟨⟨fun a b => S.comm' a b⟩⟩, S.pow_eq_one⟩

theorem pair_nondeg [Finite K] {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) :
    ((spForm r K).restrict (hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂)).Nondegenerate := by
  set U := hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂ with hU
  have hrefl : ((spForm r K).restrict U).IsRefl :=
    (show ((spForm r K).restrict U).IsAlt from
      fun w => spForm_isAlt (w : Fin r ⊕ Fin r → K)).isRefl
  refine hrefl.nondegenerate_iff_separatingLeft.mpr fun x hx => ?_
  obtain ⟨x₁, hx₁, x₂, hx₂, hxx⟩ := Submodule.mem_sup.mp x.2
  have h₁ : x₁ = 0 := by
    have := (S.blk_nondeg hF₁).1 ⟨x₁, hx₁⟩ fun y => by
      have h := hx ⟨y, Submodule.mem_sup_left y.2⟩
      change spForm r K (x : Fin r ⊕ Fin r → K) y = 0 at h
      rw [← hxx, map_add, LinearMap.add_apply, S.blk_orth hF₂ hF₁ (Ne.symm hne) hx₂ y.2,
        add_zero] at h
      exact h
    exact congrArg Subtype.val this
  have h₂ : x₂ = 0 := by
    have := (S.blk_nondeg hF₂).1 ⟨x₂, hx₂⟩ fun y => by
      have h := hx ⟨y, Submodule.mem_sup_right y.2⟩
      change spForm r K (x : Fin r ⊕ Fin r → K) y = 0 at h
      rw [← hxx, map_add, LinearMap.add_apply, S.blk_orth hF₁ hF₂ hne hx₁ y.2, zero_add] at h
      exact h
    exact congrArg Subtype.val this
  apply Subtype.ext
  rw [← hxx, h₁, h₂, add_zero]
  rfl

theorem le_spStab_pair (F₁ F₂ : Subgroup A) :
    A ≤ spStab (hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂) := by
  intro a ha u hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  refine ⟨?_, ?_⟩
  · rw [map_add]
    exact Submodule.add_mem_sup (S.blk_stable F₁ ⟨a, ha⟩ hu₁) (S.blk_stable F₂ ⟨a, ha⟩ hu₂)
  · rw [map_add]
    exact Submodule.add_mem_sup (S.blk_stable F₁ ⟨a, ha⟩⁻¹ hu₁) (S.blk_stable F₂ ⟨a, ha⟩⁻¹ hu₂)

theorem finrank_pair [Finite K] {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p)
    (hne : F₁ ≠ F₂) :
    finrank K (hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂ : Submodule K _) =
      finrank K (hyperFixed (spRep A) F₁) + finrank K (hyperFixed (spRep A) F₂) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (hyperFixed (spRep A) F₁)
    (hyperFixed (spRep A) F₂)
  rw [S.blk_inf_eq_bot hF₁ hF₂ hne, finrank_bot, add_zero] at h
  exact h

theorem range_ext_le_hyperClosure [Finite K] (hq : ¬ (p = 3 ∧ Nat.card K = 2))
    {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p) (hne : F₁ ≠ F₂)
    (h₁ : hyperFixed (spRep A) F₁ ≠ ⊥) (h₂ : hyperFixed (spRep A) F₂ ≠ ⊥) {m : ℕ}
    (e : SpSubEmb r m K) (heU : e.U = hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂)
    (hm : finrank K e.U = 2 * m) :
    e.ext.range ≤ hyperClosure p ⊤ A := by
  classical
  have hfa := S.fact
  have := S.finite
  have hAstab : A ≤ spStab e.U := heU ▸ S.le_spStab_pair F₁ F₂
  set ψ : A →* StatedSp m K := e.res.comp (Subgroup.inclusion hAstab) with hψ
  have hψa : ∀ a : A, ψ a = e.res ⟨a, hAstab a.2⟩ := fun a => rfl
  have hker : ∀ a : A, ψ a = 1 ↔ a ∈ F₁ ⊓ F₂ := by
    intro a
    rw [hψa, e.res_eq_one_iff]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · by_contra ha
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
        have hvU : v ∈ e.U := by rw [heU]; exact Submodule.mem_sup_left hv
        exact hv0 (S.eq_zero_of_fixed hF₁ ha hv (h v hvU))
      · by_contra ha
        obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
        have hvU : v ∈ e.U := by rw [heU]; exact Submodule.mem_sup_right hv
        exact hv0 (S.eq_zero_of_fixed hF₂ ha hv (h v hvU))
    · rintro ⟨ha₁, ha₂⟩ u hu
      rw [heU] at hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
      change spRep A a (u₁ + u₂) = u₁ + u₂
      rw [map_add, mem_hyperFixed.1 hu₁ a ha₁, mem_hyperFixed.1 hu₂ a ha₂]
  have hkerEq : ψ.ker = F₁ ⊓ F₂ := by
    ext a
    rw [MonoidHom.mem_ker]
    exact hker a
  have hrange : Nat.card ψ.range = p ^ 2 := by
    have h := Subgroup.card_ker_mul_card_range ψ
    rw [hkerEq, S.card_inf hF₁ hF₂ hne, S.card_eq] at h
    have : p * Nat.card ψ.range = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left S.prime.pos this
  have hrangeEl : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      apply Subtype.ext
      change (x : StatedSp m K) * y = y * x
      rw [← ha, ← hb, ← map_mul, ← map_mul, S.comm' a b]
    · obtain ⟨a, rfl⟩ := hx
      rw [← map_pow, S.pow' a, map_one]
  have hdim₁ := S.two_le_finrank h₁
  have hdim₂ := S.two_le_finrank h₂
  have hdimU : finrank K e.U = finrank K (hyperFixed (spRep A) F₁) +
      finrank K (hyperFixed (spRep A) F₂) := by
    rw [heU]; exact S.finrank_pair hF₁ hF₂ hne
  have hplane : Subgroup.closure {g : StatedSp m K | ∃ x ∈ ψ.range, x ≠ 1 ∧ g * x = x * g} =
      ⊤ := by
    have := Fintype.ofFinite K
    obtain ⟨ℓ, hchar, n, hℓ, hcardK⟩ := FiniteField.card' K
    have hcardK' : Nat.card K = ℓ ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcardK]
    have hpℓ : p ≠ ℓ := by
      rintro rfl
      exact S.cast_ne_zero (CharP.cast_eq_zero K p)
    rcases eq_or_ne p 3 with hp3 | hp3
    ·
      have hle₁ := S.finrank_le_two_of_three hp3 hF₁
      have hle₂ := S.finrank_le_two_of_three hp3 hF₂
      have hm2 : m = 2 := by omega
      subst hm2
      have h3K : (3 : K) ≠ 0 := by
        have := S.cast_ne_zero
        rwa [hp3] at this
      have hK : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hq ⟨hp3, ?_⟩
        have hle : Fintype.card K ≤ 2 := by
          have : (Finset.univ : Finset K) ⊆ {0, 1} := fun c _ => by
            by_cases hc : c = 0
            · simp [hc]
            · simp [hcon c hc]
          calc Fintype.card K = (Finset.univ : Finset K).card := Finset.card_univ.symm
            _ ≤ ({0, 1} : Finset K).card := Finset.card_le_card this
            _ ≤ 2 := Finset.card_le_two
        have h2 : 1 < Fintype.card K := Fintype.one_lt_card
        rw [Nat.card_eq_fintype_card]
        omega
      exact closure_centralizers_spFour_three h3K hK
        (fun x hx y hy => congrArg Subtype.val (hrangeEl.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
        (fun x hx => hp3 ▸ hrangeEl.2 x hx) (by rw [hrange, hp3]; norm_num)
    ·
      have hp5 : 3 < p := by
        have := S.prime.two_le
        have h2 := S.ne_two
        omega
      have hm2 : 2 ≤ m := by omega
      have hnex : ¬ (m = 2 ∧ ℓ ^ (n : ℕ) = 2) := by
        rintro ⟨rfl, hq2⟩
        have hd₁ : finrank K (hyperFixed (spRep A) F₁) = 2 := by omega
        have hcard : Nat.card (hyperFixed (spRep A) F₁) = 4 := by
          rw [Module.natCard_eq_pow_finrank (K := K), hd₁, hcardK', hq2]
          norm_num
        have hmod := S.card_blk_modEq F₁
        rw [hcard] at hmod
        have hdvd : p ∣ 3 := by
          have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 4)).mp hmod.symm
          simpa using this
        have := (Nat.prime_dvd_prime_iff_eq S.prime Nat.prime_three).mp hdvd
        omega
      have hS : SpPlaneSetup ℓ n p m K ψ.range :=
        { prime_ell := hℓ
          one_le_f := n.pos
          card_K := hcardK'
          prime_p := S.prime
          three_lt_p := hp5
          ne_char := hpℓ
          two_le_r := hm2
          not_exceptional := hnex
          elem := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).2 hrangeEl
          card_plane := hrange }
      exact closure_centralizers_spPlane hS
  obtain ⟨f, hf, hf1⟩ : ∃ f : A, f ∈ F₁ ⊓ F₂ ∧ f ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F₁ ⊓ F₂ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hcon
    have := S.card_inf hF₁ hF₂ hne
    rw [hbot, Subgroup.card_bot] at this
    exact S.prime.one_lt.ne this
  have hψf : ψ f = 1 := (hker f).2 hf
  refine le_hyperClosure_of_plane S.prime S.isElemAbelian S.card_eq f.2
    (fun h => hf1 (Subtype.ext h)) le_top ?_ ?_
  · rintro _ ⟨g, rfl⟩
    refine e.commute_ext ⟨f, hAstab f.2⟩ ?_
    change ψ f * g = g * ψ f
    rw [hψf, one_mul, mul_one]
  · have key : e.ext.range =
        Subgroup.closure (e.ext '' {g | ∃ x ∈ ψ.range, x ≠ 1 ∧ g * x = x * g}) := by
      rw [MonoidHom.range_eq_map, ← hplane, MonoidHom.map_closure]
    intro l hl
    rw [key] at hl
    refine Subgroup.closure_mono ?_ hl
    rintro _ ⟨g, ⟨x, ⟨a, rfl⟩, hx1, hgx⟩, rfl⟩
    refine ⟨⟨g, rfl⟩, a, a.2, ?_, ?_⟩
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hx1
      have : a = f ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
      rw [this, map_zpow, hψf, one_zpow]
    · exact e.commute_ext ⟨a, hAstab a.2⟩ hgx.symm

theorem transCenter_of_mem_pair [Finite K] (hq : ¬ (p = 3 ∧ Nat.card K = 2))
    {F₁ F₂ : Subgroup A} (hF₁ : F₁.index = p) (hF₂ : F₂.index = p) (hne : F₁ ≠ F₂)
    (h₁ : hyperFixed (spRep A) F₁ ≠ ⊥) (h₂ : hyperFixed (spRep A) F₂ ≠ ⊥)
    {u : Fin r ⊕ Fin r → K} (hu : u ∈ hyperFixed (spRep A) F₁ ⊔ hyperFixed (spRep A) F₂) :
    TransCenter (hyperClosure p ⊤ A) u := by
  obtain ⟨m, e, heU, hm⟩ := SpSubEmb.exists (S.pair_nondeg hF₁ hF₂ hne)
  have hL := S.range_ext_le_hyperClosure hq hF₁ hF₂ hne h₁ h₂ e heU (heU ▸ hm)
  intro t
  rw [← heU] at hu
  obtain ⟨x, hx⟩ : ∃ x, (e.φ x : Fin r ⊕ Fin r → K) = u := ⟨e.φ.symm ⟨u, hu⟩, by simp⟩
  rw [← hx, ← e.ext_spTransvection]
  exact hL ⟨_, rfl⟩

end SpAnisoSetup

end CFSG.LieType.SeitzGeneration
