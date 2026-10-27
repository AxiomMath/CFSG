module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSquare

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

theorem quaternionTwo_not_commute : ∀ g g' : QuaternionGroup 2,
    (g ≠ 1 ∧ g ≠ .a 2) → (g' ≠ 1 ∧ g' ≠ .a 2) → (g * g'⁻¹ ≠ 1 ∧ g * g'⁻¹ ≠ .a 2) →
      g * g' ≠ g' * g := by
  decide

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

omit [Finite G] h [J.Normal] in
theorem quaternionElt_injective (P : Sylow 2 J) (eP : (P : Subgroup J) ≃* QuaternionGroup 2) :
    Function.Injective (quaternionElt P eP) := fun _ _ hg =>
  eP.symm.injective (Subtype.ext (Subtype.ext hg))

omit [Finite G] h [J.Normal] in
theorem quaternionElt_mul (P : Sylow 2 J) (eP : (P : Subgroup J) ≃* QuaternionGroup 2)
    (g g' : QuaternionGroup 2) :
    quaternionElt P eP (g * g') = quaternionElt P eP g * quaternionElt P eP g' := by
  simp [quaternionElt]

theorem not_isCyclic_sylowImage_inf_centralizer :
    ¬ IsCyclic (escapingSylowImage S z ⊓ Subgroup.centralizer (J : Set (EscapingQuotient z)) :
      Subgroup (EscapingQuotient z)) := by
  intro hcyc
  have hq := h.quotientData
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  set K := Subgroup.centralizer (J : Set (EscapingQuotient z)) with hK
  have hcomm : ∀ c ∈ escapingSylowImage S z ⊓ K, ∀ c' ∈ escapingSylowImage S z ⊓ K,
      c * c' = c' * c := fun c hc c' hc' => by
    have := (IsCyclic.isMulCommutative (α := (escapingSylowImage S z ⊓ K :
      Subgroup (EscapingQuotient z)))).is_comm.comm ⟨c, hc⟩ ⟨c', hc'⟩
    exact congrArg Subtype.val this
  have hrank : CFSG.Open.pRank 2 (escapingSylowImage S z) ≤ 2 := by
    apply CFSG.SectionRank.pRank_le (by decide)
    intro E hES hE
    set ψ : E →* MulAut (J ⧸ Subgroup.center J) := (componentQuotientAction J).comp E.subtype
    have hdec : ∀ e ∈ E, ∃ g : QuaternionGroup 2, ∃ c ∈ escapingSylowImage S z ⊓ K,
        quaternionElt P eP g * c = e := by
      intro e he
      have he2 : e * e = 1 := by rw [← pow_two]; exact hE.2 e he
      have heJK := (h.action_mem_inner_iff).mp
        (h.action_mem_inner_of_mul_self_eq_one (hES he) he2)
      obtain ⟨q, hqS, hqJ, c, hcS, hcK, hqc⟩ := h.exists_mul_eq_of_mem_sup (hES he) heJK
      obtain ⟨g, rfl⟩ := exists_quaternionElt_eq P hP eP hqS hqJ
      exact ⟨g, c, ⟨hcS, hcK⟩, hqc⟩
    have hact : ∀ g : QuaternionGroup 2, ∀ c ∈ escapingSylowImage S z ⊓ K,
        componentQuotientAction J (quaternionElt P eP g * c) =
          MulAut.conj (quaternionMap P eP g) := fun g c hc => by
      rw [map_mul, (h.action_eq_one_iff).mpr hc.2, mul_one, action_quaternionElt]
    have hker : Nat.card ψ.ker ≤ 2 := by
      apply card_le_two_of_forall_ne_one
      have hmem : ∀ x : ψ.ker, x ≠ 1 → ((x : E) : EscapingQuotient z) = escapingBar z := by
        rintro ⟨⟨a, ha⟩, ha'⟩ ha1
        have haK : a ∈ K := (h.action_eq_one_iff).mp (MonoidHom.mem_ker.mp ha')
        have ha1' : a ≠ 1 := fun h1 => ha1 (by subst h1; rfl)
        exact h.eq_bar_of_mem_centralizer (hES ha) haK (orderOf_eq_prime (hE.2 a ha) ha1')
      intro x y hx hy
      exact Subtype.ext (Subtype.ext ((hmem x hx).trans (hmem y hy).symm))
    have hrange : Nat.card ψ.range ≤ 2 := by
      apply card_le_two_of_forall_ne_one
      rintro ⟨_, ⟨⟨e₁, he₁⟩, rfl⟩⟩ ⟨_, ⟨⟨e₂, he₂⟩, rfl⟩⟩ h1 h2
      obtain ⟨g₁, c₁, hc₁, rfl⟩ := hdec e₁ he₁
      obtain ⟨g₂, c₂, hc₂, rfl⟩ := hdec e₂ he₂
      apply Subtype.ext
      change componentQuotientAction J (quaternionElt P eP g₁ * c₁) =
        componentQuotientAction J (quaternionElt P eP g₂ * c₂)
      rw [hact g₁ c₁ hc₁, hact g₂ c₂ hc₂]
      have hne1 : ∀ g : QuaternionGroup 2, ∀ c ∈ escapingSylowImage S z ⊓ K,
          componentQuotientAction J (quaternionElt P eP g * c) ≠ 1 →
          quaternionMap P eP g ≠ 1 := fun g c hc hne hg => hne (by
            rw [hact g c hc, hg, map_one])
      have h1' : componentQuotientAction J (quaternionElt P eP g₁ * c₁) ≠ 1 :=
        fun h' => h1 (Subtype.ext h')
      have h2' : componentQuotientAction J (quaternionElt P eP g₂ * c₂) ≠ 1 :=
        fun h' => h2 (Subtype.ext h')
      by_contra hneq
      have hg₁ : g₁ ≠ 1 ∧ g₁ ≠ .a 2 := by
        have := (h.quaternionMap_eq_one_iff P eP g₁).not.mp (hne1 g₁ c₁ hc₁ h1')
        push Not at this
        exact this
      have hg₂ : g₂ ≠ 1 ∧ g₂ ≠ .a 2 := by
        have := (h.quaternionMap_eq_one_iff P eP g₂).not.mp (hne1 g₂ c₂ hc₂ h2')
        push Not at this
        exact this
      have hg₁₂ : g₁ * g₂⁻¹ ≠ 1 ∧ g₁ * g₂⁻¹ ≠ .a 2 := by
        have h3 : quaternionMap P eP (g₁ * g₂⁻¹) ≠ 1 := fun h3 => hneq (by
          rw [map_mul, map_inv, mul_inv_eq_one] at h3
          rw [h3])
        have := (h.quaternionMap_eq_one_iff P eP _).not.mp h3
        push Not at this
        exact this
      apply quaternionTwo_not_commute g₁ g₂ hg₁ hg₂ hg₁₂
      apply (quaternionElt_injective P eP)
      have hEc := hE.1.is_comm.comm ⟨_, he₁⟩ ⟨_, he₂⟩
      have hEc' := congrArg Subtype.val hEc
      simp only [Subgroup.coe_mul] at hEc'
      rw [quaternionElt_mul P eP, quaternionElt_mul P eP]
      have hc₁q : quaternionElt P eP g₂ * c₁ = c₁ * quaternionElt P eP g₂ :=
        (Subgroup.mem_centralizer_iff.mp hc₁.2 _ (quaternionElt_mem P eP g₂))
      have hc₂q : quaternionElt P eP g₁ * c₂ = c₂ * quaternionElt P eP g₁ :=
        (Subgroup.mem_centralizer_iff.mp hc₂.2 _ (quaternionElt_mem P eP g₁))
      have hcc := hcomm c₁ hc₁ c₂ hc₂
      have h4 : quaternionElt P eP g₁ * quaternionElt P eP g₂ * (c₁ * c₂) =
          quaternionElt P eP g₂ * quaternionElt P eP g₁ * (c₁ * c₂) := by
        calc quaternionElt P eP g₁ * quaternionElt P eP g₂ * (c₁ * c₂) =
            quaternionElt P eP g₁ * (quaternionElt P eP g₂ * c₁) * c₂ := by group
          _ = quaternionElt P eP g₁ * (c₁ * quaternionElt P eP g₂) * c₂ := by rw [hc₁q]
          _ = quaternionElt P eP g₁ * c₁ * (quaternionElt P eP g₂ * c₂) := by group
          _ = quaternionElt P eP g₂ * c₂ * (quaternionElt P eP g₁ * c₁) := hEc'
          _ = quaternionElt P eP g₂ * (c₂ * quaternionElt P eP g₁) * c₁ := by group
          _ = quaternionElt P eP g₂ * (quaternionElt P eP g₁ * c₂) * c₁ := by rw [← hc₂q]
          _ = quaternionElt P eP g₂ * quaternionElt P eP g₁ * (c₂ * c₁) := by group
          _ = quaternionElt P eP g₂ * quaternionElt P eP g₁ * (c₁ * c₂) := by rw [hcc]
      exact mul_right_cancel h4
    calc Nat.card E = Nat.card ψ.ker * ψ.ker.index := (Subgroup.card_mul_index _).symm
      _ = Nat.card ψ.ker * Nat.card ψ.range := by rw [Subgroup.index_ker]
      _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
      _ = 2 ^ 2 := by norm_num
  have h3 := hq.rank
  rw [← sylow_two_rank_eq (sylowBarSylow h.square.central), h.coe_sylow] at h3
  omega

theorem exists_sq_eq_bar_not_mem
    {w₀ : EscapingQuotient z} (hw₀S : w₀ ∈ escapingSylowImage S z)
    (hw₀ : w₀ ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    ∃ y ∈ escapingSylowImage S z, y ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧
      y ^ 2 = escapingBar z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w, hwS, hwJK, hw2⟩ := h.exists_sq_mem_centralizer hw₀S hw₀
  set K := Subgroup.centralizer (J : Set (EscapingQuotient z)) with hK
  set QK := escapingSylowImage S z ⊓ K with hQK
  set P₁ := QK ⊔ Subgroup.zpowers w with hP₁
  have hP₁S : P₁ ≤ escapingSylowImage S z := sup_le inf_le_left (Subgroup.zpowers_le.mpr hwS)
  have hφw2 : componentQuotientAction J w * componentQuotientAction J w = 1 := by
    rw [← map_mul, (h.action_eq_one_iff).mpr hw2]
  have himg : ∀ p ∈ P₁, componentQuotientAction J p = 1 ∨
      componentQuotientAction J p = componentQuotientAction J w := by
    intro p hp
    have hp' : componentQuotientAction J p ∈ P₁.map (componentQuotientAction J) :=
      Subgroup.mem_map_of_mem _ hp
    have hQKφ : QK.map (componentQuotientAction J) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨c, hc, rfl⟩
      exact (h.action_eq_one_iff).mpr hc.2
    rw [hP₁, Subgroup.map_sup, MonoidHom.map_zpowers, hQKφ, bot_sup_eq] at hp'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp'
    have hsq : componentQuotientAction J w ^ 2 = 1 := by rw [pow_two, hφw2]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← hk, ← two_mul, zpow_mul, zpow_two, hφw2, one_zpow]
    · right
      rw [← hk, zpow_add, zpow_mul, zpow_two, hφw2, one_zpow, one_mul, zpow_one]
  have hφwi : componentQuotientAction J w ∉ inner (J ⧸ Subgroup.center J) := fun hi =>
    hwJK ((h.action_mem_inner_iff).mp hi)
  have huniq : ∀ p ∈ P₁, orderOf p = 2 → p = escapingBar z := by
    intro p hp hp2
    have hpS := hP₁S hp
    have hp2' : p * p = 1 := by
      have := pow_orderOf_eq_one p
      rwa [hp2, pow_two] at this
    have hin := h.action_mem_inner_of_mul_self_eq_one hpS hp2'
    rcases himg p hp with h1 | h1
    · exact h.eq_bar_of_mem_centralizer hpS ((h.action_eq_one_iff).mp h1) hp2
    · exact absurd (h1 ▸ hin) hφwi
  have hP₁2 : IsPGroup 2 P₁ := h.sylowImage_isPGroup.to_le hP₁S
  have hrank : twoRank P₁ ≤ 1 := by
    have := pRank_two_le_one_of_forall_involution_eq h.quotientData.bar_order huniq
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 2 (by decide)] at this
  rcases CFSG.TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion P₁ hP₁2 hrank with
    hcyc | ⟨n, hn, ⟨e₁⟩⟩
  · exact absurd (Subgroup.isCyclic_of_le (le_sup_left : QK ≤ P₁))
      h.not_isCyclic_sylowImage_inf_centralizer
  set m := 2 ^ (n - 2) with hm
  have hm0 : 0 < m := by positivity
  have hex : ∃ i : ZMod (2 * m), ((e₁.symm (QuaternionGroup.xa i) : P₁) : EscapingQuotient z) ∉
      QK := by
    by_contra hall
    push Not at hall
    have hallP : ∀ p : P₁, (p : EscapingQuotient z) ∈ QK := by
      intro p
      rw [← e₁.symm_apply_apply p]
      rcases hep : e₁ p with j | j
      · have hj : (QuaternionGroup.a j : QuaternionGroup m) =
            QuaternionGroup.xa 0 * QuaternionGroup.xa (j - (m : ZMod (2 * m))) := by
          rw [QuaternionGroup.xa_mul_xa]
          congr 1
          ring
        rw [hj, map_mul, Subgroup.coe_mul]
        exact QK.mul_mem (hall 0) (hall _)
      · exact hall j
    exact hwJK (Subgroup.mem_sup_right
      (hallP ⟨w, Subgroup.mem_sup_right (Subgroup.mem_zpowers w)⟩).2)
  obtain ⟨i, hi⟩ := hex
  set y : P₁ := e₁.symm (QuaternionGroup.xa i) with hy
  refine ⟨y, hP₁S y.2, fun hyJK => ?_, ?_⟩
  · rcases himg y y.2 with h1 | h1
    · exact hi ⟨hP₁S y.2, (h.action_eq_one_iff).mp h1⟩
    · exact hφwi (h1 ▸ (h.action_mem_inner_iff).mpr hyJK)
  · have hy2 : (y : EscapingQuotient z) ^ 2 =
        ((e₁.symm (QuaternionGroup.a (m : ZMod (2 * m))) : P₁) : EscapingQuotient z) := by
      rw [← Subgroup.coe_pow, hy, ← map_pow, QuaternionGroup.xa_sq]
    rw [hy2]
    refine huniq _ (e₁.symm _).2 ?_
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, QuaternionGroup.a_mul_a, ← Nat.cast_add, ← two_mul, ZMod.natCast_self,
        ← QuaternionGroup.one_def]
    · rw [Ne, QuaternionGroup.one_def, QuaternionGroup.a.injEq, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd hm0 hdvd
      omega

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
