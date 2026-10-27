module

public import CFSG.LargeExtraspecial.AS35ISE
public import CFSG.Goldschmidt.Steps.G3aBorel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.Asc22

open Subgroup CFSG.Open

variable {X : Type} [Group X] {Q M : Subgroup X}

theorem fusionIsBenderGroup_transport {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.Open.fusionIsBenderGroup A) : CFSG.Open.fusionIsBenderGroup B := by
  rcases hA with ⟨f, hf, ⟨m⟩⟩ | ⟨f, hf, ⟨m⟩⟩ | ⟨a, ha, ⟨m⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans m⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans m⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans m⟩⟩)

namespace AbsTI

variable (h : AbsTI X Q M)
include h

omit h in
theorem exists_two [Finite X] (hQ2 : 2 < Nat.card Q) :
    ∃ a ∈ Q, ∃ b ∈ Q, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have hQ1 : Q ≠ ⊥ := fun h1 => by
    rw [h1, card_bot] at hQ2
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := (ne_bot_iff_exists_ne_one).1 hQ1
  have ha1' : a ≠ 1 := fun h1 => ha1 (Subtype.ext h1)
  by_contra hcon
  push Not at hcon
  have hcases : ∀ b : Q, (b : X) = 1 ∨ (b : X) = a := fun b => by
    by_cases hb : (b : X) = 1
    · exact Or.inl hb
    · exact Or.inr (hcon a ha b b.2 ha1' hb).symm
  have hle : Nat.card Q ≤ Nat.card Bool := by
    refine Nat.card_le_card_of_injective (fun b : Q => decide ((b : X) = a)) ?_
    intro b c hbc
    apply Subtype.ext
    rcases hcases b with hb | hb <;> rcases hcases c with hc | hc
    · rw [hb, hc]
    · simp [hb, hc, Ne.symm ha1'] at hbc
    · simp [hb, hc, Ne.symm ha1'] at hbc
    · rw [hb, hc]
  have hB2 : Nat.card Bool = 2 := by simp
  omega

theorem borel_facts [Finite X] [IsSimpleGroup X] (hQ1 : Q ≠ ⊥) (hM : M ≠ ⊤)
    (hSE : fusionStronglyEmbedded M) {T : Sylow 2 X} (hQT : Q ≤ T) (hTM : (T : Subgroup X) ≤ M)
    {D : Subgroup X} (hD : CFSG.Goldschmidt.G3a.BorelSetup T D) :
    M = normalizer ((T : Subgroup X) : Set X) ∧ M.index = Nat.card (T : Subgroup X) + 1 ∧
      Q = CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMN : M = normalizer ((T : Subgroup X) : Set X) := by
    refine le_antisymm (hD.le_normalizer_of_le hTM hM) ?_
    intro g hg
    by_contra hgM
    have hodd := hSE.2.2 g hgM
    have hTle : (T : Subgroup X) ≤ M ⊓ M.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro t ht
      refine mem_inf.2 ⟨hTM ht, CFSG.Timmesfeld.Bridge.mem_map_conj_inv_iff.2 (hTM ?_)⟩
      exact (mem_normalizer_iff.1 hg t).1 ht
    have hdvd := card_dvd_of_le hTle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 T.isPGroup'
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hQ1
      rw [eq_bot_iff, ← eq_bot_of_card_eq (T : Subgroup X) (by rw [hk, pow_zero])]
      exact hQT
    have h2 : 2 ∣ Nat.card (T : Subgroup X) := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    obtain ⟨r, hr⟩ := hodd
    have := h2.trans hdvd
    omega
  refine ⟨hMN, ?_, ?_⟩
  · rw [hMN]
    exact (Sylow.card_eq_index_normalizer T).symm.trans hD.card
  · apply le_antisymm
    · intro q hq
      exact hD.inv q (hQT hq) (by rw [pow_two, h.sq q hq])
    · intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact Q.one_mem
      obtain ⟨⟨q, hq⟩, hq1⟩ := (ne_bot_iff_exists_ne_one).1 hQ1
      have hq1' : q ≠ 1 := fun h1 => hq1 (Subtype.ext h1)
      obtain ⟨d, hd, hdx⟩ := hD.trans (hD.inv q (hQT hq) (by rw [pow_two, h.sq q hq])) hx hq1'
        hx1
      have hdM : d ∈ M := hMN ▸ hD.le hd
      have := h.norm d⁻¹ (M.inv_mem hdM) q hq
      rw [inv_inv] at this
      rwa [← hdx]


theorem fusionIsBenderGroup [Finite X] (hQ2 : 2 < Nat.card Q) (hM : M ≠ ⊤)
    (hcl : normalClosure (Q : Set X) = ⊤) (huniq : ∀ H : Subgroup X, Q ≤ H → H ≠ ⊤ → H ≤ M)
    (hcore : ∀ Y : Subgroup X, Y.Normal → Y ≤ M → Y = ⊥) : CFSG.Open.fusionIsBenderGroup X := by
  have hQ1 : Q ≠ ⊥ := fun h1 => by
    rw [h1, card_bot] at hQ2
    omega
  have hSE := h.stronglyEmbedded hQ1 hM hcl
  rcases bender_strongly_embedded_normal_series X M hSE with
    hSyl | ⟨M₀, N₀, hM₀, hN₀, hM₀N₀, hle, hM₀o, hN₀o, hB⟩
  · exfalso
    have hNC := CFSG.Timmesfeld.Bridge.noCommutingDistinctInvolutions_of_sylow hSyl
    obtain ⟨a, ha, b, hb, ha1, hb1, hab⟩ := exists_two hQ2
    have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two, h.sq a ha]) ha1
    have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two, h.sq b hb]) hb1
    exact hab (congrArg Subtype.val (hNC ⟨a, ha2⟩ ⟨b, hb2⟩ (h.comm a ha b hb)))
  · have hQN₀ : Q ≤ N₀ := fun q hq =>
      CFSG.Timmesfeld.Bridge.mem_of_odd_index hN₀o (h.sq q hq)
    have hN₀top : N₀ = ⊤ := by
      rw [eq_top_iff, ← hcl]
      exact normalClosure_le_normal hQN₀
    have hcardN₀ : Nat.card ↥N₀ = Nat.card (↥N₀ ⧸ M₀.subgroupOf N₀) * Nat.card M₀ := by
      rw [card_eq_card_quotient_mul_card_subgroup (M₀.subgroupOf N₀)]
      congr 1
      exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    have hQ2grp : IsPGroup 2 Q := fun x => ⟨1, Subtype.ext (by
      rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
      exact h.sq x x.2)⟩
    have hM₀bot : M₀ = ⊥ := by
      by_cases hMQ : M₀ ⊔ Q = ⊤
      · exfalso
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hQ2grp
        have hcop : Nat.Coprime (Nat.card M₀) (Nat.card Q) := by
          rw [hk]
          exact (Odd.coprime_two_right hM₀o).pow_right k
        have hdisj : M₀ ⊓ Q = ⊥ := disjoint_iff.1 (disjoint_of_coprime_natCard hcop)
        have hn : Q ≤ normalizer (M₀ : Set X) := by
          rw [normalizer_eq_top_iff.2 hM₀]
          exact le_top
        have h2 := card_sup_mul_card_inf hn
        rw [hMQ, card_top, hdisj, card_bot, mul_one] at h2
        have h3 : Nat.card ↥N₀ = Nat.card X := by rw [hN₀top, card_top]
        have hM₀pos : 0 < Nat.card M₀ := Nat.card_pos
        have hBQ : Nat.card (↥N₀ ⧸ M₀.subgroupOf N₀) = Nat.card Q := by
          have h4 : Nat.card (↥N₀ ⧸ M₀.subgroupOf N₀) * Nat.card M₀ =
              Nat.card Q * Nat.card M₀ := by
            rw [← hcardN₀, h3, h2, mul_comm]
          exact Nat.eq_of_mul_eq_mul_right hM₀pos h4
        obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 (↥N₀ ⧸ M₀.subgroupOf N₀)))
        obtain ⟨D, hD⟩ := CFSG.Goldschmidt.G3a.exists_borelSetup hB T
        have hcardB := hD.card_eq
        have hdvd : Nat.card (T : Subgroup (↥N₀ ⧸ M₀.subgroupOf N₀)) + 1 ∣ 2 ^ k := by
          rw [← hk, ← hBQ, hcardB]
          exact Dvd.intro_left _ rfl
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
        have hT4 : 4 ≤ Nat.card (T : Subgroup (↥N₀ ⧸ M₀.subgroupOf N₀)) :=
          hD.four.trans (card_le_of_le
            (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter_le _))
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 T.isPGroup'
        rcases m with _ | m
        · rw [hm] at hT4
          norm_num at hT4
        rcases j with _ | j
        · rw [pow_zero] at hj
          omega
        · rw [hm, pow_succ, pow_succ] at hj
          omega
      · exact hcore M₀ hM₀ (le_sup_left.trans (huniq _ le_sup_right hMQ))
    have hsub : M₀.subgroupOf N₀ = ⊥ := by
      rw [hM₀bot, bot_subgroupOf]
    let e₁ : X ≃* N₀ := (topEquiv.symm).trans (MulEquiv.subgroupCongr hN₀top.symm)
    let e₂ : N₀ ≃* ↥N₀ ⧸ M₀.subgroupOf N₀ :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hsub.symm)
    exact fusionIsBenderGroup_transport (e₁.trans e₂).symm hB

end AbsTI

end CFSG.LargeExtraspecial.Asc22
