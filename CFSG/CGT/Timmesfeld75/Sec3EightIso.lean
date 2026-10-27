module

public import CFSG.CGT.Timmesfeld75.Sec3EightQuot
public import CFSG.CGT.Timmesfeld75.Sec3IsoParts

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem Sec3.exists_cases (h214 : Lemma214) (hS : Sec3 T T₁) :
    ∃ _ : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal,
      (∃ f : ℕ, 2 ≤ f ∧ Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃*
          PSL(2, GaloisField 2 f))) ∨
        (∃ a : ℕ, 1 ≤ a ∧ Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* Sz a)) ∨
        (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ Nonempty (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃*
          DihedralGroup n)) := by
  obtain ⟨x, -, hx⟩ := hS.conj
  have hT : IsWC T := hS.cfg.wc
  have hne : conjSubgroup x T ≠ T := by
    intro h
    have hinf : T ⊓ T₁ = ⊥ := hS.cfg.inf
    rw [hx, h, inf_idem] at hinf
    apply hS.cfg.ne
    exact eq_bot_iff.2 fun y hy => by
      have hyT : y ∈ T := hy.1
      rwa [hinf] at hyT
  have hL : normIn T (conjSubgroup x T) ≠ ⊥ := hx ▸ hS.cfg.ne
  obtain ⟨-, hN, hcases⟩ := h214 G T hT x hne hL
  subst hx
  exact ⟨hN, hcases⟩

theorem Sec3.card_map_dihedral [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] (hS : Sec3 T T₁)
    {n : ℕ} (hn : Odd n)
    (e : ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁) ≃* DihedralGroup n) :
    Nat.card ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) = 2 := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  have hp : IsPGroup 2 ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) :=
    isPGroup_two_of_isElemAbelian hS.isElemAbelian_map
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hp
  have hdvd : Nat.card ((T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ∣ 2 * n := by
    rw [← DihedralGroup.nat_card (n := n), ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hne := hS.map_ne_bot
  rw [hk] at hdvd ⊢
  rcases k with _ | _ | k
  · exfalso
    exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk]; rfl))
  · rfl
  · exfalso
    obtain ⟨r, hr⟩ := hn
    have h4 : 4 ∣ 2 ^ (k + 2) := ⟨2 ^ k, by ring⟩
    have := h4.trans hdvd
    omega

theorem Sec3.sylowInner_map [IsSimpleGroup G] (h214 : Lemma214) (hSz : Section3SzInput)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hS : Sec3 T T₁)
    [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal] :
    SylowInner (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
  obtain ⟨hN', hcases⟩ := hS.exists_cases h214
  rcases hcases with ⟨f, hf, hiso⟩ | ⟨a, ha, hiso⟩ | ⟨n, hn, hn3, ⟨e⟩⟩
  · obtain ⟨hN'', f', hf', hpair⟩ := hS.exists_isL2Pair ⟨hN', f, by omega, hiso⟩
    exact hpair.sylowInner
  · exact absurd ⟨hN', hiso⟩ (hSz G hnab T T₁ hS a ha)
  · exact SylowInner.of_dihedral hn e (hS.card_map_dihedral hn e)

end CFSG.CGT.Timmesfeld75
