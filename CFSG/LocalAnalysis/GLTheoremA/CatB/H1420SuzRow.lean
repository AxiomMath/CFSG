module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420MainA
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowCentre
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowLie
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (SporadicMultipliers card_center_dvd_twelve)

private theorem eq_three_of_dvd_twelve {n : ℕ} (h12 : n ∣ 12) (hk : ∃ k : ℕ, n = 3 ^ k)
    (h3 : 3 ∣ n) : n = 3 := by
  obtain ⟨k, rfl⟩ := hk
  rcases k with _ | _ | k
  · exact absurd h3 (by norm_num)
  · rfl
  · exact absurd ((pow_dvd_pow 3 (by omega : 2 ≤ k + 2)).trans h12) (by norm_num)

theorem suzRow_of_facts {z : ℕ} (hz : z = 3 ∨ z = 9) (hAD : KDAltDown) (hb : LieOrderBridge)
    (hD : ∀ q : ℕ, KDChevDownQ 3 q) (hInn : KDChevInner 3) (h65 : KD65 3)
    (hL2 : KDOutChevCentre) (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers)
    (hCo3 : K14Spor.CardRow 3265920 .Co3) (hLy : K14Spor.CardRow 3265920 .Ly)
    (hTh : K14Spor.CardRow 3265920 .Th) (hFi23 : K14Spor.CardRow 3265920 .Fi23)
    (hFi24 : K14Spor.CardRow 3265920 .Fi24Prime) (hB : K14Spor.CardRow 3265920 .B)
    (hMon : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .M).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        β ≠ 1 → ∀ J : Subgroup S,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
            catalogIs (PSimple 3 J) (S8.isU4of 3) → False)
    (hFi22 : CentRow .Fi22 fun (T : Type) [Group T] => Subgroup.center T = ⊥)
    (hCo1 : CentRow .Co1 fun (T : Type) [Group T] =>
      Nat.card (Subgroup.center T) = 9 ∨ Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920)
    {Q : Type} [Group Q] [Finite Q] {K I₀ D : Subgroup Q} (hM : I1420ModelA 3 K I₀ D)
    (hT : S8.IsTypeWithCenter 3 I₀ (S8.isU4of 3) z) :
    catalogIs (PSimple 3 K) (S8.sporIs .Suz) ∨
      (catalogIs (PSimple 3 K) (S8.sporIs .Fi22) ∧ z = 3 ∧
        Nat.card (Subgroup.center (PQuot 3 K)) = 3) ∨
      (catalogIs (PSimple 3 K) (S8.sporIs .Co1) ∧ z = 9) := by
  have hz1 : z ≠ 1 := by rcases hz with rfl | rfl <;> norm_num
  obtain ⟨hq, ⟨i, ⟨e⟩⟩, β, J, hcore, hineq⟩ := exists_coreP_of_modelA Nat.prime_three hM hT
  have hzd : Nat.card (Subgroup.center (PQuot 3 J)) ∣ z := hcore.2.2.2.2.2.2.2
  cases i with
  | cyclic q hq' =>
    obtain ⟨a, b, hab⟩ := hcore.2.1
    exact absurd (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)) hab
  | alternating n hn => exact (suzRow_alt_of_facts hAD hn e hcore).elim
  | lie idx =>
    exact (suzRow_lie_of_facts hz1 hb hD hInn h65 hL2 idx e hcore hq
      (isPGroup_center_pQuot Nat.prime_three K) (MulEquiv.refl _) hineq).elim
  | sporadic t =>
    rcases suzRow_spor_of_rows hOrd hOut hCo3 hLy hTh hFi23 hFi24 hB hMon hFi22 hCo1 e hcore with
      rfl | ⟨rfl, hZ⟩ | ⟨rfl, hZ⟩
    · exact Or.inl ⟨.sporadic .Suz, rfl, ⟨e⟩⟩
    · rw [hZ, Subgroup.card_bot, one_mul] at hineq
      have h12 := card_center_dvd_twelve hSpM hq .Fi22 e
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hpg := (IsPGroup.iff_card).1 (isPGroup_center_pQuot Nat.prime_three K)
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl ⟨⟨.sporadic .Fi22, rfl, ⟨e⟩⟩, rfl,
          eq_three_of_dvd_twelve h12 hpg hineq⟩)
      · exact absurd (hineq.trans h12) (by norm_num)
    · rw [hZ] at hzd
      rcases hz with rfl | rfl
      · exact absurd hzd (by norm_num)
      · exact Or.inr (Or.inr ⟨⟨.sporadic .Co1, rfl, ⟨e⟩⟩, rfl⟩)

theorem i1420SuzA_of_facts (hAD : KDAltDown) (hb : LieOrderBridge)
    (hD : ∀ q : ℕ, KDChevDownQ 3 q) (hInn : KDChevInner 3) (h65 : KD65 3)
    (hL2 : KDOutChevCentre) (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers)
    (hCo3 : K14Spor.CardRow 3265920 .Co3) (hLy : K14Spor.CardRow 3265920 .Ly)
    (hTh : K14Spor.CardRow 3265920 .Th) (hFi23 : K14Spor.CardRow 3265920 .Fi23)
    (hFi24 : K14Spor.CardRow 3265920 .Fi24Prime) (hB : K14Spor.CardRow 3265920 .B)
    (hMon : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .M).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        β ≠ 1 → ∀ J : Subgroup S,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
            catalogIs (PSimple 3 J) (S8.isU4of 3) → False)
    (hFi22 : CentRow .Fi22 fun (T : Type) [Group T] => Subgroup.center T = ⊥)
    (hCo1 : CentRow .Co1 fun (T : Type) [Group T] =>
      Nat.card (Subgroup.center T) = 9 ∨ Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920) :
    I1420SuzA := by
  intro Q _ _ K I₀ D hM hT
  rcases suzRow_of_facts (Or.inl rfl) hAD hb hD hInn h65 hL2 hOrd hOut hSpM hCo3 hLy hTh hFi23
    hFi24 hB hMon hFi22 hCo1 hM hT with h | ⟨h, -, hZ⟩ | ⟨-, h9⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hZ⟩
  · exact absurd h9 (by norm_num)

theorem i1420SuzhA_of_facts (hAD : KDAltDown) (hb : LieOrderBridge)
    (hD : ∀ q : ℕ, KDChevDownQ 3 q) (hInn : KDChevInner 3) (h65 : KD65 3)
    (hL2 : KDOutChevCentre) (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers)
    (hCo3 : K14Spor.CardRow 3265920 .Co3) (hLy : K14Spor.CardRow 3265920 .Ly)
    (hTh : K14Spor.CardRow 3265920 .Th) (hFi23 : K14Spor.CardRow 3265920 .Fi23)
    (hFi24 : K14Spor.CardRow 3265920 .Fi24Prime) (hB : K14Spor.CardRow 3265920 .B)
    (hMon : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .M).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        β ≠ 1 → ∀ J : Subgroup S,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
            catalogIs (PSimple 3 J) (S8.isU4of 3) → False)
    (hFi22 : CentRow .Fi22 fun (T : Type) [Group T] => Subgroup.center T = ⊥)
    (hCo1 : CentRow .Co1 fun (T : Type) [Group T] =>
      Nat.card (Subgroup.center T) = 9 ∨ Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920) :
    I1420SuzhA := by
  intro Q _ _ K I₀ D hM hT
  rcases suzRow_of_facts (Or.inr rfl) hAD hb hD hInn h65 hL2 hOrd hOut hSpM hCo3 hLy hTh hFi23
    hFi24 hB hMon hFi22 hCo1 hM hT with h | ⟨-, h3, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact absurd h3 (by norm_num)
  · exact Or.inr h

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
