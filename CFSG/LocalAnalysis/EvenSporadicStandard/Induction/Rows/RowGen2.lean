module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Prof
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ReachGen

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction

theorem centEquivOfIsConj {Y : Type} [Group Y] {u v : Y} (h : IsConj u v) :
    Nonempty (↥(centralizer ({u} : Set Y)) ≃* ↥(centralizer ({v} : Set Y))) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  subst hc
  exact ⟨centMapEquiv (MulAut.conj c) u⟩

theorem center_eq_bot_of_fStarSimple {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : FStarSimple N) : center Y = ⊥ := by
  have h1 : center Y ≤ centralizer (N : Set Y) := fun z hz =>
    mem_centralizer_iff.2 fun n _ => (mem_center_iff.1 hz n)
  have h2 : center Y ≤ N := h1.trans hN.centralizer_le
  rw [eq_bot_iff]
  intro z hz
  have hzN : (⟨z, h2 hz⟩ : ↥N) ∈ center ↥N := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.1 hz g)
  rw [center_eq_bot_of_simple hN.isSimpleGroup hN.nonabelian, Subgroup.mem_bot] at hzN
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hzN)

theorem not_isSolvable_cq_of_isQuasisimple {X : Type} [Group X] (hq : CFSG.IsQuasisimple X) :
    ¬ Group.IsSolvable (X ⧸ center X) := by
  intro hs
  have : Group.IsPerfect X := hq.1
  have : Group.IsPerfect (X ⧸ center X) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (center X)) QuotientGroup.mk_surjective
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  exact Group.IsPerfect.not_isSolvable (X ⧸ center X) hs

theorem canLoc_eq_of_even {H : Type} [Group H] {K₁ N₀ : Subgroup H} (h : CanLoc K₁ N₀)
    (hev : Even (Nat.card ↥(center ↥K₁))) : N₀ = K₁ := by
  rcases h with ⟨-, h⟩ | ⟨hodd, -⟩
  · exact h
  · exact absurd hev (Nat.not_even_iff_odd.2 hodd)

theorem even_card_center_of_quot {K₁ : Type} [Group K₁] [Finite K₁] (hq : CFSG.IsQuasisimple K₁)
    (h : Nat.card (center (K₁ ⧸ CFSG.oddCore K₁)) = 2) : Even (Nat.card (center K₁)) := by
  have : Group.IsPerfect K₁ := hq.1
  have h1 := card_center_eq_of_cover (QuotientGroup.mk' (CFSG.oddCore K₁))
    QuotientGroup.mk_surjective (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hq)
  rw [h1, h]
  exact even_two.mul_left _

theorem twoAdic_le_one_of_card_le_two {X : Type*} [Group X] [Finite X] (H : Subgroup X)
    (h : Nat.card H ≤ 2) : twoAdic H ≤ 1 := by
  have hpos : 0 < Nat.card H := Nat.card_pos
  have h2 : Nat.card H ∣ 2 := by
    obtain h1 | h2 : Nat.card H = 1 ∨ Nat.card H = 2 := by omega
    · rw [h1]; exact one_dvd _
    · rw [h2]
  have h3 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by norm_num)).2 h2 2
  simpa [twoAdic, Nat.Prime.factorization Nat.prime_two] using h3

theorem elemBound_of_card_le {X : Type*} [Group X] [Finite X] {b : ℕ} (h : Nat.card X ≤ b) :
    ElemBound b X := fun E _ _ => (Subgroup.card_le_card_group E).trans h

theorem not_lamProfile_of_not_fix {K : Type} [Group K] (ab : Prop) (b : ℕ)
    (h : ∀ α : MulAut K, α ≠ 1 → α * α = 1 → ¬ LamProfile ab b ↥(fixSubgroup α)) :
    ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
      ¬ LamProfile ab b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
        ((∃ k : K, α = MulAut.conj k) → ¬ LamProfile ab b ↥(fixSubgroup α)) :=
  fun α h1 h2 => ⟨fun hL => h α h1 h2
    (hL.of_injective (f := MonoidHom.inl ↥(fixSubgroup α) (Multiplicative (ZMod 2)))
      (fun _ _ hab => (Prod.mk.inj hab).1)), fun _ => h α h1 h2⟩

section Arith

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Monster.Existence.Compat CFSG.Open

theorem card_isSporadic_m (mf : MonsterFacts (Carrier .M)) {Y : Type} [Group Y]
    (h : IsSporadic Y .M) : Nat.card Y = monsterOrder := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact mf.card

theorem card_isSporadic_b (F : TwoAFacts) {Y : Type} [Group Y] (h : IsSporadic Y .B) :
    Nat.card Y = monsterBabyOrder := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact F.b_card

theorem sporadicNotExc_m (mf : MonsterFacts (Carrier .M)) : SporadicNotExc .M :=
  sporadicNotExc_of_card (fun _ _ h => card_isSporadic_m mf h) (c := 1173501297218634645)
    (by unfold monsterOrder; norm_num) (by unfold monsterOrder; norm_num)
    (by unfold monsterOrder; norm_num)

theorem sporadicNotExc_b (F : TwoAFacts) : SporadicNotExc .B :=
  sporadicNotExc_of_card (fun _ _ h => card_isSporadic_b F h) (c := 202547114678)
    (by unfold monsterBabyOrder; norm_num) (by unfold monsterBabyOrder; norm_num)
    (by unfold monsterBabyOrder; norm_num)

theorem fi23Excl_of_twoAFacts (F : TwoAFacts) {s : TauCeti.SporadicName} {n : ℕ}
    (hs : ∀ (Y : Type) [Group Y], IsSporadic Y s → Nat.card Y = n)
    (hn : ¬ n ∣ monsterFi23Order) : Fi23Excl s := by
  intro X _ hX hXs
  have hcard : Nat.card X = monsterFi23Order := by
    obtain ⟨e⟩ := hX
    rw [Nat.card_congr e.toEquiv]
    exact F.fi23_card
  have hdvd : Nat.card (X ⧸ center X) ∣ Nat.card X := Subgroup.card_quotient_dvd_card (center X)
  rw [hs _ hXs, hcard] at hdvd
  exact hn hdvd

theorem fi23Excl_m (F : TwoAFacts) (mf : MonsterFacts (Carrier .M)) : Fi23Excl .M :=
  fi23Excl_of_twoAFacts F (fun _ _ h => card_isSporadic_m mf h)
    (by unfold monsterOrder monsterFi23Order; norm_num)

theorem fi23Excl_b (F : TwoAFacts) : Fi23Excl .B :=
  fi23Excl_of_twoAFacts F (fun _ _ h => card_isSporadic_b F h)
    (by unfold monsterBabyOrder monsterFi23Order; norm_num)

end Arith

end CFSG.EvenSporadicStandard.Induction.Hyp
