module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Inner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open

theorem rationalLieType_of_cover {ℓ : ℕ} {G : Type} [Group G] (R : Subgroup G) {X : Type}
    [Group X] (hX : LieFactorData ℓ X) (g : X →* ↥R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))) :
    RationalLieType ℓ R := by
  obtain ⟨e⟩ := nonempty_centralQuotient_mulEquiv hX.perfect g hg hgk
  exact ⟨isChevSimple_congr e hX.chev, ⟨fun a => hA6.false (e.trans a)⟩⟩

theorem ringChar_eq_three_of_card_eq_nine {K : Type} [Field K] [Fintype K]
    (h : Fintype.card K = 9) : ringChar K = 3 := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hd : ringChar K ∣ 3 ^ 2 := by
    have h9 : Fintype.card K = 3 ^ 2 := by rw [h]; norm_num
    rw [← h9, hcard]
    exact dvd_pow_self _ n.pos.ne'
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow hd)

theorem ringChar_subfield' {K : Type} [Field K] (k : Subfield K) : ringChar k = ringChar K := by
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : CharP k (ringChar K) := (k.subtype.charP_iff k.subtype_injective _).2 inferInstance
  exact ringChar.eq k _

theorem rationalLieType_of_slCover {K : Type} [Field K] [Finite K] {ν : ℕ} (hν : 2 ≤ ν)
    (h4 : ν = 2 → 4 ≤ Nat.card K) (hℓ3 : ringChar K ≠ 3) {G : Type} [Group G] (R : Subgroup G)
    (g : Matrix.SpecialLinearGroup (Fin ν) K →* ↥R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin ν) K)) :
    RationalLieType (ringChar K) R := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hFD := slFactorFacts_holds K ν hν (fun h => by
    rw [← Nat.card_eq_fintype_card]
    exact h4 h)
  refine rationalLieType_of_cover R hFD g hg hgk ⟨fun a => ?_⟩
  obtain ⟨-, h9⟩ := slAltSixFacts_holds K ν hν ⟨a⟩
  exact hℓ3 (ringChar_eq_three_of_card_eq_nine h9)

theorem rationalLieType_of_suCover {F : Type} [Field F] [Fintype F] {ν Q : ℕ}
    (hF : Fintype.card F = Q ^ 2) (hν : 3 ≤ ν) (hνQ : (ν, Q) ≠ (3, 2)) {G : Type} [Group G]
    (R : Subgroup G) (g : ↥(StatedSU ν Q F) →* ↥R) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center ↥(StatedSU ν Q F)) : RationalLieType (ringChar F) R :=
  rationalLieType_of_cover R (suFactorFacts_holds F ν Q hF hν hνQ) g hg hgk
    (suAltSixFacts_holds F ν Q hF hν)

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
