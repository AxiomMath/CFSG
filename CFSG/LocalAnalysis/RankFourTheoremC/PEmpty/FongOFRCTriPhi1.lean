module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCTwDefs
import CFSG.RankThree.PartOne.KLC.TriTorus
public import CFSG.RankThree.PartOne.KF.D4Sylow

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne

section Phi1General


theorem pow_pow_eq_self_of_pow_eq_one {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hpN : p ∣ ℓ ^ f - 1)
    {L : Type} [Field L] (y : L) (hy : y ^ p = 1) : y ^ (ℓ ^ f) = y := by
  obtain ⟨m, hm⟩ := hpN
  have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have he : ℓ ^ f = p * m + 1 := by
    rw [← hm]
    exact (Nat.sub_add_cancel h1).symm
  rw [he, pow_succ, pow_mul, hy, one_pow, one_mul]

theorem twistHom_tp3Hom_phi1 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hpN : p ∣ ℓ ^ f - 1) {L : Type} [Field L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (b : Fin 2 → rootsOfUnity p L) :
    twistHom TwistTag.D4 L Fr (KFU.tp3Hom p L b) = KFU.tp3Hom p L b := by
  have hfixU : ∀ x : Lˣ, x ^ p = 1 → Units.map Fr.toMonoidHom x = x := by
    intro x hx
    refine Units.ext ?_
    have h1 : (x : L) ^ p = 1 := by simpa using congrArg Units.val hx
    show Fr (x : L) = (x : L)
    rw [hFr]
    exact pow_pow_eq_self_of_pow_eq_one hℓ hpN _ h1
  rw [KFU.tp3Hom_apply, twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  have hx := hfixU _ ((mem_rootsOfUnity p _).mp (b 1).2)
  have hy := hfixU _ ((mem_rootsOfUnity p _).mp (b 0).2)
  rw [KFU.d4Tuple_perm_symm]
  rcases KFU.fin_D4_cases i with rfl | rfl | rfl | rfl
  · rw [KFU.d4Tuple_zero]
    exact hx
  · rw [KFU.d4Tuple_one]
    exact hx
  · rw [KFU.d4Tuple_two]
    exact hy
  · rw [KFU.d4Tuple_three]
    exact hx

theorem two_le_pRank_phi1_core {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {p : ℕ} (hp : p.Prime) (hpN : p ∣ ℓ ^ f - 1) (hpℓ : p ≠ ℓ)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    2 ≤ CFSG.pRank p (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) :=
    fun c => iterateFrobenius_def ℓ f c
  let ψ : (rootsOfUnity p L) × (rootsOfUnity p L) →* (Fin 2 → rootsOfUnity p L) :=
    { toFun := fun z => ![z.1, z.2]
      map_one' := by
        funext i
        fin_cases i <;> rfl
      map_mul' := fun a b => by
        funext i
        fin_cases i <;> rfl }
  let φ : (rootsOfUnity p L) × (rootsOfUnity p L) →* ModGL TwistTag.D4.tag L :=
    (KFU.tp3Hom p L).comp ψ
  have hψinj : Function.Injective ψ := by
    intro z z' h
    have h0 : z.1 = z'.1 := congrFun h 0
    have h1 : z.2 = z'.2 := congrFun h 1
    exact Prod.ext h0 h1
  have hφ : Function.Injective φ := by
    intro a b h
    apply hψinj
    apply KFU.tp3Hom_injective
    exact h
  have hφT : φ.range ≤ twistedTorusOf (1 : ModGL TwistTag.D4.tag L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := by
    rintro _ ⟨z, rfl⟩
    have hφz : φ z = KFU.tp3Hom p L (ψ z) := rfl
    refine mem_twistedTorusOf.2 ⟨?_, ?_⟩
    · rw [hφz, KFU.tp3Hom_apply]
      exact rootDiagUnit_mem_torusGroup _
    · rw [hφz, one_mul, inv_one, mul_one]
      exact twistHom_tp3Hom_phi1 hℓ hpN (iterateFrobenius L ℓ f) hFr (ψ z)
  have hrat : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
      (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
        P ≤ (triEmb K σ L).range := by
    intro P hPC hPF
    rw [triEmb_range hℓ hf hK hσ (iterateFrobenius L ℓ f) hFr]
    exact fun x hx => Subgroup.mem_inf.2 ⟨hPC hx, hPF x hx⟩
  exact KLC.two_le_pRank_triality_of_hom σ hp hpℓ L 1 1 (Subgroup.one_mem _) (by simp) hrat φ hφ
    hφT

theorem two_le_pRank_triality_phi1_general : TriPhi1Rank := by
  intro ℓ f hℓf hf K _ _ hK σ hσ p hp hp5 hpq
  have hℓ : ℓ.Prime := Fact.out
  have h1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have hpN : p ∣ ℓ ^ f - 1 := by
    apply Int.natCast_dvd_natCast.1
    rw [Nat.cast_sub h1, Nat.cast_one]
    exact hpq
  have hpℓ : p ≠ ℓ := by
    intro h
    rw [← h] at hpN
    have h2 : p ∣ p ^ f := dvd_pow_self p (by omega)
    have h3 : p ∣ (p ^ f - 1) + 1 := by
      rw [Nat.sub_add_cancel (Nat.one_le_pow f p hp.pos)]
      exact h2
    have h4 : p ∣ 1 := (Nat.dvd_add_right hpN).1 h3
    have := Nat.dvd_one.1 h4
    omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  exact two_le_pRank_phi1_core hf hK σ hσ hp hpN hpℓ (AlgebraicClosure K)

end Phi1General

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
