module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.AGLEmbedding.Extremal
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerOdd

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_close (hG : Gen5Global G) (hl : Gen5Local G p P M x)
    {N W : Subgroup G} (hLN : gen5L x ≤ N) (hW2 : IsPGroup 2 W) (hWN : W ≤ N) (hWM : W ≤ M)
    (_hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G))
    (hcomm : ∀ w ∈ W, ∀ l ∈ gen5L x, w⁻¹ * (l⁻¹ * w * l) ∈ rankThreePrimeCore p N) :
    W = ⊥ := by
  have hp := gen5_prime hl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p N
  set O := rankThreePrimeCore p N
  set U := gen5U (P : Subgroup G) x
  have hUL : U ≤ gen5L x := inf_le_right
  have hUp : IsPGroup p U := P.isPGroup'.to_le inf_le_left
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hWcop : Nat.Coprime p (Nat.card W) := hn ▸ Nat.Coprime.pow_right n
    ((Nat.coprime_primes hp Nat.prime_two).mpr (by have := gen5_five_le hG hl; omega))
  set X := O ⊔ W
  have hXcop : Nat.Coprime p (Nat.card X) :=
    CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer (hWN.trans hNO) hOcop
      hWcop
  have hLX : gen5L x ≤ normalizer (X : Set G) := by
    refine le_normalizer_iff.mpr fun l hl k hk => ?_
    refine (sup_le (fun o ho => ?_) (fun w hw => ?_) : X ≤ X.comap (MulAut.conj l).toMonoidHom) hk
    · exact mem_sup_left (le_normalizer_iff.mp (hLN.trans hNO) l hl o ho)
    · have heq : l * w * l⁻¹ = w * (w⁻¹ * (l⁻¹⁻¹ * w * l⁻¹)) := by group
      change l * w * l⁻¹ ∈ X
      rw [heq]
      exact X.mul_mem (mem_sup_right hw) (mem_sup_left (hcomm w hw l⁻¹ (inv_mem hl)))
  have hXM : X ≤ M := sup_le (gen5_coprime_le hG hl ((Nat.Prime.coprime_iff_not_dvd hp).mp hOcop)
    (hUL.trans (hLN.trans hNO))) hWM
  have hΓ : rankThreeGamma 1 p U ≤ M := by
    refine (gamma_le_iff 1 p U M).mpr fun Q hQU hQ1 => gen5_normalizer_le hG hl hQU ?_
    rintro rfl
    obtain ⟨E, hE, -, hcard⟩ := pRank_attained p ⊥ hQ1
    rw [le_bot_iff.mp hE, card_bot] at hcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (⊥ : Subgroup G) ≠ 0) hp.one_lt
    omega
  have h2 : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → U ≤ normalizer (T : Set G) →
      normalizer (T : Set G) ≤ M := fun T hT2 hT1 hUT =>
    le_of_isTwoLocal_of_gamma_one_le hG.setting hG.d2 hG.u0 hl.sigma (gen5_five_le hG hl) hl.core
      ⟨T, hT1, hT2, rfl⟩ hUT
      (inf_le_left.trans (sylow_le_of_isCoreMaxLocal hG.setting hl.sigma hl.core).1) hUp
      (not_isCyclic_of_elemAbelian (gen5_U_elemAbelian hG hl).1 (gen5_U_elemAbelian hG hl).2
        le_rfl) hΓ
  have hodd : Odd (Nat.card X) :=
    CFSG.AGLEmbedding.odd_card_of_twoLocals_le hp hUp (hUL.trans hLX)
      (fun h => gen5_not_le hG hl (hLX.trans h)) le_normalizer
      ((normal_subgroupOf_iff_le_normalizer le_normalizer).mpr le_rfl) hXcop hXM h2
  have hn0 : n = 0 := by
    by_contra hn0
    exact Nat.not_even_iff_odd.mpr (hn ▸ hodd.of_dvd_nat (card_dvd_of_le le_sup_right))
      (Nat.even_pow.mpr ⟨even_two, hn0⟩)
  exact eq_bot_of_card_eq W (by rw [hn, hn0, pow_zero])

end CFSG.LocalAnalysis.RankThreeTheoremC
