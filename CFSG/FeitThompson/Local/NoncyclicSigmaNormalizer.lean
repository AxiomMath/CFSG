module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.SigmaNormalizerCentralizerFactorization
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep08

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

theorem FTS_noncyclic_sigma_normalizer
    (h₁ : Statements.FTS_plane_maximal_overgroups.{u}) :
    Statements.FTS_noncyclic_sigma_normalizer.{u} := by
  intro G _ _ hG M X p hM hpσ hXM hXp hXnc
  have := hG.isSimpleGroup
  have hp : p.Prime := prime_of_mem_sigmaPrimes hpσ
  have hpodd : Odd p := by
    refine hp.odd_of_ne_two fun h => ?_
    have h2 : (2 : ℕ) ∣ Nat.card G :=
      h ▸ (dvd_natCard_of_mem_sigmaPrimes hpσ).trans (Subgroup.card_subgroup_dvd_card M)
    exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2 h2)
  obtain ⟨E, -, -, ⟨f⟩⟩ :=
    exists_normal_le_mulEquiv_pi_of_not_isCyclic (P := ↥X) hp hpodd hXp (⊤ : Subgroup ↥X)
      (fun _ => hXnc (isCyclic_of_surjective (⊤ : Subgroup ↥X).subtype
        fun x => ⟨⟨x, trivial⟩, rfl⟩))
  set A : Subgroup G := E.map X.subtype
  have hequiv : Nonempty (↥A ≃* (Fin 2 → Multiplicative (ZMod p))) :=
    ⟨(E.equivMapOfInjective X.subtype X.subtype_injective).symm.trans f⟩
  have hAX : A ≤ X := Subgroup.map_subtype_le E
  have hplane : IsPlaneAt p A :=
    ⟨isElementaryAbelian_of_nonempty_mulEquiv_pi hequiv, by
      obtain ⟨g⟩ := hequiv
      rw [Nat.card_congr g.toEquiv, card_pi_multiplicative_zmod]⟩
  have hCA : centralizer (A : Set G) ≤ M := (h₁ G hG M A p hM hp (hAX.trans hXM) hplane).1
  have hCX : centralizer (X : Set G) ≤ M :=
    (Subgroup.centralizer_le (by exact_mod_cast hAX)).trans hCA
  have hXne : X ≠ ⊥ := fun h => hXnc (h ▸ inferInstanceAs (IsCyclic (⊥ : Subgroup G)))
  rw [normalizer_eq_sup_centralizer_of_mem_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hM hpσ hXne hXp hXM]
  exact sup_le inf_le_left hCX

end

end CFSG.FeitThompson.Proofs
