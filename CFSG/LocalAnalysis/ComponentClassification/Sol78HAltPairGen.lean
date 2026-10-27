module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76Thm13Aux
public import CFSG.LocalAnalysis.ComponentClassification.Sol78NoStrongEmb
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ComponentClassification.Sol78H

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_oddCoreIn_of_normal {N Y : Subgroup X} (hNY : N ≤ Y)
    (hnorm : Y ≤ normalizer (N : Set X)) (hodd : Nat.Coprime 2 (Nat.card N)) :
    N ≤ FooteLit.oddCoreIn Y := by
  have h := Sol76.inf_le_oddCoreIn hodd hnorm
  rwa [inf_eq_left.mpr hNY] at h

theorem le_normalizer_sup_of_commutator {L L' O : Subgroup X} (hc : ⁅L, L'⁆ ≤ O)
    (hO : L' ≤ normalizer (O : Set X)) : L' ≤ normalizer ((L ⊔ O : Subgroup X) : Set X) := by
  intro x hx
  have hmap : (L ⊔ O).map (MulAut.conj x).toMonoidHom ≤ L ⊔ O := by
    rw [Subgroup.map_sup, Sol76.map_conj_eq_of_mem_normalizer (hO hx)]
    refine sup_le ?_ le_sup_right
    rintro _ ⟨l, hl, rfl⟩
    have h1 : l⁻¹ * x * l * x⁻¹ ∈ O := by
      have := hc (commutator_mem_commutator (inv_mem hl) hx)
      rwa [commutatorElement_def, inv_inv] at this
    have h2 : (MulAut.conj x).toMonoidHom l = l * (l⁻¹ * x * l * x⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h2]
    exact mul_mem (mem_sup_left hl) (mem_sup_right h1)
  have heq : (L ⊔ O).map (MulAut.conj x).toMonoidHom = L ⊔ O :=
    Subgroup.eq_of_le_of_card_ge hmap
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm)
  exact mem_normalizer_iff_map_conj_eq.mpr heq

omit [Finite X] in
theorem mem_normalizer_oddResidualIn {J : Subgroup X} {g : X}
    (hg : g ∈ normalizer (J : Set X)) :
    g ∈ normalizer ((FooteLit.oddResidualIn J : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq, FooteLit.map_oddResidualIn _ (MulAut.conj g).injective,
    mem_normalizer_iff_map_conj_eq.mp hg]

omit [Finite X] in
theorem comap_map_eq_self_of_injective' (M : Subgroup X) {K : Subgroup ↥M} :
    (K.map M.subtype).subgroupOf M = K :=
  comap_map_eq_self_of_injective M.subtype_injective K

theorem nonempty_coreQuot_equiv_of_sup {M L : Subgroup X} (hLM : L ≤ M)
    (hsup : L ⊔ FooteLit.oddCoreIn M = M) :
    Nonempty (↥L ⧸ pPrimeCore 2 ↥L ≃* ↥M ⧸ pPrimeCore 2 ↥M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := L.subgroupOf M with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥M)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥M = ⊤ := by
      have h2 : (L ⊔ FooteLit.oddCoreIn M).subgroupOf M = ⊤ := by
        rw [hsup]
        exact subgroupOf_self M
      rwa [FooteLit.oddCoreIn, subgroupOf_sup hLM (map_subtype_le _),
        comap_map_eq_self_of_injective' M] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥M))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, -⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  let ψ : ↥L ⧸ pPrimeCore 2 ↥L ≃* Y ⧸ pPrimeCore 2 Y :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLM).symm (pPrimeCore_map_iso 2 _)
  exact ⟨ψ.trans φ⟩

theorem two_dvd_card_alternatingGroup {n : ℕ} (hn : 8 ≤ n) :
    2 ∣ Nat.card (alternatingGroup (Fin n)) := by
  set g : alternatingGroup (Fin n) :=
    ⟨Sol78.dblTransposition hn, Equiv.Perm.mem_alternatingGroup.mpr (Sol78.sign_dbl hn)⟩ with hg
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (Sol78.dbl_mul_self hn)
  have hg1 : g ≠ 1 := by
    intro h
    have h1 := congrArg Subtype.val h
    have h2 := Sol78.card_support_dbl hn
    rw [show (g : Equiv.Perm (Fin n)) = Sol78.dblTransposition hn from rfl] at h1
    rw [h1] at h2
    simp at h2
  have := orderOf_dvd_natCard g
  rwa [orderOf_eq_prime hg2 hg1] at this

end CFSG.ComponentClassification.Sol78H
