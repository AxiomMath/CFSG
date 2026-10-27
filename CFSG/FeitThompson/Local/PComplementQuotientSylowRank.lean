module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Foundations.HallImageQuotient
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise QuotientGroup

variable {p : ℕ} {X : Type*} [Group X] {N P Q : Subgroup X} [N.Normal]

omit [N.Normal] in
theorem inf_eq_bot_of_isPGroup_of_coprime [Finite X] (hp : p.Prime) (hQ : IsPGroup p Q)
    (hN : p.Coprime (Nat.card N)) : Q ⊓ N = ⊥ := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  exact disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hN.pow_left n))

theorem injective_domRestrict_mk' (h : Q ⊓ N = ⊥) :
    Function.Injective ((mk' N).domRestrict Q) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have hmem : (x : X) ∈ Q ⊓ N :=
    ⟨x.2, (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)⟩
  rw [h] at hmem
  exact Subtype.ext (by simpa using hmem)

noncomputable def equivMapSupMk' (h : Q ⊓ N = ⊥) :
    Q ≃* ((Q ⊔ N).map (mk' N) : Subgroup (X ⧸ N)) :=
  (MonoidHom.ofInjective (injective_domRestrict_mk' h)).trans
    (MulEquiv.subgroupCongr
      ((MonoidHom.domRestrict_range Q (mk' N)).trans (map_sup_mk'_eq_map_mk' Q N).symm))

@[simp]
theorem coe_equivMapSupMk'_apply (h : Q ⊓ N = ⊥) (x : Q) :
    ((equivMapSupMk' h x : ((Q ⊔ N).map (mk' N) : Subgroup (X ⧸ N))) : X ⧸ N) = (x : X) := (rfl)

theorem natCard_map_sup_mk' (h : Q ⊓ N = ⊥) :
    Nat.card ((Q ⊔ N).map (mk' N) : Subgroup (X ⧸ N)) = Nat.card Q :=
  (Nat.card_congr (equivMapSupMk' h).toEquiv).symm

noncomputable def equivMapSup [Finite X] (hp : p.Prime) (hN : p.Coprime (Nat.card N))
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    P ≃* ((P ⊔ N).map (mk' N) : Subgroup (X ⧸ N)) :=
  equivMapSupMk' (inf_eq_bot_of_isPGroup_of_coprime hp (IsPGroup.of_card hP) hN)

@[simp]
theorem coe_equivMapSup_apply [Finite X] (hp : p.Prime) (hN : p.Coprime (Nat.card N))
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) (x : P) :
    ((equivMapSup hp hN hP x : ((P ⊔ N).map (mk' N) : Subgroup (X ⧸ N))) : X ⧸ N)
      = (x : X) := (rfl)

omit [N.Normal] in
theorem factorization_natCard_quotient [Finite X] (hp : p.Prime) (hN : p.Coprime (Nat.card N)) :
    (Nat.card (X ⧸ N)).factorization p = (Nat.card X).factorization p := by
  have hcard : Nat.card (X ⧸ N) * Nat.card N = Nat.card X := by
    rw [← Subgroup.index_eq_card, mul_comm]; exact Subgroup.card_mul_index N
  rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp [Nat.factorization_eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.1 hN)]

theorem natCard_map_sup_mk'_eq_pow_factorization [Finite X] (hp : p.Prime)
    (hN : p.Coprime (Nat.card N)) (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    Nat.card ((P ⊔ N).map (mk' N) : Subgroup (X ⧸ N))
      = p ^ (Nat.card (X ⧸ N)).factorization p := by
  rw [natCard_map_sup_mk' (inf_eq_bot_of_isPGroup_of_coprime hp (IsPGroup.of_card hP) hN), hP,
    factorization_natCard_quotient hp hN]

theorem coe_sylowMapSurjective [Finite X] [Fact p.Prime] (N : Subgroup X) [N.Normal]
    (P : Sylow p X) :
    (Sylow.mapSurjective (mk'_surjective N) P : Subgroup (X ⧸ N))
      = ((P : Subgroup X) ⊔ N).map (mk' N) := by
  rw [Sylow.coe_mapSurjective, map_sup_mk'_eq_map_mk']

theorem exists_le_conj_smul_map_sup_mk' [Finite X] (hp : p.Prime) (hN : p.Coprime (Nat.card N))
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) {S : Subgroup (X ⧸ N)}
    (hS : IsPGroup p S) :
    ∃ g : X ⧸ N, S ≤ MulAut.conj g • ((P ⊔ N).map (mk' N) : Subgroup (X ⧸ N)) := by
  have := Fact.mk hp
  exact exists_le_conj_smul_of_isPGroup (natCard_map_sup_mk'_eq_pow_factorization hp hN hP) hS

theorem elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization [Finite X] (hp : p.Prime)
    (hP : Nat.card P = p ^ (Nat.card X).factorization p) :
    elementaryAbelianPRank p P = elementaryAbelianPRank p X := by
  have := Fact.mk hp
  refine le_antisymm (elementaryAbelianPRank_subgroup_le hp.one_lt P) ?_
  obtain ⟨E, ⟨e⟩⟩ := exists_subgroup_mulEquiv_of_elementaryAbelianPRank (p := p) (X := X) hp.one_lt
  have hE : IsPGroup p E :=
    IsPGroup.of_card (by rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod])
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hP hE
  calc elementaryAbelianPRank p X
      = elementaryAbelianPRank p E := by
        rw [elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt e, elementaryAbelianPRank_pi hp.one_lt]
    _ ≤ elementaryAbelianPRank p (MulAut.conj g • P : Subgroup X) :=
        elementaryAbelianPRank_le_of_le hp.one_lt hg
    _ = elementaryAbelianPRank p P := (elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt
        (Subgroup.equivSMul (MulAut.conj g) P)).symm

theorem elementaryAbelianPRank_quotient_eq [Finite X] (hp : p.Prime)
    (hN : p.Coprime (Nat.card N)) :
    elementaryAbelianPRank p (X ⧸ N) = elementaryAbelianPRank p X := by
  have := Fact.mk hp
  obtain ⟨P⟩ : Nonempty (Sylow p X) := inferInstance
  have hP : Nat.card (P : Subgroup X) = p ^ (Nat.card X).factorization p := P.card_eq_multiplicity
  rw [← elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp
      (natCard_map_sup_mk'_eq_pow_factorization hp hN hP),
    ← elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp hP,
    elementaryAbelianPRank_eq_of_mulEquiv hp.one_lt (equivMapSup hp hN hP)]

end

end CFSG.FeitThompson
