module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangCover
public import CFSG.LieType.SemisimpleCentralizers.HeldLangI5Uni
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5FieldPieces

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification.PerfectAutomorphisms
  CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank

@[expose] def I5SUClosed : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f N : ℕ), UnitaryFieldData p f K → 3 ≤ N → 8 ≤ p ^ f →
    ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU N (p ^ f) K), Function.Surjective π →
      π.ker ≤ Subgroup.center E → ∃ s : StatedSU N (p ^ f) K →* E, ∀ g, π (s g) = g

theorem not_three_two_of_valid (n : ℕ) (q : TauCeti.PrimePower) (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid)
    (hN : 3 ≤ n + 1) : ¬(n + 1 = 3 ∧ q.p ^ q.exponent = 2) := fun ⟨h1, h2⟩ => by
  have hval := ((TauCeti.LieTypeIndex.valid_iff _).1 hd).1
  have h3 := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1 hval).2 (by omega)
  have h4 : q.card = 2 := by rw [TauCeti.PrimePower.card_def]; exact h2
  omega

theorem exists_psu_equiv_of_cover (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (L : Type) [Group L]
    (hL : IsI5UniversalCover ⟨.twistedA n q, hd⟩ L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
      Nonempty (L ⧸ Subgroup.center L ≃* StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) K)) := by
  obtain ⟨e0⟩ := hL.2.1
  obtain ⟨-, K, hF, hfin, hK, ⟨e1⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA n q hd (MulEquiv.refl _)
  exact ⟨K, hF, hfin, hK, ⟨e0.trans e1⟩⟩

theorem i5CoverIsSU_of_closed (hcl : I5SUClosed) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (hN : 3 ≤ n + 1) (hq8 : 8 ≤ q.card)
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.twistedA n q, hd⟩ L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (q.p ^ q.exponent) ^ 2 ∧
      Nonempty (L ≃* StatedSU (n + 1) (q.p ^ q.exponent) K) := by
  obtain ⟨K, hF, hfin, hK, ⟨eL⟩⟩ := exists_psu_equiv_of_cover n q hd L hL
  have hdat : UnitaryFieldData q.p q.exponent K :=
    ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  let πS : StatedSU (n + 1) (q.p ^ q.exponent) K →* StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) K) :=
    QuotientGroup.mk' _
  let πL : L →* StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) K) :=
    eL.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hker : πL.ker = Subgroup.center L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eL.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hscal := (CFSG.LinearGroups.unitary_scalar_kernel q.prime_p hK (n := n + 1) (by omega)).2.2
  refine ⟨K, hF, hfin, hK, ?_⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central_covers πS πL (QuotientGroup.mk'_surjective _)
    (eL.surjective.comp (QuotientGroup.mk'_surjective _)) (hker ▸ le_rfl) (Group.isPerfect_def.2 hL.1.1)
    (fun E _ _ π hπ hc => hcl K q.p q.exponent (n + 1) hdat hN (by rw [← hcard]; exact hq8) E π hπ hc)
    (by
      rw [QuotientGroup.ker_mk', hscal, hker, hL.2.2.2]
      show _ ≤ Nat.gcd (n + 1) (q.card + 1)
      exact le_of_eq (by rw [hcard]))
  exact ⟨e.symm⟩

theorem false_of_outer_three_twistedA_small (n : ℕ) (q : TauCeti.PrimePower)
    (hd : (TauCeti.LieTypeIndex.twistedA n q).Valid) (hN : 3 ≤ n + 1) (hq8 : q.card < 8)
    (L : Type) [Group L] [Finite L] (hL : IsI5UniversalCover ⟨.twistedA n q, hd⟩ L)
    (β : MulAut L) (hβ3 : β ^ 3 = 1)
    (hout : onCenterQuotient β ∉ innAutDerived (L ⧸ Subgroup.center L)) : False := by
  obtain ⟨K, hF, hfin, hK, ⟨e'⟩⟩ := exists_psu_equiv_of_cover n q hd L hL
  have hdat : UnitaryFieldData q.p q.exponent K :=
    ⟨q.prime_p, q.exponent_pos, by rw [hK, ← pow_mul, mul_comm]⟩
  have hNq := not_three_two_of_valid n q hd hN
  have hβbar3 : onCenterQuotient β ^ 3 = 1 := by
    have := congrArg (centerQuotientHom L) hβ3
    rwa [map_pow, map_one] at this
  have hβ'3 : MulAut.congr e' (onCenterQuotient β) ^ 3 = 1 := by
    rw [← map_pow, hβbar3, map_one]
  have hout' : MulAut.congr e' (onCenterQuotient β) ∉
      innAutDerived (StatedProj (StatedSU (n + 1) (q.p ^ q.exponent) K)) :=
    fun h => hout ((mem_innAutDerived_congr e').1 h)
  obtain ⟨A, φ, -, hφ⟩ := exists_phi_of_outer_three hdat hN hNq _ hβ'3 hout'
  have hdvd := orderOf_dvd_of_card (p := q.p) (e := 2 * q.exponent) q.prime_p
    (by have := q.exponent_pos; omega) hdat.card φ
  rw [hφ] at hdvd
  have h3e : 3 ≤ q.exponent := by
    have := Nat.le_of_dvd (by have := q.exponent_pos; omega) hdvd
    have h3 : 3 ∣ q.exponent := by omega
    exact Nat.le_of_dvd q.exponent_pos h3
  have h8 : 2 ^ 3 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact (Nat.pow_le_pow_left q.prime_p.two_le 3).trans (Nat.pow_le_pow_right q.prime_p.pos h3e)
  omega

end CFSG.LieType.SemisimpleCentralizers.HeldLang
