module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAbstract
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.AGLEmbedding.CharPGen

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits

theorem exists_pGroup_su {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 4 ≤ n)
    (e : G ≃* StatedProj (StatedSU n (p ^ f) F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 1 P = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF n (by omega) ζ hζ
  have hct := isCTGroupDatum hF n (by omega) ζ hζ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hX : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup p ((rootDatum hF n).rootGroup γ) := fun γ hγ =>
    isPGroup_rootGroup (unitaryInvolution_involutive hF) (SUExtras.toStd_ne_zero_of_mem_roots hγ)
  have hU : IsPGroup p (posUnipotent (rootDatum hF n)) := isPGroup_iSup_pos hext hX
  let ψ := equivStatedSU hF n
  let π : SU (unitaryInvolution F p f) n →* G :=
    e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ψ.toMonoidHom)
  have hπ : Function.Surjective π :=
    e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ψ.surjective)
  have hinj : ∀ x ∈ posUnipotent (rootDatum hF n), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ (ψ x) : StatedProj (StatedSU n (p ^ f) F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    have hk' : ψ x ^ p ^ k = 1 := by
      rw [← map_pow]
      exact (map_eq_one_iff _ ψ.injective).2 (congrArg Subtype.val hk)
    exact ψ.injective (by
      rw [map_one]
      exact eq_one_of_mem_statedScalars_of_pow (⟨0, by omega⟩ : Fin n)
        (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmk)) hk')
  exact ⟨(posUnipotent (rootDatum hF n)).map π, hU.map π,
    glbCore_map_eq_top (Fact.out) π hπ hU hinj
      (glbCore_posUnipotent_eq_top (D := rootDatum hF n) hct hext Fact.out
        (by show 2 ≤ n / 2; omega) hX)⟩

theorem exists_pGroup_of_model_psu {G : Type} [Group G] [Finite G] {n p f : ℕ} (hn : 4 ≤ n)
    (h : StatedClassicalModel G .PSU n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 1 P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact exists_pGroup_su hcard hn e

end CFSG.AGLEmbedding.CharPGen

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsSUIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ d.1 = .twistedA r q

theorem charPGenAt_su : CharPGenAt IsSUIndex := by
  refine charPGenAt_of_pGroup ?_
  intro K _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact CharPGen.exists_pGroup_of_model_psu (by omega)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)

end CFSG.AGLEmbedding
