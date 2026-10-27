module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSU

public section

namespace CFSG.AGLEmbedding.CharPGenThree

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem CFSG.AGLEmbedding.P1Lie

section SU

variable {n : ℕ} {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem three_le_pRank_posUnipotentExcept_su (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n)
    (i : Fin (n / 2)) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (rootDatum hF n) i) := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF n (by omega) ζ hζ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hX : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup p ((rootDatum hF n).rootGroup γ) := fun γ hγ =>
    isPGroup_rootGroup (unitaryInvolution_involutive hF) (SUExtras.toStd_ne_zero_of_mem_roots hγ)
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · have h1 : Nat.card F = 1 := by simpa using hF
      have h2 : 1 < Nat.card F := Finite.one_lt_card
      omega
    · exact h
  have hne : uSum n ≠ uHead n := fun h => by
    have h1 := congrArg (fun v => Unitary.toStd n v ⟨1, by omega⟩) h
    rw [toStd_uSum hn, toStd_uHead hn] at h1
    by_cases he : Even n <;> simp [he, Fin.ext_iff] at h1
  refine three_le_pRank_of_weighted_pair (D := rootDatum hF n) hext Fact.out
    (γ₁ := uSum n) (γ₂ := uHead n) (w₁ := 2 * f) (w₂ := 1)
    (exists_elemAbelian_uSum hF hn)
    (exists_elemAbelian_of_pGroup_ne_bot Fact.out (hX _ (uHead_mem_roots hn))
      (hext.ne_bot _ (uHead_mem_roots hn))) ?_ hne (commRoots_uSum_uHead hF hn) (by omega) i
  exact (Finset.forall_mem_insert _ _ _).2 ⟨⟨uSum_mem_roots hn, uSum_pos hn, uSum_ne_two_smul hn⟩,
    fun γ hγ => by
      rw [Finset.mem_singleton.1 hγ]
      exact ⟨uHead_mem_roots hn, uHead_pos hn, uHead_ne_two_smul hn⟩⟩

open CFSG.AGLEmbedding.CharPGen in
theorem exists_pGroup_glbCore3_su {G : Type} [Group G] [Finite G]
    (hF : Nat.card F = (p ^ f) ^ 2) (hn : 4 ≤ n) (e : G ≃* StatedProj (StatedSU n (p ^ f) F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
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
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn Fact.out π hπ
      hinj
      (glbCore_posUnipotent_eq_top_of_le_pRank (D := rootDatum hF n) hct Fact.out
        (by change 0 < n / 2; omega)
        (fun i => three_le_pRank_posUnipotentExcept_su (F := F) (p := p) (f := f) hF hn i))⟩

theorem exists_pGroup_glbCore3_of_model_psu {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (hn : 4 ≤ n) (h : StatedClassicalModel G .PSU n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact exists_pGroup_glbCore3_su hcard hn e

end SU

end CFSG.AGLEmbedding.CharPGenThree

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem charPGen3At_su : CharPGen3At IsSUIndex := by
  refine charPGen3At_of_pGroup ?_
  intro K _ _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  obtain ⟨P, hP, hcore⟩ := CFSG.AGLEmbedding.CharPGenThree.exists_pGroup_glbCore3_of_model_psu
    (by omega) (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)
  exact ⟨P, hP, hcore⟩

end CFSG.AGLEmbedding
