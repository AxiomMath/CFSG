module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Fam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenSU
public import CFSG.ClassicalInvolution.ModelFacts.Families
import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2314Abstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314

open CFSG.Open

section SL

open CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem exists_pGroup2_sl {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {r : ℕ} (hr : 2 ≤ r)
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hext := SpecialLinear.steinbergExtras r F
  have hct := SpecialLinear.isCTGroupDatum r F
  have hX : ∀ γ ∈ (SpecialLinear.rootDatum r F).roots,
      IsPGroup p ((SpecialLinear.rootDatum r F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization SL.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (SpecialLinear.rootDatum r F)) := isPGroup_iSup_pos hext hX
  have hadj : ∀ i, ∃ j, j ≠ i ∧ (SpecialLinear.rootDatum r F).cartan i j ≠ 0 :=
    exists_adj_of_isIrreducible (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_A
      (by omega : 0 < r)) hr
  let π : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (SpecialLinear.rootDatum r F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_center_of_pow
      ((QuotientGroup.eq_one_iff x).1 hmk) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (SpecialLinear.rootDatum r F)).map π, hU.map π,
    glbCore_map_eq_top_of_injOn (Fact.out) π hπ hinj
      (glbCore_two_posUnipotent_eq_top (D := SpecialLinear.rootDatum r F) hct hext Fact.out hp2
        hr hX hadj)⟩

theorem charPGen2At_sl : CharPGen2At CFSG.AGLEmbedding.IsSLIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact exists_pGroup2_sl hp2 hr
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv))

end SL

section Sp

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem exists_pGroup2_sp {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* StatedProj (StatedSp n F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  have hext := Symplectic.steinbergExtras n F
  have hct := Symplectic.isCTGroupDatum n F
  have hX : ∀ γ ∈ (Symplectic.rootDatum n F).roots,
      IsPGroup p ((Symplectic.rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization Sp.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (Symplectic.rootDatum n F)) := isPGroup_iSup_pos hext hX
  have hadj : ∀ i, ∃ j, j ≠ i ∧ (Symplectic.rootDatum n F).cartan i j ≠ 0 :=
    exists_adj_of_isIrreducible (CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanC
      (by omega : 0 < n)) hn
  let π : StatedSp n F →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (Symplectic.rootDatum n F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : StatedProj (StatedSp n F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_statedScalars_of_pow (Sum.inl ⟨0, by omega⟩)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hmk)) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (Symplectic.rootDatum n F)).map π, hU.map π,
    glbCore_map_eq_top_of_injOn (Fact.out) π hπ hinj
      (glbCore_two_posUnipotent_eq_top (D := Symplectic.rootDatum n F) hct hext Fact.out hp2
        hn hX hadj)⟩

theorem exists_pGroup2_of_model_psp {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel G .PSp n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨⟨hp, hf, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact exists_pGroup2_sp hp2 hn e

theorem charPGen2At_sp : CharPGen2At CFSG.AGLEmbedding.IsSpIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d hd e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hd⟩ | ⟨r, q, hr, hd⟩
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    exact exists_pGroup2_of_model_psp hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    exact exists_pGroup2_of_model_psp hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)

end Sp

section SU

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits

theorem isIrreducible_cartan_unitary {n : ℕ} (hn : 4 ≤ n) :
    CFSG.ClassicalInvolution.ModelFacts.IsIrreducible (cartan n) := by
  unfold cartan
  split_ifs
  · exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_cartanC (by omega)
  · exact CFSG.ClassicalInvolution.ModelFacts.isIrreducible_transpose_cartanC (by omega)

theorem exists_pGroup2_su {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ}
    (hn : 4 ≤ n) (e : G ≃* StatedProj (StatedSU n (p ^ f) F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hext := steinbergExtras hF n (by omega) ζ hζ
  have hct := isCTGroupDatum hF n (by omega) ζ hζ
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hX : ∀ γ ∈ (rootDatum hF n).roots, IsPGroup p ((rootDatum hF n).rootGroup γ) := fun γ hγ =>
    isPGroup_rootGroup (unitaryInvolution_involutive hF) (SUExtras.toStd_ne_zero_of_mem_roots hγ)
  have hU : IsPGroup p (posUnipotent (rootDatum hF n)) := isPGroup_iSup_pos hext hX
  have hadj : ∀ i, ∃ j, j ≠ i ∧ (rootDatum hF n).cartan i j ≠ 0 :=
    exists_adj_of_isIrreducible (isIrreducible_cartan_unitary hn) (by show 2 ≤ n / 2; omega)
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
      exact CFSG.AGLEmbedding.CharPGen.eq_one_of_mem_statedScalars_of_pow (⟨0, by omega⟩ : Fin n)
        (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hmk)) hk')
  exact ⟨(posUnipotent (rootDatum hF n)).map π, hU.map π,
    glbCore_map_eq_top_of_injOn (Fact.out) π hπ hinj
      (glbCore_two_posUnipotent_eq_top (D := rootDatum hF n) hct hext Fact.out hp2
        (by show 2 ≤ n / 2; omega) hX hadj)⟩

theorem exists_pGroup2_of_model_psu {G : Type} [Group G] [Finite G] {n p f : ℕ} (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (h : StatedClassicalModel G .PSU n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 2 P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact exists_pGroup2_su hp2 hcard hn e

theorem charPGen2At_su : CharPGen2At CFSG.AGLEmbedding.IsSUIndex := by
  refine charPGen2At_of_pGroup ?_
  intro K _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact exists_pGroup2_of_model_psu hp2 (by omega)
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e)

end SU

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314
