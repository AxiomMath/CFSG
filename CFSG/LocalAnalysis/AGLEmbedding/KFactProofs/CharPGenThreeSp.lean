module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CharPGenThree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieSp

public section

namespace CFSG.AGLEmbedding.CharPGenThree

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem TauCeti.GLSymplecticFin
  CFSG.AGLEmbedding.P1Lie

section Sp

open CFSG.LieType.Steinberg.Sp

private theorem three_le_pRank_sp_triple {F : Type} [Field F] {n p : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hn : 3 ≤ n) (i : Fin n) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (Symplectic.rootDatum n F) i) := by
  have hext := steinbergExtras n F
  have hX : ∀ γ ∈ (Symplectic.rootDatum n F).roots,
      IsPGroup p ((Symplectic.rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization isParametrization hγ
  exact three_le_pRank_of_image_triple (D := Symplectic.rootDatum n F) hext hp hX rfl
    (toStdSpHom n) (fun ε hε i j k => rootsC_support hε)
    (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (c := ⟨2, by omega⟩)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (cSum_mem_roots (by omega) (by omega)) (cSum_mem_roots (by omega) (by omega))
    (cSum_mem_roots (by omega) (by omega))
    (toStd_cSum (by omega) (by omega)) (toStd_cSum (by omega) (by omega))
    (toStd_cSum (by omega) (by omega))
    (two_le_ht_cSum (by omega) (by omega)) (two_le_ht_cSum (by omega) (by omega))
    (two_le_ht_cSum (by omega) (by omega)) i

private theorem three_le_pRank_sp_pair {F : Type} [Field F] {p f : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hF : Nat.card F = p ^ f) (hf : 2 ≤ f) (i : Fin 2) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (Symplectic.rootDatum 2 F) i) :=
  three_le_pRank_of_pair (D := Symplectic.rootDatum 2 F) (steinbergExtras 2 F) hp
    isParametrization hF hf (γ₁ := cSum 2 0 1) (γ₂ := cLong 2 0)
    ((Finset.forall_mem_insert _ _ _).2 ⟨posData_of_two_le_ht rfl
      (cSum_mem_roots (by omega) (by omega)) (two_le_ht_cSum (by omega) (by omega)),
      fun γ hγ => by
        rw [Finset.mem_singleton.1 hγ]
        exact posData_of_two_le_ht rfl (cLong_mem_roots (by omega)) (two_le_ht_cLong (by omega))⟩)
    (cSum_ne_cLong le_rfl) (commRoots_cSum_cLong le_rfl) i

theorem three_le_pRank_posUnipotentExcept_sp {F : Type} [Field F] {n p f : ℕ} (hp : p.Prime)
    [CharP F p] [Finite F] (hF : Nat.card F = p ^ f)
    (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f)) (i : Fin n) :
    3 ≤ CFSG.Open.pRank p (posUnipotentExcept (Symplectic.rootDatum n F) i) := by
  rcases hn with hn | ⟨rfl, hf⟩
  · exact three_le_pRank_sp_triple hp hn i
  · exact three_le_pRank_sp_pair hp hF hf i

open CFSG.AGLEmbedding.CharPGen in
theorem exists_pGroup_glbCore3_sp {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = p ^ f)
    (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f)) (e : G ≃* StatedProj (StatedSp n F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
  have hn0 : 0 < n := by omega
  have hext := steinbergExtras n F
  have hct := isCTGroupDatum n F
  have hX : ∀ γ ∈ (rootDatum n F).roots, IsPGroup p ((rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization isParametrization hγ
  have hU : IsPGroup p (posUnipotent (rootDatum n F)) := isPGroup_iSup_pos hext hX
  let π : StatedSp n F →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (rootDatum n F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : StatedProj (StatedSp n F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_statedScalars_of_pow (Sum.inl ⟨0, hn0⟩)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hmk)) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (rootDatum n F)).map π, hU.map π,
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact2314.glbCore_map_eq_top_of_injOn Fact.out π hπ
      hinj
      (glbCore_posUnipotent_eq_top_of_le_pRank (D := rootDatum n F) hct Fact.out
        (by change 0 < n; omega)
        (fun i => three_le_pRank_posUnipotentExcept_sp (F := F) (n := n) (p := p) (f := f)
          Fact.out hF hn i))⟩

theorem exists_pGroup_glbCore3_of_model_psp {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSp n p f) (hn : 3 ≤ n ∨ (n = 2 ∧ 2 ≤ f)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 3 P = ⊤ := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact exists_pGroup_glbCore3_sp hcard hn e

end Sp

end CFSG.AGLEmbedding.CharPGenThree

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem charPGen3At_sp : CharPGen3At IsWeakSpIndex := by
  refine charPGen3At_of_pGroup ?_
  intro K _ _ _ d hd e p hp hp2 hchar hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hq, hd⟩ | ⟨r, q, hr, hd⟩
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    obtain ⟨P, hP, hcore⟩ := CFSG.AGLEmbedding.CharPGenThree.exists_pGroup_glbCore3_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) (Or.inr ⟨rfl, hq⟩)
    exact ⟨P, hP, hcore⟩
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    obtain ⟨P, hP, hcore⟩ := CFSG.AGLEmbedding.CharPGenThree.exists_pGroup_glbCore3_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) (Or.inl hr)
    exact ⟨P, hP, hcore⟩

end CFSG.AGLEmbedding
