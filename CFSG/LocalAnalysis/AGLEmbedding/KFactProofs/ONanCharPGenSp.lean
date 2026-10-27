module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAbstract
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier
public import CFSG.LieType.Steinberg.Classical.Symplectic.Basic

public section

namespace CFSG.AGLEmbedding.CharPGen

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem exists_pGroup_sp {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* StatedProj (StatedSp n F)) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 1 P = ⊤ := by
  have hext := Symplectic.steinbergExtras n F
  have hct := Symplectic.isCTGroupDatum n F
  have hX : ∀ γ ∈ (Symplectic.rootDatum n F).roots,
      IsPGroup p ((Symplectic.rootDatum n F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization Sp.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (Symplectic.rootDatum n F)) := isPGroup_iSup_pos hext hX
  let π : StatedSp n F →* G := e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (Symplectic.rootDatum n F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : StatedProj (StatedSp n F)) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_statedScalars_of_pow (Sum.inl ⟨0, by omega⟩)
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hmk)) (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (Symplectic.rootDatum n F)).map π, hU.map π,
    glbCore_map_eq_top (Fact.out) π hπ hU hinj
      (glbCore_posUnipotent_eq_top (D := Symplectic.rootDatum n F) hct hext Fact.out hn hX)⟩

theorem exists_pGroup_of_model_psp {G : Type} [Group G] [Finite G] {n p f : ℕ}
    (h : StatedClassicalModel G .PSp n p f) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 1 P = ⊤ := by
  obtain ⟨⟨hp, hf, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite F
  have : CharP F p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  exact exists_pGroup_sp hn e

end CFSG.AGLEmbedding.CharPGen

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsSpIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, d.1 = .B 2 q) ∨
    ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ d.1 = .C r q

theorem charPGenAt_sp : CharPGenAt IsSpIndex := by
  refine charPGenAt_of_pGroup ?_
  intro K _ _ d hd e p hp hp2 hchar hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  rcases hd with ⟨q, hd⟩ | ⟨r, q, hr, hd⟩
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    exact CharPGen.exists_pGroup_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e)
  · simp only at hd hchar
    subst hd
    have hpq : p = q.p := by simpa using hchar
    subst hpq
    exact CharPGen.exists_pGroup_of_model_psp
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e)

end CFSG.AGLEmbedding
