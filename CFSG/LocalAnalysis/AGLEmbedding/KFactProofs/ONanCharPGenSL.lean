module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAt
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCharPGenAbstract
public import CFSG.LieType.Steinberg.Classical.SpecialLinear

public section

namespace CFSG.AGLEmbedding.CharPGen

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem eq_one_of_mem_center_of_pow {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ}
    {x : Matrix.SpecialLinearGroup (Fin (r + 1)) F} (hx : x ∈ Subgroup.center _) {k : ℕ}
    (hk : x ^ p ^ k = 1) : x = 1 := by
  obtain ⟨c, -, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  have h1 : (Matrix.scalar (Fin (r + 1)) (c ^ p ^ k)) = 1 := by
    rw [map_pow, hc, ← Matrix.SpecialLinearGroup.coe_pow, hk]
    rfl
  have h2 := congrFun (congrFun h1 0) 0
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
  have hc1 : c = 1 := eq_one_of_pow_char_pow_eq_one h2
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem exists_pGroup_sl {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] [CharP F p] {r : ℕ} (hr : 2 ≤ r)
    (e : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) :
    ∃ P : Subgroup G, IsPGroup p P ∧ GLBCore p 1 P = ⊤ := by
  have hext := SpecialLinear.steinbergExtras r F
  have hct := SpecialLinear.isCTGroupDatum r F
  have hX : ∀ γ ∈ (SpecialLinear.rootDatum r F).roots,
      IsPGroup p ((SpecialLinear.rootDatum r F).rootGroup γ) := fun γ hγ =>
    isPGroup_of_isParametrization SL.isParametrization hγ
  have hU : IsPGroup p (posUnipotent (SpecialLinear.rootDatum r F)) := isPGroup_iSup_pos hext hX
  let π : Matrix.SpecialLinearGroup (Fin (r + 1)) F →* G :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' _)
  have hπ : Function.Surjective π := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : ∀ x ∈ posUnipotent (SpecialLinear.rootDatum r F), π x = 1 → x = 1 := by
    intro x hx hx1
    have hmk : (QuotientGroup.mk' _ x : Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) = 1 :=
      e.symm.injective (by rw [map_one]; exact hx1)
    obtain ⟨k, hk⟩ := hU ⟨x, hx⟩
    exact eq_one_of_mem_center_of_pow ((QuotientGroup.eq_one_iff x).1 hmk)
      (congrArg Subtype.val hk)
  exact ⟨(posUnipotent (SpecialLinear.rootDatum r F)).map π, hU.map π,
    glbCore_map_eq_top (Fact.out) π hπ hU hinj
      (glbCore_posUnipotent_eq_top (D := SpecialLinear.rootDatum r F) hct hext Fact.out hr hX)⟩

end CFSG.AGLEmbedding.CharPGen

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def IsSLIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 2 ≤ r ∧ d.1 = .A r q

theorem charPGenAt_sl : CharPGenAt IsSLIndex := by
  refine charPGenAt_of_pGroup ?_
  intro K _ _ d ⟨r, q, hr, hd⟩ e p hp hp2 hchar hrank
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd hchar
  subst hd
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  exact CharPGen.exists_pGroup_sl hr
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv))

end CFSG.AGLEmbedding
