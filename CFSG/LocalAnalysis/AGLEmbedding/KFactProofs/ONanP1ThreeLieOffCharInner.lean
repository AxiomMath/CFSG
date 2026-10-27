module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharCover

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.AGLEmbeddingD2
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

@[expose] def P1OffCharClassicalCover : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex, IsClassicalIndex d.1 →
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p ≠ d.1.characteristic → p ∣ Nat.card (Subgroup.center K) →
        (∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
            E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
            E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) →
        P1ThreeLieList p d

@[expose] def P1OffCharNoInnerCube : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (Rb : Sylow p Y) (Y₀ : Subgroup Y),
    ReducedNongeneration p Y Rb Y₀ → CatalogSimpleSections Y →
    ∀ K : Subgroup Y, IsComponentOf K ⊤ → (∀ L : Subgroup Y, IsComponentOf L ⊤ → L = K) →
      ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y) →
      (∀ c ∈ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
        c ∈ (Subgroup.center K).map K.subtype) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        p ≠ d.1.characteristic →
        (¬ ∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
            E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
            E ≤ K ⊔ Subgroup.centralizer (K : Set Y)) →
        P1ThreeLieList p d

namespace ReducedNongeneration

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y}
  {Y₀ : Subgroup Y}

theorem false_of_cube_of_le (h : ReducedNongeneration p Y Rb Y₀) {K E₂ : Subgroup Y}
    (hKn : K.Normal) (hE₂K : E₂ ≤ K) (hE₂a : IsElemAbelian p E₂) (hE₂c : Nat.card E₂ = p ^ 3)
    (hgen₂ : HyperGen p K E₂) : False := by
  obtain ⟨g, hg⟩ := exists_conj_le_sylow Rb hE₂a.2
  have hE₃a : IsElemAbelian p (E₂.map (MulAut.conj g).toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₂a _
  have hE₃c : Nat.card (E₂.map (MulAut.conj g).toMonoidHom) = p ^ 3 :=
    (Nat.card_congr (E₂.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm.trans
      hE₂c
  have hE₃N : E₂.map (MulAut.conj g).toMonoidHom ≤ (K ⊔ (Rb : Subgroup Y)).normalCore := by
    refine le_trans ?_
      (Subgroup.normal_le_normalCore.2 (le_sup_left : K ≤ K ⊔ (Rb : Subgroup Y)))
    rintro _ ⟨x, hx, rfl⟩
    exact hKn.conj_mem x (hE₂K hx) g
  exact h.false_of_hyperGen hE₃a hE₃c hg hE₃N (hyperGen_conj g hgen₂)

theorem false_of_inner_of_not_dvd (h : ReducedNongeneration p Y Rb Y₀) {K E : Subgroup Y}
    (hKn : K.Normal) {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hpd : p ≠ d.1.characteristic) (hlist : ¬ P1ThreeLieList p d)
    (hEx : HyperExFor fun _ => True) (hEa : IsElemAbelian p E) (hEc : Nat.card E = p ^ 3)
    (hker : ∀ c ∈ E ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype)
    (hin : E ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    (hz : ¬ p ∣ Nat.card (Subgroup.center K)) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  let ρ : K →* Cat d := (e : K ⧸ Subgroup.center K →* Cat d).comp
    (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ∀ k : K, ρ k = 1 ↔ k ∈ Subgroup.center K := by
    intro k
    change e (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψi, hψs⟩ := exists_quotientMap hp ρ hρk hz hEa.2 hker hin
  have hE₀ : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, hx⟩ := a.2
      obtain ⟨y, hy⟩ := b.2
      apply Subtype.ext
      show (a : Cat d) * b = b * a
      rw [← hx, ← hy, ← map_mul, ← map_mul, hEa.1.is_comm.comm x y]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := Subtype.ext (hEa.2 x x.2)
      rw [this, map_one]
  have hcard0 : Nat.card ψ.range = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hψi).toEquiv).symm.trans hEc
  obtain ⟨EL, hELa, hELc, hELgen⟩ := hEx d p hp hp2 hpd hlist ⟨ψ.range, hE₀, hcard0, trivial⟩
  have hkerρ : ρ.ker = Subgroup.center K := Subgroup.ext fun k => hρk k
  have hcop : Nat.Coprime (Nat.card ρ.ker) p := by
    rw [hkerρ]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hz).symm
  obtain ⟨E₁, hE₁a, hE₁c, hE₁img⟩ := exists_lift_isElemAbelian hp ρ hρs hcop hELa hELc
  let E₂ : Subgroup Y := E₁.map K.subtype
  have hE₂a : IsElemAbelian p E₂ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁a K.subtype
  have hE₂c : Nat.card E₂ = p ^ 3 :=
    (Nat.card_congr (E₁.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm.trans
      hE₁c
  have hE₂K : E₂ ≤ K := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hin₂ : E₂ ≤ K ⊔ Subgroup.centralizer (K : Set Y) := hE₂K.trans le_sup_left
  have hker₂ : ∀ c ∈ E₂ ⊓ Subgroup.centralizer (K : Set Y), orderOf c = p →
      c ∈ (Subgroup.center K).map K.subtype := by
    intro c hc _
    refine ⟨⟨c, hE₂K hc.1⟩, ?_, rfl⟩
    exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g g.2)
  obtain ⟨ψ₂, -, hψ₂s⟩ := exists_quotientMap hp ρ hρk hz hE₂a.2 hker₂ hin₂
  have hψ₂ : ∀ y : K, ∀ hy : y ∈ E₁, ψ₂ ⟨(y : Y), ⟨y, hy, rfl⟩⟩ = ρ y := fun y hy =>
    hψ₂s ⟨(y : Y), ⟨y, hy, rfl⟩⟩ y 1 (Subgroup.one_mem _) (by simp)
  have hrange : ψ₂.range = EL := by
    rw [← hE₁img]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := x.2
      have hx : x = ⟨(y : Y), ⟨y, hy, rfl⟩⟩ := Subtype.ext hyx.symm
      rw [hx, hψ₂ y hy]
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : Y), ⟨y, hy, rfl⟩⟩, hψ₂ y hy⟩
  have hgen₂ : HyperGen p K E₂ := by
    refine hyperGen_of_quotientMap hp ρ hρs hρk hz hE₂a.2 hE₂c hin₂ ψ₂ hψ₂s ?_
    rw [hrange]
    exact hELgen
  exact h.false_of_cube_of_le hKn hE₂K hE₂a hE₂c hgen₂

end ReducedNongeneration

theorem p1ThreeLieOffChar_of_innerEx
    (hLC : HyperExFor fun d => IsClassicalIndex d.1)
    (hLE : HyperExFor fun d => ¬ IsClassicalIndex d.1)
    (hCXE : HyperExCoverFor fun d => ¬ IsClassicalIndex d.1)
    (hCC : P1OffCharClassicalCover) (hRes : P1OffCharNoInnerCube) : P1ThreeLieOffChar := by
  intro p _ Y _ _ Rb Y₀ h hcat K hK huniq hnc hcent d hd hpd
  by_cases hex : ∃ E : Subgroup Y, E ≤ (Rb : Subgroup Y) ∧
      E ≤ (K ⊔ (Rb : Subgroup Y)).normalCore ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      E ≤ K ⊔ Subgroup.centralizer (K : Set Y)
  swap
  · exact hRes p Y Rb Y₀ h hcat K hK huniq hnc hcent d hd hpd hex
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := h.ne_two
  have hKn : K.Normal := normal_of_forall_isComponentOf_eq hK huniq
  by_cases hz : p ∣ Nat.card (Subgroup.center K)
  · by_cases hcl : IsClassicalIndex d.1
    · exact hCC p Y Rb Y₀ h hcat K hK huniq hnc hcent d hcl hd hpd hz hex
    · by_contra hlist
      obtain ⟨E₁, hE₁a, hE₁c, hgen₁⟩ := hCXE p hp hp2 K hK.2.2 d hcl hd hpd hlist hz
      refine h.false_of_cube_of_le hKn (E₂ := E₁.map K.subtype)
        (by rintro _ ⟨x, -, rfl⟩; exact x.2)
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₁a K.subtype) ?_
        (hyperGen_map_subtype hgen₁)
      exact (Nat.card_congr
        (E₁.equivMapOfInjective K.subtype K.subtype_injective).toEquiv).symm.trans hE₁c
  · by_contra hlist
    obtain ⟨E, hER, -, hEa, hEc, hin⟩ := hex
    obtain ⟨e⟩ := hd
    have hEx : HyperExFor fun _ => True :=
      HyperExFor.mono (fun d _ => em (IsClassicalIndex d.1)) (hyperExFor_or hLC hLE)
    exact h.false_of_inner_of_not_dvd hKn e hpd hlist hEx hEa hEc
      (fun c hc hcp => hcent c ⟨hER hc.1, hc.2⟩ hcp) hin hz

section Cubes


theorem p1ThreeLieOffChar_of_cubesV6 (hX : ExcCubeResidualsV4) (hGA : GriessMultipliersAllModels)
    (hCC : P1OffCharClassicalCover) (hRes : P1OffCharNoInnerCube) : P1ThreeLieOffChar :=
  p1ThreeLieOffChar_of_innerEx (hyperExFor_classical_of_orthogonal hyperExFor_orthogonal)
    (hyperExFor_exc_of_residuals hX.toV3.toV2.toResiduals) (hyperExCoverFor_exc hGA) hCC hRes

end Cubes

end CFSG.AGLEmbedding
