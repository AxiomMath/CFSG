module

public import CFSG.LieType.OutStructureDispatch
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog

public section

namespace CFSG.LieType.OutStructure

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Semidihedral.SemilinearOuterQuotient

theorem mem_coordinateG_of_conj_mem_inner (K : Type) [Field K] [Finite K] {e : coordinateE K}
    (h : coordinateConjugation K e ∈ inner (coordinateG K)) :
    e ∈ (coordinateG K).subgroupOf (coordinateE K) := by
  rw [← coordinateConjugation_G_image K] at h
  obtain ⟨g, hg, hge⟩ := h
  have hge' : g = e := coordinateConjugation_injective K hge
  rwa [← hge']

theorem fieldLift_injective (K : Type) [Field K] [Finite K] :
    Function.Injective (fieldLift K) := by
  intro σ τ h
  have h' := congrArg (fieldProjection K) h
  simpa only [fieldProjection_fieldLift] using h'

theorem exists_fieldPart_coordinateG (K : Type) [Field K] [Finite K] {p p₀ f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp₀ : p₀.Prime) (hf : 0 < f)
    (hK : Nat.card K = p₀ ^ f) :
    ∃ F : Subgroup (MulAut (coordinateG K)),
      (inner (coordinateG K) ⊔ F).Normal ∧ IsCyclic ↥F ∧
      F ⊓ inner (coordinateG K) = ⊥ ∧
      ¬ p ∣ (inner (coordinateG K) ⊔ F).index ∧
      ∀ x : MulAut (coordinateG K), (∃ k : ℕ, x ^ (p ^ k) = 1) →
        x ∈ inner (coordinateG K) ⊔ F := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let G := coordinateG K
  let Q := Outer G
  let mk : MulAut G →* Q := QuotientGroup.mk' (inner G)
  let Ψ : (K ≃+* K) →* MulAut G := (coordinateConjugationEquiv K).toMonoidHom.comp (fieldLift K)
  let φ : (K ≃+* K) →* Q := mk.comp Ψ
  haveI hQcomm : IsMulCommutative Q :=
    IsMulCommutative.of_comm fun a b =>
      (coordinateOuterEquivPSL K).injective (by
        rw [map_mul, map_mul]
        exact CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm K _ _)
  have hΨinj : Function.Injective Ψ :=
    (coordinateConjugationEquiv K).injective.comp (fieldLift_injective K)
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext σ
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : Ψ σ ∈ inner G := by
        have h' : QuotientGroup.mk' (inner G) (Ψ σ) = 1 := h
        exact (QuotientGroup.eq_one_iff (N := inner G) (Ψ σ)).mp h'
      have h2 : fieldLift K σ ∈ (coordinateG K).subgroupOf (coordinateE K) :=
        mem_coordinateG_of_conj_mem_inner (K := K) (e := fieldLift K σ) h1
      have h3 : fieldLift K σ ∈ (coordinateD K).subgroupOf (coordinateE K) :=
        coordinateG_le_D K h2
      have h4 : fieldProjection K (fieldLift K σ) = 1 := by
        rw [← MonoidHom.mem_ker, fieldProjection_ker K]
        exact h3
      have h5 : σ = 1 := by
        rw [← fieldProjection_fieldLift K σ]
        exact h4
      exact h5
    · intro h
      rw [h, map_one]
  have hED : Nat.card (CoordinateQuotientED K) = f := by
    rw [Nat.card_congr (coordinateEDQuotientEquivField K).toEquiv]
    exact fieldAut_card K hp₀ hK
  have hEG : Nat.card (CoordinateQuotientEG K) =
      Nat.card (CoordinateQuotientDG K) * Nat.card (CoordinateQuotientED K) :=
    (Subgroup.relIndex_mul_relIndex _ _ _ (coordinateG_le_D K) (coordinateD_le_E K)).symm
  have hQcard : Nat.card Q = Nat.card (CoordinateQuotientDG K) * f := by
    rw [← Nat.card_congr (coordinateOuterQuotientEquiv K).toEquiv, hEG, hED]
  have hDG : Nat.card (CoordinateQuotientDG K) ∣ 2 := by
    rw [← Nat.card_congr (pglQuotientEquivCoordinateDG K).toEquiv]
    exact (card_pgl_quotient_psl_dvd K).trans (Nat.gcd_dvd_left 2 _)
  haveI hfinAut : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
      (fun σ τ h => RingEquiv.ext fun x => congrFun h x)
  haveI : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  let S : Sylow p (K ≃+* K) := default
  let C : Subgroup Q := (S : Subgroup (K ≃+* K)).map φ
  have hCcard : Nat.card C = p ^ Nat.factorization f p := by
    have h1 : Nat.card C = Nat.card (S : Subgroup (K ≃+* K)) :=
      Subgroup.card_map_of_injective (K := (S : Subgroup (K ≃+* K))) (f := φ) hφinj
    rw [h1, Sylow.card_eq_multiplicity, fieldAut_card K hp₀ hK]
  have hΦbarCard : Nat.card (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))) = f := by
    rw [Subgroup.map_top, ← fieldAut_card K hp₀ hK]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hCle : C ≤ Subgroup.map φ (⊤ : Subgroup (K ≃+* K)) := by
    intro x hx
    exact Subgroup.map_mono (le_top : (S : Subgroup (K ≃+* K)) ≤ ⊤) hx
  have hCrel : C.relIndex (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))) = S.index := by
    rw [Subgroup.relIndex_map_map_of_injective (S : Subgroup (K ≃+* K)) ⊤ hφinj,
      Subgroup.relIndex_top_right]
  have hΦidx_dvd : (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))).index ∣ 2 := by
    have h1 : (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))).index *
        Nat.card (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))) = Nat.card Q :=
      Subgroup.index_mul_card _
    rw [hΦbarCard, hQcard] at h1
    have h2 : (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))).index =
        Nat.card (CoordinateQuotientDG K) := Nat.eq_of_mul_eq_mul_right hf h1
    rw [h2]
    exact hDG
  have hΦidx : ¬ p ∣ (Subgroup.map φ (⊤ : Subgroup (K ≃+* K))).index := by
    intro h
    have h2 : p ∣ 2 := h.trans hΦidx_dvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact hp.ne_one h1
    · exact hp2 h1
  have hCp : IsPGroup p C := (S.isPGroup').map φ
  have hCidx : ¬ p ∣ C.index := by
    rw [← Subgroup.relIndex_mul_index hCle]
    intro h
    rcases hp.dvd_mul.mp h with h' | h'
    · rw [hCrel] at h'
      exact S.not_dvd_index h'
    · exact hΦidx h'
  let F : Subgroup (MulAut G) := (S : Subgroup (K ≃+* K)).map Ψ
  have hCeq : C = F.map mk :=
    (Subgroup.map_map (K := (S : Subgroup (K ≃+* K))) (f := Ψ) (g := mk)).symm
  have hCnormal : C.Normal := inferInstance
  have hsup : (inner G : Subgroup (MulAut G)) ⊔ F = C.comap mk := by
    rw [hCeq, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    exact sup_comm ((inner G : Subgroup (MulAut G))) F
  have hnorm : ((inner G : Subgroup (MulAut G)) ⊔ F).Normal := by
    rw [hsup]
    exact hCnormal.comap mk
  have hbot : F ⊓ (inner G : Subgroup (MulAut G)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxF, hxI⟩ := hx
    obtain ⟨σ, -, rfl⟩ := hxF
    have h2 : fieldLift K σ ∈ (coordinateG K).subgroupOf (coordinateE K) :=
      mem_coordinateG_of_conj_mem_inner (K := K) (e := fieldLift K σ) hxI
    have h3 : fieldLift K σ ∈ (coordinateD K).subgroupOf (coordinateE K) :=
      coordinateG_le_D K h2
    have h4 : fieldProjection K (fieldLift K σ) = 1 := by
      rw [← MonoidHom.mem_ker, fieldProjection_ker K]
      exact h3
    have h5 : σ = 1 := by
      rw [← fieldProjection_fieldLift K σ]
      exact h4
    rw [h5, map_one]
    exact Subgroup.one_mem ⊥
  have hFcyc : IsCyclic ↥F := by
    have hScyc : IsCyclic ↥(S : Subgroup (K ≃+* K)) := Subgroup.isCyclic _
    exact (Subgroup.equivMapOfInjective (S : Subgroup (K ≃+* K)) Ψ hΨinj).isCyclic.mp hScyc
  have hmap : ((inner G : Subgroup (MulAut G)) ⊔ F).map mk = C := by
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    exact hCeq.symm
  have hidx : C.index = ((inner G : Subgroup (MulAut G)) ⊔ F).index := by
    rw [← hmap]
    exact Subgroup.index_map_eq (H := (inner G : Subgroup (MulAut G)) ⊔ F)
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact le_sup_left)
  have hFidx : ¬ p ∣ ((inner G : Subgroup (MulAut G)) ⊔ F).index := by
    rw [← hidx]
    exact hCidx
  have hcov : ∀ x : MulAut G, (∃ k : ℕ, x ^ (p ^ k) = 1) →
      x ∈ (inner G : Subgroup (MulAut G)) ⊔ F := by
    intro x hx
    obtain ⟨k, hk⟩ := hx
    have hy : IsPGroup p ↥(Subgroup.zpowers (mk x)) := by
      rw [isPGroup_iff_card_dvd_pow]
      refine ⟨k, ?_⟩
      rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one, ← map_pow, hk, map_one]
    have hmem : mk x ∈ C := by
      have hle := IsPGroup.le_sylow_of_normal (N := Subgroup.zpowers (mk x)) hy
        (hCp.toSylow hCidx)
      simpa using hle (Subgroup.mem_zpowers (mk x))
    rw [hsup]
    exact hmem
  exact ⟨F, hnorm, hFcyc, hbot, hFidx, hcov⟩

theorem exists_fieldPart_of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (e : X ≃* Y) {p : ℕ}
    (h : ∃ F : Subgroup (MulAut Y),
      (inner Y ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ inner Y = ⊥ ∧
      ¬ p ∣ (inner Y ⊔ F).index ∧
      ∀ x : MulAut Y, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ inner Y ⊔ F) :
    ∃ F : Subgroup (MulAut X),
      (inner X ⊔ F).Normal ∧ IsCyclic ↥F ∧ F ⊓ inner X = ⊥ ∧
      ¬ p ∣ (inner X ⊔ F).index ∧
      ∀ x : MulAut X, (∃ k : ℕ, x ^ (p ^ k) = 1) → x ∈ inner X ⊔ F := by
  obtain ⟨F, hnorm, hcyc, hbot, hidx, hcov⟩ := h
  let ce : MulAut X ≃* MulAut Y := MulAut.congr e
  let ce' : MulAut Y ≃* MulAut X := MulAut.congr e.symm
  have hinner : inner X = (inner Y).map ce'.toMonoidHom := (inner_map_congr e.symm).symm
  have hsup : inner X ⊔ F.map ce'.toMonoidHom = (inner Y ⊔ F).map ce'.toMonoidHom := by
    rw [Subgroup.map_sup, ← hinner]
  have hce'_symm : ∀ x : MulAut X, ce'.symm x = ce x := fun _ => rfl
  refine ⟨F.map ce'.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsup]
    exact hnorm.map ce'.toMonoidHom ce'.surjective
  · exact (Subgroup.equivMapOfInjective F ce'.toMonoidHom ce'.injective).isCyclic.mp hcyc
  · rw [hinner, ← Subgroup.map_inf F (inner Y) ce'.toMonoidHom ce'.injective, hbot,
      Subgroup.map_bot]
  · rw [hsup]
    show ¬ p ∣ (Subgroup.map (ce' : MulAut Y →* MulAut X) (inner Y ⊔ F)).index
    rw [Subgroup.index_map_equiv]
    exact hidx
  · intro x hx
    rw [hsup, Subgroup.mem_map_equiv, hce'_symm]
    exact hcov (ce x) (by
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩)

theorem i713ClauseFor_lie_A1 (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) :
    I713ClauseFor (TauCeti.CFSGIndex.lie ⟨.A 1 q, hv⟩) := by
  intro K _ _ hK hnab ⟨e⟩ p hp hp2 hpRank
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e2⟩ := CFSG.AGLEmbedding.nonempty_mulEquiv_psl2GF_of_isLinTwoIndex
    (p := q.p) (n := q.exponent) (d := ⟨.A 1 q, hv⟩) ⟨q, rfl, rfl, rfl⟩
  let e3 : K ≃* coordinateG (GaloisField q.p q.exponent) :=
    e.trans (e2.trans (pslEquivCoordinateG (GaloisField q.p q.exponent)))
  have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card q.p q.exponent q.exponent_pos.ne'
  exact Or.inr (Or.inl (exists_fieldPart_of_mulEquiv e3
    (exists_fieldPart_coordinateG (K := GaloisField q.p q.exponent)
      (p := p) (p₀ := q.p) (f := q.exponent) hp hp2 q.prime_p q.exponent_pos hcard)))

end CFSG.LieType.OutStructure
