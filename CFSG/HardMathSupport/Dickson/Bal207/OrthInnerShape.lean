module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthIdxRank
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Dickson.Bal207.OrthSU38Image
import CFSG.HardMathSupport.Dickson.Bal207.SpShape
import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorUnit

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCOrthogonalAut
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LocalAnalysis.ComponentInitial
  CFSG.GroupTheory.WeirSylow

section Semilin

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {xe : V ≃ₗ[K] V}

theorem semilinConj_mem_specialBlock {σ : K ≃+* K} {Fs : V ≃+ V}
    (hF : ∀ (c : K) (v : V), Fs (c • v) = σ c • Fs v) {μ : K}
    (hFQ : ∀ v, Q (Fs v) = μ * σ (Q v)) (hFx : ∀ v, Fs (xe v) = xe (Fs v))
    (hfix : ∀ k ∈ primaryFactors xe.toLinearMap, k.map ((σ.symm : K ≃+* K) : K →+* K) = k)
    {h : K[X]} (hperf : Group.IsPerfect ↥(specialBlock Q xe h)) {f : V ≃ₗ[K] V}
    (hf : f ∈ specialBlock Q xe h) : semilinConj Fs σ hF f ∈ specialBlock Q xe h := by
  classical
  have hF' := semilin_symm_smul Fs σ hF
  have hFx' : ∀ v, Fs.symm (xe v) = xe (Fs.symm v) := fun v => by
    apply Fs.injective
    rw [AddEquiv.apply_symm_apply, hFx, AddEquiv.apply_symm_apply]
  have hFk : ∀ k ∈ primaryFactors xe.toLinearMap, ∀ v ∈ primaryComponent xe.toLinearMap k,
      Fs.symm v ∈ primaryComponent xe.toLinearMap k := by
    intro k hk v hv
    have := KCOrthComm.F_mem_primaryComponent σ.symm Fs.symm hF' hFx' hv
    rwa [hfix k hk] at this
  set φ := semilinConj Fs σ hF with hφ
  have hmapS : ∀ g ∈ supportedBlock Q xe h, φ g ∈ supportedBlock Q xe h := by
    intro g hg
    rw [mem_supportedBlock] at hg ⊢
    obtain ⟨hgI, hgo⟩ := hg
    obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp hgI
    have hgQ' : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
    refine ⟨mem_isometryCentralizer.mpr ⟨?_, fun v => ?_⟩, ?_⟩
    · exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (semilinConj_mem_orthogonalGroup Fs σ hF μ hFQ hgQ')
    · change Fs (g (Fs.symm (xe v))) = xe (Fs (g (Fs.symm v)))
      rw [hFx' v, hgx, hFx]
    · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
      have h1 := (fixes_othersSpace_iff.mp hgo) k hk hkh hkh' (Fs.symm v) (hFk k hk v hv)
      change Fs (g (Fs.symm v)) = v
      rw [h1, AddEquiv.apply_symm_apply]
  have hP'S : (specialBlock Q xe h).map φ ≤ supportedBlock Q xe h := by
    rintro _ ⟨g, hg, rfl⟩
    exact hmapS g (specialBlock_le_supportedBlock h hg)
  haveI := hperf
  have hP'perf : Group.IsPerfect ↥((specialBlock Q xe h).map φ) :=
    Group.IsPerfect.map (H := specialBlock Q xe h) φ
  have hdet : ∀ z (hz : z ∈ (specialBlock Q xe h).map φ),
      blockDet Q xe h ⟨z, hP'S hz⟩ = 1 := by
    intro z hz
    let ψ : ↥((specialBlock Q xe h).map φ) →* AdjoinRoot h :=
      (blockDet Q xe h).comp (Subgroup.inclusion hP'S)
    exact KCOrthComm.hom_eq_one_of_perfect_of_commMonoid hP'perf ψ ⟨z, hz⟩
  have hfm : φ f ∈ (specialBlock Q xe h).map φ := ⟨f, hf, rfl⟩
  exact mem_specialBlock.mpr ⟨hP'S hfm, hdet _ hfm⟩

end Semilin

theorem orthFixedIdx_mono {m n : ℕ} {i : TauCeti.LieTypeIndex} (h : OrthFixedIdx m i)
    (hmn : m ≤ n) : OrthFixedIdx n i := by
  cases i with
  | D s q => exact ⟨h.1, h.2.1, h.2.2.1, lt_of_lt_of_le h.2.2.2 hmn⟩
  | twistedD s q => exact ⟨h.1, h.2.1, h.2.2.1, lt_of_lt_of_le h.2.2.2 hmn⟩
  | twistedA r q => exact ⟨h.1, h.2.1, lt_of_lt_of_le h.2.2 hmn⟩
  | A r q => exact h
  | _ => exact h.elim

theorem exists_lie_twistedA_of_le {E : Type} [Field E] [Finite E] {k m n : ℕ}
    (hE : Nat.card E = (2 ^ k) ^ 2) (hk : k = 1 ∨ k = 3) (hm : 3 ≤ m)
    (hmq : (m, 2 ^ k) ≠ (3, 2)) (hmn : m ≤ n) :
    ∃ i : TauCeti.ValidLieTypeIndex, OrthCompIdx i.1 ∧ OrthIdxRankLt n i.1 ∧
      Nonempty ((↥(CFSG.Open.StatedSU m (2 ^ k) E) ⧸
        Subgroup.center ↥(CFSG.Open.StatedSU m (2 ^ k) E)) ≃*
          (TauCeti.CFSGIndex.lie i).Group) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : 0 < k := by omega
  have hQ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) hE hm hmq
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
  have hv : (TauCeti.LieTypeIndex.twistedA r q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff]
    refine ⟨?_, by simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]⟩
    rw [TauCeti.LieTypeIndex.inStandardRange_iff]
    refine ⟨by omega, fun hr => ?_⟩
    rw [TauCeti.PrimePower.card_def]
    show 3 ≤ 2 ^ k
    rcases hk with rfl | rfl
    · exact absurd (by subst hr; rfl) hmq
    · norm_num
  obtain ⟨-, K₀, _, _, hK₀, ⟨e₀⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  haveI : Fintype K₀ := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hKK : Fintype.card E = Fintype.card K₀ := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK₀, hE]
  let eK : E ≃+* K₀ := FiniteField.ringEquivOfCardEq hKK
  let eP := CFSG.Open.StatedSUFieldChange.statedProjSUEquiv eK (r + 1) (2 ^ k)
  let eC := QuotientGroup.quotientMulEquivOfEq hQ.2
  refine ⟨⟨.twistedA r q, hv⟩, Or.inl ⟨?_, by omega, fun h => hmq ?_⟩, ?_,
    ⟨(eC.trans eP).trans e₀.symm⟩⟩
  · rcases hk with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  · obtain ⟨h2, -, h1⟩ := h
    have : k = 1 := h1
    subst this h2
    rfl
  · show r < n
    omega

section Components

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem dims_of_orderOf_three (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hQ : (polarBilin Q).Nondegenerate) {n : ℕ} (hdim : finrank F V = 2 * n)
    (hV : IsPlusType Q ↔ Even n) (x : orthDerived Q) (hx3 : orderOf x = 3) :
    OddOrderIsometry Q 3 (x : V ≃ₗ[F] V) ∧ 3 ∣ Nat.card F + 1 ∧
      (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (x : V ≃ₗ[F] V).toLinearMap ∧
      ∃ s : ℕ, finrank F (fixedSpace (x : V ≃ₗ[F] V)) = 2 * s ∧
        s + primaryMultiplicity (x : V ≃ₗ[F] V).toLinearMap (X ^ 2 + X + 1) = n ∧
        (1 ≤ s → (IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) ↔ Even s)) := by
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have hpq : 3 ∣ Nat.card F + 1 := by
    rcases hF with h | h <;> rw [h] <;> norm_num
  have hx1 : (x : V ≃ₗ[F] V) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hx3
    omega
  exact ⟨hx, hpq, dims hx hpq hx1 hdim hV⟩

theorem exists_normal_of_fixed [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {G : Subgroup (V ≃ₗ[F] V)}
    (hGq : CFSG.IsQuasisimple ↥G) (hGle : G ≤ supportedFixedDerived Q x)
    (hGn : (G.subgroupOf (supportedFixedDerived Q x)).Normal) :
    ∃ N : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)), N.Normal ∧
      CFSG.IsQuasisimple ↥N ∧
      Nonempty (↥((G.subgroupOf (orthDerived Q)).map (piOrth Q)) ≃* ↥N) ∧
      (N.comap (supportedFixedDerivedEquiv hx :
        ↥(supportedFixedDerived Q x) →* ↥(orthDerived (Q.comp (fixedSpace x).subtype)))).map
          (supportedFixedDerived Q x).subtype = G := by
  have hGΩ : G ≤ orthDerived Q := hGle.trans hx.supportedFixedDerived_le_orthDerived
  let eGN : ↥G ≃* ↥((G.subgroupOf (supportedFixedDerived Q x)).map
      (supportedFixedDerivedEquiv hx :
        ↥(supportedFixedDerived Q x) →* ↥(orthDerived (Q.comp (fixedSpace x).subtype)))) :=
    (Subgroup.subgroupOfEquivOfLe hGle).symm.trans ((supportedFixedDerivedEquiv hx).subgroupMap _)
  let eL : ↥((G.subgroupOf (orthDerived Q)).map (piOrth Q)) ≃* ↥G :=
    (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
      (Subgroup.subgroupOfEquivOfLe hGΩ)
  refine ⟨_, hGn.map _ (supportedFixedDerivedEquiv hx).surjective,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv eGN hGq, ⟨eL.trans eGN⟩, ?_⟩
  rw [Subgroup.comap_map_eq_self_of_injective (supportedFixedDerivedEquiv hx).injective,
    Subgroup.map_subgroupOf_eq_of_le hGle]

theorem fixed_image_center_type [Nontrivial V] (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    {s : ℕ} (hs : finrank F (fixedSpace x) = 2 * s)
    (htype : 1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even s))
    {G : Subgroup (V ≃ₗ[F] V)} (hGq : CFSG.IsQuasisimple ↥G)
    (hGle : G ≤ supportedFixedDerived Q x)
    (hGn : (G.subgroupOf (supportedFixedDerived Q x)).Normal) :
    Subgroup.center ↥((G.subgroupOf (orthDerived Q)).map (piOrth Q)) = ⊥ ∧
      ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx (s + 1) i.1 ∧
        Nonempty ((↥((G.subgroupOf (orthDerived Q)).map (piOrth Q)) ⧸
          Subgroup.center ↥((G.subgroupOf (orthDerived Q)).map (piOrth Q))) ≃*
            (TauCeti.CFSGIndex.lie i).Group) := by
  obtain ⟨N, hNn, hNq, ⟨e⟩, -⟩ := exists_normal_of_fixed hQ hx hGq hGle hGn
  obtain ⟨hZ, i, hi, ⟨φ⟩⟩ :=
    (orthDerived_quasisimple_normal hF hx.polarBilin_fixed_nondegenerate hs htype).1 N hNn hNq
  refine ⟨?_, i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans φ⟩⟩
  have h2 := Subgroup.map_center_eq e
  rw [hZ] at h2
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h2

theorem fixed_not_small [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x) {s : ℕ}
    (hs : finrank F (fixedSpace x) = 2 * s)
    (htype : 1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even s))
    (hsmall : s ≤ 1 ∨ (s = 2 ∧ Nat.card F = 2)) {G : Subgroup (V ≃ₗ[F] V)}
    (hGq : CFSG.IsQuasisimple ↥G) (hGle : G ≤ supportedFixedDerived Q x)
    (hGn : (G.subgroupOf (supportedFixedDerived Q x)).Normal) : False := by
  obtain ⟨N, hNn, hNq, -, -⟩ := exists_normal_of_fixed hQ hx hGq hGle hGn
  exact orthDerived_not_quasisimple_small hx.polarBilin_fixed_nondegenerate hs htype hsmall N
    hNn hNq

theorem fixed_image_pair [Nontrivial V] (hF : Nat.card F = 2 ∨ Nat.card F = 8)
    (hQ : (polarBilin Q).Nondegenerate) {p : ℕ} {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    {s : ℕ} (hs : finrank F (fixedSpace x) = 2 * s)
    (htype : 1 ≤ s → (IsPlusType (Q.comp (fixedSpace x).subtype) ↔ Even s)) :
    ∃ C₁ C₂ : Subgroup (ProjOrthDerived Q), ∀ G : Subgroup (V ≃ₗ[F] V),
      CFSG.IsQuasisimple ↥G → G ≤ supportedFixedDerived Q x →
      (G.subgroupOf (supportedFixedDerived Q x)).Normal →
      (G.subgroupOf (orthDerived Q)).map (piOrth Q) = C₁ ∨
        (G.subgroupOf (orthDerived Q)).map (piOrth Q) = C₂ := by
  obtain ⟨N₁, N₂, hN⟩ :=
    (orthDerived_quasisimple_normal hF hx.polarBilin_fixed_nondegenerate hs htype).2
  let img : Subgroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) →
      Subgroup (ProjOrthDerived Q) := fun N =>
    (((N.comap (supportedFixedDerivedEquiv hx :
      ↥(supportedFixedDerived Q x) →* ↥(orthDerived (Q.comp (fixedSpace x).subtype)))).map
        (supportedFixedDerived Q x).subtype).subgroupOf (orthDerived Q)).map (piOrth Q)
  refine ⟨img N₁, img N₂, fun G hGq hGle hGn => ?_⟩
  obtain ⟨N, hNn, hNq, -, hG⟩ := exists_normal_of_fixed hQ hx hGq hGle hGn
  have himg : img N = (G.subgroupOf (orthDerived Q)).map (piOrth Q) :=
    congrArg (fun H : Subgroup (V ≃ₗ[F] V) => (H.subgroupOf (orthDerived Q)).map (piOrth Q)) hG
  rcases hN N hNn hNq with rfl | rfl
  · exact Or.inl himg.symm
  · exact Or.inr himg.symm

theorem two_le_primaryMultiplicity_phi {p : ℕ} {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hmem : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors x.toLinearMap)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x (X ^ 2 + X + 1))) :
    2 ≤ primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) := by
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have h1 := hx.primaryMultiplicity_pos hmem
  by_contra hlt
  have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hmem (by omega)
  have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
  rw [hbot] at hnt
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl

theorem specialBlock_phi_type (hF : Nat.card F = 2 ∨ Nat.card F = 8) {x : V ≃ₗ[F] V}
    (hx : OddOrderIsometry Q 3 x) (hmem : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors x.toLinearMap)
    (hq : CFSG.IsQuasisimple ↥(specialBlock Q x (X ^ 2 + X + 1))) :
    (Nat.card F = 2 → 4 ≤ primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) ∧
      ∀ n : ℕ, primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) ≤ n →
        ∃ i : TauCeti.ValidLieTypeIndex, OrthCompIdx i.1 ∧ OrthIdxRankLt n i.1 ∧
          Nonempty ((↥(specialBlock Q x (X ^ 2 + X + 1)) ⧸
            Subgroup.center ↥(specialBlock Q x (X ^ 2 + X + 1))) ≃*
              (TauCeti.CFSGIndex.lie i).Group) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hmem
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) := ⟨hirr⟩
  have hm2 := two_le_primaryMultiplicity_phi hx hmem hq
  obtain ⟨f, hf, hKf⟩ := exists_exp hF
  obtain ⟨d, ℓ, f', hU, B, -, hq', hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx ⟨1, rfl⟩ hmem phi_ne (reciprocal_cyc3 F).symm
  let e₁ : ↥(specialBlock Q x (X ^ 2 + X + 1)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hmem)).trans
      (MulEquiv.subgroupCongr hrange)
  have hℓ : ℓ = 2 := by
    have hf' : f' ≠ 0 := by
      rintro rfl
      have := hU.one_le
      rw [zero_mul] at this
      omega
    have h2 : ℓ ∣ 2 ^ f := by
      rw [← hKf, hq']
      exact dvd_pow_self ℓ hf'
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).mp (hU.prime.dvd_of_dvd_pow h2)
  subst hℓ
  have : Module.Finite F (AdjoinRoot (X ^ 2 + X + 1 : F[X])) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : F[X])) = Nat.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, monic_phi.2]
  have hqf : f' * d = f := by
    have h2 := hU.card
    rw [hcardE, hKf, ← pow_mul] at h2
    have := Nat.pow_right_injective le_rfl h2
    omega
  have hk : f' * d = 1 ∨ f' * d = 3 := hqf ▸ hf
  haveI := hU.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hU.charP
  have hE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : F[X])) = (2 ^ (f' * d)) ^ 2 := by
    rw [hU.card, ← pow_mul, mul_comm]
  have : Finite V := Module.finite_of_finite F
  have : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite ↥(sesqSpecialUnitaryGroup B) := Finite.of_equiv _ e₁.toEquiv
  have hsolv : ¬ Group.IsSolvable ↥(sesqSpecialUnitaryGroup B) := fun hs => by
    haveI := CFSG.LocalCores.isQuasisimple_nontrivial hq
    haveI : Group.IsPerfect ↥(specialBlock Q x (X ^ 2 + X + 1)) := hq.1
    exact Group.IsPerfect.not_isSolvable _
      (Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective)
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) 3 with hm3 | hm3
  ·
    have hm2' : Module.finrank (AdjoinRoot (X ^ 2 + X + 1 : F[X]))
        (primaryComponent x.toLinearMap (X ^ 2 + X + 1)) = 2 := by
      have : primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = 2 := by omega
      exact this
    obtain ⟨φ⟩ := CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU
      hBsymm hBl hm2'
    have hcardF : Nat.card ↥hU.fixedField = Nat.card F := by
      rw [hU.card_fixedField, hqf, hKf]
    have h8 : Nat.card F = 8 := by
      refine hF.resolve_left fun h2 => hsolv ?_
      haveI := CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
        ↥hU.fixedField (Or.inl (hcardF.trans h2))
      haveI : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) ↥hU.fixedField) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin 2) ↥hU.fixedField →* _))
          Matrix.SpecialLinearGroup.toGL_injective
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    refine ⟨fun h2 => absurd (h2.symm.trans h8) (by norm_num), fun n _ => ?_⟩
    obtain ⟨i, hi, ⟨ψ⟩⟩ := exists_lie_A_one (hcardF.trans h8) n
    obtain ⟨hi1, hi2⟩ := orthFixedIdx_orthCompIdx hi le_rfl
    exact ⟨i, hi1, hi2, ⟨(QuotientGroup.congr _ _ (e₁.trans φ)
      (Subgroup.map_center_eq (e₁.trans φ))).trans ψ⟩⟩
  ·
    have hmq : (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1), 2 ^ (f' * d)) ≠ (3, 2) := by
      intro h
      apply hsolv
      refine isSolvable_of_card_primeFactors_le_two ?_
      have hcard := (CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
        (n := primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) rfl (by omega)).2.1
      rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2] at hcard
      have e : ((2 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
          ∏ i ∈ Finset.Icc 2 3, (((2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 216 := by decide +kernel
      have h216 : Nat.card ↥(sesqSpecialUnitaryGroup B) = 216 := by
        exact_mod_cast hcard.trans e
      rw [h216, show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      decide
    refine ⟨fun h2 => ?_, fun n hmn => ?_⟩
    · by_contra h4
      refine hmq (Prod.ext ?_ ?_)
      · show primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) = 3
        omega
      · show 2 ^ (f' * d) = 2
        rw [hqf, ← hKf, h2]
    · obtain ⟨e₀, he₀⟩ := hU.exists_orthonormal_basis hBsymm hBl
      obtain ⟨e₂⟩ :=
        CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid hU e₀ he₀
      have hS : CFSG.LieType.Universal.Unitary.SUid hU.barEquiv
          (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) =
          CFSG.Open.StatedSU (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) (2 ^ (f' * d))
            (AdjoinRoot (X ^ 2 + X + 1 : F[X])) := by
        rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hU]
        exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hE _
      let e₃ := (e₂.trans (MulEquiv.subgroupCongr hS)).symm
      obtain ⟨i, hi, hr, ⟨ψ⟩⟩ := exists_lie_twistedA_of_le hE hk hm3 hmq hmn
      exact ⟨i, hi, hr, ⟨(QuotientGroup.congr _ _ (e₁.trans e₃.symm)
        (Subgroup.map_center_eq (e₁.trans e₃.symm))).trans ψ⟩⟩

end Components

theorem orthInner_comp_cases {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ∨ Nat.card F = 8) {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {n : ℕ} (hdim : d = 2 * n) (_hn : 4 ≤ n)
    (hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n)
    (x : orthDerived Q) (hx3 : orderOf x = 3) {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q)))) :
    ((X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap ∧
      2 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap (X ^ 2 + X + 1) ∧
      primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap (X ^ 2 + X + 1) ≤ n ∧
      L = componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) ∧
      CFSG.IsQuasisimple
        ↥(specialBlock Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1))) ∨
    ∃ s : ℕ, Module.finrank F (KCOrthogonal.fixedSpace (x : (Fin d → F) ≃ₗ[F] (Fin d → F))) =
        2 * s ∧ s < n ∧ L ≤ fixedComponentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) ∧
      (3 ≤ s → L = fixedComponentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F))) ∧
      Subgroup.center ↥L = ⊥ ∧
      ∃ i : TauCeti.ValidLieTypeIndex, OrthFixedIdx n i.1 ∧
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie i).Group) := by
  classical
  haveI : Nontrivial (Fin d → F) := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := F)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
  obtain ⟨hx, -, hmem, s, hs, hsm, htype⟩ :=
    dims_of_orderOf_three hF hQ (by rw [Module.finrank_fin_fun, hdim]) hV x hx3
  rcases inner_comp_cases hF hQ x hx3 hL with ⟨-, hq, hLJ⟩ | ⟨G, hGq, hGle, hGn, hG4, hLG⟩
  · exact Or.inl ⟨hmem, two_le_primaryMultiplicity_phi hx hmem hq, by omega, hLJ, hq⟩
  · haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) :=
      ⟨irreducible_of_mem_primaryFactors hmem⟩
    have hm1 := hx.primaryMultiplicity_pos hmem
    subst hLG
    obtain ⟨hZ, i, hi, hiso⟩ := fixed_image_center_type hF hQ hx hs htype hGq hGle hGn
    refine Or.inr ⟨s, hs, by omega, Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      (hGle (Subgroup.mem_subgroupOf.mp hg)), fun h3 => ?_, hZ, i,
      orthFixedIdx_mono hi (by omega), hiso⟩
    rw [hG4.resolve_left (by omega)]
    rfl

theorem orthInner_comp_unique_two {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF2 : Nat.card F = 2) {d : ℕ} {Q : QuadraticForm F (Fin d → F)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {n : ℕ} (hdim : d = 2 * n) (hn : n = 4)
    (hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n)
    {t : ProjOrthDerived Q} (ht : orderOf t = 3) {L L' : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)))
    (hL' : CFSG.Open.IsComponentOf L' (Solomon.Coordinator.fixSubgroup (MulAut.conj t))) :
    L = L' := by
  classical
  haveI : Nontrivial (Fin d → F) := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := F)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
  obtain ⟨x, rfl, hx3⟩ := exists_lift_orderOf_three hQ ht
  rw [fixSubgroup_conj_eq_centralizer] at hL hL'
  obtain ⟨hx, -, hmem, s, hs, hsm, htype⟩ :=
    dims_of_orderOf_three (Or.inl hF2) hQ (by rw [Module.finrank_fin_fun, hdim]) hV x hx3
  have key : ∀ L₀ : Subgroup (ProjOrthDerived Q), CFSG.Open.IsComponentOf L₀
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))) →
      (L₀ = componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) ∧
        4 ≤ primaryMultiplicity (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap
          (X ^ 2 + X + 1)) ∨
      (L₀ = fixedComponentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) ∧ 3 ≤ s) := by
    intro L₀ hL₀
    rcases inner_comp_cases (Or.inl hF2) hQ x hx3 hL₀ with ⟨-, hq, hLJ⟩ |
      ⟨G, hGq, hGle, hGn, hG4, hLG⟩
    · exact Or.inl ⟨hLJ, (specialBlock_phi_type (Or.inl hF2) hx hmem hq).1 hF2⟩
    · have hs3 : 3 ≤ s := by
        by_contra hlt
        refine fixed_not_small hQ hx hs htype ?_ hGq hGle hGn
        rcases Nat.lt_or_ge s 2 with h2 | h2
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, hF2⟩
      refine Or.inr ⟨?_, hs3⟩
      rw [hLG, hG4.resolve_left (by omega)]
      rfl
  rcases key L hL with ⟨h1, h1m⟩ | ⟨h1, h1s⟩ <;>
    rcases key L' hL' with ⟨h2, h2m⟩ | ⟨h2, h2s⟩
  · exact h1.trans h2.symm
  · omega
  · omega
  · exact h1.trans h2.symm

theorem orthInnerShape {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ∨ Nat.card F = 8) {d : ℕ} (hd : 0 < d) {Q : QuadraticForm F (Fin d → F)}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule F (Fin d → F), Module.finrank F U = 3 ∧ ∀ u ∈ U, Q u = 0)
    {n : ℕ} (hdim : d = 2 * n) (hn : 4 ≤ n)
    (hV : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even n)
    {t : ProjOrthDerived Q} (ht : orderOf t = 3) :
    PerfectInLayer (MulAut.conj t) ∧
      (∀ L : Subgroup (ProjOrthDerived Q),
        CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
        ∃ i : TauCeti.ValidLieTypeIndex, OrthCompIdx i.1 ∧ OrthIdxRankLt n i.1 ∧
          Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* (TauCeti.CFSGIndex.lie i).Group)) ∧
      (∀ ω : MulAut (ProjOrthDerived Q),
        MulAut.congr (coordBridge Q hd).symm ω ∈ matrixProjectiveImage Q →
        ω * MulAut.conj t = MulAut.conj t * ω → ω ^ 3 = 1 →
        ∀ L : Subgroup (ProjOrthDerived Q),
          CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
          L.map ω.toMonoidHom = L) ∧
      (∀ ω : MulAut (ProjOrthDerived Q), ω * MulAut.conj t = MulAut.conj t * ω →
        ∀ L : Subgroup (ProjOrthDerived Q),
          CFSG.Open.IsComponentOf L (Solomon.Coordinator.fixSubgroup (MulAut.conj t)) →
          L.map ω.toMonoidHom ≠ L → Subgroup.center ↥L = ⊥) := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hpl : (3 : ℕ) ≠ ringChar F := by
    rw [ringChar.eq F 2]
    norm_num
  have hlayer := LieSemisimple.perfectInLayer_conj_projOrth_of_orderOf hQ hT Nat.prime_three
    (by norm_num) hpl t ht
  obtain ⟨x, rfl, hx3⟩ := exists_lift_orderOf_three hQ ht
  obtain ⟨hx, hpq, hmem, s, hs, -, htype⟩ :=
    dims_of_orderOf_three hF hQ (by rw [Module.finrank_fin_fun, hdim]) hV x hx3
  have hcomp : ∀ L₀ : Subgroup (ProjOrthDerived Q),
      CFSG.Open.IsComponentOf L₀ (Solomon.Coordinator.fixSubgroup (MulAut.conj (piOrth Q x))) →
      CFSG.Open.IsComponentOf L₀
        (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))) := fun L₀ hL₀ => by
    rwa [fixSubgroup_conj_eq_centralizer] at hL₀
  refine ⟨hlayer, fun L hL => ?_, fun ω hα hω hω3 L hL => ?_, fun ω hω L hL hne => ?_⟩
  ·
    rcases orthInner_comp_cases hF hQ hT hdim hn hV x hx3 (hcomp L hL) with
      ⟨-, -, hmn, hLJ, hq⟩ | ⟨_, -, -, -, -, -, i, hi, hiso⟩
    · subst hLJ
      obtain ⟨i, hi, hr, ⟨φ⟩⟩ := (specialBlock_phi_type hF hx hmem hq).2 n hmn
      let e : ↥(componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)) ≃*
          ↥(specialBlock Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)) :=
        (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
          (Subgroup.subgroupOfEquivOfLe (specialBlock_le_orthDerived_of_perfect hq.1
            ((specialBlock_le_isometryCentralizer _).trans
              fun _ hg => (Subgroup.mem_inf.mp hg).1)))
      exact ⟨i, hi, hr, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans φ⟩⟩
    · obtain ⟨h1, h2⟩ := orthFixedIdx_orthCompIdx hi le_rfl
      exact ⟨i, h1, h2, hiso⟩
  ·
    by_contra hne
    haveI : Finite ((Fin d → F) ≃ₗ[F] (Fin d → F)) :=
      Finite.of_injective (fun e : (Fin d → F) ≃ₗ[F] (Fin d → F) => (e : (Fin d → F) → Fin d → F))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    haveI : Finite (ProjOrthDerived Q) := Finite.of_surjective (piOrth Q) piOrth_surjective
    have hωt : ω (piOrth Q x) = piOrth Q x := by
      apply KCOrthogonalD4.conj_injective_projOrthDerived Q hQ hT
      refine MulEquiv.ext fun g => ?_
      have h1 := congrArg (fun φ : MulAut (ProjOrthDerived Q) => φ (ω.symm g)) hω
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
        MulEquiv.apply_symm_apply] at h1
      simpa only [MulAut.conj_apply] using h1
    obtain ⟨σ, Fs, hFs, μ, -, hQF, hind⟩ := exists_semilin_of_mem_matrixProjectiveImage Q hd ω hα
    have hFx : ∀ v, Fs ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) v) =
        (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs v) := by
      have h1 := hind x
        ⟨semilinConj Fs σ hFs x, semilinConj_mem_orthDerived Fs σ hFs μ hQF x.2⟩ fun v => rfl
      have h2 : (⟨semilinConj Fs σ hFs x, semilinConj_mem_orthDerived Fs σ hFs μ hQF x.2⟩ :
          orthDerived Q) = x := piOrth_injective hQ (h1.symm.trans hωt)
      intro v
      have h3 : Fs ((x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs.symm (Fs v))) =
          (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (Fs v) :=
        LinearEquiv.congr_fun (congrArg Subtype.val h2) (Fs v)
      rwa [AddEquiv.symm_apply_apply] at h3
    have hfix : ∀ k ∈ primaryFactors (x : (Fin d → F) ≃ₗ[F] (Fin d → F)).toLinearMap,
        k.map ((σ.symm : F ≃+* F) : F →+* F) = k := by
      intro k hk
      by_cases hk1 : k = X - 1
      · rw [hk1, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
      · rw [eq_phi hx hpq hk hk1]
        simp
    have hJ : CFSG.IsQuasisimple
        ↥(specialBlock Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)) →
        (componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)).map
          ω.toMonoidHom = componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) := by
      intro hq
      have hle : (componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1)).map
          ω.toMonoidHom ≤ componentImage Q (x : (Fin d → F) ≃ₗ[F] (Fin d → F)) (X ^ 2 + X + 1) := by
        rintro _ ⟨y, ⟨g, hg, rfl⟩, rfl⟩
        refine ⟨⟨semilinConj Fs σ hFs g, semilinConj_mem_orthDerived Fs σ hFs μ hQF g.2⟩,
          Subgroup.mem_subgroupOf.mpr (semilinConj_mem_specialBlock hFs hQF hFx hfix hq.1
            (Subgroup.mem_subgroupOf.mp hg)), ?_⟩
        exact (hind g ⟨semilinConj Fs σ hFs g, semilinConj_mem_orthDerived Fs σ hFs μ hQF g.2⟩
          fun v => rfl).symm
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (f := ω.toMonoidHom) ω.injective).ge
    obtain ⟨C₁, C₂, hC⟩ := fixed_image_pair hF hQ hx hs htype
    have hcls : ∀ L₀ : Subgroup (ProjOrthDerived Q),
        CFSG.Open.IsComponentOf L₀ (Solomon.Coordinator.fixSubgroup (MulAut.conj (piOrth Q x))) →
        L₀.map ω.toMonoidHom = L₀ ∨ L₀ = C₁ ∨ L₀ = C₂ := by
      intro L₀ hL₀
      rcases inner_comp_cases hF hQ x hx3 (hcomp L₀ hL₀) with ⟨-, hq, hLJ⟩ |
        ⟨G, hGq, hGle, hGn, -, hLG⟩
      · left
        rw [hLJ]
        exact hJ hq
      · right
        rw [hLG]
        exact hC G hGq hGle hGn
    have hc1 := isComponentOf_map_of_commute hω hL
    have hc2 := isComponentOf_map_of_commute hω hc1
    have h3' : ∀ g, ω (ω (ω g)) = g := fun g => by
      have := congrArg (fun φ : MulAut (ProjOrthDerived Q) => φ g) hω3
      simpa [pow_three, MulAut.mul_apply] using this
    have h3 : ((L.map ω.toMonoidHom).map ω.toMonoidHom).map ω.toMonoidHom = L := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨_, ⟨_, ⟨g, hg, rfl⟩, rfl⟩, rfl⟩
        rwa [h3']
      · intro hy
        exact ⟨ω (ω y), ⟨ω y, ⟨y, hy, rfl⟩, rfl⟩, h3' y⟩
    have h12 : L.map ω.toMonoidHom ≠ (L.map ω.toMonoidHom).map ω.toMonoidHom := fun h =>
      hne (Subgroup.map_injective ω.injective h).symm
    have h20 : (L.map ω.toMonoidHom).map ω.toMonoidHom ≠ L := fun h => by
      have h' : ((L.map ω.toMonoidHom).map ω.toMonoidHom).map ω.toMonoidHom =
          L.map ω.toMonoidHom := by rw [h]
      rw [h3] at h'
      exact hne h'.symm
    rcases hcls L hL with hA | hA
    · exact hne hA
    rcases hcls _ hc1 with hB | hB
    · exact h12 hB.symm
    rcases hcls _ hc2 with hC' | hC'
    · exact h20 (hC'.symm.trans h3)
    rcases hA with h1 | h1 <;> rcases hB with h2 | h2 <;> rcases hC' with h4 | h4 <;>
      first
      | exact hne (h2.trans h1.symm)
      | exact h12 (h2.trans h4.symm)
      | exact h20 (h4.trans h1.symm)
  ·
    have hc := isComponentOf_map_of_commute hω hL
    rcases orthInner_comp_cases hF hQ hT hdim hn hV x hx3 (hcomp L hL) with
      ⟨-, -, -, hLJ, -⟩ | ⟨_, -, -, -, -, hZ, -⟩
    · rcases orthInner_comp_cases hF hQ hT hdim hn hV x hx3 (hcomp _ hc) with
        ⟨-, -, -, hLJ', -⟩ | ⟨_, -, -, -, -, hZ', -⟩
      · exact absurd (hLJ'.trans hLJ.symm) hne
      · let g : ↥L ≃* ↥(L.map ω.toMonoidHom) := L.equivMapOfInjective ω.toMonoidHom ω.injective
        have h2 := Subgroup.map_center_eq g
        rw [hZ'] at h2
        exact (Subgroup.map_eq_bot_iff_of_injective _ g.injective).1 h2
    · exact hZ

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
