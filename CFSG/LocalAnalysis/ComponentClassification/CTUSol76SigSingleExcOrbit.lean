module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExcTools
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormTwE6
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormD4Kernel

public noncomputable section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup

@[expose] def BigCompUniqueGrp (r : ℕ) (G : Type) [Group G] [Finite G] : Prop :=
  ∀ L L' : Subgroup G, CFSG.IsComponent L → CFSG.IsComponent L' → 2 ≤ CFSG.Open.pRank 2 L →
    2 ≤ CFSG.Open.pRank 2 L' → L = L' ∧ r ∣ Nat.card L

theorem bigCompUniqueGrp_of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {r : ℕ} (h : BigCompUniqueGrp r H) : BigCompUniqueGrp r G := by
  intro L L' hL hL' hr hr'
  have hp : ∀ M : Subgroup G, 2 ≤ CFSG.Open.pRank 2 M →
      2 ≤ CFSG.Open.pRank 2 (M.map e.toMonoidHom) :=
    fun M hM => hM.trans (SectionRank.pRank_le_map (by norm_num) e.toMonoidHom e.injective M)
  obtain ⟨h1, h2⟩ := h _ _ (LocalCores.isComponent_map_mulEquiv e hL)
    (LocalCores.isComponent_map_mulEquiv e hL') (hp L hr) (hp L' hr')
  exact ⟨Subgroup.map_injective e.injective h1,
    by rwa [card_map_of_injective (f := e.toMonoidHom) e.injective] at h2⟩

theorem bigComponentUniqueAt_of_grp {T : Type} [Group T] [Finite T] {r : ℕ}
    (h : ∀ a : T, orderOf a = 2 → BigCompUniqueGrp r (centralizer ({a} : Set T))) :
    BigComponentUniqueAt r T := by
  intro a ha L L' hL hL' hr hr'
  have hLc := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL.1).1 hL
  have hL'c := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hL'.1).1 hL'
  have hp : ∀ M : Subgroup T, M ≤ centralizer ({a} : Set T) → 2 ≤ CFSG.Open.pRank 2 M →
      2 ≤ CFSG.Open.pRank 2 (M.subgroupOf (centralizer ({a} : Set T))) := by
    intro M hM hMr
    rw [SectionRank.pRank_eq_pRank_top_subgroup,
      SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (subgroupOfEquivOfLe hM),
      ← SectionRank.pRank_eq_pRank_top_subgroup]
    exact hMr
  obtain ⟨h1, h2⟩ := h a ha _ _ hLc hL'c (hp L hL.1 hr) (hp L' hL'.1 hr')
  refine ⟨?_, ?_⟩
  · rwa [Subgroup.subgroupOf_inj, inf_of_le_left hL.1, inf_of_le_left hL'.1] at h1
  · rwa [Nat.card_congr (subgroupOfEquivOfLe hL.1).toEquiv] at h2

end CFSG.ComponentClassification.Sol76.Sig

namespace CFSG.ComponentClassification.CatLeafProof

section Uniform

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem exists_datum_uniform_conj_of_twistReduction
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {τ : Tag} (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7) {ρ : Equiv.Perm (Fin τ.rank)}
    (hA : ∀ i j, τ.cartan (ρ i) (ρ j) = τ.cartan i j)
    (hB : ∀ i j, τ.symmetrizedCartan (ρ i) (ρ j) = τ.symmetrizedCartan i j) {r₀ : ℕ}
    {reps : List (SignRep τ)}
    (htheta : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      ThetaProperties ρ r₀ (signMaskChar τ m.mask) (ToralSign.wordElt τ l))
    {D : ModGL τ k}
    (hDX : ∀ (l : List (Fin τ.rank)) (γ : Fin τ.rank → ℤ), IsRoot τ γ → ∃ μ : kˣ, ∀ c : k,
      (wordWeylMatrix τ k l * D) * pinnedX τ k γ c * (wordWeylMatrix τ k l * D)⁻¹ =
        pinnedX τ k (thetaMap (ToralSign.wordElt τ l) ρ γ) (μ * c))
    (hDT : D ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)))
    (hDG : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hpin : ∀ m ∈ reps, ∀ l ∈ m.omegaWords,
      IsTwistPinningNormalization τ k p e (signMaskChar τ m.mask)
        (thetaMap (ToralSign.wordElt τ l) ρ) (wordWeylMatrix τ k l * D))
    {x : ModGL τ k} (hred : IsFiniteToralTwistReduction τ k p e D reps x)
    (L₀ : Subgroup (ModGL τ k))
    (hL₀ : L₀ ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
      fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x})
    (hL₀c : CFSG.IsPComponent 2 (L₀.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
      (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ Dd : OrthogonalSemilinearFixedRootDatum τ p k,
      (∃ m ∈ reps, ∃ l ∈ m.omegaWords, Dd.χ = signMaskChar τ m.mask ∧
        ∀ γ, Dd.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt τ l) ρ γ)) ∧
      Dd.e = e ∧ Finite Dd.totalFixedGroup ∧ ∃ c : ModGL τ k,
      ∀ L : Subgroup (ModGL τ k),
        L ≤ ⁅fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D),
          fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓ Subgroup.centralizer {x} →
        CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup τ k)
          (frobTwistGL τ k p e D), fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)⁆ ⊓
            Subgroup.centralizer {x})) →
        ∃ J₀ : Subgroup (adjointGroup τ k), J₀ ≤ Dd.totalFixedGroup ∧
          CFSG.IsPComponent 2 (J₀.subgroupOf Dd.totalFixedGroup) ∧
          J₀.map (adjointGroup τ k).subtype = L.map (MulAut.conj c).toMonoidHom := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨r, hr, l, hl, -, hQfin, g₁, -, hcomp⟩ := hred
  set χ := signMaskChar τ r.mask with hχ
  set Q₀ := wordWeylMatrix τ k l * D with hQ₀_def
  set M := torusGroup τ k ⊔ rootSpan τ k (kernelRoots χ) with hM_def
  have hMG : M ≤ adjointGroup τ k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨-, hJc⟩ := ((hcomp 2 Nat.prime_two).1 L₀).1 ⟨hL₀, hL₀c⟩
    exact not_isPComponent_of_kernelRoots_eq_empty hne
      (inf_le_left : fixedPointsIn M (frobTwistGL τ k p e Q₀) ≤ M) _ hJc
  have hθ := htheta r hr l hl
  have hQ₀T : Q₀ ∈ Subgroup.normalizer (torusGroup τ k : Set (ModGL τ k)) :=
    mul_mem (wordWeylMatrix_mem_normalizer l) hDT
  obtain ⟨Dd, h, hhT, hDχ, hDe, hDθ, -, hX⟩ := exists_pinned_datum p hp hk he hτ hA hB hθ
    (hDX l) hQ₀T (map_conj_wordWeylMatrix_mul l hDG) (hpin r hr l hl) hne
  have hker := rootCharKernel_signCharTuple (k := k) hk2 χ
  obtain ⟨-, ⟨hMc, -, hMsm, -, -⟩, -⟩ := exceptional_toral_centralizer_identity_component τ k hk2
    (signCharTuple χ) (signCharTuple_sign χ)
  rw [toralRootPointSubgroup, toralRootGroup, hker] at hMc hMsm
  have hF₀M : ∀ g ∈ M, frobTwistGL τ k p e Q₀ g ∈ M := by
    intro g hg
    have hS : (rootSpan τ k (kernelRoots χ)).map (frobTwistGL τ k p e Q₀) =
        rootSpan τ k (kernelRoots χ) := by
      rw [map_frobTwistGL_rootSpan_of_conj p e (hDX l) fun _ hα => hα.1, hθ.image_kernelRoots]
    have hM₀ : M.map (frobTwistGL τ k p e Q₀) = M := by
      rw [hM_def, Subgroup.map_sup, map_frobTwistGL_torusGroup p e hQ₀T, hS]
    rw [← hM₀]
    exact ⟨g, hg, rfl⟩
  obtain ⟨z, hzM, hz⟩ := exists_eq_inv_mul_frobTwistGL p he Q₀ hMc hMsm hF₀M
    (Subgroup.mem_sup_left hhT)
  have hFu : frobTwistGL τ k p e Q₀ z⁻¹ = h⁻¹ * z⁻¹ := by
    rw [map_inv, hz]
    group
  have hFh : ∀ y, frobTwistGL τ k p e (h * Q₀) y = h * frobTwistGL τ k p e Q₀ y * h⁻¹ :=
    fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M (frobTwistGL τ k p e Q₀)).map (MulAut.conj z⁻¹).toMonoidHom =
      fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) :=
    map_conj_fixedPointsIn_eq M _ _ (inv_mem hzM) hFh hFu
  have hQfin' : Finite (fixedPointsIn M (frobTwistGL τ k p e Q₀)) := hQfin
  set Mh := fixedPointsIn M (frobTwistGL τ k p e (h * Q₀)) with hMh_def
  set X := Dd.totalFixedGroup with hX_def
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup τ k).subtype
      (adjointGroup τ k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ y : X, ((eX y : Mh) : ModGL τ k) =
      (((y : adjointGroup τ k)) : ModGL τ k) := fun y => rfl
  have hMhfin : Finite Mh := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj z⁻¹).subgroupMap
      (fixedPointsIn M (frobTwistGL τ k p e Q₀))).toEquiv
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  refine ⟨Dd, ⟨r, hr, l, hl, hDχ, hDθ⟩, hDe, hXfin, z⁻¹ * g₁, fun L hL hLc => ?_⟩
  obtain ⟨hJle, hJc⟩ := ((hcomp 2 Nat.prime_two).1 L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff z⁻¹ hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  set JD := J.map (MulAut.conj z⁻¹).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup τ k := hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup τ k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro y hy
    have hy' : (y : ModGL τ k) ∈ JD := hy
    have hmem : (y : ModGL τ k) ∈ X.map (adjointGroup τ k).subtype := by
      rw [hX]
      exact hJDle hy'
    obtain ⟨w, hw, hwy⟩ := hmem
    have : w = y := Subtype.ext hwy
    exact this ▸ hw
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have : (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) = (w : ModGL τ k) := by
          have := heX (eX.symm w)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm w : X) : adjointGroup τ k) : ModGL τ k) ∈ JD
        rw [this]
        exact hw
      · intro hy
        refine ⟨eX y, ?_, MulEquiv.symm_apply_apply eX y⟩
        change ((eX y : Mh) : ModGL τ k) ∈ JD
        rw [heX]
        exact hy
    rwa [h2] at h1
  refine ⟨J₀, hJ₀X, hJ₀comp, ?_⟩
  rw [hJ₀_def, Subgroup.map_subgroupOf_eq_of_le hJDG, hJD_def, hJ_def, Subgroup.map_map]
  congr 1


end Uniform

section Datum

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open scoped MatrixGroups

theorem ringChar_ne_two_of_odd_card {F : Type*} [Field F] [Finite F] (h : Odd (Nat.card F)) :
    ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := h2 ▸ ringChar.charP F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hcard] at h
  exact (Nat.not_even_iff_odd.2 h) ((Nat.even_pow' n.ne_zero).2 even_two)

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem ringChar_frobeniusFixedField_ne_two
    (D : OrthogonalSemilinearFixedRootDatum τ p k) :
    ringChar (frobeniusFixedField k p D.e) ≠ 2 := by
  have hKq : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : CharP (frobeniusFixedField k p D.e) p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      (Fact.out : p.Prime) D.one_le_e hKq
  rw [ringChar.eq (frobeniusFixedField k p D.e) p]
  exact D.odd

theorem exists_orbitGroup_of_isComponent
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hXfin : Finite D.totalFixedGroup)
    {N : Subgroup (ModGL τ k)} [Finite N] (c : ModGL τ k)
    (hall : ∀ L : Subgroup (ModGL τ k), L ≤ N → IsPComponent 2 (L.subgroupOf N) →
      ∃ J₀ : Subgroup (adjointGroup τ k), J₀ ≤ D.totalFixedGroup ∧
        IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) ∧
        J₀.map (adjointGroup τ k).subtype = L.map (MulAut.conj c).toMonoidHom)
    {L : Subgroup N} (hL : IsComponent L) : ∃ J' : Set.range D.classOrbit,
      IsQuasisimple (D.withOrbit J').orbitGroup ∧
        Nonempty (L ≃* (D.withOrbit J').orbitGroup) ∧
        (L.map N.subtype).map (MulAut.conj c).toMonoidHom =
          ((D.withOrbit J').orbitGroupC).map (adjointGroup τ k).subtype := by
  have hsub : (L.map N.subtype).subgroupOf N = L :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  obtain ⟨J₀, hJ₀X, hJ₀c, hJ₀map⟩ := hall _ (Subgroup.map_subtype_le _)
    (by rw [hsub]; exact isPComponent_two_of_isComponent hL)
  obtain ⟨J', hJ', hq⟩ := ExcSelector.exists_eq_orbitGroupC_of_isPComponent' D hXfin hJ₀X hJ₀c
  refine ⟨J', hq, ⟨?_⟩, by rw [← hJ₀map, hJ']⟩
  have e₁ : L ≃* (L.map N.subtype).map (MulAut.conj c).toMonoidHom :=
    (L.equivMapOfInjective _ N.subtype_injective).trans
      ((L.map N.subtype).equivMapOfInjective _ (MulAut.conj c).injective)
  have e₂ : J₀ ≃* J₀.map (adjointGroup τ k).subtype :=
    J₀.equivMapOfInjective _ (adjointGroup τ k).subtype_injective
  exact ((e₁.trans (MulEquiv.subgroupCongr hJ₀map.symm)).trans e₂.symm).trans
    ((MulEquiv.subgroupCongr hJ').trans
      (Subgroup.subgroupOfEquivOfLe (D.withOrbit J').orbitGroup_le_adjointGroup))

theorem bigCompUniqueGrp_of_datum
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hXfin : Finite D.totalFixedGroup)
    {N : Subgroup (ModGL τ k)} [Finite N] (c : ModGL τ k)
    (hall : ∀ L : Subgroup (ModGL τ k), L ≤ N → IsPComponent 2 (L.subgroupOf N) →
      ∃ J₀ : Subgroup (adjointGroup τ k), J₀ ≤ D.totalFixedGroup ∧
        IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) ∧
        J₀.map (adjointGroup τ k).subtype = L.map (MulAut.conj c).toMonoidHom)
    {S : Set (Fin τ.rank → ℤ)} {β₁ : Fin τ.rank → ℤ} (hβ₁ : β₁ ∈ S)
    (hβ₁θ : D.θ (toReal β₁) = toReal β₁)
    (hΔ : ∀ J' : Set.range D.classOrbit, IsQuasisimple (D.withOrbit J').orbitGroup →
      (D.withOrbit J').simpleRootsJ = S ∨ ∃ (F : Type) (_ : Field F), ringChar F ≠ 2 ∧
        Nonempty ((D.withOrbit J').orbitGroup ≃* SL(2, F))) :
    Sol76.Sig.BigCompUniqueGrp p N := by
  have hS : ∀ L : Subgroup N, IsComponent L → 2 ≤ CFSG.Open.pRank 2 L →
      ∃ J' : Set.range D.classOrbit, (D.withOrbit J').simpleRootsJ = S ∧
        Nonempty (L ≃* (D.withOrbit J').orbitGroup) ∧
        (L.map N.subtype).map (MulAut.conj c).toMonoidHom =
          ((D.withOrbit J').orbitGroupC).map (adjointGroup τ k).subtype := by
    intro L hL hr
    obtain ⟨J', hq, ⟨eL⟩, hmap⟩ := exists_orbitGroup_of_isComponent D hXfin c hall hL
    rcases hΔ J' hq with h | ⟨F, _, hF, ⟨eF⟩⟩
    · exact ⟨J', h, ⟨eL⟩, hmap⟩
    · have := Sol76.Sig.pRank_le_one_of_mulEquiv_SL hF (eL.trans eF)
      omega
  intro L L' hL hL' hr hr'
  obtain ⟨J', hJ', ⟨eL⟩, hmap⟩ := hS L hL hr
  obtain ⟨J'', hJ'', -, hmap'⟩ := hS L' hL' hr'
  have hmem : ∀ J : Set.range D.classOrbit, (D.withOrbit J).simpleRootsJ = S →
      β₁ ∈ (D.withOrbit J).simpleRootsJ := fun J h => by rw [h]; exact hβ₁
  have hJJ : J' = J'' := classOrbit_eq_of_mem_simpleRootsJ D (hmem J' hJ') (hmem J'' hJ'')
  subst hJJ
  refine ⟨?_, ?_⟩
  · rw [← hmap'] at hmap
    exact Subgroup.map_injective N.subtype_injective
      (Subgroup.map_injective (MulAut.conj c).injective hmap)
  · have hKq : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
      card_frobeniusFixedField D.one_le_e
    have : Finite (frobeniusFixedField k p D.e) :=
      Nat.finite_of_card_ne_zero (by rw [hKq]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    have : CharP (frobeniusFixedField k p D.e) p :=
      LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
        (Fact.out : p.Prime) D.one_le_e hKq
    have h1 := card_SL_dvd_orbitGroup (D.withOrbit J') (hmem J' hJ') hβ₁θ
    rw [Nat.card_congr eL.toEquiv]
    refine dvd_trans ?_ h1
    have := Sol76.Sig.ringChar_dvd_card_SL (frobeniusFixedField k p D.e)
    rwa [ringChar.eq (frobeniusFixedField k p D.e) p] at this

theorem bigCompUniqueGrp_of_datum_SL
    (D : OrthogonalSemilinearFixedRootDatum τ p k) (hXfin : Finite D.totalFixedGroup)
    {N : Subgroup (ModGL τ k)} [Finite N] (c : ModGL τ k)
    (hall : ∀ L : Subgroup (ModGL τ k), L ≤ N → IsPComponent 2 (L.subgroupOf N) →
      ∃ J₀ : Subgroup (adjointGroup τ k), J₀ ≤ D.totalFixedGroup ∧
        IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) ∧
        J₀.map (adjointGroup τ k).subtype = L.map (MulAut.conj c).toMonoidHom)
    (hΔ : ∀ J' : Set.range D.classOrbit, ∃ (F : Type) (_ : Field F), ringChar F ≠ 2 ∧
        Nonempty ((D.withOrbit J').orbitGroup ≃* SL(2, F))) :
    Sol76.Sig.BigCompUniqueGrp p N := by
  intro L L' hL hL' hr hr'
  obtain ⟨J', -, ⟨eL⟩, -⟩ := exists_orbitGroup_of_isComponent D hXfin c hall hL
  obtain ⟨F, _, hF, ⟨eF⟩⟩ := hΔ J'
  have := Sol76.Sig.pRank_le_one_of_mulEquiv_SL hF (eL.trans eF)
  omega

end Datum


section E7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups

theorem bigCompUniqueGrp_E7_innerDiag
    {K : Type} [Field K] [Finite K] [Finite (ModGL .E7 K)] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (α : MulAut (adjointGroup .E7 K)) (g : adjointGroup .E7 K)
    (a : Fin (Tag.rank .E7) → Kˣ)
    (hαg : ∀ h : adjointGroup .E7 K, (α h : ModGL .E7 K) = (g : ModGL .E7 K) * rootDiagUnit .E7 a *
      (h : ModGL .E7 K) * (rootDiagUnit .E7 a)⁻¹ * (g : ModGL .E7 K)⁻¹)
    (hαo : orderOf α = 2) : Sol76.Sig.BigCompUniqueGrp p (fixedSubgroup α) := by
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := hαo ▸ pow_orderOf_eq_one α
  have hf : 1 ≤ f := (one_le_and_three_le_of_card hp hp2 hK).1
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have : CharP (AlgebraicClosure K) p :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p K (AlgebraicClosure K)
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergBM.exists_mulEquiv_E7_inner_diagonal_fixed hp2 hf hK hαg hα2
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨n7, -, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure K) p hp2 f hf
  obtain ⟨r7, -, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure K) hp2 f hf
  set R := fixedPointsIn (adjointGroup .E7 (AlgebraicClosure K))
    (frobTwistGL .E7 (AlgebraicClosure K) p f 1) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf le_rfl (map_one _) (one_pow 1)
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let eA' : fixedSubgroup α ≃* N := eA
  refine Sol76.Sig.bigCompUniqueGrp_of_mulEquiv eA' ?_
  have h2c : ∀ S' : Subgroup N, IsComponent S' → S'.map N.subtype ≤ N ∧
      CFSG.IsPComponent 2 ((S'.map N.subtype).subgroupOf N) := fun S' hS' => by
    have hsub : (S'.map N.subtype).subgroupOf N = S' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective S'
    refine ⟨Subgroup.map_subtype_le _, ExcSelector.isPComponent_two_subgroupOf ?_⟩
    exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      (Subgroup.map_subtype_le _)).2 (by rw [hsub]; exact hS')
  by_cases hex : ∃ L₀ : Subgroup N, IsComponent L₀
  swap
  · intro L _ hL
    exact absurd ⟨L, hL⟩ hex
  obtain ⟨L₀, hL₀⟩ := hex
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, c, hall⟩ :=
    exists_datum_uniform_conj_of_twistReduction p hp2 hk hf (Or.inr (Or.inr rfl)) (ρ := 1)
      (fun _ _ => rfl) (fun _ _ => rfl) h7.theta
      (fun l _ hγ => wordWeylMatrix_mul_one_conj_pinnedX l hγ) (one_mem _)
      (map_conj_one_adjointGroup _ _) n7 (r7 x hxR hx2) _ (h2c L₀ hL₀).1 (h2c L₀ hL₀).2
  have hml : (mr.mask = 0 ∧ l = []) ∨ (mr.mask = 1 ∧ l = []) ∨
      ((mr.mask = 2 ∨ mr.mask = 3) ∧ (l = [] ∨ l = e7Word2_1)) := by
    simp only [e7SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hmr
    rcases hmr with rfl | rfl | rfl | rfl
    · simp only [e7OmegaWords0, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inl ⟨rfl, hl⟩
    · simp only [e7OmegaWords1, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inl ⟨rfl, hl⟩)
    · simp only [e7OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inr ⟨Or.inl rfl, hl⟩)
    · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
      exact Or.inr (Or.inr ⟨Or.inr rfl, hl⟩)
  obtain ⟨hfix, S, hS, hΔ⟩ := e7_datum_classes Dd hml hDχ hDθ
  exact bigCompUniqueGrp_of_datum Dd hXfin c hall hS hfix fun J' hq =>
    (hΔ J' hq).imp id fun ⟨β₀, h, hθ₀⟩ =>
      ⟨_, inferInstance, ringChar_frobeniusFixedField_ne_two (Dd.withOrbit J'),
        orbitGroup_mulEquiv_SL_of_singleton (Dd.withOrbit J') h hθ₀⟩

end E7

section TwistedE6

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem bigCompUniqueGrp_twistedE6_inner
    (J : Type) [Group J] [Finite J] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .twistedE6 0 p f) (hm : Blueprint.LieModel J .twistedE6 0 p f)
    (α : MulAut J) (hα : orderOf α = 2) (hαi : α ∈ (MulAut.conj : J →* MulAut J).range) :
    Sol76.Sig.BigCompUniqueGrp p (fixedSubgroup α) := by
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, σ, hF, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card TwistTag.E6 hp hf
    (GH74.chevalleyExceptionalModel_of_lieModel (by decide) hm).2
  have hF2 : Nat.card F = (p ^ f) ^ 2 := hF
  have : CharP F p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
    (show 1 ≤ f * 2 by omega) (by rw [hF2, ← pow_mul])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  have hα' : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  have hα'2 : MulAut.congr e α ^ 2 = 1 := by
    rw [← hα']
    exact pow_orderOf_eq_one _
  have hα'i : MulAut.congr e α ∈ twistedE6Inn F σ := by
    obtain ⟨g, hg⟩ := hαi
    exact ⟨e g, by rw [← hg, mulAut_congr_conj_twistedE6]⟩
  obtain ⟨x, hxR, hx2, ⟨eA⟩⟩ :=
    LocalAnalysis.SteinbergCE.exists_mulEquiv_twisted_E6_inner_fixed hp2 hf hF2 σ hσ hα'2 hα'i
  obtain ⟨-, h6, -⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, n6, -⟩ :=
    rational_toral_twist_semilinear_pinning_normalization (k := AlgebraicClosure F) p hp2 f hf
  obtain ⟨-, r6, -⟩ :=
    rational_inner_involution_finite_toral_twist_reduction p (AlgebraicClosure F) hp2 f hf
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.E6.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.E6 (AlgebraicClosure F))) with hR
  set N := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hN
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6)
      (iterateFrobenius (AlgebraicClosure F) p f))
    (diagramMap_pow_order TwistTag.E6 (AlgebraicClosure F))
  have hNR : N ≤ R := fun y hy => Subgroup.commutator_le_self _ hy.1
  have hNfin : Finite N := Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  let Ψ : fixedSubgroup α ≃* N := (fixedSubgroupCongrEquiv e α).trans eA
  refine Sol76.Sig.bigCompUniqueGrp_of_mulEquiv Ψ ?_
  have h2 : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ → L₀.map N.subtype ≤ N ∧
      IsPComponent 2 ((L₀.map N.subtype).subgroupOf N) := fun L₀ hL₀ => by
    have hsub : (L₀.map N.subtype).subgroupOf N = L₀ :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective L₀
    exact ⟨Subgroup.map_subtype_le _, by rw [hsub]; exact hL₀⟩
  by_cases hex : ∃ L₀ : Subgroup N, IsComponent L₀
  swap
  · intro L _ hL
    exact absurd ⟨L, hL⟩ hex
  obtain ⟨L₀, hL₀⟩ := hex
  have hL₀' := isPComponent_two_of_isComponent hL₀
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, c, hall⟩ :=
    exists_datum_uniform_conj_of_twistReduction p hp2 hk hf
      (τ := TwistTag.E6.tag) (Or.inr (Or.inl rfl)) TwistTag.E6.cartan_perm
      symmetrizedCartan_perm_E6 h6.theta
      (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.E6 l hγ)
      (diagramMap_mem_normalizer TwistTag.E6) (map_conj_diagramMap TwistTag.E6 _ (Or.inl rfl))
      n6 (r6 x hxR hx2) _ (h2 L₀ hL₀').1 (h2 L₀ hL₀').2
  have hml : (mr.mask = 0 ∨ mr.mask = 20 ∨ mr.mask = 2) ∧ l = [] := by
    have hl0 : ∀ {L : List (List (Fin (Tag.rank .E6)))}, L = [[]] → l ∈ L → l = [] := by
      rintro L rfl hl
      rcases List.mem_cons.1 hl with rfl | hl
      · rfl
      · exact absurd hl List.not_mem_nil
    rcases List.mem_cons.1 hmr with rfl | hmr
    · exact ⟨Or.inl rfl, hl0 rfl hl⟩
    rcases List.mem_cons.1 hmr with rfl | hmr
    · exact ⟨Or.inr (Or.inl rfl), hl0 rfl hl⟩
    rcases List.mem_cons.1 hmr with rfl | hmr
    · exact ⟨Or.inr (Or.inr rfl), hl0 rfl hl⟩
    exact absurd hmr List.not_mem_nil
  obtain ⟨hmask, rfl⟩ := hml
  obtain ⟨hfix, S, hS, hΔ⟩ := e6_twisted_datum_classes Dd hmask hDχ hDθ
  exact bigCompUniqueGrp_of_datum Dd hXfin c hall hS hfix fun J' hq =>
    (hΔ J' hq).imp id fun ⟨β₀, h, hθ₀⟩ =>
      ⟨_, inferInstance, ringChar_frobeniusFixedField_ne_two (Dd.withOrbit J'),
        orbitGroup_mulEquiv_SL_of_singleton (Dd.withOrbit J') h hθ₀⟩

end TwistedE6

section Triality

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem bigCompUniqueGrp_triality_inner
    (J : Type) [Group J] [Finite J] (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .trialityD4 0 p f) (hm : Blueprint.LieModel J .trialityD4 0 p f)
    (α : MulAut J) (hα : orderOf α = 2) (hαi : α ∈ (MulAut.conj : J →* MulAut J).range) :
    Sol76.Sig.BigCompUniqueGrp p (fixedSubgroup α) := by
  classical
  have hf : 1 ≤ f := hadm.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have htw : TwistedChevalleyModel J .D4 (p ^ f) := by
    rcases hm with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hCdef
  set β := MulAut.congr e α with hβdef
  have hβ2 : β ^ 2 = 1 := by
    rw [hβdef, ← map_pow, ← hα, pow_orderOf_eq_one, map_one]
  have hβi : β ∈ (MulAut.conj : C →* MulAut C).range := by
    change MulAut.congr e α ∈ OuterAutomorphisms.inner C
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαi
  obtain ⟨c, hc⟩ := hβi
  obtain ⟨-, -, -, -, -, -, hZ, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hc2 : c ^ 2 = 1 :=
    mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hc, hβ2, map_one])
  set k := AlgebraicClosure K
  set ι := algebraMap K k with hι
  have hK3' : Nat.card K = p ^ (3 * f) := by rw [hK3, ← pow_mul, mul_comm]
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp (by omega) hK3'
  have : CharP k p := charP_of_injective_algebraMap (algebraMap K k).injective p
  set Fr := iterateFrobenius k p f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  have halg := isAlgebraic_zmod_of_isAlgClosure p K k
  obtain ⟨-, -, hHR, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd K hK3 σ.toRingHom hσ k Fr hFr
  have hRF : fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) =
        twistedFixedGroup TwistTag.D4 k Fr := rfl
  set y := baseChangeGL ι (c : ModGL TwistTag.D4.tag K) with hydef
  have hyR : y ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)) := by
    rw [hRF]
    exact hHR ⟨c, c.2, rfl⟩
  have hy2 : y ^ 2 = 1 := by
    rw [hydef, ← map_pow, ← Subgroup.coe_pow, hc2, Subgroup.coe_one, map_one]
  let φ : C →* ModGL TwistTag.D4.tag k := (baseChangeGL ι).comp C.subtype
  have hφ : Function.Injective φ := (baseChangeGL_injective ι).comp Subtype.val_injective
  have hmap : (fixedSubgroup (MulAut.conj c)).map φ =
      ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {y} := by
    rw [hRF, hder]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨a, a.2, rfl⟩, ?_⟩
      have ha' : c * a * c⁻¹ = a := ha
      have hac : a * c = c * a := by
        calc a * c = c * a * c⁻¹ * c := by rw [ha']
          _ = c * a := by group
      change baseChangeGL ι (a : ModGL TwistTag.D4.tag K) * y =
        y * baseChangeGL ι (a : ModGL TwistTag.D4.tag K)
      rw [hydef, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hac]
    · rintro ⟨⟨a, ha, rfl⟩, hay⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      change c * ⟨a, ha⟩ * c⁻¹ = ⟨a, ha⟩
      have hac : (⟨a, ha⟩ : C) * c = c * ⟨a, ha⟩ := by
        refine Subtype.ext (baseChangeGL_injective ι ?_)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
        exact hay
      rw [← hac]
      group
  set N := ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p f (diagramMap TwistTag.D4 k))⁆ ⊓
      Subgroup.centralizer {y} with hN
  let Φ : fixedSubgroup (MulAut.conj c) ≃* N :=
    ((fixedSubgroup (MulAut.conj c)).equivMapOfInjective φ hφ).trans
      (MulEquiv.subgroupCongr hmap)
  let Ψ : fixedSubgroup α ≃* N := ((fixedSubgroupCongrEquiv e α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc.symm))).trans Φ
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite N := Finite.of_equiv _ Φ.toEquiv
  refine Sol76.Sig.bigCompUniqueGrp_of_mulEquiv Ψ ?_
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp2 f hf
  obtain ⟨-, -, r4⟩ := rational_inner_involution_finite_toral_twist_reduction p k hp2 f hf
  have h2 : ∀ L₀ : Subgroup N, IsPComponent 2 L₀ → L₀.map N.subtype ≤ N ∧
      IsPComponent 2 ((L₀.map N.subtype).subgroupOf N) := fun L₀ hL₀ => by
    have hsub : (L₀.map N.subtype).subgroupOf N = L₀ :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective L₀
    exact ⟨Subgroup.map_subtype_le _, by rw [hsub]; exact hL₀⟩
  by_cases hex : ∃ L₀ : Subgroup N, IsComponent L₀
  swap
  · intro L _ hL
    exact absurd ⟨L, hL⟩ hex
  obtain ⟨L₀, hL₀⟩ := hex
  have hL₀' := isPComponent_two_of_isComponent hL₀
  obtain ⟨Dd, ⟨mr, hmr, l, hl, hDχ, hDθ⟩, hDe, hXfin, c', hall⟩ :=
    exists_datum_uniform_conj_of_twistReduction p hp2 halg hf
      (τ := TwistTag.D4.tag) (Or.inl rfl) TwistTag.D4.cartan_perm symmetrizedCartan_perm_D4
      h4.theta (fun l _ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 l hγ)
      (diagramMap_mem_normalizer TwistTag.D4) (map_conj_diagramMap TwistTag.D4 _ (Or.inl rfl))
      n4 (r4 y hyR hy2) _ (h2 L₀ hL₀').1 (h2 L₀ hL₀').2
  have hθ := h4.theta mr hmr l hl
  rcases List.mem_cons.1 hmr with rfl | hmr
  ·
    rcases List.mem_cons.1 hl with rfl | hl
    swap
    · exact absurd hl List.not_mem_nil
    obtain ⟨hfix, hΔ⟩ := d4_zero_datum_classes Dd hDχ hDθ
    exact bigCompUniqueGrp_of_datum Dd hXfin c' hall (S := Set.range d4FundRoot) ⟨2, rfl⟩ hfix
      fun J' hq => Or.inl (hΔ J' hq)
  rcases List.mem_cons.1 hmr with rfl | hmr
  swap
  · exact absurd hmr List.not_mem_nil
  have hθ' : ThetaProperties TwistTag.D4.perm 3 Dd.χ
      (ToralSign.wordElt TwistTag.D4.tag l) := by
    rw [hDχ]
    exact hθ
  refine bigCompUniqueGrp_of_datum_SL Dd hXfin c' hall fun J' => ?_
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := d4_four_orbitGroup_mulEquiv_SL Dd hDχ hθ' hDθ J'
  have hpo : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hodd : Odd (Nat.card F) := by
    rcases hF with hF | hF
    · rw [hF]
      exact hpo.pow
    · rw [hF]
      exact hpo.pow.pow
  exact ⟨F, inferInstance, ringChar_ne_two_of_odd_card hodd, ⟨eF⟩⟩

end Triality

end CFSG.ComponentClassification.CatLeafProof
