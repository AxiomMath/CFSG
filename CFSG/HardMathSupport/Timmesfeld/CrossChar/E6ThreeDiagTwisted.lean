module

public import CFSG.LieType.AlgebraicGroups.E6RationalTwistedFaithful
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTorality

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rootDiagUnit_mem_adjointGroup_of_isAlgClosed
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (a : Fin τ.rank → Lˣ) : rootDiagUnit τ a ∈ adjointGroup τ L := by
  refine rootDiagUnit_mem_adjointGroup_of_roots fun j => ?_
  have hd : 0 < τ.cartan.det := det_cartan_pos τ
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((a j : Lˣ) : L) (n := τ.cartan.det.toNat)
    (by omega)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hz
    exact (a j).ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, ?_⟩
  rw [show τ.cartan.det = ((τ.cartan.det.toNat : ℕ) : ℤ) by omega, zpow_natCast]
  exact Units.ext (by simpa using hz)

section Lift


@[expose] noncomputable def twistedE6DiagGL (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  ((Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K))).subtype.comp
    (compatDiagHom TwistTag.E6 K σ.toRingHom)).range

@[expose] noncomputable def twistedE6InndiagGL (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  twistedE6RootGroup K σ ⊔ twistedE6DiagGL K σ

theorem twistedE6InndiagGL_le_normalizer (K : Type) [Field K] (σ : K ≃+* K) :
    twistedE6InndiagGL K σ ≤
      Subgroup.normalizer (twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) := by
  refine sup_le Subgroup.le_normalizer ?_
  rintro _ ⟨u, rfl⟩
  exact (compatDiagHom TwistTag.E6 K σ.toRingHom u).2

@[expose] noncomputable def twistedE6InndiagConj (K : Type) [Field K] (σ : K ≃+* K) :
    ↥(twistedE6InndiagGL K σ) →* MulAut (twistedE6RootGroup K σ) :=
  (conjNormalizerHom (twistedE6InndiagGL K σ) (twistedE6RootGroup K σ)).comp
    (Subgroup.inclusion (le_inf le_rfl (twistedE6InndiagGL_le_normalizer K σ)))

theorem twistedE6InndiagConj_apply {K : Type} [Field K] {σ : K ≃+* K}
    (g : ↥(twistedE6InndiagGL K σ)) (h : twistedE6RootGroup K σ) :
    ((twistedE6InndiagConj K σ g h : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) * h * (g : ModGL TwistTag.E6.tag K)⁻¹ :=
  rfl

theorem mem_twistedE6InndiagGL_iff {K : Type} [Field K] {σ : K ≃+* K}
    {g : ModGL TwistTag.E6.tag K} :
    g ∈ twistedE6InndiagGL K σ ↔ g ∈ Subgroup.closure
      ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
        (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K))) := by
  rw [twistedE6InndiagGL, Subgroup.sup_eq_closure]

theorem range_twistedE6InndiagConj (K : Type) [Field K] (σ : K ≃+* K) :
    (twistedE6InndiagConj K σ).range = twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
  apply le_antisymm
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    have key : ∀ (x : ModGL TwistTag.E6.tag K) (hx : x ∈ Subgroup.closure
        ((twistedE6RootGroup K σ : Set (ModGL TwistTag.E6.tag K)) ∪
          (twistedE6DiagGL K σ : Set (ModGL TwistTag.E6.tag K)))),
        twistedE6InndiagConj K σ ⟨x, mem_twistedE6InndiagGL_iff.2 hx⟩ ∈
          twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with hx | ⟨u, rfl⟩
        · exact le_sup_left (b := twistedE6Diag K σ)
            ⟨⟨x, hx⟩, MulEquiv.ext fun h => Subtype.ext rfl⟩
        · exact le_sup_right (a := twistedE6Inn K σ)
            ⟨u, MulEquiv.ext fun h => Subtype.ext rfl⟩
      | one =>
        rw [show (⟨1, mem_twistedE6InndiagGL_iff.2 (Subgroup.one_mem _)⟩ :
          ↥(twistedE6InndiagGL K σ)) = 1 from rfl, map_one]
        exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
        rw [show (⟨x * y, mem_twistedE6InndiagGL_iff.2 (Subgroup.mul_mem _ hx hy)⟩ :
            ↥(twistedE6InndiagGL K σ)) = ⟨x, mem_twistedE6InndiagGL_iff.2 hx⟩ *
              ⟨y, mem_twistedE6InndiagGL_iff.2 hy⟩ from rfl, map_mul]
        exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ihx =>
        rw [show (⟨x⁻¹, mem_twistedE6InndiagGL_iff.2 (Subgroup.inv_mem _ hx)⟩ :
            ↥(twistedE6InndiagGL K σ)) = (⟨x, mem_twistedE6InndiagGL_iff.2 hx⟩)⁻¹ from rfl,
          map_inv]
        exact Subgroup.inv_mem _ ihx
    exact key g (mem_twistedE6InndiagGL_iff.1 hg)
  · refine sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩
      exact ⟨⟨g, le_sup_left (b := twistedE6DiagGL K σ) g.2⟩,
        MulEquiv.ext fun h => Subtype.ext rfl⟩
    · rintro _ ⟨u, rfl⟩
      exact ⟨⟨_, le_sup_right (a := twistedE6RootGroup K σ) ⟨u, rfl⟩⟩,
        MulEquiv.ext fun h => Subtype.ext rfl⟩

theorem twistedE6InndiagGL_le_e6InndiagGL (K : Type) [Field K] (σ : K ≃+* K) :
    twistedE6InndiagGL K σ ≤ e6InndiagGL K := by
  refine sup_le (fun g hg => adjointGroup_le_e6InndiagGL K
    (twistedFixedGroup_le_adjointGroup TwistTag.E6 K σ.toRingHom
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hg))) ?_
  rintro _ ⟨u, rfl⟩
  exact rootDiagUnit_mem_e6InndiagGL _

theorem map_twistedE6InndiagGL_le {K L : Type} [Field K] [Field L] (σ : K ≃+* K) (ι : K →+* L)
    (hroot : ∀ c : Kˣ, ∃ u : Lˣ, u ^ 3 = Units.map ι.toMonoidHom c) :
    (twistedE6InndiagGL K σ).map (baseChangeGL ι) ≤ adjointGroup Tag.E6 L :=
  (Subgroup.map_mono (twistedE6InndiagGL_le_e6InndiagGL K σ)).trans (map_e6InndiagGL_le ι hroot)

theorem map_twistedE6InndiagGL_le_twistedFixedGroup {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    (twistedE6InndiagGL K σ).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) ≤
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr := by
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  have hcomp : ∀ c, Fr (ι c) = ι (σ c) := fun c => by rw [hFr, hσ, map_pow]
  rw [twistedE6InndiagGL, Subgroup.map_sup]
  refine sup_le (CFSG.LieType.AlgebraicGroups.E6_rational_twisted_fixed_group_faithful_action
    hℓ hf K hK σ.toRingHom hσ (AlgebraicClosure K) Fr hFr).1 ?_
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  change baseChangeGL ι (rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)) ∈ _
  rw [baseChangeGL_rootDiagUnit]
  refine (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).2
    ⟨rootDiagUnit_mem_adjointGroup_of_isAlgClosed _, twistHom_rootDiagUnit fun i => ?_⟩
  rw [compatDiag_perm]
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact (hcomp _).symm

theorem twistedE6InndiagConj_injective {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Function.Injective (twistedE6InndiagConj K σ) := by
  classical
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  obtain ⟨-, -, hcent, -⟩ :=
    CFSG.LieType.AlgebraicGroups.E6_rational_twisted_fixed_group_faithful_action hℓ hf K hK
      σ.toRingHom hσ (AlgebraicClosure K) Fr hFr
  have hgΓ : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈
      twistedFixedGroup TwistTag.E6 (AlgebraicClosure K) Fr :=
    map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
      (Subgroup.mem_map_of_mem _ g.2)
  have hgC : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) ∈ Subgroup.centralizer
      ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map (baseChangeGL ι) :
        Set (ModGL TwistTag.E6.tag (AlgebraicClosure K))) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨h', hh', rfl⟩
    have e := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) =>
      ((φ ⟨h', hh'⟩ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) hg
    simp only [twistedE6InndiagConj_apply, MulAut.one_apply] at e
    rw [← map_mul, ← map_mul]
    congr 1
    calc h' * (g : ModGL TwistTag.E6.tag K) =
        ((g : ModGL TwistTag.E6.tag K) * h' * (g : ModGL TwistTag.E6.tag K)⁻¹) * g := by rw [e]
      _ = g * h' := by group
  have h1 : baseChangeGL ι (g : ModGL TwistTag.E6.tag K) = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨hgΓ, hgC⟩
    rw [hcent] at hmem
    exact (Subgroup.mem_bot).1 hmem
  exact Subtype.ext (baseChangeGL_injective ι (h1.trans (map_one _).symm))

end Lift

section Residuals


@[expose] def TwistedE6LangTorusPlaneBalanceInndiag (v : WeylGroup TwistTag.E6.tag) (p : ℕ)
    (Q : ℕ → Prop) : Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → Q (ℓ ^ f) → ∀ (K : Type) [Field K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ D₀ : Subgroup ↥(twistedE6InndiagGL K σ), (∀ x ∈ D₀, x ^ p = 1) → p < Nat.card D₀ →
      (∀ x ∈ D₀, baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) →
    ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
      localDeltaIn p H (D₀.map (twistedE6InndiagConj K σ)) = ⊥

end Residuals

section Torality


theorem twistedE6IsotropicToralInndiag_of_planeToralLang (h : TwistedE6PlaneToralLang) :
    ∀ ℓ f : ℕ, ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
      ∀ (K₁ : IntermediateField K (AlgebraicClosure K)) [Finite K₁],
      ∀ E₀ : Subgroup ↥(twistedE6InndiagGL K σ), (∀ x ∈ E₀, x ^ 3 = 1) → Nat.card E₀ = 3 ^ 2 →
        (∀ x ∈ E₀, baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈
          adjointGroup Tag.E6 K₁) →
        (∀ x y : ↥(e6Data_valid.minGroup K₁),
          (e6Isogeny K₁ x : ModGL Tag.E6 K₁) ∈
            (E₀.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL (algebraMap K K₁)) →
          (e6Isogeny K₁ y : ModGL Tag.E6 K₁) ∈
            (E₀.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL (algebraMap K K₁)) →
          x * y = y * x) →
        ∃ v : WeylGroup TwistTag.E6.tag, ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
          ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
            twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
              g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
            ∀ x ∈ E₀, baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL TwistTag.E6.tag K) ∈
              (twistedTorusOf
                (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
                (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ K₁ _ E₀ hexp hcard hC₁ hab
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  set ι₀ : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K) with hι₀
  set ι₁ : K →+* K₁ := algebraMap K K₁ with hι₁
  set ι : K₁ →+* AlgebraicClosure K := K₁.val.toRingHom with hι
  have hcomp₁ : ι.comp ι₁ = ι₀ := RingHom.ext fun _ => rfl
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius _ ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
  set P := (E₀.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL ι₁) with hP
  set S : Subgroup ↥(e6Data_valid.minGroup K₁) :=
    P.comap ((adjointGroup Tag.E6 K₁).subtype.comp (e6Isogeny K₁)) with hS
  have hSab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy => hab x y hx hy
  set φ : ↥(twistedE6InndiagGL K σ) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    (baseChangeGL ι₀).comp (twistedE6InndiagGL K σ).subtype with hφ
  have hφinj : Function.Injective φ := (baseChangeGL_injective ι₀).comp Subtype.val_injective
  have hAS : E₀.map φ ≤ S.map (e6ScToBar K₁ ι) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := e6Isogeny_surjective K₁ ⟨_, hC₁ x hx⟩
    set x' : ModGL Tag.E6 K := (x : ModGL TwistTag.E6.tag K) with hx'
    have hyv : ((e6Isogeny K₁ y : adjointGroup Tag.E6 K₁) : ModGL Tag.E6 K₁) =
        baseChangeGL ι₁ x' := congrArg Subtype.val hy
    have e2 : baseChangeGL ι (baseChangeGL ι₁ x') = baseChangeGL ι₀ x' := by
      rw [CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp₁]
    exact ⟨y, ⟨x, ⟨x, hx, rfl⟩, hyv.symm⟩, (congrArg (baseChangeGL ι) hyv).trans e2⟩
  have hexpA : ∀ x ∈ E₀.map φ, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  have hcardA : Nat.card (E₀.map φ) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective hφinj, hcard]
  have hFix : ∀ x ∈ E₀.map φ, twistHom TwistTag.E6 (AlgebraicClosure K) Fr x = x := by
    rintro _ ⟨x, -, rfl⟩
    exact ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).1
      (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
        (Subgroup.mem_map_of_mem _ x.2))).2
  obtain ⟨v, g0, hg0C, hg0, hin⟩ :=
    h ℓ f hℓ hℓ3 hf K hK K₁ ι S hSab (E₀.map φ) hAS hexpA hcardA Fr hFr hFix
  exact ⟨v, Fr, hFr, g0, hg0C, hg0, fun x hx => hin _ ⟨x, hx, rfl⟩⟩

end Torality

section Diagonal


theorem twistedE6ThreeDiagonalLarge_of_inndiag (htor : TwistedE6PlaneToralLang)
    (hT1 : ∀ v : WeylGroup TwistTag.E6.tag,
      TwistedE6LangTorusPlaneBalanceInndiag v 3 fun q => ¬ 3 ∣ q ∧ 3 ∣ q + 1 ∧ q ≠ 2) :
    TwistedE6ThreeDiagonalLarge := by
  have htorI := twistedE6IsotropicToralInndiag_of_planeToralLang htor
  intro ℓ f hℓ hℓ3 hf hq1 hq2 K _ _ hK σ hσ D hD hcard hDd _ H hH _
  have hK' : Nat.card K = (ℓ ^ f) ^ 2 := by
    rw [hK, ← pow_mul, mul_comm]
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  obtain ⟨K₁, hK₁, hroot⟩ := exists_cubeExt K
  have hinj := twistedE6InndiagConj_injective hℓ hf hK' σ hσ
  obtain ⟨E, hED, hE9, hEab⟩ := exists_isotropic_plane_of_lift (twistedE6InndiagConj K σ) hinj
    (algebraMap K K₁) (map_twistedE6InndiagGL_le σ _ hroot)
    (fun d hd => by
      have h := hDd hd
      rw [← range_twistedE6InndiagConj] at h
      exact h) hD hcard
  have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hED.trans hDd
  have hmap : (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagConj K σ) = E :=
    Subgroup.map_comap_eq_self hEr
  have hpow : ∀ x ∈ E.comap (twistedE6InndiagConj K σ), x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hD.2 _ (hED hx))
  have hcard₀ : 3 < Nat.card (E.comap (twistedE6InndiagConj K σ)) := by
    rw [← Subgroup.card_map_of_injective hinj, hmap]
    omega
  obtain ⟨E₁, hE₁, hE₁c⟩ := exists_plane_le hpow hcard₀
  have hpow₁ : ∀ x ∈ E₁, x ^ 3 = 1 := fun x hx => hpow x (hE₁ hx)
  have hC₁ : ∀ x ∈ E₁, baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈
      adjointGroup Tag.E6 K₁ := fun x _ =>
    map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
  have hmono : (E₁.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL (algebraMap K K₁)) ≤
      ((E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype).map
        (baseChangeGL (algebraMap K K₁)) :=
    Subgroup.map_mono (Subgroup.map_mono hE₁)
  obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hin⟩ := htorI ℓ f hℓ hℓ3 hf K hK' σ hσ K₁ E₁ hpow₁ hE₁c hC₁
    fun x y hx hy => hEab x y (hmono hx) (hmono hy)
  have h := hT1 v ℓ f hℓ hf ⟨h3, hq1, hq2⟩ K hK' σ hσ Fr hFr g0 hg0C hg0 E₁ hpow₁
    (by rw [hE₁c]; norm_num) hin H hH
  have hle : E₁.map (twistedE6InndiagConj K σ) ≤ D := by
    rw [← hmap] at hED
    exact (Subgroup.map_mono hE₁).trans hED
  exact le_bot_iff.1 ((localDeltaIn_antitone H hle).trans h.le)

end Diagonal

end CFSG.HardMathSupport.Timmesfeld.CrossChar
