module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwEquiv
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwPin
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwA2
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer6
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux4
public import CFSG.LieType.Chevalley.EvenTrialityTraceCommutators

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.Open
open scoped Matrix

@[expose] def e6RootsE8 : Set (Fin Tag.E8.rank → ℤ) :=
  {δ | ∃ k : Fin 6, δ = Pi.single (e8E6Node k) 1 ∨ δ = -Pi.single (e8E6Node k) 1}

theorem e6_perp_a2_foldr : ∀ (k : Fin 6) (i j : Fin 3),
    (Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ
      (wordL.foldr (reflect .E8) (e8a2Weight i) - wordL.foldr (reflect .E8) (e8a2Weight j))) = 0 := by
  decide +kernel


theorem wbE8_a2W (k : Fin 3) : wbE8 a2W k = wordL.foldr (reflect .E8) (e8a2Weight k) := by
  rw [wbE8, a2W]
  exact wordProd_smul (τ := Tag.E8) wordL _

theorem perp_e6_sigma (k : Fin 6) (i j : Fin 3) :
    (Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ sigmaRootE8 a2W i j) = 0 := by
  rw [sigmaRootE8, wbE8_a2W, wbE8_a2W]
  exact e6_perp_a2_foldr k i j

section Field

variable {K L : Type} [Field K] [Field L]

theorem bc_mem_adjointGroup {K₁ K₂ : Type} [Field K₁] [Field K₂] (f : K₁ →+* K₂)
    {g : ModGL Tag.E8 K₁} (hg : g ∈ adjointGroup Tag.E8 K₁) :
    baseChangeGL f g ∈ adjointGroup Tag.E8 K₂ := by
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, c, h | h⟩ := hy
    · rw [show y = xUnit Tag.E8 K₁ i c from Units.ext h, baseChangeGL_xUnit]
      exact xUnit_mem_adjointGroup _ _
    · rw [show y = yUnit Tag.E8 K₁ i c from Units.ext h, baseChangeGL_yUnit]
      exact yUnit_mem_adjointGroup _ _
  | one => simpa using one_mem _
  | mul x y _ _ hx hy => simpa using mul_mem hx hy
  | inv x _ hx => simpa using inv_mem hx

theorem commute_e6_a2 {g g' : ModGL Tag.E8 L} (hg : g ∈ rootSpan Tag.E8 L e6RootsE8)
    (hg' : g' ∈ (rhoSigmaE8 L a2W).range) : Commute g g' := by
  rw [rhoSigmaE8_range, sigmaSetE8_eq] at hg'
  refine commute_of_mem_rootSpan (fun α hα β hβ s t => ?_) hg hg'
  obtain ⟨i, j, hij, rfl⟩ := hβ
  have hcomm := (simply_laced_orthogonal_root_commutation (τ := Tag.E8)
    (Or.inr (Or.inr (Or.inr rfl)))).2 L
  obtain ⟨k, rfl | rfl⟩ := hα
  · exact hcomm _ _ (isRoot_single _ _) (isRoot_sigmaRootE8 a2W hij) (perp_e6_sigma k i j) _
      (Subgroup.subset_closure ⟨s, rfl⟩) _ (Subgroup.subset_closure ⟨t, rfl⟩)
  · refine hcomm _ _ (isRoot_neg_single _ _) (isRoot_sigmaRootE8 a2W hij) ?_ _
      (Subgroup.subset_closure ⟨s, rfl⟩) _ (Subgroup.subset_closure ⟨t, rfl⟩)
    rw [neg_dotProduct, perp_e6_sigma, neg_zero]

theorem bc_mem_rootSpan_e6 (ι : K →+* L)
    (Ψ : ↥(e6Data_valid.minGroup K) →* ↥(adjointGroup Tag.E8 K))
    (hΨ : ∀ (k : Fin 6) (c : K),
      Ψ (e6Data_valid.xm K (Pi.single k 1) c) = e8Par K (Pi.single (e8E6Node k) 1) c ∧
      Ψ (e6Data_valid.xm K (-Pi.single k 1) c) = e8Par K (-Pi.single (e8E6Node k) 1) c)
    (y : ↥(e6Data_valid.minGroup K)) :
    baseChangeGL ι ((Ψ y : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) ∈
      rootSpan Tag.E8 L e6RootsE8 := by
  obtain ⟨s, -, -, hsc⟩ := exists_sign_e8Par (K := K) ι
  have hΨ' : ∀ (k : Fin (Tag.rank .E6)) (c : K),
      Ψ (e6Data_valid.xm K (Pi.single k 1) c) = e8Par K (Pi.single (e8E6Node k) 1) c ∧
      Ψ (e6Data_valid.xm K (-Pi.single k 1) c) = e8Par K (-Pi.single (e8E6Node k) 1) c :=
    fun k c => hΨ k c
  let G : ↥(e6Data_valid.minGroup K) →* ModGL Tag.E8 L :=
    (baseChangeGL ι).comp ((adjointGroup Tag.E8 K).subtype.comp Ψ)
  have hmem : ∀ {α : Fin Tag.E8.rank → ℤ} (c : L), α ∈ e6RootsE8 →
      pinnedX Tag.E8 L α c ∈ rootSpan Tag.E8 L e6RootsE8 := fun c hα =>
    le_iSup₂ (f := fun β (_ : β ∈ e6RootsE8) => rootSubgroup Tag.E8 L β) _ hα
      (Subgroup.subset_closure ⟨c, rfl⟩)
  have hle : Subgroup.closure {g | ∃ (i : Fin (Tag.rank .E6)) (c : K),
      g = e6Data_valid.xm K (Pi.single i 1) c ∨ g = e6Data_valid.xm K (-Pi.single i 1) c} ≤
      (rootSpan Tag.E8 L e6RootsE8).comap G := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · show baseChangeGL ι ((Ψ (e6Data_valid.xm K (Pi.single i 1) c) :
        ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) ∈ rootSpan Tag.E8 L e6RootsE8
      rw [(hΨ' i c).1, hsc (isRoot_single _ _)]
      exact hmem _ ⟨i, Or.inl rfl⟩
    · show baseChangeGL ι ((Ψ (e6Data_valid.xm K (-Pi.single i 1) c) :
        ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) ∈ rootSpan Tag.E8 L e6RootsE8
      rw [(hΨ' i c).2, hsc (isRoot_neg_single _ _)]
      exact hmem _ ⟨i, Or.inr rfl⟩
  rw [CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top e6Data_valid K] at hle
  exact hle (Subgroup.mem_top y)

theorem twN_conj_sigmaRoot (b : Fin Tag.E8.rank → Lˣ) (i j : Fin 3) (hij : i ≠ j) :
    ∃ c : Lˣ, ∀ t : L, twN b * pinnedX Tag.E8 L (sigmaRootE8 a2W i j) t * (twN b)⁻¹ =
      pinnedX Tag.E8 L (sigmaRootE8 a2W j i) ((c : L) * t) := by
  obtain ⟨ε, hε, hεc⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv L tw8W (isRoot_sigmaRootE8 a2W hij)
  refine ⟨rootChar b (sigmaRootE8 a2W j i) * Units.mkOfMulEqOne ε ε hε, fun t => ?_⟩
  rw [twN_conj, hεc, tw8W_smul_sigmaRoot,
    rootDiagUnit_conj_pinnedX b (isRoot_sigmaRootE8 a2W hij.symm), Units.val_mul,
    Units.val_mkOfMulEqOne, mul_assoc]

theorem twN_mem_familyGroup [IsAlgClosed L] (b : Fin Tag.E8.rank → Lˣ) :
    twN b ∈ familyGroup (K := L) (fun e : Empty => e.elim : Empty → Fin Tag.E8.rank → Lˣ) := by
  have hker : familyKernel (fun e : Empty => e.elim : Empty → Fin Tag.E8.rank → Lˣ) =
      {α | IsRoot Tag.E8 α} :=
    Set.ext fun α => ⟨fun h => h.1, fun h => ⟨h, fun e => e.elim⟩⟩
  show rootDiagUnit Tag.E8 b * canonicalRep (coxeterSystem Tag.E8) L tw8W ∈ _
  refine mul_mem (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup b))
    (Subgroup.mem_sup_right ?_)
  rw [hker, ← adjointGroup_eq_rootSpan]
  exact canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) L tw8W

end Field

theorem exists_twLayer_maps {K Kq L : Type} [Field K] [Field Kq] [Finite Kq] [Field L]
    [IsAlgClosed L] [Algebra Kq L] (p f N : ℕ) [Fact p.Prime] [CharP L p] (hf : 1 ≤ f)
    (hKq : Nat.card Kq = N) (hN : ∀ c : L, iterateFrobenius L p f c = c ^ N)
    (ι : K →+* L) (θ : K →+* K) (hFr : ∀ c, iterateFrobenius L p f (ι c) = ι (θ c))
    (Ψ : ↥(e6Data_valid.minGroup K) →* ↥(adjointGroup Tag.E8 K))
    (hΨker : Ψ.ker ≤ Subgroup.center _)
    (hΨ : ∀ (k : Fin 6) (c : K),
      Ψ (e6Data_valid.xm K (Pi.single k 1) c) = e8Par K (Pi.single (e8E6Node k) 1) c ∧
      Ψ (e6Data_valid.xm K (-Pi.single k 1) c) = e8Par K (-Pi.single (e8E6Node k) 1) c) :
    ∃ (Ψ₀ : ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K θ) →* ↥(adjointGroup Tag.E8 Kq))
      (β₀ : ↥(StatedSU 3 N K) →* ↥(adjointGroup Tag.E8 Kq)),
      Ψ₀.ker ≤ Subgroup.center _ ∧ Function.Injective β₀ ∧
        ∀ x Y, Ψ₀ x * β₀ Y = β₀ Y * Ψ₀ x := by
  classical
  have hFrbij : Function.Bijective (iterateFrobenius L p f) := bijective_iterateFrobenius L p f
  have hFrcard : ∀ c : L, iterateFrobenius L p f c = c ^ Nat.card Kq := fun c => by
    rw [hKq]
    exact hN c
  obtain ⟨b, hb⟩ := exists_twN_equivariant ι θ (iterateFrobenius L p f) hFr Ψ hΨ
  obtain ⟨z, hzM, hz⟩ := lang_familyGroup (τ := Tag.E8) p (fun e : Empty => e.elim) f hf 1
    (one_mem _) (twN b) (twN_mem_familyGroup b)
  rw [one_mul, inv_one, mul_one] at hz
  have hFz : Units.map (entrywiseHom (iterateFrobenius L p f)) z = z * twN b := by
    rw [← hz]
    exact (mul_inv_cancel_left z _).symm
  have hzC : z ∈ adjointGroup Tag.E8 L :=
    (mem_familyCentralizer.1 (familyGroup_le_familyCentralizer _ hzM)).1
  have key : ∀ B : ModGL Tag.E8 L,
      twN b * Units.map (entrywiseHom (iterateFrobenius L p f)) B * (twN b)⁻¹ = B →
        Units.map (entrywiseHom (iterateFrobenius L p f)) (z * B * z⁻¹) = z * B * z⁻¹ :=
    fun B hB => by
      rw [map_mul, map_mul, map_inv, hFz]
      conv_rhs => rw [← hB]
      group
  let H : Subgroup (ModGL Tag.E8 L) :=
    (adjointGroup Tag.E8 Kq).map (baseChangeGL (algebraMap Kq L))
  have hdesc : ∀ B ∈ adjointGroup Tag.E8 L,
      twN b * Units.map (entrywiseHom (iterateFrobenius L p f)) B * (twN b)⁻¹ = B →
        z * B * z⁻¹ ∈ H := fun B hB hfix => by
    obtain ⟨y₀, hy₀, hy₀e⟩ := CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux.descent_E8
      (K := Kq) (iterateFrobenius L p f) hFrcard hFrbij
      (mul_mem (mul_mem hzC hB) (inv_mem hzC)) (key B hfix)
    exact ⟨y₀, hy₀, hy₀e⟩
  let eH : ↥(adjointGroup Tag.E8 Kq) ≃* ↥H :=
    (adjointGroup Tag.E8 Kq).equivMapOfInjective (baseChangeGL (algebraMap Kq L))
      (baseChangeGL_injective (algebraMap Kq L))
  let Φ₁ : ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup K θ) →* ModGL Tag.E8 L :=
    (MulAut.conj z).toMonoidHom.comp ((baseChangeGL ι).comp ((adjointGroup Tag.E8 K).subtype.comp
      (Ψ.comp (CFSG.LieType.Steinberg.TwistedE6.fixedGroup K θ).subtype)))
  have hΦ₁ : ∀ x, Φ₁ x =
      z * baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) * z⁻¹ :=
    fun _ => rfl
  have hΦ₁H : ∀ x, Φ₁ x ∈ H := fun x => by
    rw [hΦ₁]
    refine hdesc _ (bc_mem_adjointGroup ι (Ψ x).2) ?_
    have h1 := hb (x : ↥(e6Data_valid.minGroup K))
    rw [(CFSG.LieType.Steinberg.TwistedE6.mem_fixedGroup θ).1 x.2] at h1
    exact h1.symm
  obtain ⟨β, hβinj, hβR, hβC, hβF⟩ := exists_su3_twisted ι N (iterateFrobenius L p f) hN hFrbij
    (twN b) (fun i j hij => twN_conj_sigmaRoot b i j hij)
  let Φ₂ : ↥(StatedSU 3 N K) →* ModGL Tag.E8 L := (MulAut.conj z).toMonoidHom.comp β
  have hΦ₂ : ∀ Y, Φ₂ Y = z * β Y * z⁻¹ := fun _ => rfl
  have hΦ₂H : ∀ Y, Φ₂ Y ∈ H := fun Y => by
    rw [hΦ₂]
    exact hdesc _ (hβC Y) (hβF Y)
  refine ⟨eH.symm.toMonoidHom.comp (Φ₁.codRestrict H hΦ₁H),
    eH.symm.toMonoidHom.comp (Φ₂.codRestrict H hΦ₂H), ?_, ?_, ?_⟩
  ·
    intro x hx
    have h0 : Φ₁.codRestrict H hΦ₁H x = 1 :=
      eH.symm.injective ((MonoidHom.mem_ker.1 hx).trans (map_one eH.symm).symm)
    have h1 : Φ₁ x = 1 := congrArg Subtype.val h0
    rw [hΦ₁] at h1
    have h2 : baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) =
        baseChangeGL ι 1 := by
      rw [map_one]
      calc baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)
          = z⁻¹ * (z * baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) *
              z⁻¹) * z := by group
        _ = 1 := by rw [h1]; group
    have h3 : Ψ x = 1 := Subtype.ext (baseChangeGL_injective ι h2)
    have hcen := hΨker (MonoidHom.mem_ker.2 h3)
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro y
    exact Subtype.ext (hcen y)
  ·
    intro Y Y' h
    have h1 : Φ₂ Y = Φ₂ Y' := congrArg Subtype.val (eH.symm.injective h)
    rw [hΦ₂, hΦ₂] at h1
    exact hβinj (mul_left_cancel (mul_right_cancel h1))
  ·
    intro x Y
    have hc : Commute (baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K))
        (β Y) :=
      commute_e6_a2 (bc_mem_rootSpan_e6 ι Ψ hΨ x) (hβR Y)
    have h2 : Φ₁ x * Φ₂ Y = Φ₂ Y * Φ₁ x := by
      rw [hΦ₁, hΦ₂]
      calc z * baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) * z⁻¹ *
            (z * β Y * z⁻¹)
          = z * (baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) * β Y) *
              z⁻¹ := by group
        _ = z * (β Y * baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)) *
              z⁻¹ := by rw [hc.eq]
        _ = z * β Y * z⁻¹ *
              (z * baseChangeGL ι ((Ψ x : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K) * z⁻¹) := by
            group
    have h3 : Φ₁.codRestrict H hΦ₁H x * Φ₂.codRestrict H hΦ₂H Y =
        Φ₂.codRestrict H hΦ₂H Y * Φ₁.codRestrict H hΦ₁H x := Subtype.ext h2
    show eH.symm _ * eH.symm _ = eH.symm _ * eH.symm _
    rw [← map_mul, ← map_mul, h3]

theorem layer_of_maps {G M U : Type*} [Group G] [Group M] [Group U] (Ψ₀ : M →* G) (β₀ : U →* G)
    (hker : Ψ₀.ker ≤ Subgroup.center M) (hinj : Function.Injective β₀)
    (hcomm : ∀ x Y, Ψ₀ x * β₀ Y = β₀ Y * Ψ₀ x)
    (hM : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = (⊤ : Subgroup M))
    (hZ : Nat.card (Subgroup.center M) ∣ 3) :
    ∃ (P S : Subgroup G) (Ψ : M →* ↥P), Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center M ∧
      Nonempty (↥S ≃* U) ∧ (∀ l ∈ P, ∀ s ∈ S, l * s = s * l) ∧
        (∀ x ∈ S, x ∈ P → x ^ 3 = 1) := by
  have hker' : Ψ₀.rangeRestrict.ker ≤ Subgroup.center M := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hPS : ∀ l ∈ Ψ₀.range, ∀ s ∈ β₀.range, l * s = s * l := by
    rintro _ ⟨x, rfl⟩ _ ⟨Y, rfl⟩
    exact hcomm x Y
  refine ⟨Ψ₀.range, β₀.range, Ψ₀.rangeRestrict, Ψ₀.rangeRestrict_surjective, hker',
    ⟨(MonoidHom.ofInjective hinj).symm⟩, hPS, fun x hxS hxP => ?_⟩
  have hcenP : Nat.card (Subgroup.center ↥Ψ₀.range) ∣ 3 :=
    (card_center_dvd_of_perfect Ψ₀.rangeRestrict_surjective hker' hM).trans hZ
  have hz : (⟨x, hxP⟩ : ↥Ψ₀.range) ∈ Subgroup.center ↥Ψ₀.range :=
    Subgroup.mem_center_iff.2 fun l => Subtype.ext (hPS l l.2 x hxS)
  have hc3 : (⟨⟨x, hxP⟩, hz⟩ : ↥(Subgroup.center ↥Ψ₀.range)) ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard _).trans hcenP)
  have h := congrArg (fun c : ↥(Subgroup.center ↥Ψ₀.range) => ((c : ↥Ψ₀.range) : G)) hc3
  simpa using h

theorem twE8SCLayer_holds : E8Layer6.TwE8SCLayer := by
  intro q hv
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hq2 : 2 ≤ q.card := by
    rw [hcard]
    exact le_trans q.prime_p.two_le (Nat.le_self_pow (by omega) _)
  have hK : Nat.card (GaloisField q.p (2 * q.exponent)) = q.card ^ 2 := by
    rw [GaloisField.card q.p (2 * q.exponent) (by omega), hcard, ← pow_mul, mul_comm]
  haveI : CharP (AlgebraicClosure (GaloisField q.p (2 * q.exponent))) q.p :=
    charP_of_injective_algebraMap (algebraMap (GaloisField q.p (2 * q.exponent))
      (AlgebraicClosure (GaloisField q.p (2 * q.exponent)))).injective q.p
  obtain ⟨Kq, _, _, _, hKq⟩ := CFSG.RankThree.PartOne.KE.exists_finite_field_into q.p q.exponent
    hf (AlgebraicClosure (GaloisField q.p (2 * q.exponent)))
  have hKq' : Nat.card Kq = q.card := hKq.trans hcard.symm
  let θ : GaloisField q.p (2 * q.exponent) →+* GaloisField q.p (2 * q.exponent) :=
    iterateFrobenius (GaloisField q.p (2 * q.exponent)) q.p q.exponent
  have hθ : ∀ c, θ c = c ^ q.card := fun c => by
    rw [hcard, iterateFrobenius_def]
  have hN : ∀ c : AlgebraicClosure (GaloisField q.p (2 * q.exponent)),
      iterateFrobenius (AlgebraicClosure (GaloisField q.p (2 * q.exponent))) q.p q.exponent c =
        c ^ q.card := fun c => by
    rw [hcard, iterateFrobenius_def]
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure (GaloisField q.p (2 * q.exponent))) q.p
      q.exponent (algebraMap _ _ c) = algebraMap _ _ (θ c) := fun c => by
    rw [hN, hθ, map_pow]
  obtain ⟨Ψ, hΨker, hΨ⟩ := e8E6_pinned q.p (2 * q.exponent) ⟨q.prime_p, by omega, rfl⟩
  obtain ⟨Ψ₀, β₀, hΨ₀ker, hβ₀inj, hcomm⟩ :=
    exists_twLayer_maps (Kq := Kq) q.p q.exponent q.card hf hKq' hN (algebraMap _ _) θ hFr Ψ
      hΨker hΨ
  have hθ2 : ∀ c, θ (θ c) = c := fun c => by
    rw [hθ, hθ]
    exact CFSG.LieType.Simplicity.pow_pow_card_sq hK c
  have hK4 : 4 ≤ Nat.card (GaloisField q.p (2 * q.exponent)) := by
    rw [hK]
    nlinarith [hq2]
  have hMM : ⁅(⊤ : Subgroup ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField q.p (2 * q.exponent)) θ)), ⊤⁆ = ⊤ :=
    Group.isPerfect_def.1
      (CFSG.LieType.Steinberg.TwistedE6.fixedGroup_isQuasisimple_of_four_le_card θ hθ2 hK4).1
  have hZ : Nat.card (Subgroup.center ↥(CFSG.LieType.Steinberg.TwistedE6.fixedGroup
      (GaloisField q.p (2 * q.exponent)) θ)) ∣ 3 := by
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup
      (θ := θ) (q := q.card) hK hθ).1]
    exact Nat.gcd_dvd_left 3 _
  obtain ⟨bE⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e8 q hv Kq hKq'
  let ι8 : adjointGroup .E8 Kq ≃* Cat ⟨.E8 q, hv⟩ :=
    (CFSG.GH74.Filter.Lie.adjointQuotientEquiv .E8 Kq).symm.trans bE
  have hker8 : (ι8.toMonoidHom.comp Ψ₀).ker ≤ Subgroup.center _ := fun x hx =>
    hΨ₀ker (MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ι8).1 (MonoidHom.mem_ker.1 hx)))
  have hcomm8 : ∀ x Y, (ι8.toMonoidHom.comp Ψ₀) x * (ι8.toMonoidHom.comp β₀) Y =
      (ι8.toMonoidHom.comp β₀) Y * (ι8.toMonoidHom.comp Ψ₀) x := fun x Y => by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact (map_mul ι8 _ _).symm.trans ((congrArg ι8 (hcomm x Y)).trans (map_mul ι8 _ _))
  obtain ⟨P, S, ΨP, h1, h2, h3, h4, h5⟩ := layer_of_maps (ι8.toMonoidHom.comp Ψ₀)
    (ι8.toMonoidHom.comp β₀) hker8 (ι8.injective.comp hβ₀inj) hcomm8 hMM hZ
  exact ⟨GaloisField q.p (2 * q.exponent), inferInstance, inferInstance, θ, hK, inferInstance, hθ,
    P, S, ΨP, h1, h2, h3, h4, h5⟩

end CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw
