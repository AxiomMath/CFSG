module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftCentralizer
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftMap

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.CyclicCentralSL2Extension
  CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
  {e : S ≃* Wreath (2 ^ n)} {F : Type} [Field F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
  {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
  {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
    hSigma ≃* centralizerOddCoreQuotient n S e}
  {h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)}

omit [Finite G] in
theorem liftMap_eq_comp :
    liftMap n hn S e Ψ h = (Ψ.symm.trans (MulAut.conj
      (modelInl F b n hn Sigma hSigma h)⁻¹)).toMonoidHom.comp (centralizerOddCoreMap n S e) :=
  MonoidHom.ext fun _ => rfl

theorem map_centralizer_y :
    (Subgroup.centralizer {nModel n hn S e (Original.x2 (2 ^ n))}).map (liftMap n hn S e Ψ h) =
      Subgroup.centralizer {liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n)))} := by
  have hπ : (Subgroup.centralizer {nModel n hn S e (Original.x2 (2 ^ n))}).map
      (centralizerOddCoreMap n S e) =
      Subgroup.centralizer {centralizerOddCoreMap n S e (nModel n hn S e (Original.x2 (2 ^ n)))} :=
    OddNormalQuotientInvolutions.centralizer_map (centralizerOddCore n S e)
      (centralizerOddCore_card_odd n S e) (nModel n hn S e (Original.x2 (2 ^ n))) (by
        rw [orderOf_injective _ (wreathModelHom_injective _ _),
          ← orderOf_injective _ (wreathModelHom_injective S e)]
        exact CompatibleFamilies.orderOf_x2 S e hn)
  set θ := Ψ.symm.trans (MulAut.conj (modelInl F b n hn Sigma hSigma h)⁻¹) with hθ
  have hΦ : ∀ k, liftMap n hn S e Ψ h k = θ (centralizerOddCoreMap n S e k) := fun k => rfl
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' := Subgroup.mem_centralizer_singleton_iff.mp hk
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul, hk']
  · intro hz
    have hz' : θ.symm z ∈ Subgroup.centralizer
        {centralizerOddCoreMap n S e (nModel n hn S e (Original.x2 (2 ^ n)))} := by
      have hz1 := Subgroup.mem_centralizer_singleton_iff.mp hz
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      apply θ.injective
      rw [map_mul, map_mul, θ.apply_symm_apply, ← hΦ, hz1]
    rw [← hπ] at hz'
    obtain ⟨k, hk, hkz⟩ := hz'
    refine ⟨k, hk, ?_⟩
    change θ (centralizerOddCoreMap n S e k) = z
    rw [hkz, θ.apply_symm_apply]

theorem odd_card_of_odd_ker_range {P X : Type*} [Group P] [Group X] [Finite P] (φ : P →* X)
    (hker : Odd (Nat.card φ.ker)) (hrange : Odd (Nat.card φ.range)) : Odd (Nat.card P) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  exact hrange.mul hker

omit [Finite G] in
theorem mem_centralizer_four_iff' (k : involutionCentralizer n S e) :
    (k : G) ∈ Subgroup.centralizer (Subgroup.closure
      {wreathModelHom S e (Original.s (2 ^ n)) ^ (2 ^ n / 2),
        wreathModelHom S e (Original.t (2 ^ n)) ^ (2 ^ n / 2)} : Set G) ↔
      k ∈ Subgroup.centralizer {nModel n hn S e (Original.x2 (2 ^ n))} := by
  rw [mem_centralizer_four_iff hn S e k, Subgroup.mem_centralizer_singleton_iff]

theorem map_torusCore_eq [Finite F] :
    ((torusCore n S e).subgroupOf (involutionCentralizer n S e)).map (liftMap n hn S e Ψ h) =
      ambientOddCore (Subgroup.centralizer
        {liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n)))}) := by
  set Φ := liftMap n hn S e Ψ h with hΦ
  set yN := nModel n hn S e (Original.x2 (2 ^ n)) with hyN
  set C := Subgroup.centralizer {Φ yN} with hC
  have hCmap : (Subgroup.centralizer {yN}).map Φ = C := map_centralizer_y hn
  have hT : ∀ k : involutionCentralizer n S e, (k : G) ∈ torusCore n S e →
      k ∈ Subgroup.centralizer {yN} := fun k hk =>
    (mem_centralizer_four_iff' hn k).mp (ambientOddCore_le _ hk)
  apply le_antisymm
  · apply le_ambientOddCore
    · rintro _ ⟨k, hk, rfl⟩
      rw [← hCmap]
      exact ⟨k, hT k hk, rfl⟩
    · intro c hc z hz
      rw [← hCmap] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      obtain ⟨k, hk, rfl⟩ := hz
      refine ⟨c' * k * c'⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      apply Subgroup.mem_subgroupOf.mpr
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact ambientOddCore_conj_mem_of_mem ((mem_centralizer_four_iff' hn c').mpr hc')
        (Subgroup.mem_subgroupOf.mp hk)
    · apply Odd.of_dvd_nat _ (Subgroup.card_map_dvd _ _)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusCore_le n S e)).toEquiv]
      exact ambientOddCore_odd _
  · set P : Subgroup (involutionCentralizer n S e) :=
      (ambientOddCore C).comap Φ ⊓ Subgroup.centralizer {yN} with hP
    have hPG : P.map (involutionCentralizer n S e).subtype ≤ torusCore n S e := by
      apply le_ambientOddCore
      · rintro _ ⟨p, hp, rfl⟩
        exact (mem_centralizer_four_iff' hn p).mpr hp.2
      · intro c hc z hz
        obtain ⟨p, hp, rfl⟩ := hz
        have hcN := centralizer_four_le n S e hc
        have hcC := (mem_centralizer_four_iff' hn ⟨c, hcN⟩).mp hc
        refine ⟨⟨c, hcN⟩ * p * (⟨c, hcN⟩ : involutionCentralizer n S e)⁻¹, ⟨?_, ?_⟩, rfl⟩
        · show _ ∈ (ambientOddCore C).comap Φ
          rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
          have hΦc : Φ ⟨c, hcN⟩ ∈ C := by
            rw [← hCmap]
            exact ⟨_, hcC, rfl⟩
          exact ambientOddCore_conj_mem_of_mem hΦc hp.1
        · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hp.2) (Subgroup.inv_mem _ hcC)
      · have hcard : Nat.card (P.map (involutionCentralizer n S e).subtype) = Nat.card P :=
          Nat.card_congr (P.equivMapOfInjective _
            (involutionCentralizer n S e).subtype_injective).toEquiv.symm
        rw [hcard]
        apply odd_card_of_odd_ker_range (Φ.comp P.subtype)
        · have hle : (Φ.comp P.subtype).ker.map P.subtype ≤ centralizerOddCore n S e := by
            rintro _ ⟨k, hk, rfl⟩
            exact (liftMap_eq_one_iff (hn := hn) (Ψ := Ψ) (h := h)
              (k : involutionCentralizer n S e)).mp (MonoidHom.mem_ker.mp hk)
          have hcard' : Nat.card ((Φ.comp P.subtype).ker.map P.subtype) =
              Nat.card (Φ.comp P.subtype).ker :=
            Nat.card_congr ((Φ.comp P.subtype).ker.equivMapOfInjective _
              P.subtype_injective).toEquiv.symm
          rw [← hcard']
          exact (centralizerOddCore_card_odd n S e).of_dvd_nat (Subgroup.card_dvd_of_le hle)
        · have hle : (Φ.comp P.subtype).range ≤ ambientOddCore C := by
            rintro _ ⟨p, rfl⟩
            exact p.2.1
          exact (ambientOddCore_odd C).of_dvd_nat (Subgroup.card_dvd_of_le hle)
    intro z hz
    have hzC : z ∈ C := ambientOddCore_le _ hz
    rw [← hCmap] at hzC
    obtain ⟨c, hc, rfl⟩ := hzC
    exact ⟨c, Subgroup.mem_subgroupOf.mpr (hPG ⟨c, ⟨hz, hc⟩, rfl⟩), rfl⟩

omit [Finite G] in
theorem liftMap_torusCore_eq_one_iff (k : involutionCentralizer n S e)
    (hk : (k : G) ∈ torusCore n S e) :
    liftMap n hn S e Ψ h k = 1 ↔ (k : G) ∈ torusFixedCore n S e := by
  rw [liftMap_eq_one_iff (hn := hn)]
  constructor
  · intro hkR
    exact ⟨⟨k, hkR, rfl⟩, ambientOddCore_le _ hk⟩
  · rintro ⟨⟨r, hr, hrk⟩, -⟩
    rwa [← Subtype.ext hrk]

theorem exists_quotient_equiv [Finite F]
    (K : Subgroup (SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      Sigma hSigma))
    (hK : ambientOddCore (Subgroup.centralizer
      {liftMap n hn S e Ψ h (nModel n hn S e (Original.x2 (2 ^ n)))}) = K) :
    ∃ ζ₁ : torusCore n S e ⧸ (torusFixedCore n S e).subgroupOf (torusCore n S e) ≃* K,
      ∀ k : torusCore n S e, (ζ₁ (QuotientGroup.mk k) : SemilinearExtension F b (2 ^ n)
        (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma) =
          liftMap n hn S e Ψ h ⟨k, torusCore_le n S e k.2⟩ := by
  let χ := (liftMap n hn S e Ψ h).comp (Subgroup.inclusion (torusCore_le n S e))
  have hmap := map_torusCore_eq hn (Ψ := Ψ) (h := h)
  have hrange : χ.range = K := by
    rw [← hK, ← hmap]
    ext z
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, torusCore_le n S e k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hker : χ.ker = (torusFixedCore n S e).subgroupOf (torusCore n S e) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 := liftMap_torusCore_eq_one_iff hn (Ψ := Ψ) (h := h)
      (Subgroup.inclusion (torusCore_le n S e) k) k.2
    exact h1
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange χ).trans (MulEquiv.subgroupCongr hrange)), ?_⟩
  intro k
  have key : ((QuotientGroup.quotientKerEquivRange χ (QuotientGroup.mk k) : χ.range) :
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma) = χ k := rfl
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    MulEquiv.subgroupCongr_apply, key]
  rfl

end CFSG.Wreathed.NormalComponentLift
