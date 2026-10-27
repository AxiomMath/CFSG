module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsTransport
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizers
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeSettingValid
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsBasic
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftMap
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolution

public section

namespace CFSG.Wreathed.OriginalAllPrime.TIFacts

open CFSG.ABGTheoremB CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

variable {G : Type} [Group G]

theorem modelLayer_eq {F : Type} [Field F] (b : Fˣ) (n : ℕ) (hn : 2 ≤ n)
    (Sigma : Subgroup (F ≃+* F)) (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) :
    NormalComponentLift.modelLayer F b n hn Sigma hSigma =
      ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma :=
  MonoidHom.range_comp _ _

theorem isCyclic_modelLayer_inf_modelC {F : Type} [Field F] [Fintype F] {p f : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hcard : Nat.card F = p ^ f) {m : ℕ}
    (hm : 0 < m) (heven : Even m)
    (hm2 : m = 2 ^ padicValInt 2 ((p ^ f : ℕ) - (if p ^ f % 4 = 1 then (1 : ℤ) else -1)))
    {Sigma : Subgroup (F ≃+* F)} (hd : Odd (Nat.card Sigma)) {b : Fˣ}
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b) (hb : ¬ IsSquare b) :
    IsCyclic (ModelSignalizers.modelLayer b m hm heven Sigma hSigma ⊓
      ModelSignalizers.modelC b m hm heven Sigma hSigma : Subgroup _) := by
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hcard _ rfl m hm heven hm2 Sigma hd b hSigma hb
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, hMD, hcyc, -⟩ := hred
  have key : ModelSignalizers.modelLayer b m hm heven Sigma hSigma ⊓
      ModelSignalizers.modelC b m hm heven Sigma hSigma =
      ((specialInclusion F b m hm heven).range ⊓ Subgroup.centralizer
        {(cyclicGenerator F b m hm heven ^ 2) ^ (m / 4) *
          specialInclusion F b m hm heven (CentralSL2Abelianization.weyl F)}).map
        SemidirectProduct.inl := by
    have hinj : Function.Injective (SemidirectProduct.inl : CentralExtension F b m hm heven →*
        SemilinearExtension F b m hm heven Sigma hSigma) := SemidirectProduct.inl_injective
    rw [ModelSignalizers.modelC, ModelSignalizers.modelY, ModelSignalizers.modelLayer]
    apply le_antisymm
    · intro w hw
      obtain ⟨⟨v, hv, rfl⟩, hc⟩ := Subgroup.mem_inf.mp hw
      refine ⟨v, Subgroup.mem_inf.mpr ⟨hv, ?_⟩, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      apply hinj
      rw [map_mul _ v, map_mul _ _ v]
      exact hc
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨⟨v, hv1, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hv2 ⊢
      rw [← map_mul, ← map_mul, hv2]
  rw [key, hMD]
  exact isCyclic_of_surjective ((SemidirectProduct.inl : CentralExtension F b m hm heven →*
    SemilinearExtension F b m hm heven Sigma hSigma).subgroupMap _)
    (MonoidHom.subgroupMap_surjective _ _)

theorem modelBase_le_map_L [Finite G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {p f : ℕ} {F : Type} [Field F] {Sigma : Subgroup (F ≃+* F)}
    {b : Fˣ} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {φ : (wreathedSetting n S e p f).N →*
      SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma}
    {y : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma}
    (hφ : IsModelMap (wreathedSetting n S e p f) φ
      (ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma) y) :
    ModelSignalizers.modelBase b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma ≤
      ((wreathedSetting n S e p f).L.subgroupOf (wreathedSetting n S e p f).N).map φ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := CentralSL2Abelianization.psi F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
    Sigma hSigma with hψdef
  have hψsurj : Function.Surjective ψ :=
    CentralSL2Abelianization.psi_surjective F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma
  have hψker : ψ.ker = ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma := by
    rw [hψdef, CentralSL2Abelianization.psi_ker]
    exact MonoidHom.range_comp _ _
  have hSN : (S : Subgroup G) ≤ (wreathedSetting n S e p f).N :=
    sylow_le_involutionCentralizer n hn S e
  let P : Sylow 2 (Multiplicative (ZMod (2 ^ n)) × Sigma) :=
    (S.subtype hSN).mapSurjective (f := ψ.comp φ) (hψsurj.comp hφ.surjective)
  have hPcoe : (P : Subgroup (Multiplicative (ZMod (2 ^ n)) × Sigma)) =
      (((S : Subgroup G).subgroupOf (wreathedSetting n S e p f).N).map φ).map ψ := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, Subgroup.map_map]
  have hBnormal : (ModelSignalizers.modelBase b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma).Normal := by
    rw [ModelSignalizers.modelBase, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have : ((ModelSignalizers.modelBase b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      Sigma hSigma).map ψ).Normal := hBnormal.map ψ hψsurj
  have hpow : ∀ a : Multiplicative (ZMod (2 ^ n)), a ^ 2 ^ n = 1 := by
    intro a
    have hc : Nat.card (Multiplicative (ZMod (2 ^ n))) = 2 ^ n := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have h1 := pow_card_eq_one' (x := a)
    rwa [hc] at h1
  have hBp : IsPGroup 2 ((ModelSignalizers.modelBase b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma).map ψ) := by
    rintro ⟨_, ⟨_, ⟨v, rfl⟩, rfl⟩⟩
    refine ⟨n, Subtype.ext ?_⟩
    change (ψ (SemidirectProduct.inl v)) ^ 2 ^ n = 1
    apply Prod.ext
    · rw [Prod.pow_fst, Prod.fst_one]
      exact hpow _
    · rw [Prod.pow_snd, Prod.snd_one]
      change ((SemidirectProduct.inl v : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma).right) ^ 2 ^ n = 1
      rw [SemidirectProduct.right_inl, one_pow]
  have hle := IsPGroup.le_sylow_of_normal hBp P
  rw [hPcoe, Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, hψker] at hle
  refine hle.trans ?_
  rw [← hφ.map_L₀, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hSN hφ.L₀_le]
  exact Subgroup.map_mono (subgroupOf_mono_of_le (sup_le le_sup_right le_sup_left) _)

theorem exists_swap_conj [Finite G] {n : ℕ} (hn : 2 ≤ n) {S : Sylow 2 G}
    {e : S ≃* Wreath (2 ^ n)} {p f : ℕ} {H : Type} [Group H]
    {φ : (wreathedSetting n S e p f).N →* H} {M : Subgroup H} {y x : H}
    (hφ : IsModelMap (wreathedSetting n S e p f) φ M y)
    (hx : ∀ hxN : (wreathedSetting n S e p f).x ∈ (wreathedSetting n S e p f).N,
      φ ⟨_, hxN⟩ = x) :
    ∃ z ∈ (wreathedSetting n S e p f).D, ∃ hzN : z ∈ (wreathedSetting n S e p f).N,
      φ ⟨z, hzN⟩ * y * (φ ⟨z, hzN⟩)⁻¹ = x * y := by
  have hzS : wreathModelHom S e (Original.x2 (2 ^ n)) * wreathModelHom S e (Original.z (2 ^ n)) ∈
      (S : Subgroup G) := (S : Subgroup G).mul_mem (e.symm _).property (e.symm _).property
  have hSN := sylow_le_involutionCentralizer n hn S e
  refine ⟨_, ?_, hSN hzS, ?_⟩
  · rw [wreathedSetting_D_eq n (by omega) S e p f]
    exact hzS
  · have hxN : (wreathedSetting n S e p f).x ∈ (wreathedSetting n S e p f).N :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have key : (⟨_, hSN hzS⟩ : (wreathedSetting n S e p f).N) * ⟨_, hφ.x₂_mem⟩ *
        (⟨_, hSN hzS⟩ : (wreathedSetting n S e p f).N)⁻¹ = ⟨_, hxN⟩ * ⟨_, hφ.x₂_mem⟩ :=
      Subtype.ext (NormalComponentLift.d_conj_x2 n hn S e)
    have h1 := congrArg φ key
    rw [map_mul, map_mul, map_inv, map_mul, hφ.map_x₂, hx hxN] at h1
    exact h1

section Wreathed

variable [Finite G] [IsSimpleGroup G]

theorem exists_liftMap_eq_modelY
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    {F : Type} [Field F] [Finite F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
    {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    ∃ h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn),
      NormalComponentLift.liftMap n hn S e Ψ h
          (NormalComponentLift.nModel n hn S e (Original.x2 (2 ^ n))) =
        ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
          hSigma := by
  have : Fintype F := Fintype.ofFinite F
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have hm2 := NormalComponentLift.two_pow_eq_two_part hnonab hfour hp hp2 hf hlocal
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd hf hdata.card _ rfl (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) hm2 Sigma
    hdata.sigma_odd b hSigma hdata.nonsquare
  dsimp only at hred
  obtain ⟨-, -, -, -, -, -, -, -, -, hconj, -⟩ := hred
  have hY2 : orderOf (Ψ.symm (centralizerOddCoreMap n S e
      (NormalComponentLift.nModel n hn S e (Original.x2 (2 ^ n))))) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact NormalComponentLift.orderOf_centralizerOddCoreMap_y n hn S e
  have hYnc : Ψ.symm (centralizerOddCoreMap n S e
      (NormalComponentLift.nModel n hn S e (Original.x2 (2 ^ n)))) ∉ Subgroup.center _ := by
    intro hc
    apply NormalComponentLift.centralizerOddCoreMap_y_not_mem_center n hn S e
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro z
    apply Ψ.symm.injective
    rw [map_mul, map_mul, hc]
  obtain ⟨h, hh⟩ := hconj _ hY2 hYnc
  exact ⟨h, by rw [NormalComponentLift.liftMap_apply]; exact hh⟩

theorem liftMap_isModelMap
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    {F : Type} [Field F] [Finite F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
    {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    {h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)}
    (hh : NormalComponentLift.liftMap n hn S e Ψ h
        (NormalComponentLift.nModel n hn S e (Original.x2 (2 ^ n))) =
      ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma) :
    IsModelMap (wreathedSetting n S e p f) (NormalComponentLift.liftMap n hn S e Ψ h)
      (ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma)
      (ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma) := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  refine
    { surjective := ?_
      ker_eq := ?_
      x₂_mem := (NormalComponentLift.nModel n hn S e (Original.x2 (2 ^ n))).property
      x₂_mul_self := ?_
      map_x₂ := hh
      L₀_le := Subgroup.map_subtype_le _
      ON_le := wreathedSetting_ON_le_L₀ n S e p f
      map_L₀ := ?_ }
  · intro z
    obtain ⟨k, hk⟩ := centralizerOddCoreMap_surjective n S e
      (Ψ (SemidirectProduct.inl h * z * (SemidirectProduct.inl h)⁻¹))
    refine ⟨k, ?_⟩
    change NormalComponentLift.liftMap n hn S e Ψ h k = z
    rw [NormalComponentLift.liftMap_apply, hk, MulEquiv.symm_apply_apply]
    group
  · ext k
    exact (NormalComponentLift.liftMap_eq_one_iff k).trans
      (Subgroup.mem_map_iff_mem (involutionCentralizer n S e).subtype_injective).symm
  · have h2 := pow_orderOf_eq_one (wreathModelHom S e (Original.x2 (2 ^ n)))
    rw [CompatibleFamilies.orderOf_x2 S e hn, sq] at h2
    exact h2
  · have hL : (wreathedSetting n S e p f).L₀.subgroupOf (wreathedSetting n S e p f).N =
        (CFSG.layer (centralizerOddCoreQuotient n S e)).comap (centralizerOddCoreMap n S e) :=
      Subgroup.comap_map_eq_self_of_injective (involutionCentralizer n S e).subtype_injective _
    rw [hL, ← modelLayer_eq]
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (NormalComponentLift.liftMap_mem_modelLayer_iff hnonab hfour hp hp2 hf hlocal hdata
        k).mpr hk
    · intro hz
      obtain ⟨j, hj, rfl⟩ := NormalComponentLift.exists_liftMap_eq (h := h) hnonab hfour hp hp2
        hf hlocal hdata _ (Subgroup.map_comap_eq_self_of_surjective
          (centralizerOddCoreMap_surjective n S e) _) hz
      exact ⟨j, hj, rfl⟩

theorem liftMap_x_eq
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f)
    {F : Type} [Field F] [Finite F] {Sigma : Subgroup (F ≃+* F)} {b : Fˣ}
    {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}
    {ρ : centralizerFullQuotient n hn S e →* coordinateE F}
    {Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e}
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (h : CentralExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn))
    (hxN : (wreathedSetting n S e p f).x ∈ (wreathedSetting n S e p f).N) :
    NormalComponentLift.liftMap n hn S e Ψ h ⟨_, hxN⟩ =
      ModelSignalizers.modelX b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
        hSigma := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  have h1 := NormalComponentLift.liftMap_x (h := h) hnonab hfour hp hp2 hf hlocal hdata
  rw [ModelSignalizers.modelX, CentralSL2.cyclicGenerator_pow_m]
  exact h1

end Wreathed

end CFSG.Wreathed.OriginalAllPrime.TIFacts
