module

public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftZeta
public import CFSG.CharacterTheory.Wreathed.ReducedNoncentralInvolution
public import CFSG.CharacterTheory.Wreathed.NormalComponentLiftOdd

public section

open scoped Classical

namespace CFSG.Wreathed.NormalComponentLift

open Matrix CFSG.Wreathed.ActualProjectiveLayer CFSG.Wreathed.BaseFourCentralizerStructure
  CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.OddFieldTorus
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.Wreathed.TorusSplitting
  CFSG.Wreathed.CentralSL2Abelianization

theorem actual_normal_component_lift_eliminates_odd_field_factor
    {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (hmodel : PSLTwoClassicalModel (centralizerSimpleLayer n hn S e) p f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJM : J.map (centralizerOddCoreMap n S e) = CFSG.layer (centralizerOddCoreQuotient n S e))
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →* coordinateE F)
    (Ψ : SemilinearExtension F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
      hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ) :
    let m := 2 ^ n
    let q := Nat.card F
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let y : G := wreathModelHom S e (Original.x2 m)
    let w : G := wreathModelHom S e (Original.z m)
    let C₀ := torusCore n S e
    let A₀ := torusFixedCore n S e
    let JG : Subgroup G := J.map (involutionCentralizer n S e).subtype
    Nat.card Sigma = 1 ∧
    ∃ W₀ : Subgroup G, (∀ g, g ∈ W₀ ↔ g ∈ JG ∧ g * y = y * g ∧ Odd (orderOf g)) ∧
      W₀ ≤ C₀ ∧ (∀ k ∈ C₀, ∀ g ∈ W₀, k * g * k⁻¹ ∈ W₀) ∧ IsCyclic W₀ ∧
      W₀ ⊓ A₀ = ⊥ ∧ (∀ g ∈ W₀, ∀ z ∈ A₀, g * z = z * g) ∧
      (∀ g ∈ W₀, w * g * w⁻¹ = g⁻¹) ∧ (∀ z ∈ A₀, w * z = z * w) ∧
      (m : ℤ) * Nat.card W₀ = q - ε ∧
      (∃ WF : Subgroup (SpecialLinearGroup (Fin 2) F),
        ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g)) ∧
      ∀ (WF : Subgroup (SpecialLinearGroup (Fin 2) F))
        (hWF : ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g)),
        ∃ ζ : C₀ ⧸ A₀.subgroupOf C₀ ≃*
            WF ⋊[(oddTorusAction WF hWF).comp Sigma.subtype] Sigma,
          (∀ k : C₀, SemidirectProduct.rightHom (ζ (QuotientGroup.mk k)) =
            fieldCharacter n hn S e F Sigma ρ hdata.rho_range ⟨k, torusCore_le n S e k.2⟩) ∧
          ∀ k : C₀, (k : G) ∈ W₀ ⊔ A₀ ↔ ζ (QuotientGroup.mk k) ∈ (SemidirectProduct.inl :
            WF →* WF ⋊[(oddTorusAction WF hWF).comp Sigma.subtype] Sigma).range := by
  intro m q ε y w C₀ A₀ JG
  have : Fintype F := Fintype.ofFinite F
  have hpodd' : Odd p := hp.odd_of_ne_two hpodd
  have hcard : Nat.card F = p ^ f := hdata.card
  have hm2 := two_pow_eq_two_part hnonab hfour hp hpodd hf hmodel
  have hred :=
    ReducedInvolution.reduced_noncentral_involution_centralizer_has_exact_odd_torus_field_complement
    hp hpodd' hf hcard _ rfl (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) hm2 Sigma
    hdata.sigma_odd b hSigma hdata.nonsquare
  dsimp only at hred
  obtain ⟨-, hx₀, -, -, -, -, hMD, -, -, hconj, hWex, hWall⟩ := hred
  set yN := nModel n hn S e (Original.x2 (2 ^ n)) with hyN
  have hY2 : orderOf (Ψ.symm (centralizerOddCoreMap n S e yN)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_centralizerOddCoreMap_y n hn S e
  have hYnc : Ψ.symm (centralizerOddCoreMap n S e yN) ∉ Subgroup.center _ := by
    intro hc
    apply centralizerOddCoreMap_y_not_mem_center n hn S e
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro z
    apply Ψ.symm.injective
    rw [map_mul, map_mul, hc]
  obtain ⟨h, hh⟩ := hconj _ hY2 hYnc
  set y₀ := (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ^ 2) ^
    (2 ^ n / 4) * specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
      (weyl F) with hy₀
  have hy : liftMap n hn S e Ψ h yN = modelInl F b n hn Sigma hSigma y₀ := by
    rw [liftMap_apply]
    exact hh
  have hJmem : ∀ j ∈ J, liftMap n hn S e Ψ h j ∈ modelLayer F b n hn Sigma hSigma := by
    intro j hj
    apply (liftMap_mem_modelLayer_iff hnonab hfour hp hpodd hf hmodel hdata j).mpr
    rw [← hJM]
    exact Subgroup.mem_map_of_mem _ hj
  have hJsurj : ∀ g ∈ modelLayer F b n hn Sigma hSigma, ∃ j ∈ J, liftMap n hn S e Ψ h j = g :=
    fun g hg => exists_liftMap_eq hnonab hfour hp hpodd hf hmodel hdata J hJM hg
  have hMD' : (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)).range ⊓
      Subgroup.centralizer {y₀} = (OddFieldTorus.torus F).map
        (specialInclusion F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)) := hMD
  obtain ⟨WF₀, hWF₀⟩ := hWex
  have hWF₀' : ∀ g, g ∈ WF₀ ↔ g ∈ OddFieldTorus.torus F ∧ Odd (orderOf g) := hWF₀
  set W₀ := oddTorus n hn S e Ψ h J WF₀ with hW₀
  have hW₀mem := mem_oddTorus_iff hn hJR hJmem y₀ hy hMD' WF₀ hWF₀'
  have hW₀T := oddTorus_le_centralizer_four hn hJR hJmem y₀ hy hMD' WF₀ hWF₀'
  obtain ⟨-, -, hφall₀⟩ := hWall WF₀ hWF₀
  obtain ⟨⟨Ψ'₀, hΨ'₀⟩, -, hK₀, -⟩ := hφall₀ ((oddTorusAction WF₀ hWF₀').comp Sigma.subtype)
    (fun σ w => rfl)
  have hK₀' : ambientOddCore (Subgroup.centralizer {liftMap n hn S e Ψ h yN}) =
      WF₀.map ((SemidirectProduct.inl).comp (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn))) ⊔ (SemidirectProduct.inr : Sigma →* SemilinearExtension F b
          (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma).range := by
    rw [hy]
    exact hK₀
  have hkerω : ∀ k : C₀, (k : G) ∈ W₀ ⊔ A₀ ↔
      fieldCharacter n hn S e F Sigma ρ hdata.rho_range ⟨k, torusCore_le n S e k.2⟩ = 1 := by
    intro k
    have hle : W₀ ⊔ A₀ ≤ (fieldCharacter n hn S e F Sigma ρ hdata.rho_range).ker.map
        (involutionCentralizer n S e).subtype := by
      apply sup_le
      · intro g hg
        obtain ⟨⟨j, hjJ⟩, ⟨X, -, hXj⟩, rfl⟩ := hg
        refine ⟨j, MonoidHom.mem_ker.mpr ?_, rfl⟩
        rw [← liftMap_right (hn := hn) (h := h) hdata]
        change (liftMap n hn S e Ψ h j).right = 1
        rw [← show modelSpecial F b n hn Sigma hSigma X = liftMap n hn S e Ψ h j from hXj]
        rfl
      · rintro g ⟨⟨r, hr, rfl⟩, -⟩
        refine ⟨r, MonoidHom.mem_ker.mpr ?_, rfl⟩
        rw [← liftMap_right (hn := hn) (h := h) hdata,
          (liftMap_eq_one_iff (hn := hn) (Ψ := Ψ) (h := h) r).mpr hr]
        rfl
    constructor
    · intro hk
      obtain ⟨k', hk', hkk'⟩ := hle hk
      have hk'' : k' = ⟨k, torusCore_le n S e k.2⟩ := Subtype.ext hkk'
      rw [← hk'']
      exact hk'
    · intro hω
      have hmem : liftMap n hn S e Ψ h ⟨k, torusCore_le n S e k.2⟩ ∈
          WF₀.map ((SemidirectProduct.inl).comp (specialInclusion F b (2 ^ n)
            (wreathModulus_pos n) (wreathModulus_even hn))) ⊔
            (SemidirectProduct.inr : Sigma →* SemilinearExtension F b (2 ^ n)
              (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma).range := by
        rw [← hK₀', ← map_torusCore_eq hn]
        exact ⟨⟨k, torusCore_le n S e k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
      set x := Ψ'₀.symm ⟨_, hmem⟩ with hx
      have h1 : liftMap n hn S e Ψ h ⟨k, torusCore_le n S e k.2⟩ =
          SemidirectProduct.inl (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
            (wreathModulus_even hn) (x.left : SpecialLinearGroup (Fin 2) F)) *
            SemidirectProduct.inr x.right := by
        have h0 := hΨ'₀ x
        rw [hx, MulEquiv.apply_symm_apply] at h0
        exact h0
      have hxr : x.right = 1 := by
        have h2 := congrArg SemidirectProduct.rightHom h1
        rw [map_mul, SemidirectProduct.rightHom_inl, one_mul,
          SemidirectProduct.rightHom_inr] at h2
        rw [hx, ← h2, SemidirectProduct.rightHom_eq_right, liftMap_right (hn := hn) hdata]
        exact hω
      rw [hxr, map_one, mul_one] at h1
      obtain ⟨j, hjJ, hjk⟩ := hJsurj _ ⟨(x.left : SpecialLinearGroup (Fin 2) F), rfl⟩
      have hjW : (j : G) ∈ W₀ := ⟨⟨j, hjJ⟩, ⟨x.left, x.left.2, hjk.symm⟩, rfl⟩
      have hr : (⟨k, torusCore_le n S e k.2⟩ : involutionCentralizer n S e) * j⁻¹ ∈
          centralizerOddCore n S e := by
        rw [← liftMap_eq_one_iff (hn := hn) (Ψ := Ψ) (h := h), map_mul, map_inv, h1, hjk]
        exact mul_inv_cancel _
      have hrA : (k : G) * (j : G)⁻¹ ∈ A₀ :=
        ⟨⟨_, hr, rfl⟩, Subgroup.mul_mem _ (ambientOddCore_le _ k.2)
          (Subgroup.inv_mem _ (hW₀T hjW))⟩
      have hkj : (k : G) = ((k : G) * (j : G)⁻¹) * j := by group
      rw [hkj]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrA) (Subgroup.mem_sup_left hjW)
  have hζall : ∀ (WF : Subgroup (SpecialLinearGroup (Fin 2) F))
      (hWF : ∀ g, g ∈ WF ↔ g ∈ torus F ∧ Odd (orderOf g)),
      ∃ ζ : C₀ ⧸ A₀.subgroupOf C₀ ≃* WF ⋊[(oddTorusAction WF hWF).comp Sigma.subtype] Sigma,
        (∀ k : C₀, SemidirectProduct.rightHom (ζ (QuotientGroup.mk k)) =
          fieldCharacter n hn S e F Sigma ρ hdata.rho_range ⟨k, torusCore_le n S e k.2⟩) ∧
        ∀ k : C₀, (k : G) ∈ W₀ ⊔ A₀ ↔ ζ (QuotientGroup.mk k) ∈ (SemidirectProduct.inl :
          WF →* WF ⋊[(oddTorusAction WF hWF).comp Sigma.subtype] Sigma).range := by
    intro WF hWF
    obtain ⟨-, -, hφall⟩ := hWall WF hWF
    obtain ⟨⟨Ψ', hΨ'⟩, -, hK, -⟩ := hφall ((oddTorusAction WF hWF).comp Sigma.subtype)
      (fun σ w => rfl)
    have hK' : ambientOddCore (Subgroup.centralizer {liftMap n hn S e Ψ h yN}) =
        WF.map ((SemidirectProduct.inl).comp (specialInclusion F b (2 ^ n) (wreathModulus_pos n)
          (wreathModulus_even hn))) ⊔ (SemidirectProduct.inr : Sigma →* SemilinearExtension F b
            (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma hSigma).range := by
      rw [hy]
      exact hK
    obtain ⟨ζ₁, hζ₁⟩ := exists_quotient_equiv hn _ hK'
    have hright : ∀ k : C₀, SemidirectProduct.rightHom (Ψ'.symm (ζ₁ (QuotientGroup.mk k))) =
        fieldCharacter n hn S e F Sigma ρ hdata.rho_range ⟨k, torusCore_le n S e k.2⟩ := by
      intro k
      have h1 := hΨ' (Ψ'.symm (ζ₁ (QuotientGroup.mk k)))
      rw [MulEquiv.apply_symm_apply, hζ₁] at h1
      have h2 := congrArg SemidirectProduct.rightHom h1
      rw [map_mul, SemidirectProduct.rightHom_inl, one_mul, SemidirectProduct.rightHom_inr] at h2
      rw [SemidirectProduct.rightHom_eq_right, ← h2, SemidirectProduct.rightHom_eq_right,
        liftMap_right (hn := hn) hdata]
    refine ⟨ζ₁.trans Ψ'.symm, hright, fun k => ?_⟩
    rw [hkerω, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
      MulEquiv.trans_apply, hright]
  have hd := d_mem hnonab n hn S e hfour J hJM hJR
  have hx := liftMap_x (h := h) hnonab hfour hp hpodd hf hmodel hdata
  set a' := (cyclicGenerator F b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) ^ 2) ^
    (2 ^ n / 4) with ha'def
  have ha' : ∀ v, a' * v = v * a' := fun v =>
    (Commute.pow_left (CentralSL2.cyclicGenerator_sq_comm F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) v) _).eq
  have hinv : ∀ g ∈ W₀, w * g * w⁻¹ = g⁻¹ := fun g hg =>
    swap_inv_oddTorus hn hJR hJmem y₀ hy hMD' WF₀ hWF₀' hd hx a' ha' rfl hg
  have hW₀C₀ : W₀ ≤ C₀ := oddTorus_le_torusCore hn hJR hJmem y₀ hy hMD' WF₀ hWF₀'
  have hW₀n : ∀ k ∈ C₀, ∀ g ∈ W₀, k * g * k⁻¹ ∈ W₀ := fun k hk g hg =>
    oddTorus_normalized hn hJR hJmem y₀ hy hMD' WF₀ hWF₀' k (ambientOddCore_le _ hk) g hg
  obtain ⟨eW⟩ := exists_oddTorus_equiv hn hJR hJsurj WF₀
  obtain ⟨-, -, -, -, hWall2⟩ := OddFieldTorus.odd_field_fixed_torus_derived_centralizer hp hpodd
    hf hcard _ rfl (2 ^ n) hm2 Sigma hdata.sigma_odd
  obtain ⟨hWFcyc, hWFcard, -⟩ := hWall2 WF₀ hWF₀'
  have hW₀cyc : IsCyclic W₀ := isCyclic_of_surjective eW.symm.toMonoidHom eW.symm.surjective
  have hW₀A : W₀ ⊓ A₀ = ⊥ := oddTorus_inf_torusFixedCore hn (Ψ := Ψ) (h := h) (WF := WF₀) hJR
  have hW₀Ac : ∀ g ∈ W₀, ∀ z ∈ A₀, g * z = z * g :=
    oddTorus_comm_torusFixedCore hn (Ψ := Ψ) (h := h) (WF := WF₀) hJR
  have hwA : ∀ z ∈ A₀, w * z = z * w := swap_comm_torusFixedCore hnonab n hn S e hfour J hJM hJR
  have hW₀card : (m : ℤ) * Nat.card W₀ = q - ε := by
    rw [Nat.card_congr eW.toEquiv, hWFcard]
    have hq : (q : ℤ) = ((p ^ f : ℕ) : ℤ) := by rw [show q = p ^ f from hcard]
    have hε' : ε = if p ^ f % 4 = 1 then 1 else -1 := by
      change (if q % 4 = 1 then (1 : ℤ) else -1) = _
      rw [show q = p ^ f from hcard]
    rw [hq, hε']
    have hdvd : ((2 ^ n : ℕ) : ℤ) ∣ ((p ^ f : ℕ) : ℤ) - (if p ^ f % 4 = 1 then 1 else -1) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h1 := padicValInt_dvd (p := 2) (((p ^ f : ℕ) : ℤ) - (if p ^ f % 4 = 1 then 1 else -1))
      have h2 : ((2 ^ n : ℕ) : ℤ) = ((2 : ℕ) : ℤ) ^
          padicValInt 2 (((p ^ f : ℕ) : ℤ) - (if p ^ f % 4 = 1 then 1 else -1)) := by
        rw [hm2]
        push_cast
        rfl
      rw [h2]
      exact h1
    exact Int.mul_ediv_cancel' hdvd
  obtain ⟨ζ₀, hζ₀ω, hζ₀W⟩ := hζall WF₀ hWF₀'
  have hsplit := compatible_actual_torus_splitting_eliminates_odd_field_factor hnonab n hn S e hfour
    p f hp hpodd hf hmodel F Sigma ρ hcard hdata.sigma_odd hdata.rho_injective hdata.rho_layer
    hdata.rho_range WF₀ hWF₀' W₀ hW₀C₀ hW₀n hW₀cyc hW₀A hW₀Ac hinv hwA ζ₀ hζ₀ω hζ₀W
  exact ⟨hsplit.1, W₀, hW₀mem, hW₀C₀, hW₀n, hW₀cyc, hW₀A, hW₀Ac, hinv, hwA, hW₀card,
    ⟨WF₀, hWF₀'⟩, hζall⟩

end CFSG.Wreathed.NormalComponentLift
