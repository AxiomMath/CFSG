module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrthAdj

public section

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.ModelFacts

section SL2

variable {K : Type} [Field K]

@[expose] def sl2OffNegFun (A : SL(2, K)) : SL(2, K) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) K) 0 0, -(A : Matrix (Fin 2) (Fin 2) K) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1], by
    have h := A.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linear_combination h⟩

theorem coe_sl2OffNegFun (A : SL(2, K)) :
    ((sl2OffNegFun A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![(A : Matrix (Fin 2) (Fin 2) K) 0 0, -(A : Matrix (Fin 2) (Fin 2) K) 0 1;
        -(A : Matrix (Fin 2) (Fin 2) K) 1 0, (A : Matrix (Fin 2) (Fin 2) K) 1 1] := rfl

theorem sl2OffNegFun_one : sl2OffNegFun (1 : SL(2, K)) = 1 := by
  refine Subtype.ext ?_
  rw [coe_sl2OffNegFun]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2OffNegFun_mul (A B : SL(2, K)) :
    sl2OffNegFun (A * B) = sl2OffNegFun A * sl2OffNegFun B := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_sl2OffNegFun, coe_sl2OffNegFun, coe_sl2OffNegFun,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[expose] def sl2OffNeg : SL(2, K) →* SL(2, K) where
  toFun := sl2OffNegFun
  map_one' := sl2OffNegFun_one
  map_mul' := sl2OffNegFun_mul

theorem sl2OffNeg_uSL (c : K) : sl2OffNeg (uSL c) = uSL (-c) := by
  refine Subtype.ext ?_
  change ((sl2OffNegFun (uSL c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_sl2OffNegFun]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem sl2OffNeg_vSL (c : K) : sl2OffNeg (vSL c) = vSL (-c) := by
  refine Subtype.ext ?_
  change ((sl2OffNegFun (vSL c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = _
  rw [coe_sl2OffNegFun]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_vSL]

end SL2

section Odd

variable {τ : Tag} {K : Type} [Field K]

theorem rootTorusSL2_conj_rootSL2_of_odd {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (hodd : ¬ Even (2 * iform β γ / iform β β)) (A : SL(2, K)) :
    rootTorusSL2 τ K β (-1) * rootSL2 τ K γ A * (rootTorusSL2 τ K β (-1))⁻¹ =
      rootSL2 τ K γ (sl2OffNeg A) := by
  have hm : (-1 : Kˣ) ^ (2 * iform β γ / iform β β) = -1 :=
    (Int.not_even_iff_odd.1 hodd).neg_one_zpow
  have hm' : (-1 : Kˣ) ^ (2 * iform β (-γ) / iform β β) = -1 := by
    have hdvd := iform_dvd_of_isRoot hβ γ
    rw [iform_neg_right, mul_neg, Int.neg_ediv_of_dvd hdvd, zpow_neg, hm]
    simp
  obtain ⟨ε, hε, hεv⟩ := exists_rootSL2_vSL_eq (K := K) hγ
  have key := MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := K))
    (f := (MulAut.conj (rootTorusSL2 τ K β (-1))).toMonoidHom.comp (rootSL2 τ K γ))
    (g := (rootSL2 τ K γ).comp sl2OffNeg) (by
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change rootTorusSL2 τ K β (-1) * rootSL2 τ K γ (uSL c) *
          (rootTorusSL2 τ K β (-1))⁻¹ = rootSL2 τ K γ (sl2OffNeg (uSL c))
        rw [sl2OffNeg_uSL, rootSL2_uSL_eq, rootSL2_uSL_eq,
          rootTorusSL2_conj_pinnedX_of_isRoot hβ hγ, hm]
        congr 1
        simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, smul_neg]
      · change rootTorusSL2 τ K β (-1) * rootSL2 τ K γ (vSL c) *
          (rootTorusSL2 τ K β (-1))⁻¹ = rootSL2 τ K γ (sl2OffNeg (vSL c))
        rw [sl2OffNeg_vSL, hεv, hεv, rootTorusSL2_conj_pinnedX_of_isRoot hβ (IsRoot.neg hγ), hm']
        congr 1
        simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, mul_neg])
  have := DFunLike.congr_fun key A
  simpa using this

theorem even_two_mul_iform_div_of_commute_of_nonabelian (hK : ringChar K ≠ 2)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ) {N : Subgroup (ModGL τ K)}
    (hN : N ≤ rootRankOneGroup τ K γ) (hnc : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x)
    (h : ∀ y ∈ N, rootTorusSL2 τ K β (-1) * y = y * rootTorusSL2 τ K β (-1)) :
    Even (2 * iform β γ / iform β β) := by
  by_contra hodd
  have hinj := ((exceptional_Lang_root_rank_one_data τ K γ).2.2.2.2.2.2.2.1 hK).1
  have hdiag : ∀ y ∈ N, ∃ A : SL(2, K), rootSL2 τ K γ A = y ∧
      (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    intro y hy
    obtain ⟨A, hA⟩ := hN hy
    refine ⟨A, hA, ?_⟩
    have h1 := h y hy
    rw [← hA] at h1
    have h2 := rootTorusSL2_conj_rootSL2_of_odd hβ hγ hodd A
    rw [mul_inv_eq_iff_eq_mul.2 h1] at h2
    have h3 : sl2OffNeg A = A := hinj h2.symm
    have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK
    have e01 : -(A : Matrix (Fin 2) (Fin 2) K) 0 1 = (A : Matrix (Fin 2) (Fin 2) K) 0 1 :=
      congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 0 1) h3
    have e10 : -(A : Matrix (Fin 2) (Fin 2) K) 1 0 = (A : Matrix (Fin 2) (Fin 2) K) 1 0 :=
      congrArg (fun M : SL(2, K) => (M : Matrix (Fin 2) (Fin 2) K) 1 0) h3
    refine ⟨?_, ?_⟩
    · have : (2 : K) * (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by linear_combination -e01
      exact (mul_eq_zero.1 this).resolve_left h2K
    · have : (2 : K) * (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by linear_combination -e10
      exact (mul_eq_zero.1 this).resolve_left h2K
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  obtain ⟨A, rfl, hA1, hA2⟩ := hdiag x hx
  obtain ⟨B, rfl, hB1, hB2⟩ := hdiag y hy
  refine hxy ?_
  rw [← map_mul, ← map_mul]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [hA1, hA2, hB1, hB2, mul_comm]

end Odd

section Image

variable {τ : Tag} {p f : ℕ} [Fact p.Prime] {K : Type*} [Group K]

theorem map_conj_range_eq {G : Type*} [Group G] (ψ : K →* G) {u : G} (hu : u ∈ ψ.range) :
    ψ.range.map (MulAut.conj u).toMonoidHom = ψ.range := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hu hy) (inv_mem hu)
  · intro hx
    exact ⟨u⁻¹ * x * u, mul_mem (mul_mem (inv_mem hu) hx) hu, by simp [mul_assoc]⟩

theorem exists_rootRankOneGroup_map_conj_eq_hull (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (ψ : K →* ModGL τ (GaloisField p f)) (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p f))
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ) {Rθ : Subgroup K}
    (hhull : Rθ.map ψ ≤ rootRankOneGroup τ (GaloisField p f) θ)
    (hsat : rootRankOneGroup τ (GaloisField p f) θ ⊓ ψ.range ≤ Rθ.map ψ)
    (hinj : ∀ x ∈ Rθ, ψ x = 1 → x = 1)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p f)ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p f) γ → IsLongRoot τ γ)
    {h c : K} (hc : h⁻¹ * c * h ∈ Rθ) (hsq : c * c = 1) (hne : c ≠ 1)
    {b : Fin τ.rank → (GaloisField p f)ˣ} (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hψc : ψ c = rootDiagUnit τ b) :
    ∃ γ : Fin τ.rank → ℤ, IsLongRoot τ γ ∧
      (Generic.conjSub h Rθ).map ψ = rootRankOneGroup τ (GaloisField p f) γ ⊓ ψ.range ∧
      ψ c = rootTorusSL2 τ (GaloisField p f) γ (-1) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  set c' := h⁻¹ * c * h with hc'
  have hmem : ψ c' ∈ rootRankOneGroup τ (GaloisField p f) θ :=
    hhull (Subgroup.mem_map_of_mem ψ hc)
  have hsq' : ψ c' * ψ c' = 1 := by
    rw [← map_mul, hc']
    calc ψ (h⁻¹ * c * h * (h⁻¹ * c * h)) = ψ (h⁻¹ * (c * c) * h) := by congr 1; group
      _ = 1 := by rw [hsq]; simp
  have hne' : ψ c' ≠ 1 := fun h1 => hne (by
    have := hinj c' hc h1
    have h2 : c = h * c' * h⁻¹ := by rw [hc']; group
    rw [h2, this]
    group)
  have hd := eq_rootTorusSL2_neg_one_of_mul_self_eq_one hK hodd hmem hsq' hne'
  have hcc : ψ c = ψ h * ψ c' * (ψ h)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hc']
    congr 1
    group
  have hz : ψ h * rootTorusSL2 τ (GaloisField p f) θ (-1) * (ψ h)⁻¹ = rootDiagUnit τ b := by
    rw [← hd, ← hcc, hψc]
  obtain ⟨γ, hγ, h1, h2, h3⟩ :=
    exists_rootRankOneGroup_of_conj_toral hp2 hq hθ (hψ h) hb hz
  refine ⟨γ, hlong b γ hγ h2, ?_, ?_⟩
  · have hRθ : Rθ.map ψ = rootRankOneGroup τ (GaloisField p f) θ ⊓ ψ.range :=
      le_antisymm (le_inf hhull (Subgroup.map_le_range ψ Rθ)) hsat
    have hconj : (Generic.conjSub h Rθ).map ψ = (Rθ.map ψ).map (MulAut.conj (ψ h)).toMonoidHom := by
      unfold Generic.conjSub
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp
    rw [hconj, hRθ, Subgroup.map_inf _ _ _ (MulAut.conj (ψ h)).injective, h1,
      map_conj_range_eq ψ ⟨h, rfl⟩]
  · rw [hcc, hd]
    exact h3

end Image

section Assembly

variable {p e f : ℕ} [Fact p.Prime]

theorem orthBranch_of_hullEmbedding {t : StatedLieTag} {τ : Tag} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hqf : 5 ≤ p ^ f) (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hne2 : ¬ (t = .PSL ∧ (0 : ℕ) = 2)) (hadm : StatedLieAdmissible t 0 p e)
    (ψ : (Generic.modelUniv t 0 p e Fact.out).K →* ModGL τ (GaloisField p f))
    (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p f))
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K)
    (𝒯 : Subgroup (Generic.modelUniv t 0 p e Fact.out).K)
    (hT : ∀ c ∈ 𝒯, ∃ b : Fin τ.rank → (GaloisField p f)ˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ ψ c = rootDiagUnit τ b)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (hsingle : FundamentalSingleClass t (Generic.modelUniv t 0 p e Fact.out).D)
    {Rθ : Subgroup (Generic.modelUniv t 0 p e Fact.out).K}
    (hRθ𝓡 : Rθ ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hhull : Rθ.map ψ ≤ rootRankOneGroup τ (GaloisField p f) θ)
    (hsat : rootRankOneGroup τ (GaloisField p f) θ ⊓ ψ.range ≤ Rθ.map ψ)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p f)ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p f) γ → IsLongRoot τ γ) :
    OrthBranch p t 0 e := by
  intro _ _ R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₂₁ h₁₂
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hsq : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c * c = 1 :=
    fun {c} h => by
      rw [← pow_two]
      exact h ▸ pow_orderOf_eq_one c
  have hne : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c ≠ 1 :=
    fun {c} h h1 => by
      rw [h1, orderOf_one] at h
      omega
  have hcentral : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D,
      ∀ x ∈ R, x ∈ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K → x = 1 :=
    fun R hR x hx hxc =>
      fundNoncentral_generic p t 0 e hfund hadm hne2 R hR x hx fun y => by
        rw [Subgroup.mem_center_iff] at hxc
        have h2 : x * y * x⁻¹ * y⁻¹ = 1 := by
          calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxc y]
            _ = 1 := by group
        rw [h2]
        exact Subgroup.one_mem _
  have hinj : ∀ R ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D,
      ∀ x ∈ R, ψ x = 1 → x = 1 := fun R hR x hx h1 => hcentral R hR x hx (hker h1)
  refine orthBranch_of_frame ψ hker (𝓡 := longestFundamental _) (𝒯 := 𝒯)
    (fun R₁' h₁' R₂' h₂' => hframe R₁' (longestFundamental_subset t _ h₁') R₂'
      (longestFundamental_subset t _ h₂'))
    (fun R hR g => conjSub_mem_longestFundamental hR g)
    (fun R hR => commutator_eq_of_mem_longestFundamental hp2 hq hfund hadm hR)
    (fun R hR c hc hcc r hr => ?_)
    (ι := {γ : Fin τ.rank → ℤ // IsLongRoot τ γ ∧
      ∃ x ∈ rootRankOneGroup τ (GaloisField p f) γ ⊓ ψ.range,
        ∃ y ∈ rootRankOneGroup τ (GaloisField p f) γ ⊓ ψ.range, x * y ≠ y * x})
    (fun i => rootRankOneGroup τ (GaloisField p f) i.1 ⊓ ψ.range)
    (fun i => rootTorusSL2 τ (GaloisField p f) i.1 (-1))
    (fun R hR c hc hcc hc1 hc𝒯 => ?_)
    (fun i j h _ => ?_)
    h₁ h₂ hc₁ hc₂ (hsq ho₁) (hne ho₁) (hsq ho₂) (hne ho₂) h₂₁ h₁₂
  · by_cases h1 : c = 1
    · rw [h1]
      simp
    · exact mul_comm_of_orderOf_eq_two_of_mem_longestFundamental hp2 hq hfund hadm hG2 hD4 hR hc
        (orderOf_eq_prime (by rwa [pow_two]) h1) r hr
  · obtain ⟨g, hg⟩ := hsingle Rθ hRθ𝓡 R (longestFundamental_subset t _ hR)
    have hperf := commutator_eq_of_mem_longestFundamental hp2 hq hfund hadm hR
    have hRf := longestFundamental_subset t _ hR
    obtain ⟨b, hb, hψc⟩ := hT c hc𝒯
    subst hg
    have hcg : g⁻¹ * c * g ∈ Rθ := Generic.mem_conjSub_iff.1 hc
    obtain ⟨γ, hγ, h1, h2⟩ := exists_rootRankOneGroup_map_conj_eq_hull hp2 hqf ψ hψ hθ hhull hsat
      (hinj Rθ hRθ𝓡) hlong hcg hcc hc1 hb hψc
    refine ⟨⟨γ, hγ, ?_⟩, h1, h2⟩
    by_contra hcomm
    push Not at hcomm
    rw [← h1] at hcomm
    have hle : ⁅Generic.conjSub g Rθ, Generic.conjSub g Rθ⁆ ≤
        Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K := by
      refine Subgroup.commutator_le.2 fun r hr s hs => ?_
      refine hker ?_
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have := hcomm (ψ r) (Subgroup.mem_map_of_mem ψ hr) (ψ s) (Subgroup.mem_map_of_mem ψ hs)
      rw [this]
      group
    exact hc1 (hcentral _ hRf c hc (hle (hperf ▸ hc)))
  · have hev := even_two_mul_iform_div_of_commute_of_nonabelian hK i.2.1.1 j.2.1.1
      (N := rootRankOneGroup τ (GaloisField p f) j.1 ⊓ ψ.range) inf_le_left j.2.2 h
    rcases i.2.1.eq_or_eq_neg_or_iform_eq_zero j.2.1.1 hev with h1 | h1 | h0
    · left
      simp only [h1]
    · left
      simp only [h1]
      rw [rootRankOneGroup_eq_sup i.2.1.1, rootRankOneGroup_eq_sup (IsRoot.neg i.2.1.1), neg_neg,
        sup_comm]
    · right
      exact fun x hx y hy => i.2.1.commute_rootRankOneGroup j.2.1.1 h0 x hx.1 y hy.1

end Assembly

end CFSG.ClassicalInvolution.ModelFacts
