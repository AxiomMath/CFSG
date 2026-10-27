module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcOrth

public section

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

namespace CFSG.ClassicalInvolution.ModelFacts

variable {τ : Tag}

@[expose] def IsLongRoot (τ : Tag) (θ : Fin τ.rank → ℤ) : Prop :=
  IsRoot τ θ ∧ ∀ δ, IsRoot τ δ → iform δ δ ≤ iform θ θ

theorem iform_sub_smul_self (σ θ : Fin τ.rank → ℤ) (k : ℤ) :
    iform (σ - k • θ) (σ - k • θ) = iform σ σ - 2 * k * iform θ σ + k ^ 2 * iform θ θ := by
  simp only [iform_sub_left, iform_sub_right, iform_smul_left, iform_smul_right]
  rw [iform_comm σ θ]
  ring

theorem IsLongRoot.eq_or_eq_neg_or_iform_eq_zero {θ σ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hσ : IsRoot τ σ) (hev : Even (2 * iform θ σ / iform θ θ)) :
    σ = θ ∨ σ = -θ ∨ iform θ σ = 0 := by
  obtain ⟨hθr, hmax⟩ := hθ
  have hN : 0 < iform θ θ := iform_self_pos_of_isRoot hθr
  have hMN : iform σ σ ≤ iform θ θ := hmax σ hσ
  obtain ⟨m, hm⟩ := iform_dvd_of_isRoot hθr σ
  have hdiv : 2 * iform θ σ / iform θ θ = m := by
    rw [hm]
    exact Int.mul_ediv_cancel_left _ hN.ne'
  rw [hdiv] at hev
  obtain ⟨k, hk⟩ := hev
  have hs : iform θ σ = iform θ θ * k := by
    have : 2 * iform θ σ = 2 * (iform θ θ * k) := by rw [hm, hk]; ring
    linarith
  have hpos : 0 ≤ iform (σ - k • θ) (σ - k • θ) := by
    by_cases hx : σ - k • θ = 0
    · rw [hx]
      simp [iform]
    · exact (iform_self_pos hx).le
  rw [iform_sub_smul_self, hs] at hpos
  have hk2 : k ^ 2 ≤ 1 := by
    by_contra h
    have h : 1 < k ^ 2 := not_le.1 h
    nlinarith
  have hk1 : k = 0 ∨ k = 1 ∨ k = -1 := by
    have : k ≤ 1 := by nlinarith
    have : -1 ≤ k := by nlinarith
    omega
  rcases hk1 with rfl | rfl | rfl
  · right; right; rw [hs]; ring
  · left
    have h0 : iform (σ - (1 : ℤ) • θ) (σ - (1 : ℤ) • θ) = 0 := by
      rw [iform_sub_smul_self, hs]
      nlinarith
    by_contra hne
    have := iform_self_pos (x := σ - (1 : ℤ) • θ) (fun h => hne (by simpa [sub_eq_zero] using h))
    omega
  · right; left
    have h0 : iform (σ - (-1 : ℤ) • θ) (σ - (-1 : ℤ) • θ) = 0 := by
      rw [iform_sub_smul_self, hs]
      nlinarith
    by_contra hne
    have := iform_self_pos (x := σ - (-1 : ℤ) • θ) (fun h => hne (by
      have h' : σ = (-1 : ℤ) • θ := sub_eq_zero.1 h
      simpa using h'))
    omega

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem HSL_neg_one_mul_self : (HSL (-1 : Kˣ)) * HSL (-1) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [HSL, Matrix.mul_apply, Fin.sum_univ_two]

theorem rootTorusSL2_neg_one_mul_self (β : Fin τ.rank → ℤ) :
    rootTorusSL2 τ K β (-1) * rootTorusSL2 τ K β (-1) = 1 := by
  rw [rootTorusSL2, ← map_mul, HSL_neg_one_mul_self, map_one]

theorem rootTorusSL2_neg_one_ne_one (hK : ringChar K ≠ 2) (β : Fin τ.rank → ℤ) :
    rootTorusSL2 τ K β (-1) ≠ 1 := by
  intro h
  have hinj := ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.2.1 hK).1
  have h1 : HSL (-1 : Kˣ) = 1 := hinj (by rw [map_one]; exact h)
  have h00 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h1
  simp [HSL] at h00
  exact Ring.neg_one_ne_one_of_char_ne_two hK h00

theorem exists_signTuple_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ a : Fin τ.rank → Kˣ, (∀ i, a i = 1 ∨ a i = -1) ∧
      rootTorusSL2 τ K β (-1) = rootDiagUnit τ a ∧ rootChar a β = 1 := by
  obtain ⟨a, ha, hχ⟩ := exists_rootTorusSL2_eq_rootDiagUnit (K := K) hβ (-1)
  refine ⟨a, fun i => ?_, ha, by rw [hχ]; simp⟩
  have h2 : rootDiagUnit τ (a * a) = rootDiagUnit τ 1 := by
    rw [rootDiagUnit_mul, rootDiagUnit_one, ← ha, rootTorusSL2_neg_one_mul_self]
  have h3 : a i * a i = 1 := congrFun (rootDiagUnit_injective h2) i
  have h4 : ((a i : Kˣ) : K) * (a i : K) = 1 := by
    have := congrArg Units.val h3
    rwa [Units.val_mul, Units.val_one] at this
  rcases mul_self_eq_one_iff.1 h4 with h | h
  · exact Or.inl (Units.ext h)
  · exact Or.inr (Units.ext (by simpa using h))

theorem rootChar_signTuple_eq {β σ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hσ : IsRoot τ σ)
    {a : Fin τ.rank → Kˣ} (ha : rootTorusSL2 τ K β (-1) = rootDiagUnit τ a) :
    rootChar a σ = (-1 : Kˣ) ^ (2 * iform β σ / iform β β) := by
  have h1 := rootTorusSL2_conj_pinnedX_of_isRoot hβ hσ (-1 : Kˣ) (1 : K)
  rw [ha, rootDiagUnit_conj_pinnedX a hσ] at h1
  have h2 := pinnedX_injective τ K σ h1
  exact Units.ext (by simpa using h2)

theorem even_of_zpow_neg_one_eq_one_of_ringChar (hK : ringChar K ≠ 2) {n : ℤ}
    (h : (-1 : Kˣ) ^ n = 1) : Even n := by
  rcases Int.even_or_odd n with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_zpow] at h
    exact Ring.neg_one_ne_one_of_char_ne_two hK (by simpa using congrArg Units.val h)

theorem even_two_mul_iform_div_of_commute (hK : ringChar K ≠ 2) {β σ : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hσ : IsRoot τ σ)
    (hc : ∀ z : K, rootTorusSL2 τ K β (-1) * pinnedX τ K σ z =
      pinnedX τ K σ z * rootTorusSL2 τ K β (-1)) :
    Even (2 * iform β σ / iform β β) := by
  have h1 := rootTorusSL2_conj_pinnedX_of_isRoot hβ hσ (-1 : Kˣ) (1 : K)
  have h2 : rootTorusSL2 τ K β (-1) * pinnedX τ K σ 1 * (rootTorusSL2 τ K β (-1))⁻¹ =
      pinnedX τ K σ 1 := by
    rw [hc 1]
    group
  rw [h2] at h1
  have h3 := pinnedX_injective τ K σ h1
  exact even_of_zpow_neg_one_eq_one_of_ringChar hK (Units.ext (by simpa using h3.symm))

end Torus


section Subnormal

variable {τ : Tag} {K : Type} [Field K]

theorem IsLongRoot.not_isRoot_add_of_iform_eq_zero {θ σ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hσ : IsRoot τ σ) (h0 : iform θ σ = 0) : ¬ IsRoot τ (θ + σ) ∧ ¬ IsRoot τ (θ - σ) := by
  have hM := iform_self_pos_of_isRoot hσ
  constructor
  · intro h
    have := hθ.2 _ h
    simp only [iform_add_left, iform_add_right] at this
    rw [iform_comm σ θ, h0] at this
    omega
  · intro h
    have := hθ.2 _ h
    simp only [iform_sub_left, iform_sub_right] at this
    rw [iform_comm σ θ, h0] at this
    omega

theorem IsLongRoot.commute_rootRankOneGroup {θ σ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hσ : IsRoot τ σ) (h0 : iform θ σ = 0) :
    ∀ g ∈ rootRankOneGroup τ K θ, ∀ h ∈ rootRankOneGroup τ K σ, g * h = h * g :=
  exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hθ.1 hσ h0
    (hθ.not_isRoot_add_of_iform_eq_zero hσ h0).1 (hθ.not_isRoot_add_of_iform_eq_zero hσ h0).2

theorem rootChar_neg_eq (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  have := rootChar_sub a 0 v
  rwa [zero_sub, rootChar_zero, one_mul] at this

theorem isSubnormal_rootRankOneGroup_toralCentralizer [Finite K] (hK : ringChar K ≠ 2)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hd : rootTorusSL2 τ K θ (-1) = rootDiagUnit τ a) :
    CFSG.Open.IsSubnormal (rootRankOneGroup τ K θ) (toralCentralizer τ K a) := by
  obtain ⟨hSX, hSXn, -, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction τ K hK a ha
  have hN : iform θ θ ≠ 0 := (iform_self_pos_of_isRoot hθ.1).ne'
  have hχθ : rootChar a θ = 1 := by
    rw [rootChar_signTuple_eq hθ.1 hθ.1 hd, Int.mul_ediv_cancel _ hN]
    norm_num
  have hθK : θ ∈ rootCharKernel a := ⟨hθ.1, hχθ⟩
  have hnθK : -θ ∈ rootCharKernel a :=
    ⟨IsRoot.neg hθ.1, by rw [rootChar_neg_eq, hχθ, inv_one]⟩
  have hL : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β →
      rootRankOneGroup τ K β = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) := fun hβ =>
    (exceptional_Lang_root_rank_one_torus_transport τ K hβ).1
  have hLS : rootRankOneGroup τ K θ ≤ rootSpan τ K (rootCharKernel a) := by
    rw [hL hθ.1]
    exact sup_le (rootSubgroup_le_rootSpan hθK) (rootSubgroup_le_rootSpan hnθK)
  have hSN : rootSpan τ K (rootCharKernel a) ≤
      Subgroup.normalizer (rootRankOneGroup τ K θ : Set (ModGL τ K)) := by
    refine iSup₂_le fun σ hσ => ?_
    have hev : Even (2 * iform θ σ / iform θ θ) :=
      even_of_zpow_neg_one_eq_one_of_ringChar hK (by
        rw [← rootChar_signTuple_eq hθ.1 hσ.1 hd]
        exact hσ.2)
    rcases hθ.eq_or_eq_neg_or_iform_eq_zero hσ.1 hev with rfl | rfl | h0
    · exact fun x hx => Subgroup.le_normalizer ((le_sup_left.trans_eq (hL hθ.1).symm) hx)
    · exact fun x hx => Subgroup.le_normalizer ((le_sup_right.trans_eq (hL hθ.1).symm) hx)
    · intro x hx
      have hx' : x ∈ rootRankOneGroup τ K σ := by
        rw [hL hσ.1]
        exact Subgroup.mem_sup_left hx
      have hc : ∀ g ∈ rootRankOneGroup τ K θ, ∀ h ∈ rootRankOneGroup τ K σ, g * h = h * g :=
        hθ.commute_rootRankOneGroup hσ.1 h0
      have hxy : ∀ y ∈ rootRankOneGroup τ K θ, x * y * x⁻¹ = y := fun y hy => by
        rw [mul_inv_eq_iff_eq_mul]
        exact (hc y hy x hx').symm
      have hxy' : ∀ w ∈ rootRankOneGroup τ K θ, x⁻¹ * w * x = w := fun w hw => by
        have h1 := hc w hw x⁻¹ (inv_mem hx')
        calc x⁻¹ * w * x = (w * x⁻¹) * x := by rw [h1]
          _ = w := by group
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hxy y hy]
        exact hy
      · intro hy
        have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
        rw [← h2, hxy' _ hy]
        exact hy
  have hLn : ((rootRankOneGroup τ K θ).subgroupOf (rootSpan τ K (rootCharKernel a))).Normal :=
    (Subgroup.normal_subgroupOf_iff hLS).2 fun h g hh hg =>
      (Subgroup.mem_normalizer_iff.1 (hSN hg) h).1 hh
  exact CFSG.Open.IsSubnormal.step hLS hLn
    (CFSG.Open.IsSubnormal.step hSX hSXn (CFSG.Open.IsSubnormal.refl _))

end Subnormal

section Classical

variable {τ : Tag} {p f : ℕ} [Fact p.Prime]

@[expose] noncomputable def rootRankOneAd (τ : Tag) (K : Type) [Field K]
    (β : Fin τ.rank → ℤ) : Subgroup ↥(adjointGroup τ K) :=
  (rootRankOneGroup τ K β).subgroupOf (adjointGroup τ K)

@[expose] noncomputable def rootTorusAd (τ : Tag) (K : Type) [Field K] (β : Fin τ.rank → ℤ)
    (c : Kˣ) : ↥(adjointGroup τ K) :=
  ⟨rootTorusSL2 τ K β c, ((exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.1 c).1⟩

theorem isClassicalMember_rootRankOneAd (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {θ : Fin τ.rank → ℤ}
    (hθ : IsLongRoot τ θ) :
    IsClassicalMember p f (rootRankOneAd τ (GaloisField p f) θ)
      (rootTorusAd τ (GaloisField p f) θ (-1)) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  obtain ⟨a, ha, hd, -⟩ := exists_signTuple_of_isRoot (K := GaloisField p f) hθ.1
  have hle : rootRankOneGroup τ (GaloisField p f) θ ≤ adjointGroup τ (GaloisField p f) :=
    (exceptional_Lang_root_rank_one_data τ (GaloisField p f) θ).2.2.2.2.2.1
  obtain ⟨-, e, -⟩ := (exceptional_Lang_root_rank_one_data τ (GaloisField p f) θ).2.2.2.2.2.2.2.1 hK
  let eL : rootRankOneAd τ (GaloisField p f) θ ≃* SL(2, GaloisField p f) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans e.symm
  have hO : classicalInvolutionOddCore (rootRankOneAd τ (GaloisField p f) θ) = ⊥ :=
    normal_odd_of_equiv_sl2 hodd (by omega) eL _ inferInstance
      (CFSG.ComponentClassification.OddCore.odd_card _)
  refine ⟨?_, ?_, isPerfect_of_equiv_sl2 (by omega) eL, ?_,
    ⟨((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).trans eL⟩⟩
  · refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      simp only [rootTorusAd, pow_two, Subgroup.coe_mul, Subgroup.coe_one]
      exact rootTorusSL2_neg_one_mul_self θ
    · exact fun h => rootTorusSL2_neg_one_ne_one hK θ (congrArg Subtype.val h)
  · exact Subgroup.mem_subgroupOf.2 ⟨HSL (-1), rfl⟩
  · have hCz := centralizer_eq_subgroupOf_toralCentralizer (τ := τ) a
      (rootTorusAd τ (GaloisField p f) θ (-1)) hd
    rw [hCz]
    exact isSubnormal_comap (adjointGroup τ (GaloisField p f)).subtype
      (isSubnormal_rootRankOneGroup_toralCentralizer hK hθ ha hd)

theorem rootRankOneGroup_eq_sup {K : Type} [Field K] {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootRankOneGroup τ K β = rootSubgroup τ K β ⊔ rootSubgroup τ K (-β) :=
  (exceptional_Lang_root_rank_one_torus_transport τ K hβ).1


theorem eq_rootTorusSL2_neg_one_of_mul_self_eq_one {K : Type} [Field K] [Finite K]
    (hK : ringChar K ≠ 2) (hodd : Odd (Nat.card K)) {β : Fin τ.rank → ℤ} {z : ModGL τ K}
    (hz : z ∈ rootRankOneGroup τ K β) (h2 : z * z = 1) (h1 : z ≠ 1) :
    z = rootTorusSL2 τ K β (-1) := by
  obtain ⟨-, e, -⟩ := (exceptional_Lang_root_rank_one_data τ K β).2.2.2.2.2.2.2.1 hK
  have hdmem : rootTorusSL2 τ K β (-1) ∈ rootRankOneGroup τ K β := ⟨HSL (-1), rfl⟩
  have ho1 : orderOf (⟨z, hz⟩ : ↥(rootRankOneGroup τ K β)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rwa [pow_two]) h1
  have ho2 : orderOf (⟨_, hdmem⟩ : ↥(rootRankOneGroup τ K β)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [pow_two]; exact rootTorusSL2_neg_one_mul_self β)
      (rootTorusSL2_neg_one_ne_one hK β)
  have h3 := (orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm _).1 ho1
  have h4 := (orderOf_eq_two_iff_of_equiv_sl2 hodd e.symm _).1 ho2
  exact congrArg Subtype.val (h3.trans h4.symm)

theorem exists_rootRankOneGroup_of_conj_toral (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ) {u : ModGL τ (GaloisField p f)}
    (hu : u ∈ adjointGroup τ (GaloisField p f)) {b : Fin τ.rank → (GaloisField p f)ˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hz : u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹ = rootDiagUnit τ b) :
    ∃ (γ : Fin τ.rank → ℤ) (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      (rootRankOneGroup τ (GaloisField p f) θ).map (MulAut.conj u).toMonoidHom =
          rootRankOneGroup τ (GaloisField p f) γ ∧
      componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
          rootRankOneGroup τ (GaloisField p f) γ ∧
      u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹ =
          rootTorusSL2 τ (GaloisField p f) γ (-1) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  have hle : rootRankOneGroup τ (GaloisField p f) θ ≤ adjointGroup τ (GaloisField p f) :=
    (exceptional_Lang_root_rank_one_data τ (GaloisField p f) θ).2.2.2.2.2.1
  have hA := isClassicalMember_rootRankOneAd (τ := τ) hp2 hq hθ
  have hc := hA.conj ⟨u, hu⟩
  obtain ⟨γ, hγ, h1, h2⟩ := exists_eq_rankOne_of_isClassicalMember_toral hp2 hq b hb
    (z := ⟨u, hu⟩ * rootTorusAd τ (GaloisField p f) θ (-1) * ⟨u, hu⟩⁻¹) hz hc
  have hmap : (Generic.conjSub (⟨u, hu⟩ : ↥(adjointGroup τ (GaloisField p f)))
      (rootRankOneAd τ (GaloisField p f) θ)).map (adjointGroup τ (GaloisField p f)).subtype =
        (rootRankOneGroup τ (GaloisField p f) θ).map (MulAut.conj u).toMonoidHom := by
    unfold Generic.conjSub
    rw [Subgroup.map_map]
    have : (adjointGroup τ (GaloisField p f)).subtype.comp
        (MulAut.conj (⟨u, hu⟩ : ↥(adjointGroup τ (GaloisField p f)))).toMonoidHom =
        (MulAut.conj u).toMonoidHom.comp (adjointGroup τ (GaloisField p f)).subtype := by
      ext x
      rfl
    rw [this, ← Subgroup.map_map, rootRankOneAd, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.2 hle]
  have hLγ : componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
      rootRankOneGroup τ (GaloisField p f) γ := h2.trans (rootRankOneGroup_eq_sup hγ.1).symm
  have himg : (rootRankOneGroup τ (GaloisField p f) θ).map (MulAut.conj u).toMonoidHom =
      rootRankOneGroup τ (GaloisField p f) γ := hmap.symm.trans (h1.trans hLγ)
  refine ⟨γ, hγ, himg, hLγ, ?_⟩
  have hzmem : u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹ ∈
      rootRankOneGroup τ (GaloisField p f) γ := by
    rw [← himg]
    exact ⟨_, ⟨HSL (-1), rfl⟩, rfl⟩
  have hsq : (u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹) *
      (u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹) = 1 := by
    calc _ = u * (rootTorusSL2 τ (GaloisField p f) θ (-1) *
          rootTorusSL2 τ (GaloisField p f) θ (-1)) * u⁻¹ := by group
      _ = 1 := by rw [rootTorusSL2_neg_one_mul_self]; group
  have hne : u * rootTorusSL2 τ (GaloisField p f) θ (-1) * u⁻¹ ≠ 1 := fun h => by
    refine rootTorusSL2_neg_one_ne_one hK θ ?_
    have : rootTorusSL2 τ (GaloisField p f) θ (-1) = u⁻¹ * 1 * u := by
      rw [← h]
      group
    rw [this]
    group
  exact eq_rootTorusSL2_neg_one_of_mul_self_eq_one hK hodd hzmem hsq hne


theorem rootRankOneGroup_eq_or_commute {K : Type} [Field K] (hK : ringChar K ≠ 2)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsLongRoot τ γ)
    (h : ∀ y ∈ rootRankOneGroup τ K β,
      rootTorusSL2 τ K γ (-1) * y = y * rootTorusSL2 τ K γ (-1)) :
    rootRankOneGroup τ K γ = rootRankOneGroup τ K β ∨
      ∀ x ∈ rootRankOneGroup τ K γ, ∀ y ∈ rootRankOneGroup τ K β, x * y = y * x := by
  have hmem : ∀ z : K, pinnedX τ K β z ∈ rootRankOneGroup τ K β := fun z => by
    rw [rootRankOneGroup_eq_sup hβ]
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨z, rfl⟩)
  have hev := even_two_mul_iform_div_of_commute hK hγ.1 hβ fun z => h _ (hmem z)
  rcases hγ.eq_or_eq_neg_or_iform_eq_zero hβ hev with rfl | rfl | h0
  · exact Or.inl rfl
  · left
    rw [rootRankOneGroup_eq_sup hγ.1, rootRankOneGroup_eq_sup (IsRoot.neg hγ.1), neg_neg,
      sup_comm]
  · exact Or.inr (hγ.commute_rootRankOneGroup hβ h0)

theorem injective_of_surjective_of_equiv_sl2 {P Q : Type*} [Group P] [Group Q] {F : Type}
    [Field F] [Finite F] (eP : P ≃* SL(2, F)) (eQ : Q ≃* SL(2, F)) (φ : P →* Q)
    (hφ : Function.Surjective φ) : Function.Injective φ := by
  have : Finite P := Finite.of_equiv _ eP.symm.toEquiv
  have hcard : Nat.card P = Nat.card Q := Nat.card_congr (eP.toEquiv.trans eQ.toEquiv.symm)
  exact (hφ.bijective_of_nat_card_le hcard.le).1

section Image

variable {K : Type*} [Group K]

theorem exists_rootRankOneGroup_map_conj_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (ψ : K →* ModGL τ (GaloisField p f)) (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p f))
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ) {Rθ : Subgroup K}
    (hRθ : Rθ.map ψ = rootRankOneGroup τ (GaloisField p f) θ)
    (hinj : ∀ x ∈ Rθ, ψ x = 1 → x = 1)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p f)ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p f) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p f) γ → IsLongRoot τ γ)
    {h c : K} (hc : h⁻¹ * c * h ∈ Rθ) (hsq : c * c = 1) (hne : c ≠ 1)
    {b : Fin τ.rank → (GaloisField p f)ˣ} (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hψc : ψ c = rootDiagUnit τ b) :
    ∃ γ : Fin τ.rank → ℤ, IsLongRoot τ γ ∧
      (Generic.conjSub h Rθ).map ψ = rootRankOneGroup τ (GaloisField p f) γ ∧
      ψ c = rootTorusSL2 τ (GaloisField p f) γ (-1) := by
  obtain ⟨hodd, h5⟩ := odd_and_five_le_card_galoisField hp2 hq
  have hK : ringChar (GaloisField p f) ≠ 2 := by
    rw [ringChar.eq (GaloisField p f) p]
    exact hp2
  set c' := h⁻¹ * c * h with hc'
  have hmem : ψ c' ∈ rootRankOneGroup τ (GaloisField p f) θ := by
    rw [← hRθ]
    exact Subgroup.mem_map_of_mem ψ hc
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
  · rw [← h1, ← hRθ, Subgroup.map_map]
    unfold Generic.conjSub
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp
  · rw [hcc, hd]
    exact h3

end Image

end Classical

theorem isLongRoot_of_isRoot_of_simplyLaced {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) : IsLongRoot τ γ := by
  have h2 : ∀ δ : Fin τ.rank → ℤ, IsRoot τ δ → iform δ δ = 2 := fun δ hδ => by
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hδ
    have : τ.symmetrizer j j = 1 := by
      rcases hτ with rfl | rfl | rfl <;> fin_cases j <;> decide
    rw [hj, this]
    norm_num
  exact ⟨hγ, fun δ hδ => by rw [h2 δ hδ, h2 γ hγ]⟩

section Assembly

variable {p e : ℕ} [Fact p.Prime]

theorem conjSub_mem_longestFundamental {K : Type} [Group K] {D : UniversalRootDatum K}
    {R : Subgroup K} (hR : R ∈ longestFundamental D) (g : K) :
    Generic.conjSub g R ∈ longestFundamental D := by
  obtain ⟨g', γ, hγ, rfl⟩ := hR
  refine ⟨g * g', γ, hγ, ?_⟩
  unfold Generic.conjSub
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem orthBranch_of_adjointEmbedding {t : StatedLieTag} {τ : Tag} (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ e) (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hadm : StatedLieAdmissible t 0 p e)
    (ψ : (Generic.modelUniv t 0 p e Fact.out).K →* ModGL τ (GaloisField p e))
    (hψ : ∀ x, ψ x ∈ adjointGroup τ (GaloisField p e))
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t 0 p e Fact.out).K)
    (𝒯 : Subgroup (Generic.modelUniv t 0 p e Fact.out).K)
    (hT : ∀ c ∈ 𝒯, ∃ b : Fin τ.rank → (GaloisField p e)ˣ,
      (∀ i, b i = 1 ∨ b i = -1) ∧ ψ c = rootDiagUnit τ b)
    (hframe : PairFrame 𝒯 (fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D))
    (hsingle : FundamentalSingleClass t (Generic.modelUniv t 0 p e Fact.out).D)
    {Rθ : Subgroup (Generic.modelUniv t 0 p e Fact.out).K}
    (hRθ𝓡 : Rθ ∈ fundamentalSubgroups t (Generic.modelUniv t 0 p e Fact.out).D)
    {θ : Fin τ.rank → ℤ} (hθ : IsLongRoot τ θ)
    (hRθ : Rθ.map ψ = rootRankOneGroup τ (GaloisField p e) θ)
    (hlong : ∀ (b : Fin τ.rank → (GaloisField p e)ˣ) (γ : Fin τ.rank → ℤ)
      (hγ : γ ∈ kernelRoots (maskChar (signTupleBits b))),
      componentRootSpan (GaloisField p e) (maskChar (signTupleBits b)) ⟦⟨γ, hγ⟩⟧ =
        rootRankOneGroup τ (GaloisField p e) γ → IsLongRoot τ γ) :
    OrthBranch p t 0 e := by
  intro _ _ R₁ h₁ R₂ h₂ c₁ c₂ hc₁ hc₂ ho₁ ho₂ h₂₁ h₁₂
  have hK : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  have hsq : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c * c = 1 :=
    fun {c} h => by
      rw [← pow_two]
      exact h ▸ pow_orderOf_eq_one c
  have hne : ∀ {c : (Generic.modelUniv t 0 p e Fact.out).K}, orderOf c = 2 → c ≠ 1 :=
    fun {c} h h1 => by
      rw [h1, orderOf_one] at h
      omega
  have hinj : ∀ x ∈ Rθ, ψ x = 1 → x = 1 := by
    obtain ⟨φ⟩ := nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hRθ𝓡
    obtain ⟨-, eθ, -⟩ :=
      (exceptional_Lang_root_rank_one_data τ (GaloisField p e) θ).2.2.2.2.2.2.2.1 hK
    let φ' : Rθ →* ↥(rootRankOneGroup τ (GaloisField p e) θ) :=
      (ψ.comp Rθ.subtype).codRestrict _ (fun x => by
        have h := Subgroup.mem_map_of_mem ψ x.2
        rw [hRθ] at h
        exact h)
    have hsurj : Function.Surjective φ' := fun y => by
      have hy : (y : ModGL τ (GaloisField p e)) ∈ Rθ.map ψ := by
        rw [hRθ]
        exact y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hφ' := injective_of_surjective_of_equiv_sl2 φ eθ.symm φ' hsurj
    intro x hx h1
    have e1 : ((φ' ⟨x, hx⟩ : ↥(rootRankOneGroup τ (GaloisField p e) θ)) :
        ModGL τ (GaloisField p e)) = ψ x := rfl
    have e2 : ((φ' 1 : ↥(rootRankOneGroup τ (GaloisField p e) θ)) :
        ModGL τ (GaloisField p e)) = 1 := by
      rw [map_one]
      rfl
    have : (⟨x, hx⟩ : Rθ) = 1 := hφ' (Subtype.ext (e1.trans (h1.trans e2.symm)))
    exact congrArg Subtype.val this
  refine orthBranch_of_frame ψ hker (𝓡 := longestFundamental _) (𝒯 := 𝒯)
    (fun R₁' h₁' R₂' h₂' => hframe R₁' (longestFundamental_subset t _ h₁') R₂'
      (longestFundamental_subset t _ h₂'))
    (fun R hR g => conjSub_mem_longestFundamental hR g)
    (fun R hR => commutator_eq_of_mem_longestFundamental hp2 hq hfund hadm hR)
    (fun R hR c hc hcc r hr => ?_)
    (ι := {γ : Fin τ.rank → ℤ // IsLongRoot τ γ})
    (fun i => rootRankOneGroup τ (GaloisField p e) i.1)
    (fun i => rootTorusSL2 τ (GaloisField p e) i.1 (-1))
    (fun R hR c hc hcc hc1 hc𝒯 => ?_)
    (fun i j h _ => rootRankOneGroup_eq_or_commute hK j.2.1 i.2 h)
    h₁ h₂ hc₁ hc₂ (hsq ho₁) (hne ho₁) (hsq ho₂) (hne ho₂) h₂₁ h₁₂
  · by_cases h1 : c = 1
    · rw [h1]
      simp
    · exact mul_comm_of_orderOf_eq_two_of_mem_longestFundamental hp2 hq hfund hadm hG2 hD4 hR hc
        (orderOf_eq_prime (by rwa [pow_two]) h1) r hr
  · obtain ⟨g, hg⟩ := hsingle Rθ hRθ𝓡 R (longestFundamental_subset t _ hR)
    obtain ⟨b, hb, hψc⟩ := hT c hc𝒯
    have hcg : g⁻¹ * c * g ∈ Rθ := by
      rw [hg] at hc
      exact Generic.mem_conjSub_iff.1 hc
    obtain ⟨γ, hγ, h1, h2⟩ := exists_rootRankOneGroup_map_conj_eq hp2 hq ψ hψ hθ hRθ hinj hlong
      hcg hcc hc1 hb hψc
    exact ⟨⟨γ, hγ⟩, by rw [hg]; exact h1, h2⟩

end Assembly

end CFSG.ClassicalInvolution.ModelFacts
