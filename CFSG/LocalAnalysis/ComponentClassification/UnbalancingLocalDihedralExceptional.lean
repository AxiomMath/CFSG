module

public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.RankOneFaithful
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedGS

namespace DihedralExceptional

theorem height_le_maxHeight_stringData {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    height v ≤ τ.stringData.maxHeight := by
  have hS := τ.stringData_check
  simp only [StringData.check, Bool.and_eq_true] at hS
  obtain ⟨⟨⟨hb, -⟩, -⟩, -⟩ := hS
  simp only [StringData.checkBuckets, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at hb
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
  have h := hb k hk
  simp only [StringData.bucket] at h
  split_ifs at h with hr
  · omega
  · simp at h

theorem pinnedX_commute {τ : Tag} {K : Type} [Field K] {α β : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hβ : IsRoot τ β) (hαp : 0 < height α) (hβp : 0 < height β)
    (hne : α ≠ β) (hnot : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → ¬ IsRoot τ (a • α + b • β)) (c d : K) :
    Commute (pinnedX τ K α c) (pinnedX τ K β d) := by
  have hbot : ⁅rootSubgroup τ K α, rootSubgroup τ K β⁆ = ⊥ := by
    refine le_bot_iff.1 ((commutator_rootSubgroup_le K hα hβ hαp hβp hne).trans ?_)
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    exact absurd hγr (hnot a b ha hb)
  have h := Subgroup.commutator_mem_commutator (H₁ := rootSubgroup τ K α)
    (H₂ := rootSubgroup τ K β) (mem_rootSubgroup.2 ⟨c, rfl⟩) (mem_rootSubgroup.2 ⟨d, rfl⟩)
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem mul_mul_mul_of_commute {G : Type*} [Monoid G] {a₀ a₁ a₂ b₀ b₁ b₂ : G}
    (h₁ : Commute b₀ (a₁ * a₂)) (h₂ : Commute b₁ a₂) :
    a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by
  calc a₀ * b₀ * (a₁ * b₁) * (a₂ * b₂) = a₀ * b₀ * a₁ * (b₁ * a₂) * b₂ := by
        simp only [mul_assoc]
    _ = a₀ * b₀ * a₁ * (a₂ * b₁) * b₂ := by rw [h₂.eq]
    _ = a₀ * (b₀ * (a₁ * a₂)) * b₁ * b₂ := by simp only [mul_assoc]
    _ = a₀ * (a₁ * a₂ * b₀) * b₁ * b₂ := by rw [h₁.eq]
    _ = a₀ * a₁ * a₂ * (b₀ * b₁ * b₂) := by simp only [mul_assoc]

structure TopRoots (τ : Tag) where
  H : ℤ
  α : Fin 3 → Fin τ.rank → ℤ
  three_lt : 3 < H
  height_le : ∀ v, IsRoot τ v → height v ≤ H
  isRoot : ∀ i, IsRoot τ (α i)
  height_eq : ∀ i : Fin 3, height (α i) = H - (i : ℕ)

namespace TopRoots

variable {τ : Tag} (R : TopRoots τ)

theorem height_pos (i : Fin 3) : 0 < height (R.α i) := by
  have := R.height_eq i
  have := R.three_lt
  have : (i : ℕ) ≤ 2 := Nat.lt_succ_iff.1 i.2
  omega

theorem injective : Function.Injective R.α := fun i j h => by
  have h' := congrArg height h
  rw [R.height_eq, R.height_eq] at h'
  exact Fin.ext (by omega)

theorem commute {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j) (c d : K) :
    Commute (pinnedX τ K (R.α i) c) (pinnedX τ K (R.α j) d) := by
  refine pinnedX_commute (R.isRoot i) (R.isRoot j) (R.height_pos i) (R.height_pos j)
    (fun h => hij (R.injective h)) (fun a b ha hb hr => ?_) c d
  have hle := R.height_le _ hr
  rw [height_nsmul_add_nsmul, R.height_eq, R.height_eq] at hle
  have hi : (i : ℕ) ≤ 2 := Nat.lt_succ_iff.1 i.2
  have hj : (j : ℕ) ≤ 2 := Nat.lt_succ_iff.1 j.2
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  have hsum : ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ≤ 3 := by omega
  have h3 := R.three_lt
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hi' : ((i : ℕ) : ℤ) ≤ 2 := by exact_mod_cast hi
  have hj' : ((j : ℕ) : ℤ) ≤ 2 := by exact_mod_cast hj
  nlinarith [mul_nonneg (sub_nonneg.2 ha') (by linarith : (0 : ℤ) ≤ R.H - (i : ℕ)),
    mul_nonneg (sub_nonneg.2 hb') (by linarith : (0 : ℤ) ≤ R.H - (j : ℕ))]

include R in
theorem exists_injective_hom (K : Type) [Field K] :
    ∃ φ : Multiplicative (Fin 3 → K) →* adjointGroup τ K, Function.Injective φ := by
  let x : Fin 3 → K → ModGL τ K := fun i c => pinnedX τ K (R.α i) c
  have key : ∀ e : Fin 3 → K,
      (List.ofFn fun i => pinnedX τ K (R.α i) (e i)).prod = x 0 (e 0) * x 1 (e 1) * x 2 (e 2) := by
    intro e
    simp [x, List.ofFn_succ, mul_assoc]
  let φ : Multiplicative (Fin 3 → K) →* adjointGroup τ K :=
    { toFun := fun c => ⟨x 0 (Multiplicative.toAdd c 0) * x 1 (Multiplicative.toAdd c 1) *
          x 2 (Multiplicative.toAdd c 2), mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
            (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _)⟩
      map_one' := by
        apply Subtype.ext
        simp [x, pinnedX_zero]
      map_mul' := fun c d => by
        apply Subtype.ext
        change x 0 (Multiplicative.toAdd c 0 + Multiplicative.toAdd d 0) *
            x 1 (Multiplicative.toAdd c 1 + Multiplicative.toAdd d 1) *
            x 2 (Multiplicative.toAdd c 2 + Multiplicative.toAdd d 2) =
          x 0 (Multiplicative.toAdd c 0) * x 1 (Multiplicative.toAdd c 1) *
              x 2 (Multiplicative.toAdd c 2) *
            (x 0 (Multiplicative.toAdd d 0) * x 1 (Multiplicative.toAdd d 1) *
              x 2 (Multiplicative.toAdd d 2))
        simp only [x, pinnedX_add]
        exact mul_mul_mul_of_commute
          ((R.commute (by decide) _ _).mul_right (R.commute (by decide) _ _))
          (R.commute (by decide) _ _) }
  refine ⟨φ, fun c d h => ?_⟩
  have h' : x 0 (Multiplicative.toAdd c 0) * x 1 (Multiplicative.toAdd c 1) *
      x 2 (Multiplicative.toAdd c 2) = x 0 (Multiplicative.toAdd d 0) *
        x 1 (Multiplicative.toAdd d 1) * x 2 (Multiplicative.toAdd d 2) :=
    congrArg Subtype.val h
  rw [← key, ← key] at h'
  exact Multiplicative.toAdd.injective
    ((positive_root_product_injectivity τ K R.α R.injective
      fun i => ⟨R.isRoot i, R.height_pos i⟩).2 h')

end TopRoots

theorem isRoot_of_memDec {τ : Tag} {v : Fin τ.rank → ℤ}
    (h : τ.stringData.memDec τ.rootCertificate v = true) : IsRoot τ v :=
  (StringData.memDec_iff τ.rootCertificate_check τ.stringData_check).1 h

@[expose] def topRootsG2 : TopRoots .G2 where
  H := 5
  α := ![![2, 3], ![1, 3], ![1, 2]]
  three_lt := by norm_num
  height_le v hv := height_le_maxHeight_stringData hv
  isRoot i := by fin_cases i <;> exact isRoot_of_memDec (by decide +kernel)
  height_eq i := by fin_cases i <;> decide

@[expose] def topRootsF4 : TopRoots .F4 where
  H := 11
  α := ![![2, 3, 4, 2], ![1, 3, 4, 2], ![1, 2, 4, 2]]
  three_lt := by norm_num
  height_le v hv := height_le_maxHeight_stringData hv
  isRoot i := by fin_cases i <;> exact isRoot_of_memDec (by decide +kernel)
  height_eq i := by fin_cases i <;> decide

@[expose] def topRootsE6 : TopRoots .E6 where
  H := 11
  α := ![![1, 2, 2, 3, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 1, 2, 2, 2, 1]]
  three_lt := by norm_num
  height_le v hv := height_le_maxHeight_stringData hv
  isRoot i := by fin_cases i <;> exact isRoot_of_memDec (by decide +kernel)
  height_eq i := by fin_cases i <;> decide

@[expose] def topRootsE7 : TopRoots .E7 where
  H := 17
  α := ![![2, 2, 3, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1]]
  three_lt := by norm_num
  height_le v hv := height_le_maxHeight_stringData hv
  isRoot i := by fin_cases i <;> exact isRoot_of_memDec (by decide +kernel)
  height_eq i := by fin_cases i <;> decide

@[expose] def topRootsE8 : TopRoots .E8 where
  H := 29
  α := ![![2, 3, 4, 6, 5, 4, 3, 2], ![2, 3, 4, 6, 5, 4, 3, 1], ![2, 3, 4, 6, 5, 4, 2, 1]]
  three_lt := by norm_num
  height_le v hv := height_le_maxHeight_stringData hv
  isRoot i := by fin_cases i <;> exact isRoot_of_memDec (by decide +kernel)
  height_eq i := by fin_cases i <;> decide

theorem injective_adjointGroup_hom {T : Type} [Group T] {τ : Tag} {K : Type} [Field K]
    [Finite K] (e : T ≃* AdjointQuotient τ K) :
    Function.Injective (e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K)))) := by
  refine e.symm.injective.comp ?_
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  exact center_adjointGroup_eq_bot

theorem exists_injective_sl2 (τ : Tag) {K : Type} [Field K] (hK : ringChar K ≠ 2) :
    ∃ φ : SL2 K →* adjointGroup τ K, Function.Injective φ := by
  have i : Fin τ.rank := ⟨0, by cases τ <;> decide⟩
  obtain ⟨-, e, -⟩ := odd_Chevalley_simple_root_SL2_faithful τ K hK i
  have hle : Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ≤
      adjointGroup τ K :=
    (Subgroup.closure_le _).2 (Set.union_subset
      (Set.range_subset_iff.2 fun c => xUnit_mem_adjointGroup i c)
      (Set.range_subset_iff.2 fun c => yUnit_mem_adjointGroup i c))
  exact ⟨(Subgroup.inclusion hle).comp e.toMonoidHom,
    (Subgroup.inclusion_injective hle).comp e.injective⟩

theorem isElementaryAbelian_top_pi {K : Type} [Field K] (h2 : (2 : K) = 0) :
    CFSG.IsElementaryAbelian 2 (⊤ : Subgroup (Multiplicative (Fin 3 → K))) := by
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
  change (x : Multiplicative (Fin 3 → K)) ^ 2 = 1
  apply Multiplicative.toAdd.injective
  funext i
  rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat, h2,
    zero_mul]

theorem untwisted_exclusion {T : Type} [Group T] {τ : Tag} (R : TopRoots τ) {p f : ℕ}
    (hp : p.Prime) (hf : 1 ≤ f) (hT : UntwistedChevalleyModel T τ (p ^ f)) (s : ℕ) (hs : 2 ≤ s)
    (P : Sylow 2 T) : ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  rintro ⟨eP⟩
  obtain ⟨K, _, _, hK, ⟨eT⟩⟩ := hT
  have : Finite T := Finite.of_equiv _ eT.symm.toEquiv
  obtain ⟨hrank, hQ8⟩ :=
    SmallLocal.dihedral_sylow_rank_and_quaternion_obstructions hs ⟨P, ⟨eP⟩⟩
  have hchar : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hι := injective_adjointGroup_hom eT
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    obtain ⟨φ, hφ⟩ := R.exists_injective_hom K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := isElementaryAbelian_top_pi h2
    let ψ := (eT.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K)))).comp φ
    have hψ : Function.Injective ψ := hι.comp hφ
    have hEl := CFSG.IsElementaryAbelian.map
      (A := (⊤ : Subgroup (Multiplicative (Fin 3 → K)))) (p := 2) ψ
    have hcard : Nat.card ((⊤ : Subgroup (Multiplicative (Fin 3 → K))).map ψ) = 2 ^ (f * 3) := by
      rw [Subgroup.card_map_of_injective hψ, Subgroup.card_top]
      change Nat.card (Fin 3 → K) = _
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin, hK, ← pow_mul]
    have hle := RankOneCenter.le_pRank_of_subgroup hEl hcard
    omega
  ·
    have hkchar : ringChar K ≠ 2 := by
      rw [ringChar.eq K p]
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) even_two
    obtain ⟨φ, hφ⟩ := exists_injective_sl2 τ hkchar
    let ψ := (eT.symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K)))).comp φ
    have hψ : Function.Injective ψ := hι.comp hφ
    have hneg : (-1 : SL2 K) ≠ 1 := by
      intro h
      have h00 := congrArg (fun g : SL2 K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h
      have h1 : (-1 : K) = 1 := by simpa using h00
      exact hkchar (neg_one_eq_one_iff.1 h1)
    obtain ⟨H, ⟨eH⟩⟩ := SymplecticExclusion.exists_quaternion_of_sl2_hom hkchar ψ (by
      rw [Ne, map_eq_one_iff ψ hψ]
      exact hneg)
    exact hQ8 ⟨H, ⟨eH⟩⟩

end DihedralExceptional

open DihedralExceptional

theorem dihedral_sylow_ordinary_exceptional_model_exclusion {T : Type} [Group T]
    {t : Assembly.LowTwoRank.StatedLieTag} {p f : ℕ}
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hT : ChevalleyExceptionalModel T t p f) (s : ℕ) (hs : 2 ≤ s) (P : Sylow 2 T) :
    ¬ Nonempty ((P : Subgroup T) ≃* DihedralGroup (2 ^ (s - 1))) := by
  obtain ⟨⟨hp, hf, -⟩, hmodel⟩ := hT
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact untwisted_exclusion topRootsG2 hp hf hmodel s hs P
  · exact untwisted_exclusion topRootsF4 hp hf hmodel s hs P
  · exact untwisted_exclusion topRootsE6 hp hf hmodel s hs P
  · exact untwisted_exclusion topRootsE7 hp hf hmodel s hs P
  · exact untwisted_exclusion topRootsE8 hp hf hmodel s hs P

end CFSG.ComponentClassification.UnbalancingLocal
