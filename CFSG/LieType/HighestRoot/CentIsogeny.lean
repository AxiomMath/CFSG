module

public import CFSG.LieType.HighestRoot.CentIsogenyBasic
public import CFSG.LieType.HighestRoot.CentChevalleyThree

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section SL23

theorem eq_neg_one_of_mul_self_SL23 : ∀ x : SL23, x * x = 1 → x ≠ 1 → x = -1 := by
  decide

variable {K : Type} [Field K] [Finite K]

theorem eq_one_of_mem_center_of_ne (hK3 : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) K) {x z : J} (hx : x ∈ Subgroup.center J)
    (hz : orderOf z = 2) (hxz : x ≠ z) : x = 1 := by
  set φ := e.trans (slEquivSL23 hK3)
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz; exact absurd hz (by decide)
  have hzz : z * z = 1 := by rw [← pow_two, ← hz]; exact pow_orderOf_eq_one z
  have hφz : φ z = -1 := eq_neg_one_of_mul_self_SL23 (φ z) (by rw [← map_mul, hzz, map_one])
    (fun h => hz1 (φ.injective (by rw [h, map_one])))
  rcases (mem_center_iff_of_mulEquiv hK3 e x).1 hx with h | h
  · exact φ.injective (by rw [h, map_one])
  · exact absurd (φ.injective (h.trans hφz.symm)) hxz

end SL23

section Transport

variable {τ : Tag} {K : Type} [Field K] {G : Type*} [Group G]

theorem rootGroup_eq_subgroupOf
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootGroup (rootOperatorFamily τ) K α = (rootSubgroup τ K α).subgroupOf (adjointGroup τ K) := by
  rw [rootGroup_of_isRoot hα, ← (rootOperatorFamily τ).subgroupOf_rootSubgroup_eq K ⟨α, hα⟩]

variable {p : ℕ} [Fact p.Prime] (θ : G →* adjointGroup τ K)
  (X : (Fin τ.rank → ℤ) → Subgroup G)

theorem map_sup_eq_rankOneGroup
    (hX : ∀ α, IsRoot τ α → (X α).map θ = rootGroup (rootOperatorFamily τ) K α)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (X γ ⊔ X (-γ)).map θ = rankOneGroup (adjDatum (rootOperatorFamily τ) K) γ := by
  rw [Subgroup.map_sup, hX γ hγ, hX (-γ) (IsRoot.neg hγ)]

theorem eq_of_isogeny_of_card_eq_three
    [Finite K] [Finite G] (hK3 : Nat.card K = 3)
    (hker : θ.ker ≤ Subgroup.center G) (hpk : ¬ 3 ∣ Nat.card θ.ker)
    (hX : ∀ α, IsRoot τ α → (X α).map θ = rootGroup (rootOperatorFamily τ) K α)
    (hXp : ∀ α, IsRoot τ α → IsPGroup 3 (X α)) {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true)
    (hinj : ∀ x ∈ X (Pi.single i 1) ⊔ X (-Pi.single i 1), θ x = 1 → x = 1)
    {z : G} (hz : z ∈ X (Pi.single i 1) ⊔ X (-Pi.single i 1)) (h2 : orderOf z = 2)
    {L : Subgroup G} (hLC : L ≤ Subgroup.centralizer ({z} : Set G))
    (hCL : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) (hzL : z ∈ L) :
    L = X (Pi.single i 1) ⊔ X (-Pi.single i 1) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK := ringChar_ne_two_of_card_eq_three hK3
  set γ : Fin τ.rank → ℤ := Pi.single i 1 with hγ_def
  have hγ : IsRoot τ γ := isRoot_single τ i
  set J := X γ ⊔ X (-γ) with hJ_def
  have hJmap := map_sup_eq_rankOneGroup θ X hX hγ
  rw [rankOneGroup_adjDatum _ hγ] at hJmap
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by decide)
  have hθz1 : θ z ≠ 1 := fun h => hz1 (hinj z hz h)
  have hθz2 : orderOf (θ z) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hθz1
    rw [← map_pow, ← h2, pow_orderOf_eq_one, map_one]
  have hθzQ : (θ z : ModGL τ K) ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) :=
    Subgroup.mem_subgroupOf.1 (hJmap ▸ Subgroup.mem_map_of_mem θ hz)
  have hzC : (θ z : ModGL τ K) = rootDiagUnit τ (signTuple τ K i) := by
    rw [← torusElt_neg_one_eq]
    exact eq_torusElt_neg_one hK i hθzQ (by rwa [Subgroup.orderOf_coe])
  have hXC : ∀ α ∈ rootCharKernel (signTuple τ K i),
      X α ≤ Subgroup.centralizer ({z} : Set G) := by
    intro α hα
    refine le_centralizer_of_map_commute θ hker hpk (hXp α hα.1) fun x hx => ?_
    have hθx : θ x ∈ (rootSubgroup τ K α).subgroupOf (adjointGroup τ K) := by
      rw [← rootGroup_eq_subgroupOf hα.1, ← hX α hα.1]
      exact Subgroup.mem_map_of_mem θ hx
    have hT : ((θ x : adjointGroup τ K) : ModGL τ K) ∈
        toralCentralizer τ K (signTuple τ K i) :=
      rootSpan_rootCharKernel_le_toralCentralizer _
        ((le_iSup₂_of_le α hα le_rfl : rootSubgroup τ K α ≤
          rootSpan τ K (rootCharKernel (signTuple τ K i))) (Subgroup.mem_subgroupOf.1 hθx))
    exact Subgroup.mem_centralizer_singleton_iff.1
      ((mem_toralCentralizer_iff_mem_centralizer hzC (θ x)).1 hT)
  have hinjL : ∀ x ∈ L, θ x = 1 → x = 1 := by
    intro x hx hθx
    have hxZ : (⟨x, hx⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hθx) g)
    have hzL2 : orderOf (⟨z, hzL⟩ : L) = 2 := by rwa [← Subgroup.orderOf_coe]
    have hne : (⟨x, hx⟩ : L) ≠ ⟨z, hzL⟩ := fun h => hθz1 (by
      rw [← hθx]
      exact congrArg θ (congrArg Subtype.val h).symm)
    exact congrArg Subtype.val (eq_one_of_mem_center_of_ne hK3 eL hxZ hzL2 hne)
  set f : G →* ModGL τ K := (adjointGroup τ K).subtype.comp θ with hf
  have hfL : Function.Injective (f.comp L.subtype) := by
    refine (injective_iff_map_eq_one _).2 fun x hx => Subtype.ext (hinjL x.1 x.2 ?_)
    exact Subtype.ext hx
  have hrange : (f.comp L.subtype).range = L.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have eL' : L.map f ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    ((MonoidHom.ofInjective hfL).trans (MulEquiv.subgroupCongr hrange)).symm.trans eL
  have hLX : L.map f ≤ toralCentralizer τ K (signTuple τ K i) := by
    rintro _ ⟨l, hl, rfl⟩
    refine (mem_toralCentralizer_iff_mem_centralizer hzC (θ l)).2
      (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)]
  have hLN : rootSpan τ K (rootCharKernel (signTuple τ K i)) ≤
      Subgroup.normalizer ((L.map f : Subgroup (ModGL τ K)) : Set (ModGL τ K)) := by
    refine iSup₂_le fun α hα => ?_
    intro s hs
    have hsH : s ∈ adjointGroup τ K := rootSubgroup_le_adjointGroup α hs
    have hs' : (⟨s, hsH⟩ : adjointGroup τ K) ∈ (X α).map θ := by
      rw [hX α hα.1, rootGroup_eq_subgroupOf hα.1]
      exact Subgroup.mem_subgroupOf.2 hs
    obtain ⟨t, ht, hθt⟩ := hs'
    have hN : t ∈ Subgroup.normalizer (L : Set G) := hCL (hXC α hα ht)
    have h := Subgroup.le_normalizer_map f ⟨t, hN, rfl⟩
    rwa [hf, MonoidHom.comp_apply, hθt] at h
  have hLQ := eq_sup_of_card_eq_three hK3 (iform_le_of_symmetrizer_le hlong) hc hLX hLN eL'
  have hmapL : L.map θ = J.map θ := by
    refine Subgroup.map_injective (f := (adjointGroup τ K).subtype) Subtype.val_injective ?_
    rw [Subgroup.map_map, ← hf, hLQ, hJmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.2]
    exact sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)
  have hgen := closure_orderOf_three_eq_top_of_mulEquiv hK3 eL
  have hle : L ≤ J := by
    intro x hx
    have hle' : Subgroup.closure {y : L | orderOf y = 3} ≤ J.subgroupOf L := by
      refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2 ?_
      have hy' : orderOf (y : G) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact hy
      have hy3 : (y : G) ^ (3 ^ 1) = 1 := by
        rw [pow_one, ← hy']
        exact pow_orderOf_eq_one _
      exact mem_of_map_mem θ hker hpk (hmapL ▸ Subgroup.mem_map_of_mem θ y.2) hy3
    exact Subgroup.mem_subgroupOf.1 (hle' (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : L)))
  have hθL : Function.Injective (θ.comp L.subtype) := by
    refine (injective_iff_map_eq_one _).2 fun x hx => Subtype.ext (hinjL x.1 x.2 hx)
  have hθJ : Function.Injective (θ.comp J.subtype) := by
    refine (injective_iff_map_eq_one _).2 fun x hx => Subtype.ext (hinj x.1 x.2 hx)
  have hcL : Nat.card L = Nat.card (L.map θ) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hθL).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hcJ : Nat.card J = Nat.card (J.map θ) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hθJ).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hcL, hcJ, hmapL]

theorem centralizerCondition_of_isogeny
    [Finite K] [Finite G] [CharP K p] (hτ : NoG2 τ)
    (hK : ringChar K ≠ 2)
    (hker : θ.ker ≤ Subgroup.center G) (hpk : ¬ p ∣ Nat.card θ.ker)
    (hX : ∀ α, IsRoot τ α → (X α).map θ = rootGroup (rootOperatorFamily τ) K α)
    (hXp : ∀ α, IsRoot τ α → IsPGroup p (X α)) {i : Fin τ.rank}
    (hlong : ∀ j, τ.symmetrizer j j ≤ τ.symmetrizer i i) {wit : List ℕ}
    (hc : isolatedCheck τ i wit = true)
    (hinj : ∀ x ∈ X (Pi.single i 1) ⊔ X (-Pi.single i 1), θ x = 1 → x = 1) :
    CentralizerCondition K (X (Pi.single i 1) ⊔ X (-Pi.single i 1)) := by
  have hγ : IsRoot τ (Pi.single i 1) := isRoot_single τ i
  have hJmap := map_sup_eq_rankOneGroup θ X hX hγ
  intro z hz h2
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at h2; exact absurd h2 (by decide)
  have hθz1 : θ z ≠ 1 := fun h => hz1 (hinj z hz h)
  have hθz2 : orderOf (θ z) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ hθz1
    rw [← map_pow, ← h2, pow_orderOf_eq_one, map_one]
  have hθzJ : θ z ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1) :=
    hJmap ▸ Subgroup.mem_map_of_mem θ hz
  refine ⟨centralizer_le_normalizer_of_map θ hker hpk (hXp _ hγ) (hXp _ (IsRoot.neg hγ)) ?_,
    fun hK3 L hLC hCL ⟨eL⟩ hzL => ?_⟩
  · rw [hJmap]
    exact centralizer_le_normalizer_rankOneGroup hτ hK hlong hc hθzJ hθz2
  · have hp3 : p = 3 := by
      have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast three_eq_zero hK3
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
        ((CharP.cast_eq_zero_iff K p 3).1 h3)
    subst hp3
    exact eq_of_isogeny_of_card_eq_three θ X hK3 hker hpk hX hXp hlong hc hinj hz h2 hLC hCL eL
      hzL

end Transport

end CFSG.LieType.HighestRoot
