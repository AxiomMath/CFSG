module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain
public import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus

open CFSG.AGLEmbedding Subgroup CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

variable {r : ℕ} {K : Type} [Field K]

theorem plusResIdx_swap {t m : ℕ} (htm : t + m = r) (i : Fin m) (x : Fin m ⊕ Fin m) :
    plusResIdx htm (Equiv.swap (Sum.inl i) (Sum.inr i) x) =
      Equiv.swap (Sum.inl ⟨t + i, by have := i.isLt; omega⟩)
        (Sum.inr ⟨t + i, by have := i.isLt; omega⟩) (plusResIdx htm x) := by
  rcases x with j | j
  · by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_left, plusResIdx_inr, plusResIdx_inl, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hji) Sum.inl_ne_inr, plusResIdx_inl,
        Equiv.swap_apply_of_ne_of_ne]
      · rintro h
        exact hji (Fin.ext (by simpa using congrArg Fin.val (Sum.inl_injective h)))
      · exact Sum.inl_ne_inr
  · by_cases hji : j = i
    · subst hji
      rw [Equiv.swap_apply_right, plusResIdx_inl, plusResIdx_inr, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (by simpa using hji), plusResIdx_inr,
        Equiv.swap_apply_of_ne_of_ne]
      · exact Sum.inr_ne_inl
      · rintro h
        exact hji (Fin.ext (by simpa using congrArg Fin.val (Sum.inr_injective h)))

theorem plusResExt_swapPair {t m : ℕ} (htm : t + m = r) (i : Fin m) :
    plusResExt K htm (swapPair K i) = swapPair K (⟨t + i, by have := i.isLt; omega⟩ : Fin r) := by
  refine LinearEquiv.ext fun v => funext fun c => ?_
  by_cases hc : c ∈ Set.range (plusResIdx htm)
  · obtain ⟨c', rfl⟩ := hc
    change ((plusResExt K htm (swapPair K i)) v ∘ plusResIdx htm) c' =
      (swapPair K (⟨t + i, by have := i.isLt; omega⟩ : Fin r)) v (plusResIdx htm c')
    rw [plusResExt_apply_comp, swapPair_apply, Function.comp_apply, plusResIdx_swap,
      swapPair_apply]
  · rw [plusResExt_apply_of_not_mem htm _ v hc, swapPair_apply]
    have hfix : Equiv.swap (Sum.inl ⟨t + i, by have := i.isLt; omega⟩)
        (Sum.inr ⟨t + i, by have := i.isLt; omega⟩) c = c := by
      rw [Equiv.swap_apply_of_ne_of_ne]
      · rintro rfl
        exact hc ⟨Sum.inl i, rfl⟩
      · rintro rfl
        exact hc ⟨Sum.inr i, rfl⟩
    rw [hfix]

theorem plusResExt_swapPair_last {t m : ℕ} (htm : t + m = r) (hm : 1 ≤ m) :
    plusResExt K htm (swapPair K (⟨m - 1, by omega⟩ : Fin m)) =
      swapPair K (⟨r - 1, by omega⟩ : Fin r) := by
  rw [plusResExt_swapPair htm (⟨m - 1, by omega⟩ : Fin m)]
  congr 1
  ext
  simp only
  omega

theorem plusResAut_comp_plusResIdx {D : Finset ℕ} (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ}
    (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) {g : ↥(plusFlagStab K r D)}
    {y : Fin r ⊕ Fin r → K} (hy : y ∈ plusCutSpace r K (2 * r - t)) :
    (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) y ∘ plusResIdx htm =
      plusResAut hD ht htm g (y ∘ plusResIdx htm) := by
  classical
  have hz : y - Function.extend (plusResIdx htm) (y ∘ plusResIdx htm) 0 ∈
      plusCutSpace r K t := by
    intro u hu
    rw [Pi.sub_apply]
    by_cases hmem : u ∈ Set.range (plusResIdx htm)
    · obtain ⟨s, rfl⟩ := hmem
      rw [extend_plusResIdx_apply, Function.comp_apply, sub_self]
    · rw [extend_plusResIdx_apply_of_not_mem htm _ hmem, sub_zero]
      have hge : 2 * r - t ≤ plusPos r u := by
        by_contra hlt
        exact hmem ((mem_range_plusResIdx htm u).2 ⟨hu, not_le.mp hlt⟩)
      exact hy u hge
  have hgz : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) _ ∈ plusCutSpace r K t :=
    mapsTo_of_plusCut (plusCut_of_mem_plusFlagStab hD g.2 ht).1 _ hz
  funext s
  rw [Function.comp_apply, plusResAut_apply, Function.comp_apply]
  have hu : t ≤ plusPos r (plusResIdx htm s) :=
    ((mem_range_plusResIdx htm (plusResIdx htm s)).1 ⟨s, rfl⟩).1
  have hzero := hgz _ hu
  rw [map_sub] at hzero
  exact sub_eq_zero.mp (by simpa using hzero)

theorem swapIso_not_mem_orthElementaryGroup [Finite K] (hr : 3 ≤ r) (hq : Even (Nat.card K))
    (i : Fin r) :
    (swapIso K i : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∉
      orthElementaryGroup (quadPlus r K) := by
  intro hmem
  have hchar :=
    (orthogonal_geometry_split_maximal_family_character (K := K) (r := r) hr).2.2.2.2.2 hq
  have h1 : maxSign r K (swapIso K i) = 1 := by
    have h2 := hchar.1 (Subgroup.mem_subgroupOf.2 hmem)
    simpa [MonoidHom.mem_ker] using h2
  rw [maxSign_swapIso (by omega) hq i] at h1
  have hne : ((-1 : ℤˣ) : ℤ) ≠ ((1 : ℤˣ) : ℤ) := by norm_num
  exact hne (congrArg (fun u : ℤˣ => (u : ℤ)) h1)

theorem index_orthElementaryGroup_subgroupOf [Finite K] [CharP K 2] {m : ℕ} (hm : 3 ≤ m) :
    ((orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))).index = 2 := by
  have hnd := nondegenerate_polarBilin_quadPlus m K
  have hcard : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) =
      2 * Nat.card (orthElementaryGroup (quadPlus m K)) :=
    CFSG.Timmesfeld.ClassicalOrders.card_orthogonalGroup_eq_two_mul hnd
      (plusPair_orth (K := K) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩) (by simp [Fin.ext_iff]))
      (regular_quadPlus (by omega)).2
      (orthogonalGroup_le_closure_of_two_eq_zero (plusFamily_orth (by omega)) hnd
        CharTwo.two_eq_zero
        (fun x hx _ => eq_zero_of_mem_tailSpace_plusFamily (by omega) hx)
        (fun x hx hx0 => absurd (eq_zero_of_mem_tailSpace_plusFamily (by omega) hx) hx0)
        (by omega))
  have : Finite ↥(orthElementaryGroup (quadPlus m K)) := finite_orthElementaryGroup
  have hEcard : Nat.card ((orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))) =
      Nat.card (orthElementaryGroup (quadPlus m K)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (orthElementaryGroup_le _)).toEquiv
  have h1 := Subgroup.card_mul_index ((orthElementaryGroup (quadPlus m K)).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)))
  rw [hEcard, hcard] at h1
  have hpos : 0 < Nat.card (orthElementaryGroup (quadPlus m K)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem plusResAut_mem_orthElementaryGroup [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, d ≤ r) {t m : ℕ} (ht : t = 0 ∨ t ∈ D) (htm : t + m = r) (hm : 3 ≤ m)
    (g : ↥(plusFlagStab K r D)) :
    plusResAut hD ht htm g ∈ orthElementaryGroup (quadPlus m K) := by
  classical
  have heven : Even (Nat.card K) := by
    obtain ⟨n, hn, hcard⟩ := card_eq_two_pow_of_charP_two (K := K)
    rw [hcard]
    exact even_two.pow_of_ne_zero hn
  set h : (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K) := plusResAut hD ht htm g with hh
  have hO : h ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) := by
    rw [hh]
    exact plusResAut_mem_orthogonalGroup hD ht htm g
  by_contra hhE
  have hmax : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
      (plusResExt K htm h)⁻¹ ∈ maxStab r K := by
    refine mem_maxStab.2 ⟨mul_mem (orthElementaryGroup_le _ (mem_plusFlagStab.1 g.2).1)
      (inv_mem (plusResExt_mem_orthogonalGroup htm hO)), ?_⟩
    have hmapTo : ∀ x ∈ plusCutSpace r K r,
        (((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
          (plusResExt K htm h)⁻¹) x) ∈ plusCutSpace r K r := by
      intro x hx
      rw [LinearEquiv.mul_apply, ← map_inv]
      set y : Fin r ⊕ Fin r → K := plusResExt K htm h⁻¹ x with hydef
      have hy : y ∈ plusCutSpace r K (2 * r - t) := by
        intro u hu
        by_cases hur : u ∈ Set.range (plusResIdx htm)
        · rw [mem_range_plusResIdx htm] at hur
          omega
        · rw [hydef, plusResExt_apply_of_not_mem htm _ _ hur]
          exact hx u (by omega)
      have hgy : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) y ∈
          plusCutSpace r K (2 * r - t) :=
        mapsTo_orthogonal_of_smul_eq (mem_orthogonalGroup_of_mem_plusFlagStab g.2)
          (by omega : t ≤ r) (smul_flag_of_mem_plusFlagStab g.2 ht) y hy
      have hcomp : ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) y) ∘
          plusResIdx htm = x ∘ plusResIdx htm := by
        rw [plusResAut_comp_plusResIdx hD ht htm hy, ← hh, hydef, plusResExt_apply_comp]
        change h (h⁻¹ (x ∘ plusResIdx htm)) = x ∘ plusResIdx htm
        rw [← LinearEquiv.mul_apply, mul_inv_cancel]
        rfl
      intro u hu
      by_cases hu2 : 2 * r - t ≤ plusPos r u
      · exact hgy u hu2
      · rw [not_le] at hu2
        obtain ⟨s, rfl⟩ := (mem_range_plusResIdx htm u).2 ⟨by omega, hu2⟩
        have h1 : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) y (plusResIdx htm s) =
            (((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) y) ∘
              plusResIdx htm) s := rfl
        rw [h1, hcomp, Function.comp_apply]
        exact hx _ hu
    rw [flag_eq_plusCutSpace le_rfl]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact hmapTo x hx
    · rw [LinearEquiv.finrank_map_eq]
  have hHE : plusResExt K htm h ∈ orthElementaryGroup (quadPlus r K) := by
    have h1 : ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
        (plusResExt K htm h)⁻¹)⁻¹ *
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        orthElementaryGroup (quadPlus r K) :=
      mul_mem (inv_mem (maxStab_le_orthElementaryGroup hr hmax)) (mem_plusFlagStab.1 g.2).1
    have h2 : ((g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) *
        (plusResExt K htm h)⁻¹)⁻¹ *
        (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) = plusResExt K htm h := by
      group
    rwa [h2] at h1
  have hsO : swapPair K (⟨m - 1, by omega⟩ : Fin m) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K) :=
    (swapIso K ⟨m - 1, by omega⟩).2
  have hsE : swapPair K (⟨m - 1, by omega⟩ : Fin m) ∉
      orthElementaryGroup (quadPlus m K) := by
    have h := swapIso_not_mem_orthElementaryGroup (K := K) hm heven (⟨m - 1, by omega⟩ : Fin m)
    simpa [coe_swapIso] using h
  have hmul : h * (swapPair K (⟨m - 1, by omega⟩ : Fin m))⁻¹ ∈
      orthElementaryGroup (quadPlus m K) := by
    set Eo := (orthElementaryGroup (quadPlus m K)).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)) with hEo
    have hidx : Eo.index = 2 := index_orthElementaryGroup_subgroupOf (K := K) hm
    have h1 : (⟨h, hO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))) ∉ Eo := by
      intro hc
      exact hhE (Subgroup.mem_subgroupOf.1 hc)
    have h2 : (⟨swapPair K (⟨m - 1, by omega⟩ : Fin m), hsO⟩ :
        ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))) ∉ Eo := by
      intro hc
      exact hsE (Subgroup.mem_subgroupOf.1 hc)
    have h3 : (⟨h, hO⟩ : ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K))) *
        (⟨swapPair K (⟨m - 1, by omega⟩ : Fin m), hsO⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus m K)))⁻¹ ∈ Eo := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      exact ⟨fun ha => absurd ha h1,
        fun hb => absurd ((Subgroup.inv_mem_iff Eo).mp hb) h2⟩
    simpa using Subgroup.mem_subgroupOf.1 h3
  have hHE2 : plusResExt K htm (h * (swapPair K (⟨m - 1, by omega⟩ : Fin m))⁻¹) ∈
      orthElementaryGroup (quadPlus r K) :=
    plusResExt_mem_orthElementaryGroup htm hm hmul
  have hsr : plusResExt K htm (swapPair K (⟨m - 1, by omega⟩ : Fin m)) =
      swapPair K (⟨r - 1, by omega⟩ : Fin r) :=
    plusResExt_swapPair_last htm (by omega)
  have hsrE : swapPair K (⟨r - 1, by omega⟩ : Fin r) ∉ orthElementaryGroup (quadPlus r K) := by
    have h := swapIso_not_mem_orthElementaryGroup (K := K) hr heven (⟨r - 1, by omega⟩ : Fin r)
    simpa [coe_swapIso] using h
  apply hsrE
  rw [← hsr]
  have hcalc : plusResExt K htm (swapPair K (⟨m - 1, by omega⟩ : Fin m)) =
      (plusResExt K htm (h * (swapPair K (⟨m - 1, by omega⟩ : Fin m))⁻¹))⁻¹ *
        plusResExt K htm h := by
    rw [← map_inv, ← map_mul]
    congr 1
    group
  rw [hcalc]
  exact mul_mem (inv_mem hHE2) hHE

theorem hasLeviCensus_of_sum {Q : Type} [Group Q] [Finite Q] {ι₁ ι₂ : Type}
    [Finite ι₁] [DecidableEq ι₁] [Finite ι₂] [DecidableEq ι₂]
    {G₁ : ι₁ → Type} [∀ j, Group (G₁ j)] [∀ j, Finite (G₁ j)]
    {G₂ : ι₂ → Type} [∀ j, Group (G₂ j)] [∀ j, Finite (G₂ j)]
    (S₁ : ∀ j, Subgroup (G₁ j)) (T₁ : ∀ j, Subgroup (G₁ j))
    (S₂ : ∀ j, Subgroup (G₂ j)) (T₂ : ∀ j, Subgroup (G₂ j))
    (β₁ : ∀ j, Q →* G₁ j) (β₂ : ∀ j, Q →* G₂ j)
    (hker : ∀ N : Subgroup Q, (∀ q ∈ N, (∀ j, β₁ j q = 1) ∧ ∀ j, β₂ j q = 1) → IsPGroup 2 N)
    (hST₁ : ∀ j, S₁ j ≤ T₁ j) (hST₂ : ∀ j, S₂ j ≤ T₂ j)
    (hidx₁ : ∀ j, ¬ 2 ∣ (S₁ j).relIndex (T₁ j))
    (hidx₂ : ∀ j, ¬ 2 ∣ (S₂ j).relIndex (T₂ j))
    (hT₁ : ∀ j, ∀ q, β₁ j q ∈ T₁ j) (hT₂ : ∀ j, ∀ q, β₂ j q ∈ T₂ j)
    (hs₁ : ∀ j, ∀ x ∈ S₁ j, ∃ q, β₁ j q = x ∧ (∀ j', j' ≠ j → β₁ j' q = 1) ∧
      ∀ j', β₂ j' q = 1)
    (hs₂ : ∀ j, ∀ x ∈ S₂ j, ∃ q, β₂ j q = x ∧ (∀ j', j' ≠ j → β₂ j' q = 1) ∧
      ∀ j', β₁ j' q = 1)
    (hc₁ : ∀ j, ⁅(β₁ j).range, (β₁ j).range⁆ ≤ S₁ j)
    (hc₂ : ∀ j, ⁅(β₂ j).range, (β₂ j).range⁆ ≤ S₂ j)
    (hW₁ : ∀ j, S₁ j = ⊥ ∨ IsWBlock ↥(S₁ j))
    (hW₂ : ∀ j, S₂ j = ⊥ ∨ IsWBlock ↥(S₂ j)) :
    HasLeviCensus Q IsWBlock := by
  classical
  let S : ∀ j, Subgroup (plusSumGroup G₁ G₂ j) := fun j => match j with
    | .inl a => S₁ a
    | .inr b => S₂ b
  let T : ∀ j, Subgroup (plusSumGroup G₁ G₂ j) := fun j => match j with
    | .inl a => T₁ a
    | .inr b => T₂ b
  let β' : ∀ j, Q →* plusSumGroup G₁ G₂ j := fun j => match j with
    | .inl a => β₁ a
    | .inr b => β₂ b
  have hker' : ∀ N : Subgroup Q, (∀ q ∈ N, ∀ j, β' j q = 1) → IsPGroup 2 N := by
    intro N hN
    exact hker N fun q hq => ⟨fun j => hN q hq (Sum.inl j), fun j => hN q hq (Sum.inr j)⟩
  have hpile : Subgroup.pi Set.univ S ≤ (MonoidHom.pi β').range := by
    rw [Subgroup.pi_le_iff]
    rintro (a | b) _ ⟨x, hx, rfl⟩
    · obtain ⟨q, hq, h1, h2⟩ := hs₁ a x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · by_cases ha : a' = a
        · subst ha
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => ha (Sum.inl_injective h))]
          exact h1 a' ha
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inr_ne_inl]
        exact h2 b'
    · obtain ⟨q, hq, h1, h2⟩ := hs₂ b x hx
      refine ⟨q, funext fun j => ?_⟩
      rcases j with a' | b'
      · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
        rw [Pi.mulSingle_eq_of_ne Sum.inl_ne_inr]
        exact h2 a'
      · by_cases hb : b' = b
        · subst hb
          simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
          exact hq
        · simp only [MonoidHom.pi_apply, MonoidHom.mulSingle_apply]
          rw [Pi.mulSingle_eq_of_ne (fun h => hb (Sum.inr_injective h))]
          exact h1 b' hb
  have hcomm : ⁅(MonoidHom.pi β').range, (MonoidHom.pi β').range⁆ ≤ Subgroup.pi Set.univ S := by
    intro z hz
    refine (Subgroup.mem_pi _).2 fun j _ => ?_
    have hmap := Subgroup.map_commutator (MonoidHom.pi β').range (MonoidHom.pi β').range
      (Pi.evalMonoidHom (plusSumGroup G₁ G₂) j)
    have hz' : Pi.evalMonoidHom (plusSumGroup G₁ G₂) j z ∈
        ⁅((MonoidHom.pi β').range.map (Pi.evalMonoidHom _ j)),
          ((MonoidHom.pi β').range.map (Pi.evalMonoidHom _ j))⁆ := by
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    have hr : (MonoidHom.pi β').range.map (Pi.evalMonoidHom (plusSumGroup G₁ G₂) j) =
        (β' j).range := by
      rw [MonoidHom.range_eq_map, Subgroup.map_map, MonoidHom.range_eq_map]
      rfl
    rw [hr] at hz'
    rcases j with a | b
    · exact hc₁ a hz'
    · exact hc₂ b hz'
  have hpiT : (MonoidHom.pi β').range ≤ Subgroup.pi Set.univ T := by
    rintro _ ⟨q, rfl⟩
    rw [Subgroup.mem_pi]
    rintro (a | b) _
    · exact hT₁ a q
    · exact hT₂ b q
  have hidx : ¬ 2 ∣ (Subgroup.pi Set.univ S).relIndex (MonoidHom.pi β').range :=
    not_two_dvd_relIndex_pi_of_finite (S := S) (T := T)
      (fun j => by rcases j with a | b; exacts [hST₁ a, hST₂ b]) hpile hpiT
      (fun j => by rcases j with a | b; exacts [hidx₁ a, hidx₂ b])
  have hn : (MonoidHom.pi β').range ≤ normalizer (Subgroup.pi Set.univ S :
      Set (∀ j, plusSumGroup G₁ G₂ j)) :=
    le_normalizer_of_commutator_le hpile hcomm
  let H : Subgroup Q := ((⊤ : Subgroup Q).subgroupOf (⊤ : Subgroup Q)).comap
    (Subgroup.topEquiv.symm : Q ≃* ↥(⊤ : Subgroup Q)).toMonoidHom
  let β : ↥H →* ∀ j, plusSumGroup G₁ G₂ j := (MonoidHom.pi β').comp (Subgroup.subtype H)
  have hβ : IsPGroup 2 β.ker := by
    have hN : IsPGroup 2 ((β.ker).map (Subgroup.subtype H)) := by
      refine hker' _ fun q hq => ?_
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
      intro j
      exact congrFun (MonoidHom.mem_ker.1 hx) j
    exact hN.of_equiv (Subgroup.equivMapOfInjective β.ker (Subgroup.subtype H)
      (Subgroup.subtype_injective H)).symm
  have hHtop : H = ⊤ := by
    ext x
    simp only [H, Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_top]
  have hrange : β.range = (MonoidHom.pi β').range := by
    rw [show β = (MonoidHom.pi β').comp (Subgroup.subtype H) from rfl, MonoidHom.range_comp,
      Subgroup.range_subtype, hHtop, Subgroup.map_top]
  have hS : ∀ j, S j = ⊥ ∨ IsWBlock ↥(S j) := by
    rintro (a | b)
    · exact hW₁ a
    · exact hW₂ b
  have htop : HasLeviCensus ↥(⊤ : Subgroup Q) IsWBlock :=
    hasLeviCensus_of_mulEquiv_of_finite (X := Q) (C := Q) (L := ⊤) (J := ⊤) le_rfl
      (Subgroup.topEquiv.symm) (G := fun j => plusSumGroup G₁ G₂ j) (S := S) β hβ
      (hrange ▸ hpile) (hrange ▸ hn) (hrange ▸ hidx) hS
  exact HasLeviCensus.of_mulEquiv Subgroup.topEquiv htop

theorem hasLeviCensus_plusFlagStab_top [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hrD : r ∈ D) :
    HasLeviCensus ↥(plusFlagStab K r D) IsWBlock := by
  classical
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have ht : D.sup id = r := le_antisymm (Finset.sup_le hD') (Finset.le_sup (f := id) hrD)
  have := finite_plusAut (K := K) r
  refine hasLeviCensus_of_sum (ι₁ := ↥D) (ι₂ := Empty)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => Unit)
    (S₁ := fun b => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →* _).range)
    (T₁ := fun _ => ⊤) (S₂ := fun _ => ⊥) (T₂ := fun _ => ⊥)
    (β₁ := fun b => plusEBlockHom hD' b.2) (β₂ := fun e => e.elim)
    (hker := ?_) (hST₁ := fun _ => le_top) (hST₂ := fun e => e.elim)
    (hidx₁ := ?_) (hidx₂ := fun e => e.elim)
    (hT₁ := fun _ _ => Subgroup.mem_top _) (hT₂ := fun e => e.elim)
    (hs₁ := ?_) (hs₂ := fun e => e.elim)
    (hc₁ := fun b => commutator_range_plusEBlockHom_le hD' b.2) (hc₂ := fun e => e.elim)
    (hW₁ := ?_) (hW₂ := fun e => e.elim)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    rw [ht] at hx ⊢
    rw [show 2 * r - r = r by omega] at hx
    have hgx : (g : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) x ∈ plusCutSpace r K r := by
      rw [← flag_eq_plusCutSpace le_rfl, ← smul_flag_of_mem_plusFlagStab g.2 (Or.inr hrD)]
      rw [← flag_eq_plusCutSpace le_rfl] at hx
      exact ⟨x, hx, rfl⟩
    exact sub_mem hgx hx
  · intro b
    change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
        GL (Fin (b.1 - predCut D b.1)) K).range).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact not_two_dvd_index_range_toGL _
  · intro b x hx
    obtain ⟨q, h1, h2, -⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    exact ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun e => e.elim⟩
  · intro b
    rcases range_toGL_cases (K := K) (m := (b.1 - predCut D b.1)) with hbot | h3 | hq
    · exact Or.inl hbot
    · exact Or.inr (Or.inr h3.2.2)
    · exact Or.inr (Or.inl hq)

theorem hasLeviCensus_plusFlagStab_res [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht3 : D.sup id + 3 ≤ r) :
    HasLeviCensus ↥(plusFlagStab K r D) IsWBlock := by
  classical
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  set t := D.sup id with htdef
  have ht : t = 0 ∨ t ∈ D := sup_eq_zero_or_mem D
  have htm : t + (r - t) = r := by omega
  have hm : 3 ≤ r - t := by omega
  have hDt : ∀ d ∈ D, d ≤ t := fun d hd => Finset.le_sup (f := id) hd
  have := finite_plusAut (K := K) r
  have := finite_plusAut (K := K) (r - t)
  refine hasLeviCensus_of_sum (ι₁ := ↥D) (ι₂ := Unit)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K)
    (G₂ := fun _ => (Fin (r - t) ⊕ Fin (r - t) → K) ≃ₗ[K] (Fin (r - t) ⊕ Fin (r - t) → K))
    (S₁ := fun b => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →* _).range)
    (T₁ := fun _ => ⊤) (S₂ := fun _ => orthElementaryGroup (quadPlus (r - t) K))
    (T₂ := fun _ => orthElementaryGroup (quadPlus (r - t) K))
    (β₁ := fun b => plusEBlockHom hD' b.2) (β₂ := fun _ => plusResAut hD' ht htm)
    (hker := ?_) (hST₁ := fun _ => le_top) (hST₂ := fun _ => le_rfl)
    (hidx₁ := ?_) (hidx₂ := fun _ => by rw [Subgroup.relIndex_self]; norm_num)
    (hT₁ := fun _ _ => Subgroup.mem_top _)
    (hT₂ := fun _ q => plusResAut_mem_orthElementaryGroup hr hD' ht htm hm q)
    (hs₁ := ?_) (hs₂ := ?_)
    (hc₁ := fun b => commutator_range_plusEBlockHom_le hD' b.2) (hc₂ := ?_)
    (hW₁ := ?_) (hW₂ := ?_)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht htm
      (plusResBlockHom_eq_one_of_plusResAut hD' ht htm ((hN g hg).2 ())) hx
  · intro b
    change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
        GL (Fin (b.1 - predCut D b.1)) K).range).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact not_two_dvd_index_range_toGL _
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun _ => ?_⟩
    change matrixEquiv (r - t) K (plusResBlockHom hD' ht htm q) = 1
    rw [h3 ht htm (hDt b b.2), map_one]
  · rintro ⟨⟩ x hx
    exact ⟨⟨plusResExt K htm x, plusResExt_mem_plusFlagStab htm hm hDt hx⟩,
      plusResAut_plusResExt hD' ht htm _, fun ⟨⟩ hne => absurd rfl hne,
      fun b => plusEBlockHom_plusResExt hD' htm hDt b.2 _⟩
  · rintro ⟨⟩
    rw [← OrthogonalSplit.commutator_orthogonalGroup_quadPlus hm]
    have hle : (plusResAut (K := K) hD' ht htm).range ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus (r - t) K) := by
      rintro _ ⟨g, rfl⟩
      exact plusResAut_mem_orthogonalGroup hD' ht htm g
    exact Subgroup.commutator_mono hle hle
  · intro b
    rcases range_toGL_cases (K := K) (m := (b.1 - predCut D b.1)) with hbot | h3 | hq
    · exact Or.inl hbot
    · exact Or.inr (Or.inr h3.2.2)
    · exact Or.inr (Or.inl hq)
  · rintro ⟨⟩
    refine Or.inr (Or.inl ⟨(isQuasisimple_plusElementary hm).1, ?_⟩)
    rw [(isQuasisimple_plusElementary hm).2, Subgroup.card_bot]
    exact odd_one

theorem hasLeviCensus_plusFlagStab_two [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (ht2 : D.sup id + 2 = r) :
    HasLeviCensus ↥(plusFlagStab K r D) IsWBlock := by
  classical
  have hD' : ∀ d ∈ D, d ≤ r := fun d hd => (hD d hd).2
  have hD1 : ∀ d ∈ D, 1 ≤ d := fun d hd => (hD d hd).1
  have hDt : ∀ d ∈ D, d ≤ D.sup id := fun d hd => Finset.le_sup (f := id) hd
  have hD₂ : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r - 2 := fun d hd => ⟨hD1 d hd, by have := hDt d hd; omega⟩
  have ht : D.sup id = 0 ∨ D.sup id ∈ D := sup_eq_zero_or_mem D
  have := finite_plusAut (K := K) r
  refine hasLeviCensus_of_sum (ι₁ := ↥D) (ι₂ := Fin 2)
    (G₁ := fun b => GL (Fin (b.1 - predCut D b.1)) K) (G₂ := fun _ => GL (Fin 2) K)
    (S₁ := fun b => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →* _).range)
    (T₁ := fun _ => ⊤)
    (S₂ := fun _ => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range)
    (T₂ := fun _ => (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range)
    (β₁ := fun b => plusEBlockHom hD' b.2) (β₂ := plusFamHom K hr hD₂ hD' ht ht2)
    (hker := ?_) (hST₁ := fun _ => le_top) (hST₂ := fun _ => le_rfl)
    (hidx₁ := ?_) (hidx₂ := fun _ => by rw [Subgroup.relIndex_self]; norm_num)
    (hT₁ := fun _ _ => Subgroup.mem_top _)
    (hT₂ := fun j q => by
      fin_cases j <;> exact MonoidHom.mem_range.mpr ⟨_, rfl⟩)
    (hs₁ := ?_) (hs₂ := ?_)
    (hc₁ := fun b => commutator_range_plusEBlockHom_le hD' b.2) (hc₂ := ?_)
    (hW₁ := ?_) (hW₂ := ?_)
  · intro N hN
    refine isPGroup_of_plusBlocks hD' hD1 fun g hg => ⟨fun b hb => (hN g hg).1 ⟨b, hb⟩,
      fun x hx => ?_⟩
    exact sub_mem_of_plusResBlockHom_eq_one hD' ht ht2 (plusResBlockHom_eq_one_of_plusResAut hD'
      ht ht2 (plusResAut_eq_one_of_plusFamHom hr hD₂ hD' ht ht2 ((hN g hg).2 0)
        ((hN g hg).2 1))) hx
  · intro b
    change ¬ 2 ∣ ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin (b.1 - predCut D b.1)) K →*
        GL (Fin (b.1 - predCut D b.1)) K).range).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact not_two_dvd_index_range_toGL _
  · intro b x hx
    obtain ⟨q, h1, h2, h3⟩ := exists_plusFlagLevi_of_mem hr hD' b.2 hx
    refine ⟨q, h1, fun b' hne => h2 b'.1 b'.2 fun h => hne (Subtype.ext h), fun j => ?_⟩
    refine plusFamHom_eq_one hr hD₂ hD' ht ht2 ?_ j
    change matrixEquiv 2 K (plusResBlockHom hD' ht ht2 q) = 1
    rw [h3 ht ht2 (hDt b b.2), map_one]
  · intro j x hx
    obtain ⟨A, rfl⟩ := hx
    fin_cases j
    · have hq := plusResExt_iotaTwo_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaTwo hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e0, fun j' hj' => ?_,
        fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact absurd rfl hj'
      · exact e1
    · have hq := plusResExt_iotaOne_mem hr ht2 (D := D) hDt A
      obtain ⟨e0, e1⟩ := plusFamHom_iotaOne hr hD₂ hD' ht ht2 hq
      refine ⟨⟨_, hq⟩, e1, fun j' hj' => ?_,
        fun b => plusEBlockHom_plusResExt hD' ht2 hDt b.2 hq⟩
      fin_cases j'
      · exact e0
      · exact absurd rfl hj'
  · intro j
    have hle : (plusFamHom K hr hD₂ hD' ht ht2 j).range ≤
        (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) K →* GL (Fin 2) K).range := by
      fin_cases j <;> rintro _ ⟨g, rfl⟩ <;> exact ⟨_, rfl⟩
    refine (Subgroup.commutator_mono hle hle).trans (Subgroup.commutator_le.2 fun a ha b hb => ?_)
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · intro b
    rcases range_toGL_cases (K := K) (m := (b.1 - predCut D b.1)) with hbot | h3 | hq
    · exact Or.inl hbot
    · exact Or.inr (Or.inr h3.2.2)
    · exact Or.inr (Or.inl hq)
  · intro j
    rcases range_toGL_cases (K := K) (m := 2) with hbot | h3 | hq
    · exact Or.inl hbot
    · exact Or.inr (Or.inr h3.2.2)
    · exact Or.inr (Or.inl hq)

theorem hasLeviCensus_plusFlagStab [Finite K] [CharP K 2] (hr : 3 ≤ r) {D : Finset ℕ}
    (hD : ∀ d ∈ D, 1 ≤ d ∧ d ≤ r) (hr1 : r - 1 ∈ D → r ∈ D) :
    HasLeviCensus ↥(plusFlagStab K r D) IsWBlock := by
  have hle : D.sup id ≤ r := Finset.sup_le fun d hd => (hD d hd).2
  rcases sup_eq_zero_or_mem D with h0 | hmem
  · exact hasLeviCensus_plusFlagStab_res hr hD (by omega)
  · by_cases htop : D.sup id = r
    · exact hasLeviCensus_plusFlagStab_top hr hD (htop ▸ hmem)
    · by_cases h1 : D.sup id + 1 = r
      · exfalso
        have := Finset.le_sup (f := id) (hr1 (by rw [← h1, Nat.add_sub_cancel]; exact hmem))
        simp only [id] at this
        omega
      · by_cases h2 : D.sup id + 2 = r
        · exact hasLeviCensus_plusFlagStab_two hr hD h2
        · exact hasLeviCensus_plusFlagStab_res hr hD (by omega)

theorem hasLeviCensus_idxD (hZ : OddCenterRest) {X : Type} [Group X] [Finite X]
    {L J : Subgroup X} (hCP : CompParab L J) (h : IsLieOf IdxD (↥L ⧸ center ↥L)) :
    HasLeviCensus ↥J IsWBlock := by
  obtain ⟨r, K, hKf, hKfin, hCh, hr, ⟨φ⟩⟩ :=
    exists_mulEquiv_plusElementary_of_idxD hZ hCP.comp hCP.odd h
  obtain ⟨ψ, I, -, hI, hψ⟩ := exists_plusNodeStab_of_compParab hr hCP φ
  rw [plusNodeStab_eq_plusFlagStab (by omega : 3 ≤ r) hI] at hψ
  obtain ⟨hD1, hDr⟩ := plusNodeDims_props (by omega : 3 ≤ r) hI
  have hcensus : HasLeviCensus ↥(plusFlagStab K r (plusNodeDims I)) IsWBlock :=
    hasLeviCensus_plusFlagStab (by omega : 3 ≤ r) hD1 hDr
  exact HasLeviCensus.of_mulEquiv
    ((MulEquiv.subgroupCongr hψ).symm.trans
      ((Subgroup.equivMapOfInjective ((J.subgroupOf L).map ψ.toMonoidHom)
        (orthElementaryGroup (quadPlus r K)).subtype
        (Subgroup.subtype_injective _)).symm.trans
        ((Subgroup.equivMapOfInjective (J.subgroupOf L) ψ.toMonoidHom ψ.injective).symm.trans
          (Subgroup.subgroupOfEquivOfLe hCP.parab.1)))) hcensus

end CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
