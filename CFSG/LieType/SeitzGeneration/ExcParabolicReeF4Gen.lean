module

public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Levi
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4Parab
public import CFSG.LieType.SeitzGeneration.ExcParabolicModel

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG

theorem fixedOrbitRoots_subset_complement_of_ne (t : ReeTag) {j k : Fin t.fixedOrbitCount}
    (hjk : j ≠ k) : t.fixedOrbitRoots j ⊆ t.fixedOrbitComplementRoots k := by
  intro α hα
  obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitRoots_iff.1 hα
  have hne : ∃ i, α i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : height α = 0 := by simp [height, h]
    omega
  obtain ⟨i, hi⟩ := hne
  have hij : t.fixedOrbitIndex i = j := by
    by_contra hj
    exact hi (hsupp i hj)
  exact mem_fixedOrbitComplementRoots_iff.2 ⟨hroot, hpos, i, by rw [hij]; exact hjk, hi⟩


section Ree

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem map_conj_reeFixedOrbitUnipotent_longest {w₀ : WeylGroup F4.tag}
    (hw₀ : ∀ w, (coxeterSystem F4.tag).length w ≤ (coxeterSystem F4.tag).length w₀)
    (j : Fin F4.fixedOrbitCount) :
    (F4.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem F4.tag) K w₀)).toMonoidHom =
      F4.reeFixedOrbitNegUnipotent K a j := by
  have hn := (canonicalRep_longest_mem_reeFixedMonomial (K := K) (a := a) hw₀).2
  have hU := (canonical_weyl_root_transport F4.tag K).1 w₀ (F4.fixedOrbitRoots j)
    fun α hα => (fixedOrbitRoots_subset j hα).1
  have himg : (fun α => w₀ • α) '' F4.fixedOrbitRoots j = Neg.neg '' F4.fixedOrbitRoots j := by
    simp only [smul_longest hw₀]
  rw [himg] at hU
  rw [reeFixedOrbitUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective, hU,
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl


theorem reeGamma_le_iSup_centralizer_of_le_levi
    [IsSimpleGroup ↥(F4.reeGamma K a)] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (j : Fin F4.fixedOrbitCount) {A : Subgroup (ModGL F4.tag K)}
    [IsElementaryAbelian p A] (hcard : p ^ 2 ≤ Nat.card A)
    (hAL : A ≤ F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a) :
    F4.reeGamma K a ≤ ⨆ x ∈ A, ⨆ (_ : x ≠ 1),
      F4.reeGamma K a ⊓ Subgroup.centralizer ({x} : Set (ModGL F4.tag K)) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element F4.tag
  set n := canonicalRep (coxeterSystem F4.tag) K w₀ with hn
  have hnΓ : n ∈ F4.reeGamma K a := (canonicalRep_longest_mem_reeFixedMonomial hw₀).2
  set V := F4.reeFixedOrbitComplementUnipotent K a j with hV
  set V' := V.map (MulAut.conj n⁻¹).toMonoidHom with hV'
  set L := F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a with hL
  obtain ⟨i, hij⟩ : ∃ i : Fin F4.fixedOrbitCount, i ≠ j := by
    have : ∀ j : Fin F4.fixedOrbitCount, ∃ i : Fin F4.fixedOrbitCount, i ≠ j := by decide
    exact this j
  have hVΓ : V ≤ F4.reeGamma K a := inf_le_right
  have hV'Γ : V' ≤ F4.reeGamma K a := by
    rintro _ ⟨v, hv, rfl⟩
    exact mul_mem (mul_mem (inv_mem hnΓ) (hVΓ hv)) (by simpa using hnΓ)
  have hBP := (reeFixedBorel_lt_reeLocalParabolic (K := K) (a := a) (t := F4) j).le
  have hLP : L ≤ F4.reeLocalParabolic K a j :=
    sup_le (reeLocalBlock_le j) (reeFixedTorus_le_reeFixedBorel.trans hBP)
  have hLV : L ≤ Subgroup.normalizer (V : Set (ModGL F4.tag K)) :=
    hLP.trans (reeLocalParabolic_le_normalizer_complement j)
  have hnL : L.map (MulAut.conj n).toMonoidHom ≤
      Subgroup.normalizer (V : Set (ModGL F4.tag K)) := by
    rw [hL, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [reeLocalBlock, Subgroup.map_sup, map_conj_reeFixedOrbitUnipotent_longest hw₀,
        map_conj_reeFixedOrbitNegUnipotent_longest hw₀, sup_comm]
      exact (reeLocalBlock_le j).trans (reeLocalParabolic_le_normalizer_complement j)
    · rw [map_conj_reeFixedTorus hw₀]
      exact reeFixedTorus_le_normalizer_complement j
  have hLV' : L ≤ Subgroup.normalizer (V' : Set (ModGL F4.tag K)) := fun l hl =>
    mem_normalizer_map_conj_inv (hnL ⟨l, hl, rfl⟩)
  have hV2 : IsPGroup 2 V := isPGroup_reeFixedOrbitComplementUnipotent j
  have hV'2 : IsPGroup 2 V' := hV2.map _
  have hpV : ¬ p ∣ Nat.card V := not_dvd_card_of_isPGroup (Ne.symm hp2) hV2
  have hpV' : ¬ p ∣ Nat.card V' := not_dvd_card_of_isPGroup (Ne.symm hp2) hV'2
  have h1 := le_iSup_inf_centralizer_of_coprime (C := F4.reeGamma K a) hcard hpV
    (hAL.trans hLV) hVΓ
  have h2 := le_iSup_inf_centralizer_of_coprime (C := F4.reeGamma K a) hcard hpV'
    (hAL.trans hLV') hV'Γ
  have hXV : ∀ k, k ≠ j → F4.reeFixedOrbitUnipotent K a k ≤ V := fun k hk =>
    inf_le_inf_right _ (rootSpan_mono (fixedOrbitRoots_subset_complement_of_ne F4 hk))
  have hYV' : ∀ k, k ≠ j → F4.reeFixedOrbitNegUnipotent K a k ≤ V' := by
    intro k hk y hy
    refine ⟨n * y * n⁻¹, hXV k hk ?_, ?_⟩
    · rw [← map_conj_reeFixedOrbitNegUnipotent_longest hw₀ k]
      exact ⟨y, hy, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hMW : ∀ k, k ≠ j → F4.reeLocalBlock K a k ≤ V ⊔ V' := fun k hk =>
    sup_le ((hXV k hk).trans le_sup_left) ((hYV' k hk).trans le_sup_right)
  have hMN : ∀ k, F4.reeLocalBlock K a k ≤
      Subgroup.normalizer ((V ⊔ V' : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
    intro k
    by_cases hk : k = j
    · subst hk
      exact fun m hm => mem_normalizer_sup_of_mem (hLV (Subgroup.mem_sup_left hm))
        (hLV' (Subgroup.mem_sup_left hm))
    · exact (hMW k hk).trans Subgroup.le_normalizer
  have hΓN : F4.reeGamma K a ≤
      Subgroup.normalizer ((V ⊔ V' : Subgroup (ModGL F4.tag K)) : Set (ModGL F4.tag K)) := by
    rw [large_Ree_simple_pair_generation a K hK]
    exact sup_le (hMN _) (hMN _)
  have hWΓ : V ⊔ V' ≤ F4.reeGamma K a := sup_le hVΓ hV'Γ
  have hWnorm : ((V ⊔ V').subgroupOf (F4.reeGamma K a)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWΓ).2 hΓN
  have hV1 : V ≠ ⊥ := by
    obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (t := F4) (K := K) (a := a) i
    intro hbot
    apply hu1
    have := hXV i hij hu
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hWtop : F4.reeGamma K a ≤ V ⊔ V' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((V ⊔ V').subgroupOf (F4.reeGamma K a))
      with h | h
    · exfalso
      have hW : V ⊔ V' = ⊥ := (Subgroup.subgroupOf_eq_bot.1 h).eq_bot_of_le hWΓ
      exact hV1 (eq_bot_iff.2 (le_sup_left.trans hW.le))
    · exact Subgroup.subgroupOf_eq_top.1 h
  exact hWtop.trans (sup_le h1 h2)


theorem rootInvariantGeneration_reeGamma
    [IsSimpleGroup ↥(F4.reeGamma K a)] (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) : RootInvariantGeneration (F4.reeGamma K a) 2 p := by
  intro A R hAΓ hA hcard hRΓ hRp hR hAR
  have := hA
  have := finite_modGL (τ := F4.tag) (K := K)
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  obtain ⟨g, hgΓ, j, hAj⟩ := exists_conj_le_reeLocalParabolic hK hAΓ hRΓ hR hRp hAR
  have hA1p : IsPGroup p (A.map (MulAut.conj g).toMonoidHom) :=
    (IsElementaryAbelian.isPGroup p A).map _
  obtain ⟨y, hyP, hyA⟩ := exists_conj_le_levi j hp2 hAj hA1p
  have hxΓ : y * g ∈ F4.reeGamma K a := mul_mem (Subgroup.mem_inf.1 hyP).1 hgΓ
  have hmap : A.map (MulAut.conj (y * g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.map_map, map_mul]
    rfl
  have hAx : A.map (MulAut.conj (y * g)).toMonoidHom ≤
      F4.reeLocalBlock K a j ⊔ F4.reeFixedTorus K a := hmap ▸ hyA
  have : IsElementaryAbelian p (A.map (MulAut.conj (y * g)).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hcard' : p ^ 2 ≤ Nat.card (A.map (MulAut.conj (y * g)).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (y * g)).injective]
    exact hcard
  exact le_iSup_inf_centralizer_of_map_conj hxΓ
    (reeGamma_le_iSup_centralizer_of_le_levi hK hp2 j hcard' hAx)

end Ree

end CFSG.LieType.SeitzGeneration
