module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3GDefs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Q3GAlt
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InnerTL4
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4JHat
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
  CFSG.ComponentClassification.CatFactsL4U4 StabL CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem false_of_isSimpleGroup_le {G : Type} [Group G] [Finite G] {α : MulAut G}
    {T M : Subgroup G} (hTM : T ≤ M) (hMfix : ∀ y ∈ M, α y = y) (hM : IsSimpleGroup M)
    {t : G} (htT : t ∈ T) (ht1 : t ≠ 1) (heven : Even (Nat.card T)) {x : G} (hxM : x ∈ M)
    (hxT : x ∉ T)
    (hsub : ((T ⊔ oddCoreIn (fixedSubgroup α)).subgroupOf (fixedSubgroup α)).IsSubnormal) :
    False := by
  set C := fixedSubgroup α
  have hMC : M ≤ C := fun y hy => hMfix y hy
  have hTC : T ≤ C := hTM.trans hMC
  have hCO : C ≤ normalizer (oddCoreIn C : Set G) :=
    le_normalizer.trans
      (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic C (pPrimeCore 2 C))
  haveI := hM
  haveI : IsSimpleGroup ↥(M.subgroupOf C) := (subgroupOfEquivOfLe hMC).isSimpleGroup
  have hN := hsub.subgroupOf (K := M.subgroupOf C)
  rcases hN.eq_bot_or_top_of_isSimpleGroup inferInstance with hbot | htop
  · apply ht1
    have h1 : (⟨⟨t, hTC htT⟩, hTM htT⟩ : ↥(M.subgroupOf C)) ∈
        ((T ⊔ oddCoreIn C).subgroupOf C).subgroupOf (M.subgroupOf C) := by
      rw [mem_subgroupOf, mem_subgroupOf]
      exact mem_sup_left htT
    rw [hbot, mem_bot] at h1
    exact congrArg (fun y : ↥(M.subgroupOf C) => ((y : C) : G)) h1
  · have h1 : (⟨⟨x, hMC hxM⟩, hxM⟩ : ↥(M.subgroupOf C)) ∈
        ((T ⊔ oddCoreIn C).subgroupOf C).subgroupOf (M.subgroupOf C) := by
      rw [htop]
      exact mem_top _
    rw [mem_subgroupOf, mem_subgroupOf] at h1
    have h2 : x ∈ ((T ⊔ oddCoreIn C : Subgroup G) : Set G) := h1
    rw [coe_mul_of_left_le_normalizer_right T (oddCoreIn C) (hTC.trans hCO), Set.mem_mul] at h2
    obtain ⟨a, ha, o, ho, hao⟩ := h2
    have hoM : o ∈ M := by
      have h3 : a⁻¹ * x ∈ M := mul_mem (inv_mem (hTM ha)) hxM
      rwa [← hao, inv_mul_cancel_left] at h3
    have hnorm : ((oddCoreIn C).subgroupOf M).Normal := by
      constructor
      intro n hn m
      rw [mem_subgroupOf] at hn ⊢
      simpa using (mem_normalizer_iff.mp (hCO (hMC m.2)) n).mp hn
    rcases hnorm.eq_bot_or_eq_top with h3 | h3
    · have h4 : (⟨o, hoM⟩ : M) ∈ (oddCoreIn C).subgroupOf M := ho
      rw [h3, mem_bot] at h4
      have ho1 : o = 1 := congrArg Subtype.val h4
      apply hxT
      rw [← hao, ho1, mul_one]
      exact ha
    · have hTO : T ≤ oddCoreIn C := fun y hy => by
        have h4 : (⟨y, hTM hy⟩ : M) ∈ (oddCoreIn C).subgroupOf M := by
          rw [h3]
          exact mem_top _
        exact h4
      have hodd : Odd (Nat.card (oddCoreIn C)) := UnbalancedGS.odd_card_map_pPrimeCore_two C
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hTO))) heven

theorem l43FixedA6Input_holds : L43FixedA6Input := by
  intro G _ _ hL ℓ hℓ T hTC hTp hT360 α hαα hαT hsub
  classical
  have hSCM := hL.statedClassicalModel_of_ne_zero (by norm_num)
  have hGs : IsSimpleGroup G := (CFSG.LieType.Simplicity.fam_PSL_simplicity G 4 3 1 hSCM).2
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hSCM
  let : Fintype F := Fintype.ofFinite F
  have hF3 : Fintype.card F = 3 := by rw [Fintype.card_eq_nat_card, hF, pow_one]
  have hF4 : Fintype.card F % 4 = 3 := by rw [hF3]
  have hℓ1 : ℓ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hℓ
    omega
  have hℓ2 : ℓ ^ 2 = 1 := by rw [← hℓ, pow_orderOf_eq_one]
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨v, hv⟩ :=
    exists_prime_orderOf_dvd_card' (G := T) 5 ((by norm_num : 5 ∣ 360).trans hT360)
  have hv1 : (v : G) ≠ 1 := by
    intro h1
    have h2 : orderOf (v : G) = 1 := by rw [h1, orderOf_one]
    rw [Subgroup.orderOf_coe, hv] at h2
    omega
  obtain ⟨X, hX⟩ := QuotientGroup.mk_surjective (e ℓ)
  have hXX := CatFactsL4U4.sq_eq_neg_one_of_comm_orderOf (u := e ℓ) (v := e (v : G))
    (by rw [hF3]; decide) (by rw [Ne, MulEquiv.map_eq_one_iff]; exact hℓ1)
    (by rw [← map_pow, hℓ2, map_one]) Nat.prime_five (by norm_num) (by rw [hF3]; norm_num)
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hv])
    (by rw [← map_mul, ← map_mul, (mem_centralizer_singleton_iff.mp (hTC v.2)).symm]) X hX
  obtain ⟨e', he'⟩ := CatFactsL4U4.exists_normalized_equiv hF4 e X hX hXX
  set T' := T.map e'.toMonoidHom with hT'
  have hT'k : T' ≤ centralizer {proj 4 F k₀} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← he', ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.mp (hTC hy)]
  have hTp' : ⁅T, T⁆ = T := Subgroup.isPerfect_iff.mp hTp
  have hT'p : ⁅T', T'⁆ = T' := by rw [hT', ← map_commutator, hTp']
  have hcard' : Nat.card F ^ 2 * ((Nat.card F ^ 2) ^ 2 - 1) ≤ 2 * Nat.card T' := by
    rw [card_map_of_injective e'.injective, hF, pow_one]
    have := Nat.le_of_dvd Nat.card_pos hT360
    omega
  have hT'eq : T' = J₀ F := eq_J₀ hF4 hT'k hT'p hcard'
  have hU : HasUnipotents T' := by
    rw [hT'eq]
    exact hasUnipotents_J₀ hF4
  have hvT' : e' (v : G) ∈ T' := mem_map_of_mem _ v.2
  set α' := MulAut.congr e' α with hα'
  have hα'e : ∀ y, α' (e' y) = e' (α y) := fun y => by
    show e' (α (e'.symm (e' y))) = e' (α y)
    rw [MulEquiv.symm_apply_apply]
  have hα'2 : α' ^ 2 = 1 := by rw [sq, hα', ← map_mul, hαα, map_one]
  have hα'fix : ∀ y ∈ T', α' y = y := by
    rintro _ ⟨t, ht, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, hα'e, hαT t ht]
  rcases inner_or_alternating hF4 Nat.prime_three hF α' (m := 0) (by simpa using hα'2) hU
      hα'fix with ⟨z, hz⟩ | ⟨A, hA, hαA⟩
  ·
    have hzC : z ∈ centralizer (T' : Set (projectiveSL 4 F)) := by
      rw [mem_centralizer_iff]
      intro y hy
      have h1 := hα'fix y hy
      rw [← hz, MulAut.conj_apply] at h1
      calc y * z = z * y * z⁻¹ * z := by rw [h1]
        _ = z * y := by group
    have hkC : proj 4 F k₀ ∈ centralizer (T' : Set (projectiveSL 4 F)) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hT'k hy)
    have hk2 : proj 4 F k₀ ^ 2 = 1 := by rw [← he', ← map_pow, hℓ2, map_one]
    have hk1 : proj 4 F k₀ ≠ 1 := by
      rw [← he', Ne, MulEquiv.map_eq_one_iff]
      exact hℓ1
    have hZ : center (projectiveSL 4 F) = ⊥ := by
      haveI : IsSimpleGroup (projectiveSL 4 F) := e'.symm.isSimpleGroup
      rcases (inferInstance : (center (projectiveSL 4 F)).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have hT'b : T' = ⊥ := by
          rw [← hT'p, commutator_eq_bot_iff_le_centralizer]
          intro y _
          rw [mem_centralizer_iff]
          intro w _
          have hy : y ∈ center (projectiveSL 4 F) := by
            rw [h]
            exact mem_top y
          exact mem_center_iff.mp hy w
        rw [hT'b, mem_bot, MulEquiv.map_eq_one_iff] at hvT'
        exact hv1 hvT'
    have hz2 : z ^ 2 = 1 := by
      have h1 : MulAut.conj (z ^ 2) = 1 := by rw [map_pow, hz, hα'2]
      rw [CatFactsL4U4.conj_eq_one_iff_mem_center, hZ, mem_bot] at h1
      exact h1
    have := isCyclic_centralizer hF4 hU
    by_cases hz1 : z = 1
    · left
      apply (MulAut.congr e').injective
      rw [← hα', ← hz, hz1, map_one, map_one]
    · right
      have hzk : z = proj 4 F k₀ := congrArg Subtype.val
        (CatFactsL4U4.eq_of_sq_eq_one_of_isCyclic
          (a := (⟨z, hzC⟩ : centralizer (T' : Set (projectiveSL 4 F))))
          (b := ⟨proj 4 F k₀, hkC⟩) (Subtype.ext (by simpa using hz2))
          (Subtype.ext (by simpa using hk2)) (fun h => hz1 (congrArg Subtype.val h))
          (fun h => hk1 (congrArg Subtype.val h)))
      apply (MulAut.congr e').injective
      rw [← hα', ← hz, hzk, ← he', congr_conj']
  ·
    exfalso
    have hfixA : ∀ y ∈ T', (conjAut 4 F A * dualAut 4 F) y = y := fun y hy => by
      rw [← hαA]
      exact hα'fix y hy
    obtain ⟨M, hMs, hT'M, hMfix, x, hxM, hxT⟩ :=
      Q3G.exists_psp_not_le hF3 A hA hT'k hU hT'p hfixA
    haveI := hMs
    refine false_of_isSimpleGroup_le (α := α) (T := T) (M := M.map e'.symm.toMonoidHom)
      ?_ ?_ (e'.symm.subgroupMap M).symm.isSimpleGroup v.2 hv1 ?_ (x := e'.symm x)
      ⟨x, hxM, rfl⟩ ?_ hsub
    · intro t ht
      exact ⟨e' t, hT'M ⟨t, ht, rfl⟩, by simp⟩
    · rintro _ ⟨m, hm, rfl⟩
      have h1 := hMfix m hm
      rw [← hαA] at h1
      apply e'.injective
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      exact h1
    · exact (even_iff_two_dvd).2 ((by norm_num : 2 ∣ 360).trans hT360)
    · intro hxT'
      apply hxT
      have h1 : e' (e'.symm x) ∈ T' := mem_map_of_mem _ hxT'
      rwa [MulEquiv.apply_symm_apply] at h1

end CFSG.ComponentClassification.GSThmB
