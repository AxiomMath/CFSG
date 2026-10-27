module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23LiftData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.HeptadCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.A7Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.A7Transport

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.Wong77
  CFSG.EvenSporadicStandard.Wong77.M23Sylow CFSG.EvenSporadicStandard.M23Std.FusionCheck
  CFSG.EvenSporadicStandard.M23Std.LiftCheck CFSG.EvenSporadicStandard.M23Std.HeptadCheck
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def bpt : Fin 7 → Fin 23 := ![2, 4, 6, 15, 16, 19, 22]

theorem bpt_injective : Function.Injective bpt := by decide

theorem bpt_val (i : Fin 7) : (bpt i).val = heptad.getD i.val 0 := by
  fin_cases i <;> rfl

theorem mem_range_bpt_iff (x : Fin 23) : x ∈ Set.range bpt ↔ x.val ∈ heptad := by
  revert x
  decide

theorem toPerm_val (g : Carrier .M23) (x : Fin 23) :
    ((toPerm g) x).val = (tab g).getD x.val 0 := (getD_tabP (toPerm g) x).symm

theorem mem_range_bpt_iff_fix {F1 : Subgroup (Carrier .M23)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (x : Fin 23) :
    x ∈ Set.range bpt ↔ ∀ f ∈ F1, (toPerm f) x = x := by
  rw [mem_range_bpt_iff, heptad_fix x.val x.2]
  constructor
  · intro h f hf
    rcases (hmem1 f).1 hf with rfl | hfm
    · simp
    · apply Fin.ext
      rw [toPerm_val]
      apply h
      rw [← tab_invs16]
      exact List.mem_map_of_mem hfm
  · intro h t ht
    rw [← tab_invs16] at ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ht
    have := congrArg Fin.val (h f ((hmem1 f).2 (Or.inr hf)))
    rwa [toPerm_val] at this

theorem preserves_heptad {F1 : Subgroup (Carrier .M23)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) {n : Carrier .M23}
    (hn : n ∈ normalizer (F1 : Set (Carrier .M23))) (x : Fin 23) :
    x ∈ Set.range bpt ↔ (toPerm n) x ∈ Set.range bpt := by
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  rw [mem_range_bpt_iff_fix hmem1, mem_range_bpt_iff_fix hmem1]
  constructor
  · intro hx f hf
    have h1 : n⁻¹ * f * n ∈ F1 := by
      have := (hn' (n⁻¹ * f * n)).1
      rw [show n * (n⁻¹ * f * n) * n⁻¹ = f by group] at this
      exact (hn' (n⁻¹ * f * n)).2 (by rw [show n * (n⁻¹ * f * n) * n⁻¹ = f by group]; exact hf)
    have h2 := hx _ h1
    simp only [map_mul, map_inv, Perm.mul_apply] at h2
    have h3 : (toPerm f) ((toPerm n) x) = (toPerm n) x := by
      have := congrArg (toPerm n) h2
      simpa using this
    exact h3
  · intro hx f hf
    have h1 : n * f * n⁻¹ ∈ F1 := (hn' f).1 hf
    have h2 := hx _ h1
    simp only [map_mul, map_inv, Perm.mul_apply] at h2
    have h3 : (toPerm f) x = x := by
      have := congrArg (fun y => ((toPerm n)⁻¹ : Perm (Fin 23)) y) h2
      simpa using this
    exact h3

section Action

variable {F1 : Subgroup (Carrier .M23)}

@[expose] noncomputable def heptadAction (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M23))) : Perm (Fin 7) :=
  (Equiv.permCongr (Equiv.ofInjective bpt bpt_injective)).symm
    ((toPerm (n : Carrier .M23)).subtypePerm
      (fun x => (preserves_heptad hmem1 n.2 x).symm))

theorem bpt_heptadAction (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M23))) (i : Fin 7) :
    bpt (heptadAction hmem1 n i) = toPerm (n : Carrier .M23) (bpt i) := by
  simp only [heptadAction, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm]
  rw [Equiv.apply_ofInjective_symm bpt_injective]
  rfl

@[expose] noncomputable def rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    normalizer (F1 : Set (Carrier .M23)) →* Perm (Fin 7) where
  toFun := heptadAction hmem1
  map_one' := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_heptadAction]
    simp
  map_mul' n m := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_heptadAction]
    simp only [Subgroup.coe_mul, map_mul, Perm.mul_apply, bpt_heptadAction]

theorem bpt_rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M23))) (i : Fin 7) :
    bpt (rhoHom hmem1 n i) = toPerm (n : Carrier .M23) (bpt i) :=
  bpt_heptadAction hmem1 n i

theorem subgroupOf_le_ker_rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    F1.subgroupOf (normalizer (F1 : Set (Carrier .M23))) ≤ (rhoHom hmem1).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun i => bpt_injective ?_
  rw [bpt_rhoHom]
  have hf : (n : Carrier .M23) ∈ F1 := hn
  have := (mem_range_bpt_iff_fix hmem1 (bpt i)).1 ⟨i, rfl⟩ _ hf
  simpa using this

end Action

section Final

variable {F1 : Subgroup (Carrier .M23)}

@[expose] def g7El : Carrier .M23 := wordElt [genA, genB, genBi] g7Word

@[expose] def g3El : Carrier .M23 := wordElt [genA, genB, genBi] g3Word

theorem tab_g7El : tab g7El = g7Tab := by
  rw [g7El, tab_wordElt, tab_letters]
  rfl

theorem tab_g3El : tab g3El = g3Tab := by
  rw [g3El, tab_wordElt, tab_letters]
  rfl

theorem g7El_mem (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    g7El ∈ normalizer (F1 : Set (Carrier .M23)) :=
  Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [tab_g7El]; exact g7_norm))

theorem g3El_mem (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    g3El ∈ normalizer (F1 : Set (Carrier .M23)) :=
  Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [tab_g3El]; exact g3_norm))

theorem rhoHom_g7_isCycle (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    (rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩).IsCycle ∧
      (rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩).support = Finset.univ := by
  have hpow : (rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩) ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨g7El, g7El_mem hmem1⟩ : normalizer (F1 : Set (Carrier .M23))) ^ 7 = 1 :=
      Subtype.ext (tab_injective (by
        rw [Subgroup.coe_pow, tab_pow, tab_g7El, g7_pow]
        rfl))
    rw [this, map_one]
  have hne : rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩ ≠ 1 := by
    intro h
    have h1 := bpt_rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩ 0
    rw [h] at h1
    have h2 := congrArg Fin.val h1
    rw [toPerm_val, tab_g7El] at h2
    simp only [Perm.one_apply, bpt_val] at h2
    exact g7_moves 0 h2.symm
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hord : orderOf (rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩) = 7 := orderOf_eq_prime hpow hne
  have hcyc : (rhoHom hmem1 ⟨g7El, g7El_mem hmem1⟩).IsCycle :=
    isCycle_of_prime_order' (by rw [hord]; exact Nat.prime_seven) (by rw [hord]; simp)
  refine ⟨hcyc, ?_⟩
  have := hcyc.orderOf
  rw [hord] at this
  exact Finset.eq_univ_of_card _ (by simp [← this])

theorem rhoHom_g3_isThreeCycle (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    (rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩).IsThreeCycle := by
  rw [← card_support_eq_three_iff]
  have : (rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩).support = Finset.univ.filter
      (fun i : Fin 7 => g3Tab.getD (heptad.getD i.val 0) 0 ≠ heptad.getD i.val 0) := by
    ext i
    simp only [Perm.mem_support, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h h2
      apply h
      apply bpt_injective
      rw [bpt_rhoHom]
      apply Fin.ext
      rw [toPerm_val, tab_g3El]
      simp only [bpt_val]
      exact h2
    · intro h h2
      apply h
      have h3 := congrArg Fin.val (bpt_rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩ i)
      rw [h2, toPerm_val, tab_g3El] at h3
      simp only [bpt_val] at h3
      exact h3.symm
  rw [this]
  exact g3_moves

theorem card_normalizer_le
    (D : NData (⊤ : Subgroup (Carrier .M23)) F1) :
    Nat.card (normalizer (F1 : Set (Carrier .M23))) ≤ 40320 := by
  have hFN : F1 ≤ normalizer (F1 : Set (Carrier .M23)) := Subgroup.le_normalizer
  let κ : normalizer (F1 : Set (Carrier .M23)) →* MulAut F1 := F1.normalizerMonoidHom
  have hker_le : (κ.ker : Set (normalizer (F1 : Set (Carrier .M23)))) ⊆
      {n | (n : Carrier .M23) ∈ F1} := by
    intro n hn
    refine D.F_self n (Subgroup.mem_top _) fun f hf => ?_
    have h1 := congrArg (fun α : MulAut F1 => ((α ⟨f, hf⟩ : F1) : Carrier .M23))
      (MonoidHom.mem_ker.1 hn)
    have h2 : (n : Carrier .M23) * f * (n : Carrier .M23)⁻¹ = f := h1
    calc (n : Carrier .M23) * f = (n : Carrier .M23) * f * (n : Carrier .M23)⁻¹ *
        (n : Carrier .M23) := by group
      _ = f * (n : Carrier .M23) := by rw [h2]
  have hker_card : Nat.card κ.ker = 16 := by
    apply le_antisymm
    · rw [← D.F_card]
      refine Nat.card_le_card_of_injective
        (fun n : κ.ker => (⟨(n.1 : Carrier .M23), hker_le n.2⟩ : F1)) ?_
      intro a b hab
      have h : ((a.1 : normalizer (F1 : Set (Carrier .M23))) : Carrier .M23) =
          ((b.1 : normalizer (F1 : Set (Carrier .M23))) : Carrier .M23) :=
        congrArg (fun y : F1 => (y : Carrier .M23)) hab
      exact Subtype.ext (Subtype.ext h)
    · have hsub : F1.subgroupOf (normalizer (F1 : Set (Carrier .M23))) ≤ κ.ker := by
        intro n hn
        rw [MonoidHom.mem_ker]
        refine MulEquiv.ext fun f => Subtype.ext ?_
        have hn' : (n : Carrier .M23) ∈ F1 := hn
        show (n : Carrier .M23) * f * (n : Carrier .M23)⁻¹ = f
        rw [D.F_comm _ hn' _ f.2]
        group
      have := Subgroup.card_le_of_le hsub
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, D.F_card] at this
  have hrange : Nat.card κ.range ∣ 20160 := by
    rw [← card_mulEquiv_eq_of_elemAb16 (F := F1)
      (fun x y => Subtype.ext (D.F_comm x x.2 y y.2)) (fun x => Subtype.ext (D.F_sq x x.2))
      D.F_card]
    exact Subgroup.card_subgroup_dvd_card κ.range
  have hprod := Subgroup.card_ker_mul_card_range κ
  rw [hker_card] at hprod
  have hM : Nat.card (Carrier .M23) = 10200960 := CFSG.Sporadic.Schreier.m23_card
  have hNdvd : Nat.card (normalizer (F1 : Set (Carrier .M23))) ∣ 10200960 :=
    hM ▸ Subgroup.card_subgroup_dvd_card (normalizer (F1 : Set (Carrier .M23)))
  rw [← hprod] at hNdvd
  have h637 : Nat.card κ.range ∣ 637560 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 16) (by simpa using hNdvd)
  have h2520 : Nat.card κ.range ∣ 2520 := by
    have := Nat.dvd_gcd hrange h637
    simpa using this
  have := Nat.le_of_dvd (by norm_num) h2520
  omega

theorem normalizer_quotient_pinned
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (D : NData (⊤ : Subgroup (Carrier .M23)) F1) :
    Nonempty (↥(normalizer (F1 : Set (Carrier .M23))) ⧸
      F1.subgroupOf (normalizer (F1 : Set (Carrier .M23))) ≃* alternatingGroup (Fin 7)) := by
  have hFN : F1 ≤ normalizer (F1 : Set (Carrier .M23)) := Subgroup.le_normalizer
  have : (F1.subgroupOf (normalizer (F1 : Set (Carrier .M23)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).2 le_rfl
  refine quotient_equiv_alternatingGroup (by simp) (rhoHom hmem1) _
    (subgroupOf_le_ker_rhoHom hmem1) ?_ (card_normalizer_le D)
    (rhoHom_g7_isCycle hmem1).1 (rhoHom_g7_isCycle hmem1).2 (rhoHom_g3_isThreeCycle hmem1)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, D.F_card]

theorem normQuotA7_pinned
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (D : NData (⊤ : Subgroup (Carrier .M23)) F1) :
    NormQuotA7 (normalizer (F1 : Set (Carrier .M23))) F1 := by
  obtain ⟨e⟩ := normalizer_quotient_pinned hmem1 D
  have hFN : F1 ≤ normalizer (F1 : Set (Carrier .M23)) := Subgroup.le_normalizer
  have : (F1.subgroupOf (normalizer (F1 : Set (Carrier .M23)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).2 le_rfl
  exact NormQuotA7.of_equiv e

end Final

end CFSG.EvenSporadicStandard.M23Std
