module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22LiftData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HexadCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.A6Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.XbarGen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.M22Centralizer

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.M22Std.TabCheck
  CFSG.EvenSporadicStandard.M22Std.FusionCheck CFSG.EvenSporadicStandard.M22Std.LiftCheck
  CFSG.EvenSporadicStandard.M22Std.HexadCheck CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.M23Std (NData)

@[expose] def bpt : Fin 6 → Fin 22 := ![1, 2, 6, 11, 13, 16]

theorem bpt_injective : Function.Injective bpt := by decide

theorem bpt_val (i : Fin 6) : (bpt i).val = hexad.getD i.val 0 := by
  fin_cases i <;> rfl

theorem mem_range_bpt_iff (x : Fin 22) : x ∈ Set.range bpt ↔ x.val ∈ hexad := by
  revert x
  decide

theorem toPerm_val (g : Carrier .M22) (x : Fin 22) :
    ((toPerm g) x).val = (tab g).getD x.val 0 := (getD_tabP (toPerm g) x).symm

theorem mem_range_bpt_iff_fix {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (x : Fin 22) :
    x ∈ Set.range bpt ↔ ∀ f ∈ F1, (toPerm f) x = x := by
  rw [mem_range_bpt_iff, hexad_fix x.val x.2]
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

theorem preserves_hexad {F1 : Subgroup (Carrier .M22)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) {n : Carrier .M22}
    (hn : n ∈ normalizer (F1 : Set (Carrier .M22))) (x : Fin 22) :
    x ∈ Set.range bpt ↔ (toPerm n) x ∈ Set.range bpt := by
  have hn' := Subgroup.mem_normalizer_iff.1 hn
  rw [mem_range_bpt_iff_fix hmem1, mem_range_bpt_iff_fix hmem1]
  constructor
  · intro hx f hf
    have h1 : n⁻¹ * f * n ∈ F1 := by
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
      have := congrArg (fun y => ((toPerm n)⁻¹ : Perm (Fin 22)) y) h2
      simpa using this
    exact h3

section Action

variable {F1 : Subgroup (Carrier .M22)}

@[expose] noncomputable def hexadAction (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M22))) : Perm (Fin 6) :=
  (Equiv.permCongr (Equiv.ofInjective bpt bpt_injective)).symm
    ((toPerm (n : Carrier .M22)).subtypePerm
      (fun x => (preserves_hexad hmem1 n.2 x).symm))

theorem bpt_hexadAction (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M22))) (i : Fin 6) :
    bpt (hexadAction hmem1 n i) = toPerm (n : Carrier .M22) (bpt i) := by
  simp only [hexadAction, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm]
  rw [Equiv.apply_ofInjective_symm bpt_injective]
  rfl

@[expose] noncomputable def rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    normalizer (F1 : Set (Carrier .M22)) →* Perm (Fin 6) where
  toFun := hexadAction hmem1
  map_one' := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_hexadAction]
    simp
  map_mul' n m := by
    refine Equiv.ext fun i => bpt_injective ?_
    rw [bpt_hexadAction]
    simp only [Subgroup.coe_mul, map_mul, Perm.mul_apply, bpt_hexadAction]

theorem bpt_rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (n : normalizer (F1 : Set (Carrier .M22))) (i : Fin 6) :
    bpt (rhoHom hmem1 n i) = toPerm (n : Carrier .M22) (bpt i) :=
  bpt_hexadAction hmem1 n i

theorem subgroupOf_le_ker_rhoHom (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    F1.subgroupOf (normalizer (F1 : Set (Carrier .M22))) ≤ (rhoHom hmem1).ker := by
  intro n hn
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun i => bpt_injective ?_
  rw [bpt_rhoHom]
  have hf : (n : Carrier .M22) ∈ F1 := hn
  have := (mem_range_bpt_iff_fix hmem1 (bpt i)).1 ⟨i, rfl⟩ _ hf
  simpa using this

end Action

section Final

variable {F1 : Subgroup (Carrier .M22)}

@[expose] def g5El : Carrier .M22 := wordElt [genA, genB, genBi] g5Word

@[expose] def g3El : Carrier .M22 := wordElt [genA, genB, genBi] g3Word

theorem tab_g5El : tab g5El = g5Tab := by
  rw [g5El, tab_wordElt, tab_letters]
  rfl

theorem tab_g3El : tab g3El = g3Tab := by
  rw [g3El, tab_wordElt, tab_letters]
  rfl

theorem g5El_mem (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    g5El ∈ normalizer (F1 : Set (Carrier .M22)) :=
  Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [tab_g5El]; exact g5_norm))

theorem g3El_mem (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    g3El ∈ normalizer (F1 : Set (Carrier .M22)) :=
  Subgroup.mem_normalizer_iff.2 (normalizes_of_normOK hmem1 (by rw [tab_g3El]; exact g3_norm))

theorem rhoHom_g5_isCycle (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    (rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩).IsCycle := by
  have hpow : (rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩) ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨g5El, g5El_mem hmem1⟩ : normalizer (F1 : Set (Carrier .M22))) ^ 5 = 1 :=
      Subtype.ext (tab_injective (by
        rw [Subgroup.coe_pow, tab_pow, tab_g5El, g5_pow]
        rfl))
    rw [this, map_one]
  have hne : rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩ ≠ 1 := by
    intro h
    have h1 := bpt_rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩ 0
    rw [h] at h1
    have h2 := congrArg Fin.val h1
    rw [toPerm_val, tab_g5El] at h2
    simp only [Perm.one_apply, bpt_val] at h2
    exact g5_moves 0 (by decide) h2.symm
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hord : orderOf (rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩) = 5 := orderOf_eq_prime hpow hne
  exact isCycle_of_prime_order' (by rw [hord]; exact Nat.prime_five)
    (by rw [hord]; simp)

theorem rhoHom_g5_fix (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩ 4 = 4 := by
  apply bpt_injective
  rw [bpt_rhoHom]
  apply Fin.ext
  rw [toPerm_val, tab_g5El]
  simp only [bpt_val]
  exact g5_fix

theorem rhoHom_g5_moves (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    ∀ x : Fin 6, x ≠ 4 → rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩ x ≠ x := by
  intro x hx h
  have h1 := congrArg Fin.val (bpt_rhoHom hmem1 ⟨g5El, g5El_mem hmem1⟩ x)
  rw [h, toPerm_val, tab_g5El] at h1
  simp only [bpt_val] at h1
  exact g5_moves x hx h1.symm

theorem rhoHom_g3_moves (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩ 4 ≠ 4 := by
  intro h
  have h1 := congrArg Fin.val (bpt_rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩ 4)
  rw [h, toPerm_val, tab_g3El] at h1
  simp only [bpt_val] at h1
  exact g3_moves_p h1.symm

theorem rhoHom_g3_isThreeCycle (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    (rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩).IsThreeCycle := by
  rw [← card_support_eq_three_iff]
  have : (rhoHom hmem1 ⟨g3El, g3El_mem hmem1⟩).support = Finset.univ.filter
      (fun i : Fin 6 => g3Tab.getD (hexad.getD i.val 0) 0 ≠ hexad.getD i.val 0) := by
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

theorem tEl_mem {E : Subgroup (Carrier .M22)}
    (hE : ∀ x, x ∈ E ↔ x = 1 ∨ x ∈ invs16 1) : tEl ∈ E := by
  obtain ⟨-, -, hN, -⟩ := fusionCheck_spec
  have h1 := (hN 1).2.1
  rw [← tab_invs16] at h1
  obtain ⟨x, hx, hxt⟩ := List.mem_map.1 h1
  have : x = tEl := tab_injective (by rw [hxt, tab_tEl])
  rw [hE tEl]
  exact Or.inr (this ▸ hx)

theorem card_normalizer_le
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1)
    (D : NData (⊤ : Subgroup (Carrier .M22)) F1) :
    Nat.card (normalizer (F1 : Set (Carrier .M22))) ≤ 5760 := by
  set N : Subgroup (Carrier .M22) := normalizer (F1 : Set (Carrier .M22)) with hN
  let _ : MulAction N (Carrier .M22) :=
    MulAction.compHom (Carrier .M22) ((MulAut.conj : Carrier .M22 →* MulAut (Carrier .M22)).comp
      N.subtype)
  have hsmul : ∀ (c : N) (x : Carrier .M22),
      c • x = (c : Carrier .M22) * x * (c : Carrier .M22)⁻¹ := fun c x => rfl
  have htF : tEl ∈ F1 := tEl_mem hmem1
  obtain ⟨hsq, ht1⟩ := tEl_involution
  have ht2 : orderOf tEl = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) ht1
  have horb : Nat.card (MulAction.orbit N tEl) ≤ 15 := by
    have hsub : (MulAction.orbit N tEl : Set (Carrier .M22)) ⊆
        (F1 : Set (Carrier .M22)) \ {1} := by
      rintro _ ⟨c, rfl⟩
      refine ⟨?_, ?_⟩
      · show c • tEl ∈ F1
        rw [hsmul]
        exact (Subgroup.mem_normalizer_iff.1 c.2 tEl).1 htF
      · intro h1
        have h2 : c • tEl = 1 := h1
        rw [hsmul] at h2
        exact ht1 (conj_eq_one_iff.1 h2)
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_sdiff_singleton_of_mem F1.one_mem] at h1
    have hF : (F1 : Set (Carrier .M22)).ncard = 16 := by
      rw [← Nat.card_coe_set_eq]
      exact D.F_card
    rw [hF, ← Nat.card_coe_set_eq] at h1
    omega
  have hstab : Nat.card (MulAction.stabilizer N tEl) ≤ 384 := by
    rw [← card_centralizer_involution ht2]
    have hmemC : ∀ c : MulAction.stabilizer N tEl,
        (c.1 : Carrier .M22) ∈ Subgroup.centralizer ({tEl} : Set (Carrier .M22)) := by
      intro c
      have hc : c.1 • tEl = tEl := c.2
      rw [hsmul] at hc
      have h3 : (c.1 : Carrier .M22) * tEl = tEl * (c.1 : Carrier .M22) :=
        mul_inv_eq_iff_eq_mul.1 hc
      exact Subgroup.mem_centralizer_singleton_iff.2 h3
    refine Nat.card_le_card_of_injective
      (fun c => (⟨(c.1 : Carrier .M22), hmemC c⟩ :
        Subgroup.centralizer ({tEl} : Set (Carrier .M22)))) ?_
    intro a b hab
    have h : ((a.1 : N) : Carrier .M22) = ((b.1 : N) : Carrier .M22) :=
      congrArg (fun y : Subgroup.centralizer ({tEl} : Set (Carrier .M22)) =>
        (y : Carrier .M22)) hab
    exact Subtype.ext (Subtype.ext h)
  have hkey := Subgroup.card_mul_index (MulAction.stabilizer N tEl)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at hkey
  calc Nat.card N = Nat.card (MulAction.stabilizer N tEl) * Nat.card (MulAction.orbit N tEl) :=
        hkey.symm
    _ ≤ 384 * 15 := Nat.mul_le_mul hstab horb
    _ = 5760 := by norm_num

theorem normQuot_pinned
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) (D : NData (⊤ : Subgroup (Carrier .M22)) F1) :
    NormQuot (alternatingGroup (Fin 6)) (normalizer (F1 : Set (Carrier .M22))) F1 := by
  have hFN : F1 ≤ normalizer (F1 : Set (Carrier .M22)) := Subgroup.le_normalizer
  have : (F1.subgroupOf (normalizer (F1 : Set (Carrier .M22)))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFN).2 le_rfl
  obtain ⟨e⟩ : Nonempty (↥(normalizer (F1 : Set (Carrier .M22))) ⧸
      F1.subgroupOf (normalizer (F1 : Set (Carrier .M22))) ≃* alternatingGroup (Fin 6)) := by
    refine quotient_equiv_alternatingGroup_six (by simp) (rhoHom hmem1) _
      (subgroupOf_le_ker_rhoHom hmem1) ?_ (card_normalizer_le hmem1 D)
      (rhoHom_g5_isCycle hmem1) (rhoHom_g5_fix hmem1) (rhoHom_g5_moves hmem1)
      (rhoHom_g3_isThreeCycle hmem1) (rhoHom_g3_moves hmem1)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv, D.F_card]
  exact NormQuot.of_equiv e

end Final

end CFSG.EvenSporadicStandard.M22Std
