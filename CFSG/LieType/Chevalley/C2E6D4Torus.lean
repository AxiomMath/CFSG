module

public import CFSG.LieType.Chevalley.C2E6D4Model
public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

theorem single_weight_jD : ∀ (k : Fin 4) (m : ZMod 3) (l : Fin Tag.E6.rank),
    (3 : ℤ) ∣ (∑ t : Fin 1, (((![m] : Fin 1 → ZMod 3) t).val : ℤ) *
        Tag.E6.cartan ((![jD k] : Fin 1 → Fin Tag.E6.rank) t) l) -
      ∑ s, (((Pi.single k m : Fin 4 → ZMod 3) s).val : ℤ) * Tag.E6.cartan (jD s) l := by
  decide +kernel

theorem torusElt_jD_eq_torusWord
    (k : Fin 4) (m : ZMod 3) :
    torusElt Tag.E6 K (jD k) (omegaUnit ^ m.val) = torusWord jD (Pi.single k m) := by
  rw [← torusWord_one, torusWord_eq_torusWord_iff]
  exact single_weight_jD k m

@[expose] def torusHomD
    : Multiplicative (Fin 4 → ZMod 3) →* ModGL Tag.E6 K where
  toFun c := torusWord jD c.toAdd
  map_one' := torusWord_zero jD
  map_mul' c d := torusWord_add jD c.toAdd d.toAdd

theorem torusD_eq_range
    : torusD = torusHomD.range := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, s, rfl⟩
    obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    obtain ⟨m, rfl⟩ := exists_omegaUnit_pow_eq s
    exact ⟨Multiplicative.ofAdd (Pi.single k m), (torusElt_jD_eq_torusWord k m).symm⟩
  · rintro _ ⟨c, rfl⟩
    exact torusWordD_mem c.toAdd

theorem mem_torusD_iff
    {h : ModGL Tag.E6 K} :
    h ∈ torusD ↔ ∃ c : Fin 4 → ZMod 3, h = torusWord jD c := by
  rw [torusD_eq_range]
  exact ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem torusD_le_groupD
    : torusD ≤ groupD :=
  subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := setD)

theorem torusWord_mem_groupD
    (c : Fin 4 → ZMod 3) : torusWord jD c ∈ groupD :=
  torusD_le_groupD (torusWordD_mem c)

@[expose] def natTorusChar (c : Fin 4 → ZMod 3) : Fin 4 → Kˣ :=
  fun i => omegaUnit ^ ∑ t, ((c t).val : ℤ) * natWeight (.inl i) t

theorem elim_natTorusChar (c : Fin 4 → ZMod 3) (s : Fin 4 ⊕ Fin 4) :
    (Sum.elim (natTorusChar c) (natTorusChar c)⁻¹ s : Kˣ) =
      omegaUnit ^ ∑ t, ((c t).val : ℤ) * natWeight s t := by
  rcases s with i | i
  · rfl
  · change (natTorusChar c i)⁻¹ = _
    rw [natTorusChar, ← zpow_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_neg]
    rfl

theorem torusElt_single
    (a : Fin 4 → Kˣ) (s : Fin 4 ⊕ Fin 4) :
    torusElt 4 K a (Pi.single s 1) = ((Sum.elim a a⁻¹ s : Kˣ) : K) • Pi.single s 1 := by
  funext s'
  rw [OrthogonalSplit.torusElt_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : s' = s
  · subst h
    rfl
  · rw [Pi.single_eq_of_ne h, mul_zero, mul_zero]

theorem psiD_torusWord
    (c : Fin 4 → ZMod 3) :
    psiD ⟨torusWord jD c, torusWord_mem_groupD c⟩ = torusElt 4 K (natTorusChar c) := by
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun K (Fin 4 ⊕ Fin 4)).ext fun s => ?_)
  obtain ⟨j, rfl⟩ := exists_natD_eq s
  rw [Pi.basisFun_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← phiD_vecD j, psiD_phiD,
    phiD_vecD, torusElt_single, elim_natTorusChar]
  have h : (⟨((torusWord jD c : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (vecD j),
      mem_moduleD_of_mem_groupD (torusWord_mem_groupD c) _ (vecD_mem j)⟩ : moduleD) =
      ((omegaUnit ^ ∑ t, ((c t).val : ℤ) * natWeight (natD j) t : Kˣ) : K) •
        ⟨vecD j, vecD_mem j⟩ := by
    apply Subtype.ext
    rw [SetLike.val_smul]
    change (torusWord jD c : Module.End K (RootModule Tag.E6 K)) (vecD j) = _
    rw [torusWord_rootVec jD c (isRoot_rootD j)]
    simp only [weight_rootD]
  rw [h, map_smul, phiD_vecD]

@[expose] def natTorusPreimage (m : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  ![m 0, m 0 + m 1, 2 * (m 0 + m 1 + m 2) + m 3, 2 * (m 0 + m 1 + m 2 + m 3)]

theorem natTorusPreimage_spec : ∀ (m : Fin 4 → ZMod 3) (i : Fin 4),
    (3 : ℤ) ∣ (∑ t, ((natTorusPreimage m t).val : ℤ) * natWeight (.inl i) t) - (m i).val := by
  decide +kernel

theorem natTorusChar_surjective : Function.Surjective natTorusChar := by
  intro a
  choose m hm using fun i => exists_omegaUnit_pow_eq (a i)
  refine ⟨natTorusPreimage m, funext fun i => ?_⟩
  rw [← hm i, natTorusChar, ← zpow_natCast, ← mul_inv_eq_one, ← zpow_sub]
  exact (omegaUnit_zpow_eq_one_iff _).mpr (natTorusPreimage_spec m i)

theorem map_psiD_torusD
    : (torusD.subgroupOf groupD).map psiD = (torusElt 4 K).range := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := mem_torusD_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have e : x = ⟨torusWord jD c, torusWord_mem_groupD c⟩ := Subtype.ext hc
    rw [e, psiD_torusWord]
    exact ⟨_, rfl⟩
  · rintro _ ⟨a, rfl⟩
    obtain ⟨c, rfl⟩ := natTorusChar_surjective a
    exact ⟨⟨torusWord jD c, torusWord_mem_groupD c⟩, torusWordD_mem c, psiD_torusWord c⟩

theorem eq_one_of_mem_torusD
    {x : groupD} (hx : x ∈ torusD.subgroupOf groupD)
    (h : psiD x = 1) : x = 1 := by
  obtain ⟨c, hc⟩ := mem_torusD_iff.mp (Subgroup.mem_subgroupOf.mp hx)
  have hfix := (psiD_eq_one_iff x).mp h
  rw [hc] at hfix
  refine Subtype.ext ?_
  rw [hc]
  exact (fix_moduleD_iff c).mp hfix

theorem psiD_injOn_torusD
    : Set.InjOn psiD (torusD.subgroupOf groupD) := by
  intro x hx y hy hxy
  have h1 : psiD (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 := eq_one_of_mem_torusD (mul_mem (inv_mem hx) hy) h1
  rwa [inv_mul_eq_one] at h2

end CFSG.LieType.Chevalley.C2E6Std
