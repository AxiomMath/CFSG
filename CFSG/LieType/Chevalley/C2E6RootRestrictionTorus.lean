module

public import CFSG.LieType.Chevalley.C2E6RootRestrictionD
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def omegaUnit : Kˣ := Units.mk0 ω (by decide)

theorem omegaUnit_pow_three : omegaUnit ^ 3 = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, omegaUnit, Units.val_mk0]
  decide

theorem orderOf_omegaUnit : orderOf omegaUnit = 3 := by
  refine orderOf_eq_prime omegaUnit_pow_three fun h => ?_
  have := congrArg Units.val h
  rw [omegaUnit, Units.val_mk0, Units.val_one] at this
  exact absurd this (by decide)

theorem omegaUnit_zpow_eq_one_iff (m : ℤ) : omegaUnit ^ m = 1 ↔ (3 : ℤ) ∣ m := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_omegaUnit]
  rfl

@[expose] def torusWord
    {n : ℕ} (X : Fin n → Fin Tag.E6.rank) (c : Fin n → ZMod 3) :
    ModGL Tag.E6 K :=
  (List.ofFn fun t => torusElt Tag.E6 K (X t) (omegaUnit ^ (c t).val)).prod

@[expose] def torusChar {n : ℕ} (X : Fin n → Fin Tag.E6.rank) (c : Fin n → ZMod 3) :
    Fin Tag.E6.rank → Kˣ :=
  fun l => omegaUnit ^ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (X t) l

variable {n : ℕ} (X : Fin n → Fin Tag.E6.rank)

theorem torusWord_eq_rootDiagUnit
    (c : Fin n → ZMod 3) :
    torusWord X c = rootDiagUnit Tag.E6 (torusChar X c) := by
  have h : (List.ofFn fun t => torusElt Tag.E6 K (X t) (omegaUnit ^ (c t).val)) =
      List.ofFn (rootDiagUnitHom Tag.E6 K ∘
        fun t l => (omegaUnit ^ (c t).val) ^ Tag.E6.cartan (X t) l) := by
    congr 1
    funext t
    exact torusElt_eq_rootDiagUnit _ _
  rw [torusWord, h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  change rootDiagUnit Tag.E6 _ = _
  congr 1
  funext l
  rw [Finset.prod_apply, torusChar, ← Finset.prod_zpow_eq_zpow_sum]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [zpow_mul, zpow_natCast]

theorem torusWord_eq_one_iff
    (c : Fin n → ZMod 3) :
    torusWord X c = 1 ↔ ∀ l, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (X t) l := by
  rw [torusWord_eq_rootDiagUnit]
  constructor
  · intro h l
    have h1 := rootDiagUnit_injective (h.trans rootDiagUnit_one.symm)
    rw [← omegaUnit_zpow_eq_one_iff]
    exact congrFun h1 l
  · intro h
    rw [← rootDiagUnit_one]
    congr 1
    funext l
    exact (omegaUnit_zpow_eq_one_iff _).mpr (h l)

theorem torusWord_rootVec
    (c : Fin n → ZMod 3) {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot Tag.E6 α) :
    (torusWord X c : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) =
      ((omegaUnit ^ ∑ t, ((c t).val : ℤ) * rootWeight (X t) α : Kˣ) : K) •
        rootVec Tag.E6 K α := by
  rw [torusWord_eq_rootDiagUnit]
  change rootDiag _ _ = _
  rw [rootDiag_rootVec _ hα, rootChar]
  congr 3
  simp only [torusChar, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  simp only [rootWeight, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun l _ => by ring

theorem torusWord_hVec
    (c : Fin n → ZMod 3) (i : Fin Tag.E6.rank) :
    (torusWord X c : Module.End K (RootModule Tag.E6 K)) (hVec Tag.E6 K i) = hVec Tag.E6 K i := by
  rw [torusWord_eq_rootDiagUnit]
  exact rootDiag_hVec _ i

theorem torusWord_add
    (c d : Fin n → ZMod 3) :
    torusWord X (c + d) = torusWord X c * torusWord X d := by
  rw [torusWord_eq_rootDiagUnit, torusWord_eq_rootDiagUnit, torusWord_eq_rootDiagUnit,
    ← rootDiagUnit_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, torusChar, torusChar, torusChar, ← zpow_add, zpow_eq_zpow_iff_modEq,
    orderOf_omegaUnit, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  simp only [ZMod.natCast_zmod_val, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem torusWord_zero
    : torusWord X 0 = 1 :=
  (torusWord_eq_one_iff X 0).mpr fun l => by simp

theorem torusWord_mem_subsystemTorus
    {S : Set (Fin Tag.E6.rank)} (hX : ∀ t, X t ∈ S)
    (c : Fin n → ZMod 3) : torusWord X c ∈ subsystemTorus Tag.E6 K S := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).mp hg
  exact Subgroup.subset_closure ⟨X t, hX t, _, rfl⟩

theorem fix_span_iff
    {m : ℕ} (β : Fin m → Fin Tag.E6.rank → ℤ) (hβ : ∀ j, IsRoot Tag.E6 (β j))
    (c : Fin n → ZMod 3) :
    (∀ v ∈ Submodule.span K (Set.range fun j => rootVec Tag.E6 K (β j)),
        (torusWord X c : Module.End K (RootModule Tag.E6 K)) v = v) ↔
      ∀ j, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * rootWeight (X t) (β j) := by
  constructor
  · intro h j
    have hv := h _ (Submodule.subset_span ⟨j, rfl⟩)
    rw [torusWord_rootVec X c (hβ j)] at hv
    have hne : rootVec Tag.E6 K (β j) ≠ 0 := by
      rw [rootVec_eq_single (hβ j)]
      exact Finsupp.single_ne_zero.2 one_ne_zero
    have h1 : ((omegaUnit ^ ∑ t, ((c t).val : ℤ) * rootWeight (X t) (β j) : Kˣ) : K) = 1 :=
      smul_left_injective K hne (hv.trans (one_smul K _).symm)
    rw [← omegaUnit_zpow_eq_one_iff]
    exact Units.ext h1
  · intro h v hv
    have hEq : Set.EqOn ⇑(torusWord X c : Module.End K (RootModule Tag.E6 K))
        ⇑(LinearMap.id : Module.End K (RootModule Tag.E6 K))
        (Set.range fun j => rootVec Tag.E6 K (β j)) := by
      rintro _ ⟨j, rfl⟩
      rw [torusWord_rootVec X c (hβ j), (omegaUnit_zpow_eq_one_iff _).mpr (h j), Units.val_one,
        one_smul, LinearMap.id_apply]
    exact LinearMap.eqOn_span hEq hv

theorem kerA_iff : ∀ c : Fin 5 → ZMod 3,
    (∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (jA t) l) ↔
      c = 0 ∨ c = ![1, 2, 0, 1, 2] ∨ c = ![2, 1, 0, 2, 1] := by
  decide +kernel

theorem kerA_restrict_iff : ∀ c : Fin 5 → ZMod 3,
    (∀ j : Fin 20, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * subsetPattern (subsetA j) t) ↔
      ∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (jA t) l := by
  decide +kernel

theorem kerD_iff : ∀ c : Fin 4 → ZMod 3,
    (∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (jD t) l) ↔ c = 0 := by
  decide +kernel

theorem kerD_restrict_iff : ∀ c : Fin 4 → ZMod 3,
    (∀ j : Fin 8, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * natWeight (natD j) t) ↔
      ∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (jD t) l := by
  decide +kernel

theorem ker6_iff : ∀ c : Fin 6 → ZMod 3,
    (∀ l : Fin Tag.E6.rank, (3 : ℤ) ∣ ∑ t, ((c t).val : ℤ) * Tag.E6.cartan (i6 t) l) ↔
      c = 0 ∨ c = ![1, 0, 2, 0, 1, 2] ∨ c = ![2, 0, 1, 0, 2, 1] := by
  decide +kernel

theorem torusWordA_eq_one_iff
    (c : Fin 5 → ZMod 3) :
    torusWord jA c = 1 ↔ c = 0 ∨ c = ![1, 2, 0, 1, 2] ∨ c = ![2, 1, 0, 2, 1] := by
  rw [torusWord_eq_one_iff]
  exact kerA_iff c

theorem torusWordA_mem
    (c : Fin 5 → ZMod 3) : torusWord jA c ∈ torusA :=
  torusWord_mem_subsystemTorus jA (fun t => by
    fin_cases t
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)),
      Or.inr (Or.inr (Or.inr (Or.inl rfl))), Or.inr (Or.inr (Or.inr (Or.inr rfl)))]) c

theorem fix_moduleA_iff
    (c : Fin 5 → ZMod 3) :
    (∀ v ∈ moduleA, (torusWord jA c : Module.End K (RootModule Tag.E6 K)) v = v) ↔
      torusWord jA c = 1 := by
  rw [moduleA_eq_span, torusWord_eq_one_iff, ← kerA_restrict_iff c]
  refine (fix_span_iff jA rootA isRoot_rootA c).trans ?_
  simp only [weight_rootA]

theorem torusWordD_eq_one_iff
    (c : Fin 4 → ZMod 3) : torusWord jD c = 1 ↔ c = 0 := by
  rw [torusWord_eq_one_iff]
  exact kerD_iff c

theorem torusWordD_mem
    (c : Fin 4 → ZMod 3) : torusWord jD c ∈ torusD :=
  torusWord_mem_subsystemTorus jD (fun t => by
    fin_cases t
    exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl),
      Or.inr (Or.inr (Or.inr rfl))]) c

theorem fix_moduleD_iff
    (c : Fin 4 → ZMod 3) :
    (∀ v ∈ moduleD, (torusWord jD c : Module.End K (RootModule Tag.E6 K)) v = v) ↔
      torusWord jD c = 1 := by
  rw [moduleD_eq_span, torusWord_eq_one_iff, ← kerD_restrict_iff c]
  refine (fix_span_iff jD rootD isRoot_rootD c).trans ?_
  simp only [weight_rootD]

theorem torusWord6_eq_one_iff
    (c : Fin 6 → ZMod 3) :
    torusWord i6 c = 1 ↔ c = 0 ∨ c = ![1, 0, 2, 0, 1, 2] ∨ c = ![2, 0, 1, 0, 2, 1] := by
  rw [torusWord_eq_one_iff]
  exact ker6_iff c

@[expose] def posFixedRoots (J : Set (Fin Tag.E6.rank)) : Set (Fin Tag.E6.rank → ℤ) :=
  {α ∈ parabolicPosRoots Tag.E6 J | rhoL α = α}

@[expose] def posPairedOrbits (J : Set (Fin Tag.E6.rank)) :
    Set (Finset (Fin Tag.E6.rank → ℤ)) :=
  {O | ∃ α ∈ parabolicPosRoots Tag.E6 J, rhoL α ≠ α ∧ O = {α, rhoL α}}

section Counts

variable {J : Set (Fin Tag.E6.rank)} (P : (Fin Tag.E6.rank → ℤ) → Prop) [DecidablePred P]

theorem posFixedRoots_eq
    (hP : ∀ α, IsRoot Tag.E6 α → (α ∈ parabolicPosRoots Tag.E6 J ↔ P α)) :
    posFixedRoots J = ↑((Finset.univ.filter fun k : Fin 72 =>
      P (e6Root k) ∧ rhoL (e6Root k) = e6Root k).image e6Root) := by
  ext α
  rw [Finset.coe_image, Finset.coe_filter]
  constructor
  · rintro ⟨hα, hρ⟩
    have hr : IsRoot Tag.E6 α := hα.1.1
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hr
    exact ⟨k, ⟨Finset.mem_univ k, (hP _ hr).mp hα, hρ⟩, rfl⟩
  · rintro ⟨k, ⟨-, hk, hρ⟩, rfl⟩
    exact ⟨(hP _ (isRoot_e6Root k)).mpr hk, hρ⟩

theorem posPairedOrbits_eq
    (hP : ∀ α, IsRoot Tag.E6 α → (α ∈ parabolicPosRoots Tag.E6 J ↔ P α)) :
    posPairedOrbits J = ↑((Finset.univ.filter fun k : Fin 72 =>
      P (e6Root k) ∧ rhoL (e6Root k) ≠ e6Root k).image
        fun k => ({e6Root k, rhoL (e6Root k)} : Finset (Fin Tag.E6.rank → ℤ))) := by
  ext O
  rw [Finset.coe_image, Finset.coe_filter]
  constructor
  · rintro ⟨α, hα, hρ, rfl⟩
    have hr : IsRoot Tag.E6 α := hα.1.1
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hr
    exact ⟨k, ⟨Finset.mem_univ k, (hP _ hr).mp hα, hρ⟩, rfl⟩
  · rintro ⟨k, ⟨-, hk, hρ⟩, rfl⟩
    exact ⟨e6Root k, (hP _ (isRoot_e6Root k)).mpr hk, hρ, rfl⟩

end Counts

theorem mem_parabolicPosRoots_univ {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    α ∈ parabolicPosRoots Tag.E6 Set.univ ↔ 0 < height α :=
  ⟨fun h => h.2.2, fun h => ⟨⟨hα, fun i hi => absurd (Set.mem_univ i) hi⟩, hα, h⟩⟩

theorem not_mem_setA_iff (i : Fin Tag.E6.rank) : i ∉ setA ↔ i = i6 1 := by
  have h : ∀ i : Fin 6, ¬(i = 0 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) ↔ i = 1 := by decide
  exact h i

theorem not_mem_setD_iff (i : Fin Tag.E6.rank) : i ∉ setD ↔ i = i6 0 ∨ i = i6 5 := by
  have h : ∀ i : Fin 6, ¬(i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) ↔ i = 0 ∨ i = 5 := by decide
  exact h i

theorem mem_parabolicPosRoots_setA {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    α ∈ parabolicPosRoots Tag.E6 setA ↔ α (i6 1) = 0 ∧ 0 < height α := by
  constructor
  · rintro ⟨⟨-, h0⟩, -, h⟩
    exact ⟨h0 _ ((not_mem_setA_iff _).mpr rfl), h⟩
  · rintro ⟨h0, h⟩
    refine ⟨⟨hα, fun i hi => ?_⟩, hα, h⟩
    rw [(not_mem_setA_iff i).mp hi]
    exact h0

theorem mem_parabolicPosRoots_setD {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    α ∈ parabolicPosRoots Tag.E6 setD ↔ (α (i6 0) = 0 ∧ α (i6 5) = 0) ∧ 0 < height α := by
  constructor
  · rintro ⟨⟨-, h0⟩, -, h⟩
    exact ⟨⟨h0 _ ((not_mem_setD_iff _).mpr (Or.inl rfl)),
      h0 _ ((not_mem_setD_iff _).mpr (Or.inr rfl))⟩, h⟩
  · rintro ⟨⟨h0, h5⟩, h⟩
    refine ⟨⟨hα, fun i hi => ?_⟩, hα, h⟩
    rcases (not_mem_setD_iff i).mp hi with rfl | rfl
    exacts [h0, h5]

theorem card_fixed_univ : ((Finset.univ.filter fun k : Fin 72 =>
    0 < height (e6Root k) ∧ rhoL (e6Root k) = e6Root k).image e6Root).card = 12 := by
  decide +kernel

theorem card_paired_univ : ((Finset.univ.filter fun k : Fin 72 =>
    0 < height (e6Root k) ∧ rhoL (e6Root k) ≠ e6Root k).image
      fun k => ({e6Root k, rhoL (e6Root k)} : Finset (Fin Tag.E6.rank → ℤ))).card = 12 := by
  decide +kernel

theorem card_fixed_setA : ((Finset.univ.filter fun k : Fin 72 =>
    (e6Root k (i6 1) = 0 ∧ 0 < height (e6Root k)) ∧ rhoL (e6Root k) = e6Root k).image
      e6Root).card = 3 := by
  decide +kernel

theorem card_paired_setA : ((Finset.univ.filter fun k : Fin 72 =>
    (e6Root k (i6 1) = 0 ∧ 0 < height (e6Root k)) ∧ rhoL (e6Root k) ≠ e6Root k).image
      fun k => ({e6Root k, rhoL (e6Root k)} : Finset (Fin Tag.E6.rank → ℤ))).card = 6 := by
  decide +kernel

theorem card_fixed_setD : ((Finset.univ.filter fun k : Fin 72 =>
    ((e6Root k (i6 0) = 0 ∧ e6Root k (i6 5) = 0) ∧ 0 < height (e6Root k)) ∧
      rhoL (e6Root k) = e6Root k).image e6Root).card = 6 := by
  decide +kernel

theorem card_paired_setD : ((Finset.univ.filter fun k : Fin 72 =>
    ((e6Root k (i6 0) = 0 ∧ e6Root k (i6 5) = 0) ∧ 0 < height (e6Root k)) ∧
      rhoL (e6Root k) ≠ e6Root k).image
        fun k => ({e6Root k, rhoL (e6Root k)} : Finset (Fin Tag.E6.rank → ℤ))).card = 3 := by
  decide +kernel

theorem ncard_posFixed_univ
    : (posFixedRoots Set.univ).ncard = 12 := by
  rw [posFixedRoots_eq (fun α => 0 < height α) fun α hα => mem_parabolicPosRoots_univ hα,
    Set.ncard_coe_finset, card_fixed_univ]

theorem ncard_posPaired_univ
    : (posPairedOrbits Set.univ).ncard = 12 := by
  rw [posPairedOrbits_eq (fun α => 0 < height α) fun α hα => mem_parabolicPosRoots_univ hα,
    Set.ncard_coe_finset, card_paired_univ]

theorem ncard_posFixed_setA : (posFixedRoots setA).ncard = 3 := by
  rw [posFixedRoots_eq (fun α => α (i6 1) = 0 ∧ 0 < height α)
    fun α hα => mem_parabolicPosRoots_setA hα, Set.ncard_coe_finset, card_fixed_setA]

theorem ncard_posPaired_setA : (posPairedOrbits setA).ncard = 6 := by
  rw [posPairedOrbits_eq (fun α => α (i6 1) = 0 ∧ 0 < height α)
    fun α hα => mem_parabolicPosRoots_setA hα, Set.ncard_coe_finset, card_paired_setA]

theorem ncard_posFixed_setD : (posFixedRoots setD).ncard = 6 := by
  rw [posFixedRoots_eq (fun α => (α (i6 0) = 0 ∧ α (i6 5) = 0) ∧ 0 < height α)
    fun α hα => mem_parabolicPosRoots_setD hα, Set.ncard_coe_finset, card_fixed_setD]

theorem ncard_posPaired_setD : (posPairedOrbits setD).ncard = 3 := by
  rw [posPairedOrbits_eq (fun α => (α (i6 0) = 0 ∧ α (i6 5) = 0) ∧ 0 < height α)
    fun α hα => mem_parabolicPosRoots_setD hα, Set.ncard_coe_finset, card_paired_setD]

end CFSG.LieType.Chevalley.C2E6Std
