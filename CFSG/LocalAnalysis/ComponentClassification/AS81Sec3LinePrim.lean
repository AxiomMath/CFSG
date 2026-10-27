module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3LineCert
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridge
public import CFSG.Certificates.MergePrimitivity
public import CFSG.LargeExtraspecial.S4CEOmegaSpin
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.LargeExtraspecial.O62Model
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4SevenInput
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.Th.F2Spec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81.MinusLines

open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits

theorem lineGens_size : lineGens.size = 8 := by
  simp [lineGens, omega1Gens]

theorem omega1Gens_get {i : ℕ} (hi : i < 8) : omega1Gens[i]! = copy0Arr genArrs[i]! := by
  rw [omega1Gens, getElem!_ofFn_of_lt _ hi]

theorem lineGens_parts : allPermsOK 1120 lineGens = true ∧
    ∀ i < 8, ∀ t < 1120,
      onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.1]! = true ∧
      onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.2.1]! = true ∧
      onLine lineArr[(lineGens[i]!)[t]!]! (omega1Gens[i]!)[lineArr[t]!.2.2]! = true := by
  have h := lineGens_check
  simp only [lineGensCheck, Bool.and_eq_true] at h
  refine ⟨h.1, fun i hi t ht => ?_⟩
  have := allLt_spec (allLt_spec h.2 hi) ht
  simpa only [Bool.and_eq_true, and_assoc] using this

@[expose] def linePerm (i : ℕ) : Equiv.Perm (Fin 1120) := permOfArr 1120 lineGens[i]!

theorem rep_linePerm {i : ℕ} (hi : i < 8) :
    Rep 1120 lineGens[i]! (linePerm i) :=
  rep_of_allPermsOK lineGens_parts.1 (by rw [lineGens_size]; exact hi)

@[expose] def lineP : Subgroup (Equiv.Perm (Fin 1120)) :=
  Subgroup.closure (Set.range fun i : Fin 8 => linePerm i)

theorem linePerm_mem {i : ℕ} (hi : i < 8) : linePerm i ∈ lineP :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem lineP_eq_genGroup : lineP = genGroup lineGens linePerm := by
  rw [lineP, genGroup, lineGens_size]
  congr 1
  ext g
  simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq]
  exact ⟨fun ⟨i, hi⟩ => ⟨i, i.2, hi⟩, fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩⟩

theorem lineP_pretransitive :
    MulAction.IsPretransitive lineP (Fin 1120) := by
  have h := lineTrans_check
  unfold lineTransCheck forestOK at h
  rw [lineP_eq_genGroup]
  exact pretransitive_of_orbitLabelOK h fun i hi => rep_linePerm (by rwa [lineGens_size] at hi)

@[expose] def lineH0Gen (j : ℕ) : Equiv.Perm (Fin 1120) := wordIn 8 linePerm (lineH0Words.getD j [])

@[expose] def lineH0 : Subgroup (Equiv.Perm (Fin 1120)) := genGroup lineH0Arrs lineH0Gen

theorem lineH0Arrs_size : lineH0Arrs.size = 4 := by
  simp [lineH0Arrs, lineH0Words]

theorem lineH0_parts : (∀ w ∈ lineH0Words, lettersOK 8 w = true) ∧
    (∀ j < 4, (lineH0Arrs[j]!)[0]! = 0) ∧
    orbitLabelOK 1120 lineH0Arrs 5 lineH0Forest.1 lineH0Reps lineH0Forest.2.1 lineH0Forest.2.2.1
      lineH0Forest.2.2.2 = true := by
  have h := lineH0_check
  simp only [lineH0Check, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1, fun j hj => by simpa using allLt_spec h.1.2 hj, h.2⟩

theorem lineH0Arrs_get {j : ℕ} (hj : j < 4) :
    lineH0Arrs[j]! = wordArr 1120 lineGens (lineH0Words.getD j []) := by
  have hj' : j < lineH0Words.length := by simp [lineH0Words]; omega
  rw [lineH0Arrs, getElem!_pos _ j (by simpa using hj'), List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem _ _ hj']

theorem rep_lineH0Gen :
    ∀ j < lineH0Arrs.size, Rep 1120 lineH0Arrs[j]! (lineH0Gen j) := by
  intro j hj
  rw [lineH0Arrs_size] at hj
  rw [lineH0Arrs_get hj, lineH0Gen]
  refine rep_wordArr (by rw [lineGens_size]) (fun i hi => rep_linePerm hi)
    (fun i hi => isInvA_of_allPermsOK lineGens_parts.1 (by rw [lineGens_size]; exact hi)) ?_
  refine lineH0_parts.1 _ ?_
  rw [List.getD_eq_getElem _ _ (by simp [lineH0Words]; omega)]
  exact List.getElem_mem _

theorem lineH0_le : lineH0 ≤ lineP := by
  rw [lineH0, genGroup, Subgroup.closure_le]
  rintro _ ⟨j, -, rfl⟩
  exact wordIn_mem (fun i hi => linePerm_mem hi) _

theorem lineH0Gen_fix {j : ℕ} (hj : j < 4) : lineH0Gen j 0 = 0 := by
  have h := (rep_lineH0Gen j (by rw [lineH0Arrs_size]; exact hj)).apply
    (show 0 < 1120 by norm_num)
  rw [lineH0_parts.2.1 j hj] at h
  exact Fin.ext h.symm

theorem lineH0_fix : ∀ h ∈ lineH0, h 0 = 0 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    exact lineH0Gen_fix (by rwa [lineH0Arrs_size] at hj)
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem lineH0_cover (x : Fin 1120) (hx : x ≠ 0) :
    ∃ j : Fin 4, ∃ h ∈ lineH0, h (finPt 1120 lineH0Reps[(j : ℕ) + 1]!) = x := by
  have hok := lineH0_parts.2.2
  obtain ⟨hlab, -⟩ := orbitLabelOK_parts hok
  obtain ⟨g, hg, hgx⟩ := mem_orbit_rep hok rep_lineH0Gen x
  have hc : lineH0Forest.1[(x : ℕ)]! < 5 := hlab x x.2
  have hc0 : lineH0Forest.1[(x : ℕ)]! ≠ 0 := by
    intro h0
    apply hx
    rw [← hgx]
    have e : (⟨lineH0Reps[lineH0Forest.1[(x : ℕ)]!]! % 1120, Nat.mod_lt _ (Fin.pos x)⟩ :
        Fin 1120) = 0 := by
      apply Fin.ext
      simp only [h0]
      rfl
    rw [e]
    exact lineH0_fix g hg
  refine ⟨⟨lineH0Forest.1[(x : ℕ)]! - 1, by omega⟩, g, hg, Eq.trans (congrArg g (Fin.ext ?_)) hgx⟩
  show lineH0Reps[lineH0Forest.1[(x : ℕ)]! - 1 + 1]! % 1120 = _
  rw [show lineH0Forest.1[(x : ℕ)]! - 1 + 1 = lineH0Forest.1[(x : ℕ)]! by omega]

theorem lineMerge_valid (j : Fin 4) :
    ValidInvariantMerge (fun i : Fin 8 => linePerm i) 0 (finPt 1120 lineH0Reps[(j : ℕ) + 1]!)
      (lineMerge j) := by
  refine validInvariantMerge_of_mergeOK (G := lineGens) (fun i => rep_linePerm i.2) ?_
  have h := allLt_spec lineMerge_check j.2
  have hx : ((finPt 1120 lineH0Reps[(j : ℕ) + 1]! : Fin 1120) : ℕ) = lineH0Reps[(j : ℕ) + 1]! :=
    finPt_val (by fin_cases j <;> decide)
  rw [hx]
  exact h

theorem lineP_preprimitive :
    MulAction.IsPreprimitive lineP (Fin 1120) := by
  exact stabilizer_orbit_merge_primitivity (fun i : Fin 8 => linePerm i)
    (htrans := lineP_pretransitive) 0 lineH0 lineH0_le
    lineH0_fix (xs := fun j : Fin 4 => finPt 1120 lineH0Reps[(j : ℕ) + 1]!) lineH0_cover
    fun j => ⟨_, lineMerge_valid j⟩

theorem line_parts : (∀ t < 1120, lineArr[t]!.1 < lineArr[t]!.2.1 ∧
      lineArr[t]!.2.1 < lineArr[t]!.2.2 ∧ lineArr[t]!.2.2 < 120 ∧
      pairLine[120 * lineArr[t]!.1 + lineArr[t]!.2.1]! = t) ∧
    ∀ a < 120, ∀ b < 120, a ≠ b → bNat nsArr[a]! nsArr[b]! = true →
      pairLine[120 * a + b]! < 1120 ∧ onLine lineArr[pairLine[120 * a + b]!]! a = true ∧
        onLine lineArr[pairLine[120 * a + b]!]! b = true ∧
        onLine lineArr[pairLine[120 * a + b]!]! (thirdPt a b) = true := by
  have h := line_check
  simp only [lineCheck, Bool.and_eq_true] at h
  refine ⟨fun t ht => ?_, fun a ha b hb hab hB => ?_⟩
  · have := allLt_spec h.1 ht
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩
  · have := allLt_spec (allLt_spec h.2 ha) hb
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, bne_eq_false_iff_eq,
      hB, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with (h' | h') | h'
    · exact absurd h' hab
    · exact absurd h' (by simp)
    · exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

theorem onLine_iff {s : ℕ × ℕ × ℕ} {x : ℕ} :
    onLine s x = true ↔ x = s.1 ∨ x = s.2.1 ∨ x = s.2.2 := by
  simp [onLine, or_assoc]

@[expose] def linePts (t : Fin 1120) : Finset (Fin 120) :=
  {finPt 120 lineArr[(t : ℕ)]!.1, finPt 120 lineArr[(t : ℕ)]!.2.1, finPt 120 lineArr[(t : ℕ)]!.2.2}

theorem mem_linePts {t : Fin 1120} {y : Fin 120} : y ∈ linePts t ↔
    (y : ℕ) = lineArr[(t : ℕ)]!.1 ∨ (y : ℕ) = lineArr[(t : ℕ)]!.2.1 ∨
      (y : ℕ) = lineArr[(t : ℕ)]!.2.2 := by
  obtain ⟨h1, h2, h3, -⟩ := line_parts.1 t t.2
  simp only [linePts, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff,
    finPt_val (show lineArr[(t : ℕ)]!.1 < 120 by omega),
    finPt_val (show lineArr[(t : ℕ)]!.2.1 < 120 by omega), finPt_val h3]

theorem card_linePts (t : Fin 1120) : (linePts t).card = 3 := by
  obtain ⟨h1, h2, h3, -⟩ := line_parts.1 t t.2
  rw [linePts, Finset.card_eq_three]
  refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;> rw [Ne, Fin.ext_iff, finPt_val (by omega),
    finPt_val (by omega)] <;> omega

theorem linePts_injective : Function.Injective linePts := by
  intro t t' h
  have key : ∀ y : Fin 120, y ∈ linePts t ↔ y ∈ linePts t' := fun y => by rw [h]
  obtain ⟨a1, a2, a3, a4⟩ := line_parts.1 t t.2
  obtain ⟨b1, b2, b3, b4⟩ := line_parts.1 t' t'.2
  have m : ∀ x < 120, ((x = lineArr[(t : ℕ)]!.1 ∨ x = lineArr[(t : ℕ)]!.2.1 ∨
      x = lineArr[(t : ℕ)]!.2.2) ↔ (x = lineArr[(t' : ℕ)]!.1 ∨ x = lineArr[(t' : ℕ)]!.2.1 ∨
      x = lineArr[(t' : ℕ)]!.2.2)) := fun x hx => by
    have := key ⟨x, hx⟩
    rwa [mem_linePts, mem_linePts] at this
  have e1 := (m _ (by omega)).1 (Or.inl rfl)
  have e2 := (m _ (by omega)).1 (Or.inr (Or.inl rfl))
  have e3 := (m _ a3).1 (Or.inr (Or.inr rfl))
  have f1 := (m _ (by omega)).2 (Or.inl rfl)
  have f2 := (m _ (by omega)).2 (Or.inr (Or.inl rfl))
  have f3 := (m _ b3).2 (Or.inr (Or.inr rfl))
  have hab : lineArr[(t : ℕ)]!.1 = lineArr[(t' : ℕ)]!.1 ∧
      lineArr[(t : ℕ)]!.2.1 = lineArr[(t' : ℕ)]!.2.1 := by omega
  apply Fin.ext
  rw [← a4, ← b4, hab.1, hab.2]

theorem omega1Gens_rep {i : ℕ} (hi : i < 8) :
    Rep 120 omega1Gens[i]! (gen1 i) := by
  rw [omega1Gens_get hi]
  exact rep_gen1 hi

theorem image_gen1_linePts {i : ℕ}
    (hi : i < 8) (t : Fin 1120) : (linePts t).image (gen1 i) = linePts (linePerm i t) := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hval : ((linePerm i t : Fin 1120) : ℕ) = (lineGens[i]!)[(t : ℕ)]! :=
      ((rep_linePerm hi) t).symm
    have hg : ((gen1 i x : Fin 120) : ℕ) = (omega1Gens[i]!)[(x : ℕ)]! :=
      ((omega1Gens_rep hi) x).symm
    rw [mem_linePts] at hx
    rw [mem_linePts, hval, hg, ← onLine_iff]
    obtain ⟨o1, o2, o3⟩ := lineGens_parts.2 i hi t t.2
    rcases hx with hx | hx | hx <;> rw [hx]
    exacts [o1, o2, o3]
  · rw [card_linePts, Finset.card_image_of_injective _ (gen1 i).injective, card_linePts]

theorem exists_linePerm
    {g : Equiv.Perm (Fin 120)} (hg : g ∈ omega1T) :
    ∃ σ ∈ lineP, ∀ t, (linePts t).image g = linePts (σ t) := by
  classical
  rw [omega1T_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact ⟨linePerm i, linePerm_mem hi, image_gen1_linePts hi⟩
  | one => exact ⟨1, one_mem _, fun t => by simp⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨σ, hσ, hσt⟩ := ihg
    obtain ⟨τ, hτ, hτt⟩ := ihh
    refine ⟨σ * τ, mul_mem hσ hτ, fun t => ?_⟩
    rw [Equiv.Perm.coe_mul, ← Finset.image_image, hτt, hσt]
    rfl
  | inv g _ ih =>
    obtain ⟨σ, hσ, hσt⟩ := ih
    refine ⟨σ⁻¹, inv_mem hσ, fun t => ?_⟩
    have := hσt (σ⁻¹ t)
    rw [perm_apply_inv] at this
    rw [← this, Finset.image_image]
    simp

@[expose] def linePermOf
    (g : omega1T) : Equiv.Perm (Fin 1120) :=
  Classical.choose (exists_linePerm g.2)

theorem linePermOf_mem
    (g : omega1T) : linePermOf g ∈ lineP :=
  (Classical.choose_spec (exists_linePerm g.2)).1

theorem linePermOf_spec (g : omega1T)
    (t : Fin 1120) :
    (linePts t).image (g : Equiv.Perm (Fin 120)) = linePts (linePermOf g t) :=
  (Classical.choose_spec (exists_linePerm g.2)).2 t

theorem linePermOf_unique
    {g : omega1T} {σ : Equiv.Perm (Fin 1120)}
    (h : ∀ t, (linePts t).image (g : Equiv.Perm (Fin 120)) = linePts (σ t)) :
    linePermOf g = σ :=
  Equiv.ext fun t => linePts_injective (by rw [← linePermOf_spec, h])

@[expose] def lineHom :
    omega1T →* Equiv.Perm (Fin 1120) where
  toFun := linePermOf
  map_one' := linePermOf_unique fun t => by simp
  map_mul' g h := linePermOf_unique fun t => by
    classical
    rw [Subgroup.coe_mul, Equiv.Perm.coe_mul, ← Finset.image_image, linePermOf_spec,
      linePermOf_spec]
    rfl

theorem lineHom_spec (g : omega1T)
    (t : Fin 1120) :
    (linePts t).image (g : Equiv.Perm (Fin 120)) = linePts (lineHom g t) :=
  linePermOf_spec g t

theorem gen1_mem_omega1T {i : ℕ} (hi : i < 8) : gen1 i ∈ omega1T := by
  rw [omega1T_eq]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem lineHom_range :
    lineHom.range = lineP := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · rintro _ ⟨g, rfl⟩
    exact linePermOf_mem g
  · rintro _ ⟨i, rfl⟩
    exact ⟨⟨gen1 i, gen1_mem_omega1T i.2⟩, linePermOf_unique (image_gen1_linePts i.2)⟩

theorem exists_linePts {a b : Fin 120} (hab : a ≠ b)
    (hB : bNat nsArr[(a : ℕ)]! nsArr[(b : ℕ)]! = true) :
    ∃ t : Fin 1120, a ∈ linePts t ∧ b ∈ linePts t ∧
      ∀ c : Fin 120, (c : ℕ) = thirdPt a b → c ∈ linePts t := by
  obtain ⟨ht, ha, hb, hc⟩ := line_parts.2 a a.2 b b.2 (fun h => hab (Fin.ext h)) hB
  refine ⟨⟨_, ht⟩, ?_, ?_, fun c hc' => ?_⟩
  · rw [mem_linePts]
    exact onLine_iff.1 ha
  · rw [mem_linePts]
    exact onLine_iff.1 hb
  · rw [mem_linePts, hc']
    exact onLine_iff.1 hc

section Model

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Orthogonal

local notation "V₀" => Fin 4 ⊕ Fin 4 → ZMod 2
local notation "q₀" => quadPlus 4 (ZMod 2)

theorem card_zmod_two_eq : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2

@[expose] def nsPts (U : Submodule (ZMod 2) V₀) :
    Finset (Fin 120) := by
  classical
  exact Finset.univ.filter fun j => ((nsVec card_zmod_two_eq j : NS (ZMod 2)) : V₀) ∈ U

theorem mem_nsPts {U : Submodule (ZMod 2) V₀} {j : Fin 120} :
    j ∈ nsPts U ↔ ((nsVec card_zmod_two_eq j : NS (ZMod 2)) : V₀) ∈ U := by
  classical
  simp [nsPts]

theorem image_act0_nsPts (h : orthElementaryGroup q₀)
    (U : Submodule (ZMod 2) V₀) :
    (nsPts U).image (act0 card_zmod_two_eq h) =
      nsPts (U.map ((h : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)) := by
  classical
  ext k
  simp only [Finset.mem_image, mem_nsPts, Submodule.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, hj, (nsEquiv_act0 card_zmod_two_eq h j).symm⟩
  · rintro ⟨u, hu, hk⟩
    rw [LinearEquiv.coe_coe] at hk
    have hq : q₀ u = 1 := by
      rw [← quadPlus_elementary h u, hk]
      exact (nsVec card_zmod_two_eq k).2
    obtain ⟨j, hj⟩ := (nsVec_bijective card_zmod_two_eq).2 ⟨u, hq⟩
    refine ⟨j, by rw [hj]; exact hu, ?_⟩
    apply (nsVec_bijective card_zmod_two_eq).1
    apply Subtype.ext
    rw [← nsEquiv_apply, nsEquiv_act0, hj]
    exact hk

theorem eq_of_nsPts_eq {U U' : Submodule (ZMod 2) V₀}
    (hU : ∀ u ∈ U, q₀ u = 0 → u = 0) (hU' : ∀ u ∈ U', q₀ u = 0 → u = 0)
    (h : nsPts U = nsPts U') : U = U' := by
  have key : ∀ {U U' : Submodule (ZMod 2) V₀}, (∀ u ∈ U, q₀ u = 0 → u = 0) →
      nsPts U = nsPts U' → U ≤ U' := by
    intro U U' hU h u hu
    rcases eq_zero_or_eq_one_of_card_eq_two card_zmod_two_eq (q₀ u) with h0 | h1
    · rw [hU u hu h0]
      exact U'.zero_mem
    · obtain ⟨j, hj⟩ := (nsVec_bijective card_zmod_two_eq).2 ⟨u, h1⟩
      have hjU : j ∈ nsPts U := by rw [mem_nsPts, hj]; exact hu
      rw [h, mem_nsPts, hj] at hjU
      exact hjU
  exact le_antisymm (key hU h) (key hU' h.symm)

theorem nsArr_lt (j : Fin 120) : nsArr[(j : ℕ)]! < 256 :=
  (ns_ok.2.2.1 j j.2).1

theorem xor_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 := by
  rw [show (256 : ℕ) = 2 ^ 8 by norm_num] at ha hb ⊢
  exact Nat.xor_lt_two_pow ha hb

theorem exists_linePts_eq_nsPts
    {U : Submodule (ZMod 2) V₀} (h2 : Module.finrank (ZMod 2) U = 2)
    (hU : ∀ u ∈ U, q₀ u = 0 → u = 0) : ∃ t, linePts t = nsPts U := by
  classical
  have hK := card_zmod_two_eq
  let b := Module.finBasisOfFinrankEq (ZMod 2) U h2
  set u : V₀ := (b 0 : V₀) with hu
  set v : V₀ := (b 1 : V₀) with hv
  have hu0 : u ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
  have hv0 : v ≠ 0 := fun h => b.ne_zero 1 (Subtype.ext h)
  have huv : u ≠ v := fun h => absurd (b.injective (Subtype.ext h)) (by decide)
  have huvU : u + v ∈ U := U.add_mem (b 0).2 (b 1).2
  have huv0 : u + v ≠ 0 := by
    intro h
    apply huv
    have := charP_two_of_card_eq_two hK
    rw [← sub_eq_zero, CharTwo.sub_eq_add]
    exact h
  have hns : ∀ x ∈ U, x ≠ 0 → q₀ x = 1 := fun x hx hx0 =>
    (eq_zero_or_eq_one_of_card_eq_two hK (q₀ x)).resolve_left fun h => hx0 (hU x hx h)
  have hmem : ∀ x ∈ U, x = 0 ∨ x = u ∨ x = v ∨ x = u + v := by
    intro x hx
    have e := (b.sum_repr ⟨x, hx⟩).symm
    rw [Fin.sum_univ_two] at e
    have ex := congrArg Subtype.val e
    simp only [Submodule.coe_add, Submodule.coe_smul] at ex
    rcases eq_zero_or_eq_one_of_card_eq_two hK (b.repr ⟨x, hx⟩ 0) with c0 | c0 <;>
      rcases eq_zero_or_eq_one_of_card_eq_two hK (b.repr ⟨x, hx⟩ 1) with c1 | c1 <;>
      rw [c0, c1] at ex <;> simp only [zero_smul, one_smul, zero_add, add_zero] at ex <;>
      simp [ex, hu, hv]
  obtain ⟨a₀, ha₀⟩ := (nsVec_bijective hK).2 ⟨u, hns u (b 0).2 hu0⟩
  obtain ⟨b₀, hb₀⟩ := (nsVec_bijective hK).2 ⟨v, hns v (b 1).2 hv0⟩
  obtain ⟨c₀, hc₀⟩ := (nsVec_bijective hK).2 ⟨u + v, hns _ huvU huv0⟩
  have ea : vecK (ZMod 2) nsArr[(a₀ : ℕ)]! = u := by rw [← nsVec_val hK, ha₀]
  have eb : vecK (ZMod 2) nsArr[(b₀ : ℕ)]! = v := by rw [← nsVec_val hK, hb₀]
  have ec : vecK (ZMod 2) nsArr[(c₀ : ℕ)]! = u + v := by rw [← nsVec_val hK, hc₀]
  have hab : a₀ ≠ b₀ := by
    rintro rfl
    exact huv (by rw [← ea, ← eb])
  have hB : bNat nsArr[(a₀ : ℕ)]! nsArr[(b₀ : ℕ)]! = true := by
    have hp := polar_vecK hK nsArr[(a₀ : ℕ)]! nsArr[(b₀ : ℕ)]!
    rw [ea, eb, polar, hns _ huvU huv0, hns u (b 0).2 hu0, hns v (b 1).2 hv0] at hp
    by_contra hf
    rw [Bool.not_eq_true] at hf
    rw [hf] at hp
    revert hp
    decide
  have hthird : thirdPt a₀ b₀ = c₀ := by
    have hx : nsArr[(a₀ : ℕ)]! ^^^ nsArr[(b₀ : ℕ)]! = nsArr[(c₀ : ℕ)]! := by
      apply vecK_injective (K := ZMod 2) (xor_lt_256 (nsArr_lt a₀) (nsArr_lt b₀)) (nsArr_lt c₀)
      rw [vecK_xor hK, ea, eb, ec]
    rw [thirdPt, hx]
    exact (ns_ok.2.2.1 c₀ c₀.2).2.2
  obtain ⟨t, hta, htb, htc⟩ := exists_linePts hab hB
  refine ⟨t, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro j hj
    rw [mem_nsPts] at hj
    rcases hmem _ hj with h | h | h | h
    · exfalso
      have hq := (nsVec hK j).2
      rw [h, QuadraticMap.map_zero] at hq
      exact zero_ne_one hq
    · have : j = a₀ := (nsVec_bijective hK).1 (Subtype.ext (by rw [h, ha₀]))
      rw [this]
      exact hta
    · have : j = b₀ := (nsVec_bijective hK).1 (Subtype.ext (by rw [h, hb₀]))
      rw [this]
      exact htb
    · have : j = c₀ := (nsVec_bijective hK).1 (Subtype.ext (by rw [h, hc₀]))
      rw [this]
      exact htc c₀ hthird.symm
  · rw [card_linePts]
    have hsub : ({a₀, b₀, c₀} : Finset (Fin 120)) ⊆ nsPts U := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [mem_nsPts]
      rcases hj with rfl | rfl | rfl
      · rw [ha₀]; exact (b 0).2
      · rw [hb₀]; exact (b 1).2
      · rw [hc₀]; exact huvU
    have hac : a₀ ≠ c₀ := by
      rintro rfl
      exact hv0 (by simpa [← ea] using ec)
    have hbc : b₀ ≠ c₀ := by
      rintro rfl
      exact hu0 (by simpa [← eb] using ec)
    calc 3 = ({a₀, b₀, c₀} : Finset (Fin 120)).card := (Finset.card_eq_three.2
          ⟨a₀, b₀, c₀, hab, hac, hbc, rfl⟩).symm
      _ ≤ _ := Finset.card_le_card hsub

@[expose] def modelHom :
    orthElementaryGroup q₀ →* Equiv.Perm (Fin 1120) :=
  lineHom.comp (elementaryOmega1Equiv card_zmod_two_eq).toMonoidHom

theorem linePts_modelHom
    (h : orthElementaryGroup q₀) (t : Fin 1120) :
    linePts (modelHom h t) = (linePts t).image (act0 card_zmod_two_eq h) := by
  rw [modelHom, MonoidHom.comp_apply, ← lineHom_spec]
  rfl

theorem modelHom_range :
    modelHom.range = lineP := by
  rw [modelHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 (elementaryOmega1Equiv card_zmod_two_eq).surjective,
    ← MonoidHom.range_eq_map, lineHom_range]

end Model

section Abstract

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial

local notation "V₀" => Fin 4 ⊕ Fin 4 → ZMod 2
local notation "q₀" => quadPlus 4 (ZMod 2)

theorem omega_model_eq :
    omegaGroup q₀ (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) = orthElementaryGroup q₀ :=
  S4.omegaGroup_eq_elementaryGroup (nondegenerate_polarBilin_quadPlus 4 (ZMod 2))
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]; norm_num)
    (plusPair_orth (K := ZMod 2) (n := 4) (i := 0) (j := 1) (by decide))

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem map_one_linearEquiv (W : Submodule (ZMod 2) V) :
    W.map ((1 : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W :=
  Submodule.map_id W

theorem map_mul_linearEquiv (a b : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    W.map ((a * b : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) =
      (W.map (b : V →ₗ[ZMod 2] V)).map (a : V →ₗ[ZMod 2] V) :=
  Submodule.map_comp _ _ W

theorem aniso_map_orth {W : Submodule (ZMod 2) V} (hWa : ∀ w ∈ W, Q w = 0 → w = 0)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ∀ x ∈ W.map (g : V →ₗ[ZMod 2] V), Q x = 0 → x = 0 := by
  rintro _ ⟨w, hw, rfl⟩ h
  rw [LinearEquiv.coe_coe, map_of_mem hg] at h
  rw [LinearEquiv.coe_coe, hWa w hw h, map_zero]

variable [FiniteDimensional (ZMod 2) V]

@[expose] def omegaStab (hQ : Q.polarBilin.Nondegenerate) (W : Submodule (ZMod 2) V) :
    Subgroup (omegaGroup Q hQ) where
  carrier := {g | W.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W}
  one_mem' := map_one_linearEquiv W
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [Subgroup.coe_mul, map_mul_linearEquiv, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← map_mul_linearEquiv, Subgroup.coe_inv, inv_mul_cancel, map_one_linearEquiv]

theorem mem_omegaStab {hQ : Q.polarBilin.Nondegenerate} {W : Submodule (ZMod 2) V}
    {g : omegaGroup Q hQ} :
    g ∈ omegaStab hQ W ↔ W.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) = W :=
  Iff.rfl

theorem orth_of_omega {hQ : Q.polarBilin.Nondegenerate} (g : omegaGroup Q hQ) :
    (g : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  (mem_omegaGroup.1 g.2).1

variable (hQ : Q.polarBilin.Nondegenerate) {L : V ≃ₗ[ZMod 2] V₀} (hL : ∀ v, q₀ (L v) = Q v)

omit [FiniteDimensional (ZMod 2) V] in
theorem map_conjL_map (g : V ≃ₗ[ZMod 2] V) (W : Submodule (ZMod 2) V) :
    (W.map (L : V →ₗ[ZMod 2] V₀)).map ((O62.conjL L g : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀) =
      (W.map (g : V →ₗ[ZMod 2] V)).map (L : V →ₗ[ZMod 2] V₀) := by
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext v
  simp [O62.conjL_apply]

include hL

omit [FiniteDimensional (ZMod 2) V] in
theorem aniso_map_L {W : Submodule (ZMod 2) V} (hWa : ∀ w ∈ W, Q w = 0 → w = 0) :
    ∀ x ∈ W.map (L : V →ₗ[ZMod 2] V₀), q₀ x = 0 → x = 0 := by
  rintro _ ⟨w, hw, rfl⟩ h
  rw [LinearEquiv.coe_coe, hL] at h
  rw [LinearEquiv.coe_coe, hWa w hw h, map_zero]

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_line
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) :
    ∃ t, linePts t = nsPts (W.map (L : V →ₗ[ZMod 2] V₀)) :=
  exists_linePts_eq_nsPts (by rw [LinearEquiv.finrank_map_eq]; exact hW) (aniso_map_L hL hWa)

theorem conjL_mem_elem (g : omegaGroup Q hQ) :
    O62.conjL L g ∈ orthElementaryGroup q₀ := by
  rw [← omega_model_eq]
  exact (O62.mem_omegaGroup_conjL hQ _ hL).2 g.2

@[expose] def toElem : omegaGroup Q hQ →* orthElementaryGroup q₀ :=
  ((O62.conjL L).toMonoidHom.comp (omegaGroup Q hQ).subtype).codRestrict _
    fun g => conjL_mem_elem hQ hL g

theorem toElem_apply (g : omegaGroup Q hQ) :
    (toElem hQ hL g : V₀ ≃ₗ[ZMod 2] V₀) = O62.conjL L g := rfl

theorem toElem_bijective : Function.Bijective (toElem hQ hL) := by
  refine ⟨fun g h e => Subtype.ext ((O62.conjL L).injective ?_), fun h => ?_⟩
  · have := congrArg Subtype.val e
    rwa [toElem_apply, toElem_apply] at this
  · refine ⟨⟨(O62.conjL L).symm h, ?_⟩, Subtype.ext ?_⟩
    · rw [← O62.mem_omegaGroup_conjL hQ (nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) hL,
        MulEquiv.apply_symm_apply, omega_model_eq]
      exact h.2
    · rw [toElem_apply, MulEquiv.apply_symm_apply]

@[expose] def lineAct :
    omegaGroup Q hQ →* Equiv.Perm (Fin 1120) :=
  modelHom.comp (toElem hQ hL)

theorem lineAct_range :
    (lineAct hQ hL).range = lineP := by
  rw [lineAct, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (toElem_bijective hQ hL).2,
    ← MonoidHom.range_eq_map, modelHom_range]

theorem linePts_lineAct
    {W : Submodule (ZMod 2) V} {t : Fin 1120}
    (ht : linePts t = nsPts (W.map (L : V →ₗ[ZMod 2] V₀))) (g : omegaGroup Q hQ) :
    linePts (lineAct hQ hL g t) =
      nsPts ((W.map ((g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V)).map (L : V →ₗ[ZMod 2] V₀)) := by
  rw [lineAct, MonoidHom.comp_apply, linePts_modelHom, ht, image_act0_nsPts, toElem_apply,
    map_conjL_map]

theorem lineAct_eq_iff
    {W : Submodule (ZMod 2) V} (hWa : ∀ w ∈ W, Q w = 0 → w = 0) {t : Fin 1120}
    (ht : linePts t = nsPts (W.map (L : V →ₗ[ZMod 2] V₀))) (g : omegaGroup Q hQ) :
    lineAct hQ hL g t = t ↔ g ∈ omegaStab hQ W := by
  rw [mem_omegaStab]
  constructor
  · intro h
    have h1 := linePts_lineAct hQ hL ht g
    rw [h, ht] at h1
    exact (Submodule.map_injective_of_injective L.injective (eq_of_nsPts_eq
      (aniso_map_L hL (aniso_map_orth hWa (orth_of_omega g))) (aniso_map_L hL hWa)
      h1.symm))
  · intro h
    apply linePts_injective
    rw [linePts_lineAct hQ hL ht g, h, ht]

@[expose] def lineActP :
    omegaGroup Q hQ →* lineP :=
  (lineAct hQ hL).codRestrict lineP fun g => lineAct_range hQ hL ▸ ⟨g, rfl⟩

theorem lineActP_surjective :
    Function.Surjective (lineActP hQ hL) := by
  rintro ⟨σ, hσ⟩
  rw [← lineAct_range hQ hL] at hσ
  obtain ⟨g, rfl⟩ := hσ
  exact ⟨g, rfl⟩

theorem omegaStab_eq_comap
    {W : Submodule (ZMod 2) V} (hWa : ∀ w ∈ W, Q w = 0 → w = 0) {t : Fin 1120}
    (ht : linePts t = nsPts (W.map (L : V →ₗ[ZMod 2] V₀))) :
    omegaStab hQ W = (MulAction.stabilizer lineP t).comap (lineActP hQ hL) := by
  ext g
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, ← lineAct_eq_iff hQ hL hWa ht]
  rfl

theorem isCoatom_omegaStab'
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) : IsCoatom (omegaStab hQ W) := by
  obtain ⟨t, ht⟩ := exists_line hL hW hWa
  have := lineP_preprimitive
  rw [omegaStab_eq_comap hQ hL hWa ht]
  exact Subgroup.isCoatom_comap_of_surjective (lineActP_surjective hQ hL)
    (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive lineP t)

theorem card_omegaGroup' : Nat.card (omegaGroup Q hQ) = 174182400 := by
  rw [Nat.card_congr (MulEquiv.ofBijective _ (toElem_bijective hQ hL)).toEquiv,
    card_elementaryGroup_four card_zmod_two_eq]

theorem card_omegaStab'
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) : Nat.card (omegaStab hQ W) = 155520 := by
  obtain ⟨t, ht⟩ := exists_line hL hW hWa
  have := lineP_pretransitive
  have hidx : (omegaStab hQ W).index = 1120 := by
    rw [omegaStab_eq_comap hQ hL hWa ht,
      Subgroup.index_comap_of_surjective _ (lineActP_surjective hQ hL),
      MulAction.index_stabilizer_of_transitive, Nat.card_fin]
  have h := Subgroup.card_mul_index (omegaStab hQ W)
  rw [hidx, card_omegaGroup' hQ hL] at h
  omega

theorem exists_map_eq'
    {W₁ W₂ : Submodule (ZMod 2) V} (hW₁ : Module.finrank (ZMod 2) W₁ = 2)
    (hW₁a : ∀ w ∈ W₁, Q w = 0 → w = 0) (hW₂ : Module.finrank (ZMod 2) W₂ = 2)
    (hW₂a : ∀ w ∈ W₂, Q w = 0 → w = 0) :
    ∃ g ∈ omegaGroup Q hQ, W₁.map (g : V →ₗ[ZMod 2] V) = W₂ := by
  obtain ⟨t₁, ht₁⟩ := exists_line hL hW₁ hW₁a
  obtain ⟨t₂, ht₂⟩ := exists_line hL hW₂ hW₂a
  have := lineP_pretransitive
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq lineP t₁ t₂
  obtain ⟨g, hg⟩ := lineActP_surjective hQ hL σ
  refine ⟨g, g.2, ?_⟩
  have h1 := linePts_lineAct hQ hL ht₁ g
  have h2 : lineAct hQ hL g t₁ = t₂ := by
    rw [← hσ, ← hg]
    rfl
  rw [h2, ht₂] at h1
  exact (Submodule.map_injective_of_injective L.injective (eq_of_nsPts_eq
    (aniso_map_L hL (aniso_map_orth hW₁a (orth_of_omega g))) (aniso_map_L hL hW₂a)
    h1.symm))

omit hL

variable (h8 : Module.finrank (ZMod 2) V = 8) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
include hQ h8 hplus

theorem exists_isometry_model :
    ∃ L : V ≃ₗ[ZMod 2] V₀, ∀ v, q₀ (L v) = Q v := by
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_quadPlus hQ (n := 4)
    (by rw [h8]) hplus
  exact ⟨e.toLinearEquiv, e.map_app⟩

theorem card_omegaGroup_of_plus : Nat.card (omegaGroup Q hQ) = 174182400 := by
  obtain ⟨L, hL⟩ := exists_isometry_model hQ h8 hplus
  exact card_omegaGroup' hQ hL

theorem isCoatom_omegaStab
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) : IsCoatom (omegaStab hQ W) := by
  obtain ⟨L, hL⟩ := exists_isometry_model hQ h8 hplus
  exact isCoatom_omegaStab' hQ hL hW hWa

theorem card_omegaStab
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) : Nat.card (omegaStab hQ W) = 155520 := by
  obtain ⟨L, hL⟩ := exists_isometry_model hQ h8 hplus
  exact card_omegaStab' hQ hL hW hWa

theorem exists_omega_map_eq
    {W₁ W₂ : Submodule (ZMod 2) V} (hW₁ : Module.finrank (ZMod 2) W₁ = 2)
    (hW₁a : ∀ w ∈ W₁, Q w = 0 → w = 0) (hW₂ : Module.finrank (ZMod 2) W₂ = 2)
    (hW₂a : ∀ w ∈ W₂, Q w = 0 → w = 0) :
    ∃ g ∈ omegaGroup Q hQ, W₁.map (g : V →ₗ[ZMod 2] V) = W₂ := by
  obtain ⟨L, hL⟩ := exists_isometry_model hQ h8 hplus
  exact exists_map_eq' hQ hL hW₁ hW₁a hW₂ hW₂a

theorem eq_omegaGroup_of_stab_le
    {W : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 2)
    (hWa : ∀ w ∈ W, Q w = 0 → w = 0) {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hHΩ : H ≤ omegaGroup Q hQ)
    (hstab : ∀ g ∈ omegaGroup Q hQ, W.map (g : V →ₗ[ZMod 2] V) = W → g ∈ H)
    (hmove : ∃ g ∈ H, W.map (g : V →ₗ[ZMod 2] V) ≠ W) : H = omegaGroup Q hQ := by
  have hco := isCoatom_omegaStab hQ h8 hplus hW hWa
  have hle : omegaStab hQ W ≤ H.subgroupOf (omegaGroup Q hQ) := fun g hg =>
    hstab g g.2 hg
  have hne : omegaStab hQ W ≠ H.subgroupOf (omegaGroup Q hQ) := by
    obtain ⟨g, hgH, hg⟩ := hmove
    intro h
    have hmem : (⟨g, hHΩ hgH⟩ : omegaGroup Q hQ) ∈ H.subgroupOf (omegaGroup Q hQ) := hgH
    rw [← h] at hmem
    exact hg hmem
  have htop := hco.2 _ (lt_of_le_of_ne hle hne)
  refine le_antisymm hHΩ fun g hg => ?_
  have : (⟨g, hg⟩ : omegaGroup Q hQ) ∈ H.subgroupOf (omegaGroup Q hQ) := by
    rw [htop]
    trivial
  exact this

end Abstract

end CFSG.ComponentClassification.AS81.MinusLines
