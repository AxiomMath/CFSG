module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBasic

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial CFSG CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne

section Blocks

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (n : ℕ)

abbrev t6psub_Idx (B : primeFormUnitary h (idGram K n)) : Type :=
  {b : primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) // IsGoodBlock h (t6psub_toLin B) b}

variable {h n}

@[expose] noncomputable def t6psub_block (B : primeFormUnitary h (idGram K n))
    (i : t6psub_Idx h n B) : Subgroup ↥(gramSU h (idGram K n)) :=
  (specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X])).comap (t6psuh_toLinSU h n)

theorem t6psub_specialBlock_le_range (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) (i : t6psub_Idx h n B) :
    specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X]) ≤ (t6psuh_toLinSU h n).range :=
  fun _ hg => t6psuh_mem_range_toLinSU
    (specialBlock_le_sesqSpecialUnitaryGroup_of_good H (t6psuh_hq h) i.1 i.2 hg)

theorem t6psub_map_block (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) (i : t6psub_Idx h n B) :
    (t6psub_block B i).map (t6psuh_toLinSU h n) =
      specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X]) :=
  Subgroup.map_comap_eq_self (t6psub_specialBlock_le_range B H i)

theorem t6psub_block_le_fix (B : primeFormUnitary h (idGram K n)) (i : t6psub_Idx h n B) :
    t6psub_block B i ≤ fixSubgroup (t6psub_actSU h n B) := fun g hg =>
  (t6psub_mem_fix_iff B g).mpr (specialBlock_le_unitaryCentralizer (Subgroup.mem_comap.mp hg)).2

theorem t6psub_block_normal (B : primeFormUnitary h (idGram K n)) (i : t6psub_Idx h n B) :
    ∀ c ∈ fixSubgroup (t6psub_actSU h n B), ∀ m ∈ t6psub_block B i,
      c * m * c⁻¹ ∈ t6psub_block B i := by
  intro c hc g hg
  have hcU := t6psub_toLinSU_mem_unitaryCentralizer B hc
  have := conj_mem_specialBlock hcU (Subgroup.mem_comap.mp hg)
  rw [t6psub_block, Subgroup.mem_comap, map_mul, map_mul, map_inv]
  exact this

theorem t6psub_isQuasisimple_block (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) (i : t6psub_Idx h n B) :
    CFSG.IsQuasisimple (t6psub_block B i) := by
  have e : ↥(t6psub_block B i) ≃*
      ↥(specialBlock (idForm h n) (t6psub_toLin B) (i.1 : K[X])) :=
    (Subgroup.equivMapOfInjective (t6psub_block B i) (t6psuh_toLinSU h n)
      t6psuh_toLinSU_injective).trans (MulEquiv.subgroupCongr (t6psub_map_block B H i))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    ((specialBlockFacts_of_good H (t6psuh_hq h) i.1 i.2).quasisimple i.2.1)

theorem t6psub_derived (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B)) :
    ∃ k : ℕ, ∀ g ∈ derivedSeries ↥(fixSubgroup (t6psub_actSU h n B)) k,
      (g : ↥(gramSU h (idGram K n))) ∈ ⨆ i : t6psub_Idx h n B, t6psub_block B i := by
  classical
  have hq := t6psuh_hq h
  set x := t6psub_toLin B with hx
  set C := fixSubgroup (t6psub_actSU h n B) with hC
  let φ : ↥C →* gl_centralizer x :=
    ((t6psuh_toLinSU h n).comp C.subtype).codRestrict (gl_centralizer x) fun g =>
      (t6psub_mem_fix_iff B g.1).mp g.2
  have hφU : ∀ g, (φ g : LinearMap.GeneralLinearGroup K (Fin n → K)) ∈
      unitaryCentralizer (idForm h n) x := fun g => t6psub_toLinSU_mem_unitaryCentralizer B g.2
  let ρ : (b : {b : primaryFactors (x : Module.End K (Fin n → K)) // ¬ IsGoodBlock h x b}) →
      ↥C →* blockGL (x : Module.End K (Fin n → K)) (b.1 : K[X]) :=
    fun b => (blockRestrict x (b.1 : K[X])).comp φ
  haveI : ∀ b, Group.IsSolvable ↥(ρ b).range := fun b =>
    t6psuh_isSolvable_range_blockRestrict_of_not_good hq H b.1 b.2 φ hφU
  haveI : Group.IsSolvable ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) := t6psl_isSolvable_pi
  haveI : Group.IsSolvable ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) := inferInstance
  let ψ : ↥C →* ((b : primaryFactors (x : Module.End K (Fin n → K))) →
      (AdjoinRoot (b : K[X]))ˣ) × ((b : {b : primaryFactors (x : Module.End K (Fin n → K)) //
      ¬ IsGoodBlock h x b}) → ↥(ρ b).range) :=
    MonoidHom.prod (MonoidHom.pi fun b => (blockDetHom x (b : K[X])).comp φ)
      (MonoidHom.pi fun b => (ρ b).rangeRestrict)
  have hker : ∀ g : ↥C, ψ g = 1 → (g : ↥(gramSU h (idGram K n))) ∈
      ⨆ i : t6psub_Idx h n B, t6psub_block B i := by
    intro g hg
    have hy := hφU g
    have hdet : ∀ b : primaryFactors (x : Module.End K (Fin n → K)),
        blockDetHom x (b : K[X]) ⟨t6psuh_toLinSU h n g, hy.2⟩ = 1 := fun b =>
      congrFun (congrArg Prod.fst hg) b
    have hbad : ∀ b : primaryFactors (x : Module.End K (Fin n → K)), ¬ IsGoodBlock h x b →
        blockRestrict x (b : K[X]) ⟨t6psuh_toLinSU h n g, hy.2⟩ = 1 := fun b hb =>
      congrArg Subtype.val (congrFun (congrArg Prod.snd hg) ⟨b, hb⟩)
    have hmem := t6psuh_mem_iSup_specialBlock_of_blocks H hy hdet hbad
    have hmapsup : (⨆ i : t6psub_Idx h n B, t6psub_block B i).map (t6psuh_toLinSU h n) =
        ⨆ a' : {a' : primaryFactors (x : Module.End K (Fin n → K)) // IsGoodBlock h x a'},
          specialBlock (idForm h n) x (a'.1 : K[X]) := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => t6psub_map_block B H i
    have hk : t6psuh_toLinSU h n g ∈ (⨆ i : t6psub_Idx h n B, t6psub_block B i).map
        (t6psuh_toLinSU h n) := by
      rw [hmapsup]
      exact hmem
    obtain ⟨s, hs, hs'⟩ := hk
    have : s = g := t6psuh_toLinSU_injective hs'
    rw [← this]
    exact hs
  obtain ⟨k, hk⟩ := t6psl_derived_le_ker ψ
  exact ⟨k, fun g hg => hker g (MonoidHom.mem_ker.1 (hk hg))⟩

theorem t6psub_isSolvable_fix_of_no_good (B : primeFormUnitary h (idGram K n))
    (H : UnitaryPrimaryData h.bar (idForm h n) (t6psub_toLin B))
    (hno : ∀ b : primaryFactors ((t6psub_toLin B : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)), ¬ IsGoodBlock h (t6psub_toLin B) b) :
    Group.IsSolvable ↥(fixSubgroup (t6psub_actSU h n B)) := by
  obtain ⟨k, hk⟩ := t6psub_derived B H
  have hempty : IsEmpty (t6psub_Idx h n B) := ⟨fun i => hno i.1 i.2⟩
  refine ⟨⟨k, ?_⟩⟩
  rw [eq_bot_iff]
  intro x hx
  have := hk x hx
  rw [iSup_of_empty, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact Subtype.ext this

end Blocks

end CFSG.HardMathSupport.Dickson.Sec6.I1431
