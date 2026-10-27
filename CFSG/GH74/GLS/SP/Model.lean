module

public import CFSG.GH74.GLS.SP.SpRoots
public import CFSG.GH74.GLS.SP.SpBN
public import CFSG.ClassicalGroups.Symplectic.Simple

public noncomputable section

namespace CFSG.GH74.GLS.SP

open CFSG.GH74.BNPair CFSG.LieType.Universal.Symplectic CFSG.LieType.Steinberg
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Pre

variable (F : Type) [Field F]

abbrev spW₁ : WeylGroup (spB F) (spN F) :=
  ((spNRep F 0 : spN F) : WeylGroup (spB F) (spN F))

abbrev spW₂ : WeylGroup (spB F) (spN F) :=
  ((spNRep F 1 : spN F) : WeylGroup (spB F) (spN F))

theorem spActsAs (i : Fin 2) {m : spN F}
    (h : (m : WeylGroup (spB F) (spN F)) =
      ((spNRep F i : spN F) : WeylGroup (spB F) (spN F))) :
    ActsAs (rootDatum 2 F) (m : StatedSp 2 F)
      ((coxeterMatrix (rootDatum 2 F).isFiniteType).toCoxeterSystem.simple i) :=
  actsAs_of_mk_eq (D := rootDatum 2 F) (n := weylRep 2 F) (H := torus 2 F) (isCTGroupDatum 2 F)
    (steinbergExtras 2 F) (_hN := spCartan_normal F) h

theorem spRootGroupSystem :
    IsRootGroupSystem (spB F) (spN F) (spW₁ F) (spW₂ F) (spU F) 4 (octGroup F) where
  ne_bot := (spOctagon F).ne_bot
  invariant i hi h hh x hx := (spOctagon F).invariant i hi h (by rwa [spB_inf_spN F] at hh) x hx
  carrier_eq := (spOctagon F).carrier_eq
  unique := (spOctagon F).unique
  reverse_eq := (spOctagon F).reverse_eq
  subgroup := (spOctagon F).subgroup
  action₁ m hm := by
    obtain ⟨a1, a2, a3⟩ := spAction₁ F (spActsAs F 0 hm)
    exact ⟨a1, a2, fun i h2 h4 => a3 i h2 (by exact_mod_cast h4)⟩
  action₂ m hm := spAction₂' F (spActsAs F 1 hm)
  meet_one := (spOctagon F).meet_one

@[expose] def spPre : PreRankTwoSystem (StatedSp 2 F) 4 where
  B := spB F
  N := spN F
  w₁ := spW₁ F
  w₂ := spW₂ F
  U := spU F
  root := octGroup F
  isTits := spIsTitsSystem F (isNilpotent_spU F)
  w₁_ne_w₂ := spNRep_ne F
  isSplit := spIsSplit F (isNilpotent_spU F)
  isSaturated := spIsSaturated F (spBruhatExtras F)
  card_weyl := by rw [card_weyl_sp F]
  three_le := by norm_num
  roots := spRootGroupSystem F

end Pre

section Quotient

variable (F : Type) [Field F]

@[expose] def spProj : StatedSp 2 F →* StatedProj (StatedSp 2 F) :=
  QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F))

theorem spProj_surjective : Function.Surjective (spProj F) :=
  QuotientGroup.mk'_surjective _

theorem ker_spProj : (spProj F).ker = Subgroup.center (StatedSp 2 F) := by
  rw [spProj, QuotientGroup.ker_mk', center_eq 2 F]

theorem ker_spProj_le : (spProj F).ker ≤ spB F ⊓ spN F := by
  rw [ker_spProj, spB_inf_spN]
  exact center_le_spT F

theorem spU_inf_ker : spU F ⊓ (spProj F).ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxT : x ∈ spT F := by
    have := hx.2
    rw [ker_spProj] at this
    exact center_le_spT F this
  have h : spT F ⊓ spU F = ⊥ := (steinbergExtras 2 F).torus_inf_posPart
  have hx' : x ∈ spT F ⊓ spU F := ⟨hxT, hx.1⟩
  rw [h] at hx'
  exact hx'

@[expose] def modelPre : PreRankTwoSystem (StatedProj (StatedSp 2 F)) 4 :=
  (spPre F).map (spProj F) (spProj_surjective F) (ker_spProj_le F) (spU_inf_ker F)

theorem isSimpleGroup_model (hF : 4 ≤ Nat.card F) : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
  CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
    (Or.inl (Or.inr hF))

@[expose] def modelSystem (hF : 4 ≤ Nat.card F) : RankTwoSystem (StatedProj (StatedSp 2 F)) 4 :=
  haveI := isSimpleGroup_model F hF
  (modelPre F).toSystemOfSimple

theorem modelSystem_root (hF : 4 ≤ Nat.card F) (i : ℤ) :
    (modelSystem F hF).root i = (octGroup F i).map (spProj F) :=
  rfl

theorem modelSystem_U (hF : 4 ≤ Nat.card F) :
    (modelSystem F hF).U = (spU F).map (spProj F) :=
  rfl

end Quotient

end CFSG.GH74.GLS.SP
