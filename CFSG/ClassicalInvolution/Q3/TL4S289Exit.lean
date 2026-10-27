module

public import CFSG.ClassicalInvolution.Q3.TL4S289Kind2
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3
public import CFSG.ClassicalInvolution.Q3.TL4S289Brg
public import CFSG.ClassicalInvolution.Q3.TL4SecIdMu

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def ExitIdent3 {X : Type} [Group X] (Φ : Set (Subgroup X)) : Prop :=
  ∃ L : Subgroup X, L.Normal ∧ (∀ K ∈ Φ, ∀ a : X, IsUniqueInvolution K a → a ∈ L) ∧
    ((IsSimpleGroup ↥L ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel ↥L .PSL 3 p f ∨ LieModel ↥L .PSU 3 p f)) ∨
      (Group.IsPerfect ↥L ∧ NativeSporadic.IsSporadic (↥L ⧸ Subgroup.center ↥L) .M12))

@[expose] def SecIdExitS3Ident (n : ℕ) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nat.card X < n → ∀ Φ : Set (Subgroup X), TypeRFam 3 Φ →
    classicalInvolutionOddCore X = ⊥ → omegaGen Φ = ⊤ →
    (∀ L ∈ Φ, ∀ L' ∈ Φ, ∃ g : X, conjSub g L = L') → SecIdExitS3 Φ → ExitIdent3 Φ

@[expose] def SecIdE3L2NoStar : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (R : Subgroup X) (S : Sylow 2 R) (z : X),
    EdgelessMember3 R S z → IsSimpleGroup ↥(genFittingFStar X) →
      (genFittingFStar X).index ≤ 2 → ∀ p f : ℕ, p.Prime → p ≠ 2 → Even f →
        LieModel (FStarQuot X) .PSL 2 p f →
          ∀ L ∈ CoreAssembly.conjClass (tightCore R),
            omegaStarNbr (CoreAssembly.conjClass (tightCore R)) L = ∅

namespace S289

section Groups

open scoped commutatorElement

variable {Q : Type} [Group Q]

theorem isQuasisimple_of_perfect (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : CFSG.IsQuasisimple Q := by
  refine ⟨hperf, hs, ?_⟩
  by_contra hno
  push Not at hno
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
    exact hno _ _
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  obtain ⟨y, hy⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  apply hy
  rw [QuotientGroup.eq_one_iff, hle]
  exact Subgroup.mem_top y0

theorem isPerfect_of_simple (hs : IsSimpleGroup Q) (hZ : Subgroup.center Q = ⊥) :
    Group.IsPerfect Q := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    apply hx
    have hc : x ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun y => by
      have h1 : ⁅y, x⁆ ∈ commutator Q :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x)
      rwa [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [hZ] at hc
    exact Subgroup.mem_bot.mp hc
  · exact ⟨h⟩

theorem isSimpleGroup_of_lieModel3 {p f : ℕ}
    (h : LieModel Q .PSL 3 p f ∨ LieModel Q .PSU 3 p f) : IsSimpleGroup Q := by
  rcases h with h | h
  · rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact (LieType.Simplicity.fam_PSL_simplicity Q 3 p f h).2
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · cases ht
  · rcases h with ⟨-, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact (ClassicalGroups.Unitary.fam_PSU_simplicity Q 3 p f h).2
    · simp [chevalleyExceptionalTags] at ht
    · simp [reeTitsTags] at ht
    · cases ht

theorem eq_of_le_of_exitType {C L₀ : Subgroup Q}
    (hC : IsComponent C)
    (ht : (IsSimpleGroup ↥L₀ ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel ↥L₀ .PSL 3 p f ∨ LieModel ↥L₀ .PSU 3 p f)) ∨
      (Group.IsPerfect ↥L₀ ∧ NativeSporadic.IsSporadic (↥L₀ ⧸ Subgroup.center ↥L₀) .M12))
    (hle : C ≤ L₀) : C = L₀ := by
  have hsub : (C.subgroupOf L₀).IsSubnormal := Subgroup.IsSubnormal.subgroupOf (K := L₀) hC.2
  suffices h : C.subgroupOf L₀ = ⊤ from le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h)
  rcases ht with ⟨hs, -⟩ | ⟨hperf, he⟩
  · rcases hsub.eq_bot_or_top_of_isSimpleGroup hs with h | h
    · exfalso
      have : Nontrivial ↥C := LocalCores.isQuasisimple_nontrivial hC.1
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥C)
      apply hx
      have h1 : (⟨(x : Q), hle x.2⟩ : ↥L₀) ∈ C.subgroupOf L₀ := Subgroup.mem_subgroupOf.mpr x.2
      rw [h, Subgroup.mem_bot] at h1
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    · exact h
  · obtain ⟨e⟩ := he
    have hM : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    have hq := isQuasisimple_of_perfect hperf e.isSimpleGroup
    exact eq_top_of_isComponent hq
      ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hC.1, hsub⟩

end Groups

variable {X : Type} [Group X] [Finite X]

theorem isSporadic_fstarQuot_of_center_quot
    (hsimp : IsSimpleGroup ↥(genFittingFStar X))
    (e : X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12) :
    NativeSporadic.IsSporadic (FStarQuot X) .M12 := by
  have hM : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  have hS : IsSimpleGroup (X ⧸ Subgroup.center X) := e.isSimpleGroup
  have hZ : Subgroup.center X ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hS.toNontrivial.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))
  have hFn : (genFittingFStar X).Normal := genFittingFStar_isNormal
  have hZF : Subgroup.center X ≤ genFittingFStar X := fun z hz =>
    centralizer_genFittingFStar_le (Subgroup.mem_centralizer_iff.mpr fun f _ =>
      (Subgroup.mem_center_iff.mp hz f))
  have hF : genFittingFStar X = ⊤ := by
    have hN' := hFn.map _ (QuotientGroup.mk'_surjective (Subgroup.center X))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((genFittingFStar X).map (QuotientGroup.mk' (Subgroup.center X))) with h | h
    · exfalso
      have hFZ : genFittingFStar X ≤ Subgroup.center X := by
        intro f hf
        have h1 : QuotientGroup.mk' (Subgroup.center X) f ∈
            (genFittingFStar X).map (QuotientGroup.mk' _) := ⟨f, hf, rfl⟩
        rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      apply hZ
      rw [eq_top_iff]
      intro g _
      exact hFZ (centralizer_genFittingFStar_le (Subgroup.mem_centralizer_iff.mpr fun f hf =>
        (Subgroup.mem_center_iff.mp (hFZ hf) g).symm))
    · rw [eq_top_iff]
      intro g _
      have h1 : QuotientGroup.mk' (Subgroup.center X) g ∈
          (genFittingFStar X).map (QuotientGroup.mk' _) := h ▸ Subgroup.mem_top _
      obtain ⟨f, hf, hfg⟩ := h1
      have h2 := (genFittingFStar X).mul_mem hf (hZF (QuotientGroup.eq.mp hfg))
      rwa [mul_inv_cancel_left] at h2
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hXs : IsSimpleGroup X := eF.symm.isSimpleGroup
  have hZX : Subgroup.center X = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right hZ
  have hZF' : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (f := eF.toMonoidHom) eF.injective]
    rw [show (Subgroup.center ↥(genFittingFStar X)).map eF.toMonoidHom = Subgroup.center X from
      Subgroup.map_center_eq eF, hZX]
  exact ⟨((((QuotientGroup.quotientMulEquivOfEq hZF').trans QuotientGroup.quotientBot).trans
    eF).trans ((QuotientGroup.quotientMulEquivOfEq hZX).trans
      QuotientGroup.quotientBot).symm).trans e⟩

theorem exitIdent3_of_fstar {Φ : Set (Subgroup X)}
    (hΦ : TypeRFam 3 Φ) (hsimp : IsSimpleGroup ↥(genFittingFStar X))
    (hidx : (genFittingFStar X).index ∣ 6)
    (hid : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel (FStarQuot X) .PSL 3 p f ∨ LieModel (FStarQuot X) .PSU 3 p f)) ∨
      NativeSporadic.IsSporadic (FStarQuot X) .M12) : ExitIdent3 Φ := by
  have hFn : (genFittingFStar X).Normal := genFittingFStar_isNormal
  have hQs : IsSimpleGroup (FStarQuot X) := by
    rcases hid with ⟨p, f, -, -, hk⟩ | he
    · exact isSimpleGroup_of_lieModel3 hk
    · obtain ⟨e⟩ := he
      have hM : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
        CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      exact e.isSimpleGroup
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal _).resolve_right fun h => ?_
    obtain ⟨a, b, hab⟩ := hQs.toNontrivial.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))
  let eZ : ↥(genFittingFStar X) ≃* FStarQuot X :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  refine ⟨genFittingFStar X, hFn, fun K hK a ha => ?_, ?_⟩
  · obtain ⟨σ, -, hσ4, rfl⟩ := exists_sq_eq_of_typeRFam hΦ hK ha
    exact sq_mem_of_index_dvd_six hidx hσ4
  · rcases hid with ⟨p, f, hp, hp2, hk⟩ | he
    · exact Or.inl ⟨hsimp, p, f, hp, hp2,
        hk.imp (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm)
          (LieType.CurtisTits.lieModel_of_mulEquiv eZ.symm)⟩
    · exact Or.inr ⟨isPerfect_of_simple hsimp hZ, he⟩

theorem exitIdent3_of_datum (hL2 : SecIdE3L2NoStar)
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam 3 Φ) (hst : ∃ L ∈ Φ, (omegaStarNbr Φ L).Nonempty)
    {R : Subgroup X} {S : Sylow 2 R} {z : X} (hm : EdgelessMember3 R S z)
    (heq : CoreAssembly.conjClass (tightCore R) = Φ)
    (hout : (¬ TightActs3 R z ∧ (Thm6Exit X ∨ TightTwisted X z)) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* NativeSporadic.Carrier .M12))
    (hsimp : IsSimpleGroup ↥(genFittingFStar X)) (hidx : (genFittingFStar X).index ∣ 6)
    (hntw : ¬ TightTwisted X z) : ExitIdent3 Φ := by
  refine exitIdent3_of_fstar hΦ hsimp hidx ?_
  rcases hout with ⟨-, hX | hX⟩ | he
  · rcases hX with ⟨p, f, hp, hp2, ⟨hf, hk, hidx2⟩ | ⟨hk, -⟩⟩ | ⟨hk, -⟩
    · exfalso
      obtain ⟨L, hL, hne⟩ := hst
      have h1 := hL2 X R S z hm hsimp hidx2 p f hp hp2 hf hk L (heq ▸ hL)
      rw [heq] at h1
      rw [h1] at hne
      exact Set.not_nonempty_empty hne
    · exact Or.inl ⟨p, f, hp, hp2, hk⟩
    · exact Or.inr hk
  · exact absurd hX hntw
  · obtain ⟨e⟩ := he
    exact Or.inr (isSporadic_fstarQuot_of_center_quot hsimp e)

end S289

theorem secIdExitS3Ident_of (hE3 : SecIdE3MuS3)
    (hL2 : SecIdE3L2NoStar) (n : ℕ) (h6 : Thm6RBelow 3 n) : SecIdExitS3Ident n := by
  intro X _ _ hX Φ hΦ _ _ _ h
  obtain ⟨hed, hst, R, S, z, hm, heq, hO2, hout⟩ := h
  have hmu : MuS3Member R := fun W hW => Q3T6.Mu.muIsoS3_of_shape hm.datum.partIHypG hW
    (heq ▸ hed) (heq ▸ hst)
  obtain ⟨hsimp, hidx, hntw⟩ :=
    hE3 X (fun Y _ _ hY => h6 Y (hY.trans hX)) R S z hm hmu hO2 hout
  exact S289.exitIdent3_of_datum hL2 hΦ hst hm heq hout hsimp hidx hntw

end CFSG.ClassicalInvolution.Q3.TL4
