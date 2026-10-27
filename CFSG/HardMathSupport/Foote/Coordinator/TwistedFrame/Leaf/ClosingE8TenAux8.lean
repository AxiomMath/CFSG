module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux7
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenData2

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


theorem mem_frame_iff' {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8}
    (D : LangLevi Tag.E8 K w) (S : Set (Fin Tag.E8.rank → ℤ)) (x : ModGL Tag.E8 K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup Tag.E8 K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan Tag.E8 D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

theorem g_mem_adjointGroup' {K : Type} [Field K] [Finite K] {w : WeylGroup Tag.E8}
    (D : LangLevi Tag.E8 K w) : D.g ∈ adjointGroup Tag.E8 D.L :=
  Pθ_le_adjointGroup Tag.E8 D.L (Lθ_le_Pθ Tag.E8 D.L D.g_mem)

@[expose] def w8 : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd TwClass.wordE8Ten

theorem w8_eq : TwClass.e8Ten.w = w8 := rfl

theorem w_smul (γ : Fin Tag.E8.rank → ℤ) : w8 • γ = wm.mulVec γ :=
  wordProd_smul_eq_wordMat_mulVec Tag.E8 TwClass.wordE8Ten γ

theorem pinnedX_commute_of_not_root {R : Type} [CommRing R] {β₁ β₂ : Fin Tag.E8.rank → ℤ}
    (h₁ : β₁ ∈ rootFinset Tag.E8) (h₂ : β₂ ∈ rootFinset Tag.E8) (hne : β₁ ≠ β₂) (hne' : β₁ ≠ -β₂)
    (hs : β₁ + β₂ ∉ rootFinset Tag.E8) (s t : R) :
    pinnedX Tag.E8 R β₁ s * pinnedX Tag.E8 R β₂ t = pinnedX Tag.E8 R β₂ t * pinnedX Tag.E8 R β₁ s :=
  ((simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
    (mem_rootFinset.1 h₁) (mem_rootFinset.1 h₂) hne hne').2 (fun h => hs (mem_rootFinset.2 h)) R
    (pinnedX Tag.E8 R β₁ s) (mem_rootSubgroup.2 ⟨s, rfl⟩) (pinnedX Tag.E8 R β₂ t)
    (mem_rootSubgroup.2 ⟨t, rfl⟩))

theorem pinnedX_A2_rel {R : Type} [CommRing R] {β₁ β₂ β₃ : Fin Tag.E8.rank → ℤ}
    (h₁ : β₁ ∈ rootFinset Tag.E8) (h₂ : β₂ ∈ rootFinset Tag.E8) (h₃ : β₃ = β₁ + β₂)
    (hs : β₃ ∈ rootFinset Tag.E8) (hne : β₁ ≠ β₂) (hne' : β₁ ≠ -β₂)
    (h31 : β₃ + β₁ ∉ rootFinset Tag.E8) (h32 : β₃ + β₂ ∉ rootFinset Tag.E8)
    (n31 : β₃ ≠ β₁) (n31' : β₃ ≠ -β₁) (n32 : β₃ ≠ β₂) (n32' : β₃ ≠ -β₂) :
    ∃ η : R, ∀ a b : R, pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b =
      pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₃ (η * a * b) := by
  subst h₃
  obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} Tag.E8 (Or.inr (Or.inr (Or.inr rfl)))
    (mem_rootFinset.1 h₁) (mem_rootFinset.1 h₂) hne hne').1 (mem_rootFinset.1 hs)
  refine ⟨-(commConst Tag.E8 β₁ β₂ (1, 1) : R), fun a b => ?_⟩
  have hc₁ : ∀ s b : R, pinnedX Tag.E8 R (β₁ + β₂) s * pinnedX Tag.E8 R β₁ b =
      pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R (β₁ + β₂) s := fun s b =>
    pinnedX_commute_of_not_root hs h₁ n31 n31' h31 s b
  have hc₂ : ∀ s a : R, pinnedX Tag.E8 R (β₁ + β₂) s * pinnedX Tag.E8 R β₂ a =
      pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R (β₁ + β₂) s := fun s a =>
    pinnedX_commute_of_not_root hs h₂ n32 n32' h32 s a
  have hf := hform R b a
  rw [commutatorElement_def] at hf
  have h1 : pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a =
      pinnedX Tag.E8 R (β₁ + β₂) ((commConst Tag.E8 β₁ β₂ (1, 1) : R) * b * a) *
        (pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b) := by
    rw [← hf]
    group
  have h2 : pinnedX Tag.E8 R β₂ a * pinnedX Tag.E8 R β₁ b =
      pinnedX Tag.E8 R (β₁ + β₂) (-((commConst Tag.E8 β₁ β₂ (1, 1) : R) * b * a)) *
        (pinnedX Tag.E8 R β₁ b * pinnedX Tag.E8 R β₂ a) := by
    rw [h1, ← mul_assoc, ← pinnedX_add, neg_add_cancel, pinnedX_zero, one_mul]
  rw [h2, ← mul_assoc, hc₁, mul_assoc, hc₂, ← mul_assoc]
  congr 3
  ring

theorem gens12_cases : ∀ γ ∈ gens12, γ = Pi.single 0 1 ∨ γ = Pi.single 1 1 ∨ γ = Pi.single 2 1 ∨
    γ = Pi.single 3 1 ∨ γ = Pi.single 5 1 ∨ γ = Pi.single 6 1 ∨ γ = -Pi.single 0 1 ∨
    γ = -Pi.single 1 1 ∨ γ = -Pi.single 2 1 ∨ γ = -Pi.single 3 1 ∨ γ = -Pi.single 5 1 ∨
    γ = -Pi.single 6 1 := by decide +kernel

section Generic

namespace Setup

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [IsAlgClosed L]
  (S : Setup K L) (hw : ∀ γ, S.w • γ = wm.mulVec γ)

include hw

theorem Einv_fixedRoot (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ fixedRoots)
    (hγX : ∀ t, pinnedX Tag.E8 L γ t ∈ Xbar) :
    ∀ u ∈ Uspace S.h S.H, Eop aE8 γ u ∈ Uspace S.h S.H := by
  obtain ⟨hlx, hfix⟩ := fixedRoots_data γ hγ
  obtain ⟨hr, h0, -⟩ := lxRoots_data γ hlx
  exact S.Einv_fixed Xbar hX hr h0 (by rw [hw]; exact hfix) hγX

theorem Einv_perpPair (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {p : (Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)} (hp : p ∈ perpPairs)
    (hX₁ : ∀ t, pinnedX Tag.E8 L p.1 t ∈ Xbar) (hX₂ : ∀ t, pinnedX Tag.E8 L p.2 t ∈ Xbar) :
    (∀ u ∈ Uspace S.h S.H, Eop aE8 p.1 u ∈ Uspace S.h S.H) ∧
      (∀ u ∈ Uspace S.h S.H, Eop aE8 p.2 u ∈ Uspace S.h S.H) := by
  obtain ⟨h1, h2, hw1, hw2, hne, hne', hs⟩ := perpPairs_data p hp
  obtain ⟨hr1, h01, -⟩ := lxRoots_data p.1 h1
  obtain ⟨hr2, h02, -⟩ := lxRoots_data p.2 h2
  exact S.Einv_perp Xbar hX hr1 h01 hr2 h02 (by rw [hw]; exact hw1) (by rw [hw]; exact hw2)
    (fun s t => pinnedX_commute_of_not_root hr1 hr2 hne hne' hs s t) hX₁ hX₂

theorem Einv_a2Triple (Xbar : Subgroup (ModGL Tag.E8 L)) (hX : S.XLink Xbar)
    {t : (Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ) × (Fin Tag.E8.rank → ℤ)}
    (ht : t ∈ a2Triples) (hX₁ : ∀ s, pinnedX Tag.E8 L t.1 s ∈ Xbar)
    (hX₂ : ∀ s, pinnedX Tag.E8 L t.2.1 s ∈ Xbar) (hX₃ : ∀ s, pinnedX Tag.E8 L t.2.2 s ∈ Xbar)
    (hE₃ : ∀ u ∈ Uspace S.h S.H, Eop aE8 t.2.2 u ∈ Uspace S.h S.H) :
    (∀ u ∈ Uspace S.h S.H, Eop aE8 t.1 u ∈ Uspace S.h S.H) ∧
      (∀ u ∈ Uspace S.h S.H, Eop aE8 t.2.1 u ∈ Uspace S.h S.H) := by
  obtain ⟨h1, h2, h3, hw1, hw2, hw3, hsum, hne, hne', h31, h32, n31, n31', n32, n32'⟩ :=
    a2Triples_data t ht
  obtain ⟨hr1, h01, -⟩ := lxRoots_data t.1 h1
  obtain ⟨hr2, h02, -⟩ := lxRoots_data t.2.1 h2
  obtain ⟨hr3, -, -⟩ := lxRoots_data t.2.2 h3
  obtain ⟨η, hη⟩ := pinnedX_A2_rel (R := L) hr1 hr2 hsum.symm hr3 hne hne' h31 h32 n31 n31'
    n32 n32'
  exact S.Einv_A2 Xbar hX hr1 h01 hr2 h02 h3 (by rw [hw]; exact hw1) (by rw [hw]; exact hw2)
    (by rw [hw]; exact hw3) η hη hX₁ hX₂ hX₃ hE₃

theorem invE_pos (Xa Xb : Subgroup (ModGL Tag.E8 L)) (hXa : S.XLink Xa) (hXb : S.XLink Xb)
    (ha : ∀ γ ∈ listA, ∀ t, pinnedX Tag.E8 L γ t ∈ Xa)
    (hb : ∀ γ ∈ listB, ∀ t, pinnedX Tag.E8 L γ t ∈ Xb) :
    InvE (Uspace S.h S.H) := by
  refine ⟨fun u hu ν hν => Uspace_supp S.h S.H hu ν (fun hh => hν (mem_deg1Roots.2 hh)), ?_⟩
  have f1 := S.Einv_fixedRoot hw Xa hXa
    (γ := (Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E8.rank → ℤ)) (by simp [fixedRoots])
    (ha _ (by simp [listA]))
  have f1n := S.Einv_fixedRoot hw Xa hXa
    (γ := (-(Pi.single 2 1 + Pi.single 3 1) : Fin Tag.E8.rank → ℤ)) (by simp [fixedRoots])
    (ha _ (by simp [listA]))
  have f2 := S.Einv_fixedRoot hw Xb hXb
    (γ := (Pi.single 5 1 + Pi.single 6 1 : Fin Tag.E8.rank → ℤ)) (by simp [fixedRoots])
    (hb _ (by simp [listB]))
  have f2n := S.Einv_fixedRoot hw Xb hXb
    (γ := (-(Pi.single 5 1 + Pi.single 6 1) : Fin Tag.E8.rank → ℤ)) (by simp [fixedRoots])
    (hb _ (by simp [listB]))
  have p1 := S.Einv_perpPair hw Xa hXa
    (p := ((Pi.single 0 1 : Fin Tag.E8.rank → ℤ), (Pi.single 1 1 : Fin Tag.E8.rank → ℤ)))
    (by simp [perpPairs]) (ha _ (by simp [listA])) (ha _ (by simp [listA]))
  have p2 := S.Einv_perpPair hw Xa hXa
    (p := ((-Pi.single 0 1 : Fin Tag.E8.rank → ℤ), (-Pi.single 1 1 : Fin Tag.E8.rank → ℤ)))
    (by simp [perpPairs]) (ha _ (by simp [listA])) (ha _ (by simp [listA]))
  have t1 := S.Einv_a2Triple hw Xa hXa
    (t := ((Pi.single 2 1 : Fin Tag.E8.rank → ℤ), (Pi.single 3 1 : Fin Tag.E8.rank → ℤ),
      (Pi.single 2 1 + Pi.single 3 1 : Fin Tag.E8.rank → ℤ))) (by simp [a2Triples])
    (ha _ (by simp [listA])) (ha _ (by simp [listA])) (ha _ (by simp [listA])) f1
  have t2 := S.Einv_a2Triple hw Xa hXa
    (t := ((-Pi.single 2 1 : Fin Tag.E8.rank → ℤ), (-Pi.single 3 1 : Fin Tag.E8.rank → ℤ),
      (-(Pi.single 2 1 + Pi.single 3 1) : Fin Tag.E8.rank → ℤ))) (by simp [a2Triples])
    (ha _ (by simp [listA])) (ha _ (by simp [listA])) (ha _ (by simp [listA])) f1n
  have t3 := S.Einv_a2Triple hw Xb hXb
    (t := ((Pi.single 5 1 : Fin Tag.E8.rank → ℤ), (Pi.single 6 1 : Fin Tag.E8.rank → ℤ),
      (Pi.single 5 1 + Pi.single 6 1 : Fin Tag.E8.rank → ℤ))) (by simp [a2Triples])
    (hb _ (by simp [listB])) (hb _ (by simp [listB])) (hb _ (by simp [listB])) f2
  have t4 := S.Einv_a2Triple hw Xb hXb
    (t := ((-Pi.single 5 1 : Fin Tag.E8.rank → ℤ), (-Pi.single 6 1 : Fin Tag.E8.rank → ℤ),
      (-(Pi.single 5 1 + Pi.single 6 1) : Fin Tag.E8.rank → ℤ))) (by simp [a2Triples])
    (hb _ (by simp [listB])) (hb _ (by simp [listB])) (hb _ (by simp [listB])) f2n
  intro γ hγ
  rcases gens12_cases γ hγ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact p1.1
  · exact p1.2
  · exact t1.1
  · exact t1.2
  · exact t3.1
  · exact t3.2
  · exact p2.1
  · exact p2.2
  · exact t2.1
  · exact t2.2
  · exact t4.1
  · exact t4.2

theorem block_pos (Xa Xb : Subgroup (ModGL Tag.E8 L)) (hXa : S.XLink Xa) (hXb : S.XLink Xb)
    (ha : ∀ γ ∈ listA, ∀ t, pinnedX Tag.E8 L γ t ∈ Xa)
    (hb : ∀ γ ∈ listB, ∀ t, pinnedX Tag.E8 L γ t ∈ Xb)
    {u : Fn L} (hu : u ∈ Uspace S.h S.H) {μ : Fin Tag.E8.rank → ℤ} (hμ : μ ∈ mRoots)
    (h0 : u μ ≠ 0) :
    ∀ ν ∈ mRoots, (cls ν = cls μ ∨ cls ν = 5 - cls μ) →
      (Pi.single ν (1 : L) : Fn L) ∈ Uspace S.h S.H := by
  refine block_of_coord S.h S.H S.Fr S.hfix S.hlang S.hn (w := S.w) ?_ ?_
    (S.invE_pos hw Xa Xb hXa hXb ha hb) hu hμ h0
  · intro μ hμ
    refine ⟨S.sg μ * 1, ?_, Mg_single _ _ _ _⟩
    rw [mul_one]
    exact S.sg_ne_zero (mem_mRoots.1 hμ).1
  · intro μ hμ
    rw [hw]
    exact wm_mRoots μ hμ

end Setup

end Generic

section Inst

variable {K : Type} [Field K] [Finite K]

@[expose] def toSetup (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)
    (H : Subgroup (ModGL Tag.E8 K)) : Setup K D.L where
  Fr := D.Fr
  hFr := D.hFr
  hbij := by
    haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
    refine ⟨D.Fr.injective, fun c => ?_⟩
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (show 0 < Nat.card K from Nat.card_pos)
    exact ⟨d, by rw [D.hFr, hd]⟩
  h := D.g
  n := canonicalRep (coxeterSystem Tag.E8) D.L w8
  hh := g_mem_adjointGroup' D
  hlang := D.lang
  w := w8
  sg := sgn w8
  hm := mono_canonicalRep w8
  hθ := by
    rw [w_smul]
    exact wm_theta
  hD := fun μ hμ => by
    rw [w_smul]
    exact mem_deg1Roots.1 (wm_deg1 μ (mem_deg1Roots.2 hμ))
  H := H

variable (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w) (H : Subgroup (ModGL Tag.E8 K))

theorem toSetup_hw (γ : Fin Tag.E8.rank → ℤ) : (toSetup D H).w • γ = wm.mulVec γ := w_smul γ

theorem pinnedX_mem_S₂ {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8)
    (hs : ∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → γ i = 0) (t : D.L) :
    pinnedX Tag.E8 D.L γ t ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₂ :=
  pinnedX_mem_rootSpan (S := TwClass.e8Ten.S₂) ⟨mem_rootFinset.1 hγ, hs⟩ t

theorem pinnedX_mem_S₁ {γ : Fin Tag.E8.rank → ℤ} (hγ : γ ∈ rootFinset Tag.E8)
    (hs : ∀ α ∈ rootFinset Tag.E8,
      (∀ i : Fin Tag.E8.rank, i.val ∉ TwClass.e8Ten.J₂ → α i = 0) → iform γ α = 0) (t : D.L) :
    pinnedX Tag.E8 D.L γ t ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₁ :=
  pinnedX_mem_rootSpan (S := TwClass.e8Ten.S₁)
    ⟨mem_rootFinset.1 hγ, fun α hα => hs α (mem_rootFinset.2 hα.1) hα.2⟩ t

theorem xlink (S : Set (Fin Tag.E8.rank → ℤ)) (hH : D.frame S ≤ H) :
    (toSetup D H).XLink (rootSpan Tag.E8 D.L S) := by
  intro l₀ hl₀ hx
  exact hH ((mem_frame_iff' D S l₀).2 ⟨hl₀, hx⟩)

theorem listA_mem_S₂ : ∀ γ ∈ listA, ∀ t : D.L,
    pinnedX Tag.E8 D.L γ t ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₂ := by
  intro γ hγ t
  have hd := listA_data γ hγ
  exact pinnedX_mem_S₂ D hd.1 hd.2 t

theorem listB_mem_S₁ : ∀ γ ∈ listB, ∀ t : D.L,
    pinnedX Tag.E8 D.L γ t ∈ rootSpan Tag.E8 D.L TwClass.e8Ten.S₁ := by
  intro γ hγ t
  have hd := listB_data γ hγ
  exact pinnedX_mem_S₁ D hd.1 hd.2 t

variable [IsAlgClosed D.L]

theorem invE_e8Ten (h1 : D.frame TwClass.e8Ten.S₁ ≤ H) (h2 : D.frame TwClass.e8Ten.S₂ ≤ H) :
    InvE (Uspace D.g H) :=
  (toSetup D H).invE_pos (toSetup_hw D H) _ _ (xlink D H TwClass.e8Ten.S₂ h2)
    (xlink D H TwClass.e8Ten.S₁ h1) (listA_mem_S₂ D) (listB_mem_S₁ D)

theorem block_e8Ten (h1 : D.frame TwClass.e8Ten.S₁ ≤ H) (h2 : D.frame TwClass.e8Ten.S₂ ≤ H)
    {u : Fn D.L} (hu : u ∈ Uspace D.g H) {μ : Fin Tag.E8.rank → ℤ} (hμ : μ ∈ mRoots)
    (h0 : u μ ≠ 0) :
    ∀ ν ∈ mRoots, (cls ν = cls μ ∨ cls ν = 5 - cls μ) →
      (Pi.single ν (1 : D.L) : Fn D.L) ∈ Uspace D.g H :=
  (toSetup D H).block_pos (toSetup_hw D H) _ _ (xlink D H TwClass.e8Ten.S₂ h2)
    (xlink D H TwClass.e8Ten.S₁ h1) (listA_mem_S₂ D) (listB_mem_S₁ D) hu hμ h0

end Inst

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
