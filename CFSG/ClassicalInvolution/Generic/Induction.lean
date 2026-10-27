module

public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalInvolution.Generic.LineModel
public import CFSG.LieType.Universal.Catalog
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs

public section

namespace CFSG.ClassicalInvolution.Generic

open CFSG.Open CFSG.LieType CFSG.LieType.Universal
open scoped MatrixGroups

section Models

@[expose] def IsFundTag : CFSG.Assembly.LowTwoRank.StatedLieTag → Prop
  | .PSL | .PSU | .PSp | .POmegaOdd | .POmegaPlus | .POmegaMinus
  | .G2 | .F4 | .E6 | .E7 | .E8 | .twistedE6 | .trialityD4 => True
  | _ => False

@[expose] noncomputable def modelUniv (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n p f : ℕ) (hp : p.Prime) : LieUniversal :=
  haveI : Fact p.Prime := ⟨hp⟩
  match t with
  | .G2 =>
    ⟨↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 (GaloisField p f)),
      CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p f)⟩
  | .trialityD4 =>
    ⟨↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
        (iterateFrobenius (GaloisField p (3 * f)) p f)),
      CFSG.LieType.Steinberg.TwistedD4.twistedDatum
        (iterateFrobenius (GaloisField p (3 * f)) p f)⟩
  | _ => lieUniversal t n p f hp

variable {K : Type} [Group K]

open CFSG.LieType.RootSystem in
@[expose] def IsLongestRoot (D : UniversalRootDatum K) (γ : Fin D.rank → ℤ) : Prop :=
  γ ∈ D.roots ∧ ∀ δ ∈ D.roots,
    form D.isFiniteType (toRat δ) (toRat δ) ≤ form D.isFiniteType (toRat γ) (toRat γ)

@[expose] def fundamentalSubgroups (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (D : UniversalRootDatum K) : Set (Subgroup K) :=
  {R | ∃ (g : K) (γ : Fin D.rank → ℤ),
    (IsLongestRoot D γ ∨ (t = .G2 ∧ γ ∈ D.roots) ∨ (t = .trialityD4 ∧ γ ∈ D.roots)) ∧
    R = conjSub g (D.rootGroup γ ⊔ D.rootGroup (-γ))}

@[expose] def FundamentalSingleClass (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (D : UniversalRootDatum K) : Prop :=
  ∀ R ∈ fundamentalSubgroups t D, ∀ R' ∈ fundamentalSubgroups t D, ∃ g : K, R' = conjSub g R

@[expose] def ModelClauseZero : Prop :=
  ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n p e : ℕ) (hp : p.Prime), IsFundTag t →
    CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p e →
    CFSG.Open.IsQuasisimple (modelUniv t n p e hp).K ∧
      CFSG.Blueprint.LieModel
        ((modelUniv t n p e hp).K ⧸ Subgroup.center (modelUniv t n p e hp).K) t n p e

end Models

section Class

variable (p f : ℕ) [Fact p.Prime] {Y : Type} [Group Y]

structure IsClassicalMember (L : Subgroup Y) (z : Y) : Prop where
  orderOf_eq_two : orderOf z = 2
  mem : z ∈ L
  perfect : Group.IsPerfect L
  subnormal : IsSubnormal L (Subgroup.centralizer ({z} : Set Y))
  nonempty_equiv : Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, GaloisField p f))

structure InClass (Λ : Set (Subgroup Y)) : Prop where
  nonempty : Λ.Nonempty
  conjInvariant : ConjInvariant Λ
  generated : ⨆ L ∈ Λ, L = ⊤
  classical : ∀ L ∈ Λ, ∃ z : Y, IsClassicalMember p f L z

variable {p f}

@[expose] def ExactMembers (Λ : Set (Subgroup Y)) : Prop :=
  ∀ L ∈ Λ, classicalInvolutionOddCore L = ⊥

theorem IsClassicalMember.nonempty_equiv_sl2 {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (hL : classicalInvolutionOddCore L = ⊥) :
    Nonempty (L ≃* SL(2, GaloisField p f)) := by
  obtain ⟨e⟩ := h.nonempty_equiv
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hL).trans QuotientGroup.quotientBot).symm.trans e⟩

@[expose] def restrictFamily (Λ : Set (Subgroup Y)) (H : Subgroup Y) : Set (Subgroup H) :=
  {L' | ∃ L ∈ Λ, L ≤ H ∧ L' = L.subgroupOf H}

@[expose] def centralizingMembers (Λ : Set (Subgroup Y)) (A : Set Y) : Set (Subgroup Y) :=
  {L | L ∈ Λ ∧ L ≤ Subgroup.centralizer A}

@[expose] def centralizingLayer (Λ : Set (Subgroup Y)) (A : Set Y) : Subgroup Y :=
  ⨆ L ∈ centralizingMembers Λ A, L

@[expose] def LocalOddCentral (Λ : Set (Subgroup Y)) (A : Set Y) : Prop :=
  classicalInvolutionOddCore ↥(centralizingLayer Λ A) ≤
    Subgroup.center ↥(centralizingLayer Λ A)

end Class

section LieSystem

variable (p f : ℕ) [Fact p.Prime]

structure LieSystemData (X : Type) [Group X] (Φ : Set (Subgroup X)) where
  card : ℕ
  tag : Fin card → CFSG.Assembly.LowTwoRank.StatedLieTag
  rank : Fin card → ℕ
  exp : Fin card → ℕ
  hom : ∀ i, (modelUniv (tag i) (rank i) p (exp i) Fact.out).K →* X
  isFundTag : ∀ i, IsFundTag (tag i)
  admissible : ∀ i, CFSG.Assembly.LowTwoRank.StatedLieAdmissible (tag i) (rank i) p (exp i)
  exp_eq : ∀ i, exp i = f ∨ (tag i = .trialityD4 ∧ 3 * exp i = f)
  ker_le_center : ∀ i, (hom i).ker ≤ Subgroup.center _
  commute : ∀ i j, i ≠ j → ∀ x y, hom i x * hom j y = hom j y * hom i x
  generate : ⨆ i, (hom i).range = ⊤
  fundamental : ∀ L ∈ Φ, ∃ i,
    ∃ R ∈ fundamentalSubgroups (tag i) (modelUniv (tag i) (rank i) p (exp i) Fact.out).D,
      L = R.map (hom i)
  meets : ∀ i,
    ∃ R ∈ fundamentalSubgroups (tag i) (modelUniv (tag i) (rank i) p (exp i) Fact.out).D,
      R.map (hom i) ∈ Φ

@[expose] def LieSystem (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop :=
  Nonempty (LieSystemData p f X Φ)

theorem LieSystem.of_empty {X : Type} [Group X] [Subsingleton X] {Φ : Set (Subgroup X)}
    (hΦ : Φ = ∅) : LieSystem p f X Φ :=
  ⟨{ card := 0
     tag := fun i => i.elim0
     rank := fun i => i.elim0
     exp := fun i => i.elim0
     hom := fun i => i.elim0
     isFundTag := fun i => i.elim0
     admissible := fun i => i.elim0
     exp_eq := fun i => i.elim0
     ker_le_center := fun i => i.elim0
     commute := fun i => i.elim0
     generate := by
       rw [eq_top_iff]
       intro x _
       rw [Subsingleton.elim x 1]
       exact Subgroup.one_mem _
     fundamental := by simp [hΦ]
     meets := fun i => i.elim0 }⟩

variable {Y : Type} [Group Y]

@[expose] def oddQuotientFamily (Λ : Set (Subgroup Y)) :
    Set (Subgroup (Y ⧸ classicalInvolutionOddCore Y)) :=
  Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) '' Λ

@[expose] def LieSystemMod (Λ : Set (Subgroup Y)) : Prop :=
  LieSystem p f (Y ⧸ classicalInvolutionOddCore Y) (oddQuotientFamily Λ)

@[expose] def LocalLieSystems (Λ : Set (Subgroup Y)) : Prop :=
  ∀ A : Set Y, ¬ A ⊆ Subgroup.center Y →
    LieSystemMod p f (restrictFamily (centralizingMembers Λ A) (centralizingLayer Λ A))

end LieSystem

section Components

variable {p f : ℕ} [Fact p.Prime] {X : Type} [Group X] {Φ : Set (Subgroup X)}

namespace LieSystemData

variable (D : LieSystemData p f X Φ)

noncomputable def comp (i : Fin D.card) : Subgroup X := (D.hom i).range

theorem comp_commute {i j : Fin D.card} (h : i ≠ j) : Commutes (D.comp i) (D.comp j) := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact D.commute i j h a b

theorem iSup_comp : ⨆ i, D.comp i = ⊤ := D.generate

theorem comp_inf_le_center {i j : Fin D.card} (h : i ≠ j) :
    D.comp i ⊓ D.comp j ≤ Subgroup.center X := by
  rintro x ⟨hxi, hxj⟩
  have key : ∀ k, D.comp k ≤ Subgroup.centralizer ({x} : Set X) := by
    intro k y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hki : k = i
    · subst hki
      exact D.comp_commute h y hy x hxj
    · exact D.comp_commute hki y hy x hxi
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (⨆ k, D.comp k : Subgroup X) := by rw [D.iSup_comp]; trivial
  exact Subgroup.mem_centralizer_singleton_iff.mp ((iSup_le key) hg)

theorem comp_normal (i : Fin D.card) : (D.comp i).Normal := by
  have key : ∀ g ∈ (⨆ k, D.comp k : Subgroup X), ∀ n ∈ D.comp i, g * n * g⁻¹ ∈ D.comp i := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.comp k).mul_mem ((D.comp k).mul_mem hy hn) ((D.comp k).inv_mem hy)
      · have := D.comp_commute hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.iSup_comp]
  trivial

theorem exists_comp_of_mem {L : Subgroup X} (hL : L ∈ Φ) : ∃ i, L ≤ D.comp i := by
  obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
  exact ⟨i, Subgroup.map_le_range _ _⟩

theorem map_mem_of_single_class (hΦ : ConjInvariant Φ) (i : Fin D.card)
    (hsingle : FundamentalSingleClass (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D)
    {R : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K}
    (hR : R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D) :
    R.map (D.hom i) ∈ Φ := by
  obtain ⟨R₀, hR₀, hmem⟩ := D.meets i
  obtain ⟨g, rfl⟩ := hsingle R₀ hR₀ R hR
  have := hΦ (D.hom i g) _ hmem
  rwa [conjSub_map] at this

end LieSystemData

variable {X' : Type} [Group X']

noncomputable def LieSystemData.congr (e : X ≃* X') (D : LieSystemData p f X Φ) :
    LieSystemData p f X' (Subgroup.map e.toMonoidHom '' Φ) where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom i := e.toMonoidHom.comp (D.hom i)
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩

theorem LieSystem.congr (e : X ≃* X') (h : LieSystem p f X Φ) :
    LieSystem p f X' (Subgroup.map e.toMonoidHom '' Φ) :=
  h.map (LieSystemData.congr e)

variable {Y Y' : Type} [Group Y] [Group Y']

theorem LieSystemMod.congr (e : Y ≃* Y') {Λ : Set (Subgroup Y)} (h : LieSystemMod p f Λ) :
    LieSystemMod p f (Subgroup.map e.toMonoidHom '' Λ) := by
  have hO : (classicalInvolutionOddCore Y).map e.toMonoidHom = classicalInvolutionOddCore Y' :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  let q : Y ⧸ classicalInvolutionOddCore Y ≃* Y' ⧸ classicalInvolutionOddCore Y' :=
    QuotientGroup.congr _ _ e hO
  have key : oddQuotientFamily (Subgroup.map e.toMonoidHom '' Λ) =
      Subgroup.map q.toMonoidHom '' oddQuotientFamily Λ := by
    ext L'
    simp only [oddQuotientFamily, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
      refine ⟨_, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
      refine ⟨_, ⟨L, hL, rfl⟩, ?_⟩
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
  rw [LieSystemMod, key]
  exact LieSystem.congr q h

theorem conjInvariant_oddQuotientFamily {Λ : Set (Subgroup Y)} (h : ConjInvariant Λ) :
    ConjInvariant (oddQuotientFamily Λ) := by
  rintro n _ ⟨L, hL, rfl⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ n
  exact ⟨conjSub y L, h y L hL, (conjSub_map (QuotientGroup.mk' _) y L).symm⟩

end Components

section Induction

variable (p f : ℕ) [Fact p.Prime]

@[expose] def CITInductiveU : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)),
    InClass p f Λ → LieSystemMod p f Λ

@[expose] def CITBelowU (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ Λ : Set (Subgroup Y), InClass p f Λ → LieSystemMod p f Λ

theorem CITBelowU.mono {m n : ℕ} (h : m ≤ n) (hn : CITBelowU p f n) : CITBelowU p f m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

@[expose] def CITStepU (n : ℕ) : Prop :=
  p ≠ 2 → 5 ≤ p ^ f → CITBelowU p f n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ Λ : Set (Subgroup Y), InClass p f Λ → LieSystemMod p f Λ

theorem citInductiveU_of_step (h : ∀ n, CITStepU p f n) : CITInductiveU p f := by
  intro hp hq
  have key : ∀ n, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
      ∀ Λ : Set (Subgroup Y), InClass p f Λ → LieSystemMod p f Λ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y _ _ hY Λ hΛ
      exact h n hp hq (fun Y' _ _ hlt Λ' hΛ' => ih _ hlt Y' rfl Λ' hΛ') Y hY Λ hΛ
  intro Y _ _ Λ hΛ
  exact key _ Y rfl Λ hΛ

end Induction

end CFSG.ClassicalInvolution.Generic
