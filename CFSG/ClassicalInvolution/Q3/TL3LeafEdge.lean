module

public import CFSG.ClassicalInvolution.Q3.TL3LeafCore
public import CFSG.ClassicalInvolution.Q3.TL3Weak
public import CFSG.ClassicalInvolution.Q3.TL3Main
public import CFSG.ClassicalInvolution.Q3.Q3CLBasic
public import CFSG.ClassicalInvolution.TwoGroupCase.EscapeOdd

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

@[expose] def TightThm6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) →
        TwoSubgroupsFourGenerated (genFittingFStar G)

@[expose] def TightEdgeLarge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t →
      ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))

theorem tightEdgeLarge_of_tightThm6 (h : TightThm6) : TightEdgeLarge :=
  fun G _ _ _ hnab hlarge R S t hd hE => hlarge (h G hnab R S t hd hE)

theorem TightDatum.nonempty_omegaNbr_of_not_dEdgeless (h : TightDatum R S t)
    (hne : ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))) :
    (omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)).Nonempty := by
  have hΩ := h.hypOmegaGen
  simp only [Disconnected.DEdgeless, not_forall] at hne
  obtain ⟨K, hK, J, hJ, hadj⟩ := hne
  have hadj' := not_not.mp hadj
  have hJK : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) K := by
    rcases hadj' with h1 | h1
    · exact h1
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ hK h1
  obtain ⟨g, rfl⟩ := hK
  refine ⟨conjSub g⁻¹ J, ?_⟩
  have := omegaNbr_conj hΩ.conjInvariant hJK g⁻¹
  rwa [conjSub_inv_conjSub] at this

theorem TightDatum.not_dEdgeless_of_escape (h : TightDatum R S t) {T U : Subgroup G} {x : G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (e : Escape T U x) :
    ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) := by
  classical
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S h.quat h.mem h.order h.cent h.normal h.twoGroup
  set S0 : Subgroup G := (S : Subgroup R).map R.subtype with hS0
  have huniq := h.isUniqueInvolution_core
  have hΩ := h.hypOmegaGen
  have hS0K0 : S0 ≤ tightCore R := by
    intro s hs
    exact Subgroup.subset_closure ⟨d.S_le hs, d.S_two.to_le (Subgroup.zpowers_le.mpr hs)⟩
  have hSyl : IsSylow2In S0 (tightCore R) :=
    ⟨hS0K0, d.S_two, fun V hVK hV2 hle => d.sylow.2.2 V (hVK.trans (tightCore_le R)) hV2 hle⟩
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hJ : conjSub x (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨x, rfl⟩
  have hne : conjSub x (tightCore R) ≠ tightCore R := by
    intro heq
    have h1 : IsUniqueInvolution (conjSub x (tightCore R)) (x * t * x⁻¹) := huniq.conj x
    rw [heq] at h1
    exact d.t₁_ne hT e (huniq.eq h1).symm
  have hR' : conjSub x S0 ∈ RSet (CoreAssembly.conjClass (tightCore R)) :=
    RSet.conj hΩ.conjInvariant (mem_RSet_of_isSylow2In hK hSyl) x
  have hnbr : conjSub x (tightCore R) ∈
      omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    refine ⟨hJ, hne, conjSub x S0, hR', conjSub_mono hS0K0, fun y hy => ?_⟩
    have hy' : y ∈ conjSubgroup x S0 := mem_conjSubgroup_iff.mpr (mem_conjSub_iff.mp hy)
    have hty : t * y = y * t := d.commute_S_S₁ hT e t h.mem y hy'
    exact h.le_normalizer_core (Subgroup.mem_centralizer_singleton_iff.mpr hty.symm)
  intro hedge
  exact hedge (tightCore R) hK _ hJ (Or.inl hnbr)

theorem TightDatum.not_dEdgeless_of_not_sylow (h : TightDatum R S t) {T : Subgroup G}
    (hT : IsSylow2Of T
      (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)))
    (hnot : ¬ IsSylow2Of T ⊤) :
    ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R)) := by
  obtain ⟨U, hU, hTU⟩ := exists_isSylow2Of_ge hT.2.1 (le_top : T ≤ ⊤)
  obtain ⟨x, e⟩ := exists_escape hnot hU hTU
  exact h.not_dEdgeless_of_escape hT e

@[expose] def TightEdgeSylowCase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
    (∃ a b : genFittingFStar G, a * b ≠ b * a) →
    ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
    ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → ∀ T : Subgroup G,
      IsSylow2Of T
        (Subgroup.normalizer (((S : Subgroup R).map R.subtype : Subgroup G) : Set G)) →
      IsSylow2Of T ⊤ → ¬ Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore R))

theorem tightEdgeLarge_of_sylowCase (h : TightEdgeSylowCase) : TightEdgeLarge := by
  intro G _ _ _ hnab hlarge R S t hd
  have d : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S hd.quat hd.mem hd.order hd.cent hd.normal hd.twoGroup
  obtain ⟨T, hT, -⟩ := exists_isSylow2Of_ge d.S_two
    (Subgroup.le_normalizer : ((S : Subgroup R).map R.subtype : Subgroup G) ≤ _)
  by_cases hsyl : IsSylow2Of T ⊤
  · exact h G hnab hlarge R S t hd T hT hsyl
  · exact hd.not_dEdgeless_of_not_sylow hT hsyl

@[expose] def GoodThreeElement {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ (x : Y) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set Y) ∧ x ^ 3 ^ k = 1 ∧
    (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
    ∀ y ∈ Subgroup.centralizer ({t} : Set Y), (∀ r ∈ R, ⁅y, r⁆ ∈ oddCoreImg R) →
      ⁅x, y⁆ ∈ oddCoreImg (Subgroup.centralizer ({t} : Set Y))

theorem tightThreeElementLarge_iff_good : TightThreeElementLarge ↔
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → GoodThreeElement R t :=
  ⟨fun h G _ _ _ hnab hlarge R S t hd => h G hnab hlarge R S hd.quat t hd.mem hd.order hd.cent
      hd.normal hd.twoGroup,
    fun h G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2 =>
      h G hnab hlarge R S t ⟨hS, ht, hto, hRC, hRn, h2⟩⟩

theorem isSubnormal_of_centralizer_nbhd {C X L : Subgroup G} {t : G}
    (hCX : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X) (htX : t ∈ X)
    (hLN : L ≤ C ⊓ Subgroup.centralizer (X : Set G))
    (hL : IsSubnormal L (Subgroup.centralizer ({t} : Set G))) : IsSubnormal L C := by
  set N : Subgroup G := C ⊓ Subgroup.centralizer (X : Set G) with hN
  have hNt : N ≤ Subgroup.centralizer ({t} : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2) t htX).symm
  have h1 : IsSubnormal L N := by
    have := isSubnormal_inf hL N
    rwa [inf_eq_left.mpr hLN, inf_eq_right.mpr hNt] at this
  have hNC : N ≤ C := inf_le_left
  have hnorm : (N.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨by
      simpa using C.mul_mem (C.mul_mem c.2 (Subgroup.mem_inf.mp hn).1) (C.inv_mem c.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcx := hCX ((c⁻¹ : C) : G) (C.inv_mem c.2) x hx
    have hth := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2) _ hcx
    set cg : G := (c : G) with hcg
    set ng : G := (n : G) with hng
    have hth' : ng * (cg⁻¹ * x * cg) = (cg⁻¹ * x * cg) * ng := by
      simpa [hcg, hng, mul_assoc] using hth.symm
    show x * (cg * ng * cg⁻¹) = (cg * ng * cg⁻¹) * x
    calc x * (cg * ng * cg⁻¹) = cg * ((cg⁻¹ * x * cg) * ng) * cg⁻¹ := by group
      _ = cg * (ng * (cg⁻¹ * x * cg)) * cg⁻¹ := by rw [hth']
      _ = (cg * ng * cg⁻¹) * x := by group
  exact isSubnormal_trans h1 (IsSubnormal.step hNC hnorm (IsSubnormal.refl C))

section Scaffold

@[expose] def TightHasLift {Y : Type} [Group Y] (R : Subgroup Y) (t : Y) : Prop :=
  ∃ L : Subgroup Y, tightCore R ≤ L ∧ IsClassicalMember3 L t

@[expose] def TightLiftBelow (Cls Ex : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (_S : Sylow 2 R) (_t : Y), Prop) (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n → ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → Cls Y R S t → Ex Y R S t ∨ TightHasLift R t

@[expose] def TightLiftInductive (Cls Ex : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (_S : Sylow 2 R) (_t : Y), Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → Cls Y R S t → Ex Y R S t ∨ TightHasLift R t

@[expose] def TightLiftStep (Cls Ex : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (_S : Sylow 2 R) (_t : Y), Prop) (n : ℕ) : Prop :=
  TightLiftBelow Cls Ex n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → Cls Y R S t →
      Ex Y R S t ∨ TightHasLift R t

theorem tightLiftInductive_of_step {Cls Ex : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y)
    (_S : Sylow 2 R) (_t : Y), Prop} (h : ∀ n, TightLiftStep Cls Ex n) :
    TightLiftInductive Cls Ex := by
  intro Y _ _ R S t hd hc
  have key : ∀ n, TightLiftBelow Cls Ex n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y' _ _ hlt R' S' t' hd' hc'
      exact h (Nat.card Y') (ih (Nat.card Y') hlt) Y' rfl R' S' t' hd' hc'
  exact key (Nat.card Y + 1) Y (Nat.lt_succ_self _) R S t hd hc

theorem tightHasMember3Large_of_inductive
    {Cls Ex : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (_S : Sylow 2 R) (_t : Y), Prop}
    (hI : TightLiftInductive Cls Ex)
    (hCls : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → Cls G R S t)
    (hEx : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup (genFittingFStar G)],
      (∃ a b : genFittingFStar G, a * b ≠ b * a) →
      ¬ TwoSubgroupsFourGenerated (genFittingFStar G) →
      ∀ (R : Subgroup G) (S : Sylow 2 R) (t : G), TightDatum R S t → ¬ Ex G R S t) :
    TightHasMember3Large := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  have hd : TightDatum R S t := ⟨hS, ht, hto, hRC, hRn, h2⟩
  rcases hI G R S t hd (hCls G hnab hlarge R S t hd) with hex | ⟨L, -, hL⟩
  · exact absurd hex (hEx G hnab hlarge R S t hd)
  · exact ⟨t, L, hL⟩

end Scaffold

end CFSG.ClassicalInvolution.Q3
