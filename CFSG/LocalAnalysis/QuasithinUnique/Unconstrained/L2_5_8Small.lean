module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Setting
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

@[expose] def innerAut (X : Type*) [Group X] : Subgroup (MulAut X) :=
  (MulAut.conj : X →* MulAut X).range

structure SmallListFacts (X : Type) [Group X] : Prop where
  simple : IsSimpleGroup X
  out_two : ∀ φ : MulAut X, ∃ k : ℕ, φ ^ 2 ^ k ∈ innerAut X
  sylow_shape : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ →
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨ Nonempty (↥P ≃* SemidihedralGroup 4)
  sylow_normalizer : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → Subgroup.normalizer (P : Set X) ≤ P
  four_normalizer : ∀ F : Subgroup X, IsFourSubgroup F →
    Nonempty (↥(Subgroup.normalizer (F : Set X)) ≃* Equiv.Perm (Fin 4))
  four_fixes : ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∀ F : Subgroup X, F ≤ P → IsFourSubgroup F →
    ∀ φ : MulAut X, (∀ f ∈ F, φ f = f) → ∀ y : X, φ y ∈ P ↔ y ∈ P

@[expose] def FixPointwiseInner (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsSylowTwoOf P ⊤ → ∀ α : MulAut X, (∀ y ∈ P, α y = y) → α ∈ innerAut X

@[expose] def A6DynkinCentral (X : Type) [Group X] : Prop :=
  ∀ P : Subgroup X, IsSylowTwoOf P ⊤ →
    ∀ B : Subgroup (MulAut X), (∀ β ∈ B, ∀ y : X, β y ∈ P ↔ y ∈ P) →
      (∀ Y : Subgroup X, P ≤ Y → (∀ β ∈ B, ∀ y : X, β y ∈ Y ↔ y ∈ Y) → Y = P ∨ Y = ⊤) →
      ∀ α : MulAut X, (∀ y ∈ P, α y = y) → (∀ β ∈ B, α * β = β * α) → α ∈ innerAut X

@[expose] def IsSmallNonA6 (X : Type) [Group X] : Prop :=
  StatedClassicalModel X .PSL 3 2 1 ∨ StatedClassicalModel X .PSL 3 3 1 ∨
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
    ∃ p : ℕ, IsFermatOrMersenne p ∧ 7 < p ∧ StatedClassicalModel X .PSL 2 p 1

structure SmallListCatalogue : Prop where
  a6 : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 6)) →
    SmallListFacts X ∧ A6DynkinCentral X
  l32 : ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSL 3 2 1 →
    SmallListFacts X ∧ FixPointwiseInner X
  l33 : ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSL 3 3 1 →
    SmallListFacts X ∧ FixPointwiseInner X
  m11 : ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) →
    SmallListFacts X ∧ FixPointwiseInner X
  l2p : ∀ p : ℕ, IsFermatOrMersenne p → 7 < p → ∀ (X : Type) [Group X] [Finite X],
    StatedClassicalModel X .PSL 2 p 1 → SmallListFacts X ∧ FixPointwiseInner X

namespace Unc25Small

theorem statedClassicalModel_psl_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : StatedClassicalModel Y .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem statedClassicalModel_psp_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : StatedClassicalModel Y .PSp n p f) : StatedClassicalModel X .PSp n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem normal_pGroup_eq_bot_of_simple {X : Type} [Group X] [Finite X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (N : Subgroup X) [N.Normal]
    (hN : IsPGroup p N) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    rw [h] at hN
    have hX : IsPGroup p X := hN.of_equiv Subgroup.topEquiv
    obtain ⟨a, b, hab⟩ := hnc
    have : Nontrivial X := ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
    have : Nontrivial (Subgroup.center X) := hX.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h2 | h2
    · obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne (1 : Subgroup.center X)
      rw [h2, Subgroup.mem_bot] at hx
      exact hx1 (Subtype.ext hx)
    · have : a ∈ Subgroup.center X := by rw [h2]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp this b).symm)

theorem exists_noncomm_K {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    {hs : UnconstrainedSetting G T M} (N : Notation25 hs) :
    ∃ a b : ↥N.K, a * b ≠ b * a := by
  obtain ⟨-, ⟨⟨-, -, a, b, hab⟩, -⟩⟩ := N.isComp
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hnc : a' * b' ≠ b' * a' := fun h =>
    hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  have ha'K : ((a' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp a'.2
  have hb'K : ((b' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp b'.2
  refine ⟨⟨_, ha'K⟩, ⟨_, hb'K⟩, fun h => hnc ?_⟩
  have := congrArg Subtype.val h
  exact Subtype.ext (Subtype.ext this)

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}

theorem smallList_cases {N : Notation25 hs} (h : Lv257 N) :
    (Nonempty (↥N.K ≃* alternatingGroup (Fin 6)) ∧ N.S ≤ M ∧ NontrivialOnDynkin M N.S N.K ∧
      IsBorelIn (M ⊓ N.K) N.K) ∨ IsSmallNonA6 ↥N.K := by
  obtain ⟨-, -, -, -, hcases⟩ := h.list252
  have hSM : N.S ≤ M := (N.tuple.sylow_inf.1).trans inf_le_right
  have hnc := exists_noncomm_K N
  have hq : IsSimpleGroup ↥N.K → Nonempty ((↥N.K ⧸ CFSG.pCore 2 ↥N.K) ≃* ↥N.K) := by
    intro hsimple
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpc : CFSG.pCore 2 ↥N.K = ⊥ :=
      normal_pGroup_eq_bot_of_simple hsimple hnc _ CFSG.pCore_isPGroup
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot⟩
  rcases hcases with ⟨hB, -⟩ | ⟨hRank, hDyn, hBor⟩ | ⟨hLM, -⟩ | ⟨hFM, -⟩
  · exact absurd hB N.nonBender
  · rcases hRank with ⟨n, hn1, hm⟩ | ⟨n, hn2, hm⟩ | ⟨⟨e6⟩⟩ | hm4
    · have hsimple : IsSimpleGroup ↥N.K :=
        (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n hm).2
      obtain ⟨e0⟩ := hq hsimple
      have hn : n = 1 :=
        h.concl257 n (Or.inl (statedClassicalModel_psl_of_mulEquiv e0 hm))
      subst hn
      exact Or.inr (Or.inl hm)
    · exfalso
      have hsimple : IsSimpleGroup ↥N.K :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n hm
      obtain ⟨e0⟩ := hq hsimple
      have := h.concl257 n (Or.inr (statedClassicalModel_psp_of_mulEquiv e0 hm))
      omega
    · exact Or.inl ⟨⟨e6⟩, hSM, hDyn, hBor⟩
    · exfalso
      have := h.concl257 2 (Or.inl hm4)
      omega
  · rcases hLM with hL | hM
    · exact Or.inr (Or.inr (Or.inl hL))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hM)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hFM)))

end Unc25Small

end CFSG.QuasithinUnique
