module

public import CFSG.GH74.Generic.S45.PumpLeaves

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.GH74.GLS Subgroup
open CFSG.Assembly.LowTwoRank

@[expose] def Hyp1310 (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K) : Prop :=
  InCalK2 K ∧ orderOf y = 2 ∧ L ≤ fixSub (zpowers y) ∧
    (L.subgroupOf (fixSub (zpowers y))).IsSubnormal ∧ HasL2Model ↥L Odd ∧
    (∀ P : Sylow 2 ↥(fixSub (zpowers y)),
      IsElementaryAbelian 2 ↥(P : Subgroup ↥(fixSub (zpowers y)))) ∧
    (¬ ∃ f : ℕ, LieModel K .twistedG2 0 3 f) ∧
    (HasL2Model ↥L (fun q => q = 5) → ¬ NativeSporadic.IsSporadic K .J1)

@[expose] def Concl1310 (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K) : Prop :=
  HasL2Model ↥L (fun q => q = 5) ∧ IsPumpOutcome K ∧
    (¬ NativeSporadic.IsSporadic K .J2 → y ∉ (MulAut.conj : K →* MulAut K).range)

@[expose] def LieTypeChar (X : Type) [Group X] (p : ℕ) : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), StatedClassicalModel X t n p f) ∨
  (∃ (t : StatedLieTag) (f : ℕ), t ∈ chevalleyExceptionalTags ∧ ChevalleyExceptionalModel X t p f) ∨
  (∃ (t : StatedLieTag) (f : ℕ), t ∈ reeTitsTags ∧ ReeTitsModel X t p f) ∨
  ∃ f : ℕ, SuzukiModel X p f

@[expose] def B_1310_alt : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    (∃ n : ℕ, 5 ≤ n ∧ Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n))) → False

@[expose] def B_1310_spor : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    (∃ s : TauCeti.SporadicName, NativeSporadic.IsSporadic (K ⧸ center K) s) → Concl1310 K y L

@[expose] def B_1310_even : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    LieTypeChar (K ⧸ center K) 2 → Concl1310 K y L

@[expose] def B_1310_odd : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (y : MulAut K) (L : Subgroup K), Hyp1310 K y L →
    ∀ r : ℕ, r.Prime → r ≠ 2 → LieTypeChar (K ⧸ center K) r → False

theorem catalog_of_inCalK2 {K : Type} [Group K] (hK : InCalK2 K) : Catalog (K ⧸ center K) := by
  have hq : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  exact CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hK.2.2 ⊤
    ((QuotientGroup.mk' (center K)).comp (Subgroup.topEquiv (G := K)).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := K)).surjective)

theorem b_III11_13_10_of_leaves (hAlt : B_1310_alt) (hSpor : B_1310_spor) (hEven : B_1310_even)
    (hOdd : B_1310_odd) : B_III11_13_10 := by
  intro K _ _ hK y hy L hL hsub hL2 hA hb1 hb2
  have hyp : Hyp1310 K y L := ⟨hK, hy, hL, hsub, hL2, hA, hb1, hb2⟩
  have hcat := catalog_of_inCalK2 hK
  have hnab : ∃ a b : K ⧸ center K, a * b ≠ b * a := hK.1.2.2
  have hLie : ∀ p : ℕ, p.Prime → LieTypeChar (K ⧸ center K) p → Concl1310 K y L := by
    intro p hp hlie
    by_cases h2 : p = 2
    · subst h2
      exact hEven K y L hyp hlie
    · exact (hOdd K y L hyp p hp h2 hlie).elim
  rcases hcat with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, he⟩ | ⟨t, n, p, f, hm⟩ | hex | ⟨s, he⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (hAlt K y L hyp ⟨n, hn, he⟩).elim
  · exact hLie p hm.1.1 (Or.inl ⟨t, n, f, hm⟩)
  · rcases hex with ⟨t, p, f, ht, hm⟩ | ⟨t, p, f, ht, hm⟩ | ⟨p, f, hm⟩
    · exact hLie p hm.1.1 (Or.inr (Or.inl ⟨t, f, ht, hm⟩))
    · exact hLie p hm.1.1 (Or.inr (Or.inr (Or.inl ⟨t, f, ht, hm⟩)))
    · have hp2 : p = 2 := hm.1
      subst hp2
      exact hEven K y L hyp (Or.inr (Or.inr (Or.inr ⟨f, hm⟩)))
  · exact hSpor K y L hyp ⟨s, he⟩

end CFSG.GH74.Generic.S45
