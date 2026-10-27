module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93Quasi

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint CFSG.ComponentClassification

theorem ivk93cov_isDoubleCoverOfAlt_of_equiv {K L : Type} [Group K] [Group L] (e : K ≃* L) {n : ℕ}
    (h : IsDoubleCoverOfAlt K n) : IsDoubleCoverOfAlt L n := by
  obtain ⟨hq, hc, ⟨φ⟩⟩ := h
  refine ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).1 hq, ?_, ?_⟩
  · rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]; exact hc
  · have hmap : (center K).map e.toMonoidHom = center L := by
      ext y
      simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro g
        have := hx (e.symm g)
        have h2 := congrArg e this
        simpa using h2
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        rw [Subgroup.mem_center_iff] at hy ⊢
        intro g
        have := hy (e g)
        have h2 := congrArg e.symm this
        simpa using h2
    exact ⟨(QuotientGroup.congr (center K) (center L) e hmap).symm.trans φ⟩

structure Ivk93Cov {J : Type} [Group J] [Finite J] (x : J) (n : ℕ) (B : Subgroup J) : Prop where
  ord : orderOf x = 2
  eight : 8 ≤ n
  le_eleven : n ≤ 11
  comp : IsPCompIn 2 (centralizer ({x} : Set J)) B
  mem : x ∈ B
  cover : IsDoubleCoverOfAlt (↥B ⧸ pPrimeCore 2 ↥B) n

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem mul_self_eq_one (h : Ivk93Cov x n B) : x * x = 1 := by
  rw [← pow_two, ← h.ord]
  exact pow_orderOf_eq_one x

theorem ne_one (h : Ivk93Cov x n B) : x ≠ 1 := by
  intro h1
  have := h.ord
  rw [h1, orderOf_one] at this
  omega

theorem le (h : Ivk93Cov x n B) : B ≤ centralizer ({x} : Set J) := h.comp.1

theorem perfect (h : Ivk93Cov x n B) : Group.IsPerfect ↥B := by
  have h1 := CatalogueBAlternating.pComponent_perfect h.comp.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h.le).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h.le).surjective

theorem card_quot (h : Ivk93Cov x n B) : Nat.card (↥B ⧸ pPrimeCore 2 ↥B) = n.factorial := by
  have hn : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by have := h.eight; omega)
  obtain ⟨-, hc, ⟨e⟩⟩ := h.cover
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (↥B ⧸ pPrimeCore 2 ↥B))
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin, hc] at h1
  have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by have := h.eight; omega)
  rw [h1]
  exact Nat.div_mul_cancel h2

theorem card_ge (h : Ivk93Cov x n B) : n.factorial ≤ Nat.card ↥B := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥B)
  have h2 : 1 ≤ Nat.card ↥(pPrimeCore 2 ↥B) := Nat.card_pos
  rw [h.card_quot] at h1
  calc n.factorial = n.factorial * 1 := (mul_one _).symm
    _ ≤ n.factorial * Nat.card ↥(pPrimeCore 2 ↥B) := Nat.mul_le_mul_left _ h2
    _ = Nat.card ↥B := h1.symm

theorem card_ge_big (h : Ivk93Cov x n B) : 40320 ≤ Nat.card ↥B := by
  have h1 : Nat.factorial 8 ≤ n.factorial := Nat.factorial_le h.eight
  have h2 : Nat.factorial 8 = 40320 := by decide
  have := h.card_ge
  omega

theorem nontrivial (h : Ivk93Cov x n B) : Nontrivial ↥B := by
  have h1 := h.card_ge_big
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have := Nat.card_of_subsingleton (1 : ↥B)
  omega

theorem not_solvable (h : Ivk93Cov x n B) : ¬ Group.IsSolvable ↥B := by
  have := h.perfect
  have := h.nontrivial
  exact Group.IsPerfect.not_isSolvable ↥B

theorem false_of_solvable (h : Ivk93Cov x n B)
    (hs : Group.IsSolvable ↥(centralizer ({x} : Set J))) : False :=
  h.not_solvable (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion h.le) (Subgroup.inclusion_injective h.le))

theorem false_of_card_cent_lt (h : Ivk93Cov x n B)
    (hC : Nat.card ↥(centralizer ({x} : Set J)) < 40320) : False := by
  have h1 : Nat.card ↥B ≤ Nat.card ↥(centralizer ({x} : Set J)) := Subgroup.card_le_of_le h.le
  have := h.card_ge_big
  omega

theorem false_of_card_group_lt (h : Ivk93Cov x n B) (hJ : Nat.card J < 40320) : False := by
  have h1 : Nat.card ↥B ≤ Nat.card J := Subgroup.card_le_card_group B
  have := h.card_ge_big
  omega

theorem of_equiv {J' : Type} [Group J'] [Finite J'] (Φ : J ≃* J') (h : Ivk93Cov x n B) :
    Ivk93Cov (Φ x) n (B.map Φ.toMonoidHom) := by
  have hc := map_centralizer_singleton_equiv' Φ x
  refine ⟨?_, h.eight, h.le_eleven, ?_, ⟨x, h.mem, rfl⟩, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact h.ord
  · rw [← hc]
    exact ⟨Subgroup.map_mono h.le, (isPComponent_subgroupOf_map_iff' Φ h.le).1 h.comp.2⟩
  · exact ivk93cov_isDoubleCoverOfAlt_of_equiv
      (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
        (B.equivMapOfInjective Φ.toMonoidHom Φ.injective)) h.cover

theorem eq_centralizer_of_quasisimple (h : Ivk93Cov x n B)
    (hq : CFSG.IsQuasisimple ↥(centralizer ({x} : Set J))) : B = centralizer ({x} : Set J) :=
  ivk93x_eq_centralizer_of_pComp h.comp h.not_solvable hq

end Ivk93Cov

@[expose] def Ivk93CovEmpty (P : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (n : ℕ) (B : Subgroup J), Ivk93Cov x n B → False

@[expose] def Ivk93CovEq (P : (X : Type) → [Group X] → Prop) (r : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
    ∀ (n : ℕ) (B : Subgroup J), Ivk93Cov x n B → r = n

theorem ivk93cov_empty_of_cfg {P : (X : Type) → [Group X] → Prop}
    (h : ∀ (J : Type) [Group J] [Finite J], P J → ∀ x : J, IsCentralInvolution x →
      ∀ (n : ℕ) (B : Subgroup J), Ivk93Cov x n B → False) : Ivk93CovEmpty P := h

@[expose] def Ivk93CovJ : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → GHList J → ∀ x : J, IsCentralInvolution x →
    ∀ (n : ℕ) (B : Subgroup J), Ivk93Cov x n B →
      (NativeSporadic.IsSporadic J .McL ∧ n = 8) ∨ (NativeSporadic.IsSporadic J .Ly ∧ n = 11)

structure Ivk93CovLeaves : Prop where
  alt : ∀ m : ℕ, 7 ≤ m → m ≤ 11 → Ivk93CovEmpty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin m)))
  m11 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M11)
  m12 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M12)
  m22 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M22)
  m23 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .M23)
  j1 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .J1)
  j2 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .J2)
  j3 : Ivk93CovEmpty (fun X _ => NativeSporadic.IsSporadic X .J3)
  mcl : Ivk93CovEq (fun X _ => NativeSporadic.IsSporadic X .McL) 8
  ly : Ivk93CovEq (fun X _ => NativeSporadic.IsSporadic X .Ly) 11
  l2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .PSL 2 p f)
  l3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .PSL 3 p f)
  u3 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .PSU 3 p f)
  sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .PSp 2 p f)
  g2 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .G2 0 p f)
  d4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → Ivk93CovEmpty (fun X _ => LieModel X .trialityD4 0 p f)
  l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSL 4 p f)
  u4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 7 →
    Ivk93CovEmpty (fun X _ => LieModel X .PSU 4 p f)
  l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 → Ivk93CovEmpty (fun X _ => LieModel X .PSL 5 p f)
  u5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 1 → Ivk93CovEmpty (fun X _ => LieModel X .PSU 5 p f)
  ree : ∀ f : ℕ, Ivk93CovEmpty (fun X _ => LieModel X .twistedG2 0 3 f)
  l28 : Ivk93CovEmpty (fun X _ => LieModel X .PSL 2 2 3)
  l216 : Ivk93CovEmpty (fun X _ => LieModel X .PSL 2 2 4)
  l34 : Ivk93CovEmpty (fun X _ => LieModel X .PSL 3 2 2)
  u34 : Ivk93CovEmpty (fun X _ => LieModel X .PSU 3 2 2)
  sz8 : Ivk93CovEmpty (fun X _ => LieModel X .twistedB2 0 2 3)

theorem ivk93CovJ_of_leaves (hl : Ivk93CovLeaves) : Ivk93CovJ := by
  intro J _ _ hs hGH x hx n B hc
  rcases hGH with ⟨m, h7, h11, he⟩ | hspor | ⟨p, f, hp, hf, hlie⟩
  · exact (hl.alt m h7 h11 J he x hx n B hc).elim
  · rcases hspor with h | h | h | h | h | h | h | h | h
    · exact (hl.m11 J h x hx n B hc).elim
    · exact (hl.m12 J h x hx n B hc).elim
    · exact (hl.m22 J h x hx n B hc).elim
    · exact (hl.m23 J h x hx n B hc).elim
    · exact (hl.j1 J h x hx n B hc).elim
    · exact (hl.j2 J h x hx n B hc).elim
    · exact (hl.j3 J h x hx n B hc).elim
    · exact Or.inl ⟨h, (hl.mcl J h x hx n B hc).symm⟩
    · exact Or.inr ⟨h, (hl.ly J h x hx n B hc).symm⟩
  · rcases hlie with ⟨hp2, hm | hm | hm | hm | hm | hm⟩ | ⟨hp2, hmod, hm⟩ | ⟨hp2, hmod, hm⟩ |
      ⟨hmod, hm⟩ | ⟨hmod, hm⟩ | hm | ⟨hp2, hm | hm | hm | hm | hm⟩
    · exact (hl.l2 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.l3 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.u3 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.sp4 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.g2 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.d4 p f hp hp2 hf J hm x hx n B hc).elim
    · exact (hl.l4 p f hp hp2 hf hmod J hm x hx n B hc).elim
    · exact (hl.u4 p f hp hp2 hf hmod J hm x hx n B hc).elim
    · exact (hl.l5 p f hp hf hmod J hm x hx n B hc).elim
    · exact (hl.u5 p f hp hf hmod J hm x hx n B hc).elim
    · exact (hl.ree f J hm x hx n B hc).elim
    · exact (hl.l28 J hm x hx n B hc).elim
    · exact (hl.l216 J hm x hx n B hc).elim
    · exact (hl.l34 J hm x hx n B hc).elim
    · exact (hl.u34 J hm x hx n B hc).elim
    · exact (hl.sz8 J hm x hx n B hc).elim

end CFSG.GH74.GLS.IVK.Proofs2
