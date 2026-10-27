module

public import CFSG.ClassicalInvolution.Generic.TypeA
public import CFSG.ClassicalInvolution.Generic.Induction
import CFSG.ClassicalInvolution.RouteD.TypeF4Model
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.Models.TwistedPairs.Basic
public import CFSG.LieType.Steinberg.TwistedE6.Fixed

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.CurtisTits
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank

section Standard

variable {F E : Type} [Field F] [Field E] {G : Type} [Group G] {X : Type} [Group X]

theorem _root_.CFSG.ClassicalInvolution.Models.TwistedPairs.TwistedB2Model.StandardPair.subgroupOf
    {P : TwistedB2Model F E G} {J W U V : Subgroup X} (hW : W ≤ J) (h : P.StandardPair W U V) :
    P.StandardPair (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, hrange, hker, hl, hs, hU, hV⟩ := h
  have hθ : ∀ x, θ x ∈ J := fun x => hW (by rw [← hrange]; exact ⟨x, rfl⟩)
  refine ⟨θ.codRestrict J hθ, ?_, by rwa [MonoidHom.ker_codRestrict], ?_, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, map_codRestrict_eq, ← MonoidHom.range_eq_map, hrange]
  · intro a b hab
    exact hl (congrArg Subtype.val hab)
  · intro a b hab
    exact hs (congrArg Subtype.val hab)
  · rw [map_codRestrict_eq, hU]
  · rw [map_codRestrict_eq, hV]

end Standard

section HighestRoot

@[expose] def hiTE6 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem isRoot_hiTE6 : IsRoot .F4 hiTE6 := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem not_isRoot_hiTE6_add (j : Fin (Tag.rank .F4)) (hj : j.val ≠ 0) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : ¬ IsRoot .F4 (hiTE6 + s • Pi.single j 1) := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  rcases hs with rfl | rfl
  · fin_cases j
    · exact absurd rfl hj
    all_goals decide +kernel
  · fin_cases j
    · exact absurd rfl hj
    all_goals decide +kernel

theorem iform_hiTE6_single (j : Fin (Tag.rank .F4)) (hj : j.val ≠ 0) :
    iform hiTE6 (Pi.single j 1) = 0 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals decide +kernel

theorem iform_hiTE6_self : iform hiTE6 hiTE6 = 4 := by
  decide +kernel

theorem isLongest_of_isRoot_F4_TE6 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h4 : iform γ γ = 4) (hA : TauCeti.IsFiniteType (Tag.cartan .F4)) :
    CFSG.ClassicalInvolution.ModelFacts.IsLongest hA ∅ γ :=
  CFSG.ClassicalInvolution.RouteD.isLongest_of_isRoot_F4 hγ h4 hA

variable {E : Type*} [Field E] (σ : E →+* E)

theorem isLongestRoot_hiTE6 :
    CFSG.ClassicalInvolution.ModelFacts.IsLongestRoot (twistedDatum E σ) hiTE6 :=
  isLongest_of_isRoot_F4_TE6 isRoot_hiTE6 iform_hiTE6_self _

end HighestRoot

section Commute

variable {E : Type} [Field E] (σ : E →+* E)

theorem commute_of_mem_rootGroup_TE6 {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ = 0)
    (hsum : ¬ IsRoot .F4 (γ + δ)) {x y : fixedGroup E σ}
    (hx : x ∈ (twistedDatum E σ).rootGroup γ) (hy : y ∈ (twistedDatum E σ).rootGroup δ) :
    Commute x y := by
  have hlin : LinIndepPair γ δ := by
    by_contra h
    rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    exacts [hne h', hne' h']
  have hcone : openCone (twistedDatum E σ).roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ε ⟨hε, m, n, hm, hn, hεe⟩ => ?_
    have hε1 : IsRoot .F4 ε := by
      rw [twistedDatum_roots] at hε
      exact hε
    have hε' : IsRoot .F4 (m • γ + n • δ) := (congrArg (IsRoot .F4) hεe).mp hε1
    rcases exponent_pair_cases noG2_F4 hγ hδ hne hne' hm hn hε' with
      ⟨rfl, rfl⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact hsum (by simpa using hε')
    · rw [h0] at h; omega
    · rw [h0] at h; omega
  have key := commutator_mem_twistedDatum (θ := σ) γ (by rw [twistedDatum_roots]; exact hγ) δ
    (by rw [twistedDatum_roots]; exact hδ) hlin x hx y hy
  rw [hcone] at key
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at key
  exact commutatorElement_eq_one_iff_commute.1 key

theorem isRoot_neg_hiTE6 : IsRoot .F4 (-hiTE6) := IsRoot.neg isRoot_hiTE6

theorem isRoot_single_F4_TE6 (j : Fin (Tag.rank .F4)) : IsRoot .F4 (Pi.single j 1) := .basis j

theorem isRoot_neg_single_F4_TE6 (j : Fin (Tag.rank .F4)) : IsRoot .F4 (-Pi.single j 1) :=
  IsRoot.neg (isRoot_single_F4_TE6 j)

theorem commute_hiTE6_single {j : Fin (Tag.rank .F4)} (hj : j.val ≠ 0)
    {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : γ = hiTE6 ∨ γ = -hiTE6)
    (hδ : δ = Pi.single j 1 ∨ δ = -Pi.single j 1) {x y : fixedGroup E σ}
    (hx : x ∈ (twistedDatum E σ).rootGroup γ) (hy : y ∈ (twistedDatum E σ).rootGroup δ) :
    Commute x y := by
  have hc0 : (hiTE6 : Fin (Tag.rank .F4) → ℤ) ⟨0, by decide⟩ = 2 := rfl
  have hjne : j ≠ ⟨0, by decide⟩ := fun h => hj (by rw [h])
  have hcoord : (Pi.single j (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) ⟨0, by decide⟩ = 0 :=
    Pi.single_eq_of_ne (Ne.symm hjne) _
  have hneg : ∀ a b : Fin (Tag.rank .F4) → ℤ, iform (-a) b = -iform a b := fun a b => by
    simpa using iform_smul_left (-1) a b
  have hneg' : ∀ a b : Fin (Tag.rank .F4) → ℤ, iform a (-b) = -iform a b := fun a b => by
    simpa using iform_smul_right (-1) a b
  have hγr : IsRoot .F4 γ := by
    rcases hγ with rfl | rfl
    · exact isRoot_hiTE6
    · exact isRoot_neg_hiTE6
  have hδr : IsRoot .F4 δ := by
    rcases hδ with rfl | rfl
    · exact isRoot_single_F4_TE6 j
    · exact isRoot_neg_single_F4_TE6 j
  refine commute_of_mem_rootGroup_TE6 σ hγr hδr (fun h => ?_) (fun h => ?_) ?_ ?_ hx hy
  · have := congrFun h ⟨0, by decide⟩
    rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
      simp only [Pi.neg_apply, hc0, hcoord] at this <;> omega
  · have := congrFun h ⟨0, by decide⟩
    rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
      simp only [Pi.neg_apply, neg_neg, hc0, hcoord] at this <;> omega
  · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
      simp [hneg, hneg', iform_hiTE6_single j hj]
  · rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl
    · simpa using not_isRoot_hiTE6_add j hj 1 (Or.inl rfl)
    · simpa [sub_eq_add_neg] using not_isRoot_hiTE6_add j hj (-1) (Or.inr rfl)
    · intro h
      refine not_isRoot_hiTE6_add j hj (-1) (Or.inr rfl) ?_
      have := IsRoot.neg h
      convert this using 1
      simp
      abel
    · intro h
      refine not_isRoot_hiTE6_add j hj 1 (Or.inl rfl) ?_
      have := IsRoot.neg h
      convert this using 1
      simp
      abel

theorem commutes_sup_of_both_TE6 {G : Type*} [Group G] {A₁ A₂ B : Subgroup G}
    (h₁ : Commutes A₁ B) (h₂ : Commutes A₂ B) : Commutes (A₁ ⊔ A₂) B := by
  intro y hy b hb
  have : A₁ ⊔ A₂ ≤ Subgroup.centralizer (B : Set G) :=
    sup_le (fun y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h₁ y hy b hb).symm)
      (fun y hy => Subgroup.mem_centralizer_iff.mpr fun b hb => (h₂ y hy b hb).symm)
  exact (Subgroup.mem_centralizer_iff.mp (this hy) b hb).symm

@[expose] noncomputable def rankOneHiTE6 : Subgroup (fixedGroup E σ) :=
  (twistedDatum E σ).rootGroup hiTE6 ⊔ (twistedDatum E σ).rootGroup (-hiTE6)

theorem commutes_rankOneHiTE6 {j : Fin (Tag.rank .F4)} (hj : j.val ≠ 0) :
    Commutes (rankOneHiTE6 σ) (rankOne (twistedDatum E σ).rootGroup j) := by
  have key : ∀ γ δ : Fin (Tag.rank .F4) → ℤ, (γ = hiTE6 ∨ γ = -hiTE6) →
      (δ = Pi.single j 1 ∨ δ = -Pi.single j 1) →
      Commutes ((twistedDatum E σ).rootGroup γ) ((twistedDatum E σ).rootGroup δ) :=
    fun γ δ hγ hδ x hx y hy => (commute_hiTE6_single σ hj hγ hδ hx hy).eq
  have k11 := key hiTE6 (Pi.single j 1) (Or.inl rfl) (Or.inl rfl)
  have k12 := key hiTE6 (-Pi.single j 1) (Or.inl rfl) (Or.inr rfl)
  have k21 := key (-hiTE6) (Pi.single j 1) (Or.inr rfl) (Or.inl rfl)
  have k22 := key (-hiTE6) (-Pi.single j 1) (Or.inr rfl) (Or.inr rfl)
  exact commutes_sup_of_both_TE6 (commutes_sup_of_both_TE6 k11.symm k12.symm).symm
    (commutes_sup_of_both_TE6 k21.symm k22.symm).symm

theorem rankOneHiTE6_mem_fund :
    rankOneHiTE6 σ ∈ fundamentalSubgroups .twistedE6 (twistedDatum E σ) :=
  ⟨1, hiTE6, Or.inl (isLongestRoot_hiTE6 σ), (conjSub_one _).symm⟩

end Commute

section Nodes

variable (p f : ℕ) [Fact p.Prime]

@[expose] noncomputable def nodeTE6 (i : Fin 4) : Subgroup (twistedE6Group p f) :=
  rankOne (twistedE6Datum p f).rootGroup i

variable {p f}

theorem nodeTE6_mem_fund {i : Fin 4} (hi : i.val < 2) :
    nodeTE6 p f i ∈ fundamentalSubgroups .twistedE6 (twistedE6Datum p f) :=
  ⟨1, Pi.single i 1, Or.inl (CFSG.ClassicalInvolution.ModelFacts.isLongest_single_F4 rfl _ hi),
    (conjSub_one _).symm⟩

theorem commutes_rankOneHiTE6_node {i : Fin 4} (hi : i.val ≠ 0) :
    Commutes (rankOneHiTE6 (frobQ p f)) (nodeTE6 p f i) :=
  commutes_rankOneHiTE6 (frobQ p f) hi

end Nodes

end CFSG.ClassicalInvolution.RouteD
