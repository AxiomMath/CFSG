module

public import CFSG.ClassicalInvolution.WeakCT.F4
public import CFSG.ClassicalInvolution.RouteD.TypeF4Closure
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCRecognition
public import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  linearBlockStandardPair_subgroupOf symplecticBlockStandardPair_subgroupOf
  linearBlockStandardPair_le_sup symplecticBlockStandardPair_le_sup iSup_subgroupOf_eq_top)

section HighestRoot

@[expose] def hiF4 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem isRoot_hiF4 : IsRoot .F4 hiF4 := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  decide +kernel

theorem not_isRoot_hiF4_add (j : Fin (Tag.rank .F4)) (hj : j.val ≠ 0) (s : ℤ)
    (hs : s = 1 ∨ s = -1) : ¬ IsRoot .F4 (hiF4 + s • Pi.single j 1) := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .F4)]
  rcases hs with rfl | rfl
  · fin_cases j
    · exact absurd rfl hj
    all_goals decide +kernel
  · fin_cases j
    · exact absurd rfl hj
    all_goals decide +kernel

theorem iform_hiF4_single (j : Fin (Tag.rank .F4)) (hj : j.val ≠ 0) :
    iform hiF4 (Pi.single j 1) = 0 := by
  fin_cases j
  · exact absurd rfl hj
  all_goals decide +kernel

theorem iform_hiF4_self : iform hiF4 hiF4 = 4 := by
  decide +kernel

theorem isLongest_of_isRoot_F4 {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (h4 : iform γ γ = 4) (hA : TauCeti.IsFiniteType (Tag.cartan .F4)) :
    CFSG.ClassicalInvolution.ModelFacts.IsLongest hA ∅ γ := by
  induction hγ with
  | basis j =>
    have hj : j.val < 2 := by
      rw [iform_single_single] at h4
      fin_cases j
      · decide
      · decide
      all_goals exact absurd h4 (by decide)
    exact CFSG.ClassicalInvolution.ModelFacts.isLongest_single_F4 rfl hA hj
  | @reflect i v hv ih =>
    rw [iform_reflect] at h4
    have := (ih h4).map_weylAction
      ((CFSG.LieType.RootSystem.coxeterMatrix hA).toCoxeterSystem.simple i)
    rw [weylAction_simple_eq_reflect] at this
    exact this

variable {F : Type} [Field F]

theorem isLongestRoot_hiF4 : IsLongestRoot (f4Datum F) hiF4 :=
  isLongest_of_isRoot_F4 isRoot_hiF4 iform_hiF4_self _

theorem isLongestRoot_single_F4 {k : Fin (Tag.rank .F4)} (hk : k.val < 2) :
    IsLongestRoot (f4Datum F) (Pi.single k 1) :=
  CFSG.ClassicalInvolution.ModelFacts.isLongest_single_F4 rfl _ hk

end HighestRoot

section Commute

variable {F : Type} [Field F]

theorem commute_of_mem_rootGroup_F4 {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (hne : γ ≠ δ) (hne' : γ ≠ -δ) (h0 : iform γ δ = 0)
    (hsum : ¬ IsRoot .F4 (γ + δ)) {x y : adjointGroup .F4 F}
    (hx : x ∈ rootGroup (rootOperatorFamily .F4) F γ)
    (hy : y ∈ rootGroup (rootOperatorFamily .F4) F δ) : Commute x y := by
  have hlin : LinIndepPair γ δ := by
    by_contra h
    rcases CFSG.LieType.Steinberg.TagRoots.eq_or_eq_neg_of_not_linIndepPair hγ hδ h with h' | h'
    exacts [hne h', hne' h']
  have hcone : openCone (adjDatum (rootOperatorFamily .F4) F).roots γ δ = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ε ⟨hε, m, n, hm, hn, hεe⟩ => ?_
    rw [mem_adjDatum_roots, hεe] at hε
    rcases exponent_pair_cases Adjoint.noG2_F4 hγ hδ hne hne' hm hn hε with
      ⟨rfl, rfl⟩ | ⟨-, -, -, -, h⟩ | ⟨-, -, -, -, h⟩
    · exact hsum (by simpa using hε)
    · rw [h0] at h; omega
    · rw [h0] at h; omega
  have key := commutator_mem_openCone_of_linIndepPair hγ hδ hlin hx hy
  rw [hcone] at key
  simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at key
  exact commutatorElement_eq_one_iff_commute.1 key

theorem isRoot_neg_hiF4 : IsRoot .F4 (-hiF4) := IsRoot.neg isRoot_hiF4

theorem isRoot_single_F4 (j : Fin (Tag.rank .F4)) : IsRoot .F4 (Pi.single j 1) := .basis j

theorem isRoot_neg_single_F4 (j : Fin (Tag.rank .F4)) : IsRoot .F4 (-Pi.single j 1) :=
  IsRoot.neg (isRoot_single_F4 j)

theorem commute_hiF4_single {j : Fin (Tag.rank .F4)} (hj : j.val ≠ 0) (s t : ℤ)
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) {x y : adjointGroup .F4 F}
    (hx : x ∈ rootGroup (rootOperatorFamily .F4) F (s • hiF4))
    (hy : y ∈ rootGroup (rootOperatorFamily .F4) F (t • Pi.single j 1)) : Commute x y := by
  have hc0 : (hiF4 : Fin (Tag.rank .F4) → ℤ) ⟨0, by decide⟩ = 2 := rfl
  have hroot : ∀ u : ℤ, (u = 1 ∨ u = -1) → IsRoot .F4 (u • hiF4) := by
    rintro u (rfl | rfl)
    · rw [one_smul]; exact isRoot_hiF4
    · rw [neg_smul, one_smul]; exact isRoot_neg_hiF4
  have hroot' : ∀ u : ℤ, (u = 1 ∨ u = -1) → IsRoot .F4 (u • Pi.single j 1) := by
    rintro u (rfl | rfl)
    · rw [one_smul]; exact isRoot_single_F4 j
    · rw [neg_smul, one_smul]; exact isRoot_neg_single_F4 j
  have hjne : j ≠ ⟨0, by decide⟩ := fun h => hj (by rw [h])
  have hcoord : (Pi.single j (1 : ℤ) : Fin (Tag.rank .F4) → ℤ) ⟨0, by decide⟩ = 0 :=
    Pi.single_eq_of_ne (Ne.symm hjne) _
  refine commute_of_mem_rootGroup_F4 (hroot s hs) (hroot' t ht) (fun h => ?_) (fun h => ?_) ?_ ?_
    hx hy
  · have := congrFun h ⟨0, by decide⟩
    simp only [Pi.smul_apply, smul_eq_mul, hc0, hcoord] at this
    rcases hs with rfl | rfl <;> omega
  · have := congrFun h ⟨0, by decide⟩
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hc0, hcoord] at this
    rcases hs with rfl | rfl <;> omega
  · rw [iform_smul_left, iform_smul_right, iform_hiF4_single j hj]
    ring
  · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · simpa using not_isRoot_hiF4_add j hj 1 (Or.inl rfl)
    · simpa [sub_eq_add_neg] using not_isRoot_hiF4_add j hj (-1) (Or.inr rfl)
    · intro h
      refine not_isRoot_hiF4_add j hj (-1) (Or.inr rfl) ?_
      have := IsRoot.neg h
      convert this using 1
      simp
      abel
    · intro h
      refine not_isRoot_hiF4_add j hj 1 (Or.inl rfl) ?_
      have := IsRoot.neg h
      convert this using 1
      simp
      abel

@[expose] noncomputable def rankOneHiF4 (F : Type) [Field F] : Subgroup (adjointGroup .F4 F) :=
  (f4Datum F).rootGroup hiF4 ⊔ (f4Datum F).rootGroup (-hiF4)

theorem commutes_rankOneHiF4 {j : Fin (Tag.rank .F4)} (hj : j.val ≠ 0) :
    Commutes (rankOneHiF4 F) (CurtisTits.rankOne (f4Datum F).rootGroup j) := by
  have key : ∀ s t : ℤ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
      Commutes ((f4Datum F).rootGroup (s • hiF4)) ((f4Datum F).rootGroup (t • Pi.single j 1)) :=
    fun s t hs ht x hx y hy => (commute_hiF4_single hj s t hs ht hx hy).eq
  have k11 := key 1 1 (Or.inl rfl) (Or.inl rfl)
  have k12 := key 1 (-1) (Or.inl rfl) (Or.inr rfl)
  have k21 := key (-1) 1 (Or.inr rfl) (Or.inl rfl)
  have k22 := key (-1) (-1) (Or.inr rfl) (Or.inr rfl)
  simp only [one_smul, neg_one_smul] at k11 k12 k21 k22
  unfold rankOneHiF4 CurtisTits.rankOne
  exact commutes_sup_sup k11 k12 k21 k22

end Commute

section Fund

variable {F : Type} [Field F]

theorem rankOneHiF4_mem_fund : rankOneHiF4 F ∈ fundamentalSubgroups .F4 (f4Datum F) :=
  ⟨1, hiF4, Or.inl isLongestRoot_hiF4, by simp [rankOneHiF4]⟩

theorem rankOne_mem_fund {k : Fin (Tag.rank .F4)} (hk : k.val < 2) :
    CurtisTits.rankOne (f4Datum F).rootGroup k ∈ fundamentalSubgroups .F4 (f4Datum F) :=
  ⟨1, Pi.single k 1, Or.inl (isLongestRoot_single_F4 hk), by simp [CurtisTits.rankOne]⟩

end Fund

section Recognition

variable {p f : ℕ} [Fact p.Prime]

theorem weakCT_f4_subgroup (hadm : StatedLieAdmissible .F4 0 p f) (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) {G : Type} [Group G]
    (U : Fin 4 → Subgroup G)
    (hcomm : ∀ i j : Fin 4, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 4, i.val + 1 = j.val → i.val ≠ 1 →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair F W (U 1) (U 2)) :
    ∃ Ψ : adjointGroup .F4 (GaloisField p f) →* G, Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range = ⨆ k, U k ∧
      ∀ k, (CurtisTits.rankOne (f4Datum (GaloisField p f)).rootGroup k).map Ψ = U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -, -, -, hblk⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_f4 p f hadm hp2
    hF hq (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hi1 => by
      obtain ⟨W, hW⟩ := hpair i j hij hi1
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (by
      obtain ⟨W, hW⟩ := hsp
      exact ⟨W.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hW).trans (sup_le (hUle 1) (hUle 2))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]
  · intro k
    rw [← Subgroup.map_map (f := Ψ') (g := Gs.subtype), hblk k, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hUle k)]

end Recognition

end CFSG.ClassicalInvolution.RouteD
