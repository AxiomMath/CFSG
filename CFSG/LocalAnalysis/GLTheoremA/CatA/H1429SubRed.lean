module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1429Res
public import CFSG.LocalAnalysis.GLTheoremA.PCompNoncomm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Trans
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterTransport
public import CFSG.LieType.SemisimpleCentralizers.HeldLangCover

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open scoped commutatorElement

@[expose] def I1429SubSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) → IsChevSimple 3 S →
    ∀ β : MulAut S, β ^ 3 = 1 → β ∉ (MulAut.conj : S →* MulAut S).range →
      ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup β) I →
        catalogIs (PSimple 3 I) S9.isU4two → catalogIs S isSp4_27

namespace H1429Sub

theorem eq_of_central_displacement {G H : Type} [Group G] [Group H] (hG : commutator G = ⊤) (f g : G →* H)
    (h : ∀ x, (g x)⁻¹ * f x ∈ Subgroup.center H) : f = g := by
  have hfg : ∀ x, f x = g x * ((g x)⁻¹ * f x) := fun x => by group
  have hle : commutator G ≤ MonoidHom.eqLocus f g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    show f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement, hfg a, hfg b]
    exact CFSG.LieType.SemisimpleCentralizers.HeldLang.commutatorElement_mul_central_mul_central (h a) (h b)
  rw [hG] at hle
  ext x
  exact hle (Subgroup.mem_top x)

end H1429Sub

theorem i1429SubfieldOut_of_simple (h : I1429SubSimple) : I1429SubfieldOut := by
  intro Q _ _ hQ hChev β hβ hout I hI hU
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  set π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hker : π.ker ≤ Subgroup.center Q := (QuotientGroup.ker_mk' _).le
  have hαβ : ∀ k, π (β k) = H1419.centerBar β (π k) := fun k => (H1419.centerBar_mk β k).symm
  have hI' : GLAPComponent 3 (fixSubgroup (H1419.centerBar β)) (I.map π) :=
    glaPComponent_map_fixSubgroup π hker β (H1419.centerBar β) hαβ (QuotientGroup.mk'_surjective _)
      Nat.prime_three hI
  have hnc := exists_mul_ne_mul_of_glaPComponent Nat.prime_three hI'
  have hout' : H1419.centerBar β ∉
      (MulAut.conj : (Q ⧸ Subgroup.center Q) →* MulAut (Q ⧸ Subgroup.center Q)).range := by
    rintro ⟨s, hs⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    apply hout
    refine ⟨q, ?_⟩
    have hf : (MulAut.conj q).toMonoidHom = β.toMonoidHom := by
      apply H1429Sub.eq_of_central_displacement hQ.1
      intro x
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have h1 : π (β x) = π (q * x * q⁻¹) := by
        rw [hαβ, ← hs]
        simp [hπ, MulAut.conj_apply]
      show (π (β x))⁻¹ * π (q * x * q⁻¹) = 1
      rw [h1, inv_mul_cancel]
    ext x
    exact congrArg (fun f : Q →* Q => f x) hf
  obtain ⟨e⟩ := nonempty_pSimple_equiv_map Nat.prime_three π hI hI'
  obtain ⟨i, hi, ⟨f⟩⟩ := hU
  exact h _ hQ.2 hnc hChev _ (H1419.centerBar_pow_three β hβ) hout' _ hI' ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem H1429Sub.false_of_solvable {G : Type} [Group G] [Finite G] {X I : Subgroup G}
    (hX : Group.IsSolvable ↥X) (hI : GLAPComponent 3 X I) : False := by
  have hIX : I ≤ X := hI.1
  haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.mpr (glaPComponent_perfect hI)
  haveI : Group.IsSolvable ↥I :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hIX)
      (Subgroup.inclusion_injective hIX)
  haveI : Nontrivial ↥I := (Subgroup.nontrivial_iff_ne_bot I).2 (glaPComponent_ne_bot' hI)
  exact Group.IsPerfect.not_isSolvable (G := ↥I) inferInstance

theorem H1429Sub.false_of_ambiguous (hamb : KDAmbSolv 3) {S : Type} [Group S] [Finite S]
    (hS : catalogIs S (ambiguousChev 3)) {β : MulAut S} (hβ : β ^ 3 = 1)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) : False := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hS
  have hβ' : MulAut.congr e β ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
  have hβ1 : MulAut.congr e β ≠ 1 := fun h =>
    hout ⟨1, by
      rw [map_one]
      exact ((MulAut.congr e).injective (h.trans (map_one _).symm)).symm⟩
  have hsol : Group.IsSolvable ↥(fixSubgroup (MulAut.congr e β)) := hamb i hi _ hβ' hβ1
  rw [CFSG.HardMathSupport.Dickson.I271.fixSubgroup_congr] at hsol
  haveI := hsol
  let φ : ↥(fixSubgroup β) ≃* ↥((fixSubgroup β).map e.toMonoidHom) :=
    Subgroup.equivMapOfInjective (fixSubgroup β) e.toMonoidHom e.injective
  have hsolβ : Group.IsSolvable ↥(fixSubgroup β) :=
    Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
  exact H1429Sub.false_of_solvable hsolβ hI

@[expose] def I1429SubLieAt (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 3 → P d.1 →
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∀ β : MulAut S, β ^ 3 = 1 → β ∉ (MulAut.conj : S →* MulAut S).range →
        ∀ I : Subgroup S, GLAPComponent 3 (fixSubgroup β) I →
          catalogIs (PSimple 3 I) S9.isU4two → catalogIs S isSp4_27

@[expose] def SubIsLin (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .A n q

@[expose] def SubIsUni (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedA n q

@[expose] def SubIsSymp (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, e = .B 2 q) ∨ (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .C n q)

@[expose] def SubIsOrth (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .B n q ∧ 3 ≤ n) ∨
    (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .D n q ∧ 5 ≤ n) ∨
    (∃ (n : ℕ) (q : TauCeti.PrimePower), e = .twistedD n q)

@[expose] def SubIsD4 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .D 4 q

@[expose] def SubIsExc (e : TauCeti.LieTypeIndex) : Prop :=
  (∃ q : TauCeti.PrimePower, e = .E6 q) ∨ (∃ q : TauCeti.PrimePower, e = .E7 q) ∨
    (∃ q : TauCeti.PrimePower, e = .E8 q) ∨ (∃ q : TauCeti.PrimePower, e = .F4 q) ∨
    (∃ q : TauCeti.PrimePower, e = .G2 q)

@[expose] def SubIsTwE6 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedE6 q

@[expose] def SubIsTri (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .trialityD4 q

@[expose] def SubIsRee (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ m : ℕ, e = .reeG2 m

theorem i1429SubSimple_of_families (hamb : KDAmbSolv 3)
    (hLin : I1429SubLieAt SubIsLin) (hUni : I1429SubLieAt SubIsUni) (hSymp : I1429SubLieAt SubIsSymp)
    (hOrth : I1429SubLieAt SubIsOrth) (hD4 : I1429SubLieAt SubIsD4) (hExc : I1429SubLieAt SubIsExc)
    (hTwE6 : I1429SubLieAt SubIsTwE6) (hTri : I1429SubLieAt SubIsTri) (hRee : I1429SubLieAt SubIsRee) :
    I1429SubSimple := by
  intro S _ _ hS hnc hChev β hβ hout I hI hU
  rcases hChev with ⟨i, hi, ⟨e⟩⟩ | hA
  · cases i with
    | cyclic p hp => exact absurd hi (by simp [onLie])
    | alternating n hn => exact absurd hi (by simp [onLie])
    | sporadic s => exact absurd hi (by simp [onLie])
    | lie d =>
      have hchar : d.1.characteristic = 3 := hi
      obtain ⟨d, hv⟩ := d
      cases d with
      | A n q => exact hLin S hS hnc ⟨_, hv⟩ hchar ⟨n, q, rfl⟩ ⟨e⟩ β hβ hout I hI hU
      | twistedA n q => exact hUni S hS hnc ⟨_, hv⟩ hchar ⟨n, q, rfl⟩ ⟨e⟩ β hβ hout I hI hU
      | B n q =>
        rcases Nat.lt_or_ge n 3 with hn | hn
        · have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
          obtain rfl : n = 2 := by omega
          exact hSymp S hS hnc ⟨_, hv⟩ hchar (Or.inl ⟨q, rfl⟩) ⟨e⟩ β hβ hout I hI hU
        · exact hOrth S hS hnc ⟨_, hv⟩ hchar (Or.inl ⟨n, q, rfl, hn⟩) ⟨e⟩ β hβ hout I hI hU
      | C n q => exact hSymp S hS hnc ⟨_, hv⟩ hchar (Or.inr ⟨n, q, rfl⟩) ⟨e⟩ β hβ hout I hI hU
      | D n q =>
        rcases Nat.lt_or_ge n 5 with hn | hn
        · have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
          obtain rfl : n = 4 := by omega
          exact hD4 S hS hnc ⟨_, hv⟩ hchar ⟨q, rfl⟩ ⟨e⟩ β hβ hout I hI hU
        · exact hOrth S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inl ⟨n, q, rfl, hn⟩)) ⟨e⟩ β hβ hout I hI hU
      | twistedD n q =>
        exact hOrth S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inr ⟨n, q, rfl⟩)) ⟨e⟩ β hβ hout I hI hU
      | E6 q => exact hExc S hS hnc ⟨_, hv⟩ hchar (Or.inl ⟨q, rfl⟩) ⟨e⟩ β hβ hout I hI hU
      | E7 q => exact hExc S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inl ⟨q, rfl⟩)) ⟨e⟩ β hβ hout I hI hU
      | E8 q =>
        exact hExc S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩))) ⟨e⟩ β hβ hout I hI hU
      | F4 q =>
        exact hExc S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)))) ⟨e⟩ β hβ hout
          I hI hU
      | G2 q =>
        exact hExc S hS hnc ⟨_, hv⟩ hchar (Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))) ⟨e⟩ β hβ hout
          I hI hU
      | twistedE6 q => exact hTwE6 S hS hnc ⟨_, hv⟩ hchar ⟨q, rfl⟩ ⟨e⟩ β hβ hout I hI hU
      | trialityD4 q => exact hTri S hS hnc ⟨_, hv⟩ hchar ⟨q, rfl⟩ ⟨e⟩ β hβ hout I hI hU
      | suzuki m => exact absurd hchar (by simp)
      | reeG2 m => exact hRee S hS hnc ⟨_, hv⟩ hchar ⟨m, rfl⟩ ⟨e⟩ β hβ hout I hI hU
      | reeF4 m => exact absurd hchar (by simp)
      | tits => exact absurd hchar (by simp)
  · exact (H1429Sub.false_of_ambiguous hamb hA hβ hout hI).elim

end CFSG.LocalAnalysis.GLTheoremA

end
