module

public import CFSG.HardMathSupport.Foote.Coordinator.Component
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35SporData
public import CFSG.GH74.E2.ComponentsShape
public import CFSG.LargeExtraspecial.S12TriG2
public import CFSG.Quasithin.EmptyFaithful.E22SUK1
public import CFSG.GH74.GLS.LU.Local.FiveSL2

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6M

section Facts

variable {Q : Type} [Group Q] {V : Type} [CommGroup V] [Finite V]
  {L Y : Subgroup (MulAut V)} {z : MulAut V} {π : ↥L →* Q}

noncomputable def FooteK.quotientEquiv (h : FooteK Q L Y z π) :
    (↥L ⧸ Subgroup.center ↥L) ≃* Q :=
  (QuotientGroup.quotientMulEquivOfEq h.ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π h.surj)

theorem FooteK.finite (h : FooteK Q L Y z π) : Finite Q :=
  Finite.of_surjective π h.surj

theorem FooteK.isSimpleGroup (h : FooteK Q L Y z π) : IsSimpleGroup Q :=
  (MulEquiv.isSimpleGroup_congr h.quotientEquiv).mp h.quasi.2

theorem FooteK.nonabelian (h : FooteK Q L Y z π) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hs := h.isSimpleGroup
  have hL : ∀ x : ↥L, π x = 1 := by
    intro x
    have hx : x ∈ commutator ↥L := by rw [h.quasi.1]; trivial
    rw [commutator_def] at hx
    rw [← MonoidHom.mem_ker]
    refine (Subgroup.commutator_le.mpr ?_) hx
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab (π a) (π b)
  obtain ⟨a, b, hab'⟩ := exists_pair_ne Q
  obtain ⟨x, rfl⟩ := h.surj a
  obtain ⟨y, rfl⟩ := h.surj b
  exact hab' ((hL x).trans (hL y).symm)

end Facts

theorem card_quotient_center_of_sl25 {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    Nat.card (K ⧸ Subgroup.center K) = 60 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
  rw [CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e.symm,
    CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card e.symm] at h
  omega

theorem nonempty_alt5_of_sl25 {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite K := Finite.of_equiv _ e.symm.toEquiv
  have h4 : 4 ≤ Nat.card (ZMod 5) := by rw [Nat.card_zmod]; norm_num
  have : IsSimpleGroup (K ⧸ Subgroup.center K) :=
    CFSG.Quasithin.E22S.UK1.isSimpleGroup_quotient_center_of_equiv_sl2 h4 e
  exact CFSG.LargeExtraspecial.S12Tri.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (card_quotient_center_of_sl25 e)

theorem smallCentralQuotient_of_sl25 {K : Type} [Group K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    CFSG.ComponentClassification.RestrictedStd.SmallCentralQuotient K :=
  Or.inl ⟨5, 1, Nat.prime_five, by norm_num, le_rfl, by norm_num,
    CFSG.GH74.E2.lieModel_psl_two_five_of_alt (nonempty_alt5_of_sl25 e)⟩

section Inner

variable {Q : Type} [Group Q] {w : Q} {K : Subgroup Q}

theorem InnerComp5.orderOf_eq (h : InnerComp5 Q w K) : orderOf w = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.invol) h.ne_one

theorem InnerComp5.subgroupOf_equiv (h : InnerComp5 Q w K) :
    Nonempty (↥(K.subgroupOf (Subgroup.centralizer ({w} : Set Q))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨e⟩ := h.sl5
  exact ⟨(Subgroup.subgroupOfEquivOfLe h.le).trans e⟩

theorem InnerComp5.isComponentOf (h : InnerComp5 Q w K) :
    CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({w} : Set Q)) := by
  have h1 : CFSG.Assembly.IsComponentOf (K.subgroupOf (Subgroup.centralizer ({w} : Set Q))) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).mpr h.comp
  have h2 : CFSG.Open.IsComponentOf (K.subgroupOf (Subgroup.centralizer ({w} : Set Q))) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mp h1
  have h3 : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({w} : Set Q)) :=
    CFSG.Quasithin.isComponentOf_iff_subgroupOf.mpr ⟨h.le, h2⟩
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mpr h3

end Inner

theorem end415K_of_innerComp5_false {Q : Type} [Group Q]
    (hQ : ∀ [Finite Q], IsSimpleGroup Q → (∃ a b : Q, a * b ≠ b * a) →
      ∀ (w : Q) (K : Subgroup Q), InnerComp5 Q w K → False) : End415K Q := by
  intro V _ _ L Y z π h
  have := h.finite
  exact hQ h.isSimpleGroup h.nonabelian _ _ h.innerComp5

theorem end415K_of_sporCompData {s : TauCeti.SporadicName}
    (hd : CFSG.ComponentClassification.HarrisLit.SporCompData s) :
    End415K (Blueprint.NativeSporadic.Carrier s) := by
  refine end415K_of_innerComp5_false fun hsimple hnab w K h => ?_
  obtain ⟨e⟩ := h.subgroupOf_equiv
  exact hd.inner _ hsimple hnab ⟨MulEquiv.refl _⟩ w h.orderOf_eq _ h.comp
    (smallCentralQuotient_of_sl25 e)

end CFSG.HardMathSupport.Foote.Coordinator
