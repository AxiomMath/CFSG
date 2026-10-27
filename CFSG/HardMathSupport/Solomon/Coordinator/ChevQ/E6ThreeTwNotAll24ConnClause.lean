module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Types
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnType

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem relIndex_zpowers_sup_zpowers {X : Type} [Group X] {E : Subgroup (MulAut X)}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) {f e : MulAut X} (hf : f ∈ E)
    (he : e ∈ E) (hf1 : f ≠ 1) (hne : e ∉ Subgroup.zpowers f) :
    (Subgroup.zpowers f ⊔ Subgroup.zpowers e).relIndex E = 3 := by
  have hcomm : Commute f e := congrArg Subtype.val (hE.1.is_comm.comm ⟨f, hf⟩ ⟨e, he⟩)
  have hFE : Subgroup.zpowers f ⊔ Subgroup.zpowers e ≤ E :=
    sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 he)
  exact KSNotAll24.relIndex_eq_three hFE hEc
    (KSNotAll24.card_zpowers_sup_zpowers hcomm hf1 (hE.2 f hf) (hE.2 e he) hne)

theorem exists_mem_not_mem_zpowers {X : Type} [Group X] {E : Subgroup (MulAut X)}
    (hEc : Nat.card E = 3 ^ 3) {f : MulAut X} (hf3 : f ^ 3 = 1) :
    ∃ e ∈ E, e ∉ Subgroup.zpowers f := by
  by_contra hcon
  push Not at hcon
  have hfin : IsOfFinOrder f := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hf3⟩
  haveI : Finite (Subgroup.zpowers f) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact hfin.orderOf_pos.ne')
  have hle : Nat.card E ≤ Nat.card (Subgroup.zpowers f) := Subgroup.card_le_of_le hcon
  have hord : orderOf f ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hf3)
  rw [Nat.card_zpowers, hEc] at hle
  omega

section Conn

set_option linter.unusedSectionVars false

@[expose] def TwE6ComponentShape {X : Type} [Group X] (J : Subgroup X) : Prop :=
  3 ∣ Nat.card (J ⧸ Subgroup.center J) →
    (∃ (d : TauCeti.ValidLieTypeIndex)
        (_ : (J ⧸ Subgroup.center J) ≃* (TauCeti.CFSGIndex.lie d).Group),
        3 ≠ d.1.characteristic ∧ ¬ AGLEmbeddingD2.IsD2SeitzException 3 d.1) ∨
      NoPlane3 (J ⧸ Subgroup.center J)

theorem twE6ComponentType_of_shape {X : Type} [Group X] [Finite X] {J : Subgroup X}
    {f : MulAut X} (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)))
    (hshape : TwE6ComponentShape J) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center J)) :
    TwE6ComponentType J := by
  by_cases h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)
  · rcases hshape h3 with ⟨d, e, hd, hex⟩ | hno
    · exact Or.inl ⟨hZ, d, e, hd, hex⟩
    · exact Or.inr (Or.inl hno)
  · exact Or.inr (Or.inr (KSNotAll24.not_three_dvd_card_of_perfect hJ.2.2.1 h3))

theorem twE6ComponentShape_of_odd (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hK2 : ringChar K ≠ 2) (hσ : ∀ c, σ c = c ^ q)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) {f : MulAut (twistedE6RootGroup K σ)}
    (hf3 : f ^ 3 = 1) {J : Subgroup (twistedE6RootGroup K σ)}
    (hJ : CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))) :
    TwE6ComponentShape J := by
  intro h3J
  have h := KSNotAll24.component_isChevSimple K σ q hK3 hσ hKq hq2 hf3 hJ h3J
  rcases KSNotAll24.chevSimple_odd hK2 hK3 h with ⟨d, ⟨e⟩, hd, hex⟩ | hno
  · exact Or.inl ⟨d, e, hd, hex⟩
  · exact Or.inr hno

@[expose] def TwE6ConnLine (K : Type) [Field K] (σ : K ≃+* K) (q : ℕ)
    (f : MulAut (twistedE6RootGroup K σ)) : Prop :=
  ∃ h : twistedE6InndiagGL K σ, twistedE6InndiagConj K σ h = f ∧
    twE6MatFixDim K σ h ∈ ({28, 36, 46} : Set ℕ) ∧ (q = 8 → twE6MatFixDim K σ h ≠ 28)

@[expose] def TwE6ConnCentre : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → TwE6ConnLine K σ q f →
        ∀ J : Subgroup (twistedE6RootGroup K σ),
          CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) →
            ¬ 3 ∣ Nat.card (Subgroup.center J)

@[expose] def TwE6ConnShapeEven : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E → ringChar K = 2 →
      ∀ f ∈ E, f ≠ 1 → TwE6ConnLine K σ q f →
        ∀ J : Subgroup (twistedE6RootGroup K σ),
          CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f)) → TwE6ComponentShape J

@[expose] def TwE6ConnGen : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))), TwE6Cube K σ q E →
      ∀ f ∈ E, f ≠ 1 → TwE6ConnLine K σ q f → TwE6LineGenAt K σ E f

theorem twE6LineComponentsAt_of_conn (hC : TwE6ConnCentre) (hS : TwE6ConnShapeEven)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hcube : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    (hconn : TwE6ConnLine K σ q f) : TwE6LineComponentsAt K σ E f := by
  have hq2 : 2 ≤ q := by
    have := Nat.le_of_dvd (by omega) hcube.three_dvd
    omega
  have hf3 : f ^ 3 = 1 := hcube.elemAbelian.2 f hfE
  intro J hJ
  refine ⟨?_, ?_⟩
  · obtain ⟨h, hh, hdim, -⟩ := hconn
    have hinj := twE6_conj_injective K σ q hcube.frob hcube.card_field hq2
    have hh1 : h ≠ 1 := by
      rintro rfl
      exact hf1 (hh.symm.trans (map_one _))
    have hh3 : h ^ 3 = 1 := by
      apply hinj
      rw [map_pow, hh, map_one]
      exact hf3
    exact KSNotAll24.components_invariant_of_mem K σ q hcube.char_ne_three hcube.frob
      hcube.card_field hq2 hcube.elemAbelian hfE h hh hh1 hh3 hdim J hJ
  · have hshape : TwE6ComponentShape J := by
      by_cases h2 : ringChar K = 2
      · exact hS K σ q E hcube h2 f hfE hf1 hconn J hJ
      · exact twE6ComponentShape_of_odd K σ q hcube.char_ne_three h2 hcube.frob
          hcube.card_field hq2 hf3 hJ
    exact twE6ComponentType_of_shape hJ hshape (hC K σ q E hcube f hfE hf1 hconn J hJ)

theorem twE6LineStructureAt_of_conn (hC : TwE6ConnCentre) (hS : TwE6ConnShapeEven)
    (hG : TwE6ConnGen) {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hcube : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hfE : f ∈ E) (hf1 : f ≠ 1)
    (hconn : TwE6ConnLine K σ q f) : TwE6LineStructureAt K σ E f :=
  ⟨twE6LineComponentsAt_of_conn hC hS hcube hfE hf1 hconn, hG K σ q E hcube f hfE hf1 hconn⟩

theorem twE6LineStructureA5_of_residuals (hC : TwE6ConnCentre) (hS : TwE6ConnShapeEven)
    (hG : TwE6ConnGen) : TwE6LineStructureA5 := by
  intro K _ _ σ q E hcube f hfE hf1 hdim
  obtain ⟨h, hh, hd⟩ := hdim
  exact twE6LineStructureAt_of_conn hC hS hG hcube hfE hf1
    ⟨h, hh, by rw [hd]; simp, fun _ => by rw [hd]; norm_num⟩

theorem twE6LineStructureA1A4_of_residuals (hC : TwE6ConnCentre) (hS : TwE6ConnShapeEven)
    (hG : TwE6ConnGen) : TwE6LineStructureA1A4 := by
  intro K _ _ σ q E hcube hq8 f hfE hf1 hdim
  obtain ⟨h, hh, hd⟩ := hdim
  exact twE6LineStructureAt_of_conn hC hS hG hcube hfE hf1
    ⟨h, hh, by rw [hd]; simp, fun h8 => absurd h8 hq8⟩

theorem twE6LineStructureD5_of_residuals (hC : TwE6ConnCentre) (hS : TwE6ConnShapeEven)
    (hG : TwE6ConnGen) : TwE6LineStructureD5 := by
  intro K _ _ σ q E hcube f hfE hf1 hdim
  obtain ⟨h, hh, hd⟩ := hdim
  exact twE6LineStructureAt_of_conn hC hS hG hcube hfE hf1
    ⟨h, hh, by rw [hd]; simp, fun _ => by rw [hd]; norm_num⟩

end Conn

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
