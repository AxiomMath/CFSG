module

public import CFSG.LargeExtraspecial.DW2AOutOrth
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.RankThree.Classical.SteinbergR3EHigherSymplecticOuterOrder
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
public import CFSG.LieType.SteinbergBRSmallAltSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms

theorem chevalleyExceptionalModel_of_lieModel {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t ∈ chevalleyExceptionalTags) (h : LieModel X t n p f) :
    ChevalleyExceptionalModel X t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem lieModel_POmegaPlus_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {n p f : ℕ} (h : LieModel X .POmegaPlus n p f) : LieModel X' .POmegaPlus n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

theorem isPGroup_outer_psl {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 3 ≤ n)
    (h : LieModel X .PSL n 2 1) : IsPGroup 2 (Outer X) := by
  have := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) hn Nat.prime_two le_rfl (statedClassicalModel_of_lieModel (by decide) h)).1
  exact isPGroup_of_card_dvd_two (by
    simpa [CFSG.RankThree.OuterOrder.determinantParameter] using this)

theorem isPGroup_outer_psu {X : Type} [Group X] [Finite X] (h : LieModel X .PSU 3 3 1) :
    IsPGroup 2 (Outer X) := by
  have := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) le_rfl Nat.prime_three le_rfl (statedClassicalModel_of_lieModel (by decide) h)).1
  have h1 : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (3 ^ 1) = 1 := by
    norm_num [CFSG.RankThree.OuterOrder.determinantParameter]
  rw [h1] at this
  exact isPGroup_of_card_dvd_two this

theorem isPGroup_outer_psp {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n)
    (h : LieModel X .PSp n 2 1) : IsPGroup 2 (Outer X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel (by decide) h
  have h1 := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    Nat.prime_two le_rfl hn hK).1
  exact isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two
    ((by simpa using h1 : _ ∣ 1).trans (one_dvd 2)))

theorem isPGroup_outer_E78
    {X : Type} [Group X] {t : StatedLieTag} (ht : t = .E7 ∨ t = .E8)
    (h : LieModel X t 0 2 1) : IsPGroup 2 (Outer X) := by
  rcases ht with rfl | rfl
  · obtain ⟨-, hm⟩ := chevalleyExceptionalModel_of_lieModel (by decide) h
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E7 hm
    refine isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two ?_)
    simpa using (CFSG.LieType.Chevalley.ordinary_E_outer_order_Cartan_divisor .E7
      (Or.inr (Or.inl rfl)) Nat.prime_two le_rfl K hK 2 1 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))).1
  · obtain ⟨-, hm⟩ := chevalleyExceptionalModel_of_lieModel (by decide) h
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E8 hm
    refine isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two ?_)
    have := (CFSG.LieType.Chevalley.ordinary_E_outer_order_Cartan_divisor .E8
      (Or.inr (Or.inr rfl)) Nat.prime_two le_rfl K hK 1 1 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))).1
    exact (by simpa using this : _ ∣ 1).trans (one_dvd 2)

theorem isPGroup_outer_E6
    {X : Type} [Group X] (h : LieModel X .E6 0 2 1) :
    IsPGroup 2 (Outer X) := by
  obtain ⟨-, hm⟩ := chevalleyExceptionalModel_of_lieModel (by decide) h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .E6 hm
  refine isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two ?_)
  obtain ⟨Φ, -, hker, -⟩ := CFSG.LieType.Chevalley.exists_outer_hom_E (τ := .E6) (K := K)
    (Or.inl rfl)
  have hu : ∀ u : Kˣ, u = 1 := by
    have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]; rfl
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact fun u => Subsingleton.elim u 1
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, eq_bot_iff]
    rintro _ ⟨a, rfl⟩
    rw [show a = 1 from funext fun i => hu (a i), map_one]
    exact Subgroup.one_mem _
  have h1 := Subgroup.card_dvd_of_injective Φ hinj
  rw [Nat.card_prod, (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    hK).1, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at h1
  simpa [CFSG.LieType.Chevalley.exactE] using h1

theorem isPGroup_outer_F4
    {X : Type} [Group X] (h : LieModel X .F4 0 2 1) :
    IsPGroup 2 (Outer X) := by
  obtain ⟨-, hm⟩ := chevalleyExceptionalModel_of_lieModel (by decide) h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
    charP_of_card_eq_prime_pow (p := 2) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form le_rfl K hK
  refine isPGroup_outer_of_mulEquiv e (isPGroup_of_card_dvd_two ?_)
  have hI : CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K) = Θ.ker := hker.symm
  have e₂ := (QuotientGroup.quotientMulEquivOfEq hI).trans
    (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  change Nat.card (Outer (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)) ∣ 2
  rw [Nat.card_congr e₂.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem isPGroup_outer_alt6 {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    IsPGroup 2 (Outer X) :=
  isPGroup_outer_of_mulEquiv e CFSG.LieType.SteinbergBR.SmallAlt.isPGroup_outer_six

end CFSG.LargeExtraspecial.DW
