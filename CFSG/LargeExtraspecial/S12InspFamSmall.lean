module

public import CFSG.LargeExtraspecial.S12InspFamTools
public import CFSG.GH74.SmallRanks.PSU3
public import CFSG.LieType.SteinbergBRAltFiveGL3TwoRank
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.Monster.B.TwoA.Base.SymFiveAut
public import CFSG.Quasithin.Background.G118S3
public import CFSG.LargeExtraspecial.S12InspFamDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Equiv Equiv.Perm CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

namespace S12Insp5

theorem card_outer_eq_one_of_inner {Y : Type*} [Group Y]
    (h : ∀ ψ : MulAut Y, ∃ g : Y, ψ = MulAut.conj g) : Nat.card (Outer Y) = 1 := by
  have htop : inner Y = ⊤ := by
    rw [eq_top_iff]
    rintro ψ -
    obtain ⟨g, rfl⟩ := h ψ
    exact ⟨g, rfl⟩
  show (inner Y).index = 1
  rw [htop, Subgroup.index_top]

theorem card_eq_factorial_of_perm {X : Type} [Group X] {m : ℕ} (φ : X ≃* Equiv.Perm (Fin m)) :
    Nat.card X = m.factorial := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isElementaryAbelian_of_isElemAbelian {X : Type*} [Group X] {E : Subgroup X}
    (hE : CFSG.Open.IsElemAbelian 2 E) : IsElementaryAbelian 2 E where
  is_comm := hE.1.is_comm
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hE.2 x x.2)

theorem orderOf_sGL : orderOf CFSG.LieType.SteinbergBR.AutGL32.sGL = 2 ^ 2 :=
  orderOf_eq_prime_pow (p := 2) (n := 1) (by decide) (by decide)

theorem card_le_four_of_lieModel_PSL32 {X : Type} [Group X] (h : LieModel X .PSL 3 2 1)
    (E : Subgroup X) (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 2 := by
  obtain ⟨e⟩ := CFSG.LieType.SteinbergBR.AltFiveGL3.nonempty_equiv_GL32 h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' := isElementaryAbelian_of_isElemAbelian
    (CFSG.SectionRank.isElemAbelian_map hE e.toMonoidHom)
  have h1 := CFSG.LieType.SteinbergBR.card_le_sq_of_orderOf orderOf_sGL
    (by rw [CFSG.LieType.SteinbergBR.AutGL32.card_GL32]; decide) (E.map e.toMonoidHom)
  rwa [Subgroup.card_map_of_injective e.injective] at h1

theorem alt6_exists_conj_orderOf_five :
    ∀ a : Perm (Fin 6), Perm.sign a = 1 → a * a = 1 → a ≠ 1 →
      ∃ g : Perm (Fin 6), Perm.sign g = 1 ∧ (a * (g * a * g⁻¹)) ^ 5 = 1 ∧
        a * (g * a * g⁻¹) ≠ 1 := by
  decide +kernel

end S12Insp5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_lieModel_PSU33 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (h : LieModel (S.Xbar12 g) .PSU 3 3 1) : False := by
  have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hr := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_three hcl
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inr rfl) le_rfl Nat.prime_three le_rfl hcl).1
  simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
  exact false_of_twoRank_le_two haQ hne hn hS hr
    (Nat.le_of_dvd (by norm_num) (by norm_num at hout; exact hout))

theorem false_of_lieModel_PSL32 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t)
    (h : LieModel (S.Xbar12 g) .PSL 3 2 1) : False := by
  have hcl := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl Nat.prime_two le_rfl hcl).1
  simp only [CFSG.RankThree.OuterOrder.determinantParameter] at hout
  exact false_of_elemAbelian_le_four haQ hne hn hS
    (S12Insp5.card_le_four_of_lieModel_PSL32 h)
    (Nat.le_of_dvd (by norm_num) (by norm_num at hout; exact hout))

theorem false_of_perm_three_five {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 5 ≤ S.width) {t : S.O} (hS : S.S12Standing g t) {m : ℕ}
    (hm : m = 3 ∨ m = 5) (φ : S.Xbar12 g ≃* Equiv.Perm (Fin m)) : False := by
  have h16 := sixteen_dvd_card_Xbar12_mul_card_outer haQ hne hn hS
  rcases hm with rfl | rfl
  · have hO : Nat.card (Outer (S.Xbar12 g)) = 1 := by
      rw [Nat.card_congr (equivalence φ).toEquiv]
      refine S12Insp5.card_outer_eq_one_of_inner fun ψ => ?_
      obtain ⟨c, hc⟩ := CFSG.Quasithin.G11.G118.g118_perm_three_aut_inner ψ
      exact ⟨c, MulEquiv.ext fun x => (hc x).trans (MulAut.conj_apply c x).symm⟩
    rw [hO, S12Insp5.card_eq_factorial_of_perm φ] at h16
    exact absurd h16 (by decide)
  · have hO : Nat.card (Outer (S.Xbar12 g)) = 1 := by
      rw [Nat.card_congr (equivalence φ).toEquiv]
      refine S12Insp5.card_outer_eq_one_of_inner fun ψ => ?_
      obtain ⟨c, hc⟩ := CFSG.Monster.B.TwoA.sym5_conj_surjective ψ
      exact ⟨c, hc.symm⟩
    rw [hO, S12Insp5.card_eq_factorial_of_perm φ] at h16
    exact absurd h16 (by decide)

theorem false_of_mulEquiv_alt6 {g : G} {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hS : S.S12Standing g t)
    (φ : S.Xbar12 g ≃* alternatingGroup (Fin 6)) : False := by
  obtain ⟨-, ⟨d₀, hd₀, hcls⟩, hinv, hord, -⟩ := isTransClass34_Ebar12 ht htA hS
  set a : Perm (Fin 6) := (φ d₀ : Perm (Fin 6)) with ha
  have ha1 : a ≠ 1 := fun h =>
    (hinv d₀ hd₀).1 (φ.injective (Subtype.ext (by rw [← ha, h, map_one]; rfl)))
  have haa : a * a = 1 := by
    rw [ha, ← Subgroup.coe_mul, ← map_mul, (hinv d₀ hd₀).2, map_one]
    rfl
  obtain ⟨c, hcs, h5, h51⟩ := S12Insp5.alt6_exists_conj_orderOf_five a
    (Perm.mem_alternatingGroup.mp (φ d₀).2) haa ha1
  set c' : S.Xbar12 g := φ.symm ⟨c, Perm.mem_alternatingGroup.mpr hcs⟩ with hc'
  have hmem : c' * d₀ * c'⁻¹ ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) :=
    (hcls _).mpr (isConj_iff.mpr ⟨c', rfl⟩)
  have h4 := hord d₀ hd₀ _ hmem
  have h5' : orderOf (d₀ * (c' * d₀ * c'⁻¹)) = 5 := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← MulEquiv.orderOf_eq φ, ← Subgroup.orderOf_coe]
    refine orderOf_eq_prime ?_ ?_
    · simpa [hc', ha] using h5
    · simpa [hc', ha] using h51
  omega

end Setting

theorem inspU33 : InspU33 := by
  intro G _ _ _ S g t haQ hne hn _ _ hS _ h
  exact (Setting.false_of_lieModel_PSU33 haQ hne hn hS h).elim

theorem inspAlt6 : InspAlt6 := by
  intro G _ _ _ S g t _ _ _ ht htA hS _ h
  obtain ⟨φ⟩ := h
  exact (Setting.false_of_mulEquiv_alt6 ht htA hS φ).elim

end CFSG.LargeExtraspecial
