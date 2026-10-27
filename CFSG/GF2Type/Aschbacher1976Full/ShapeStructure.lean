module

public import CFSG.RankThree.GroupTheory.SteinbergBYSymplecticCritical
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXSmallKernelFiltrations
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm Subgroup
open scoped commutatorElement

section Crit

variable {P : Type*} [Group P]

abbrev Zof (D : Subgroup P) : Subgroup P := (center D).map D.subtype

structure CritData (D E R : Subgroup P) (z : P) : Prop where
  crit : ThompsonCritical D
  z_ord : orderOf z = 2
  z_mem : z ∈ Zof D
  z_uniq : ∀ x ∈ Zof D, orderOf x = 2 → x = z
  z_center : z ∈ center P
  center_uniq : ∀ x ∈ center P, orderOf x = 2 → x = z
  cyc : IsCyclic (Zof D)
  char : (Zof D).Characteristic
  cent : centralizer ((Zof D : Subgroup P) : Set P) = D
  ED : E ⊔ Zof D = D
  R_eq : R = centralizer (E : Set P)
  ER : E ⊔ R = ⊤
  RZ : R ⊓ centralizer ((Zof D : Subgroup P) : Set P) = Zof D
  E_normal : E.Normal
  R_normal : R.Normal
  cases : (E = ⊥ ∧ R = ⊤) ∨
    ∃ w : ℕ, 1 ≤ w ∧ IsExtraspecialPGroup 2 E ∧ Nat.card E = 2 ^ (1 + 2 * w) ∧
      E ⊓ R = zpowers z ∧ E ⊓ Zof D = zpowers z ∧ (center E).map E.subtype = zpowers z ∧
      Nat.card (D ⧸ center D) = 2 ^ (2 * w)

theorem exists_critData [Finite P] [Nontrivial P] (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    {D : Subgroup P} (hD : ThompsonCritical D) :
    ∃ (E R : Subgroup P) (z : P), CritData D E R z := by
  obtain ⟨-, hcp⟩ := RankThree.GroupTheory.SteinbergBY.symplectic_critical_subgroup_central_product
    hP hsymp
  obtain ⟨-, hcyc, hZchar, z, hzZ, hz, huniq, hzc, huniqP, hcZ, E, R, hEZ, hR, hER, -,
    hRZ, hEn, hRn, hcases, -, -⟩ := hcp D hD
  refine ⟨E, R, z, ⟨hD, hz, hzZ, huniq, hzc, huniqP, hcyc, hZchar, hcZ, hEZ, hR, hER, hRZ, hEn,
    hRn, ?_⟩⟩
  rcases hcases with ⟨-, hE, hR'⟩ | ⟨w, hw, -, hcard, -, hExtra, hEcard, -, hERz, hEZz, hEc, -⟩
  · exact Or.inl ⟨hE, hR'⟩
  · exact Or.inr ⟨w, hw, hExtra, hEcard, hERz, hEZz, hEc, hcard⟩

theorem sq_eq_one_of_mem_zpowers {z x : P} (hz : orderOf z = 2) (hx : x ∈ zpowers z) :
    x ^ 2 = 1 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]

namespace CritData

variable {D E R : Subgroup P} {z : P}

theorem Z_le_D (D : Subgroup P) : Zof D ≤ D :=
  RankThree.GroupTheory.SteinbergBY.map_center_le D

theorem Z_comm (D : Subgroup P) {y d : P} (hy : y ∈ Zof D) (hd : d ∈ D) : d * y = y * d :=
  mem_centralizer_iff.mp (RankThree.GroupTheory.SteinbergBY.map_center_le_centralizer D hy) d hd

theorem Z_normal (c : CritData D E R z) : (Zof D).Normal := by
  haveI := c.char
  exact normal_of_characteristic _

theorem exists_mul_of_mem_D (c : CritData D E R z) {d : P} (hd : d ∈ D) :
    ∃ e ∈ E, ∃ y ∈ Zof D, e * y = d := by
  haveI := c.Z_normal
  rw [← c.ED] at hd
  exact mem_sup_of_normal_right.mp hd

theorem E_le_D (c : CritData D E R z) : E ≤ D := by
  rw [← c.ED]
  exact le_sup_left

theorem D_eq_Z (c : CritData D E R z) (hE : E = ⊥) : D = Zof D := by
  have := c.ED
  rw [hE, bot_sup_eq] at this
  exact this.symm

theorem E_comm (c : CritData D E R z) : ∀ e ∈ E, ∀ e' ∈ E, ⁅e, e'⁆ ∈ zpowers z := by
  intro e he e' he'
  rcases c.cases with ⟨hE, -⟩ | ⟨w, -, hEx, -, -, -, hEc, -⟩
  · rw [hE, mem_bot] at he
    subst he
    simp
  · rw [← hEc]
    exact ⟨⁅(⟨e, he⟩ : E), ⟨e', he'⟩⁆,
      LocalAnalysis.GorensteinLyons.extraspecial_two_commutatorElement_mem_center hEx _ _, rfl⟩

theorem E_sq [Finite P] (c : CritData D E R z) : ∀ e ∈ E, e ^ 2 ∈ zpowers z := by
  intro e he
  rcases c.cases with ⟨hE, -⟩ | ⟨w, -, hEx, -, -, -, hEc, -⟩
  · rw [hE, mem_bot] at he
    subst he
    simp
  · rw [← hEc]
    exact ⟨⟨e, he⟩ ^ 2, LocalAnalysis.GorensteinLyons.extraspecial_two_sq_mem_center hEx _, rfl⟩

theorem E_four [Finite P] (c : CritData D E R z) : ∀ e ∈ E, e ^ 4 = 1 := by
  intro e he
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
  exact sq_eq_one_of_mem_zpowers c.z_ord (c.E_sq e he)

theorem E_R_comm (c : CritData D E R z) {e r : P} (he : e ∈ E) (hr : r ∈ R) : e * r = r * e := by
  rw [c.R_eq] at hr
  exact mem_centralizer_iff.mp hr e he

end CritData

theorem exists_max_critical [Finite P] (hP : IsPGroup 2 P) :
    ∃ D : Subgroup P, ThompsonCritical D ∧
      ∀ D' : Subgroup P, ThompsonCritical D' → Nat.card D' ≤ Nat.card D := by
  obtain ⟨C, hC⟩ := (CFSG.GroupTheory.PG.exists_thompsonCritical hP).1
  set S : Set ℕ := {n | ∃ D : Subgroup P, ThompsonCritical D ∧ Nat.card D = n} with hS
  have hne : S.Nonempty := ⟨_, C, hC, rfl⟩
  have hbdd : BddAbove S := ⟨Nat.card P, by
    rintro n ⟨D, -, rfl⟩
    exact Subgroup.card_le_card_group D⟩
  obtain ⟨D, hD, hDn⟩ := Nat.sSup_mem hne hbdd
  exact ⟨D, hD, fun D' hD' => hDn ▸ le_csSup hbdd ⟨D', hD', rfl⟩⟩

end Crit

section Lift

variable {G : Type*} [Group G] {K : Subgroup G}

abbrev lift (S : Subgroup K) : Subgroup G := S.map K.subtype

noncomputable def liftEquiv (S : Subgroup K) : ↥S ≃* ↥(lift S) :=
  S.equivMapOfInjective K.subtype K.subtype_injective

theorem lift_le (S : Subgroup K) : lift S ≤ K := Subgroup.map_subtype_le S

theorem mem_lift {S : Subgroup K} {x : K} : (x : G) ∈ lift S ↔ x ∈ S :=
  (Subgroup.mem_map_iff_mem K.subtype_injective)

theorem card_lift (S : Subgroup K) : Nat.card (lift S) = Nat.card S :=
  Subgroup.card_map_of_injective K.subtype_injective

theorem isCyclic_lift {S : Subgroup K} (h : IsCyclic S) : IsCyclic (lift S) :=
  ((liftEquiv S).isCyclic).mp h

theorem isExtraspecialPGroup_lift {p : ℕ} {S : Subgroup K} (h : IsExtraspecialPGroup p S) :
    IsExtraspecialPGroup p (lift S) :=
  LocalAnalysis.GorensteinLyons.isExtraspecialPGroup_congr_mulEquiv (liftEquiv S) h

theorem lift_sup (S T : Subgroup K) : lift (S ⊔ T) = lift S ⊔ lift T := Subgroup.map_sup _ _ _

theorem lift_inf (S T : Subgroup K) : lift (S ⊓ T) = lift S ⊓ lift T :=
  Subgroup.map_inf_eq _ _ _ K.subtype_injective

theorem lift_top : lift (⊤ : Subgroup K) = K := by
  rw [lift, Subgroup.map_top, Subgroup.range_subtype]

theorem lift_zpowers (x : K) : lift (zpowers x) = zpowers (x : G) := by
  rw [lift, MonoidHom.map_zpowers]
  rfl

end Lift

end CFSG.GF2Type.Aschbacher1976Full.Shape
