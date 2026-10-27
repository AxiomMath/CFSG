module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure NoncentralConfig (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M D U : Subgroup G) (u : G) : Prop where
  setting : Setting G
  sigma : p ∈ rankThreeSigmaA G
  ext : ExtremalObstruction p P M D
  PD : (P : Subgroup G) ≤ normalizer (D : Set G)
  UD : U < D
  PU : (P : Subgroup G) ≤ normalizer (U : Set G)
  Ue : IsElemAbelian p U
  Uc : Nat.card U = p ^ 2
  rank3 : 3 ≤ CFSG.Open.pRank p ((P : Subgroup G) ⊓ centralizer (U : Set G))
  NU : normalizer (U : Set G) ≤ M
  uU : u ∈ U
  u1 : u ≠ 1
  uZ : u ∉ (center D).map D.subtype

omit [Finite G] in
theorem commutator_mul_aux_7 {g h x : G}
    (hgb : g * (h * x * h⁻¹ * x⁻¹) = (h * x * h⁻¹ * x⁻¹) * g)
    (hab : (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) = (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹)) :
    g * h * x * (g * h)⁻¹ * x⁻¹ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) :=
  calc g * h * x * (g * h)⁻¹ * x⁻¹
      = g * (h * x * h⁻¹ * x⁻¹) * x * g⁻¹ * x⁻¹ := by group
    _ = (h * x * h⁻¹ * x⁻¹) * g * x * g⁻¹ * x⁻¹ := by rw [hgb]
    _ = (h * x * h⁻¹ * x⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    _ = (g * x * g⁻¹ * x⁻¹) * (h * x * h⁻¹ * x⁻¹) := hab.symm

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem prime : p.Prime := sigmaA_prime p hc.sigma

theorem odd : p ≠ 2 := sigmaA_odd p hc.sigma

theorem nonab : ¬ IsMulCommutative D :=
  (hc.ext.exists_normal_plane hc.setting hc.sigma hc.PD).1

theorem card_D : Nat.card D = p ^ 3 :=
  hc.ext.card_eq_of_not_isMulCommutative hc.prime hc.odd hc.nonab

theorem pow_D : ∀ x ∈ D, x ^ p = 1 :=
  (hc.ext.pow_eq_one_and_commutator_mem hc.prime hc.odd).1

theorem D_le_P : D ≤ (P : Subgroup G) := hc.ext.obstruction.2.1

theorem card_Z : Nat.card ((center D).map D.subtype) = p :=
  hc.ext.card_center_eq hc.prime hc.odd hc.nonab

theorem Z_comm {z : G} (hz : z ∈ (center D).map D.subtype) {g : G} (hg : g ∈ (P : Subgroup G)) :
    g * z = z * g :=
  mem_centralizer_iff.mp (hc.ext.center_le_centralizer hc.prime hc.odd hc.nonab hz) g hg

theorem U_le_D : U ≤ D := hc.UD.le

theorem U_le_P : U ≤ (P : Subgroup G) := hc.U_le_D.trans hc.D_le_P

theorem U_comm {a b : G} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a :=
  congrArg Subtype.val (hc.Ue.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem pow_U {a : G} (ha : a ∈ U) : a ^ p = 1 := hc.Ue.2 a ha

theorem exists_Z_gen : ∃ z ∈ (center D).map D.subtype, z ≠ 1 ∧ orderOf z = p ∧
    zpowers z = (center D).map D.subtype := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hZc := hc.card_Z
  have hZne : (center D).map D.subtype ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hZc
    exact hprime.one_lt.ne hZc
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzp : z ^ p = 1 := hc.pow_D z (map_subtype_le _ hzZ)
  have hord : orderOf z = p := orderOf_eq_prime hzp hz1'
  refine ⟨z, hzZ, hz1', hord, ?_⟩
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzZ) ?_
  rw [hZc, Nat.card_zpowers, hord]

theorem Z_le_U : (center D).map D.subtype ≤ U := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hDP := hc.D_le_P
  have hUt : (U.subgroupOf D).Normal :=
    (normal_subgroupOf_iff_le_normalizer hc.U_le_D).2 (hDP.trans hc.PU)
  have hDp : IsPGroup p D := P.isPGroup'.to_le hDP
  have : Group.IsNilpotent D := hDp.isNilpotent
  have hUne : U.subgroupOf D ≠ ⊥ := by
    intro h
    have hmem : (⟨u, hc.U_le_D hc.uU⟩ : D) ∈ U.subgroupOf D := hc.uU
    rw [h, mem_bot] at hmem
    exact hc.u1 (congrArg Subtype.val hmem)
  obtain ⟨⟨q, hq⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hUne)
  obtain ⟨hqU, hqZ⟩ := mem_inf.mp hq
  obtain ⟨z, hzZ, hz1, hord, hzeq⟩ := hc.exists_Z_gen
  have hqG : (q : G) ∈ (center D).map D.subtype := ⟨q, hqZ, rfl⟩
  have hq1' : (q : G) ≠ 1 := by
    intro h
    apply hq1
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hqp : (q : G) ^ p = 1 := hc.pow_D q q.2
  have hordq : orderOf (q : G) = p := orderOf_eq_prime hqp hq1'
  have hzq : zpowers (q : G) = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hqG) ?_
    rw [hc.card_Z, Nat.card_zpowers, hordq]
  rw [← hzq]
  exact zpowers_le.mpr hqU

theorem U_eq : U = (center D).map D.subtype ⊔ zpowers u := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hle : (center D).map D.subtype ⊔ zpowers u ≤ U :=
    sup_le hc.Z_le_U (zpowers_le.mpr hc.uU)
  have hcomm : ∀ z ∈ (center D).map D.subtype, z * u = u * z := fun z hz =>
    hc.U_comm (hc.Z_le_U hz) hc.uU
  have hcard : Nat.card ↥((center D).map D.subtype ⊔ zpowers u) = p ^ 2 := by
    rw [card_sup_zpowers hprime _ (hc.pow_U hc.uU) hc.uZ hcomm, hc.card_Z, pow_two]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hcard, hc.Uc]

theorem orderOf_u : orderOf u = p :=
  have : Fact p.Prime := ⟨hc.prime⟩
  orderOf_eq_prime (hc.pow_U hc.uU) hc.u1

theorem inf_centralizer_eq :
    (P : Subgroup G) ⊓ centralizer ({u} : Set G) = (P : Subgroup G) ⊓ centralizer (U : Set G) := by
  refine le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hc.uU)))
  rintro g ⟨hgP, hgu⟩
  refine ⟨hgP, ?_⟩
  have hgu' : g * u = u * g := mem_centralizer_singleton_iff.mp hgu
  have hU : U ≤ centralizer ({g} : Set G) := by
    rw [hc.U_eq]
    refine sup_le (fun z hz => ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (hc.Z_comm hz hgP).symm
    · exact mem_centralizer_singleton_iff.mpr hgu'.symm
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hU hx)

theorem exists_not_comm : ∃ x ∈ (P : Subgroup G), x * u ≠ u * x := by
  by_contra hall
  push Not at hall
  apply hc.uZ
  exact hc.ext.mem_center_of_mem_centralizer_sylow hc.prime hc.odd hc.nonab
    (hc.U_le_P hc.uU) (mem_centralizer_iff.mpr fun g hg => hall g hg)
    (hc.pow_U hc.uU)

theorem commutator_mem_Z {g : G} (hg : g ∈ (P : Subgroup G)) :
    g * u * g⁻¹ * u⁻¹ ∈ (center D).map D.subtype := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨z, hzZ, hz1, hord, hzeq⟩ := hc.exists_Z_gen
  have hzU : z ∈ U := hc.Z_le_U hzZ
  have hup := hc.pow_U hc.uU
  have hdz : u ∉ zpowers z := by
    rw [hzeq]
    exact hc.uZ
  have hcd : u * z = z * u := hc.U_comm hc.uU hzU
  have hnz : g * z = z * g := hc.Z_comm hzZ hg
  obtain ⟨a, b, hab⟩ := exists_pow_mul_pow_of_mem_plane hc.Ue hc.Uc hzU hz1 hc.uU hdz
    ((mem_normalizer_iff.1 (hc.PU hg) u).1 hc.uU)
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
  have hk' : g ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨β, hβ⟩ := exists_conj_pow_eq_pow_mul_pow hcd hnz hab (p ^ k)
  rw [hk', inv_one, mul_one, one_mul] at hβ
  have h1 := natCast_eq_one_of_eq_pow_mul_pow hup hdz hβ
  have ha : (a : ZMod p) = 1 := by
    rwa [Nat.cast_pow, ZMod.pow_card_pow] at h1
  have hb' := conj_eq_mul_pow_of_natCast_eq_one hup hab ha
  rw [hb']
  have hcomm : u * z ^ b = z ^ b * u := (Commute.pow_right hcd b).eq
  rw [hcomm, mul_inv_cancel_right]
  exact pow_mem hzZ b

theorem PR : (P : Subgroup G) ≤
    normalizer (((P : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) := by
  rw [hc.inf_centralizer_eq]
  exact (le_inf le_normalizer ((hc.PU).trans (normalizer_le_normalizer_centralizer U))).trans
    inf_normalizer_le_normalizer_inf

theorem card_index : Nat.card (P : Subgroup G) =
    p * Nat.card ((P : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hZc := hc.card_Z
  let φ : (P : Subgroup G) →* ((center D).map D.subtype) :=
    { toFun := fun g => ⟨(g : G) * u * (g : G)⁻¹ * u⁻¹, hc.commutator_mem_Z g.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by
        have hb := hc.commutator_mem_Z h.2
        have hg' := hc.commutator_mem_Z g.2
        change (g : G) * h * u * ((g : G) * h)⁻¹ * u⁻¹ =
          ((g : G) * u * (g : G)⁻¹ * u⁻¹) * ((h : G) * u * (h : G)⁻¹ * u⁻¹)
        exact commutator_mul_aux_7 (hc.Z_comm hb g.2)
          (hc.U_comm (hc.Z_le_U hg') (hc.Z_le_U hb))) }
  have hker : φ.ker.map (P : Subgroup G).subtype =
      (P : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.2, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : (g : G) * u * (g : G)⁻¹ * u⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    · rintro ⟨hxP, hxu⟩
      refine ⟨⟨x, hxP⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      have h1 : x * u = u * x := mem_centralizer_singleton_iff.mp hxu
      change x * u * x⁻¹ * u⁻¹ = 1
      rw [h1]
      group
  have hrange : Nat.card φ.range = p := by
    have hdvd : Nat.card φ.range ∣ Nat.card ((center D).map D.subtype) :=
      Subgroup.card_subgroup_dvd_card _
    rw [hZc] at hdvd
    rcases (Nat.dvd_prime hprime).mp hdvd with h | h
    · exfalso
      obtain ⟨x, hxP, hx⟩ := hc.exists_not_comm
      have hmem : φ ⟨x, hxP⟩ ∈ φ.range := ⟨⟨x, hxP⟩, rfl⟩
      have hbot : φ.range = ⊥ := (Subgroup.card_eq_one).mp h
      rw [hbot, mem_bot] at hmem
      apply hx
      have h1 : x * u * x⁻¹ * u⁻¹ = 1 := congrArg Subtype.val hmem
      exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
    · exact h
  have h1 : Nat.card φ.ker =
      Nat.card ((P : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) := by
    rw [← hker, card_map_of_injective (P : Subgroup G).subtype_injective]
  have hcard := card_ker_mul_card_range φ
  rw [h1, hrange] at hcard
  rw [← hcard, mul_comm]

end NoncentralConfig

end CFSG.LocalAnalysis.RankThreeTheoremC
