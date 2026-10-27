module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11
  CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof


theorem le_commutator_of_isPerfect {G : Type*} [Group G] {N C : Subgroup G}
    (hN : Group.IsPerfect N) (hNC : N ≤ C) : N ≤ ⁅C, C⁆ := by
  have h := congrArg (Subgroup.map N.subtype) hN.commutator_eq_top
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact fun x hx => Subgroup.commutator_mono hNC hNC (by rw [h]; exact hx)

theorem le_commutator_of_isQuasisimple {G : Type*} [Group G] {N C : Subgroup G}
    (hN : CFSG.IsQuasisimple N) (hNC : N ≤ C) : N ≤ ⁅C, C⁆ :=
  le_commutator_of_isPerfect hN.1 hNC

section Classes

variable {K : Type} [Field K] [Finite K]

theorem commutator_centralizer_of_mem_short (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    {z : adjointGroup .G2 K} (hzS : z ∈ g2ShortSL2 K) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ ∧
      3 ∣ Nat.card ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ := by
  obtain ⟨N, hNC, hcomm, hNq, x, hxN, -, hx1, hx3⟩ :=
    KS11Lie7Proof.g2ThreeACent_holds K hK3 hK4 z hzS hz3 hz1
  have hEq : ⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ = N := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_)
      (le_commutator_of_isQuasisimple hNq hNC)
    rw [commutatorElement_def]
    exact hcomm a ha b hb
  rw [hEq]
  refine ⟨hNq, ?_⟩
  have : orderOf (⟨x, hxN⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  rw [← this]
  exact orderOf_dvd_natCard _

theorem commutator_centralizer_of_mem_long (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K} (hzM : z ∈ g2LongSL2 K) (hz3 : z ^ 3 = 1)
    (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ ∧
      3 ∣ Nat.card ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ := by
  obtain ⟨hB1, -⟩ := g2ThreeBCent_holds K hK3 hK4 z hzM hz3 hz1
  have hSC : g2ShortSL2 K ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := fun s hs => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact g2Short_commute_g2Long hs hzM
  have hq := isQuasisimple_g2ShortSL2 (K := K) hK4
  have hEq : ⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ = g2ShortSL2 K := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_)
      (le_commutator_of_isQuasisimple hq hSC)
    rw [commutatorElement_def]
    exact hB1 a ha b hb
  rw [hEq]
  refine ⟨hq, ?_⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_g2ShortSL2 (K := K)
  rw [← Nat.card_congr e.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have h2 : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  exact Dvd.dvd.mul_left (h2 ▸ Dvd.dvd.mul_right h3 _) _

theorem centralizer_conj_eq_map {G : Type*} [Group G] (g z : G) :
    Subgroup.centralizer ({g * z * g⁻¹} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply]; group⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * x) * g := by rw [hx]
      _ = z * (g⁻¹ * x * g) := by group
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * y * g⁻¹ * (g * z * g⁻¹) = g * (y * z) * g⁻¹ := by group
      _ = g * (z * y) * g⁻¹ := by rw [hy]
      _ = g * z * g⁻¹ * (g * y * g⁻¹) := by group

theorem commutator_centralizer_isQuasisimple (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K)
    (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    CFSG.IsQuasisimple ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ ∧
      3 ∣ Nat.card ↥⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆ := by
  obtain ⟨g, hg⟩ := KS11Lie7Proof.g2ThreeConjSL2_holds K hK3 hK4 z hz3 hz1
  have hz'3 : (g * z * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hz3]
    group
  have hz'1 : g * z * g⁻¹ ≠ 1 := fun h => hz1 (by
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group)
  have hcls := hg.elim
    (fun h => commutator_centralizer_of_mem_short hK3 hK4 h hz'3 hz'1)
    (fun h => commutator_centralizer_of_mem_long hK3 hK4 h3 h hz'3 hz'1)
  rw [centralizer_conj_eq_map, ← Subgroup.map_commutator] at hcls
  let e := Subgroup.equivMapOfInjective
    ⁅Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)),
      Subgroup.centralizer ({z} : Set (adjointGroup .G2 K))⁆
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hcls.1, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  exact hcls.2

end Classes

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.G2Aux
