module

public import CFSG.CharacterTheory.Wreathed.SquareRootSmallCharacterRigidityCentralizers

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare
open scoped Classical

theorem normal_odd_elements_eq_oddCore {H : Type*} [Group H]
    (N : Subgroup H) (hNnormal : N.Normal) (hNodd : Odd (Nat.card N))
    (hmem : ∀ c : H, c ∈ N ↔ Odd (orderOf c)) : N = CFSG.oddCore H := by
  apply le_antisymm
  · exact le_sSup ⟨hNnormal, hNodd⟩
  · apply sSup_le
    intro M hM c hc
    apply (hmem c).mpr
    have ho := hM.2.of_dvd_nat (orderOf_dvd_natCard (⟨c, hc⟩ : M))
    rwa [Subgroup.orderOf_mk] at ho

@[expose] def complementaryCentralProductEquiv {H : Type*} [Group H]
    (N Z : Subgroup H) (hinf : N ⊓ Z = ⊥) (hsup : N ⊔ Z = ⊤)
    (hcentral : Z ≤ Subgroup.center H) : N × Z ≃* H := by
  let comm : ∀ n : N, ∀ z : Z, Commute (N.subtype n) (Z.subtype z) :=
    fun n z => Subgroup.mem_center_iff.mp (hcentral z.property) n
  let φ := N.subtype.noncommCoprod Z.subtype comm
  apply MulEquiv.ofBijective φ
  constructor
  · exact Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hinf)
  · apply MonoidHom.range_eq_top.mp
    exact (MonoidHom.noncommCoprod_range N.subtype Z.subtype comm).trans
      (by simpa only [Subgroup.subtype_range] using hsup)

theorem complementaryCentralProductEquiv_apply {H : Type*} [Group H]
    (N Z : Subgroup H) (hinf : N ⊓ Z = ⊥) (hsup : N ⊔ Z = ⊤)
    (hcentral : Z ≤ Subgroup.center H) (n : N) (z : Z) :
    complementaryCentralProductEquiv N Z hinf hsup hcentral (n, z) =
      (n : H) * (z : H) := rfl

theorem root_cyclic_subgroup_le_center {G : Type*} [Group G] (y : G) :
    Subgroup.zpowers
      (⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({y} : Set G)) ≤
      Subgroup.center (Subgroup.centralizer ({y} : Set G)) := by
  apply Subgroup.zpowers_le.mpr
  apply Subgroup.mem_center_iff.mpr
  intro c
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp c.property

theorem maximal_root_centralizer_direct_product {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    let C := Subgroup.centralizer ({y} : Set G)
    let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    Odd (Nat.card (CFSG.oddCore C)) ∧
      (∀ c : C, c ∈ CFSG.oddCore C ↔ Odd (orderOf (c : G))) ∧
      (CFSG.oddCore C).Characteristic ∧
      CFSG.oddCore C ⊓ Subgroup.zpowers yC = ⊥ ∧
      CFSG.oddCore C ⊔ Subgroup.zpowers yC = ⊤ ∧
      IsPGroup 2 (C ⧸ CFSG.oddCore C) ∧ IsCyclic (C ⧸ CFSG.oddCore C) ∧
      ∃ E : CFSG.oddCore C × Subgroup.zpowers yC ≃* C,
        (∀ k : CFSG.oddCore C, ∀ z : Subgroup.zpowers yC,
          E (k, z) = (k : C) * (z : C)) ∧
        (∀ c : C, ((E.symm c).1 : C) * ((E.symm c).2 : C) = c) ∧
        ∃ φ : Subgroup.zpowers yC ≃* C ⧸ CFSG.oddCore C,
          ∀ z : Subgroup.zpowers yC, φ z = QuotientGroup.mk' (CFSG.oddCore C) z := by
  intro C yC
  obtain ⟨N, hnormal, hodd, hmem, hchar, hinf, hsup, hquot, hcyc, φ, hφ⟩ :=
    maximal_root_centralizer_odd_complement n hn S e y hy
  have hN : N = CFSG.oddCore C := normal_odd_elements_eq_oddCore N hnormal hodd hmem
  subst N
  let E := complementaryCentralProductEquiv (CFSG.oddCore C) (Subgroup.zpowers yC)
    hinf hsup (root_cyclic_subgroup_le_center y)
  refine ⟨hodd, ?_, hchar, hinf, hsup, hquot, hcyc, E, ?_, ?_, φ, hφ⟩
  · intro c
    rw [hmem, Subgroup.orderOf_coe]
  · exact fun k z => complementaryCentralProductEquiv_apply _ _ _ _ _ k z
  · intro c
    have he := E.apply_symm_apply c
    rw [show E (E.symm c) = ((E.symm c).1 : C) * ((E.symm c).2 : C) from rfl] at he
    exact he

@[expose] def centralizerRootEquiv {G : Type*} [Group G] (y : G) :
    Subgroup.zpowers
      (⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({y} : Set G)) ≃* Subgroup.zpowers y := by
  let C := Subgroup.centralizer ({y} : Set G)
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact ((Subgroup.zpowers yC).equivMapOfInjective C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr (MonoidHom.map_zpowers C.subtype yC))

theorem centralizerRootEquiv_apply {G : Type*} [Group G] (y : G)
    (z : Subgroup.zpowers
      (⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        Subgroup.centralizer ({y} : Set G))) :
    (centralizerRootEquiv y z : G) = ((z : Subgroup.centralizer ({y} : Set G)) : G) := rfl

theorem maximal_root_centralizer_ambient_product {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    let C := Subgroup.centralizer ({y} : Set G)
    ∃ E : CFSG.oddCore C × Subgroup.zpowers y ≃* C,
      (∀ k : CFSG.oddCore C, ∀ z : Subgroup.zpowers y,
        (E (k, z) : G) = ((k : C) : G) * (z : G)) ∧
      (∀ c : C,
        (((E.symm c).1 : C) : G) * ((E.symm c).2 : G) = (c : G)) := by
  intro C
  obtain ⟨_, _, _, _, _, _, _, E, hE, hinv, _⟩ :=
    maximal_root_centralizer_direct_product n hn S e y hy
  let E' := ((MulEquiv.refl (CFSG.oddCore C)).prodCongr
    (centralizerRootEquiv y).symm).trans E
  have hvalue (k : CFSG.oddCore C) (z : Subgroup.zpowers y) :
      (E' (k, z) : G) = ((k : C) : G) * (z : G) := by
    change (E (k, (centralizerRootEquiv y).symm z) : G) = _
    rw [hE]
    change ((k : C) : G) * (((centralizerRootEquiv y).symm z : C) : G) = _
    congr 1
    exact (centralizerRootEquiv_apply y ((centralizerRootEquiv y).symm z)).symm.trans
      (congrArg (fun z : Subgroup.zpowers y => (z : G))
        ((centralizerRootEquiv y).apply_symm_apply z))
  refine ⟨E', hvalue, ?_⟩
  intro c
  exact (hvalue (E'.symm c).1 (E'.symm c).2).symm.trans
    (congrArg (fun c : C => (c : G)) (E'.apply_symm_apply c))

theorem maximal_root_centralizer_index {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    let C := Subgroup.centralizer ({y} : Set G)
    (CFSG.oddCore C).index = 2 * 2 ^ n ∧
      Nat.card (C ⧸ CFSG.oddCore C) = 2 * 2 ^ n ∧
      Nat.card C = Nat.card (CFSG.oddCore C) * (2 * 2 ^ n) := by
  intro C
  obtain ⟨_, _, _, _, _, _, _, E, _, _, φ, _⟩ :=
    maximal_root_centralizer_direct_product n hn S e y hy
  have hcard : Nat.card (C ⧸ CFSG.oddCore C) = 2 * 2 ^ n := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_zpowers, Subgroup.orderOf_mk, hy]
  refine ⟨(Subgroup.index_eq_card _).trans hcard, hcard, ?_⟩
  rw [Nat.card_congr E.toEquiv.symm, Nat.card_prod, Nat.card_zpowers,
    Subgroup.orderOf_mk, hy]

theorem original_root_centralizer_product {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let y := actualRoot S e
    let C := Subgroup.centralizer ({y} : Set G)
    y ^ 2 = wreathModelHom S e (Original.a (2 ^ n)) ∧
      y ^ (2 ^ n) = wreathModelHom S e (Original.x (2 ^ n)) ∧
      orderOf y = 2 * 2 ^ n ∧ Odd (Nat.card (CFSG.oddCore C)) ∧
      (∀ c : C, c ∈ CFSG.oddCore C ↔ Odd (orderOf (c : G))) ∧
      (CFSG.oddCore C).index = 2 * 2 ^ n ∧
      ∃ E : CFSG.oddCore C × Subgroup.zpowers y ≃* C,
        (∀ k : CFSG.oddCore C, ∀ z : Subgroup.zpowers y,
          (E (k, z) : G) = ((k : C) : G) * (z : G)) ∧
        (∀ c : C,
          (((E.symm c).1 : C) : G) * ((E.symm c).2 : G) = (c : G)) := by
  intro y C
  have hy := actualRoot_orderOf n hn S e
  obtain ⟨hodd, hmem, _⟩ := maximal_root_centralizer_direct_product n hn S e y hy
  exact ⟨actualRoot_sq S e, actualRoot_pow_modulus n (by omega) S e, hy, hodd, hmem,
    (maximal_root_centralizer_index n hn S e y hy).1,
    maximal_root_centralizer_ambient_product n hn S e y hy⟩

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
