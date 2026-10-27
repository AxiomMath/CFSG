module

public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicSylowComplement

public noncomputable section

namespace CFSG.Wreathed.SquareRootSmallCharacterRigidity

open CFSG.Wreathed CFSG.Wreathed.WreathCentralSquare
open scoped Classical Pointwise

@[expose] def outsideCentralizerEquiv (m : ℕ) (c d : ZMod m) :
    Subgroup.centralizer ({element m c d 1} : Set (Wreath m)) ≃ ZMod m × ZMod 2 where
  toFun g := let coord := coordinateEquiv m g; (coord.2.1, coord.2.2)
  invFun coord := ⟨element m (if coord.2 = 0 then coord.1 else coord.1 + (c - d)) coord.1 coord.2,
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      rcases swap_exponent_cases coord.2 with h | h
      · rw [h, ite_eq_left rfl]
        exact (base_commutes_swap_iff m coord.1 coord.1 c d).mpr rfl
      · rw [h, ite_eq_right one_ne_zero]
        exact (swap_commutes_swap_iff m _ _ c d).mpr (by abel))⟩
  left_inv g := by
    apply Subtype.ext
    obtain ⟨⟨a, b, e⟩, heq⟩ := (coordinateEquiv m).symm.surjective (g : Wreath m)
    change element m a b e = (g : Wreath m) at heq
    have hcomm : Commute (element m a b e) (element m c d 1) := by
      rw [heq]
      exact Subgroup.mem_centralizer_singleton_iff.mp g.2
    change element m (if (coordinateEquiv m (g : Wreath m)).2.2 = 0 then
      (coordinateEquiv m (g : Wreath m)).2.1 else
      (coordinateEquiv m (g : Wreath m)).2.1 + (c - d))
      (coordinateEquiv m (g : Wreath m)).2.1
      (coordinateEquiv m (g : Wreath m)).2.2 = (g : Wreath m)
    rw [← heq, show coordinateEquiv m (element m a b e) = (a, b, e) from
      (coordinateEquiv m).apply_symm_apply (a, b, e)]
    rcases swap_exponent_cases e with rfl | rfl
    · have hab := (base_commutes_swap_iff m a b c d).mp hcomm
      simpa only [ite_true] using congrArg (fun a => element m a b 0) hab.symm
    · have hab := (swap_commutes_swap_iff m a b c d).mp hcomm
      simp only [ite_eq_right one_ne_zero]
      congr 1
      linear_combination -hab
  right_inv coord := by
    change ((coordinateEquiv m
      (element m (if coord.2 = 0 then coord.1 else coord.1 + (c - d)) coord.1 coord.2)).2.1,
        (coordinateEquiv m
          (element m (if coord.2 = 0 then coord.1 else coord.1 + (c - d)) coord.1 coord.2)).2.2) =
      coord
    rw [show coordinateEquiv m
      (element m (if coord.2 = 0 then coord.1 else coord.1 + (c - d)) coord.1 coord.2) =
        (if coord.2 = 0 then coord.1 else coord.1 + (c - d), coord.1, coord.2) from
      (coordinateEquiv m).apply_symm_apply
        (if coord.2 = 0 then coord.1 else coord.1 + (c - d), coord.1, coord.2)]

theorem outside_centralizer_card (m : ℕ) (c d : ZMod m) :
    Nat.card (Subgroup.centralizer ({element m c d 1} : Set (Wreath m))) = 2 * m := by
  rw [Nat.card_congr (outsideCentralizerEquiv m c d), Nat.card_prod, Nat.card_zmod,
    Nat.card_zmod, Nat.mul_comm]

theorem maximal_order_centralizer_eq_zpowers (k : ℕ) (y : Wreath (2 ^ (k + 1)))
    (hy : orderOf y = 2 * 2 ^ (k + 1)) :
    Subgroup.centralizer ({y} : Set (Wreath (2 ^ (k + 1)))) = Subgroup.zpowers y := by
  obtain ⟨⟨c, d, e⟩, heq⟩ := (coordinateEquiv (2 ^ (k + 1))).symm.surjective y
  change element (2 ^ (k + 1)) c d e = y at heq
  have he : e = 1 := ((element_maximal_order_iff k c d e).mp (heq ▸ hy)).1
  have hle : Subgroup.zpowers y ≤ Subgroup.centralizer ({y} : Set (Wreath (2 ^ (k + 1)))) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  apply (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, hy, ← heq, he, outside_centralizer_card]

theorem original_root_centralizer (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.centralizer ({originalRoot (2 ^ n)} : Set (Wreath (2 ^ n))) =
      Subgroup.zpowers (originalRoot (2 ^ n)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  subst n
  exact maximal_order_centralizer_eq_zpowers k _ (originalRoot_orderOf _ hn)

theorem exists_cyclic_centralizer_sylow {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({y} : Set G)),
      (P : Subgroup (Subgroup.centralizer ({y} : Set G))) =
        Subgroup.zpowers (⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
          Subgroup.centralizer ({y} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hyC : orderOf yC = 2 ^ (n + 1) := by
    rw [Subgroup.orderOf_mk, hy, pow_succ, Nat.mul_comm]
  have hZp : IsPGroup 2 (Subgroup.zpowers yC) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hyC])
  obtain ⟨P, hZP⟩ := hZp.exists_le_sylow
  let Q : Subgroup G := (P : Subgroup C).map C.subtype
  have hQ : IsPGroup 2 Q := P.isPGroup'.map C.subtype
  obtain ⟨S', hQS⟩ := hQ.exists_le_sylow
  have hyP : yC ∈ (P : Subgroup C) := hZP (Subgroup.mem_zpowers yC)
  have hyS : y ∈ (S' : Subgroup G) := hQS ⟨yC, hyP, rfl⟩
  let yS : S' := ⟨y, hyS⟩
  let e' : S' ≃* Wreath (2 ^ n) := (Sylow.equiv S S').symm.trans e
  have hye : orderOf (e' yS) = 2 * 2 ^ n := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy]
  have hcentral : Subgroup.centralizer ({e' yS} : Set (Wreath (2 ^ n))) =
      Subgroup.zpowers (e' yS) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    subst n
    exact maximal_order_centralizer_eq_zpowers k _ hye
  refine ⟨P, le_antisymm ?_ hZP⟩
  intro p hp
  have hpS : (p : G) ∈ (S' : Subgroup G) := hQS ⟨p, hp, rfl⟩
  let pS : S' := ⟨p, hpS⟩
  have hcomm : Commute pS yS := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp p.2
  have hemem : e' pS ∈ Subgroup.zpowers (e' yS) := by
    rw [← hcentral]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm.map e').eq
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hemem
  have hpseq : yS ^ k = pS := e'.injective (by rw [map_zpow]; exact hk)
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k, Subtype.ext ?_⟩
  exact congrArg (fun s : S' => (s : G)) hpseq

theorem maximal_root_centralizer_odd_complement {G : Type} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : G) (hy : orderOf y = 2 * 2 ^ n) :
    let C := Subgroup.centralizer ({y} : Set G)
    let yC : C := ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    ∃ (N : Subgroup C) (_ : N.Normal), Odd (Nat.card N) ∧
      (∀ c : C, c ∈ N ↔ Odd (orderOf c)) ∧ N.Characteristic ∧
      N ⊓ Subgroup.zpowers yC = ⊥ ∧ N ⊔ Subgroup.zpowers yC = ⊤ ∧
      IsPGroup 2 (C ⧸ N) ∧ IsCyclic (C ⧸ N) ∧
      ∃ φ : Subgroup.zpowers yC ≃* C ⧸ N,
        ∀ z : Subgroup.zpowers yC, φ z = QuotientGroup.mk' N z := by
  intro C yC
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_cyclic_centralizer_sylow n hn S e y hy
  have hcyc : IsCyclic (P : Subgroup C) := hP ▸ inferInstance
  obtain ⟨N, hnormal, ⟨hN, k, hk⟩, _, hchar, hmem, hproduct, hinter, hbij⟩ :=
    CFSG.Semidihedral.Principal.cyclicSylowTwo_normal_odd_complement P hcyc
  let φP := MulEquiv.ofBijective ((QuotientGroup.mk' N).comp (P : Subgroup C).subtype) hbij
  have hquot : IsPGroup 2 (C ⧸ N) :=
    P.isPGroup'.of_surjective ((QuotientGroup.mk' N).comp (P : Subgroup C).subtype) hbij.2
  have hqcyc : IsCyclic (C ⧸ N) := (MulEquiv.isCyclic φP).mp hcyc
  have hsup : N ⊔ (P : Subgroup C) = ⊤ := by
    apply top_unique
    intro c _
    have hc : c ∈ (N : Set C) * (P : Set C) := by rw [hproduct]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := hc
    rw [← hab]
    exact (N ⊔ (P : Subgroup C)).mul_mem (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hb)
  refine ⟨N, hnormal, hN, hmem, hchar, ?_, ?_, hquot, hqcyc, ?_⟩
  · rwa [hP] at hinter
  · rwa [hP] at hsup
  · let φ := (MulEquiv.subgroupCongr hP).symm.trans φP
    refine ⟨φ, fun z => ?_⟩
    rfl

end CFSG.Wreathed.SquareRootSmallCharacterRigidity
