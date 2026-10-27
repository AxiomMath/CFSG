module

public import CFSG.GroupTheory.QuasiDihedralFusion.Quotient
public import CFSG.CharacterTheory.Wreathed.SimpleOddIndexQuotient

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.GorensteinWalter
open CFSG.Wreathed.SimpleOddIndexQuotient

universe u v

section Sylow

variable {G : Type u} [Group G] [Finite G]

theorem nonempty_sylow_equiv_of_le (S : Sylow 2 G) {L : Subgroup G}
    (hSL : (S : Subgroup G) ≤ L) (P : Sylow 2 L) :
    Nonempty ((P : Subgroup L) ≃* (S : Subgroup G)) :=
  ⟨(P.equiv (S.subtype hSL)).trans ((MulEquiv.subgroupCongr (Sylow.coe_subtype S hSL)).trans
    (Subgroup.subgroupOfEquivOfLe hSL))⟩

theorem HasSemidihedralSylow.of_le {n : ℕ} (hG : HasSemidihedralSylow G n) (S : Sylow 2 G)
    {L : Subgroup G} (hSL : (S : Subgroup G) ≤ L) : HasSemidihedralSylow L n := by
  refine ⟨hG.1, fun P => ?_⟩
  obtain ⟨f⟩ := hG.2 S
  obtain ⟨eP⟩ := nonempty_sylow_equiv_of_le S hSL P
  exact ⟨f.trans eP.symm⟩

theorem HasWreathedSylow.of_le {n : ℕ} (hG : HasWreathedSylow G n) (S : Sylow 2 G)
    {L : Subgroup G} (hSL : (S : Subgroup G) ≤ L) : HasWreathedSylow L n := by
  refine ⟨hG.1, fun P => ?_⟩
  obtain ⟨e⟩ := hG.2 S
  obtain ⟨eP⟩ := nonempty_sylow_equiv_of_le S hSL P
  exact ⟨eP.trans e⟩

theorem HasQDOrWreathedSylowOfHeight.of_le {h : ℕ} (hG : HasQDOrWreathedSylowOfHeight G h)
    (S : Sylow 2 G) {L : Subgroup G} (hSL : (S : Subgroup G) ≤ L) :
    HasQDOrWreathedSylowOfHeight L h := by
  rcases hG with ⟨h1, n, hn⟩ | hw
  · exact Or.inl ⟨h1, n, hn.of_le S hSL⟩
  · exact Or.inr (hw.of_le S hSL)

theorem HasQDOrWreathedSylow.of_le (hG : HasQDOrWreathedSylow G) (S : Sylow 2 G)
    {L : Subgroup G} (hSL : (S : Subgroup G) ≤ L) : HasQDOrWreathedSylow L := by
  obtain ⟨h, hh⟩ := hG
  exact ⟨h, hh.of_le S hSL⟩

omit [Finite G] in
theorem four_dvd_card_sylow (hG : HasQDOrWreathedSylow G) (S : Sylow 2 G) :
    4 ∣ Nat.card (S : Subgroup G) := by
  obtain ⟨h, hh⟩ := hG
  rcases hh with ⟨-, n, hn⟩ | hw
  · obtain ⟨f⟩ := hn.2 S
    rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by have := hn.1; omega)]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ n := pow_dvd_pow 2 (by have := hn.1; omega)
  · obtain ⟨e⟩ := hw.2 S
    rw [Nat.card_congr e.toEquiv, card_wreath]
    have h2 : 2 ∣ 2 ^ h := dvd_pow_self 2 (by have := hw.1; omega)
    exact Dvd.dvd.mul_left (by simpa [pow_two] using mul_dvd_mul h2 h2) 2

end Sylow

theorem noIndexTwo_of_isSimpleGroup {X : Type v} [Group X] [IsSimpleGroup X]
    (hX : Nat.card X ≠ 2) : ∀ M : Subgroup X, M.index ≠ 2 := by
  intro M hM
  have : M.Normal := Subgroup.normal_of_index_eq_two hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
  · rw [Subgroup.index_bot] at hM
    exact hX hM
  · rw [Subgroup.index_top] at hM
    omega

section Semidihedral

variable {G : Type u} [Group G] [Finite G] {n : ℕ}

theorem semidihedral_central_involution_mem_even_normal (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (D : Subgroup G) [D.Normal] (hD : Even (Nat.card D)) :
    (f (z n) : G) ∈ D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T := D.subgroupOf (S : Subgroup G)
  have : T.Normal := inferInstance
  have hT : T ≠ ⊥ := by
    intro hbot
    obtain ⟨P, hP⟩ :=
      CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 D S
    have hmap : D ⊓ (S : Subgroup G) = ⊥ := by
      have h := congrArg (Subgroup.map (S : Subgroup G).subtype) hbot
      simpa only [T, Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] using h
    have hPbot : (P : Subgroup D) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).mp
      rw [hP, Subgroup.subgroupOf_map_subtype, inf_comm, hmap]
    exact P.ne_bot_of_dvd_card hD.two_dvd hPbot
  have hcard : Nat.card (Subgroup.center (S : Subgroup G)) = 2 := by
    rw [← Subgroup.map_center_eq f, Subgroup.card_map_of_injective f.injective,
      CFSG.Semidihedral.center_card n hn]
  have : IsCyclic (Subgroup.center (S : Subgroup G)) := isCyclic_of_prime_card hcard
  have hzc : f (z n) ∈ Subgroup.center (S : Subgroup G) := by
    rw [← Subgroup.map_center_eq f]
    exact ⟨z n, CFSG.Semidihedral.z_mem_center n hn, rfl⟩
  have hzo : orderOf (f (z n)) = 2 := (f.orderOf_eq _).trans (orderOf_z n (by omega))
  exact CFSG.Wreathed.OriginalNonstationaryWreathAction.central_involution_mem_normal_two_subgroup
    S.isPGroup' (f (z n)) hzc hzo T hT

omit [Finite G] in
theorem semidihedral_involutionClosure_ne_bot (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) : involutionClosure G ≠ ⊥ := by
  have hx : orderOf (f (z n) : G) = 2 := by
    rw [Subgroup.orderOf_coe, f.orderOf_eq, orderOf_z n (by omega)]
  intro hbot
  have h1 : (f (z n) : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure hx)
  rw [h1, orderOf_one] at hx
  omega

theorem semidihedral_involutionClosure_quotient_Sylow_isCyclic (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    IsCyclic (S.mapSurjective (QuotientGroup.mk'_surjective (involutionClosure G))) := by
  let q := QuotientGroup.mk' (involutionClosure G)
  let F := q.comp (FocalFusion.ambientHom n (S : Subgroup G) f)
  have hs : F (s n) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    apply Subgroup.subset_closure
    change orderOf (FocalFusion.ambientHom n (S : Subgroup G) f (s n)) = 2
    rw [orderOf_ambientHom, orderOf_s n (by omega)]
  have hc : IsCyclic F.range := by
    apply Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (F (r n)))
    rw [MonoidHom.range_eq_map, ← CentralQuotients.original_generators_closure n (by omega),
      F.map_closure, Subgroup.closure_le]
    rintro x ⟨y, hy, rfl⟩
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · rw [hy]
      exact Subgroup.mem_zpowers _
    · rw [Set.mem_singleton_iff.mp hy, hs]
      exact Subgroup.one_mem _
  have hr : F.range = (S : Subgroup G).map q := by
    rw [MonoidHom.range_comp, FocalFusion.ambientHom_range]
  rwa [hr, ← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) S] at hc

theorem semidihedral_involutionClosure_odd_index (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (hindex : ∀ K : Subgroup G, K.index ≠ 2) :
    Odd (involutionClosure G).index := by
  rw [Subgroup.index_eq_card]
  apply Nat.not_even_iff_odd.mp
  intro heven
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (involutionClosure G))
  obtain ⟨K, hK⟩ := cyclic_Sylow_two_index_two heven Q
    (semidihedral_involutionClosure_quotient_Sylow_isCyclic hn S f)
  exact hindex (K.comap (QuotientGroup.mk' (involutionClosure G)))
    ((Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)).trans hK)

theorem minimal_normal_with_semidihedral_Sylow_isSimple (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hSN : (S : Subgroup G) ≤ N) : IsSimpleGroup N := by
  obtain ⟨r, F, hr, hFN, hsimple, hconj, hnormal, E, hE⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors inferInstance hN hmin
  have heven : Even (Nat.card N) := by
    apply even_iff_two_dvd.mpr
    have hs : 2 ∣ Nat.card S := by
      rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by omega)]
      exact dvd_pow_self 2 (by omega)
    exact hs.trans (Subgroup.card_dvd_of_le hSN)
  have hFeven := simple_factors_even heven F hconj E
  let T := S.subtype hSN
  let fT : SemidihedralGroup n ≃* T := f.trans (Subgroup.subgroupOfEquivOfLe hSN).symm
  let x : N := (fT (z n) : N)
  have hx : ∀ i, x ∈ (F i).subgroupOf N := by
    intro i
    let : ((F i).subgroupOf N).Normal := hnormal i
    apply semidihedral_central_involution_mem_even_normal hn T fT
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hFN i)).toEquiv]
    exact hFeven i
  have hxne : (x : G) ≠ 1 := by
    intro h
    have horder : orderOf x = 2 := by
      have hcoe : orderOf x = orderOf (fT (z n)) := Subgroup.orderOf_coe (G := N) (fT (z n))
      exact hcoe.trans ((fT.orderOf_eq _).trans (orderOf_z n (by omega)))
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at horder
    omega
  have hr1 : r = 1 := by
    by_contra h
    let i : Fin r := ⟨0, by omega⟩
    let j : Fin r := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp [i, j] at this
    have hbot := simple_factor_inf_eq_bot F E hE hij
    exact hxne (Subgroup.mem_bot.mp (hbot ▸ ⟨hx i, hx j⟩))
  subst hr1
  let : IsSimpleGroup (F (default : Fin 1)) := hsimple _
  exact ((E.symm).trans (MulEquiv.piUnique (fun i : Fin 1 => F i))).isSimpleGroup

theorem semidihedral_involutionClosure_isSimple (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ K : Subgroup G, K.index ≠ 2) :
    IsSimpleGroup (involutionClosure G) ∧ Odd (involutionClosure G).index ∧
      (S : Subgroup G) ≤ involutionClosure G := by
  have hne := semidihedral_involutionClosure_ne_bot hn S f
  have hmin : ∀ N : Subgroup G, N.Normal → N ≤ involutionClosure G →
      N = ⊥ ∨ N = involutionClosure G := by
    intro N hN hle
    have : N.Normal := hN
    by_cases hbot : N = ⊥
    · exact Or.inl hbot
    · exact Or.inr (le_antisymm hle (involutionClosure_le_nontrivial_normal hcore hfusion N hbot))
  have hodd := semidihedral_involutionClosure_odd_index hn S f hindex
  have hle := Sylow_le_normal_of_odd_index (involutionClosure G) hodd S
  exact ⟨minimal_normal_with_semidihedral_Sylow_isSimple hn S f (involutionClosure G) hne hmin
    hle, hodd, hle⟩

end Semidihedral

section QDGroup

variable {G : Type u} [Group G] [Finite G]

theorem IsQDGroup.involutionClosure_isSimple (hG : IsQDGroup G) (hcore : CFSG.oddCore G = ⊥) :
    IsSimpleGroup (involutionClosure G) ∧ Odd (involutionClosure G).index ∧
      ∀ S : Sylow 2 G, (S : Subgroup G) ≤ involutionClosure G := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  have key : IsSimpleGroup (involutionClosure G) ∧ Odd (involutionClosure G).index := by
    obtain ⟨h, hh⟩ := hG.sylow
    rcases hh with ⟨-, n, hn⟩ | hw
    · obtain ⟨f⟩ := hn.2 S
      obtain ⟨h1, h2, -⟩ := semidihedral_involutionClosure_isSimple hn.1 S f hcore
        hG.involutions_isConj hG.noIndexTwo
      exact ⟨h1, h2⟩
    · obtain ⟨e⟩ := hw.2 S
      obtain ⟨h1, -, h3, -⟩ := original_involutionClosure_isSimple h hw.1 S e hcore
        hG.involutions_isConj hG.noIndexTwo
      exact ⟨h1, h3⟩
  exact ⟨key.1, key.2, fun P => Sylow_le_normal_of_odd_index _ key.2 P⟩

theorem IsQDGroup.involutionClosure_isQDGroup (hG : IsQDGroup G) (hcore : CFSG.oddCore G = ⊥) :
    IsQDGroup (involutionClosure G) := by
  obtain ⟨hsimple, -, hle⟩ := hG.involutionClosure_isSimple hcore
  obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
  rw [isQDGroup_iff]
  refine ⟨hG.sylow.of_le S (hle S), noIndexTwo_of_isSimpleGroup ?_⟩
  intro h2
  have h4 := (four_dvd_card_sylow hG.sylow S).trans (Subgroup.card_dvd_of_le (hle S))
  rw [h2] at h4
  omega

end QDGroup

section Quotient

variable {H : Type u} [Group H] [Finite H]

theorem IsQDGroup.involutionClosure_quotient_oddCore (hH : IsQDGroup H) :
    IsSimpleGroup (involutionClosure (H ⧸ CFSG.oddCore H)) ∧
      Odd (involutionClosure (H ⧸ CFSG.oddCore H)).index ∧
      IsQDGroup (involutionClosure (H ⧸ CFSG.oddCore H)) ∧
      (∀ S : Sylow 2 (H ⧸ CFSG.oddCore H),
        (S : Subgroup (H ⧸ CFSG.oddCore H)) ≤ involutionClosure (H ⧸ CFSG.oddCore H)) ∧
      ∀ N : Subgroup (H ⧸ CFSG.oddCore H), N.Normal → N ≠ ⊥ →
        involutionClosure (H ⧸ CFSG.oddCore H) ≤ N := by
  have hG : IsQDGroup (H ⧸ CFSG.oddCore H) := isQDGroup_quotient_oddCore_iff.mpr hH
  have hcore := actual_oddCore_quotient_eq_bot H
  obtain ⟨hsimple, hodd, hle⟩ := hG.involutionClosure_isSimple hcore
  refine ⟨hsimple, hodd, hG.involutionClosure_isQDGroup hcore, hle, fun N hN hne => ?_⟩
  have : N.Normal := hN
  exact involutionClosure_le_nontrivial_normal hcore hG.involutions_isConj N hne

theorem IsQDGroup.exists_simple_normal_odd_index (hH : IsQDGroup H) :
    ∃ L : Subgroup (H ⧸ CFSG.oddCore H), L.Normal ∧ IsSimpleGroup L ∧ Odd L.index ∧
      IsQDGroup L := by
  obtain ⟨hsimple, hodd, hQD, -⟩ := hH.involutionClosure_quotient_oddCore
  exact ⟨involutionClosure _, inferInstance, hsimple, hodd, hQD⟩

end Quotient

end CFSG.QuasiDihedralFusion
