module

public import CFSG.CharacterTheory.Wreathed.OriginalNonstationaryWreathAction
public import CFSG.CharacterTheory.Wreathed.OddNormalQuotientInvolutions
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection

public noncomputable section

namespace CFSG.Wreathed.SimpleOddIndexQuotient

open scoped Classical

universe u v

@[expose] def involutionClosure (G : Type u) [Group G] : Subgroup G :=
  Subgroup.closure {x : G | orderOf x = 2}

instance involutionClosure_characteristic (G : Type u) [Group G] :
    (involutionClosure G).Characteristic := by
  apply Subgroup.characteristic_iff_map_eq.mpr
  intro e
  unfold involutionClosure
  rw [e.toMonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (e.orderOf_eq y).trans hy
  · intro hx
    exact ⟨e.symm x, (e.symm.orderOf_eq x).trans hx, e.apply_symm_apply x⟩

instance involutionClosure_normal (G : Type u) [Group G] :
    (involutionClosure G).Normal := inferInstance

theorem wreath_involution_killing_image_isCyclic
    {H : Type v} [Group H] (m : ℕ) (f : Wreath m →* H)
    (hf : ∀ x : Wreath m, orderOf x = 2 → f x = 1) : IsCyclic f.range := by
  apply Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (f (Original.s m)))
  rw [MonoidHom.range_eq_map, ← wreath_eq_generated_s_swap m, f.map_closure,
    Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  rcases Set.mem_insert_iff.mp hy with hy | hy
  · rw [hy]
    exact Subgroup.mem_zpowers _
  · rw [Set.mem_singleton_iff.mp hy]
    change f (Original.z m) ∈ Subgroup.zpowers (f (Original.s m))
    rw [hf _ (Original.orderOf_z m)]
    exact Subgroup.one_mem _

theorem wreath_involution_quotient_isCyclic (m : ℕ) :
    IsCyclic (Wreath m ⧸ involutionClosure (Wreath m)) := by
  let f := QuotientGroup.mk' (involutionClosure (Wreath m))
  have hc := wreath_involution_killing_image_isCyclic m f (fun x hx =>
    (QuotientGroup.eq_one_iff x).mpr (Subgroup.subset_closure hx))
  rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at hc
  exact (Subgroup.topEquiv (G := Wreath m ⧸ involutionClosure (Wreath m))).isCyclic.mp hc

theorem original_r_mem_involutionClosure (m : ℕ) :
    Original.r m ∈ involutionClosure (Wreath m) := by
  have hz : Original.z m ∈ involutionClosure (Wreath m) :=
    Subgroup.subset_closure (Original.orderOf_z m)
  have hrz : orderOf (Original.r m * Original.z m) = 2 := by
    have he : Original.r m * Original.z m = element m 1 (-1) 1 := by
      simp [Original.r_eq, Original.z, element_base_mul]
    rw [he, element_swap_involution_iff]
    simp
  have h := (involutionClosure (Wreath m)).mul_mem
    (Subgroup.subset_closure hrz) ((involutionClosure (Wreath m)).inv_mem hz)
  simpa only [mul_inv_cancel_right] using h

theorem wreath_involutionClosure_nonabelian (n : ℕ) (hn : 2 ≤ n) :
    ¬ IsMulCommutative (involutionClosure (Wreath (2 ^ n))) := by
  intro hc
  let : IsMulCommutative (involutionClosure (Wreath (2 ^ n))) := hc
  let r : involutionClosure (Wreath (2 ^ n)) :=
    ⟨Original.r (2 ^ n), original_r_mem_involutionClosure _⟩
  let z : involutionClosure (Wreath (2 ^ n)) :=
    ⟨Original.z (2 ^ n), Subgroup.subset_closure (Original.orderOf_z _)⟩
  have hcomm : Original.z (2 ^ n) * Original.r (2 ^ n) =
      Original.r (2 ^ n) * Original.z (2 ^ n) :=
    congrArg Subtype.val ((isMulCommutative_iff.mp hc) z r)
  have hinvert : Original.z (2 ^ n) * Original.r (2 ^ n) *
      (Original.z (2 ^ n))⁻¹ = (Original.r (2 ^ n))⁻¹ := by
    rw [Original.r_eq, Original.z, conjugate_base_by_swap, element_base_inv]
    simp
  rw [hcomm, mul_inv_cancel_right] at hinvert
  have hsquare : Original.r (2 ^ n) ^ 2 = 1 := by
    simpa only [pow_two, ← hinvert] using inv_mul_cancel (Original.r (2 ^ n))
  have hdiv : 2 ^ n ∣ 2 := by
    simpa only [Original.orderOf_r] using orderOf_dvd_of_pow_eq_one hsquare
  have hlarge : 4 ≤ 2 ^ n := by
    calc
      4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hsmall := Nat.le_of_dvd (by decide : 0 < 2) hdiv
  omega

theorem cyclic_Sylow_two_index_two {G : Type u} [Group G] [Finite G]
    (hG : Even (Nat.card G)) (S : Sylow 2 G) (hS : IsCyclic S) :
    ∃ K : Subgroup G, K.index = 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  have hcenter := hS.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr hG.two_dvd)
  let f := MonoidHom.transferSylow S hcenter
  have hrestriction : Function.Bijective (f.domRestrict (S : Subgroup G)) := by
    rw [MonoidHom.transferSylow_domRestrict_eq_pow]
    exact (S.isPGroup'.powEquiv' S.not_dvd_index).bijective
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨s, hs⟩ := hrestriction.surjective x
    exact ⟨s.val, hs⟩
  refine ⟨(powMonoidHom 2 : S →* S).range.comap f, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range]
  exact Nat.gcd_eq_right (S.dvd_card_of_dvd_card hG.two_dvd)

theorem original_central_involution_mem_even_normal
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (D : Subgroup G) [D.Normal] (hD : Even (Nat.card D)) :
    (e.symm (Original.x (2 ^ n)) : G) ∈ D := by
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
  exact OriginalNonstationaryWreathAction.original_involution_mem_normal_sylow_subgroup
    n hn S e T hT

theorem nontrivial_normal_even {G : Type u} [Group G]
    (hcore : CFSG.oddCore G = ⊥) (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    Even (Nat.card N) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  have hle : N ≤ CFSG.oddCore G := le_sSup ⟨inferInstance, hodd⟩
  exact hN (le_bot_iff.mp (hcore ▸ hle))

theorem involutions_mem_nontrivial_normal {G : Type u} [Group G] [Finite G]
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) (x : G) (hx : orderOf x = 2) : x ∈ N := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := N) 2
    (nontrivial_normal_even hcore N hN).two_dvd
  have hyG : orderOf (y : G) = 2 := (Subgroup.orderOf_coe y).trans hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfusion y x hyG hx)
  rw [← hg]
  exact (inferInstance : N.Normal).conj_mem y y.property g

theorem involutionClosure_le_nontrivial_normal {G : Type u} [Group G] [Finite G]
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) : involutionClosure G ≤ N := by
  rw [involutionClosure, Subgroup.closure_le]
  exact fun x hx => involutions_mem_nontrivial_normal hcore hfusion N hN x hx

theorem original_involutionClosure_ne_bot {G : Type u} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    involutionClosure G ≠ ⊥ := by
  let x := wreathModelHom S e (Original.z (2 ^ n))
  have hx : orderOf x = 2 :=
    (orderOf_injective _ (wreathModelHom_injective S e) _).trans (Original.orderOf_z _)
  intro hbot
  have h1 : x = 1 := Subgroup.mem_bot.mp (hbot ▸ Subgroup.subset_closure hx)
  rw [h1, orderOf_one] at hx
  omega

theorem original_involutionClosure_minimal {G : Type u} [Group G] [Finite G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    (involutionClosure G).Normal ∧ involutionClosure G ≠ ⊥ ∧
      ∀ N : Subgroup G, N.Normal → N ≤ involutionClosure G →
        N = ⊥ ∨ N = involutionClosure G := by
  refine ⟨inferInstance, original_involutionClosure_ne_bot n S e, ?_⟩
  intro N hN hle
  have : N.Normal := hN
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  · exact Or.inr (le_antisymm hle (involutionClosure_le_nontrivial_normal hcore hfusion N hbot))

theorem original_wreath_involutionClosure_le {G : Type u} [Group G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (involutionClosure (Wreath (2 ^ n))).map (wreathModelHom S e) ≤
      involutionClosure G := by
  rw [involutionClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  apply Subgroup.subset_closure
  exact (orderOf_injective _ (wreathModelHom_injective S e) y).trans hy

theorem original_involutionClosure_nonabelian {G : Type u} [Group G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ¬ IsMulCommutative (involutionClosure G) := by
  intro hc
  apply wreath_involutionClosure_nonabelian n hn
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  apply wreathModelHom_injective S e
  let f := wreathModelHom S e
  have hx : f (x : Wreath (2 ^ n)) ∈ involutionClosure G :=
    original_wreath_involutionClosure_le n S e (Subgroup.mem_map_of_mem f x.property)
  have hy : f (y : Wreath (2 ^ n)) ∈ involutionClosure G :=
    original_wreath_involutionClosure_le n S e (Subgroup.mem_map_of_mem f y.property)
  exact (map_mul f _ _).trans ((congrArg Subtype.val ((isMulCommutative_iff.mp hc)
    (⟨f x, hx⟩ : involutionClosure G) ⟨f y, hy⟩)).trans (map_mul f _ _).symm)

theorem original_involutionClosure_quotient_Sylow_isCyclic {G : Type u} [Group G]
    [Finite G] (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsCyclic (S.mapSurjective (QuotientGroup.mk'_surjective (involutionClosure G))) := by
  let q := QuotientGroup.mk' (involutionClosure G)
  let f := q.comp (wreathModelHom S e)
  have hc : IsCyclic f.range := wreath_involution_killing_image_isCyclic (2 ^ n) f (by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_closure
      ((orderOf_injective _ (wreathModelHom_injective S e) x).trans hx))
  have hr : f.range = (S : Subgroup G).map q := by
    rw [MonoidHom.range_comp, wreathModelHom_range]
  rwa [hr, ← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective _) S] at hc

theorem original_involutionClosure_odd_index {G : Type u} [Group G] [Finite G]
    (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hindex : ∀ K : Subgroup G, K.index ≠ 2) : Odd (involutionClosure G).index := by
  rw [Subgroup.index_eq_card]
  apply Nat.not_even_iff_odd.mp
  intro heven
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (involutionClosure G))
  obtain ⟨K, hK⟩ := cyclic_Sylow_two_index_two heven Q
    (original_involutionClosure_quotient_Sylow_isCyclic n S e)
  exact hindex (K.comap (QuotientGroup.mk' (involutionClosure G)))
    ((Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)).trans hK)

theorem Sylow_le_normal_of_odd_index {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal] (hindex : Odd N.index) (S : Sylow 2 G) :
    (S : Subgroup G) ≤ N := by
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective N)
  have hQ : (Q : Subgroup (G ⧸ N)) = ⊥ := by
    apply (Subgroup.eq_bot_iff_card _).mpr
    exact Q.isPGroup'.card_eq_or_dvd.resolve_right (fun h => hindex.not_two_dvd_nat
      ((Subgroup.index_eq_card N).symm ▸ h.trans (Subgroup.card_subgroup_dvd_card _)))
  rw [Sylow.coe_mapSurjective, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hQ
  exact hQ

theorem simple_factor_inf_eq_bot {G : Type u} [Group G]
    {N : Subgroup G} {r : ℕ} (F : Fin r → Subgroup G)
    (E : ((i : Fin r) → F i) ≃* N)
    (hE : ∀ (i : Fin r) (x : (j : Fin r) → F j),
      (∀ j, j ≠ i → x j = 1) → (E x : G) = x i)
    {i j : Fin r} (hij : i ≠ j) : F i ⊓ F j = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  let xi : F i := ⟨x, hx.1⟩
  let xj : F j := ⟨x, hx.2⟩
  have hei : (E (Pi.mulSingle i xi) : G) = x := by
    simpa only [Pi.mulSingle_eq_same] using
      hE i (Pi.mulSingle i xi) (fun k hk => by simp only [Pi.mulSingle_eq_of_ne hk])
  have hej : (E (Pi.mulSingle j xj) : G) = x := by
    simpa only [Pi.mulSingle_eq_same] using
      hE j (Pi.mulSingle j xj) (fun k hk => by simp only [Pi.mulSingle_eq_of_ne hk])
  have heq : Pi.mulSingle i xi = Pi.mulSingle j xj :=
    E.injective (Subtype.ext (hei.trans hej.symm))
  have hx1 := congrFun heq i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at hx1
  exact congrArg Subtype.val hx1

theorem simple_factors_even {G : Type u} [Group G]
    {N : Subgroup G} (hN : Even (Nat.card N)) {r : ℕ}
    (F : Fin r → Subgroup G)
    (hconj : ∀ i j, ∃ g : G, F j = CFSG.conjugate (F i) g)
    (E : ((i : Fin r) → F i) ≃* N) : ∀ i, Even (Nat.card (F i)) := by
  have hdvd : 2 ∣ ∏ i : Fin r, Nat.card (F i) := by
    rw [← Nat.card_pi, Nat.card_congr E.toEquiv]
    exact hN.two_dvd
  obtain ⟨j, -, hj⟩ := (Nat.prime_two.prime.dvd_finsetProd_iff _).mp hdvd
  intro i
  obtain ⟨g, hg⟩ := hconj j i
  rw [hg, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  exact even_iff_two_dvd.mpr hj

theorem minimal_normal_with_original_Sylow_isSimple
    {G : Type u} [Group G] [Finite G] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N)
    (hSN : (S : Subgroup G) ≤ N) : IsSimpleGroup N := by
  obtain ⟨r, F, hr, hFN, hsimple, hconj, hnormal, E, hE⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors inferInstance hN hmin
  have heven : Even (Nat.card N) := by
    apply even_iff_two_dvd.mpr
    have hs : 2 ∣ Nat.card S := by
      rw [Nat.card_congr e.toEquiv,
        (wreath_center_involution_and_quaternion_coordinates n hn).card]
      exact dvd_mul_right 2 _
    exact hs.trans (Subgroup.card_dvd_of_le hSN)
  have hFeven := simple_factors_even heven F hconj E
  let T := S.subtype hSN
  let eT : T ≃* Wreath (2 ^ n) := (Subgroup.subgroupOfEquivOfLe hSN).trans e
  let x : N := (eT.symm (Original.x (2 ^ n)) : N)
  have hx : ∀ i, x ∈ (F i).subgroupOf N := by
    intro i
    let : ((F i).subgroupOf N).Normal := hnormal i
    apply original_central_involution_mem_even_normal n hn T eT
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hFN i)).toEquiv]
    exact hFeven i
  have hxne : (x : G) ≠ 1 := by
    intro h
    have horder : orderOf x = 2 := by
      have hcoe : orderOf x = orderOf (eT.symm (Original.x (2 ^ n))) :=
        Subgroup.orderOf_coe (G := N) (eT.symm (Original.x (2 ^ n)))
      exact hcoe.trans ((eT.symm.orderOf_eq _).trans
        (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1)
    have hx1 : x = 1 := Subtype.ext h
    rw [hx1, orderOf_one] at horder
    omega
  have hr1 : r = 1 := by
    by_contra h
    have htwo : 2 ≤ r := by omega
    let i : Fin r := ⟨0, by omega⟩
    let j : Fin r := ⟨1, by omega⟩
    have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i, j] at this
    have hbot := simple_factor_inf_eq_bot F E hE hij
    exact hxne (Subgroup.mem_bot.mp (hbot ▸ ⟨hx i, hx j⟩))
  subst hr1
  let : IsSimpleGroup (F (default : Fin 1)) := hsimple _
  exact ((E.symm).trans (MulEquiv.piUnique (fun i : Fin 1 => F i))).isSimpleGroup

theorem original_involutionClosure_isSimple {G : Type u} [Group G] [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ K : Subgroup G, K.index ≠ 2) :
    IsSimpleGroup (involutionClosure G) ∧ ¬ IsMulCommutative (involutionClosure G) ∧
      Odd (involutionClosure G).index ∧ (S : Subgroup G) ≤ involutionClosure G := by
  have hmin := original_involutionClosure_minimal n S e hcore hfusion
  have hodd := original_involutionClosure_odd_index n S e hindex
  have hle := Sylow_le_normal_of_odd_index (involutionClosure G) hodd S
  exact ⟨minimal_normal_with_original_Sylow_isSimple n hn S e (involutionClosure G)
    hmin.2.1 hmin.2.2 hle, original_involutionClosure_nonabelian n hn S e, hodd, hle⟩

theorem original_involutionClosure_unique_minimal {G : Type u} [Group G] [Finite G]
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (L : Subgroup G) [L.Normal] (hL : L ≠ ⊥)
    (hmin : ∀ N : Subgroup G, N.Normal → N ≤ L → N = ⊥ ∨ N = L)
    (hOmega : involutionClosure G ≠ ⊥) : L = involutionClosure G := by
  rcases hmin (involutionClosure G) inferInstance
    (involutionClosure_le_nontrivial_normal hcore hfusion L hL) with h | h
  · exact (hOmega h).elim
  · exact h.symm

theorem center_eq_bot_of_nonabelian_simple {G : Type u} [Group G] [IsSimpleGroup G]
    (hG : ¬ IsMulCommutative G) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exact (hG (Subgroup.center_eq_top_iff.mp h)).elim

theorem original_involutionClosure_centralizer_eq_bot {G : Type u} [Group G] [Finite G]
    (hcore : CFSG.oddCore G = ⊥)
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hOmega : IsSimpleGroup (involutionClosure G))
    (hnonab : ¬ IsMulCommutative (involutionClosure G)) :
    Subgroup.centralizer (involutionClosure G : Set G) = ⊥ := by
  let : IsSimpleGroup (involutionClosure G) := hOmega
  let C := Subgroup.centralizer (involutionClosure G : Set G)
  have hcenter := center_eq_bot_of_nonabelian_simple hnonab
  by_contra hC
  have hle : involutionClosure G ≤ C :=
    involutionClosure_le_nontrivial_normal hcore hfusion C hC
  have htop : Subgroup.center (involutionClosure G) = ⊤ := by
    apply top_unique
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle x.property)) y y.property)
  exact top_ne_bot (htop.symm.trans hcenter)

theorem conjNormal_ker {G : Type u} [Group G] (L : Subgroup G) [L.Normal] :
    (MulAut.conjNormal : G →* MulAut L).ker = Subgroup.centralizer (L : Set G) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have heq := congrArg (fun a : MulAut L => (a (⟨x, hx⟩ : L) : G)) h
    have hconj : g * x * g⁻¹ = x := by
      simpa only [MulAut.conjNormal_apply, MulAut.one_apply] using heq
    exact ((mul_inv_eq_iff_eq_mul).mp hconj).symm
  · intro h
    ext x
    change g * (x : G) * g⁻¹ = (x : G)
    rw [← h x x.property, mul_inv_cancel_right]

theorem conjNormal_injective_of_centralizer_eq_bot {G : Type u} [Group G]
    (L : Subgroup G) [L.Normal] (hC : Subgroup.centralizer (L : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut L) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [conjNormal_ker, hC]

theorem actual_oddCore_odd (G : Type u) [Group G] [Finite G] :
    Odd (Nat.card (CFSG.oddCore G)) := by
  rw [CFSG.oddCore_eq_piCore]
  apply Nat.not_even_iff_odd.mp
  intro h
  exact CFSG.LocalCores.piCore_isPiSubgroup (G := G) {q : Nat.Primes | q.val ≠ 2}
    ⟨2, Nat.prime_two⟩ h.two_dvd rfl

theorem actual_oddCore_quotient_eq_bot (G : Type u) [Group G] [Finite G] :
    CFSG.oddCore (G ⧸ CFSG.oddCore G) = ⊥ := by
  exact CFSG.Wreathed.weakClosure_oddCore_quotient_eq_bot G

theorem quotient_no_index_two {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (hindex : ∀ K : Subgroup G, K.index ≠ 2) :
    ∀ K : Subgroup (G ⧸ R), K.index ≠ 2 := by
  intro K hK
  exact hindex (K.comap (QuotientGroup.mk' R))
    ((Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective R)).trans hK)

theorem odd_quotient_single_involution_class {G : Type u} [Group G]
    (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R))
    (hfusion : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) :
    ∀ x y : G ⧸ R, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  intro x y hx hy
  obtain ⟨a, ha, hax⟩ := OddNormalQuotientInvolutions.exists_involution_lift R hR x hx
  obtain ⟨b, hb, hby⟩ := OddNormalQuotientInvolutions.exists_involution_lift R hR y hy
  obtain ⟨g, hg⟩ := isConj_iff.mp (hfusion a b ha hb)
  apply isConj_iff.mpr
  refine ⟨QuotientGroup.mk' R g, ?_⟩
  rw [← hax, ← hby, ← map_inv, ← map_mul, ← map_mul, hg]

theorem odd_subgroup_inf_Sylow_eq_bot {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (hR : Odd (Nat.card R)) (S : Sylow 2 G) :
    R ⊓ (S : Subgroup G) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  apply disjoint_iff.mp
  apply Subgroup.disjoint_of_coprime_natCard
  rw [hk]
  exact hR.coprime_two_right.pow_right k

theorem odd_quotient_Sylow_restriction_injective {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R)) (S : Sylow 2 G) :
    Function.Injective ((QuotientGroup.mk' R).comp (S : Subgroup G).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro s hs
  change QuotientGroup.mk' R (s : G) = 1 at hs
  have hRmem : (s : G) ∈ R := (QuotientGroup.eq_one_iff _).mp hs
  exact Subtype.ext (Subgroup.mem_bot.mp
    (odd_subgroup_inf_Sylow_eq_bot R hR S ▸ ⟨hRmem, s.property⟩))

@[expose] def oddQuotientSylowEquiv {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R)) (S : Sylow 2 G) :
    S ≃* (S.mapSurjective (QuotientGroup.mk'_surjective R)) :=
  (MonoidHom.ofInjective (odd_quotient_Sylow_restriction_injective R hR S)).trans
    (MulEquiv.subgroupCongr (by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, Sylow.coe_mapSurjective]))

theorem oddQuotientSylowEquiv_apply {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) [R.Normal] (hR : Odd (Nat.card R)) (S : Sylow 2 G) (s : S) :
    (oddQuotientSylowEquiv R hR S s : G ⧸ R) = QuotientGroup.mk' R (s : G) := by
  dsimp only [oddQuotientSylowEquiv, MulEquiv.trans_apply]
  rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  rfl

theorem one_involution_class_no_index_two_has_simple_odd_index_core_quotient
    {X : Type u} [Group X] [Finite X] (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 X) (e : S ≃* Wreath (2 ^ n))
    (hfusion : ∀ x y : X, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hindex : ∀ K : Subgroup X, K.index ≠ 2) :
    let O := CFSG.oddCore X
    let Xbar := X ⧸ O
    let pi := QuotientGroup.mk' O
    let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective O)
    let L := involutionClosure Xbar
    L.Normal ∧ L ≠ ⊥ ∧
      (∀ N : Subgroup Xbar, N.Normal → N ≤ L → N = ⊥ ∨ N = L) ∧
      (∀ N : Subgroup Xbar, N.Normal → N ≠ ⊥ →
        (∀ M : Subgroup Xbar, M.Normal → M ≤ N → M = ⊥ ∨ M = N) → N = L) ∧
      IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧ Odd L.index ∧
      (Sbar : Subgroup Xbar) ≤ L ∧
      Subgroup.centralizer (L : Set Xbar) = ⊥ ∧ L.Characteristic ∧
      (MulAut.conjNormal : Xbar →* MulAut L).ker =
        Subgroup.centralizer (L : Set Xbar) ∧
      Function.Injective (MulAut.conjNormal : Xbar →* MulAut L) ∧
      ∃ SL : Sylow 2 L,
        (SL : Subgroup L) = (Sbar : Subgroup Xbar).subgroupOf L ∧
        (SL : Subgroup L).map L.subtype = (S : Subgroup X).map pi ∧
        ∃ (f : S ≃* SL) (eL : SL ≃* Wreath (2 ^ n)),
          (∀ s : S, ((f s : L) : Xbar) = pi (s : X)) ∧
          ∀ s : S, eL (f s) = e s := by
  let O := CFSG.oddCore X
  let Xbar := X ⧸ O
  let pi := QuotientGroup.mk' O
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective O)
  let L := involutionClosure Xbar
  have hO : Odd (Nat.card O) := actual_oddCore_odd X
  let E : S ≃* Sbar := oddQuotientSylowEquiv O hO S
  let ebar : Sbar ≃* Wreath (2 ^ n) := E.symm.trans e
  have hcore : CFSG.oddCore Xbar = ⊥ := actual_oddCore_quotient_eq_bot X
  have hf : ∀ x y : Xbar, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    odd_quotient_single_involution_class O hO hfusion
  have hi : ∀ K : Subgroup Xbar, K.index ≠ 2 := quotient_no_index_two O hindex
  have hmin := original_involutionClosure_minimal n Sbar ebar hcore hf
  obtain ⟨hsimple, hnonab, hodd, hSL⟩ :=
    original_involutionClosure_isSimple n hn Sbar ebar hcore hf hi
  have hC := original_involutionClosure_centralizer_eq_bot hcore hf hsimple hnonab
  change L.Normal ∧ L ≠ ⊥ ∧ _
  refine ⟨hmin.1, hmin.2.1, hmin.2.2, ?_, hsimple, hnonab, hodd, hSL, hC,
    inferInstance, conjNormal_ker L, conjNormal_injective_of_centralizer_eq_bot L hC, ?_⟩
  · intro N hN hNne hNmin
    let : N.Normal := hN
    exact original_involutionClosure_unique_minimal hcore hf N hNne hNmin hmin.2.1
  · let SL := Sbar.subtype hSL
    let F : Sbar ≃* SL := (Subgroup.subgroupOfEquivOfLe hSL).symm
    let f : S ≃* SL := E.trans F
    let eL : SL ≃* Wreath (2 ^ n) := f.symm.trans e
    refine ⟨SL, Sylow.coe_subtype Sbar hSL, ?_, f, eL, ?_, ?_⟩
    · rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSL, Sylow.coe_mapSurjective]
    · intro s
      exact oddQuotientSylowEquiv_apply O hO S s
    · intro s
      exact congrArg e (f.symm_apply_apply s)

end CFSG.Wreathed.SimpleOddIndexQuotient
