module

public import CFSG.LocalAnalysis.ComponentInitial.CyclicIndexTwoRank
public import CFSG.LocalAnalysis.ComponentInitial.RankThreeSquare
public import CFSG.LocalAnalysis.RankTwoShapes.FourShapes.SelfCentralizingFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

theorem exists_cyclic_index_le_two_of_mulEquiv {P Q : Type*} [Group P] [Group Q]
    (e : P ≃* Q) {H₀ : Subgroup Q} (hH₀ : IsCyclic H₀) (hind : H₀.index ≤ 2) :
    ∃ H : Subgroup P, IsCyclic H ∧ H.index ≤ 2 := by
  refine ⟨H₀.comap e.toMonoidHom, ?_, ?_⟩
  · let φ : H₀.comap e.toMonoidHom →* H₀ :=
      { toFun := fun x => ⟨e (x : P), x.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (by
          change e ((x : P) * y) = e x * e y
          exact map_mul e _ _) }
    exact isCyclic_of_injective φ fun x y hxy =>
      Subtype.ext (e.injective (congrArg Subtype.val hxy))
  · rw [index_comap_of_surjective _ e.surjective]
    exact hind

theorem isolated_involution_central_split_obstruction {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hrank : 3 ≤ CFSG.pRank 2 P) {z t : P} (hz : z ∈ center P)
    (hz2 : orderOf z = 2) (ht2 : orderOf t = 2)
    (hnot : ¬ ∃ E : Subgroup P, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 8 ∧ t ∈ E) :
    ¬ ∃ R : Subgroup P, R ≤ centralizer ({t} : Set P) ∧
      R.relIndex (centralizer ({t} : Set P)) = 2 ∧ t ∈ R ∧ z ∉ R := by
  classical
  rintro ⟨R, hRD, hRind, htR, hzR⟩
  set D := centralizer ({t} : Set P) with hD
  have hzz : z * z = 1 := by rw [← sq, ← hz2, pow_orderOf_eq_one]
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hzt : Commute z t := (mem_center_iff.1 hz t).symm
  have hzD : z ∈ D := mem_centralizer_singleton_iff.2 hzt.eq
  have htD : t ∈ D := mem_centralizer_singleton_iff.2 rfl
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; norm_num at hz2
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht2; norm_num at ht2
  have hzne : z ≠ t := fun h => hzR (h ▸ htR)
  have height : ∀ u ∈ R, orderOf u = 2 → u = t := by
    intro u huR hu2
    by_contra hut
    apply hnot
    let zD : D := ⟨z, hzD⟩
    let tD : D := ⟨t, htD⟩
    let uD : D := ⟨u, hRD huR⟩
    have hzzD : zD * zD = 1 := Subtype.ext hzz
    have httD : tD * tD = 1 := Subtype.ext htt
    have hztD : Commute zD tD := Subtype.ext hzt.eq
    let V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions zD tD hzzD httD hztD
    have hVK : IsKleinFour V := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
      zD tD hzzD httD (fun h => hz1 (congrArg Subtype.val h))
      (fun h => ht1 (congrArg Subtype.val h)) (fun h => hzne (congrArg Subtype.val h)) hztD
    have hmemV : ∀ x : D, x ∈ V ↔ x = zD * tD ∨ x = zD ∨ x = tD ∨ x = 1 := fun x => by
      change x ∈ ({zD * tD, zD, tD, 1} : Set D) ↔ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    have hcentral : V ≤ center D := by
      intro x hx
      have hzc : zD ∈ center D := mem_center_iff.2 fun g => Subtype.ext
        (mem_center_iff.1 hz g)
      have htc : tD ∈ center D := mem_center_iff.2 fun g => Subtype.ext
        (mem_centralizer_singleton_iff.1 g.2)
      rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
      · exact mul_mem hzc htc
      · exact hzc
      · exact htc
      · exact one_mem _
    have hVel : CFSG.Open.IsElemAbelian 2 V := by
      refine ⟨IsKleinFour.isMulCommutative, fun x hx => ?_⟩
      have := IsKleinFour.mul_self (G := V) ⟨x, hx⟩
      rw [sq]
      exact congrArg Subtype.val this
    have huV : uD ∉ V := by
      intro h
      rcases (hmemV uD).1 h with h | h | h | h
      · have hu : u = z * t := congrArg Subtype.val h
        apply hzR
        have : z = u * t := by rw [hu, mul_assoc, htt, mul_one]
        rw [this]
        exact mul_mem huR htR
      · have hu : u = z := congrArg Subtype.val h
        exact hzR (hu ▸ huR)
      · exact hut (congrArg Subtype.val h)
      · have hu : u = 1 := congrArg Subtype.val h
        rw [hu, orderOf_one] at hu2
        norm_num at hu2
    have huD2 : orderOf uD = 2 := (Subgroup.orderOf_coe uD).symm.trans hu2
    have htD2 : orderOf tD = 2 := (Subgroup.orderOf_coe tD).symm.trans ht2
    obtain ⟨E, hE, hEcard, htE⟩ := CFSG.ProperTwoGeneratedCore.central_four_involution_coverage
      V hcentral hVel hVK.card_four uD huD2 huV tD htD2
    refine ⟨E.map D.subtype, (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 _).2
      (CFSG.SectionRank.isElemAbelian_map hE D.subtype), ?_, ⟨tD, htE, rfl⟩⟩
    rw [Subgroup.card_map_of_injective D.subtype_injective, hEcard]
  have hR : ∀ x ∈ R, x = 1 ∨ x = t := by
    intro x hxR
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP) x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hx1 hk
    have hw2 : orderOf (x ^ 2 ^ (k - 1)) = 2 := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 1)),
        hk]
      rw [show k = (k - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel]
      exact Nat.mul_div_cancel_left 2 (pow_pos two_pos _)
    have hw := height _ (pow_mem hxR _) hw2
    by_cases hk1 : k = 1
    · subst hk1
      simpa using hw
    ·
      exfalso
      apply hnot
      refine rank_three_square_involution_coverage_pRank hrank ht2 ⟨x ^ 2 ^ (k - 2), ?_⟩
      rw [← pow_mul, ← pow_succ, show k - 2 + 1 = k - 1 by omega, hw]
  have hRcard : Nat.card R ≤ 2 := by
    have hsub : (R : Set P) ⊆ {1, t} := fun x hx => by
      rcases hR x hx with h | h <;> simp [h]
    calc Nat.card R = (R : Set P).ncard := (Nat.card_coe_set_eq _)
      _ ≤ ({1, t} : Set P).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({t} : Set P).ncard + 1 := Set.ncard_insert_le 1 {t}
      _ = 2 := by rw [Set.ncard_singleton]
  have hDcard : Nat.card D ≤ 4 := by
    have h := Subgroup.card_mul_index (R.subgroupOf D)
    have hRD' : Nat.card (R.subgroupOf D) = Nat.card R := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv]
    change Nat.card (R.subgroupOf D) * R.relIndex D = Nat.card D at h
    rw [hRind, hRD'] at h
    omega
  let V := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions z t hzz htt hzt
  have hVK : IsKleinFour V := CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    z t hzz htt hz1 ht1 hzne hzt
  have hmemV : ∀ x : P, x ∈ V ↔ x = z * t ∨ x = z ∨ x = t ∨ x = 1 := fun x => by
    change x ∈ ({z * t, z, t, 1} : Set P) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hVD : V ≤ D := by
    intro x hx
    rcases (hmemV x).1 hx with rfl | rfl | rfl | rfl
    · exact mul_mem hzD htD
    · exact hzD
    · exact htD
    · exact one_mem _
  have hDV : D = V := by
    refine (Subgroup.eq_of_le_of_card_ge hVD ?_).symm
    rw [hVK.card_four]
    exact hDcard
  have hcent : centralizer (V : Set P) = V := by
    refine le_antisymm ?_ ?_
    · have htV : t ∈ (V : Set P) := (hmemV t).2 (Or.inr (Or.inr (Or.inl rfl)))
      exact (centralizer_le (Set.singleton_subset_iff.2 htV)).trans hDV.le
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have := (IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩
      exact congrArg Subtype.val this
  have hVcomm : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hVexp : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    rw [sq]
    exact congrArg Subtype.val (IsKleinFour.mul_self (G := V) ⟨v, hv⟩)
  obtain ⟨H, hHcyc, hHind⟩ : ∃ H : Subgroup P, IsCyclic H ∧ H.index ≤ 2 := by
    rcases CFSG.RankTwoShapes.selfCentralizing_four_shapes hP V hVcomm hVexp hVK.card_four hcent
      with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · refine exists_cyclic_index_le_two_of_mulEquiv e (H₀ := zpowers (DihedralGroup.r 1))
        inferInstance (le_of_eq ?_)
      have hm : 2 ^ (n - 1) ≠ 0 := pow_ne_zero _ two_ne_zero
      have h1 := Subgroup.card_mul_index (zpowers (DihedralGroup.r 1 : DihedralGroup (2 ^ (n - 1))))
      rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one, DihedralGroup.nat_card] at h1
      have hpos : 0 < 2 ^ (n - 1) := Nat.pos_of_ne_zero hm
      nlinarith
    · obtain ⟨-, -, -, -, hcyc, -, hidx⟩ := CFSG.Semidihedral.normal_form n hn
      exact exists_cyclic_index_le_two_of_mulEquiv e hcyc hidx.le
  have := cyclic_index_two_rank_bound hHcyc hHind
  omega

end CFSG.LocalAnalysis.ComponentInitial
