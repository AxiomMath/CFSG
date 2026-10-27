module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.CharacterTheory.TwoRankLowerBound.CommutingInvolutions
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeQuotientRank

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.TwoRankLowerBound.Helpers
open CFSG.GorensteinWalter
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem le_of_kleinFour_centralizers_le {A O X : Subgroup G} [hA : IsKleinFour A]
    (hAO : A ≤ Subgroup.normalizer (O : Set G)) (hO : Odd (Nat.card O))
    (hcentralizers : ∀ a ∈ A, a ≠ 1 → O ⊓ Subgroup.centralizer ({a} : Set G) ≤ X) :
    O ≤ X := by
  have : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨mul_comm_of_exponent_two hA.exponent_two⟩⟩
      exponent_dvd_p := by rw [hA.exponent_two] }
  let : MulDistribMulAction A O :=
    MulDistribMulAction.compHom O (O.normalizerMonoidHom.comp (Subgroup.inclusion hAO))
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := A) (H := O)
    (by rw [hA.card_four]; norm_num)
    (fun h => (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr h))
  intro x hx
  have hle : ⨆ (a : A) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) O ≤
      X.comap O.subtype := by
    refine iSup₂_le fun a ha => ?_
    intro y hy
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hy
    have hconj : (a : G) * y * (a : G)⁻¹ = y :=
      (O.normalizerMonoidHom_apply_apply_coe _ y).symm.trans (congrArg Subtype.val hy)
    refine hcentralizers a a.property (fun h => ha (Subtype.ext h))
      ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (y : G) * a = (a : G) * y * (a : G)⁻¹ * a := by rw [hconj]
      _ = a * y := by group
  exact hle (hgen.symm ▸ Subgroup.mem_top (⟨x, hx⟩ : O))

theorem odd_relIndex_of_mul_odd_normal {J M O : Subgroup G} (hJM : J ≤ M) (hOM : O ≤ M)
    (hOnormal : (O.subgroupOf M).Normal) (hOodd : Odd (Nat.card O))
    (hMJO : (J : Set G) * (O : Set G) = (M : Set G)) : Odd (J.relIndex M) := by
  let J' := J.subgroupOf M
  let O' := O.subgroupOf M
  have hsup : J' ⊔ O' = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : (m : G) ∈ (J : Set G) * (O : Set G) := hMJO ▸ m.property
    obtain ⟨j, hj, o, ho, hjo⟩ := Set.mem_mul.mp hm
    have hmjo : m = ⟨j, hJM hj⟩ * ⟨o, hOM ho⟩ := Subtype.ext hjo.symm
    rw [hmjo]
    exact Subgroup.mul_mem_sup hj ho
  have h1 : O'.relIndex J' = O'.index := by
    have h := Subgroup.relIndex_sup_right J' O'
    rw [hsup, Subgroup.relIndex_top_right] at h
    exact h.symm
  have h2 := Subgroup.relIndex_inf_mul_relIndex J' O' ⊤
  have h3 := Subgroup.relIndex_inf_mul_relIndex O' J' ⊤
  simp only [inf_top_eq, Subgroup.relIndex_top_right] at h2 h3
  rw [inf_comm, h1] at h3
  have heq : J'.relIndex O' = J'.index := by
    have h := h2.trans h3.symm
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h
  have hO'card : Nat.card O' = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOM).toEquiv
  change Odd J'.index
  rw [← heq]
  exact Odd.of_dvd_nat hOodd (hO'card ▸ Subgroup.relIndex_dvd_card J' O')

theorem exists_sylow_map_eq_of_odd_relIndex {J M : Subgroup G} (hJM : J ≤ M)
    (hodd : Odd (J.relIndex M)) (T : Sylow 2 J) :
    ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = (T : Subgroup J).map J.subtype := by
  let TG := (T : Subgroup J).map J.subtype
  have hTGJ : TG ≤ J := Subgroup.map_subtype_le _
  have hTGM : TG ≤ M := hTGJ.trans hJM
  have htwo : IsPGroup 2 (TG.subgroupOf M) := (T.isPGroup'.map J.subtype).comap_subtype
  have hTindex : TG.relIndex J = (T : Subgroup J).index := by
    change (TG.comap J.subtype).index = _
    rw [Subgroup.comap_map_eq_self_of_injective J.subtype_injective]
  have hindex : ¬ 2 ∣ (TG.subgroupOf M).index := by
    change ¬ 2 ∣ TG.relIndex M
    rw [← Subgroup.relIndex_mul_relIndex TG J M hTGJ hJM, hTindex]
    intro hdvd
    rcases (Nat.prime_two.dvd_mul).mp hdvd with h | h
    · exact T.not_dvd_index h
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  refine ⟨htwo.toSylow hindex, ?_⟩
  change (TG.subgroupOf M).map M.subtype = TG
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTGM]

theorem odd_factor_rank_one_intersections_force_three_involutions
    {H M O : Subgroup G} (hMH : ¬ M ≤ H) {u z : G} (huH : u ∈ H) (huM : u ∈ M)
    (huCentral : u ∈ Subgroup.centralizer (M : Set G)) (hzJ : z ∈ H ⊓ M)
    (hzCentral : z ∈ Subgroup.centralizer ((H ⊓ M : Subgroup G) : Set G))
    (hu : orderOf u = 2) (hz : orderOf z = 2) (huz : u ≠ z)
    (hOM : O ≤ M) (hOnormal : (O.subgroupOf M).Normal) (hOodd : Odd (Nat.card O))
    (hMJO : ((H ⊓ M : Subgroup G) : Set G) * (O : Set G) = (M : Set G))
    (hrank : ∀ g ∈ M, g ∉ H → CFSG.Open.pRank 2 (H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 1) :
    let J := H ⊓ M
    (∀ t : G, t ∈ J ∧ orderOf t = 2 ↔ t = u ∨ t = z ∨ t = u * z) ∧
    ∀ T : Sylow 2 J,
      let TG := (T : Subgroup J).map J.subtype
      (∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = TG) ∧
      (∀ t : G, t ∈ TG ∧ orderOf t = 2 ↔ t = u ∨ t = z ∨ t = u * z) ∧
      Subgroup.closure {t : G | t ∈ TG ∧ orderOf t = 2} = Subgroup.closure {u, z} ∧
      Nonempty (Subgroup.closure ({u, z} : Set G) ≃*
        Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := by
  classical
  intro J
  have huJ : u ∈ J := ⟨huH, huM⟩
  have huzComm : Commute u z := (Subgroup.mem_centralizer_iff.mp huCentral z hzJ.2).symm
  have hsq : ∀ {x : G}, orderOf x = 2 → x * x = 1 := fun hx => by
    rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hne : ∀ {x : G}, orderOf x = 2 → x ≠ 1 := fun hx h => by simp [h] at hx
  have huzOrder : orderOf (u * z) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [huzComm.mul_pow, pow_two, pow_two, hsq hu, hsq hz, one_mul]
    · intro h
      exact huz (eq_inv_of_mul_eq_one_left h |>.trans (inv_eq_of_mul_eq_one_right (hsq hz)))
  have hkey : ∀ v ∈ J, orderOf v = 2 → v = u ∨ v = z ∨ v = u * z := by
    intro v hvJ hv
    by_contra hnot
    push Not at hnot
    obtain ⟨hvu, hvz, hvuz⟩ := hnot
    have hvzComm : Commute v z := Subgroup.mem_centralizer_iff.mp hzCentral v hvJ
    let A := kleinFourOfCommutingInvolutions v z (hsq hv) (hsq hz) hvzComm
    have hA : IsKleinFour A := isKleinFour_kleinFourOfCommutingInvolutions v z (hsq hv)
      (hsq hz) (hne hv) (hne hz) hvz hvzComm
    have hAmem : ∀ a ∈ A, a = v * z ∨ a = v ∨ a = z ∨ a = 1 := by
      intro a ha
      change a ∈ ({v * z, v, z, 1} : Set G) at ha
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ha
    have hAJ : A ≤ J := by
      intro a ha
      rcases hAmem a ha with rfl | rfl | rfl | rfl
      · exact J.mul_mem hvJ hzJ
      · exact hvJ
      · exact hzJ
      · exact J.one_mem
    have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
      (hAJ.trans inf_le_right).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mp hOnormal)
    have hOH : O ≤ H := by
      refine le_of_kleinFour_centralizers_le hAO hOodd fun a ha ha1 => ?_
      have haJ := hAJ ha
      have hau : a ≠ u := by
        rcases hAmem a ha with rfl | rfl | rfl | rfl
        · intro h
          apply hvuz
          calc v = v * z * z := by rw [mul_assoc, hsq hz, mul_one]
            _ = u * z := by rw [h]
        · exact hvu
        · exact huz.symm
        · exact absurd rfl ha1
      have ha2 : orderOf a = 2 := by
        refine orderOf_eq_prime ?_ ha1
        have h := Monoid.pow_exponent_eq_one (⟨a, ha⟩ : A)
        rw [hA.exponent_two] at h
        exact congrArg Subtype.val h
      have huaComm : Commute u a := (Subgroup.mem_centralizer_iff.mp huCentral a haJ.2).symm
      intro o ho
      obtain ⟨hoO, hoa⟩ := Subgroup.mem_inf.mp ho
      by_contra hoH
      have hoM : o ∈ M := hOM hoO
      have hbound := hrank o hoM hoH
      have hmem : ∀ x ∈ H, o * x = x * o → x ∈ H ⊓ H.map (MulAut.conj o⁻¹).toMonoidHom := by
        intro x hxH hox
        refine Subgroup.mem_inf.mpr ⟨hxH, ?_⟩
        rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, hox, mul_inv_cancel_right]
        exact hxH
      have huK := hmem u huH (Subgroup.mem_centralizer_iff.mp huCentral o hoM)
      have haK := hmem a haJ.1 (Subgroup.mem_centralizer_singleton_iff.mp hoa)
      have htwo := two_le_twoRank_of_commuting_involutions _ ⟨u, huK⟩ ⟨a, haK⟩
        ((Subgroup.orderOf_coe _).symm.trans hu) ((Subgroup.orderOf_coe _).symm.trans ha2)
        (fun h => hau (congrArg Subtype.val h).symm) (Subtype.ext huaComm.eq)
      rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)] at htwo
      omega
    apply hMH
    intro m hm
    rw [← SetLike.mem_coe, ← hMJO] at hm
    obtain ⟨j, hj, o, ho, rfl⟩ := Set.mem_mul.mp hm
    exact H.mul_mem hj.1 (hOH ho)
  have hinvJ : ∀ t : G, t ∈ J ∧ orderOf t = 2 ↔ t = u ∨ t = z ∨ t = u * z := by
    intro t
    constructor
    · rintro ⟨htJ, ht⟩
      exact hkey t htJ ht
    · rintro (rfl | rfl | rfl)
      · exact ⟨huJ, hu⟩
      · exact ⟨hzJ, hz⟩
      · exact ⟨J.mul_mem huJ hzJ, huzOrder⟩
  refine ⟨hinvJ, fun T => ?_⟩
  intro TG
  let V := kleinFourOfCommutingInvolutions u z (hsq hu) (hsq hz) huzComm
  have hV : IsKleinFour V := isKleinFour_kleinFourOfCommutingInvolutions u z (hsq hu)
    (hsq hz) (hne hu) (hne hz) huz huzComm
  have hVmem : ∀ x, x ∈ V ↔ x = u * z ∨ x = u ∨ x = z ∨ x = 1 := by
    intro x
    change x ∈ ({u * z, u, z, 1} : Set G) ↔ _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have huC : u ∈ Subgroup.centralizer (J : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right) huCentral
  have hVcentral : V ≤ Subgroup.centralizer (J : Set G) := by
    intro x hx
    rcases (hVmem x).mp hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mul_mem _ huC hzCentral
    · exact huC
    · exact hzCentral
    · exact Subgroup.one_mem _
  let VJ : Subgroup J := V.subgroupOf J
  have hVJnormal : VJ.Normal := ⟨fun n hn g => by
    have hcomm : (g : G) * n = n * g :=
      Subgroup.mem_centralizer_iff.mp (hVcentral hn) g g.property
    change (g : G) * n * (g : G)⁻¹ ∈ V
    rw [hcomm, mul_inv_cancel_right]
    exact hn⟩
  have hVJtwo : IsPGroup 2 VJ :=
    (IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num) : IsPGroup 2 V).comap_subtype
  have hVT : VJ ≤ T := hVJtwo.le_sylow_of_normal T
  have hmemT : ∀ x (hx : x ∈ J), x ∈ V → x ∈ TG := fun x hx hxV =>
    Subgroup.mem_map_of_mem J.subtype (hVT (show (⟨x, hx⟩ : J) ∈ VJ from hxV))
  have hinvT : ∀ t : G, t ∈ TG ∧ orderOf t = 2 ↔ t = u ∨ t = z ∨ t = u * z := by
    intro t
    constructor
    · rintro ⟨htT, ht⟩
      exact hkey t (Subgroup.map_subtype_le _ htT) ht
    · rintro (rfl | rfl | rfl)
      · exact ⟨hmemT _ huJ ((hVmem _).mpr (Or.inr (Or.inl rfl))), hu⟩
      · exact ⟨hmemT _ hzJ ((hVmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))), hz⟩
      · exact ⟨hmemT _ (J.mul_mem huJ hzJ) ((hVmem _).mpr (Or.inl rfl)), huzOrder⟩
  have hset : {t : G | t ∈ TG ∧ orderOf t = 2} = ({u, z, u * z} : Set G) := by
    ext t
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hinvT t
  have huCl : u ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hzCl : z ∈ Subgroup.closure ({u, z} : Set G) := Subgroup.subset_closure (by simp)
  have hclosure : Subgroup.closure {t : G | t ∈ TG ∧ orderOf t = 2} =
      Subgroup.closure {u, z} := by
    rw [hset]
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact huCl
      · exact hzCl
      · exact Subgroup.mul_mem _ huCl hzCl
    · exact Subgroup.closure_mono (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
        tauto)
  have hVclosure : V = Subgroup.closure {u, z} := by
    apply le_antisymm
    · intro x hx
      rcases (hVmem x).mp hx with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ huCl hzCl
      · exact huCl
      · exact hzCl
      · exact Subgroup.one_mem _
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact (hVmem _).mpr (Or.inr (Or.inl rfl))
      · exact (hVmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hKlein : IsKleinFour (Subgroup.closure ({u, z} : Set G)) := hVclosure ▸ hV
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := Subgroup.closure ({u, z} : Set G))
    (G₂ := Multiplicative (ZMod 2 × ZMod 2))
  exact ⟨exists_sylow_map_eq_of_odd_relIndex inf_le_right
    (odd_relIndex_of_mul_odd_normal inf_le_right hOM hOnormal hOodd hMJO) T, hinvT, hclosure,
    ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩⟩

end CFSG.ProperTwoGeneratedCore.RankOnePair
