module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem le_of_perfect_le_sup_of_odd {K R T : Subgroup H} [R.Normal] (hR : Odd (Nat.card R))
    (hRK : R ≤ normalizer (K : Set H)) (hT : Group.IsPerfect T) (hTKR : T ≤ K ⊔ R) : T ≤ K := by
  have hKQ : (K.subgroupOf (K ⊔ R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hRK)
  let φ : R →* (K ⊔ R : Subgroup H) ⧸ K.subgroupOf (K ⊔ R) :=
    (QuotientGroup.mk' (K.subgroupOf (K ⊔ R))).comp (inclusion le_sup_right)
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf (K ⊔ R)) q
    have hx' : x ∈ ((K ⊔ R : Subgroup H) : Set H) := hx
    rw [mul_normal] at hx'
    obtain ⟨k, hk, r, hr, rfl⟩ := Set.mem_mul.mp hx'
    have hk : k ∈ K := hk
    have hr : r ∈ R := hr
    refine ⟨⟨r, hr⟩, ?_⟩
    change QuotientGroup.mk' (K.subgroupOf (K ⊔ R)) (inclusion le_sup_right ⟨r, hr⟩) =
      QuotientGroup.mk' (K.subgroupOf (K ⊔ R)) ⟨k * r, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
    have h := (mem_normalizer_iff.mp (hRK (inv_mem hr)) k).mp hk
    rw [inv_inv] at h
    change r⁻¹ * (k * r) ∈ K
    rwa [← mul_assoc]
  have hodd : Odd (Nat.card ((K ⊔ R : Subgroup H) ⧸ K.subgroupOf (K ⊔ R))) :=
    hR.of_dvd_nat (Subgroup.card_dvd_of_surjective hφ)
  have hsolv : Group.IsSolvable ((K ⊔ R : Subgroup H) ⧸ K.subgroupOf (K ⊔ R)) :=
    Milestones.odd_order_solvable hodd
  have hTQ : Group.IsPerfect (T.subgroupOf (K ⊔ R)) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTKR).symm.toMonoidHom)
      (subgroupOfEquivOfLe hTKR).symm.surjective
  have himg : (T.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (K.subgroupOf (K ⊔ R))) = ⊥ := by
    by_contra hne
    have : Nontrivial ((T.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (K.subgroupOf (K ⊔ R)))) :=
      (nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect
        ((T.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (K.subgroupOf (K ⊔ R)))) :=
      Group.IsPerfect.map _
    exact Group.IsPerfect.not_isSolvable
      (G := (T.subgroupOf (K ⊔ R)).map (QuotientGroup.mk' (K.subgroupOf (K ⊔ R))))
      (Group.isSolvable_of_isSolvable_injective (subtype_injective _))
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg
  exact le_of_subgroupOf_le hTKR himg

theorem two_layer_fixed_component_orbit_location {t : H} (ht : orderOf t = 2) {T : Subgroup H}
    (hTC : T ≤ centralizer ({t} : Set H))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer ({t} : Set H)))) (hTE : T ≤ pLayer H 2) :
    ∃ M : Subgroup H, IsPComponent 2 M ∧ T ≤ M ⊔ conjugate M t ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ conjugate M t) ⊓ centralizer ({t} : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have htb := orderOf_mk_eq_two hRodd ht
  have hCmap := map_centralizer_eq hRodd htt
  have hTperf : Group.IsPerfect T := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hT
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hTbC : T.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) := by
    rw [← hCmap]
    exact map_mono hTC
  let f : centralizer ({t} : Set H) →*
      centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 H)).comp (centralizer ({t} : Set H)).subtype).codRestrict _
      fun c => by
        rw [← hCmap]
        exact mem_map_of_mem _ c.2
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    have hq' := hq
    rw [← hCmap] at hq'
    obtain ⟨c, hc, hcq⟩ := hq'
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  have hmemR : ∀ x : f.ker, ((x : centralizer ({t} : Set H)) : H) ∈ pPrimeCore 2 H := by
    intro x
    have h : QuotientGroup.mk' (pPrimeCore 2 H) ((x : centralizer ({t} : Set H)) : H) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hfker : ¬ 2 ∣ Nat.card f.ker := by
    let ι : f.ker →* pPrimeCore 2 H :=
      { toFun := fun x => ⟨_, hmemR x⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hι : Function.Injective ι := by
      intro x y h
      have h' : ((ι x : pPrimeCore 2 H) : H) = ((ι y : pPrimeCore 2 H) : H) :=
        congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    intro h2
    exact (Nat.not_even_iff_odd.mpr hRodd)
      (even_iff_two_dvd.mpr (h2.trans (Subgroup.card_dvd_of_injective ι hι)))
  have hTb : IsPComponent 2 ((T.map (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
      (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H)))) := by
    have h := (CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f hf
      hfker).1.mapsTo hT
    have heq : (T.subgroupOf (centralizer ({t} : Set H))).map f =
        (T.map (QuotientGroup.mk' (pPrimeCore 2 H))).subgroupOf
          (centralizer ({QuotientGroup.mk' (pPrimeCore 2 H) t} : Set (H ⧸ pPrimeCore 2 H))) := by
      ext q
      rw [mem_map, mem_subgroupOf, mem_map]
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨c, mem_subgroupOf.mp hc, rfl⟩
      · rintro ⟨x, hx, hxq⟩
        exact ⟨⟨x, hTC hx⟩, mem_subgroupOf.mpr hx, Subtype.ext hxq⟩
    rw [← heq]
    exact h
  have hTbE : T.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ layer (H ⧸ pPrimeCore 2 H) := by
    rw [map_le_iff_le_comap]
    refine hTE.trans (sSup_le fun L hL => ?_)
    rw [← map_le_iff_le_comap]
    obtain ⟨K, hK, -, hLK, -⟩ := hL
    rw [hLK]
    exact component_le_layer hK
  obtain ⟨Mb, hMb, hTK, -, hK2⟩ :=
    ordinary_layer_local_prime_component_orbit_location Nat.prime_two hTbC hTb hTbE
  rw [hK2 htb] at hTK
  obtain ⟨M, hM, hMb'⟩ : ∃ M : Subgroup H, IsPComponent 2 M ∧
      M.map (QuotientGroup.mk' (pPrimeCore 2 H)) = Mb :=
    ⟨_, CatalogueBPrimeJoin.canonicalPrimeLift_isPComponent 2 Mb hMb⟩
  have hMt := isPComponent_conjugate hM t
  have hKmap : (M ⊔ conjugate M t).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      Mb ⊔ conjugate Mb (QuotientGroup.mk' (pPrimeCore 2 H) t) := by
    rw [Subgroup.map_sup, map_conjugate, hMb']
  have hRK : pPrimeCore 2 H ≤ normalizer ((M ⊔ conjugate M t : Subgroup H) : Set H) := by
    intro n hn
    have h := mem_normalizer_sSup (S := {M, conjugate M t}) (g := n) (by
      intro N hN
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hN
      rcases hN with hN | hN <;> rw [hN]
      · exact pPrimeCore_le_normalizer hM hn
      · exact pPrimeCore_le_normalizer hMt hn)
    rwa [sSup_pair] at h
  have hTKR : T ≤ (M ⊔ conjugate M t) ⊔ pPrimeCore 2 H := by
    have h2 : T ≤ ((M ⊔ conjugate M t).map (QuotientGroup.mk' (pPrimeCore 2 H))).comap
        (QuotientGroup.mk' (pPrimeCore 2 H)) :=
      (le_comap_map (QuotientGroup.mk' (pPrimeCore 2 H)) T).trans
        (comap_mono (hTK.trans hKmap.symm.le))
    rwa [comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hTK' := le_of_perfect_le_sup_of_odd hRodd hRK hTperf hTKR
  exact ⟨M, hM, hTK', CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hTK' hTC)
    inf_le_right hT⟩

end CFSG.ComponentClassification.UnbalancedLayer
