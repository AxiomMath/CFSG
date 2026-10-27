module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SplitQuotient
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LocalQuotient

public section

namespace CFSG.LyonsUnitaryFour

section Helpers

variable {G : Type*} [Group G]

theorem centralizer_zpowers_eq_centralizer_singleton (z : G) :
    Subgroup.centralizer (Subgroup.zpowers z : Set G) = Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem natCard_map_of_injective_comp_subtype {M : Type*} [Group M] (H : Subgroup G)
    (f : G →* M) (hf : Function.Injective (f.comp H.subtype)) :
    Nat.card (H.map f) = Nat.card H := by
  have hrange : H.map f = (f.comp H.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem injective_comp_subtype_of_le {M : Type*} [Group M] {H H' : Subgroup G} (hle : H' ≤ H)
    (f : G →* M) (hf : Function.Injective (f.comp H.subtype)) :
    Function.Injective (f.comp H'.subtype) := by
  intro a b hab
  have h := congrArg (fun x : H => (x : G)) (@hf ⟨a, hle a.2⟩ ⟨b, hle b.2⟩ hab)
  exact Subtype.ext h

theorem coprime_two_orderOf_of_map {M : Type*} [Group M] (π : G →* M)
    (hker : ¬ 2 ∣ Nat.card π.ker) {y : G} (hy : ¬ 2 ∣ orderOf (π y)) :
    Nat.Coprime 2 (orderOf y) := by
  have hmem : y ^ orderOf (π y) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hpow : y ^ (orderOf (π y) * Nat.card π.ker) = 1 := by
    have h := congrArg Subtype.val
      (pow_card_eq_one' (G := π.ker) (x := ⟨y ^ orderOf (π y), hmem⟩))
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← pow_mul] at h
    exact h
  apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp (h2.trans (orderOf_dvd_of_pow_eq_one hpow))
    with h | h
  · exact hy h
  · exact hker h

theorem exists_lift_coprime_two_orderOf {M : Type*} [Group M] {H : Subgroup G} (π : H →* M)
    (hπ : Function.Surjective π) (hker : ¬ 2 ∣ Nat.card π.ker) {h : M} (hh : orderOf h = 5) :
    ∃ y : H, π y = h ∧ Nat.Coprime 2 (orderOf (y : G)) := by
  obtain ⟨y, rfl⟩ := hπ h
  refine ⟨y, rfl, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact coprime_two_orderOf_of_map π hker (by rw [hh]; decide)

end Helpers

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem unitary_four_exists_third_central {T : Type} [Group T]
    (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2) (S : Sylow 2 G)
    (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T))) (z : G) :
    ∃ w ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype, w ≠ 1 ∧ w ≠ z := by
  obtain ⟨-, -, -, -, hZcard⟩ := unitary_four_sylow_structure hT S U hSU
  apply exists_third_mem_four _ z
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hZcard

theorem lyons_order_fifteen_local_data [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {T : Type} [Group T] (hT : CFSG.Assembly.LowTwoRank.StatedClassicalModel T .PSU 3 2 2)
    (S : Sylow 2 G) (U : Sylow 2 T) (hSU : Nonempty ((S : Subgroup G) ≃* (U : Subgroup T)))
    (hd : (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup G) : Set G))).index = 15)
    {z : G} (hzZ : z ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
    (hz1 : z ≠ 1) :
    ∃ (L : Type) (_ : Group L) (_ : Fintype L) (S₀ : Subgroup L) (h : L)
      (π : Subgroup.centralizer (Subgroup.zpowers z : Set G) →* L)
      (hSC : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G)),
      UnitaryFourByFive S₀ h ∧ Function.Surjective π ∧ ¬ 2 ∣ Nat.card π.ker ∧
      (∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
        π ⟨v, hSC (Subgroup.map_subtype_le _ hv)⟩ ∈ (Subgroup.center S₀).map S₀.subtype) ∧
      (∀ v (hv : v ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype)
        v' (hv' : v' ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype),
        π ⟨v, hSC (Subgroup.map_subtype_le _ hv)⟩ =
          π ⟨v', hSC (Subgroup.map_subtype_le _ hv')⟩ → v = v') := by
  classical
  have hCC := centralizer_zpowers_eq_centralizer_singleton z
  obtain ⟨hKodd, hinj, hnormal, -, h, hh5, hsup, hinf, hcenter, hfix, hfree, -, -⟩ :=
    lyons_order_fifteen_involution_centralizer_split_quotient hnonab hT S U hSU hd hzZ hz1 _ rfl
  obtain ⟨hcard64, hZcomm, -, hZcard, -⟩ :=
    lyons_unitary_four_fusion_and_centralizers hnonab hT S U hSU
  have hZS : (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ≤ S :=
    Subgroup.map_subtype_le _
  have hSC0 : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((mem_map_center_iff.mp hzZ).2 s hs)
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    rw [hCC]
    exact hSC0
  have hZC0 := hZS.trans hSC0
  let e := MulEquiv.subgroupCongr hCC
  let π := (QuotientGroup.mk' (CFSG.oddCore (Subgroup.centralizer ({z} : Set G)))).comp
    e.toMonoidHom
  refine ⟨_, inferInstance, Fintype.ofFinite _, _, h, π, hSC,
    ⟨hnormal, ?_, ?_, ?_, ?_, hh5, hsup, hinf, hfix, hfree⟩, ?_, ?_, ?_, ?_⟩
  · exact (S.isPGroup'.comap_of_injective _ (Subgroup.subtype_injective _)).map _
  · rw [natCard_map_of_injective_comp_subtype _ _ hinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC0).toEquiv]
    exact hcard64
  · have hle : ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype).subgroupOf
        (Subgroup.centralizer ({z} : Set G)) ≤
        (S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G)) := fun x hx => hZS hx
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcenter,
      natCard_map_of_injective_comp_subtype _ _ (injective_comp_subtype_of_le hle _ hinj),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC0).toEquiv,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact hZcard
  · intro x hx y hy
    rw [hcenter]
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    refine ⟨a * b * a⁻¹ * b⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, hZcomm]
    have hab := Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
    rw [commutatorElement_def] at hab
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hab
  · exact (QuotientGroup.mk'_surjective _).comp e.surjective
  · have hker : π.ker =
        (CFSG.oddCore (Subgroup.centralizer ({z} : Set G))).map e.symm.toMonoidHom := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · intro hx
        exact ⟨e x, hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        change e (e.symm y) ∈ _
        rw [e.apply_symm_apply]
        exact hy
    rw [hker, Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hKodd)
  · intro v hv
    rw [hcenter]
    exact Subgroup.mem_map_of_mem _ (show (⟨v, hZC0 hv⟩ : Subgroup.centralizer ({z} : Set G)) ∈
      ((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype).subgroupOf _ from hv)
  · intro v hv v' hv' hvv
    have hvv' := @hinj ⟨⟨v, hZC0 hv⟩, hZS hv⟩ ⟨⟨v', hZC0 hv'⟩, hZS hv'⟩ hvv
    exact congrArg (fun x : ((S : Subgroup G).subgroupOf (Subgroup.centralizer ({z} : Set G))) =>
      ((x : Subgroup.centralizer ({z} : Set G)) : G)) hvv'

end CFSG.LyonsUnitaryFour
