module

public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG CFSG.GorensteinWalter

universe u

structure QuaternionSetting (G : Type u) [Group G] (z : G) (r : ℕ) : Prop where
  three_le : 3 ≤ r
  orderOf_eq_two : orderOf z = 2
  mem_center : z ∈ Subgroup.center G
  eq_of_orderOf_eq_two : ∀ t : G, orderOf t = 2 → t = z
  sylow_equiv : ∀ P : Sylow 2 G, Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2)))
  oddCore_eq_bot : oddCore G = ⊥

theorem nonempty_mulEquiv_of_ker_eq {P A B : Type*} [Group P] [Group A] [Group B] (ψ : P →* A)
    (φ : P →* B) (hψ : Function.Surjective ψ) (hφ : Function.Surjective φ)
    (hker : ψ.ker = φ.ker) : Nonempty (A ≃* B) :=
  ⟨((QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

namespace QuaternionSetting

variable {G : Type u} [Group G] {z : G} {r : ℕ} (h : QuaternionSetting G z r)

include h

theorem zpowers_le_center : Subgroup.zpowers z ≤ Subgroup.center G :=
  Subgroup.zpowers_le.mpr h.mem_center

theorem normal_zpowers : (Subgroup.zpowers z).Normal :=
  Subgroup.normal_of_le_center h.zpowers_le_center

theorem natCard_zpowers : Nat.card (Subgroup.zpowers z) = 2 := by
  rw [Nat.card_zpowers, h.orderOf_eq_two]

theorem isPGroup_zpowers : IsPGroup 2 (Subgroup.zpowers z) :=
  IsPGroup.of_card (n := 1) (by rw [h.natCard_zpowers, pow_one])

theorem hasDihedralSylowTwo_quotient [(Subgroup.zpowers z).Normal] :
    HasDihedralSylowTwo (G ⧸ Subgroup.zpowers z) := by
  intro T
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr := h.three_le
  refine ⟨r - 2, by omega, ?_⟩
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  have hker2 : IsPGroup 2 π.ker := by rw [hker]; exact h.isPGroup_zpowers
  let P : Sylow 2 G :=
    T.comapOfKerIsPGroup π hker2 (by rw [MonoidHom.range_eq_top.mpr hπ]; exact le_top)
  have hP : (P : Subgroup G) = (T : Subgroup (G ⧸ Subgroup.zpowers z)).comap π := rfl
  obtain ⟨e⟩ := h.sylow_equiv P
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have hzP : z ∈ (P : Subgroup G) := by
    rw [hP, Subgroup.mem_comap, hπz]
    exact one_mem _
  let zP : (P : Subgroup G) := ⟨z, hzP⟩
  have hzPord : orderOf zP = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  let ψ : (P : Subgroup G) →* (T : Subgroup (G ⧸ Subgroup.zpowers z)) :=
    (π.comp (P : Subgroup G).subtype).codRestrict _ (fun x =>
      Subgroup.mem_comap.mp
        (x.2 : (x : G) ∈ (T : Subgroup (G ⧸ Subgroup.zpowers z)).comap π))
  have hψ : Function.Surjective ψ := by
    intro t
    obtain ⟨g, hg⟩ := hπ (t : G ⧸ Subgroup.zpowers z)
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [hP, Subgroup.mem_comap, hg]
    exact t.2
  let φ : (P : Subgroup G) →* DihedralGroup (2 ^ (r - 2)) :=
    (CFSG.Semidihedral.CentralQuotients.quaternionToDihedral (2 ^ (r - 2))).comp e.toMonoidHom
  have hφ : Function.Surjective φ :=
    (CFSG.Semidihedral.CentralQuotients.quaternionToDihedral_surjective _).comp e.surjective
  have hezP : e zP = QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))) :=
    quaternionGroup_eq_a_of_orderOf_eq_two (by rw [MulEquiv.orderOf_eq]; exact hzPord)
  have hkψ : ψ.ker = Subgroup.zpowers zP := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      have h1 : π (x : G) = 1 := congrArg Subtype.val hx
      have h2 : (x : G) ∈ Subgroup.zpowers z := by
        rw [← hker]; exact h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h2
      exact ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
    · rintro ⟨k, rfl⟩
      apply Subtype.ext
      change π ((zP ^ k : (P : Subgroup G)) : G) = 1
      rw [Subgroup.coe_zpow, map_zpow]
      change π z ^ k = 1
      rw [hπz, one_zpow]
  have hkφ : φ.ker = Subgroup.zpowers zP := by
    ext x
    have hmap : Subgroup.zpowers (e zP) = (Subgroup.zpowers zP).map e.toMonoidHom :=
      (MonoidHom.map_zpowers e.toMonoidHom zP).symm
    rw [MonoidHom.mem_ker]
    change CFSG.Semidihedral.CentralQuotients.quaternionToDihedral _ (e x) = 1 ↔ _
    rw [← MonoidHom.mem_ker, CFSG.Semidihedral.CentralQuotients.quaternionToDihedral_ker]
    change e x ∈ Subgroup.zpowers
      (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) ↔ _
    rw [← hezP, hmap, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  obtain ⟨f⟩ := nonempty_mulEquiv_of_ker_eq ψ φ hψ hφ (hkψ.trans hkφ.symm)
  exact ⟨f⟩

variable [Finite G]

theorem pPrimeCore_quotient_eq_bot [(Subgroup.zpowers z).Normal] :
    pPrimeCore 2 (G ⧸ Subgroup.zpowers z) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Subgroup.zpowers z := QuotientGroup.ker_mk' _
  let Nbar : Subgroup (G ⧸ Subgroup.zpowers z) := pPrimeCore 2 (G ⧸ Subgroup.zpowers z)
  have hNbar_normal : Nbar.Normal := pPrimeCore_normal
  have hNbar_odd : Odd (Nat.card Nbar) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let N : Subgroup G := Nbar.comap π
  have hNnormal : N.Normal := hNbar_normal.comap π
  have hcard : Nat.card N = 2 * Nat.card Nbar := by
    rw [natCard_comap_eq π hπ, hker, h.natCard_zpowers]
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have hzN : z ∈ N := by
    rw [Subgroup.mem_comap, hπz]
    exact one_mem _
  let z' : N := ⟨z, hzN⟩
  have hz'ord : orderOf z' = 2 := by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hz'central : z' ∈ Subgroup.center N := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp h.mem_center g)
  let P0 : Subgroup N := Subgroup.zpowers z'
  have hP0card : Nat.card P0 = 2 := by rw [Nat.card_zpowers, hz'ord]
  have hP0p : IsPGroup 2 P0 := IsPGroup.of_card (n := 1) (by rw [hP0card, pow_one])
  have hP0index : P0.index = Nat.card Nbar := by
    have h1 := Subgroup.card_mul_index P0
    rw [hP0card, hcard] at h1
    omega
  have hP0idx : ¬ 2 ∣ P0.index := by
    rw [hP0index]
    exact hNbar_odd.not_two_dvd_nat
  let P : Sylow 2 N := hP0p.toSylow hP0idx
  have hPcoe : (P : Subgroup N) = P0 := rfl
  have hnc : Subgroup.normalizer (P : Set N) ≤ Subgroup.centralizer (P : Set N) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hp' : p ∈ Subgroup.center N := by
      have : (P : Subgroup N) ≤ Subgroup.center N := by
        rw [hPcoe]
        exact Subgroup.zpowers_le.mpr hz'central
      exact this hp
    exact (Subgroup.mem_center_iff.mp hp' x).symm
  obtain ⟨K, hKn, hK2, hKidx, -, hKchar, -, -, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement P hnc
  have : K.Characteristic := hKchar
  have hKG : (K.map N.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  have hKodd : Odd (Nat.card (K.map N.subtype)) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact Nat.not_even_iff_odd.mp (fun he => hK2 (even_iff_two_dvd.mp he))
  have hKle : K.map N.subtype ≤ oddCore G := le_sSup ⟨hKG, hKodd⟩
  rw [h.oddCore_eq_bot, le_bot_iff,
    Subgroup.map_eq_bot_iff_of_injective K N.subtype_injective] at hKle
  have hKidx2 : K.index = 2 := by rw [hKidx, hPcoe, hP0card]
  have hKcard : Nat.card K = 1 := by rw [hKle]; exact Subgroup.card_bot
  have hcardN : Nat.card N = 2 := by
    have h1 := Subgroup.card_mul_index K
    rw [hKcard, hKidx2] at h1
    omega
  have : Nat.card Nbar = 1 := by omega
  exact Subgroup.card_eq_one.mp this

theorem gw_trichotomy (hGW : gorensteinWalterStatement.{u}) [(Subgroup.zpowers z).Normal] :
    IsPGroup 2 (G ⧸ Subgroup.zpowers z) ∨
      Nonempty ((G ⧸ Subgroup.zpowers z) ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type u) (_ : Field K) (_ : Finite K), IsOddPrimePower (Nat.card K) ∧
        ∃ L : Subgroup (G ⧸ Subgroup.zpowers z), L.Normal ∧ Odd L.index ∧
          (Nonempty (L ≃* PSL2 K) ∨ Nonempty (L ≃* PGL2 K)) := by
  have hO2 := h.pPrimeCore_quotient_eq_bot
  let qE : ((G ⧸ Subgroup.zpowers z) ⧸ pPrimeCore 2 (G ⧸ Subgroup.zpowers z)) ≃*
      (G ⧸ Subgroup.zpowers z) :=
    (QuotientGroup.quotientMulEquivOfEq hO2).trans (QuotientGroup.quotientBot (G := _))
  rcases hGW (G ⧸ Subgroup.zpowers z) h.hasDihedralSylowTwo_quotient with
    ⟨_, hQ⟩ | ⟨_, ⟨e7⟩⟩ | ⟨_, K, hK, L', hL'n, hL'i, hL'model⟩
  · exact Or.inl (hQ.of_equiv qE)
  · exact Or.inr (Or.inl ⟨qE.symm.trans e7⟩)
  · refine Or.inr (Or.inr ⟨K, inferInstance, inferInstance, hK, L'.map qE.toMonoidHom,
      hL'n.map _ qE.surjective, ?_, ?_⟩)
    · rw [Subgroup.index_map_of_bijective qE.bijective]
      exact hL'i
    · let eL : L' ≃* L'.map qE.toMonoidHom := L'.equivMapOfInjective _ qE.injective
      rcases hL'model with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
      · exact Or.inl ⟨eL.symm.trans e⟩
      · exact Or.inr ⟨eL.symm.trans e⟩

end QuaternionSetting

end CFSG.ClassicalInvolution.QuaternionStructure
