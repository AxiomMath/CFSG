module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitBlowup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma46a
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

theorem exists_lift_twoComponent {X : Type} [Group X] [Finite X] {β u : X}
    (huβ : u ∈ centralizer ({β} : Set X)) (hu : orderOf u = 2) {Y : Subgroup (MBar β)}
    (hYle : Y ≤ centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})
    (hY : IsPComponent 2 (Y.subgroupOf (centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)}))) :
    ∃ J : Subgroup X, J ≤ centralizer {β} ⊓ centralizer {u} ∧
      IsPComponent 2 (J.subgroupOf (centralizer {β} ⊓ centralizer {u})) ∧
      (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (∃ k : ℕ, orderOf w = 2 ^ k) → (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ J) ∧
      (∀ S : Subgroup X, (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (∃ k : ℕ, orderOf w = 2 ^ k) → (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ S) →
          J ≤ S) ∧
      (J.subgroupOf (centralizer {β})).map (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
        ({β} : Set X)))) = Y ∧
      ∃ g : ↥J →* ↥Y, Function.Surjective g ∧ ¬ 2 ∣ Nat.card g.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := centralizer ({β} : Set X)
  let u' : ↥M := ⟨u, huβ⟩
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥M)
  let C := centralizer ({u'} : Set ↥M)
  have hu'2 : u' * u' = 1 := Subtype.ext (by
    change u * u = 1
    rw [← sq, ← hu, pow_orderOf_eq_one])
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥M)) := by
    have h2 := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥M)
    rw [QuotientGroup.ker_mk'] at h2
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
  have hCmap : C.map π = centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :=
    map_centralizer_eq hodd hu'2
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} : Set (MBar β))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 ↥M := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 ↥M) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨-, hlift, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  obtain ⟨hĴ, hĴmap⟩ := hlift _ hY
  have hCX : C.map M.subtype = centralizer {β} ⊓ centralizer {u} := by
    rw [map_subtype_centralizer huβ, inf_comm]
  let eC : ↥C ≃* ↥(centralizer ({β} : Set X) ⊓ centralizer {u}) :=
    (C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hCX)
  generalize hĴdef : closure {x : ↥C | x ∈ (Y.subgroupOf (centralizer
    {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})).comap φ ∧ ∃ k : ℕ, orderOf x = 2 ^ k} = Ĵ at hĴ hĴmap
  have hwĴ : ∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)) (hwu : (⟨w, hw⟩ : ↥M) ∈ C),
      (∃ k : ℕ, orderOf w = 2 ^ k) → (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y →
        (⟨⟨w, hw⟩, hwu⟩ : ↥C) ∈ Ĵ := by
    intro w hw hwu ⟨k, hk⟩ hwY
    rw [← hĴdef]
    refine subset_closure ⟨hwY, k, ?_⟩
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hk
  have hJle : (Ĵ.map C.subtype).map M.subtype ≤ centralizer {β} ⊓ centralizer {u} := by
    rw [← hCX]
    exact map_mono (map_subtype_le Ĵ)
  have hJeq : ((Ĵ.map C.subtype).map M.subtype).subgroupOf (centralizer {β} ⊓ centralizer {u}) =
      Ĵ.map eC.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      have h1 : ((eC y : ↥(centralizer ({β} : Set X) ⊓ centralizer {u})) : X) = x :=
        congrArg Subtype.val hyx
      exact ⟨(y : ↥M), ⟨y, hy, rfl⟩, h1⟩
  refine ⟨(Ĵ.map C.subtype).map M.subtype, hJle,
    by rw [hJeq]; exact isPComponent_map_mulEquiv eC hĴ, ?_, ?_, ?_, ?_⟩
  ·
    intro w hw hwu hk hwY
    have hwu' : (⟨w, hw⟩ : ↥M) ∈ C := by
      rw [mem_centralizer_singleton_iff] at hwu ⊢
      exact Subtype.ext hwu
    exact ⟨⟨w, hw⟩, ⟨⟨⟨w, hw⟩, hwu'⟩, hwĴ w hw hwu' hk hwY, rfl⟩, rfl⟩
  ·
    intro S hS
    rw [← hĴdef, MonoidHom.map_closure, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨x, ⟨hxY, k, hk⟩, rfl⟩, rfl⟩
    have hxu : ((x : ↥M) : X) ∈ centralizer {u} := by
      have h := mem_centralizer_singleton_iff.mp x.2
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val h
    refine hS _ (x : ↥M).2 hxu ⟨k, ?_⟩ hxY
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe] at hk
    exact hk
  ·
    have h1 : ((Ĵ.map C.subtype).map M.subtype).subgroupOf M = Ĵ.map C.subtype :=
      comap_map_eq_self_of_injective M.subtype_injective _
    have hcomp : π.comp C.subtype = (centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :
        Set (MBar β))).subtype.comp φ := rfl
    rw [h1, map_map, hcomp, ← map_map, hĴmap, subgroupOf_map_subtype, inf_eq_left.mpr hYle]
  ·
    let eJ : ↥Ĵ ≃* ↥((Ĵ.map C.subtype).map M.subtype) :=
      ((Ĵ.equivMapOfInjective C.subtype C.subtype_injective).trans
        ((Ĵ.map C.subtype).equivMapOfInjective M.subtype M.subtype_injective))
    have hφĴ : ∀ x : ↥Ĵ, ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :
        Set (MBar β)))) : MBar β) ∈ Y := by
      intro x
      have : φ x ∈ Ĵ.map φ := mem_map_of_mem φ x.2
      rw [hĴmap] at this
      exact this
    let g₀ : ↥Ĵ →* ↥Y := ((centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :
      Set (MBar β))).subtype.comp (φ.comp Ĵ.subtype)).codRestrict Y hφĴ
    have hg₀ : Function.Surjective g₀ := by
      rintro ⟨y, hy⟩
      have hy' : (⟨y, hYle hy⟩ : ↥(centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} :
          Set (MBar β)))) ∈ Ĵ.map φ := by
        rw [hĴmap]; exact hy
      obtain ⟨x, hx, hxy⟩ := hy'
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      show ((φ x : ↥(centralizer ({(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)} : Set (MBar β)))) :
        MBar β) = y
      rw [hxy]
    have hg₀k : ¬ 2 ∣ Nat.card g₀.ker := by
      have hle : g₀.ker.map Ĵ.subtype ≤ φ.ker := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : g₀ x = 1 := hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        have h2 := congrArg Subtype.val hx'
        exact h2
      have hc : Nat.card g₀.ker ∣ Nat.card φ.ker := by
        rw [← Subgroup.card_map_of_injective Ĵ.subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact fun h2 => hφk (h2.trans hc)
    refine ⟨g₀.comp eJ.symm.toMonoidHom, hg₀.comp eJ.symm.surjective, ?_⟩
    have hk : Nat.card (g₀.comp eJ.symm.toMonoidHom).ker = Nat.card g₀.ker := by
      rw [← MonoidHom.comap_ker]
      exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ eJ.symm.injective).trans
        (MulEquiv.subgroupCongr (by
          rw [Subgroup.map_comap_eq_self_of_surjective eJ.symm.surjective]))).toEquiv
    rw [hk]
    exact hg₀k

theorem exists_conj_of_inv_mul_mem {G : Type*} [Group G] {R : Subgroup G} [Finite R]
    (hR : Odd (Nat.card R)) {u w : G} (hu : u * u = 1) (hw : w * w = 1) (huw : u⁻¹ * w ∈ R) :
    ∃ c ∈ R, c * u * c⁻¹ = w := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  set o := u * w with ho
  have hoR : o ∈ R := by rw [ho, ← hui]; exact huw
  have hodd : Odd (orderOf o) := by
    have h := orderOf_dvd_natCard (⟨o, hoR⟩ : R)
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hR h
  obtain ⟨k, hk⟩ := hodd
  have hok : o ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one o
  have h1 : u * o * u⁻¹ = o⁻¹ := by
    rw [ho, mul_inv_rev, hui, hwi, ← mul_assoc, hu, one_mul]
  have hinv : u * o ^ k * u⁻¹ = (o ^ k)⁻¹ := by rw [← conj_pow, h1, inv_pow]
  have h3 : o ^ (2 * k) = o⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hok])
  refine ⟨o ^ k, pow_mem hoR k, ?_⟩
  calc o ^ k * u * (o ^ k)⁻¹ = o ^ k * (u * o ^ k * u⁻¹)⁻¹ * u := by group
    _ = o ^ (2 * k) * u := by rw [hinv, inv_inv, ← pow_add, two_mul]
    _ = w := by rw [h3, ho, mul_inv_rev, inv_mul_cancel_right, hwi]

theorem exists_conj_of_mk_conj {G : Type*} [Group G] {N : Subgroup G} [N.Normal] [Finite N]
    (hN : Odd (Nat.card N)) {u v g : G} (hu : u * u = 1) (hv : v * v = 1)
    (h : (u : G ⧸ N) = (g : G ⧸ N) * v * (g : G ⧸ N)⁻¹) : ∃ x : G, x * v * x⁻¹ = u := by
  have hw : g * v * g⁻¹ * (g * v * g⁻¹) = 1 := by
    rw [show g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ by group, hv, mul_one,
      mul_inv_cancel]
  have huw : u⁻¹ * (g * v * g⁻¹) ∈ N := by
    rw [← QuotientGroup.eq, h, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  obtain ⟨c, -, hc⟩ := exists_conj_of_inv_mul_mem hN hu hw huw
  refine ⟨c⁻¹ * g, ?_⟩
  calc c⁻¹ * g * v * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * v * g⁻¹) * c := by group
    _ = c⁻¹ * (c * u * c⁻¹) * c := by rw [hc]
    _ = u := by group

end CFSG.ComponentClassification.HarrisLit.T1
