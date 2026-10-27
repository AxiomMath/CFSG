module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCHGF2CenterFourWidthThreeRankFour
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCCyclicFourExclusion
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBMLocalConjugate

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement Pointwise

namespace SteinbergCH

variable {G : Type*} [Group G]

theorem bk_conjugate_clauses
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) {z : G}
    (hzZ : z ∈ (center Q).map Q.subtype) (hzord : orderOf z = 2) :
    ∀ g : G, (CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ↔
        ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥) ∧
      (⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ↔
        g⁻¹ * z * g ∈ M ⊓ centralizer ((center Q).map Q.subtype : Set G)) := by
  obtain ⟨⟨D, hD⟩, hBK⟩ := gf2_critical_center_and_exponent_four_reduction hchar he hM hsym hB
    hBM hQ hzZ hzord rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcase⟩ := hBK D hD _ rfl _ rfl
  have hnotB : ¬ (8 ≤ Nat.card ((center D).map D.subtype) ∧ ∃ x : Q, 8 ≤ orderOf x) := by
    rintro ⟨-, x, hx⟩
    have h1 : x ^ 4 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hexp x x.2)
    have h2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h1)
    omega
  obtain ⟨-, -, hZ₀, -⟩ := (hcase hnex).elim (fun h => h.1) fun h => absurd h.1 hnotB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hgcl, -⟩ := hBK D hD (center Q) hZ₀.symm _ rfl
  exact fun g => ⟨(hgcl g).2.1, (hgcl g).2.2.1⟩

theorem conjugate_center_facts {M Z : Subgroup G} {z : G}
    (huniq : ∀ y ∈ Z, orderOf y = 2 → y = z) (hMC : M = centralizer ({z} : Set G))
    (hMNZ : M = normalizer (Z : Set G)) (hZcyc : IsCyclic Z) (hZ4 : Nat.card Z = 4) (g : G) :
    IsCyclic (CFSG.conjugate Z g) ∧ Nat.card (CFSG.conjugate Z g) = 4 ∧
    normalizer (CFSG.conjugate Z g : Set G) = centralizer ({g⁻¹ * z * g} : Set G) ∧
    ∀ t : G, zpowers t = CFSG.conjugate Z g → orderOf t = 4 ∧ t ^ 2 = g⁻¹ * z * g := by
  have hcard : Nat.card (CFSG.conjugate Z g) = 4 := by
    rw [CFSG.conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hZ4]
  refine ⟨isCyclic_of_surjective ((MulAut.conj g⁻¹).subgroupMap Z).toMonoidHom
    (MulEquiv.surjective _), hcard, ?_, fun t ht => ?_⟩
  · rw [normalizer_conjugate_eq, ← hMNZ, hMC, conjugate_centralizer_singleton_eq]
  · have h4 : orderOf t = 4 := by rw [← Nat.card_zpowers, ht, hcard]
    refine ⟨h4, ?_⟩
    have h2 : orderOf (t ^ 2) = 2 := by
      rw [orderOf_pow' t (by norm_num), h4]
      rfl
    have hmem : g * t ^ 2 * g⁻¹ ∈ Z := by
      rw [← mem_conjugate_iff_conj_mem, ← ht]
      exact pow_mem (mem_zpowers t) 2
    have hord : orderOf (g * t ^ 2 * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h2]
    have hz' := huniq _ hmem hord
    calc t ^ 2 = g⁻¹ * (g * t ^ 2 * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [hz']

theorem centralizes_or_inverts {Z : Subgroup G} (hZcyc : IsCyclic Z) (hZ4 : Nat.card Z = 4)
    {h : G} (hh : h ∈ normalizer (Z : Set G)) :
    (∀ c ∈ Z, h * c * h⁻¹ = c) ∨ ∀ c ∈ Z, h * c * h⁻¹ = c⁻¹ := by
  obtain ⟨c₀, hc₀Z, hc₀⟩ := exists_zpowers_eq_of_isCyclic hZcyc
  have h4 : orderOf c₀ = 4 := by rw [← Nat.card_zpowers, hc₀, hZ4]
  have hmem : h * c₀ * h⁻¹ ∈ zpowers c₀ := by
    rw [hc₀]
    exact (mem_normalizer_iff.mp hh c₀).mp hc₀Z
  have hord : orderOf (h * c₀ * h⁻¹) = 4 := by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h4]
  have hc3 : c₀ ^ 3 = c₀⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, show 3 + 1 = orderOf c₀ by rw [h4],
      pow_orderOf_eq_one]
  have hconj : ∀ k : ℤ, h * c₀ ^ k * h⁻¹ = (h * c₀ * h⁻¹) ^ k := fun k => by
    rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
  rcases eq_or_eq_of_mem_zpowers_of_orderOf_eq_four h4 hmem hord with h1 | h1
  · left
    intro c hc
    rw [← hc₀] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [hconj, h1]
  · right
    intro c hc
    rw [← hc₀] at hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [hconj, h1, hc3, inv_zpow]

theorem sq_mem_of_order_four_root [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzZ : z ∈ (center Q).map Q.subtype)
    (hzord : orderOf z = 2) (hZcyc : IsCyclic (center Q)) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hΦ : (frattini Q).map Q.subtype = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hρ : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hker : ρ.ker = CFSG.pCore 2 M) {t : G} (htM : t ∈ M) (ht4 : orderOf t = 4)
    (htZ : ∀ c ∈ (center Q).map Q.subtype, t * c = c * t)
    (hNX : normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G)) : t ^ 2 ∈ Q := by
  by_contra haQ
  have hinj := M.subtype_injective
  have hPQ : (CFSG.pCore 2 M).map M.subtype = Q := by rw [hQ]; rfl
  obtain ⟨e, heval⟩ : ∃ e : CFSG.pCore 2 M ≃* Q,
      ∀ x : CFSG.pCore 2 M, ((e x : Q) : G) = ((x : M) : G) := by
    subst hQ
    exact ⟨(CFSG.pCore 2 M).equivMapOfInjective M.subtype hinj, fun _ => rfl⟩
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [← hPQ]
    exact mem_map_iff_mem hinj
  have hzQ : z ∈ Q := map_subtype_le _ hzZ
  have hcyc₀ : IsCyclic (center (CFSG.pCore 2 M)) :=
    isCyclic_of_surjective (Subgroup.centerCongr e).symm.toMonoidHom (MulEquiv.surjective _)
  have hz₀ord : orderOf (e.symm ⟨z, hzQ⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hzord
  have hcomm₀ : commutator (CFSG.pCore 2 M) = zpowers (e.symm ⟨z, hzQ⟩) := by
    have h1 : commutator Q = zpowers (⟨z, hzQ⟩ : Q) := by
      apply map_injective Q.subtype_injective
      rw [map_subtype_commutator, hQ', MonoidHom.map_zpowers]
      rfl
    rw [← map_commutator_mulEquiv e.symm, h1, MonoidHom.map_zpowers]
    rfl
  have hfrat₀ : frattini (CFSG.pCore 2 M) = zpowers (e.symm ⟨z, hzQ⟩) := by
    have h1 : frattini Q = zpowers (⟨z, hzQ⟩ : Q) := by
      apply map_injective Q.subtype_injective
      rw [hΦ, MonoidHom.map_zpowers]
      rfl
    rw [← map_frattini_mulEquiv e.symm, h1, MonoidHom.map_zpowers]
    rfl
  have ht₀ : orderOf (⟨t, htM⟩ : M) = 4 := by rw [← Subgroup.orderOf_coe]; exact ht4
  have htN₀ : (⟨t, htM⟩ : M) ∈ normalizer (CFSG.pCore 2 M : Set M) := by
    rw [normalizer_eq_top]
    exact mem_top _
  have htZ₀ : ∀ c : CFSG.pCore 2 M, c ∈ center (CFSG.pCore 2 M) →
      (⟨t, htM⟩ : M) * (c : M) * (⟨t, htM⟩ : M)⁻¹ = c := by
    intro c hc
    have hcZ : ((c : M) : G) ∈ (center Q).map Q.subtype := by
      refine ⟨e c, ?_, heval c⟩
      rw [← map_center_eq e]
      exact mem_map_of_mem _ hc
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, htZ _ hcZ]
    group
  have haQ₀ : (⟨t, htM⟩ : M) ^ 2 ∉ CFSG.pCore 2 M := fun h =>
    haQ (by have := hQmap.mpr h; rwa [Subgroup.coe_pow] at this)
  have hNX₀ : normalizer (zpowers (⟨t, htM⟩ : M) : Set M) =
      centralizer ({(⟨t, htM⟩ : M) ^ 2} : Set M) := by
    ext x
    have h1 : x ∈ normalizer (zpowers (⟨t, htM⟩ : M) : Set M) ↔
        (x : G) ∈ normalizer (zpowers t : Set G) := by
      rw [mem_normalizer_iff_map_conj_eq, mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers,
        MonoidHom.map_zpowers]
      constructor
      · intro h
        have h' := congrArg (map M.subtype) h
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h'
        simpa [MulAut.conj_apply] using h'
      · intro h
        apply map_injective hinj
        rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        simpa [MulAut.conj_apply] using h
    rw [h1, hNX, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor <;> intro h
    · exact Subtype.ext (by simpa using h)
    · simpa using congrArg Subtype.val h
  obtain ⟨-, -, hTT, -, -⟩ :=
    cyclic_four_normalizer_excludes_order_four_central_quotient_action (G := M)
      (Q := CFSG.pCore 2 M) CFSG.pCore_isPGroup hcyc₀ hz₀ord hfrat₀ hcomm₀ htN₀ ht₀ htZ₀ haQ₀
      hNX₀ _ (hρ ⟨t, htM⟩)
  apply haQ₀
  rw [← hker, MonoidHom.mem_ker, pow_two]
  apply Units.ext
  rw [map_mul, Units.val_mul, hTT, Units.val_one]

theorem conjugate_le_iff_mem [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzZ : z ∈ (center Q).map Q.subtype)
    (hzord : orderOf z = 2) (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G)) (hZcyc : IsCyclic (center Q))
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hΦ : (frattini Q).map Q.subtype = zpowers z)
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {ρ : M →* LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hρ : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      ((ρ h : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hker : ρ.ker = CFSG.pCore 2 M)
    (hbk : ∀ g : G, CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ↔
        ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype)) :
    ∀ g : G, CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ↔ g⁻¹ * z * g ∈ Q := by
  have hZcyc' : IsCyclic ((center Q).map Q.subtype) :=
    isCyclic_of_surjective
      ((center Q).equivMapOfInjective Q.subtype Q.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)
  intro g
  constructor
  · intro hle
    have hcomm := (hbk g).mp hle
    obtain ⟨hcyc, -, hN, hgen⟩ := conjugate_center_facts huniq hMC hMNZ hZcyc' hZ4 g
    obtain ⟨t, htX, ht⟩ := exists_zpowers_eq_of_isCyclic hcyc
    obtain ⟨h4, hsq⟩ := hgen t ht
    have htZ : ∀ c ∈ (center Q).map Q.subtype, t * c = c * t := by
      intro c hc
      have hc' := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hc
      exact mem_centralizer_iff.mp hc' t (ht ▸ mem_zpowers t)
    have hNX : normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G) := by
      rw [ht, hN, hsq]
    rw [← hsq]
    exact sq_mem_of_order_four_root hQ hzZ hzord hZcyc hQ' hΦ hρ hker (hle htX) h4 htZ hNX
  · intro h
    by_cases ha : g⁻¹ * z * g = z
    · have hgM : g ∈ M := by
        rw [hMC, mem_centralizer_singleton_iff]
        calc g * z = g * (g⁻¹ * z * g) := by rw [ha]
          _ = z * g := by group
      rw [mem_normalizer_iff_conjugate_eq.mp (hMNZ ▸ hgM)]
      exact (map_subtype_le _).trans (by rw [hQ]; exact map_subtype_le _)
    · exact le_sup_right.trans (hconj g h ha).1

theorem canonical_root_package [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G)) (hMNQ : M = normalizer (Q : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G))
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    {a g : G} (haQ : a ∈ Q) (haz : a ≠ z) (hg : g⁻¹ * z * g = a) :
    CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
    CFSG.conjugate ((center Q).map Q.subtype) g ≠ (center Q).map Q.subtype ∧
    CFSG.conjugate ((center Q).map Q.subtype) g ⊓ Q = zpowers a ∧
    ∀ t : G, zpowers t = CFSG.conjugate ((center Q).map Q.subtype) g → ∀ htM : t ∈ M,
      orderOf ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = 2 ∧
      ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Module.finrank (ZMod 2) (LinearMap.range
        ((((ι ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
          Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1)) =
          m := by
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [hQ]
    exact mem_map_iff_mem M.subtype_injective
  have hQM : Q ≤ M := by rw [hQ]; exact map_subtype_le _
  have hzM : z ∈ M := hMC ▸ mem_centralizer_singleton_iff.mpr rfl
  have haZ : a ∉ (center Q).map Q.subtype := by
    intro h
    refine haz (huniq a h ?_)
    rw [← hg, show g⁻¹ * z * g = MulAut.conj g⁻¹ z by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq, hzord]
  have key : CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      CFSG.conjugate ((center Q).map Q.subtype) g ≠ (center Q).map Q.subtype ∧
      CFSG.conjugate ((center Q).map Q.subtype) g ⊓ Q = zpowers a ∧
      ∀ t : G, zpowers t = CFSG.conjugate ((center Q).map Q.subtype) g → t ∈ M ∧
        orderOf t = 4 ∧ t ^ 2 = a ∧ (∀ c ∈ (center Q).map Q.subtype, t * c = c * t) ∧
        normalizer (zpowers t : Set G) = centralizer ({t ^ 2} : Set G) ∧ t ∉ Q := by
    obtain ⟨-, hXM, hXcyc, hXcomm, hXN, hgen⟩ :=
      fused_conjugate_center huniq hMC hMNZ hconj hZ4 haQ haz hg
    have haZ' : ∃ q ∈ Q, a * q ≠ q * a := by
      by_contra hall
      push Not at hall
      exact haZ ⟨⟨a, haQ⟩, mem_center_iff.mpr fun c => Subtype.ext (hall c c.2).symm, rfl⟩
    have hgens := fused_generators hQ hzord hMNQ hΦ hQ' haQ haZ' hXM hXcomm hXN hgen
    obtain ⟨t₁, -, ht₁⟩ := exists_zpowers_eq_of_isCyclic hXcyc
    obtain ⟨-, -, hsq₁, -, -, htQ₁⟩ := hgens t₁ ht₁
    refine ⟨hXM, fun hXZ => ?_, ht₁ ▸ zpowers_inf_eq_of_sq htQ₁ hsq₁ haQ, hgens⟩
    have haX : a ∈ CFSG.conjugate ((center Q).map Q.subtype) g := by
      rw [← ht₁, ← hsq₁]
      exact pow_mem (mem_zpowers t₁) 2
    rw [hXZ] at haX
    exact haZ haX
  refine ⟨key.1, key.2.1, key.2.2.1, fun t ht htM => ?_⟩
  have hgt := key.2.2.2 t ht
  have hσ2 : ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    apply hQmap.mp
    rw [Subgroup.coe_pow]
    exact hgt.2.2.1 ▸ haQ
  have hσ1 : ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => hgt.2.2.2.2.2 (hQmap.mpr h)
  have hca := cyclic_four_core_action hQ hzord hzM hΦ hQ' hrule htM (hιf ⟨t, htM⟩) hgt.2.1
    (hgt.2.2.1 ▸ haQ) (hgt.2.2.1 ▸ haZ) hgt.2.2.2.1 hgt.2.2.2.2.1
    (a₀ := ⟨⟨a, hQM haQ⟩, hQmap.mp haQ⟩) hgt.2.2.1.symm
  exact ⟨orderOf_eq_prime hσ2 hσ1, hca.2.choose, hca.2.choose_spec.2.2.1, hca.2.choose_spec.1⟩

theorem relIndex_inf_centralizer_eq_two {Z K : Subgroup G} (hZcyc : IsCyclic Z)
    (hZ4 : Nat.card Z = 4) (hKN : K ≤ normalizer (Z : Set G)) {a : G} (haK : a ∈ K)
    (haC : a ∉ centralizer (Z : Set G)) : (K ⊓ centralizer (Z : Set G)).relIndex K = 2 := by
  obtain ⟨c₀, hc₀Z, hc₀⟩ := exists_zpowers_eq_of_isCyclic hZcyc
  have h4 : orderOf c₀ = 4 := by rw [← Nat.card_zpowers, hc₀, hZ4]
  have hc₀ne : c₀⁻¹ ≠ c₀ := by
    intro h
    have h2 : c₀ ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [← h]
      exact inv_mul_cancel c₀
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hdich : ∀ h ∈ normalizer (Z : Set G), h * c₀ * h⁻¹ = c₀ ∨ h * c₀ * h⁻¹ = c₀⁻¹ :=
    fun h hh => (centralizes_or_inverts hZcyc hZ4 hh).imp (fun h1 => h1 c₀ hc₀Z)
      (fun h1 => h1 c₀ hc₀Z)
  have hcent : ∀ h ∈ normalizer (Z : Set G),
      h ∈ centralizer (Z : Set G) ↔ h * c₀ * h⁻¹ = c₀ := by
    intro h hh
    constructor
    · intro hc
      rw [← mem_centralizer_iff.mp hc c₀ hc₀Z]
      group
    · intro hc
      rcases centralizes_or_inverts hZcyc hZ4 hh with h1 | h1
      · refine mem_centralizer_iff.mpr fun c hc' => ?_
        calc c * h = h * c * h⁻¹ * h := by rw [h1 c hc']
          _ = h * c := by group
      · exact absurd ((h1 c₀ hc₀Z).symm.trans hc) hc₀ne
  have haC' : a * c₀ * a⁻¹ = c₀⁻¹ :=
    (hdich a (hKN haK)).resolve_left fun h => haC ((hcent a (hKN haK)).mpr h)
  rw [relIndex_eq_two_iff]
  refine ⟨a, haK, fun b hb => ?_⟩
  have hbN := hKN hb
  have hbaN : b * a ∈ normalizer (Z : Set G) := mul_mem hbN (hKN haK)
  have hba : (b * a) * c₀ * (b * a)⁻¹ = (b * c₀ * b⁻¹)⁻¹ := by
    calc (b * a) * c₀ * (b * a)⁻¹ = b * (a * c₀ * a⁻¹) * b⁻¹ := by group
      _ = b * c₀⁻¹ * b⁻¹ := by rw [haC']
      _ = (b * c₀ * b⁻¹)⁻¹ := by group
  simp only [mem_inf, and_iff_right hb, and_iff_right (mul_mem hb haK)]
  rw [hcent _ hbaN, hcent _ hbN, hba]
  rcases hdich b hbN with h1 | h1
  · rw [h1]
    exact Or.inr ⟨rfl, hc₀ne⟩
  · rw [h1, inv_inv]
    exact Or.inl ⟨rfl, hc₀ne⟩

end SteinbergCH

namespace SteinbergCH

theorem cyclic_root_package {G : Type} [Group G] [Finite G] {M Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzord : orderOf z = 2)
    (huniq : ∀ y ∈ (center Q).map Q.subtype, orderOf y = 2 → y = z)
    (hMC : M = centralizer ({z} : Set G)) (hMNQ : M = normalizer (Q : Set G))
    (hMNZ : M = normalizer ((center Q).map Q.subtype : Set G))
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ4 : Nat.card ((center Q).map Q.subtype) = 4)
    (hconj : ∀ g : G, g⁻¹ * z * g ∈ Q → g⁻¹ * z * g ≠ z →
      (center Q).map Q.subtype ⊔ CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ∧
      ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ∧
      IsCyclic (CFSG.conjugate ((center Q).map Q.subtype) g) ∧
      Nat.card (CFSG.conjugate ((center Q).map Q.subtype) g) =
        Nat.card ((center Q).map Q.subtype))
    [CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))]
    {b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))}
    (hrule : ∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
      z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
        (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val)
    (ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b)
    (hιf : ∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
      (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
          LinearMap.GeneralLinearGroup (ZMod 2)
            (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
        Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
          (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
        Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
    (hzZ : z ∈ (center Q).map Q.subtype) (hZcyc : IsCyclic (center Q))
    (hSyl : ∀ S : Subgroup G, IsSylowOf 2 S M → IsSylowOf 2 S ⊤)
    (hle : ∀ g : G, CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ↔ g⁻¹ * z * g ∈ Q)
    (hbk : ∀ g : G, (CFSG.conjugate ((center Q).map Q.subtype) g ≤ M ↔
        ⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥) ∧
      (⁅(center Q).map Q.subtype, CFSG.conjugate ((center Q).map Q.subtype) g⁆ = ⊥ ↔
        g⁻¹ * z * g ∈ M ⊓ centralizer ((center Q).map Q.subtype : Set G)))
    {Z : Subgroup G} (hZ : Z = (center Q).map Q.subtype) {F : Set G}
    (hF : F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z}) :
    (∀ g : G, CFSG.conjugate Z g ≤ M ↔ g⁻¹ * z * g ∈ Q) ∧
    {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) =
      {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) ∧
    (∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g ≠ Z → g⁻¹ * z * g ∈ F) ∧
    (∀ a ∈ F, ∀ g : G, g⁻¹ * z * g = a →
      CFSG.conjugate Z g ≤ M ∧ CFSG.conjugate Z g ≠ Z ∧ CFSG.conjugate Z g ⊓ Q = zpowers a ∧
      ∀ t : G, zpowers t = CFSG.conjugate Z g → ∀ htM : t ∈ M,
        ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Module.finrank (ZMod 2) (LinearMap.range
          ((((ι ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2)
              (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
            Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1)) =
            m) ∧
    (∀ g : G, CFSG.conjugate Z g ≤ M → ∀ t : G, zpowers t = CFSG.conjugate Z g →
      ∀ htM : t ∈ M, orderOf ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) ≠ 4) ∧
    (F = ∅ ↔ ∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g = Z) ∧
    (F = ∅ ↔ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
      ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = {z}) ∧
    (F = ∅ → ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
      a ∉ M ⊓ centralizer (Z : Set G) ∧ ∀ c ∈ Z, a * c * a⁻¹ = c⁻¹) ∧
    (F = ∅ → IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      ∀ S : Subgroup G, IsSylowOf 2 S M →
        (S ⊓ centralizer (Z : Set G)).relIndex S = 2 ∧ Q ≤ S ⊓ centralizer (Z : Set G) ∧
        Z ≤ (center ↥(S ⊓ centralizer (Z : Set G))).map (S ⊓ centralizer (Z : Set G)).subtype ∧
        {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((S ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) =
          {z} ∧
        ∃ a ∈ S, (∃ g : G, g⁻¹ * z * g = a) ∧ a ∉ S ⊓ centralizer (Z : Set G)) := by
  subst hZ
  have hzQ : z ∈ Q := map_subtype_le _ hzZ
  have hZQ : (center Q).map Q.subtype ≤ Q := map_subtype_le _
  have hQM : Q ≤ M := by rw [hQ]; exact map_subtype_le _
  have hQmap : ∀ {x : M}, (x : G) ∈ Q ↔ x ∈ CFSG.pCore 2 M := fun {x} => by
    rw [hQ]
    exact mem_map_iff_mem M.subtype_injective
  have hZcyc' : IsCyclic ((center Q).map Q.subtype) :=
    isCyclic_of_surjective
      ((center Q).equivMapOfInjective Q.subtype Q.subtype_injective).toMonoidHom
      (MulEquiv.surjective _)
  have hgM : ∀ g : G, g⁻¹ * z * g = z → g ∈ M := fun g ha => by
    rw [hMC, mem_centralizer_singleton_iff]
    calc g * z = g * (g⁻¹ * z * g) := by rw [ha]
      _ = z * g := by group
  have hint : {w | ∃ g : G, g⁻¹ * z * g = w} ∩
      ((M ⊓ centralizer ((center Q).map Q.subtype : Set G) : Subgroup G) : Set G) =
      {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) := by
    ext w
    constructor
    · rintro ⟨⟨g, rfl⟩, hw⟩
      exact ⟨⟨g, rfl⟩, (hle g).mp ((hbk g).1.mpr ((hbk g).2.mpr hw))⟩
    · rintro ⟨⟨g, rfl⟩, hw⟩
      exact ⟨⟨g, rfl⟩, (hbk g).2.mp ((hbk g).1.mp ((hle g).mpr hw))⟩
  have h3a : ∀ g : G, CFSG.conjugate ((center Q).map Q.subtype) g ≤ M →
      CFSG.conjugate ((center Q).map Q.subtype) g ≠ (center Q).map Q.subtype →
      g⁻¹ * z * g ∈ F := by
    intro g hle' hne
    rw [hF, mem_fusedSet_iff]
    exact ⟨⟨g, rfl⟩, (hle g).mp hle', fun ha =>
      hne (mem_normalizer_iff_conjugate_eq.mp (hMNZ ▸ hgM g ha))⟩
  have hroot := fun a (ha : a ∈ F) g (hg : g⁻¹ * z * g = a) => by
    rw [hF, mem_fusedSet_iff] at ha
    exact canonical_root_package hQ hzord huniq hMC hMNQ hMNZ hΦ hQ' hZ4 hconj hrule ι hιf
      ha.2.1 ha.2.2 hg
  have hF0 : F = ∅ ↔ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
      ((M ⊓ centralizer ((center Q).map Q.subtype : Set G) : Subgroup G) : Set G) = {z} := by
    rw [hint]
    constructor
    · intro hF0
      ext w
      constructor
      · rintro ⟨⟨g, rfl⟩, hw⟩
        by_contra hne
        have : g⁻¹ * z * g ∈ F := by
          rw [hF, mem_fusedSet_iff]
          exact ⟨⟨g, rfl⟩, hw, hne⟩
        rw [hF0] at this
        exact this
      · rintro rfl
        exact ⟨⟨1, by group⟩, hzQ⟩
    · intro hset
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      rw [hF, mem_fusedSet_iff] at ha
      obtain ⟨⟨g, hg⟩, haQ, haz⟩ := ha
      have : a ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) := ⟨⟨g, hg⟩, haQ⟩
      rw [hset] at this
      exact haz this
  have h6 : F = ∅ → ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
      a ∉ M ⊓ centralizer ((center Q).map Q.subtype : Set G) ∧
      ∀ c ∈ (center Q).map Q.subtype, a * c * a⁻¹ = c⁻¹ := by
    intro hF00 a ha
    obtain ⟨⟨⟨g, hg⟩, haM⟩, haz⟩ := ha
    have hnot : a ∉ M ⊓ centralizer ((center Q).map Q.subtype : Set G) := by
      intro hmem
      have : a ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
          ((M ⊓ centralizer ((center Q).map Q.subtype : Set G) : Subgroup G) : Set G) :=
        ⟨⟨g, hg⟩, hmem⟩
      rw [hF0.mp hF00] at this
      exact haz this
    refine ⟨hnot, ?_⟩
    rcases centralizes_or_inverts hZcyc' hZ4 (hMNZ ▸ haM) with h1 | h1
    · exfalso
      refine hnot ⟨haM, mem_centralizer_iff.mpr fun c hc => ?_⟩
      calc c * a = a * c * a⁻¹ * a := by rw [h1 c hc]
        _ = a * c := by group
    · exact h1
  refine ⟨hle, hint, h3a, fun a ha g hg => ?_, fun g hle' t ht htM => ?_, ⟨fun hF00 g hle' => ?_,
    fun hwc => ?_⟩, hF0, h6, fun hF00 hsimple hnonab S hS => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hroot a ha g hg
    exact ⟨h1, h2, h3, fun t ht htM => (h4 t ht htM).2⟩
  · by_cases hZg : CFSG.conjugate ((center Q).map Q.subtype) g = (center Q).map Q.subtype
    · have htQ : t ∈ Q := hZQ (hZg ▸ ht ▸ mem_zpowers t)
      have h1 : ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) = 1 := by
        rw [QuotientGroup.eq_one_iff]
        exact hQmap.mp htQ
      rw [h1, orderOf_one]
      norm_num
    · rw [((hroot _ (h3a g hle' hZg) g rfl).2.2.2 t ht htM).1]
      norm_num
  · by_contra hne
    have := h3a g hle' hne
    rw [hF00] at this
    exact this
  · ext a
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ha
    have ha' := ha
    rw [hF, mem_fusedSet_iff] at ha'
    obtain ⟨⟨g, hg⟩, -, -⟩ := ha'
    exact (hroot a ha g hg).2.1 (hwc g (hroot a ha g hg).1)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hSM : S ≤ M := (CFSG.ABGLocalTools.isSylowOf_iff.mp hS).1
    obtain ⟨-, hS2, hSidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSyl S hS)
    rw [relIndex_top_right] at hSidx
    obtain ⟨⟨a, haS, haz, g, hga⟩, -⟩ := simple_two_central_involution_has_local_conjugate hnonab
      hzord (hS2.toSylow hSidx) (by rw [IsPGroup.toSylow_coe, ← hMC]; exact hSM)
    rw [IsPGroup.toSylow_coe] at haS
    obtain ⟨hnot, -⟩ := h6 hF00 a ⟨⟨⟨g, hga.symm⟩, hSM haS⟩, haz⟩
    have haC : a ∉ centralizer ((center Q).map Q.subtype : Set G) := fun h => hnot ⟨hSM haS, h⟩
    obtain ⟨T, rfl⟩ := hS
    have hQS : Q ≤ T.map M.subtype := by
      rw [hQ]
      exact map_mono (CFSG.pCore_isPGroup.le_sylow_of_normal T)
    have hQC : Q ≤ centralizer ((center Q).map Q.subtype : Set G) := by
      intro q hq
      rw [mem_centralizer_iff]
      rintro c ⟨c', hc', rfl⟩
      exact (congrArg Subtype.val (mem_center_iff.mp hc' ⟨q, hq⟩)).symm
    refine ⟨relIndex_inf_centralizer_eq_two hZcyc' hZ4 (hSM.trans (hMNZ ▸ le_rfl)) haS haC,
      le_inf hQS hQC, fun c hc => ?_, ?_, a, haS, ⟨g, hga.symm⟩, fun h => haC h.2⟩
    · refine ⟨⟨c, le_inf hQS hQC (hZQ hc)⟩, mem_center_iff.mpr fun s => Subtype.ext ?_, rfl⟩
      exact (mem_centralizer_iff.mp s.2.2 c hc).symm
    · ext w
      constructor
      · rintro ⟨hw, hwS⟩
        have : w ∈ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
            ((M ⊓ centralizer ((center Q).map Q.subtype : Set G) : Subgroup G) : Set G) :=
          ⟨hw, hSM hwS.1, hwS.2⟩
        rwa [hF0.mp hF00] at this
      · rintro rfl
        exact ⟨⟨1, by group⟩, hQS hzQ, hQC hzQ⟩

theorem all_cyclic_roots_aux
    {G : Type} [Group G] [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 3 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M)
    {Q : Subgroup G} (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hnex : ¬ IsExtraspecialPGroup 2 Q) (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    ∀ Z : Subgroup G, Z = (center Q).map Q.subtype →
    ∃ z ∈ Z, orderOf z = 2 ∧ (∀ y ∈ Z, orderOf y = 2 → y = z) ∧
      ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
        b.IsAlt ∧ b.Nondegenerate ∧
        ∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
          (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
              (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                  LinearMap.GeneralLinearGroup (ZMod 2)
                    (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
                  (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
                Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
          ∀ F : Set G, F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} →
            (∀ g : G, CFSG.conjugate Z g ≤ M ↔ g⁻¹ * z * g ∈ Q) ∧
            {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) =
              {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) ∧
            (∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g ≠ Z → g⁻¹ * z * g ∈ F) ∧
            (∀ a ∈ F, ∀ g : G, g⁻¹ * z * g = a →
              CFSG.conjugate Z g ≤ M ∧ CFSG.conjugate Z g ≠ Z ∧ CFSG.conjugate Z g ⊓ Q = zpowers a ∧
              ∀ t : G, zpowers t = CFSG.conjugate Z g → ∀ htM : t ∈ M,
                ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Module.finrank (ZMod 2) (LinearMap.range
                  ((((ι ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                    LinearMap.GeneralLinearGroup (ZMod 2)
                      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                    Module.End (ZMod 2)
                      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1)) = m) ∧
            (∀ g : G, CFSG.conjugate Z g ≤ M → ∀ t : G, zpowers t = CFSG.conjugate Z g →
              ∀ htM : t ∈ M, orderOf ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) ≠ 4) ∧
            (F = ∅ ↔ ∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g = Z) ∧
            (F = ∅ ↔ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
              ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = {z}) ∧
            (F = ∅ → ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
              a ∉ M ⊓ centralizer (Z : Set G) ∧ ∀ c ∈ Z, a * c * a⁻¹ = c⁻¹) ∧
            (F = ∅ → IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
              ∀ S : Subgroup G, IsSylowOf 2 S M →
                (S ⊓ centralizer (Z : Set G)).relIndex S = 2 ∧ Q ≤ S ⊓ centralizer (Z : Set G) ∧
                Z ≤ (center ↥(S ⊓ centralizer (Z : Set G))).map
                  (S ⊓ centralizer (Z : Set G)).subtype ∧
                {w | ∃ g : G, g⁻¹ * z * g = w} ∩
                  ((S ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = {z} ∧
                ∃ a ∈ S, (∃ g : G, g⁻¹ * z * g = a) ∧ a ∉ S ⊓ centralizer (Z : Set G)) := by
  obtain ⟨hcharM, hBodd, hZcyc, -, hVel, -, z, hzZ, hzord, huniq, hMC, hMNQ, hMNZ, hSyl, hQ'G,
    hΦ, hZ4, hconj, -⟩ := fused_base_package hchar he hM hsym hB hBM hQ hnex hexp
  obtain ⟨hVel₀, -, b, hrule, -, halt, hnd, ρ, hρ, hker, -, ⟨ι, hιinj, hιρ⟩, -⟩ :=
    core_symplectic_transport hBM hcharM hBodd hQ hZcyc hVel hzZ hzord hQ'G
  have hbk := bk_conjugate_clauses hchar he hM hsym hB hBM hQ hnex hexp hzZ hzord
  have hle := conjugate_le_iff_mem hQ hzZ hzord huniq hMC hMNZ hZcyc hZ4 hQ'G hΦ hρ hker
    (fun g => (hbk g).1) hconj
  intro Z hZ
  subst hZ
  exact ⟨z, hzZ, hzord, huniq, hVel₀, b, hrule, halt, hnd, ι, hιinj, iota_conj_formula hρ hιρ,
    fun F hF => cyclic_root_package hQ hzord huniq hMC hMNQ hMNZ hΦ hQ'G hZ4 hconj hrule ι
      (iota_conj_formula hρ hιρ) hzZ hZcyc hSyl hle hbk rfl hF⟩

end SteinbergCH

open SteinbergCH

theorem gf2_center_four_all_cyclic_root_images_and_weak_closure_obstruction
    {G : Type} [Group G]
    [Finite G] (hchar : IsCharacteristicPType G 2) (he : 3 ≤ CFSG.twoLocalOddRank G)
    {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M) (hsym : GLASymplecticType (pCoreOf 2 M))
    (hB : GLAIsBmax 3 B) (hBM : B ≤ M) {Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) (hnex : ¬ IsExtraspecialPGroup 2 Q)
    (hexp : ∀ x ∈ Q, x ^ 4 = 1) :
    ∀ Z : Subgroup G, Z = (center Q).map Q.subtype →
    ∃ z ∈ Z, orderOf z = 2 ∧ (∀ y ∈ Z, orderOf y = 2 → y = z) ∧
      ∃ (_ : CFSG.IsElementaryAbelian 2 (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
      ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))),
        (∀ x y : CFSG.pCore 2 M, (((⁅x, y⁆ : CFSG.pCore 2 M) : M) : G) =
          z ^ (b (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))
            (Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))).val) ∧
        b.IsAlt ∧ b.Nondegenerate ∧
        ∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
          (∀ (h : M) (x y : CFSG.pCore 2 M), (y : M) = h * x * h⁻¹ →
              (((ι (h : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                  LinearMap.GeneralLinearGroup (ZMod 2)
                    (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                Module.End (ZMod 2) (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))))
                  (Additive.ofMul (x : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) =
                Additive.ofMul (y : CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M))) ∧
          ∀ F : Set G, F = ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G)) \ {z} →
            (∀ g : G, CFSG.conjugate Z g ≤ M ↔ g⁻¹ * z * g ∈ Q) ∧
            {w | ∃ g : G, g⁻¹ * z * g = w} ∩ ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) =
              {w | ∃ g : G, g⁻¹ * z * g = w} ∩ (Q : Set G) ∧
            (∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g ≠ Z → g⁻¹ * z * g ∈ F) ∧
            (∀ a ∈ F, ∀ g : G, g⁻¹ * z * g = a →
              CFSG.conjugate Z g ≤ M ∧ CFSG.conjugate Z g ≠ Z ∧ CFSG.conjugate Z g ⊓ Q = zpowers a ∧
              ∀ t : G, zpowers t = CFSG.conjugate Z g → ∀ htM : t ∈ M,
                ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Module.finrank (ZMod 2) (LinearMap.range
                  ((((ι ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
                    LinearMap.GeneralLinearGroup (ZMod 2)
                      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) :
                    Module.End (ZMod 2)
                      (Additive (CFSG.pCore 2 M ⧸ center (CFSG.pCore 2 M)))) - 1)) = m) ∧
            (∀ g : G, CFSG.conjugate Z g ≤ M → ∀ t : G, zpowers t = CFSG.conjugate Z g →
              ∀ htM : t ∈ M, orderOf ((⟨t, htM⟩ : M) : M ⧸ CFSG.pCore 2 M) ≠ 4) ∧
            (F = ∅ ↔ ∀ g : G, CFSG.conjugate Z g ≤ M → CFSG.conjugate Z g = Z) ∧
            (F = ∅ ↔ {w | ∃ g : G, g⁻¹ * z * g = w} ∩
              ((M ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = {z}) ∧
            (F = ∅ → ∀ a ∈ ({w | ∃ g : G, g⁻¹ * z * g = w} ∩ (M : Set G)) \ {z},
              a ∉ M ⊓ centralizer (Z : Set G) ∧ ∀ c ∈ Z, a * c * a⁻¹ = c⁻¹) ∧
            (F = ∅ → IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
              ∀ S : Subgroup G, IsSylowOf 2 S M →
                (S ⊓ centralizer (Z : Set G)).relIndex S = 2 ∧ Q ≤ S ⊓ centralizer (Z : Set G) ∧
                Z ≤ (center ↥(S ⊓ centralizer (Z : Set G))).map
                  (S ⊓ centralizer (Z : Set G)).subtype ∧
                {w | ∃ g : G, g⁻¹ * z * g = w} ∩
                  ((S ⊓ centralizer (Z : Set G) : Subgroup G) : Set G) = {z} ∧
                ∃ a ∈ S, (∃ g : G, g⁻¹ * z * g = a) ∧ a ∉ S ⊓ centralizer (Z : Set G)) :=
  all_cyclic_roots_aux hchar he hM hsym hB hBM hQ hnex hexp

end CFSG.LocalAnalysis.GorensteinLyons
