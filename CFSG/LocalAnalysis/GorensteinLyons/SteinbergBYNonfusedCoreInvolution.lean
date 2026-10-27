module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLIndexTwoInvolutions

public section

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace NonfusedCore

theorem eq_one_or_eq_of_mem_zpowers_two {a x : G} (ha : orderOf a = 2) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem eq_of_orderOf_eq_two_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  have := Fintype.ofFinite C
  have hd : 2 ∣ Fintype.card C := ha ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient hd
  rw [Nat.totient_two] at h
  exact Finset.card_le_one.mp h.le a (by simp [ha]) b (by simp [hb])

theorem mem_map_center_iff {S : Subgroup G} {x : G} :
    x ∈ (center S).map S.subtype ↔ x ∈ S ∧ ∀ y ∈ S, y * x = x * y := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun w hw => congrArg Subtype.val (mem_center_iff.mp hy ⟨w, hw⟩)⟩
  · rintro ⟨hxS, h⟩
    exact ⟨⟨x, hxS⟩, mem_center_iff.mpr fun w => Subtype.ext (h w w.2), rfl⟩

theorem eq_or_eq_of_relIndex_eq_two {P X Q : Subgroup G} (hPX : P ≤ X) (hXQ : X ≤ Q)
    (h2 : P.relIndex Q = 2) : X = P ∨ X = Q := by
  have h := relIndex_mul_relIndex P X Q hPX hXQ
  rw [h2] at h
  have hdvd : X.relIndex Q ∣ 2 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · right
    exact le_antisymm hXQ (relIndex_eq_one.mp h1)
  · left
    rw [h1] at h
    have h3 : P.relIndex X = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp h3) hPX

theorem mem_conjugate_iff' {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [conjugate, mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rwa [show g * (g⁻¹ * h * g) * g⁻¹ = h by group]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem commutatorElement_mul_left_of_comm {a b t : G} (h1 : ⁅b, t⁆ * a = a * ⁅b, t⁆)
    (h2 : ⁅b, t⁆ * ⁅a, t⁆ = ⁅a, t⁆ * ⁅b, t⁆) : ⁅a * b, t⁆ = ⁅a, t⁆ * ⁅b, t⁆ := by
  have e1 : b * t * b⁻¹ = ⁅b, t⁆ * t := by rw [commutatorElement_def]; group
  calc ⁅a * b, t⁆ = a * (b * t * b⁻¹) * a⁻¹ * t⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅b, t⁆ * a * t * a⁻¹ * t⁻¹ := by rw [e1, ← mul_assoc, ← h1]
    _ = ⁅b, t⁆ * ⁅a, t⁆ := by rw [commutatorElement_def]; group
    _ = ⁅a, t⁆ * ⁅b, t⁆ := h2

theorem eq_of_mem_center_of_orderOf_eq_two {Q : Subgroup G} [Finite Q] (hZ : IsCyclic (center Q))
    {z c : G} (hzQ : z ∈ Q) (hzc : ∀ y ∈ Q, y * z = z * y) (hz : orderOf z = 2) (hcQ : c ∈ Q)
    (hc : ∀ y ∈ Q, y * c = c * y) (hc2 : orderOf c = 2) : c = z := by
  have hcZ : (⟨c, hcQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  have hzZ : (⟨z, hzQ⟩ : Q) ∈ center Q := mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)
  have h := eq_of_orderOf_eq_two_of_isCyclic (C := center Q) (a := ⟨⟨c, hcQ⟩, hcZ⟩)
    (b := ⟨⟨z, hzQ⟩, hzZ⟩) (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hc2)
    (by rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]; exact hz)
  exact congrArg (fun w : center Q => ((w : Q) : G)) h

theorem mem_of_mem_centralizer_of_relIndex_eq_two [Finite G] {z : G} (hz : orderOf z = 2)
    {M : Subgroup G} (hM : M = centralizer ({z} : Set G)) (hchar : IsCharacteristicP 2 M)
    (hΦ : (frattini (CFSG.inSubgroup (CFSG.pCore 2) M)).map
      (CFSG.inSubgroup (CFSG.pCore 2) M).subtype = zpowers z)
    (hZ : IsCyclic (center (CFSG.inSubgroup (CFSG.pCore 2) M))) {L : Subgroup G}
    (hLQ : L ≤ CFSG.inSubgroup (CFSG.pCore 2) M)
    (hL2 : L.relIndex (CFSG.inSubgroup (CFSG.pCore 2) M) = 2) {x : G}
    (hx : x ∈ centralizer (L : Set G)) (hx2 : orderOf x = 2) : x ∈ L := by
  classical
  set Q := CFSG.inSubgroup (CFSG.pCore 2) M with hQ
  have hQM : Q ≤ M := map_subtype_le _
  have hcentM : ∀ y ∈ M, z * y = y * z := fun y hy => by
    rw [hM] at hy
    exact mem_centralizer_iff.mp hy z (Set.mem_singleton z)
  have hzmem : z ∈ (frattini Q).map Q.subtype := hΦ ▸ mem_zpowers z
  obtain ⟨z', hz'Φ, hz'z⟩ := hzmem
  have hzL : z ∈ L := by
    have hidx : (L.subgroupOf Q).index = 2 := hL2
    have hcoatom : IsCoatom (L.subgroupOf Q) :=
      isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_two)
    have h1 := frattini_le_coatom hcoatom hz'Φ
    rw [mem_subgroupOf] at h1
    rwa [← hz'z]
  have hxM : x ∈ M := by
    rw [hM, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact mem_centralizer_iff.mp hx z hzL
  let e : ↥(CFSG.pCore 2 M) ≃* ↥Q :=
    (CFSG.pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective
  have hzQ : z ∈ Q := hz'z ▸ z'.2
  have hZ' : ∀ w ∈ center (CFSG.pCore 2 M), orderOf w = 2 → w ∈ frattini (CFSG.pCore 2 M) := by
    intro w hw hw2
    have hew : e w ∈ center Q := mem_center_iff.mpr fun g => by
      have h1 := mem_center_iff.mp hw (e.symm g)
      calc g * e w = e (e.symm g * w) := by rw [map_mul, MulEquiv.apply_symm_apply]
        _ = e (w * e.symm g) := by rw [h1]
        _ = e w * g := by rw [map_mul, MulEquiv.apply_symm_apply]
    have hew2 : orderOf ((e w : Q) : G) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hw2]
    have hewz : ((e w : Q) : G) = z :=
      eq_of_mem_center_of_orderOf_eq_two hZ hzQ (fun y hy => (hcentM y (hQM hy)).symm) hz
        (e w).2 (fun y hy => congrArg Subtype.val (mem_center_iff.mp hew ⟨y, hy⟩)) hew2
    have hewz' : e w = z' := Subtype.ext (hewz.trans hz'z.symm)
    have h1 := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hz'Φ
    rw [mem_comap, MulEquiv.coe_toMonoidHom, ← hewz', MulEquiv.symm_apply_apply] at h1
    exact h1
  have hLM : L ≤ M := hLQ.trans hQM
  have hPQ : L.subgroupOf M ≤ CFSG.pCore 2 M := by
    intro y hy
    obtain ⟨y', hy', hy'y⟩ := hLQ (mem_subgroupOf.mp hy)
    rwa [show y' = y from Subtype.ext hy'y] at hy'
  have hP2 : (L.subgroupOf M).relIndex (CFSG.pCore 2 M) = 2 := by
    have h1 := relIndex_subgroupOf (H := L) hQM
    have h2 : Q.subgroupOf M = CFSG.pCore 2 M :=
      comap_map_eq_self_of_injective M.subtype_injective _
    rw [h2] at h1
    rw [h1, hL2]
  have hxC : (⟨x, hxM⟩ : M) ∈ centralizer ((L.subgroupOf M : Subgroup M) : Set M) := by
    rw [mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (mem_centralizer_iff.mp hx (h : G) (mem_subgroupOf.mp hh))
  have hx2' : orderOf (⟨x, hxM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have key := index_two_core_centralizers_no_new_involutions hchar hZ' hPQ hP2 hxC hx2'
  exact mem_subgroupOf.mp key

end NonfusedCore

open NonfusedCore

theorem nonfused_core_involution_global_centralizer_control [Finite G] {z : G}
    (hz : orderOf z = 2) {M Q : Subgroup G} (hM : M = centralizer ({z} : Set G))
    (hchar : IsCharacteristicP 2 M) (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M)
    (hΦ : (frattini Q).map Q.subtype = zpowers z) (hQ' : ⁅Q, Q⁆ = zpowers z)
    (hZ : IsCyclic (center Q)) (_hSyl : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M) :
    (∀ L : Subgroup G, L ≤ Q → L.relIndex Q = 2 → ∀ x ∈ centralizer (L : Set G),
      orderOf x = 2 → x ∈ L) ∧
    ∀ t ∈ Q, t ∉ (center Q).map Q.subtype → orderOf t = 2 →
      (Q ⊓ centralizer ({t} : Set G)).relIndex Q = 2 ∧
      (center ↥(Q ⊓ centralizer ({t} : Set G))).map (Q ⊓ centralizer ({t} : Set G)).subtype =
        (center Q).map Q.subtype ⊔ zpowers t ∧
      (∃ q ∈ Q, q * t * q⁻¹ = t * z) ∧
      ((∃ g : G, g⁻¹ * z * g = t) ↔
        ∃ g : G, g ∉ M ∧ Q ⊓ centralizer ({t} : Set G) ≤ conjugate M g) ∧
      ((¬ ∃ g : G, g⁻¹ * z * g = t) →
        {w | ∃ g : G, g⁻¹ * z * g = w} ∩
            (centralizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) : Set G) =
          {z} ∧
        normalizer ((Q ⊓ centralizer ({t} : Set G) : Subgroup G) : Set G) ≤ M ∧
        (∀ T : Sylow 2 (centralizer ({t} : Set G)),
          Q ⊓ centralizer ({t} : Set G) ≤
            (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
          z ∈ (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ⊓
            centralizer (((T : Subgroup (centralizer ({t} : Set G))).map
              (centralizer ({t} : Set G)).subtype : Subgroup G) : Set G)) ∧
        (IsCharacteristicP 2 (centralizer ({t} : Set G)) →
          z ∈ CFSG.inSubgroup (CFSG.pCore 2) (centralizer ({t} : Set G)))) := by
  classical
  have := Fact.mk Nat.prime_two
  subst hQ
  set Q := CFSG.inSubgroup (CFSG.pCore 2) M with hQ
  have hQM : Q ≤ M := map_subtype_le _
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map M.subtype
  have hcentM : ∀ y ∈ M, z * y = y * z := fun y hy => by
    rw [hM] at hy
    exact mem_centralizer_iff.mp hy z (Set.mem_singleton z)
  have hmemM : ∀ y : G, z * y = y * z → y ∈ M := fun y hy => by
    rw [hM, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hy
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z := fun a ha b hb =>
    hQ' ▸ commutator_mem_commutator ha hb
  have hzQ : z ∈ Q := Subgroup.commutator_le_self Q (hQ' ▸ mem_zpowers z)
  have hzZ : ∀ y ∈ Q, y * z = z * y := fun y hy => (hcentM y (hQM hy)).symm
  have hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ = 1 ∨ ⁅a, b⁆ = z := fun a ha b hb =>
    eq_one_or_eq_of_mem_zpowers_two hz (hcommQ a ha b hb)
  have hcommc : ∀ a ∈ Q, ∀ b ∈ Q, ∀ x ∈ M, ⁅a, b⁆ * x = x * ⁅a, b⁆ := by
    intro a ha b hb x hx
    rcases hcomm a ha b hb with h | h <;> rw [h]
    · rw [one_mul, mul_one]
    · exact hcentM x hx
  have hcommQ' : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Q := fun a ha b hb =>
    Subgroup.commutator_le_self Q (commutator_mem_commutator ha hb)
  have hA : ∀ L : Subgroup G, L ≤ Q → L.relIndex Q = 2 → ∀ x ∈ centralizer (L : Set G),
      orderOf x = 2 → x ∈ L := fun L hLQ hL2 x hx hx2 =>
    mem_of_mem_centralizer_of_relIndex_eq_two hz hM hchar hΦ hZ hLQ hL2 hx hx2
  refine ⟨hA, fun t htQ htZ ht2 => ?_⟩
  set P := Q ⊓ centralizer ({t} : Set G) with hP
  have htM : t ∈ M := hQM htQ
  have hmemP : ∀ q, q ∈ P ↔ q ∈ Q ∧ q * t = t * q := fun q => by
    rw [hP, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨hq, h⟩
      exact ⟨hq, (h t (Set.mem_singleton t)).symm⟩
    · rintro ⟨hq, h⟩
      refine ⟨hq, fun x hx => ?_⟩
      rw [Set.mem_singleton_iff.mp hx]
      exact h.symm
  have hPQ : P ≤ Q := inf_le_left
  have hzP : z ∈ P := (hmemP z).mpr ⟨hzQ, hcentM t htM⟩
  have htP : t ∈ P := (hmemP t).mpr ⟨htQ, rfl⟩
  obtain ⟨q₀, hq₀Q, hq₀t⟩ : ∃ q₀ ∈ Q, q₀ * t ≠ t * q₀ := by
    by_contra hcon
    push Not at hcon
    exact htZ (mem_map_center_iff.mpr ⟨htQ, fun y hy => hcon y hy⟩)
  have hq₀z : ⁅q₀, t⁆ = z := (hcomm q₀ hq₀Q t htQ).resolve_left fun h =>
    hq₀t (commutatorElement_eq_one_iff_mul_comm.mp h)
  let f : Q →* G :=
    { toFun := fun q => ⁅(q : G), t⁆
      map_one' := by simp
      map_mul' := fun a b => commutatorElement_mul_left_of_comm
        (hcommc b b.2 t htQ a (hQM a.2)) (hcommc b b.2 t htQ _ (hQM (hcommQ' a a.2 t htQ))) }
  have hker : f.ker = P.subgroupOf Q := by
    ext q
    rw [MonoidHom.mem_ker, mem_subgroupOf, hmemP]
    exact ⟨fun h => ⟨q.2, commutatorElement_eq_one_iff_mul_comm.mp h⟩,
      fun h => commutatorElement_eq_one_iff_mul_comm.mpr h.2⟩
  have hrange : f.range = zpowers z := by
    apply le_antisymm
    · rintro _ ⟨q, rfl⟩
      exact hcommQ q q.2 t htQ
    · rw [zpowers_le]
      exact ⟨⟨q₀, hq₀Q⟩, hq₀z⟩
  have hPidx : P.relIndex Q = 2 := by
    change (P.subgroupOf Q).index = 2
    rw [← hker, Subgroup.index_ker, hrange, Nat.card_zpowers, hz]
  have hZP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) →
      (x ∈ Q ∧ ∀ y ∈ Q, y * x = x * y) ∨
        (x * t⁻¹ ∈ Q ∧ ∀ y ∈ Q, y * (x * t⁻¹) = x * t⁻¹ * y) := by
    intro x hxP hx
    by_cases hxQ : ∀ y ∈ Q, y * x = x * y
    · exact Or.inl ⟨hPQ hxP, hxQ⟩
    right
    push Not at hxQ
    obtain ⟨q₁, hq₁Q, hq₁⟩ := hxQ
    set Cx := Q ⊓ centralizer ({x} : Set G) with hCx
    have hmemCx : ∀ y, y ∈ Cx ↔ y ∈ Q ∧ y * x = x * y := fun y => by
      rw [hCx, mem_inf, mem_centralizer_iff]
      constructor
      · rintro ⟨hy, h⟩
        exact ⟨hy, (h x (Set.mem_singleton x)).symm⟩
      · rintro ⟨hy, h⟩
        refine ⟨hy, fun w hw => ?_⟩
        rw [Set.mem_singleton_iff.mp hw]
        exact h.symm
    have hPCx : P ≤ Cx := fun y hy => (hmemCx y).mpr ⟨hPQ hy, hx y hy⟩
    have hCxP : Cx = P := by
      rcases eq_or_eq_of_relIndex_eq_two hPCx inf_le_left hPidx with h | h
      · exact h
      · exfalso
        have h1 : q₁ ∈ Cx := h ▸ hq₁Q
        exact hq₁ ((hmemCx q₁).mp h1).2
    have heq : ∀ y ∈ Q, ⁅y, x⁆ = ⁅y, t⁆ := by
      intro y hyQ
      by_cases hyP : y ∈ P
      · rw [commutatorElement_eq_one_iff_mul_comm.mpr (hx y hyP),
          commutatorElement_eq_one_iff_mul_comm.mpr ((hmemP y).mp hyP).2]
      · have h1 : ⁅y, x⁆ ≠ 1 := fun h => hyP (hCxP ▸ (hmemCx y).mpr
          ⟨hyQ, commutatorElement_eq_one_iff_mul_comm.mp h⟩)
        have h2 : ⁅y, t⁆ ≠ 1 := fun h => hyP ((hmemP y).mpr
          ⟨hyQ, commutatorElement_eq_one_iff_mul_comm.mp h⟩)
        rw [(hcomm y hyQ x (hPQ hxP)).resolve_left h1, (hcomm y hyQ t htQ).resolve_left h2]
    refine ⟨mul_mem (hPQ hxP) (inv_mem htQ), fun y hyQ => ?_⟩
    have e1 : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
    have e2 : y * t * y⁻¹ = ⁅y, t⁆ * t := by rw [commutatorElement_def]; group
    have hc := hcommc y hyQ t htQ (x * t⁻¹) (hQM (mul_mem (hPQ hxP) (inv_mem htQ)))
    calc y * (x * t⁻¹) = y * x * y⁻¹ * (y * t * y⁻¹)⁻¹ * y := by group
      _ = ⁅y, t⁆ * (x * t⁻¹) * ⁅y, t⁆⁻¹ * y := by rw [e1, e2, heq y hyQ]; group
      _ = x * t⁻¹ * ⁅y, t⁆ * ⁅y, t⁆⁻¹ * y := by rw [hc]
      _ = x * t⁻¹ * y := by group
  have hZPeq : (center P).map P.subtype = (center Q).map Q.subtype ⊔ zpowers t := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxc⟩ := mem_map_center_iff.mp hx
      rcases hZP x hxP hxc with ⟨hxQ, hxQc⟩ | ⟨hxtQ, hxtc⟩
      · exact mem_sup_left (mem_map_center_iff.mpr ⟨hxQ, hxQc⟩)
      · have e : x = x * t⁻¹ * t := by group
        rw [e]
        exact mul_mem (mem_sup_left (mem_map_center_iff.mpr ⟨hxtQ, hxtc⟩))
          (mem_sup_right (mem_zpowers t))
    · refine sup_le (fun x hx => ?_) ((zpowers_le).mpr ?_)
      · obtain ⟨hxQ, hxc⟩ := mem_map_center_iff.mp hx
        exact mem_map_center_iff.mpr ⟨(hmemP x).mpr ⟨hxQ, (hxc t htQ).symm⟩,
          fun y hy => hxc y (hPQ hy)⟩
      · exact mem_map_center_iff.mpr ⟨htP, fun y hy => ((hmemP y).mp hy).2⟩
  have hconj : q₀ * t * q₀⁻¹ = t * z := by
    have e : q₀ * t * q₀⁻¹ = ⁅q₀, t⁆ * t := by rw [commutatorElement_def]; group
    rw [e, hq₀z]
    exact hcentM t htM
  have hzt : ∀ g : G, g⁻¹ * z * g = t * z → ∃ g' : G, g'⁻¹ * z * g' = t := by
    intro g hg
    refine ⟨g * q₀, ?_⟩
    calc (g * q₀)⁻¹ * z * (g * q₀) = q₀⁻¹ * (g⁻¹ * z * g) * q₀ := by group
      _ = q₀⁻¹ * (q₀ * t * q₀⁻¹) * q₀ := by rw [hg, hconj]
      _ = t := by group
  have hfuse : ∀ w ∈ centralizer (P : Set G), orderOf w = 2 → w = z ∨ w = t ∨ w = t * z := by
    intro w hwC hw2
    have hwP : w ∈ P := hA P hPQ hPidx w hwC hw2
    have hwc : ∀ y ∈ P, y * w = w * y := fun y hy => mem_centralizer_iff.mp hwC y hy
    rcases hZP w hwP hwc with ⟨hwQ, hwQc⟩ | ⟨hwtQ, hwtc⟩
    · exact Or.inl (eq_of_mem_center_of_orderOf_eq_two hZ hzQ hzZ hz hwQ hwQc hw2)
    · right
      have hwt : w * t = t * w := (hwc t htP).symm
      have hw1 : w * w = 1 := by rw [← pow_two, ← hw2, pow_orderOf_eq_one]
      have ht1 : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
      have hc2 : (w * t⁻¹) ^ 2 = 1 := by
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht1
        rw [pow_two, htinv]
        calc w * t * (w * t) = w * (t * w) * t := by group
          _ = w * (w * t) * t := by rw [hwt]
          _ = (w * w) * (t * t) := by group
          _ = 1 := by rw [hw1, ht1, one_mul]
      have hdvd : orderOf (w * t⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · left
        rw [orderOf_eq_one_iff, mul_inv_eq_one] at h1
        exact h1
      · right
        have h3 := eq_of_mem_center_of_orderOf_eq_two hZ hzQ hzZ hz hwtQ hwtc h1
        rw [← hcentM t htM, ← h3]
        group
  have hconjord : ∀ g : G, orderOf (g⁻¹ * z * g) = 2 := fun g => by
    have h := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) z
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, hz]
  have hconjC : ∀ g : G, (∀ y ∈ P, g * y * g⁻¹ ∈ M) → g⁻¹ * z * g ∈ centralizer (P : Set G) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro y hy
    have h2 := hcentM _ (hg y hy)
    calc y * (g⁻¹ * z * g) = g⁻¹ * ((g * y * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * y * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * z * g * y := by group
  have hzM_of : ∀ g : G, g⁻¹ * z * g = z → g ∈ M := fun g hg => hmemM g (by
    calc z * g = g * (g⁻¹ * z * g) := by group
      _ = g * z := by rw [hg])
  refine ⟨hPidx, hZPeq, ⟨q₀, hq₀Q, hconj⟩, ⟨?_, ?_⟩, fun hnot => ?_⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, fun hgM => ?_, fun y hy => ?_⟩
    · have h1 : g⁻¹ * z * g = z := by rw [mul_assoc, hcentM g hgM, inv_mul_cancel_left]
      rw [h1] at hg
      exact htZ (hg ▸ mem_map_center_iff.mpr ⟨hzQ, hzZ⟩)
    · rw [mem_conjugate_iff']
      apply hmemM
      have hyt : y * t = t * y := ((hmemP y).mp hy).2
      rw [← hg] at hyt
      calc z * (g * y * g⁻¹) = g * ((g⁻¹ * z * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * z * g)) * g⁻¹ := by rw [hyt]
        _ = g * y * g⁻¹ * z := by group
  · rintro ⟨g, hgM, hPg⟩
    have hwC := hconjC g fun y hy => mem_conjugate_iff'.mp (hPg hy)
    rcases hfuse _ hwC (hconjord g) with h | h | h
    · exact absurd (hzM_of g h) hgM
    · exact ⟨g, h⟩
    · exact hzt g h
  have hfix : ∀ g : G, g⁻¹ * z * g ∈ centralizer (P : Set G) → g⁻¹ * z * g = z := by
    intro g hg
    rcases hfuse _ hg (hconjord g) with h | h | h
    · exact h
    · exact absurd ⟨g, h⟩ hnot
    · exact absurd (hzt g h) hnot
  have hzC : z ∈ centralizer (P : Set G) :=
    mem_centralizer_iff.mpr fun y hy => (hcentM y (hQM (hPQ hy))).symm
  have hTM : ∀ T : Sylow 2 (centralizer ({t} : Set G)),
      P ≤ (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype →
      (T : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype ≤ M := by
    intro T hPT
    set T' := (T : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype with hT'
    have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
    by_contra hcon
    set N := T' ⊓ M with hN
    have hlt : N.subgroupOf T' < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun h => hcon fun x hx => ?_
      have h1 : (⟨x, hx⟩ : T') ∈ N.subgroupOf T' := h ▸ mem_top _
      exact (mem_inf.mp (mem_subgroupOf.mp h1)).2
    have : Group.IsNilpotent T' := hT'2.isNilpotent
    have hnc := Group.normalizerCondition_of_isNilpotent (G := T') _ hlt
    obtain ⟨x, hxN, hxN'⟩ := IsConcreteLE.exists_of_lt hnc
    have hxM : (x : G) ∉ M := fun h => hxN' (mem_subgroupOf.mpr (mem_inf.mpr ⟨x.2, h⟩))
    have hw : ((x : G)⁻¹)⁻¹ * z * (x : G)⁻¹ ∈ centralizer (P : Set G) := by
      refine hconjC _ fun y hy => ?_
      have hyN : (⟨y, hPT hy⟩ : T') ∈ N.subgroupOf T' :=
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hPT hy, hQM (hPQ hy)⟩)
      have h1 : x⁻¹ * ⟨y, hPT hy⟩ * x ∈ N.subgroupOf T' := by
        have h2 := (mem_normalizer_iff.mp hxN (x⁻¹ * ⟨y, hPT hy⟩ * x)).mpr
        apply h2
        rwa [show x * (x⁻¹ * ⟨y, hPT hy⟩ * x) * x⁻¹ = ⟨y, hPT hy⟩ by group]
      have h3 : (x : G)⁻¹ * y * (x : G) ∈ M := (mem_inf.mp (mem_subgroupOf.mp h1)).2
      rwa [inv_inv]
    have h4 : ((x : G)⁻¹)⁻¹ * z * (x : G)⁻¹ = z := hfix _ hw
    have h5 : (x : G)⁻¹ ∈ M := hzM_of _ h4
    exact hxM (by simpa using inv_mem h5)
  refine ⟨?_, fun n hn => ?_, fun T hPT => ?_, fun hcharX => ?_⟩
  · ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨g, rfl⟩, hw⟩
      exact hfix g hw
    · rintro rfl
      exact ⟨⟨1, by group⟩, hzC⟩
  ·
    have hw : (n⁻¹)⁻¹ * z * n⁻¹ ∈ centralizer (P : Set G) := by
      refine hconjC _ fun y hy => ?_
      have h1 : n⁻¹ * y * n⁻¹⁻¹ ∈ P := by
        have h2 := (mem_normalizer_iff.mp hn (n⁻¹ * y * n⁻¹⁻¹)).mpr
        apply h2
        rwa [show n * (n⁻¹ * y * n⁻¹⁻¹) * n⁻¹ = y by group]
      exact hQM (hPQ h1)
    have h1 := hfix _ hw
    have h2 : n⁻¹ ∈ M := hzM_of _ h1
    simpa using inv_mem h2
  ·
    have h1 := hTM T hPT
    exact mem_inf.mpr ⟨hPT hzP, mem_centralizer_iff.mpr fun y hy => (hcentM y (h1 hy)).symm⟩
  ·
    set X := centralizer ({t} : Set G) with hX
    have hPX : P ≤ X := inf_le_right
    have hP2 : IsPGroup 2 (P.subgroupOf X) :=
      (hQ2.to_le hPQ).comap_of_injective X.subtype X.subtype_injective
    obtain ⟨T, hT⟩ := hP2.exists_le_sylow
    have hPT : P ≤ (T : Subgroup X).map X.subtype := fun y hy =>
      ⟨⟨y, hPX hy⟩, hT (mem_subgroupOf.mpr hy), rfl⟩
    have h1 := hTM T hPT
    have hOT : CFSG.inSubgroup (CFSG.pCore 2) X ≤ (T : Subgroup X).map X.subtype :=
      map_mono (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup T)
    have hzX : z ∈ X := by
      rw [hX, mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact (hcentM t htM).symm
    have hzc : (⟨z, hzX⟩ : X) ∈ centralizer (CFSG.pCore 2 X : Set X) := by
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (hcentM _ (h1 (hOT ⟨y, hy, rfl⟩))).symm
    exact ⟨⟨z, hzX⟩, hcharX hzc, rfl⟩

end CFSG.LocalAnalysis.GorensteinLyons
