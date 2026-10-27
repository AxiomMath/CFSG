module

public import CFSG.GH74.QTGen4.Recog.Ku.CloseCentC
public import CFSG.GH74.QTGen4.Recog.Ku.CloseAlt
public import CFSG.Quasithin.Recognition.HSType129e

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Quasithin.HSType

variable {G : Type} [Group G]

section Quot

theorem card_cenX {x : G} (hx : orderOf x = 3) : Nat.card (cenX x) = 3 := by
  have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hx]

theorem card_centralizer_eq_three_mul [Finite G] {x : G} (hx : orderOf x = 3) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = 3 * Nat.card (cenQuot x) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (cenX x), card_cenX hx, mul_comm]

theorem exists_invol_lift {x : G} (hx : orderOf x = 3) {i : cenQuot x} (hi : orderOf i = 2) :
    ∃ c : ↥(Subgroup.centralizer ({x} : Set G)), (c : G) * c = 1 ∧ c ≠ 1 ∧
      (QuotientGroup.mk c : cenQuot x) = i := by
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective i
  have hi2 : (QuotientGroup.mk c0 : cenQuot x) ^ 2 = 1 := by
    have := pow_orderOf_eq_one (QuotientGroup.mk c0 : cenQuot x)
    rwa [hi] at this
  have hc2 : ((c0 ^ 2 : ↥(Subgroup.centralizer ({x} : Set G))) : G) ∈ Subgroup.zpowers x := by
    rw [← cenQuot_mk_eq_one_iff, QuotientGroup.mk_pow]
    exact hi2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc2
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hmk : (QuotientGroup.mk (c0 ^ 3) : cenQuot x) = QuotientGroup.mk c0 := by
    rw [QuotientGroup.mk_pow, pow_succ, hi2, one_mul]
  refine ⟨c0 ^ 3, ?_, ?_, hmk⟩
  · have h1 : ((c0 ^ 3 : ↥(Subgroup.centralizer ({x} : Set G))) : G) *
        ((c0 ^ 3 : ↥(Subgroup.centralizer ({x} : Set G))) : G) = (x ^ k) ^ 3 := by
      rw [hk]
      simp only [Subgroup.coe_pow]
      group
    rw [h1, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  · intro h
    rw [h, QuotientGroup.mk_one] at hmk
    rw [← hmk] at hi
    simp at hi

theorem nonempty_mulEquiv_dihedral_two {K : Type*} [Group K] (hcard : Nat.card K = 4)
    (h2 : ∀ a : K, a * a = 1) : Nonempty (K ≃* DihedralGroup 2) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hexp : Monoid.exponent K = 2 := by
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2 g)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg
    · exact h
  have : IsKleinFour K := ⟨hcard, hexp⟩
  exact IsKleinFour.nonempty_mulEquiv

theorem card_centralizer_conj {H : Type*} [Group H] (a b : H) :
    Nat.card ↥(Subgroup.centralizer ({a * b * a⁻¹} : Set H)) =
      Nat.card ↥(Subgroup.centralizer ({b} : Set H)) := by
  refine Nat.card_congr
    { toFun := fun y => ⟨a⁻¹ * y * a, ?_⟩
      invFun := fun y => ⟨a * y * a⁻¹, ?_⟩
      left_inv := fun y => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }
  · have h := Subgroup.mem_centralizer_singleton_iff.mp y.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc a⁻¹ * (y : H) * a * b = a⁻¹ * ((y : H) * (a * b * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * b * a⁻¹) * (y : H)) * a := by rw [h]
      _ = b * (a⁻¹ * (y : H) * a) := by group
  · have h := Subgroup.mem_centralizer_singleton_iff.mp y.2
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc a * (y : H) * a⁻¹ * (a * b * a⁻¹) = a * ((y : H) * b) * a⁻¹ := by group
      _ = a * (b * (y : H)) * a⁻¹ := by rw [h]
      _ = (a * b * a⁻¹) * (a * (y : H) * a⁻¹) := by group

end Quot

theorem kuDelta_le_centralizer {E : Subgroup G} (x : G) :
    kuDelta E x ≤ Subgroup.centralizer ({x} : Set G) :=
  inf_le_right

namespace KuA6Model

variable [Finite G] {E W V2 N : Subgroup G} {z : G} (Ψ : KuA6Model E W V2 N z)
include Ψ

theorem exists_sylow_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    ∃ S : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G)),
      (S : Subgroup ↥(Subgroup.centralizer ({x} : Set G))) =
        (kuDelta E x).subgroupOf (Subgroup.centralizer ({x} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hD'2 : IsPGroup 2 ↥((kuDelta E x).subgroupOf C) := by
    intro g
    refine ⟨1, ?_⟩
    have h1 : ((g : ↥C) : G) * ((g : ↥C) : G) = 1 :=
      Ψ.E_mul_self _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp g.2)).1
    apply Subtype.ext
    apply Subtype.ext
    simpa [pow_two] using h1
  obtain ⟨Q, hQ⟩ := hD'2.exists_le_sylow
  refine ⟨Q, ?_⟩
  have hS2 : IsPGroup 2 ↥((Q : Subgroup ↥C).map C.subtype) := Q.isPGroup'.map _
  have hΔS : kuDelta E x ≤ (Q : Subgroup ↥C).map C.subtype := by
    intro d hd
    exact ⟨⟨d, kuDelta_le_centralizer x hd⟩, hQ (Subgroup.mem_subgroupOf.mpr hd), rfl⟩
  have hS := Ψ.delta_sylow hHN hxH hx (Subgroup.map_subtype_le _) hS2 hΔS
  apply le_antisymm
  · intro g hg
    have : (g : G) ∈ (Q : Subgroup ↥C).map C.subtype := ⟨g, hg, rfl⟩
    rw [hS] at this
    exact Subgroup.mem_subgroupOf.mpr this
  · exact hQ

theorem exists_conj_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3)
    {c : ↥(Subgroup.centralizer ({x} : Set G))} (hc : (c : G) * c = 1) (hc1 : c ≠ 1) :
    ∃ (g : ↥(Subgroup.centralizer ({x} : Set G))) (i : G) (hi : i ∈ kuDelta E x),
      i ≠ 1 ∧ g * c * g⁻¹ = ⟨i, kuDelta_le_centralizer (E := E) x hi⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := Ψ.exists_sylow_delta hHN hxH hx
  have hc1' : (c : G) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hco : orderOf c = 2 := by
    have hd : orderOf c ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by
        apply Subtype.ext
        simpa [pow_two] using hc)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hc1
    · exact h
  have hc2 : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hco]
    exact ⟨1, by norm_num⟩
  obtain ⟨Q, hQ⟩ := hc2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(Subgroup.centralizer ({x} : Set G)) Q S
  have hmem : g * c * g⁻¹ ∈ (S : Subgroup ↥(Subgroup.centralizer ({x} : Set G))) := by
    rw [← hg]
    show g * c * g⁻¹ ∈ ((g • Q : Sylow 2 ↥(Subgroup.centralizer ({x} : Set G))) :
      Set ↥(Subgroup.centralizer ({x} : Set G)))
    rw [Sylow.coe_smul]
    exact Set.smul_mem_smul_set (hQ (Subgroup.mem_zpowers c))
  rw [hS] at hmem
  have hmem' := Subgroup.mem_subgroupOf.mp hmem
  refine ⟨g, ((g * c * g⁻¹ : ↥(Subgroup.centralizer ({x} : Set G))) : G), hmem', ?_, Subtype.ext rfl⟩
  intro h
  apply hc1
  have h1 : g * c * g⁻¹ = 1 := Subtype.ext h
  calc c = g⁻¹ * (g * c * g⁻¹) * g := by group
    _ = 1 := by rw [h1]; group

theorem exists_klein_sylow_cenQuot (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    ∃ D : Sylow 2 (cenQuot x), Nonempty ((D : Subgroup (cenQuot x)) ≃* DihedralGroup 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  obtain ⟨S, hS⟩ := Ψ.exists_sylow_delta hHN hxH hx
  set q : ↥C →* cenQuot x := QuotientGroup.mk' (cenX x) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  refine ⟨S.mapSurjective hqs, ?_⟩
  have hD : ((S.mapSurjective hqs : Sylow 2 (cenQuot x)) : Subgroup (cenQuot x)) =
      ((kuDelta E x).subgroupOf C).map q := by
    rw [Sylow.coe_mapSurjective, hS]
  rw [hD]
  have hsq : ∀ d : ↥((kuDelta E x).subgroupOf C), ((d : ↥C) : G) * ((d : ↥C) : G) = 1 := fun d =>
    Ψ.E_mul_self _ (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp d.2)).1
  have hinj : Function.Injective (q.comp ((kuDelta E x).subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hd' : (QuotientGroup.mk (d : ↥C) : cenQuot x) = 1 := hd
    rw [cenQuot_mk_eq_one_iff] at hd'
    have h3 : ((d : ↥C) : G) ^ 3 = 1 := by
      have := orderOf_dvd_of_mem_zpowers hd'
      rw [hx] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h1 : ((d : ↥C) : G) = 1 := by
      calc ((d : ↥C) : G) = ((d : ↥C) : G) ^ 3 := by
            rw [pow_succ, pow_two, hsq d, one_mul]
        _ = 1 := h3
    exact Subtype.ext (Subtype.ext h1)
  refine nonempty_mulEquiv_dihedral_two ?_ ?_
  · have hr : (q.comp ((kuDelta E x).subgroupOf C).subtype).range =
        ((kuDelta E x).subgroupOf C).map q := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr]
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (kuDelta_le_centralizer (E := E) x)).toEquiv,
      Ψ.card_delta hHN hxH hx]
  · rintro ⟨a, d, hd, rfl⟩
    apply Subtype.ext
    show q d * q d = 1
    rw [← map_mul]
    have : d * d = 1 := Subtype.ext (hsq ⟨d, hd⟩)
    rw [this, map_one]

theorem card_centralizer_mk_delta (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) {i : G}
    (hi : i ∈ kuDelta E x) (hi1 : i ≠ 1) :
    Nat.card ↥(Subgroup.centralizer
      ({(QuotientGroup.mk (⟨i, kuDelta_le_centralizer (E := E) x hi⟩ :
        ↥(Subgroup.centralizer ({x} : Set G))) : cenQuot x)} : Set (cenQuot x))) = 4 := by
  classical
  set C := Subgroup.centralizer ({x} : Set G) with hC
  set i' : ↥C := ⟨i, kuDelta_le_centralizer (E := E) x hi⟩ with hi'
  set q : ↥C →* cenQuot x := QuotientGroup.mk' (cenX x) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hii : i * i = 1 := Ψ.E_mul_self i (Subgroup.mem_inf.mp hi).1
  have hi'i : (i' : G) * i' = 1 := hii
  set Z : Subgroup ↥C := (Subgroup.centralizer ({q i'} : Set (cenQuot x))).comap q with hZ
  have hZeq : Z = Subgroup.centralizer ({i'} : Set ↥C) := by
    ext c
    constructor
    · intro hc
      have hc' : q c * q i' = q i' * q c := Subgroup.mem_centralizer_singleton_iff.mp hc
      have ha : ((c * i' * c⁻¹ : ↥C) : G) * ((c * i' * c⁻¹ : ↥C) : G) = 1 := by
        have : ((c * i' * c⁻¹ : ↥C) : G) * ((c * i' * c⁻¹ : ↥C) : G) =
            (c : G) * ((i' : G) * i') * (c : G)⁻¹ := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [this, hi'i]
        group
      have hab : (QuotientGroup.mk (c * i' * c⁻¹) : cenQuot x) = QuotientGroup.mk i' := by
        show q (c * i' * c⁻¹) = q i'
        rw [map_mul, map_mul, map_inv, hc']
        group
      have heq := eq_of_mk_eq_of_mul_self hx ha hi'i hab
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc c * i' = c * i' * c⁻¹ * c := by group
        _ = i' * c := by rw [heq]
    · intro hc
      have hc' : c * i' = i' * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      show q c * q i' = q i' * q c
      rw [← map_mul, ← map_mul, hc']
  have hZcard : Nat.card Z = 12 := by
    rw [hZeq, ← Ψ.card_centralizer_delta hHN hxH hx hi hi1]
    refine Nat.card_congr
      { toFun := fun c => ⟨(c.1 : G), ?_⟩
        invFun := fun d => ⟨⟨d.1, (Subgroup.mem_inf.mp d.2).2⟩, ?_⟩
        left_inv := fun c => rfl
        right_inv := fun d => rfl }
    · refine Subgroup.mem_inf.mpr ⟨?_, c.1.2⟩
      have := Subgroup.mem_centralizer_singleton_iff.mp c.2
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val this)
    · refine Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp d.2).1
  have hidx : Z.index = (Subgroup.centralizer ({q i'} : Set (cenQuot x))).index :=
    Subgroup.index_comap_of_surjective _ hqs
  have h1 := Subgroup.card_mul_index Z
  have h2 := Subgroup.card_mul_index (Subgroup.centralizer ({q i'} : Set (cenQuot x)))
  have h3 := card_centralizer_eq_three_mul hx
  have hpos : 0 < Z.index := by
    rw [Nat.pos_iff_ne_zero]
    exact Subgroup.FiniteIndex.index_ne_zero
  rw [hZcard, hidx] at h1
  rw [hidx] at hpos
  have : 12 * (Subgroup.centralizer ({q i'} : Set (cenQuot x))).index =
      3 * ((Subgroup.centralizer ({q i'} : Set (cenQuot x))).index *
        Nat.card ↥(Subgroup.centralizer ({q i'} : Set (cenQuot x)))) := by
    rw [h1, h3, ← h2]
    ring
  have hfin : Nat.card ↥(Subgroup.centralizer ({q i'} : Set (cenQuot x))) = 4 := by
    nlinarith
  exact hfin

theorem card_centralizer_cenQuot (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3) :
    ∀ i : cenQuot x, orderOf i = 2 →
      Nat.card ↥(Subgroup.centralizer ({i} : Set (cenQuot x))) = 4 := by
  intro i' hi'
  obtain ⟨c, hc, hc1, rfl⟩ := exists_invol_lift hx hi'
  obtain ⟨g, i, hi, hi1, hgc⟩ := Ψ.exists_conj_delta hHN hxH hx hc hc1
  have h := Ψ.card_centralizer_mk_delta hHN hxH hx hi hi1
  rw [← hgc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h
  rw [← h]
  exact (card_centralizer_conj _ _).symm

theorem cenQuot_alt
    (hHN : Subgroup.centralizer ({z} : Set G) ≤ N) {x w : G}
    (hxH : x ∈ Subgroup.centralizer ({z} : Set G)) (hx : orderOf x = 3)
    (hw : orderOf w = 3) (hwx : w * x = x * w) (hwX : w ∉ Subgroup.zpowers x) :
    Nonempty (cenQuot x ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (cenQuot x ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨D, ⟨eD⟩⟩ := Ψ.exists_klein_sylow_cenQuot hHN hxH hx
  have hcen := Ψ.card_centralizer_cenQuot hHN hxH hx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hwC : w ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwx
  have hw3 : orderOf (QuotientGroup.mk (⟨w, hwC⟩ : ↥(Subgroup.centralizer ({x} : Set G))) :
      cenQuot x) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, cenQuot_mk_eq_one_iff]
      have : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      simp [this]
    · rw [Ne, cenQuot_mk_eq_one_iff]
      exact hwX
  exact alt_four_or_five_of_klein D eD hcen hw3

end KuA6Model

end CFSG.GH74.QTGen4.Ku
