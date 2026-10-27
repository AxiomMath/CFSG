module

public import CFSG.GH74.Uniqueness.Section156R
public import CFSG.GH74.Uniqueness.Section156Defs
public import CFSG.GH74.Uniqueness.Section15Aux3

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]


namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

omit [Finite X] in
theorem E_normal_R1 {g : X} (hg : g ∈ R1 V Mo U) {x : X}
    (hx : x ∈ Mo ⊔ U) : g * x * g⁻¹ ∈ Mo ⊔ U :=
  (mem_normalizer_iff.mp (mem_inf.mp hg).2 x).mp hx

omit [Finite X] in
theorem Mo_central (H : Hyp156 M n L D K J Mo V U Y) {g : X} (hg : g ∈ R1 V Mo U) {m : X}
    (hm : m ∈ Mo) : g * m = m * g := H.F.V_comm g (mem_inf.mp hg).1 m hm

theorem sq_R1_E (H : Hyp156 M n L D K J Mo V U Y) : ∀ x ∈ R1 V Mo U, x * x ∈ Mo ⊔ U := by
  have htrans := trans_of_free_of_card (A := K) H.E_le_R1 (fun k hk x hx => H.K_conj_R1 hk hx)
    (fun k hk x hx => H.K_conj_E hk hx) (fun k hk hk1 x hx hxk => H.free_R1 hk hk1 hx hxk)
    (by rw [H.F.card_K, H.index_R1])
  exact sq_mem_of_transitive (A := K) (H.F.V_pgroup.to_le inf_le_left) H.E_le_R1
    (fun g hg x hx => E_normal_R1 hg hx) (fun k hk x hx => H.K_conj_R1 hk hx)
    (fun k hk x hx => H.K_conj_E hk hx) htrans

omit [Finite X] in
theorem cent_U_out (H : Hyp156 M n L D K J Mo V U Y) {x : X} (hx : x ∈ R1 V Mo U)
    (hxE : x ∉ Mo ⊔ U) {u : X} (hu : u ∈ U) (hxu : x * u = u * x) : u = 1 := by
  by_contra hu1
  exact hxE (H.NV_L (mem_inf.mp hx).1 (H.centralizer_le_N hu hu1 hxu))

theorem sq_R1 (H : Hyp156 M n L D K J Mo V U Y) : ∀ x ∈ R1 V Mo U, x * x ∈ Mo := by
  intro x hx
  by_cases hxE : x ∈ Mo ⊔ U
  · rw [H.E_sq hxE]
    exact one_mem _
  · obtain ⟨m, hm, u, hu, hmu⟩ := H.mem_E (H.sq_R1_E x hx)
    have hxm : x * m = m * x := H.Mo_central hx hm
    have hxx : x * (x * x) = (x * x) * x := by group
    have hxu : x * u = u * x := by
      rw [hmu] at hxx
      have h1 : m * (x * u) = m * (u * x) := by
        calc m * (x * u) = (m * x) * u := by group
          _ = (x * m) * u := by rw [hxm]
          _ = x * (m * u) := by group
          _ = (m * u) * x := hxx
          _ = m * (u * x) := by group
      exact mul_left_cancel h1
    rw [H.cent_U_out hx hxE hu hxu, mul_one] at hmu
    rw [hmu]
    exact hm

omit [Finite X] in
theorem exists_U_ne (H : Hyp156 M n L D K J Mo V U Y) : ∃ u ∈ U, u ≠ 1 := by
  by_contra hno
  push Not at hno
  apply H.U_ne
  rw [eq_bot_iff]
  intro x hx
  exact mem_bot.mpr (hno x hx)

theorem exists_sq_ne (H : Hyp156 M n L D K J Mo V U Y) :
    ∃ x₀ ∈ R1 V Mo U, x₀ * x₀ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push Not at hno
  obtain ⟨g, hgV, hgE, hgN⟩ := exists_mem_normalizer_not_mem H.F.V_pgroup H.E_le_V H.E_ne_V
  have hgR : g ∈ R1 V Mo U := mem_inf.mpr ⟨hgV, hgN⟩
  obtain ⟨u, hu, hu1⟩ := H.exists_U_ne
  have huR : u ∈ R1 V Mo U := H.E_le_R1 (mem_sup_right hu)
  have hgu : g * u = u * g := by
    have h1 : (g * u)⁻¹ = g * u := inv_eq_of_mul_eq_one_right (hno _ (mul_mem hgR huR))
    have hg' : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hno g hgR)
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hno u huR)
    calc g * u = (g * u)⁻¹ := h1.symm
      _ = u⁻¹ * g⁻¹ := mul_inv_rev g u
      _ = u * g := by rw [hg', hu']
  exact hu1 (H.cent_U_out hgR hgE hu hgu)

omit [Finite X] in
@[expose] def orbitSet (K Mo : Subgroup X) (x₀ : X) : Set X :=
  {y : X | ∃ k ∈ K, ∃ m ∈ Mo, y = k * x₀ * k⁻¹ * m}

theorem eq_one_of_conj_mem (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U)
    (hx₀E : x₀ ∉ Mo ⊔ U) {c : X} (hc : c ∈ K) (hcx : x₀⁻¹ * (c * x₀ * c⁻¹) ∈ Mo ⊔ U) :
    c = 1 := by
  by_contra hc1
  exact hx₀E (H.free_R1 hc hc1 hx₀ hcx)

theorem ncard_orbitSet (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U)
    (hx₀E : x₀ ∉ Mo ⊔ U) : (orbitSet K Mo x₀).ncard = (2 ^ n - 1) * 2 ^ n := by
  let φ : ↥K × ↥Mo → X := fun p => (p.1 : X) * x₀ * (p.1 : X)⁻¹ * (p.2 : X)
  have hφ : Function.Injective φ := by
    rintro ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ ⟨⟨k', hk'⟩, ⟨m', hm'⟩⟩ h
    have h' : k * x₀ * k⁻¹ * m = k' * x₀ * k'⁻¹ * m' := h
    have h2 : k * x₀ * k⁻¹ = k' * x₀ * k'⁻¹ * m' * m⁻¹ := by
      rw [← h']
      group
    have hcK : k'⁻¹ * k ∈ K := mul_mem (inv_mem hk') hk
    have hmem : x₀⁻¹ * ((k'⁻¹ * k) * x₀ * (k'⁻¹ * k)⁻¹) ∈ Mo ⊔ U := by
      have e : x₀⁻¹ * ((k'⁻¹ * k) * x₀ * (k'⁻¹ * k)⁻¹) = k'⁻¹ * (m' * m⁻¹) * k'⁻¹⁻¹ := by
        calc x₀⁻¹ * ((k'⁻¹ * k) * x₀ * (k'⁻¹ * k)⁻¹) = x₀⁻¹ * (k'⁻¹ * (k * x₀ * k⁻¹) * k') := by
              group
          _ = x₀⁻¹ * (k'⁻¹ * (k' * x₀ * k'⁻¹ * m' * m⁻¹) * k') := by rw [h2]
          _ = k'⁻¹ * (m' * m⁻¹) * k'⁻¹⁻¹ := by group
      rw [e]
      exact mem_sup_left (H.F.Mo_normal _ (inv_mem (H.F.K_le_M hk')) _ (mul_mem hm' (inv_mem hm)))
    have hc1 := H.eq_one_of_conj_mem hx₀ hx₀E hcK hmem
    have hkk : k = k' := (inv_mul_eq_one.mp hc1).symm
    subst hkk
    have hmm : m = m' := mul_left_cancel h'
    subst hmm
    rfl
  have hrange : orbitSet K Mo x₀ = Set.range φ := by
    ext y
    constructor
    · rintro ⟨k, hk, m, hm, rfl⟩
      exact ⟨(⟨k, hk⟩, ⟨m, hm⟩), rfl⟩
    · rintro ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, rfl⟩
      exact ⟨k, hk, m, hm, rfl⟩
  rw [hrange, Set.ncard_range_of_injective hφ, Nat.card_prod, H.F.card_K, H.F.card_Mo]

theorem sq_orbit (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U)
    {k : X} (hk : k ∈ K) {m : X} (hm : m ∈ Mo) :
    (k * x₀ * k⁻¹ * m) * (k * x₀ * k⁻¹ * m) = k * (x₀ * x₀) * k⁻¹ := by
  have hy : k * x₀ * k⁻¹ ∈ R1 V Mo U := H.K_conj_R1 hk hx₀
  have hc : k * x₀ * k⁻¹ * m = m * (k * x₀ * k⁻¹) := H.Mo_central hy hm
  calc (k * x₀ * k⁻¹ * m) * (k * x₀ * k⁻¹ * m) = (k * x₀ * k⁻¹) * (m * (k * x₀ * k⁻¹)) * m := by
        group
    _ = (k * x₀ * k⁻¹) * (k * x₀ * k⁻¹ * m) * m := by rw [hc]
    _ = (k * x₀ * k⁻¹) * (k * x₀ * k⁻¹) * (m * m) := by group
    _ = k * (x₀ * x₀) * k⁻¹ := by rw [H.F.Mo_sq m hm]; group

theorem partition (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U)
    (hx₀2 : x₀ * x₀ ≠ 1) :
    (R1 V Mo U : Set X) =
      ({1} ∪ ((Mo : Set X) \ {1})) ∪ conjSet M U ∪ orbitSet K Mo x₀ := by
  have hx₀E : x₀ ∉ Mo ⊔ U := fun h => hx₀2 (H.E_sq h)
  have hnorm := (H.R1_normal_and_big).1
  have hsub : ({1} ∪ ((Mo : Set X) \ {1})) ∪ conjSet M U ∪ orbitSet K Mo x₀ ⊆
      (R1 V Mo U : Set X) := by
    refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
    · rintro _ rfl
      exact one_mem _
    · rintro x ⟨hx, -⟩
      exact H.E_le_R1 (mem_sup_left hx)
    · rintro _ ⟨g, hg, a, ha, -, rfl⟩
      exact hnorm g hg a (H.E_le_R1 (mem_sup_right ha))
    · rintro _ ⟨k, hk, m, hm, rfl⟩
      exact mul_mem (H.K_conj_R1 hk hx₀) (H.E_le_R1 (mem_sup_left hm))
  have hsq_orbit : ∀ y ∈ orbitSet K Mo x₀, y * y ≠ 1 := by
    rintro _ ⟨k, hk, m, hm, rfl⟩ h1
    rw [H.sq_orbit hx₀ hk hm] at h1
    apply hx₀2
    calc x₀ * x₀ = k⁻¹ * (k * (x₀ * x₀) * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  have hsq_conj : ∀ y ∈ conjSet M U, y * y = 1 := by
    rintro _ ⟨g, -, a, ha, -, rfl⟩
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [H.U_sq a ha]; group
  have hd1 : Disjoint ({1} : Set X) ((Mo : Set X) \ {1}) := by
    rw [Set.disjoint_left]
    rintro x rfl ⟨-, h⟩
    exact h rfl
  have hd2 : Disjoint ({1} ∪ ((Mo : Set X) \ {1})) (conjSet M U) := by
    rw [Set.disjoint_left]
    rintro x hx ⟨g, hg, a, ha, ha1, rfl⟩
    rcases hx with hx | ⟨hx, -⟩
    · apply ha1
      have h1 : g * a * g⁻¹ = 1 := hx
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exact H.conj_not_mem_Mo hg ha ha1 hx
  have hd3 : Disjoint ({1} ∪ ((Mo : Set X) \ {1}) ∪ conjSet M U) (orbitSet K Mo x₀) := by
    rw [Set.disjoint_left]
    intro x hx hxO
    apply hsq_orbit x hxO
    rcases hx with (hx | ⟨hx, -⟩) | hx
    · rw [Set.mem_singleton_iff.mp hx, one_mul]
    · exact H.F.Mo_sq x hx
    · exact hsq_conj x hx
  have hcard : (({1} ∪ ((Mo : Set X) \ {1})) ∪ conjSet M U ∪ orbitSet K Mo x₀).ncard =
      Nat.card (R1 V Mo U) := by
    rw [Set.ncard_union_eq hd3 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq hd1 (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton,
      Set.ncard_sdiff_singleton_of_mem (one_mem Mo), H.ncard_conjSet_M,
      H.ncard_orbitSet hx₀ hx₀E, H.card_R1]
    have hMo : (Mo : Set X).ncard = 2 ^ n := by
      rw [← Nat.card_coe_set_eq]
      exact H.F.card_Mo
    rw [hMo]
    have hq : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hr := H.two_le_card_U
    set q := 2 ^ n
    set r := Nat.card U
    have h2n : 2 ^ (2 * n) = q * q := by rw [two_mul, pow_add]
    rw [h2n]
    have e1 : q * q * (r - 1) + q * q = q * q * r := by
      rw [Nat.mul_sub, mul_one]
      have : q * q ≤ q * q * r := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have e2 : (q - 1) * q + q = q * q := by
      rw [Nat.sub_mul, one_mul]
      have : q ≤ q * q := Nat.le_mul_of_pos_right _ (by omega)
      omega
    omega
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, ← Nat.card_coe_set_eq]; exact le_rfl)
    (Set.toFinite _)).symm

end Hyp156

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

theorem U_eq_pair (H : Hyp156 M n L D K J Mo V U Y) :
    ∃ u₀ ∈ U, u₀ ≠ 1 ∧ ∀ x ∈ U, x = 1 ∨ x = u₀ := by
  obtain ⟨x₀, hx₀, hx₀2⟩ := H.exists_sq_ne
  have hx₀E : x₀ ∉ Mo ⊔ U := fun h => hx₀2 (H.E_sq h)
  have hpart := H.partition hx₀ hx₀2
  have hinv : ∀ u ∈ U, u ≠ 1 → u * x₀ * u = x₀⁻¹ := by
    intro u hu hu1
    have huR : u ∈ R1 V Mo U := H.E_le_R1 (mem_sup_right hu)
    have hux : u * x₀ ∈ (R1 V Mo U : Set X) := mul_mem huR hx₀
    rw [hpart] at hux
    have hsq : u * x₀ * (u * x₀) = 1 := by
      rcases hux with ((hux | ⟨hux, -⟩) | hux) | hux
      · exfalso
        apply hx₀E
        have h1 : u * x₀ = 1 := hux
        have e : x₀ = u⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [e]
        exact inv_mem (mem_sup_right hu)
      · exfalso
        apply hx₀E
        have e : x₀ = u⁻¹ * (u * x₀) := by group
        rw [e]
        exact mul_mem (inv_mem (mem_sup_right hu)) (mem_sup_left hux)
      · obtain ⟨g, -, a, ha, -, hga⟩ := hux
        rw [hga]
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [H.U_sq a ha]; group
      · exfalso
        obtain ⟨k, hk, m, hm, hkm⟩ := hux
        have hmem : x₀⁻¹ * (k * x₀ * k⁻¹) ∈ Mo ⊔ U := by
          have e : x₀⁻¹ * (k * x₀ * k⁻¹) = x₀⁻¹ * u * x₀ * m⁻¹ := by
            have h1 : k * x₀ * k⁻¹ = u * x₀ * m⁻¹ := by rw [hkm]; group
            rw [h1]
            group
          rw [e]
          have h2 : x₀⁻¹ * u * x₀ ∈ Mo ⊔ U := by
            have := E_normal_R1 (inv_mem hx₀) (mem_sup_right hu : u ∈ Mo ⊔ U)
            rwa [inv_inv] at this
          exact mul_mem h2 (inv_mem (mem_sup_left hm))
        have hk1 := H.eq_one_of_conj_mem hx₀ hx₀E hk hmem
        rw [hk1] at hkm
        have hum : u = x₀ * m * x₀⁻¹ := by
          calc u = u * x₀ * x₀⁻¹ := by group
            _ = 1 * x₀ * 1⁻¹ * m * x₀⁻¹ := by rw [hkm]
            _ = x₀ * m * x₀⁻¹ := by group
        have hmx : x₀ * m = m * x₀ := H.Mo_central hx₀ hm
        rw [hmx, mul_inv_cancel_right] at hum
        exact hu1 (H.eq_one_of_mem_Mo_U (hum ▸ hm) hu)
    have huu : u * u = 1 := H.U_sq u hu
    calc u * x₀ * u = (u * x₀ * (u * x₀)) * x₀⁻¹ := by group
      _ = x₀⁻¹ := by rw [hsq, one_mul]
  obtain ⟨u₀, hu₀, hu₀1⟩ := H.exists_U_ne
  refine ⟨u₀, hu₀, hu₀1, fun x hx => ?_⟩
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  right
  have hcomm : x₀ * (x * u₀) = (x * u₀) * x₀ := by
    have h1 := hinv x hx hx1
    have h2 := hinv u₀ hu₀ hu₀1
    have hxx : x * x = 1 := H.U_sq x hx
    have huu : u₀ * u₀ = 1 := H.U_sq u₀ hu₀
    calc x₀ * (x * u₀) = (x * x) * x₀ * (x * u₀) := by rw [hxx, one_mul]
      _ = x * (x * x₀ * x) * u₀ := by group
      _ = x * x₀⁻¹ * u₀ := by rw [h1]
      _ = x * (u₀ * x₀ * u₀) * u₀ := by rw [h2]
      _ = (x * u₀) * x₀ * (u₀ * u₀) := by group
      _ = (x * u₀) * x₀ := by rw [huu, mul_one]
  have hxu : x * u₀ ∈ U := mul_mem hx hu₀
  have h1 := H.cent_U_out hx₀ hx₀E hxu hcomm
  have hu₀i : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right (H.U_sq u₀ hu₀)
  calc x = x * u₀ * u₀⁻¹ := by group
    _ = u₀ := by rw [h1, one_mul, hu₀i]

theorem Y_trivial (H : Hyp156 M n L D K J Mo V U Y) {u₀ : X} (hu₀ : u₀ ∈ U) (hu₀1 : u₀ ≠ 1)
    (hU : ∀ x ∈ U, x = 1 ∨ x = u₀) : ∀ y ∈ Y, y = 1 := by
  intro y hy
  by_contra hy1
  have hyu : y * u₀ * y⁻¹ ∈ U := by
    refine H.U_two _ (mul_mem (mul_mem (H.Y_le hy) (H.U_le hu₀)) (inv_mem (H.Y_le hy))) ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hxP : IsPGroup 2 (zpowers u₀) := H.U_pgroup.to_le (zpowers_le.mpr hu₀)
    obtain ⟨k, hk⟩ := hxP.exists_card_eq
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ← Nat.card_zpowers, hk]
  rcases hU _ hyu with h1 | h1
  · apply hu₀1
    calc u₀ = y⁻¹ * (y * u₀ * y⁻¹) * y := by group
      _ = 1 := by rw [h1]; group
  · apply hu₀1
    refine H.fpf y hy hy1 u₀ hu₀ ?_
    calc y * u₀ = (y * u₀ * y⁻¹) * y := by group
      _ = u₀ * y := by rw [h1]

end Hyp156

namespace Hyp156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V U Y : Subgroup X}

theorem orbitSet_subset_R1 (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U) :
    orbitSet K Mo x₀ ⊆ (R1 V Mo U : Set X) := by
  rintro _ ⟨k, hk, m, hm, rfl⟩
  exact mul_mem (H.K_conj_R1 hk hx₀) (H.E_le_R1 (mem_sup_left hm))

theorem sq_ne_of_mem_orbitSet (H : Hyp156 M n L D K J Mo V U Y) {x₀ : X} (hx₀ : x₀ ∈ R1 V Mo U)
    (hx₀2 : x₀ * x₀ ≠ 1) {y : X} (hy : y ∈ orbitSet K Mo x₀) : y * y ≠ 1 := by
  obtain ⟨k, hk, m, hm, rfl⟩ := hy
  intro h1
  rw [H.sq_orbit hx₀ hk hm] at h1
  apply hx₀2
  calc x₀ * x₀ = k⁻¹ * (k * (x₀ * x₀) * k⁻¹) * k := by group
    _ = 1 := by rw [h1]; group

theorem conf156 (H : Hyp156 M n L D K J Mo V U Y) :
    ∃ u : X, Conf156 M n L D K J Mo V (R1 V Mo U) u := by
  obtain ⟨u₀, hu₀, hu₀1, hU⟩ := H.U_eq_pair
  have hY := H.Y_trivial hu₀ hu₀1 hU
  have hJ : ∀ j ∈ J, j = 1 ∨ j = u₀ := by
    intro j hj
    obtain ⟨x, hx, y, hy, rfl⟩ := H.JUY j hj
    rw [hY y hy, mul_one]
    exact hU x hx
  have hu₀2 : u₀ * u₀ = 1 := H.U_sq u₀ hu₀
  have hcardU : Nat.card U = 2 := by
    have hUz : U = zpowers u₀ := by
      apply le_antisymm
      · intro x hx
        rcases hU x hx with rfl | rfl
        · exact one_mem _
        · exact mem_zpowers _
      · exact zpowers_le.mpr hu₀
    rw [hUz, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hu₀2) hu₀1
  obtain ⟨x₀, hx₀, hx₀2⟩ := H.exists_sq_ne
  have hpart := H.partition hx₀ hx₀2
  have hx₀E : x₀ ∉ Mo ⊔ U := fun h => hx₀2 (H.E_sq h)
  obtain ⟨hnorm, hbig⟩ := H.R1_normal_and_big
  have hfour : {x : X | x ∈ R1 V Mo U ∧ x * x ≠ 1} = orbitSet K Mo x₀ := by
    ext x
    constructor
    · rintro ⟨hx, hx2⟩
      have hx' : x ∈ (R1 V Mo U : Set X) := hx
      rw [hpart] at hx'
      rcases hx' with ((hx' | ⟨hx', -⟩) | ⟨g, -, a, ha, -, rfl⟩) | hx'
      · exact absurd (by rw [Set.mem_singleton_iff.mp hx', one_mul]) hx2
      · exact absurd (H.F.Mo_sq x hx') hx2
      · exfalso
        apply hx2
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [H.U_sq a ha]; group
      · exact hx'
    · intro hx
      exact ⟨H.orbitSet_subset_R1 hx₀ hx, H.sq_ne_of_mem_orbitSet hx₀ hx₀2 hx⟩
  refine ⟨u₀,
    { F := H.F
      u_mem_J := H.U_le hu₀
      u_sq := hu₀2
      u_ne := hu₀1
      J_eq := hJ
      VD := fun d hd hdV => hU d (H.VD_eq ▸ mem_inf.mpr ⟨hdV, hd⟩)
      C0_le := fun g _ hcomm => by
        obtain ⟨v, hv, y, hy, rfl⟩ :=
          H.C0_eq g (mem_centralizer_iff.mpr fun x hx => (hcomm x hx).symm)
        rw [hY y hy, mul_one]
        exact hv
      NV := fun x hxV hxN => by
        obtain ⟨m, hm, a, ha, rfl⟩ := H.mem_E (H.NV_L hxV hxN)
        rcases hU a ha with rfl | rfl
        · left
          rw [mul_one]
          exact hm
        · right
          rw [mul_assoc, hu₀2, mul_one]
          exact hm
      R₁_le := inf_le_left
      Mo_le_R₁ := fun x hx => H.E_le_R1 (mem_sup_left hx)
      u_mem_R₁ := H.E_le_R1 (mem_sup_right hu₀)
      R₁_normal := hnorm
      card_R₁ := by rw [H.card_R1, hcardU, pow_succ]
      sq_R₁ := H.sq_R1
      inv_R₁ := fun x hx hxMo hx2 => by
        have hx' : x ∈ (R1 V Mo U : Set X) := hx
        rw [hpart] at hx'
        rcases hx' with ((hx' | ⟨hx', -⟩) | ⟨g, hg, a, ha, ha1, rfl⟩) | hx'
        · exact absurd (Set.mem_singleton_iff.mp hx' ▸ one_mem Mo) hxMo
        · exact absurd hx' hxMo
        · rcases hU a ha with rfl | rfl
          · exact absurd rfl ha1
          · exact ⟨g, hg, rfl⟩
        · exact absurd hx2 (H.sq_ne_of_mem_orbitSet hx₀ hx₀2 hx')
      card_four := by
        rw [hfour, H.ncard_orbitSet hx₀ hx₀E, mul_comm]
      cent_K := fun k hk hk1 x hx hkx => hU x (H.cent_R1 hk hk1 hx hkx)
      big := fun hne => by
        obtain ⟨h1, h2, h3⟩ := hbig hne
        exact ⟨by rw [h1, hcardU, pow_succ], h2, h3⟩ }⟩

end Hyp156

end CFSG.GH74.Uniqueness
