module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Act

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup

@[expose] def centralizerBar {G : Type*} [Group G] (B : Subgroup G) (y : G) :
    Subgroup (↥B ⧸ center ↥B) :=
  ((B ⊓ centralizer ({y} : Set G)).subgroupOf B).map (QuotientGroup.mk' (center ↥B))

end CFSG.OddStandard.Seitz77

namespace CFSG.OddStandard.Seitz77.L34

open Subgroup CFSG.ComponentClassification CFSG.PSL3Four.Native CFSG.ABGLocalTools
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem exists_pow_conj_of_odd {G : Type*} [Group G] {w w' : G} (hw : w * w = 1)
    (hw' : w' * w' = 1) (hodd : Odd (orderOf (w⁻¹ * w'))) :
    ∃ n : ℕ, (w⁻¹ * w') ^ n * w' * ((w⁻¹ * w') ^ n)⁻¹ = w := by
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw
  have hw'i : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right hw'
  set k := w⁻¹ * w' with hk
  obtain ⟨j, hj⟩ := hodd
  have hinv : w' * k * w'⁻¹ = k⁻¹ := by
    rw [hk, hwi, hw'i, mul_inv_rev, hw'i, hwi]
    calc w' * (w * w') * w' = w' * w * (w' * w') := by group
      _ = w' * w := by rw [hw', mul_one]
  have h1 : w' * k ^ (j + 1) * w'⁻¹ = (k⁻¹) ^ (j + 1) := by
    have := map_pow (MulAut.conj w') k (j + 1)
    simpa [MulAut.conj_apply, hinv] using this
  refine ⟨j + 1, ?_⟩
  have hpow : k ^ (j + 1) * k ^ (j + 1) = k := by
    rw [← pow_add, show j + 1 + (j + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc k ^ (j + 1) * w' * (k ^ (j + 1))⁻¹
      = k ^ (j + 1) * (w' * (k ^ (j + 1))⁻¹ * w'⁻¹) * w' := by group
    _ = k ^ (j + 1) * (w' * k ^ (j + 1) * w'⁻¹)⁻¹ * w' := by group
    _ = k ^ (j + 1) * ((k⁻¹) ^ (j + 1))⁻¹ * w' := by rw [h1]
    _ = k ^ (j + 1) * k ^ (j + 1) * w' := by rw [inv_pow, inv_inv]
    _ = k * w' := by rw [hpow]
    _ = w := by rw [hk, hwi, mul_assoc, hw', mul_one]

theorem exists_conj_of_involution
    (hcheck : Nat.card S = 20160 → ∀ r ∈ [r₂, r₃, r₄], ∀ c ∈ S, c * r = r * c → c * c = 1 →
      ∃ s ∈ S, s * r = r * c * s)
    {y : Equiv.Perm (Fin 42)} (hyR : y ∈ R) (hyS : y ∉ S) (hy2 : y * y = 1)
    {c : Equiv.Perm (Fin 42)} (hcS : c ∈ S) (hcy : c * y = y * c) (hc2 : c * c = 1) :
    ∃ s ∈ S, s * y * s⁻¹ = y * c := by
  have hx2 : orderOf (⟨y, hyR⟩ : R) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (Subtype.ext ?_) ?_
    · rw [Subgroup.coe_pow, Subgroup.coe_one, sq]
      exact hy2
    · intro h1
      have hy1 : y = 1 := congrArg Subtype.val h1
      exact hyS (hy1 ▸ S.one_mem)
  have hfu := hcheck PSL3Four.card_S
  have key : ∀ r' ∈ [r₂, r₃, r₄], ∀ u ∈ R, y = u * r' * u⁻¹ → ∃ s ∈ S, s * y * s⁻¹ = y * c := by
    intro r' hr' u hu hyu
    have hcS' : u⁻¹ * c * u ∈ S := by
      have := conj_mem_S (R.inv_mem hu) hcS
      rwa [inv_inv] at this
    have hcy' : c * (u * r' * u⁻¹) = (u * r' * u⁻¹) * c := by rw [← hyu]; exact hcy
    have hcr : (u⁻¹ * c * u) * r' = r' * (u⁻¹ * c * u) := by
      calc (u⁻¹ * c * u) * r' = u⁻¹ * (c * (u * r' * u⁻¹)) * u := by group
        _ = u⁻¹ * ((u * r' * u⁻¹) * c) * u := by rw [hcy']
        _ = r' * (u⁻¹ * c * u) := by group
    have hcc : (u⁻¹ * c * u) * (u⁻¹ * c * u) = 1 := by
      calc (u⁻¹ * c * u) * (u⁻¹ * c * u) = u⁻¹ * (c * c) * u := by group
        _ = 1 := by rw [hc2]; group
    obtain ⟨s', hs'S, hs'⟩ := hfu r' hr' _ hcS' hcr hcc
    refine ⟨u * s' * u⁻¹, conj_mem_S hu hs'S, ?_⟩
    calc u * s' * u⁻¹ * y * (u * s' * u⁻¹)⁻¹ = u * (s' * r' * s'⁻¹) * u⁻¹ := by rw [hyu]; group
      _ = u * (r' * (u⁻¹ * c * u)) * u⁻¹ := by
          rw [mul_inv_eq_iff_eq_mul.2 hs']
      _ = y * c := by rw [hyu]; group
  rcases (PSL3Four.orderOf_eq_two_iff _).1 hx2 with h | h | h | h
  · exact absurd (PSL3Four.mem_S_of_isConj₁ h) hyS
  · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
    exact key r₂ (by simp) u hu hyu
  · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
    exact key r₃ (by simp) u hu hyu
  · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
    exact key r₄ (by simp) u hu hyu

theorem commutator_eq_top_of_simple {K : Type*} [Group K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : commutator K = ⊤ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator K) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : (⊤ : Subgroup K) ≤ centralizer ((⊤ : Subgroup K) : Set K) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    exact hab (mem_centralizer_iff.1 (h1 (Subgroup.mem_top b)) a (Subgroup.mem_top a))
  · exact h

theorem exists_perfect_involution {H K : Type*} [Group H] [Finite H] [Group K] [IsSimpleGroup K]
    (π : H →* K) (hπ : Function.Surjective π) (hnab : ∃ a b : K, a * b ≠ b * a)
    (heven : 2 ∣ Nat.card K) :
    ∃ D : Subgroup H, ⁅D, D⁆ = D ∧ ∃ c ∈ D, c * c = 1 ∧ c ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, n, hmn, hmn'⟩ := Finite.exists_ne_map_eq_of_infinite (derivedSeries H)
  have hstab : ∃ m, derivedSeries H (m + 1) = derivedSeries H m := by
    rcases lt_or_gt_of_ne hmn with h | h
    · refine ⟨m, le_antisymm (derivedSeries_antitone H (Nat.le_succ m)) ?_⟩
      rw [hmn']
      exact derivedSeries_antitone H (by omega)
    · refine ⟨n, le_antisymm (derivedSeries_antitone H (Nat.le_succ n)) ?_⟩
      rw [← hmn']
      exact derivedSeries_antitone H (by omega)
  obtain ⟨m, hm⟩ := hstab
  refine ⟨derivedSeries H m, by rw [← derivedSeries_succ, hm], ?_⟩
  have hK : ∀ k, derivedSeries K k = ⊤ := by
    intro k
    cases k with
    | zero => exact derivedSeries_zero K
    | succ k => rw [IsSimpleGroup.derivedSeries_succ, commutator_eq_top_of_simple hnab]
  have hsurj : Function.Surjective ((π.comp (derivedSeries H m).subtype)) := by
    intro b
    have hb : b ∈ (derivedSeries H m).map π := by
      rw [map_derivedSeries_eq hπ m, hK m]
      exact Subgroup.mem_top b
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨⟨d, hd⟩, hdb⟩
  have hdvd : 2 ∣ Nat.card (derivedSeries H m) :=
    heven.trans (Subgroup.card_dvd_of_surjective hsurj)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := derivedSeries H m) 2 hdvd
  refine ⟨c, c.2, ?_, ?_⟩
  · have h2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    have : (c : H) ^ 2 = 1 := congrArg Subtype.val h2
    rwa [sq] at this
  · intro h1
    have : c = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hc
    omega

section Lift

open RankTwoSporadic

variable {G : Type*} [Group G] {B : Subgroup G} {ψ : normalizer (B : Set G) →* ↥PSL3Four.R}

theorem exists_lift_conj_aux (hZ : Odd (Nat.card (center ↥B)))
    (hψ : IsActionHom B (PSL3Four.S.subgroupOf PSL3Four.R) ψ) {w w' : G}
    (hw : w ∈ normalizer (B : Set G)) (hw' : w' ∈ normalizer (B : Set G)) (hw2 : w * w = 1)
    (hw'2 : w' * w' = 1) (hψww : ψ ⟨w, hw⟩ = ψ ⟨w', hw'⟩) (hk : w⁻¹ * w' ∈ B) :
    ∃ (x : G) (hx : x ∈ B), x * w' * x⁻¹ = w ∧ ψ ⟨x, le_normalizer hx⟩ = 1 := by
  set k := w⁻¹ * w' with hkdef
  have hkN : k ∈ normalizer (B : Set G) := (normalizer _).mul_mem ((normalizer _).inv_mem hw) hw'
  have hψk : ψ ⟨k, hkN⟩ = 1 := by
    have : (⟨k, hkN⟩ : normalizer (B : Set G)) = ⟨w, hw⟩⁻¹ * ⟨w', hw'⟩ := Subtype.ext rfl
    rw [this, map_mul, map_inv, hψww, inv_mul_cancel]
  have hkC : k ∈ centralizer (B : Set G) := (hψ.eq_one_iff _).1 hψk
  have hkZ : (⟨k, hk⟩ : ↥B) ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext (mem_centralizer_iff.1 hkC b b.2)
  have hodd : Odd (orderOf k) := by
    have := orderOf_dvd_natCard (⟨⟨k, hk⟩, hkZ⟩ : center ↥B)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
    exact hZ.of_dvd_nat this
  obtain ⟨n, hn⟩ := exists_pow_conj_of_odd hw2 hw'2 hodd
  have hkn : k ^ n ∈ B := B.pow_mem hk n
  refine ⟨k ^ n, hkn, hn, ?_⟩
  have : (⟨k ^ n, le_normalizer hkn⟩ : normalizer (B : Set G)) = (⟨k, hkN⟩ : _) ^ n :=
    Subtype.ext (by simp)
  rw [this, map_pow, hψk, one_pow]

theorem exists_lift_conj (hZ : Odd (Nat.card (center ↥B)))
    (hψ : IsActionHom B (PSL3Four.S.subgroupOf PSL3Four.R) ψ) {y : G}
    (hy : y ∈ normalizer (B : Set G)) (hy2 : y * y = 1) {c : G} (hcB : c ∈ B)
    (hcy : c * y = y * c) (hc2 : c * c = 1) {a : G} (haB : a ∈ B)
    (hψa : ψ ⟨a, le_normalizer haB⟩ * ψ ⟨y, hy⟩ * (ψ ⟨a, le_normalizer haB⟩)⁻¹ =
      ψ ⟨y, hy⟩ * ψ ⟨c, le_normalizer hcB⟩) :
    ∃ (b : G) (hb : b ∈ B), b * y * b⁻¹ = y * c ∧
      ψ ⟨b, le_normalizer hb⟩ = ψ ⟨a, le_normalizer haB⟩ := by
  have hwN : y * c ∈ normalizer (B : Set G) := (normalizer _).mul_mem hy (le_normalizer hcB)
  have hw'N : a * y * a⁻¹ ∈ normalizer (B : Set G) :=
    (normalizer _).mul_mem ((normalizer _).mul_mem (le_normalizer haB) hy)
      ((normalizer _).inv_mem (le_normalizer haB))
  have hw2 : (y * c) * (y * c) = 1 := by
    calc (y * c) * (y * c) = y * (c * y) * c := by group
      _ = y * (y * c) * c := by rw [hcy]
      _ = (y * y) * (c * c) := by group
      _ = 1 := by rw [hy2, hc2, one_mul]
  have hw'2 : (a * y * a⁻¹) * (a * y * a⁻¹) = 1 := by
    calc (a * y * a⁻¹) * (a * y * a⁻¹) = a * (y * y) * a⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  have hψww : ψ ⟨y * c, hwN⟩ = ψ ⟨a * y * a⁻¹, hw'N⟩ := by
    have h1 : (⟨y * c, hwN⟩ : normalizer (B : Set G)) = ⟨y, hy⟩ * ⟨c, le_normalizer hcB⟩ :=
      Subtype.ext rfl
    have h2 : (⟨a * y * a⁻¹, hw'N⟩ : normalizer (B : Set G)) =
        ⟨a, le_normalizer haB⟩ * ⟨y, hy⟩ * ⟨a, le_normalizer haB⟩⁻¹ := Subtype.ext rfl
    rw [h1, h2, map_mul, map_mul, map_mul, map_inv]
    exact hψa.symm
  have hk : (y * c)⁻¹ * (a * y * a⁻¹) ∈ B := by
    have h1 : y⁻¹ * a * y ∈ B := by
      have := (mem_normalizer_iff.1 ((normalizer _).inv_mem hy) a).1 haB
      rwa [inv_inv] at this
    have : (y * c)⁻¹ * (a * y * a⁻¹) = c⁻¹ * (y⁻¹ * a * y) * a⁻¹ := by group
    rw [this]
    exact B.mul_mem (B.mul_mem (B.inv_mem hcB) h1) (B.inv_mem haB)
  obtain ⟨x, hxB, hx, hψx⟩ := exists_lift_conj_aux hZ hψ hwN hw'N hw2 hw'2 hψww hk
  refine ⟨x * a, B.mul_mem hxB haB, ?_, ?_⟩
  · calc x * a * y * (x * a)⁻¹ = x * (a * y * a⁻¹) * x⁻¹ := by group
      _ = y * c := hx
  · have : (⟨x * a, le_normalizer (B.mul_mem hxB haB)⟩ : normalizer (B : Set G)) =
        ⟨x, le_normalizer hxB⟩ * ⟨a, le_normalizer haB⟩ := Subtype.ext rfl
    rw [this, map_mul, hψx, one_mul]

theorem centralizerBar_equiv (hZ : Odd (Nat.card (center ↥B)))
    (hψ : IsActionHom B (PSL3Four.S.subgroupOf PSL3Four.R) ψ) {y : G}
    (hy : y ∈ normalizer (B : Set G)) (hy2 : y * y = 1) {u r : Equiv.Perm (Fin 42)}
    (hu : u ∈ PSL3Four.R) (hyr : (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) = u * r * u⁻¹) :
    Nonempty (centralizerBar B y ≃*
      ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S)) := by
  let φ : ↥B →* Equiv.Perm (Fin 42) :=
    PSL3Four.R.subtype.comp (ψ.comp (Subgroup.inclusion le_normalizer))
  have hφ : ∀ a : ↥B, φ a = (ψ ⟨a, le_normalizer a.2⟩ : Equiv.Perm (Fin 42)) := fun a => rfl
  have hφker : ∀ a : ↥B, φ a = 1 ↔ a ∈ center ↥B := fun a => by
    rw [hφ]
    constructor
    · intro h
      have h1 : ψ ⟨a, le_normalizer a.2⟩ = 1 := Subtype.ext h
      have h2 := (hψ.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (mem_centralizer_iff.1 h2 b b.2)
    · intro h
      have h2 : (a : G) ∈ centralizer (B : Set G) :=
        mem_centralizer_iff.2 fun b hb => congrArg Subtype.val (Subgroup.mem_center_iff.1 h ⟨b, hb⟩)
      exact congrArg Subtype.val ((hψ.eq_one_iff _).2 h2)
  let φbar : (↥B ⧸ center ↥B) →* Equiv.Perm (Fin 42) :=
    QuotientGroup.lift (center ↥B) φ fun a ha => (hφker a).2 ha
  have hφbar : ∀ a : ↥B, φbar (QuotientGroup.mk a) = φ a := fun a => rfl
  have hinj : Function.Injective φbar := by
    intro p q h
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hφbar, hφbar] at h
    exact QuotientGroup.eq.2 ((hφker _).1 (by rw [map_mul, map_inv, h, inv_mul_cancel]))
  have hCmap : (centralizerBar B y).map φbar =
      centralizer ({(ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓
        PSL3Four.S := by
    ext s
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have hval : φbar ((QuotientGroup.mk' (center ↥B)) a) =
          (ψ ⟨a, le_normalizer a.2⟩ : Equiv.Perm (Fin 42)) := rfl
      rw [hval]
      refine ⟨mem_centralizer_singleton_iff.2 ?_, hψ.map_mem a a.2⟩
      have h1 : (⟨a, le_normalizer a.2⟩ : ↥(normalizer (B : Set G))) * ⟨y, hy⟩ =
          ⟨y, hy⟩ * ⟨a, le_normalizer a.2⟩ := Subtype.ext (mem_centralizer_singleton_iff.1 ha.2)
      have h2 : ψ ⟨a, le_normalizer a.2⟩ * ψ ⟨y, hy⟩ = ψ ⟨y, hy⟩ * ψ ⟨a, le_normalizer a.2⟩ := by
        rw [← map_mul, ← map_mul, h1]
      exact congrArg Subtype.val h2
    · rintro ⟨hsc, hsS⟩
      have hsc' : s * (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) = (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) * s :=
        mem_centralizer_singleton_iff.1 hsc
      obtain ⟨a, haB, hax⟩ := hψ.exists_eq ⟨s, PSL3Four.S_le_R hsS⟩
        (Subgroup.mem_subgroupOf.2 hsS)
      have hψa : ψ ⟨a, le_normalizer haB⟩ * ψ ⟨y, hy⟩ * (ψ ⟨a, le_normalizer haB⟩)⁻¹ =
          ψ ⟨y, hy⟩ * ψ ⟨(1 : G), le_normalizer B.one_mem⟩ := by
        have h1 : (⟨(1 : G), le_normalizer B.one_mem⟩ : ↥(normalizer (B : Set G))) = 1 := rfl
        rw [h1, map_one, mul_one, hax]
        apply Subtype.ext
        change s * (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) * (s⁻¹) = ψ ⟨y, hy⟩
        rw [hsc', mul_inv_cancel_right]
      obtain ⟨b, hbB, hb, hψb⟩ := exists_lift_conj hZ hψ hy hy2 B.one_mem
        (by rw [one_mul, mul_one]) (by rw [mul_one]) haB hψa
      have hbc : b * y = y * b := by
        rw [mul_one] at hb
        calc b * y = b * y * b⁻¹ * b := by group
          _ = y * b := by rw [hb]
      refine ⟨QuotientGroup.mk ⟨b, hbB⟩,
        ⟨⟨b, hbB⟩, ⟨hbB, mem_centralizer_singleton_iff.2 hbc⟩, rfl⟩, ?_⟩
      have hval : φbar (QuotientGroup.mk (⟨b, hbB⟩ : ↥B)) =
          (ψ ⟨b, le_normalizer hbB⟩ : Equiv.Perm (Fin 42)) := rfl
      rw [hval, hψb, hax]
  have hconj : centralizer ({(ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42))} : Set (Equiv.Perm (Fin 42))) ⊓
      PSL3Four.S = (centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S).map
        (MulAut.conj u).toMonoidHom := by
    rw [hyr]
    ext x
    constructor
    · rintro ⟨hxc, hxS⟩
      have hxc' : x * (u * r * u⁻¹) = (u * r * u⁻¹) * x := mem_centralizer_singleton_iff.1 hxc
      refine ⟨u⁻¹ * x * u, ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩, ?_⟩
      · calc (u⁻¹ * x * u) * r = u⁻¹ * (x * (u * r * u⁻¹)) * u := by group
          _ = u⁻¹ * ((u * r * u⁻¹) * x) * u := by rw [hxc']
          _ = r * (u⁻¹ * x * u) := by group
      · have := PSL3Four.conj_mem_S (PSL3Four.R.inv_mem hu) hxS
        rwa [inv_inv] at this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · rintro ⟨c, ⟨hcc, hcS⟩, rfl⟩
      have hcc' : c * r = r * c := mem_centralizer_singleton_iff.1 hcc
      refine ⟨mem_centralizer_singleton_iff.2 ?_, PSL3Four.conj_mem_S hu hcS⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc u * c * u⁻¹ * (u * r * u⁻¹) = u * (c * r) * u⁻¹ := by group
        _ = u * (r * c) * u⁻¹ := by rw [hcc']
        _ = (u * r * u⁻¹) * (u * c * u⁻¹) := by group
  refine ⟨?_⟩
  have e1 := Subgroup.equivMapOfInjective (centralizerBar B y) φbar hinj
  have e2 := MulEquiv.subgroupCongr (hCmap.trans hconj)
  have e3 := Subgroup.equivMapOfInjective
    (centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ PSL3Four.S) (MulAut.conj u).toMonoidHom
    (MulAut.conj u).injective
  exact e1.trans (e2.trans e3.symm)

end Lift

end CFSG.OddStandard.Seitz77.L34

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification CFSG.PSL3Four.Native CFSG.ABGLocalTools
  CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem isSolvable_centralizer_of_bar {G : Type*} [Group G] (B : Subgroup G) (y : G)
    (h : Group.IsSolvable ↥(centralizerBar B y)) :
    Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G)) := by
  let C : Subgroup ↥B := (B ⊓ centralizer ({y} : Set G)).subgroupOf B
  let π : ↥C →* ↥B ⧸ center ↥B := (QuotientGroup.mk' (center ↥B)).comp C.subtype
  have hrange : π.range = centralizerBar B y := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : Group.IsSolvable ↥π.ker := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha : ((a : ↥C) : ↥B) ∈ center ↥B := QuotientGroup.eq_one_iff _ |>.1 a.2
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.1 ha b.1.1).symm)
  have hrange' : Group.IsSolvable ↥π.range := by
    rw [hrange]
    exact h
  have hC : Group.IsSolvable ↥C :=
    Group.isSolvable_of_ker_le_range π.ker.subtype π.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  let eC := subgroupOfEquivOfLe (inf_le_left : B ⊓ centralizer ({y} : Set G) ≤ B)
  exact Group.isSolvable_of_isSolvable_injective (f := eC.symm.toMonoidHom) eC.symm.injective

theorem outer_involution_cases {G : Type*} [Group G]
    {B : Subgroup G} (hB : commutator ↥B = ⊤) (hZ : Odd (Nat.card (center ↥B)))
    (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S)
    (hcheck : Nat.card S = 20160 → ∀ r ∈ [r₂, r₃, r₄], ∀ c ∈ S, c * r = r * c → c * c = 1 →
      ∃ s ∈ S, s * r = r * c * s)
    {y : G} (hy : y ∈ normalizer (B : Set G)) (hy2 : y * y = 1)
    (hout : y ∉ B ⊔ centralizer (B : Set G)) :
    (∀ c ∈ B ⊓ centralizer ({y} : Set G), c * c = 1 → ∃ b ∈ B, b * y * b⁻¹ = y * c) ∧
      (Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G)) ∨
        (IsSimpleGroup ↥(centralizerBar B y) ∧
          (∃ a b : ↥(centralizerBar B y), a * b ≠ b * a) ∧
          (Nat.card ↥(centralizerBar B y) = 60 ∨ Nat.card ↥(centralizerBar B y) = 168))) := by
  obtain ⟨ψ, hψ⟩ := RankTwoSporadic.exists_isActionHom RankTwoL3Four.HypII.l34AutModel hB e
  have hy'R : (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) ∈ R := (ψ ⟨y, hy⟩).2
  have hψy2 : ψ ⟨y, hy⟩ * ψ ⟨y, hy⟩ = 1 := by
    have h1 : (⟨y, hy⟩ : ↥(normalizer (B : Set G))) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
    rw [← map_mul, h1, map_one]
  have hy'2 : (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) * ψ ⟨y, hy⟩ = 1 := congrArg Subtype.val hψy2
  have hy'S : (ψ ⟨y, hy⟩ : Equiv.Perm (Fin 42)) ∉ S := fun hS =>
    hout ((L34.mem_sup_centralizer_iff hψ hy).2 hS)
  refine ⟨?_, ?_⟩
  ·
    rintro c ⟨hcB, hcC⟩ hc2
    have hcy : c * y = y * c := mem_centralizer_singleton_iff.1 hcC
    have hc'S : (ψ ⟨c, le_normalizer hcB⟩ : Equiv.Perm (Fin 42)) ∈ S := hψ.map_mem c hcB
    have hc'y : (ψ ⟨c, le_normalizer hcB⟩ : Equiv.Perm (Fin 42)) * ψ ⟨y, hy⟩ =
        ψ ⟨y, hy⟩ * ψ ⟨c, le_normalizer hcB⟩ := by
      have h1 : (⟨c, le_normalizer hcB⟩ : ↥(normalizer (B : Set G))) * ⟨y, hy⟩ =
          ⟨y, hy⟩ * ⟨c, le_normalizer hcB⟩ := Subtype.ext hcy
      have h2 : ψ ⟨c, le_normalizer hcB⟩ * ψ ⟨y, hy⟩ = ψ ⟨y, hy⟩ * ψ ⟨c, le_normalizer hcB⟩ := by
        rw [← map_mul, ← map_mul, h1]
      exact congrArg Subtype.val h2
    have hc'2 : (ψ ⟨c, le_normalizer hcB⟩ : Equiv.Perm (Fin 42)) *
        ψ ⟨c, le_normalizer hcB⟩ = 1 := by
      have h1 : (⟨c, le_normalizer hcB⟩ : ↥(normalizer (B : Set G))) * ⟨c, le_normalizer hcB⟩ =
          1 := Subtype.ext hc2
      have h2 : ψ ⟨c, le_normalizer hcB⟩ * ψ ⟨c, le_normalizer hcB⟩ = 1 := by
        rw [← map_mul, h1, map_one]
      exact congrArg Subtype.val h2
    obtain ⟨s, hsS, hs⟩ := L34.exists_conj_of_involution hcheck hy'R hy'S hy'2 hc'S hc'y hc'2
    obtain ⟨a, haB, hax⟩ := hψ.exists_eq ⟨s, PSL3Four.S_le_R hsS⟩ (Subgroup.mem_subgroupOf.2 hsS)
    have hψa : ψ ⟨a, le_normalizer haB⟩ * ψ ⟨y, hy⟩ * (ψ ⟨a, le_normalizer haB⟩)⁻¹ =
        ψ ⟨y, hy⟩ * ψ ⟨c, le_normalizer hcB⟩ := by
      rw [hax]
      exact Subtype.ext hs
    obtain ⟨b, hbB, hb, -⟩ := L34.exists_lift_conj hZ hψ hy hy2 hcB hcy hc2 haB hψa
    exact ⟨b, hbB, hb⟩
  · have hx2 : orderOf (ψ ⟨y, hy⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hψy2) fun h => hy'S (by rw [h]; exact S.one_mem)
    rcases (PSL3Four.orderOf_eq_two_iff _).1 hx2 with h | h | h | h
    · exact absurd (PSL3Four.mem_S_of_isConj₁ h) hy'S
    · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₂ := e'
      have := PSL3Four.isSimpleGroup_C₂
      obtain ⟨a, b, hab⟩ := PSL3Four.exists_mul_ne_C₂
      refine Or.inr ⟨e''.isSimpleGroup, ⟨e''.symm a, e''.symm b, fun h' => hab ?_⟩, Or.inr ?_⟩
      · simpa using congrArg e'' h'
      · rw [Nat.card_congr e''.toEquiv, PSL3Four.card_C₂]
    · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₃ := e'
      have := PSL3Four.isSimpleGroup_C₃
      obtain ⟨a, b, hab⟩ := PSL3Four.exists_mul_ne_C₃
      refine Or.inr ⟨e''.isSimpleGroup, ⟨e''.symm a, e''.symm b, fun h' => hab ?_⟩, Or.inl ?_⟩
      · simpa using congrArg e'' h'
      · rw [Nat.card_congr e''.toEquiv, PSL3Four.card_C₃]
    · obtain ⟨u, hu, hyu⟩ := PSL3Four.eq_conj_of_isConj h
      obtain ⟨e'⟩ := L34.centralizerBar_equiv hZ hψ hy hy2 hu hyu
      have e'' : centralizerBar B y ≃* ↥C₄ := e'
      have := PSL3Four.isSolvable_C₄
      refine Or.inl (isSolvable_centralizer_of_bar B y ?_)
      exact Group.isSolvable_of_isSolvable_injective (f := e''.toMonoidHom) e''.injective


theorem exists_perfect_involution_of_outer {G : Type*} [Group G]
    [Finite G] {B : Subgroup G} (hB : commutator ↥B = ⊤) (hZ : Odd (Nat.card (center ↥B)))
    (e : ↥B ⧸ center ↥B ≃* ↥PSL3Four.S)
    (hcheck : Nat.card S = 20160 → ∀ r ∈ [r₂, r₃, r₄], ∀ c ∈ S, c * r = r * c → c * c = 1 →
      ∃ s ∈ S, s * r = r * c * s)
    {y : G} (hy : y ∈ normalizer (B : Set G)) (hy2 : y * y = 1)
    (hout : y ∉ B ⊔ centralizer (B : Set G))
    (hns : ¬ Group.IsSolvable ↥(B ⊓ centralizer ({y} : Set G))) :
    ∃ D : Subgroup G, D ≤ B ⊓ centralizer ({y} : Set G) ∧ ⁅D, D⁆ = D ∧
      ∃ c ∈ D, c * c = 1 ∧ c ≠ 1 := by
  obtain ⟨-, h2⟩ := outer_involution_cases hB hZ e hcheck hy hy2 hout
  rcases h2 with h | ⟨hsimple, hnab, hcard⟩
  · exact absurd h hns
  · have hle : B ⊓ centralizer ({y} : Set G) ≤ B := inf_le_left
    let π : ↥(B ⊓ centralizer ({y} : Set G)) →* ↥(centralizerBar B y) :=
      ((QuotientGroup.mk' (center ↥B)).comp (Subgroup.inclusion hle)).codRestrict
        (centralizerBar B y) fun a => ⟨Subgroup.inclusion hle a, a.2, rfl⟩
    have hπ : Function.Surjective π := by
      rintro ⟨_, c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
    have heven : 2 ∣ Nat.card ↥(centralizerBar B y) := by
      rcases hcard with h | h <;> rw [h] <;> decide
    obtain ⟨D, hD, c, hcD, hc2, hc1⟩ := L34.exists_perfect_involution π hπ hnab heven
    refine ⟨D.map (B ⊓ centralizer ({y} : Set G)).subtype, Subgroup.map_subtype_le D, ?_,
      (c : G), ⟨c, hcD, rfl⟩, congrArg Subtype.val hc2, fun h => hc1 (Subtype.ext h)⟩
    rw [← Subgroup.map_commutator, hD]

end CFSG.OddStandard.Seitz77
