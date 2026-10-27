module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Three
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiLocalGraph
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFi22Five

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Local

open CFSG.Sporadic.Fi23


theorem fi23_local_d_five {s : J} (hs : orderOf s = 5) (hsd : s * d = d * s) (x : J)
    (hx : x ∈ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set J))) (hxd : x * d = d * x) :
    x = 1 ∨ x = d := by
  set N := GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set J)) with hN
  set M : Subgroup Cd := (N ⊓ Cd).subgroupOf Cd with hM
  set s₀ : Cd := ⟨s, mem_Cd.2 hsd⟩ with hs₀
  have hs5 : s ^ 5 = 1 := hs ▸ pow_orderOf_eq_one s
  have hs₀5 : s₀ ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hs5)
  have hdd : dCd * dCd = 1 := Subtype.ext d_sq
  have hker : ∀ u : Cd, rho u = 1 → u = 1 ∨ u = dCd := fun u hu =>
    eq_one_or_eq_of_mem_zpowers hdd (by rw [← ker_rho]; exact hu)
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.1
    (show rho s₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨s₀, rfl⟩)
  have ht5 : t ^ 5 = 1 := by
    apply pi22_injective
    rw [map_pow, ht, ← map_pow, hs₀5, map_one, map_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : rho s₀ = 1 := by rw [← ht, h, map_one]
    rcases hker s₀ h1 with h2 | h2
    · have h3 : s = 1 := congrArg Subtype.val h2
      rw [h3, orderOf_one] at hs
      exact absurd hs (by norm_num)
    · have h3 : s = d := congrArg Subtype.val h2
      rw [h3, orderOf_d] at hs
      exact absurd hs (by norm_num)
  have hto : orderOf t = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime ht5 ht1
  set K : Subgroup CFSG.Sporadic.Fi22.J := (M.map rho).comap pi22 with hK
  have hKC : K ≤ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Fi22.J) := by
    intro k hk
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    have hmN : (m : J) ∈ N := (Subgroup.mem_subgroupOf.1 hm).1
    have hms : (m : J) * s = s * (m : J) :=
      (Subgroup.mem_centralizer_singleton_iff (g := s)).1 (GLAPPrimeCoreOf_le _ hmN)
    have hms₀ : m * s₀ = s₀ * m := Subtype.ext hms
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply pi22_injective
    rw [map_mul, map_mul, ← hmk, ht, ← map_mul, ← map_mul, hms₀]
  have hKn : ∀ y ∈ Subgroup.centralizer ({t} : Set CFSG.Sporadic.Fi22.J), ∀ k ∈ K,
      y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 (pi22_mem_range y)
    have hyt : y * t = t * y := (Subgroup.mem_centralizer_singleton_iff (g := t)).1 hy
    have hu : rho (g * s₀ * g⁻¹ * s₀⁻¹) = 1 := by
      have e : y * t * y⁻¹ * t⁻¹ = 1 := by rw [hyt, mul_inv_cancel_right, mul_inv_cancel]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg, ← ht, ← map_inv pi22 y,
        ← map_inv pi22 t, ← map_mul pi22, ← map_mul pi22, ← map_mul pi22, e, map_one]
    have hgC : (g : J) ∈ Subgroup.centralizer ({s} : Set J) := by
      rcases hker _ hu with h | h
      · have h' := congrArg Subtype.val h
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, Subgroup.coe_one, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h'
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h'
      · exfalso
        have h' := congrArg Subtype.val h
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.coe_inv, dCd_val, mul_inv_eq_iff_eq_mul] at h'
        exact d_ne_one (@eq_one_of_conj_eq_mul_of_odd J (inferInstance : Group J) d s (g : J)
          hsd.symm d_sq 2 hs5 h')
    obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hk)
    have hmN : (m : J) ∈ N := (Subgroup.mem_subgroupOf.1 hm).1
    have hgmN : ((g * m * g⁻¹ : Cd) : J) ∈ N := by
      have := GLAPPrimeCoreOf_conj_mem (g : J) hgC _ hmN
      simpa using this
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨g * m * g⁻¹,
      Subgroup.mem_subgroupOf.2 ⟨hgmN, (g * m * g⁻¹).2⟩, ?_⟩)
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hg, hmk]
  have hKcop : Nat.Coprime 5 (Nat.card K) := by
    have h1 : Nat.card K = Nat.card (K.map pi22) :=
      (Subgroup.card_map_of_injective pi22_injective).symm
    have h3 : Nat.card (K.map pi22) ∣ Nat.card (M.map rho) :=
      Subgroup.card_dvd_of_le (Subgroup.map_comap_le _ _)
    have h4 : Nat.card (M.map rho) ∣ Nat.card M := Subgroup.card_map_dvd M rho
    have h5 : Nat.card M = Nat.card ↥(N ⊓ Cd) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    have h6 : Nat.card ↥(N ⊓ Cd) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hcop := coprime_card_GLAPPrimeCoreOf Nat.prime_five
      (Subgroup.centralizer ({s} : Set J))
    rw [h1]
    rw [h5] at h4
    exact Nat.Coprime.coprime_dvd_right (h3.trans (h4.trans h6)) hcop
  have hKle := le_GLAPPrimeCoreOf_of_normal hKC hKn hKcop
  rw [oPrimeCoreTrivialAt_Fi22J_five t hto] at hKle
  set x₀ : Cd := ⟨x, mem_Cd.2 hxd⟩ with hx₀
  have hx₀M : x₀ ∈ M := Subgroup.mem_subgroupOf.2 ⟨hx, x₀.2⟩
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1
    (show rho x₀ ∈ pi22.range by rw [← range_rho]; exact MonoidHom.mem_range.2 ⟨x₀, rfl⟩)
  have hkK : k ∈ K := Subgroup.mem_comap.2 (by rw [hk]; exact Subgroup.mem_map_of_mem rho hx₀M)
  have hk1 : k = 1 := Subgroup.mem_bot.1 (hKle hkK)
  have hρ : rho x₀ = 1 := by rw [← hk, hk1, map_one]
  rcases hker x₀ hρ with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem fi23_local_five {s : J} (hs : orderOf s = 5) {e : J} (he : e ∈ D23)
    (hes : e * s = s * e) (n : J)
    (hn : n ∈ GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set J)))
    (hne : n * e = e * n) : n = 1 ∨ n = e := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (show IsConj d e from he)
  have hs' : orderOf (g⁻¹ * s * g) = 5 := by
    have h := CFSG.Sporadic.Fi23.orderOf_conj g⁻¹ s
    rw [inv_inv] at h
    rw [h, hs]
  have hs'd : g⁻¹ * s * g * d = d * (g⁻¹ * s * g) := by
    rw [← hg] at hes
    calc g⁻¹ * s * g * d = g⁻¹ * (s * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * s) * g := by rw [hes]
      _ = d * (g⁻¹ * s * g) := by group
  have hn' := @conj_mem_gLAPPrimeCoreOf_centralizer J (inferInstance : Group J) 5 g⁻¹ s n hn
  rw [inv_inv] at hn'
  have hn'd : g⁻¹ * n * g * d = d * (g⁻¹ * n * g) := by
    rw [← hg] at hne
    calc g⁻¹ * n * g * d = g⁻¹ * (n * (g * d * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * d * g⁻¹ * n) * g := by rw [hne]
      _ = d * (g⁻¹ * n * g) := by group
  rcases fi23_local_d_five hs' hs'd _ hn' hn'd with h | h
  · left
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc n = g * (g⁻¹ * n * g) * g⁻¹ := by group
      _ = e := by rw [h, hg]

theorem gLAPPrimeCoreOf_fi23_five_eq_bot {s : J} (hs : orderOf s = 5)
    (hT0 : ∃ e ∈ D23, e * s = s * e)
    (hT1 : ∀ x ∈ D23, x * s = s * x → ∃ y ∈ D23, y * s = s * y ∧ y ≠ x ∧ x * y = y * x)
    (hT2 : ∀ x ∈ D23, x * s = s * x → ∀ y ∈ D23, y * s = s * y → x * y ≠ y * x →
      ∃ z ∈ D23, z * s = s * z ∧ z * x = x * z ∧ z * y = y * z) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer ({s} : Set J)) = ⊥ :=
  @gLAPPrimeCoreOf_eq_bot_of_fixed_graph J (inferInstance : Group J) inferInstance D23 5
    (fun x hx => D23_mul_self hx) (fun x hx => D23_ne_one hx)
    (fun x hx y hy hxy => D23_cube hx hy hxy) (fun x hx g => D23_conj hx g) s hT0 hT1 hT2
    (fun x hx hxs n hn hnx => fi23_local_five hs hx hxs n hn hnx)

end Local

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
