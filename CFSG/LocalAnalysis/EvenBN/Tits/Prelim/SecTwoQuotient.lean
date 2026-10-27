module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoTwoGroup
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open

variable {X : Type*} [Group X] [Finite X]

theorem secTwo_odd_card_oddCore : Odd (Nat.card (standardComponentOddCore X)) :=
  CFSG.ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore X

theorem secTwo_oddCore_quotient :
    standardComponentOddCore (X ⧸ standardComponentOddCore X) = ⊥ :=
  CFSG.ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot X

omit [Finite X] in
theorem secTwo_eq_one_of_sq {K : Subgroup X} (hK : Odd (Nat.card K)) {g : X} (hg : g ∈ K)
    (hg2 : g ^ 2 = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg2
  have h2 : orderOf g ∣ Nat.card K := by
    rw [← Subgroup.orderOf_mk g hg]; exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h3 | h3
  · exact orderOf_eq_one_iff.mp h3
  · exfalso; rw [h3] at h2; exact (Nat.not_even_iff_odd.mpr hK) (even_iff_two_dvd.mpr h2)

omit [Finite X] in
theorem secTwo_exists_mem_centralizer {K : Subgroup X} [K.Normal] (hK : Odd (Nat.card K))
    {t g : X} (ht : t * t = 1) (hg : t⁻¹ * (g * t * g⁻¹) ∈ K) :
    ∃ m ∈ K, m * g ∈ centralizer ({t} : Set X) := by
  set k := t⁻¹ * (g * t * g⁻¹) with hkdef
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht]; group
  have hc : (g * t * g⁻¹)⁻¹ = g * t * g⁻¹ := inv_eq_of_mul_eq_one_right h1
  have htk : t * k * t⁻¹ = k⁻¹ := by
    calc t * k * t⁻¹ = (g * t * g⁻¹) * t⁻¹ := by rw [hkdef]; group
      _ = (g * t * g⁻¹)⁻¹ * t := by rw [hc, htinv]
      _ = k⁻¹ := by rw [hkdef]; group
  have hodd : Odd (orderOf k) := by
    have h2 : orderOf k ∣ Nat.card K := by
      rw [← Subgroup.orderOf_mk k hg]; exact orderOf_dvd_natCard _
    obtain ⟨c, hc'⟩ := h2
    rw [hc'] at hK
    exact (Nat.odd_mul.mp hK).1
  obtain ⟨n, hn⟩ := hodd
  set m₀ := k ^ (n + 1) with hm₀
  have hm₀sq : m₀ * m₀ = k := by
    rw [hm₀, ← pow_add, show n + 1 + (n + 1) = orderOf k + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have htm : t * m₀ * t⁻¹ = m₀⁻¹ := by rw [hm₀, ← conj_pow, htk, inv_pow]
  have htm' : t * m₀ = m₀⁻¹ * t := by
    calc t * m₀ = t * m₀ * t⁻¹ * t := by group
      _ = m₀⁻¹ * t := by rw [htm]
  have hgt : g * t * g⁻¹ = t * k := by rw [hkdef]; group
  refine ⟨m₀, pow_mem hg _, mem_centralizer_singleton_iff.mpr ?_⟩
  calc m₀ * g * t = m₀ * (g * t * g⁻¹) * g := by group
    _ = m₀ * (t * k) * g := by rw [hgt]
    _ = m₀ * (t * m₀) * m₀ * g := by rw [← hm₀sq]; group
    _ = m₀ * (m₀⁻¹ * t) * m₀ * g := by rw [htm']
    _ = t * (m₀ * g) := by group

theorem SecTwoHyp.quotient {t u : X} (h : SecTwoHyp X t u) :
    SecTwoHyp (X ⧸ standardComponentOddCore X) (QuotientGroup.mk t) (QuotientGroup.mk u) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := standardComponentOddCore X with hKdef
  have hK : Odd (Nat.card K) := secTwo_odd_card_oddCore
  set π : X →* X ⧸ K := QuotientGroup.mk' K with hπ
  have hπK : ∀ a : X, π a = 1 ↔ a ∈ K := fun a => QuotientGroup.eq_one_iff a
  have hinv1 : ∀ a : X, a ^ 2 = 1 → π a = 1 → a = 1 := fun a ha2 ha =>
    secTwo_eq_one_of_sq hK ((hπK a).mp ha) ha2
  have hz2 := h.z_sq
  have hzt : u ^ 2 * t = t * u ^ 2 := ((h.commute_tu.pow_right 2).eq).symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime (by change π t ^ 2 = 1; rw [← map_pow, h.t_sq, map_one])
      fun h' => h.t_ne_one ?_
    exact hinv1 t h.t_sq h'
  · refine orderOf_eq_prime_pow (p := 2) (n := 1) (fun h' => h.z_ne_one ?_) ?_
    · exact hinv1 _ hz2 (by rw [map_pow]; exact h')
    · change π u ^ 4 = 1; rw [← map_pow, h.u_pow_four, map_one]
  · change π t * π u = π u * π t
    rw [← map_mul, h.commute, map_mul]
  · intro h'
    apply h.sq_ne
    have h2 : π (t⁻¹ * u ^ 2) = 1 := by
      rw [map_mul, map_inv, map_pow]; change (π u) ^ 2 = π t at h'; rw [h', inv_mul_cancel]
    have h3 : (t⁻¹ * u ^ 2) ^ 2 = 1 := by
      rw [sq, show t⁻¹ * u ^ 2 * (t⁻¹ * u ^ 2) = t⁻¹ * (u ^ 2 * t⁻¹) * u ^ 2 by group,
        show u ^ 2 * t⁻¹ = t⁻¹ * u ^ 2 by
          calc u ^ 2 * t⁻¹ = t⁻¹ * (t * u ^ 2) * t⁻¹ := by group
            _ = t⁻¹ * (u ^ 2 * t) * t⁻¹ := by rw [hzt]
            _ = t⁻¹ * u ^ 2 := by group,
        show t⁻¹ * (t⁻¹ * u ^ 2) * u ^ 2 = (t * t)⁻¹ * (u ^ 2 * u ^ 2) by group, h.t_mul_t,
        ← sq, hz2]
      group
    have := hinv1 _ h3 h2
    calc u ^ 2 = t * (t⁻¹ * u ^ 2) := by group
      _ = t := by rw [this, mul_one]
  ·
    set H := centralizer ({t} : Set X) with hH
    have hR2 := h.isPGroup_R
    have hC : centralizer ({π t} : Set (X ⧸ K)) ≤ H.map π := by
      intro y hy
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      rw [mem_centralizer_singleton_iff] at hy
      change π g * π t = π t * π g at hy
      have hg : t⁻¹ * (g * t * g⁻¹) ∈ K := by
        rw [← hπK, map_mul, map_mul, map_mul, map_inv, map_inv]
        change (π t)⁻¹ * (π g * π t * (π g)⁻¹) = 1
        rw [hy]; group
      obtain ⟨m, hm, hmg⟩ := secTwo_exists_mem_centralizer hK h.t_mul_t hg
      exact ⟨m * g, hmg, by rw [map_mul, (hπK m).mpr hm, one_mul]; rfl⟩
    have hRbar : secTwoR (π t) (π u) = (secTwoR t u).map π := by
      rw [secTwoR, secTwoR, MonoidHom.map_closure, Set.image_pair]
    have hRinj : Nat.card ((secTwoR t u).map π) = Nat.card (secTwoR t u) := by
      have hk := Subgroup.card_ker_mul_card_range (π.comp (secTwoR t u).subtype)
      rw [MonoidHom.range_comp, Subgroup.range_subtype] at hk
      have hker : Nat.card (π.comp (secTwoR t u).subtype).ker = 1 := by
        rw [Subgroup.card_eq_one, eq_bot_iff]
        intro r hr
        have hrK : (r : X) ∈ K := (hπK _).mp hr
        obtain ⟨k, hk'⟩ := (IsPGroup.iff_orderOf.mp hR2) r
        have hdvd : orderOf (r : X) ∣ Nat.card K := by
          rw [← Subgroup.orderOf_mk (r : X) hrK]; exact orderOf_dvd_natCard _
        rw [Subgroup.orderOf_coe, hk'] at hdvd
        have hk0 : k = 0 := by
          by_contra hk0
          obtain ⟨c, hc⟩ := hdvd
          rw [hc] at hK
          exact (Nat.not_even_iff_odd.mpr (Nat.odd_mul.mp hK).1)
            ((Nat.even_pow' hk0).mpr even_two)
        rw [hk0, pow_zero] at hk'
        exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hk')
      rw [hker, one_mul] at hk
      exact hk
    have hRH : Nat.card (secTwoR t u) = 2 ^ (Nat.card H).factorization 2 := by
      have := Sylow.card_eq_multiplicity (secTwoSylowOf h.sylow)
      rw [← this]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.R_le_centralizer).toEquiv).symm
    have hHbar : (Nat.card (H.map π)).factorization 2 = (Nat.card H).factorization 2 := by
      have hk := Subgroup.card_ker_mul_card_range (π.comp H.subtype)
      rw [MonoidHom.range_comp, Subgroup.range_subtype] at hk
      have hker : Odd (Nat.card (π.comp H.subtype).ker) := by
        have hdvd : Nat.card (π.comp H.subtype).ker ∣ Nat.card K := by
          let f : (π.comp H.subtype).ker →* K :=
            { toFun := fun x => ⟨(x : H), (hπK _).mp x.2⟩
              map_one' := rfl
              map_mul' := fun _ _ => rfl }
          have hf : Function.Injective f := fun a b hab => by
            have h1 : ((a : H) : X) = ((b : H) : X) := congrArg (fun x : K => (x : X)) hab
            exact Subtype.ext (Subtype.ext h1)
          rw [Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
          exact Subgroup.card_subgroup_dvd_card _
        obtain ⟨c, hc⟩ := hdvd
        rw [hc] at hK
        exact (Nat.odd_mul.mp hK).1
      rw [← hk, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
          (fun h2 => (Nat.not_even_iff_odd.mpr hker) (even_iff_two_dvd.mpr h2)), zero_add]
    refine ⟨?_, ?_, ?_⟩
    · change secTwoR (π t) (π u) ≤ centralizer ({π t} : Set (X ⧸ K))
      rw [hRbar]
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h.commute_t_of_mem_R hr]
    · change IsPGroup 2 (secTwoR (π t) (π u))
      rw [hRbar]; exact hR2.map π
    · intro P hPC hP2 hRP
      change P ≤ centralizer ({π t} : Set (X ⧸ K)) at hPC
      change secTwoR (π t) (π u) ≤ P at hRP
      change P = secTwoR (π t) (π u)
      rw [hRbar] at hRP ⊢
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP2
      have hdvd : Nat.card P ∣ Nat.card (H.map π) := Subgroup.card_dvd_of_le (hPC.trans hC)
      rw [ha] at hdvd
      have hle : a ≤ (Nat.card H).factorization 2 := by
        rw [← hHbar]
        exact (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
      refine (Subgroup.eq_of_le_of_card_ge hRP ?_).symm
      rw [ha, hRinj, hRH]
      exact Nat.pow_le_pow_right (by norm_num) hle

end CFSG.LocalAnalysis.EvenBN.Tits
