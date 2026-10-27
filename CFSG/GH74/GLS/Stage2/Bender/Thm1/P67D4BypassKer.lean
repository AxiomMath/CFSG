module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutCrit
public import CFSG.Certificates.Kernel.ThDemp.OrbCent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

theorem d4PtKer_of_inner_trivial {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ e : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hinner : ∀ ζ ∈ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range, Odd (orderOf ζ) →
      Nat.Coprime (orderOf ζ) 3 → ζ * φ = φ * ζ → ζ * e = e * ζ →
        (∀ c ∈ fixSub φ, ζ c = c) → ζ = 1)
    (U₀ : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hU : U₀ ≤ fixSub φ)
    (hUp : IsPGroup p U₀) (hcard : (p ^ f) ^ 3 ≤ Nat.card U₀)
    (ζ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hodd : Odd (orderOf ζ))
    (hcop : Nat.Coprime (orderOf ζ) 3) (hcomm : ζ * φ = φ * ζ) (hcomme : ζ * e = e * ζ)
    (hfix : ∀ c ∈ fixSub φ, ζ c = c) : ζ = 1 := by
  classical
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, ⟨Θ, hΘ, -, hΘker, -⟩, -, hcardAut, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpowcomm : ∀ n : ℕ, ζ ^ n * φ = φ * ζ ^ n := fun n =>
    (Commute.pow_left (show Commute ζ φ from hcomm) n).eq
  have hpowcomme : ∀ n : ℕ, ζ ^ n * e = e * ζ ^ n := fun n =>
    (Commute.pow_left (show Commute ζ e from hcomme) n).eq
  have hpowfix : ∀ n : ℕ, ∀ c ∈ fixSub φ, (ζ ^ n) c = c := by
    intro n
    induction n with
    | zero => intro c _; rw [pow_zero]; rfl
    | succ n ih => intro c hc; rw [pow_succ, MulAut.mul_apply, hfix c hc, ih c hc]
  set m := orderOf (Θ ζ) with hm
  have hζm : ζ ^ m = 1 := by
    have h1 : Θ (ζ ^ m) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
    have hmem : ζ ^ m ∈ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := by rw [← hΘker]; exact h1
    have hdv : orderOf (ζ ^ m) ∣ orderOf ζ := orderOf_pow_dvd m
    exact hinner _ hmem (Odd.of_dvd_nat hodd hdv) (Nat.Coprime.coprime_dvd_left hdv hcop)
      (hpowcomm m) (hpowcomme m) (hpowfix m)
  have hmdvd : m ∣ orderOf ζ := orderOf_map_dvd Θ ζ
  have hzord : orderOf ζ = m := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hζm) hmdvd
  by_cases hm1 : m = 1
  · rw [hm1, pow_one] at hζm
    exact hζm
  exfalso
  have hm0 : 0 < m := orderOf_pos _
  have hmodd : Odd m := hzord ▸ hodd
  have hmcop : Nat.Coprime m 3 := hzord ▸ hcop
  set r := Nat.minFac m with hrdef
  have hr : r.Prime := Nat.minFac_prime hm1
  have hrm : r ∣ m := Nat.minFac_dvd m
  have hr2 : r ≠ 2 := fun h => by
    rw [h] at hrm
    exact (Nat.not_even_iff_odd.2 hmodd) (even_iff_two_dvd.2 hrm)
  have hr3' : r ≠ 3 := fun h => by
    rw [h] at hrm
    exact absurd (Nat.Coprime.eq_one_of_dvd hmcop.symm hrm) (by norm_num)
  have hr3 : 3 < r := by have := hr.two_le; omega
  have hdiv : m / r ∣ m := Nat.div_dvd_of_dvd hrm
  have hdpos : 0 < m / r := Nat.div_pos (Nat.le_of_dvd hm0 hrm) hr.pos
  set ζ' := ζ ^ (m / r) with hζ'
  have hζ'ord : orderOf ζ' = r := by
    rw [hζ', orderOf_pow_of_dvd hdpos.ne' (hzord ▸ hdiv), hzord, Nat.div_div_self hrm hm0.ne']
  have hζ'out : ζ' ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range := by
    intro hmem
    rw [← hΘker, MonoidHom.mem_ker, hζ', map_pow] at hmem
    have h1 := orderOf_dvd_of_pow_eq_one hmem
    have h2 : m / r < m := Nat.div_lt_self hm0 hr.one_lt
    exact absurd (Nat.le_of_dvd hdpos h1) (by omega)
  obtain ⟨hηord, hrf, ⟨g₀, hg₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hp hf K hK σ hσ Θ hΘ hr hr3
      ⊤ le_top ⟨ζ', Subgroup.mem_top _⟩ hζ'out (by rw [Subgroup.orderOf_mk]; exact hζ'ord)
  obtain ⟨M, hpM, hMcard⟩ := d4_card_fixSub_fieldActor hp hp2 hf hr hr3 hrf K hK σ hσ (Θ ζ') hηord
  have hU₁ : U₀.map (MulAut.conj g₀).toMonoidHom ≤
      fixSub (fieldActor (t := TwistTag.D4) σ (Θ ζ')) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixSub, ← hg₀]
    have hxfix := hpowfix (m / r) x (hU hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.mul_apply, MulAut.inv_apply_self]
    rw [show ζ' x = x from hxfix]
  obtain ⟨a, ha⟩ := hUp.exists_card_eq
  have hcardU₁ : Nat.card (U₀.map (MulAut.conj g₀).toMonoidHom) = Nat.card U₀ :=
    (Nat.card_congr (Subgroup.equivMapOfInjective U₀ (MulAut.conj g₀).toMonoidHom
      (MulAut.conj g₀).injective).toEquiv).symm
  have hdvd := Subgroup.card_dvd_of_le hU₁
  rw [hcardU₁, ha, hMcard] at hdvd
  have hcopM : Nat.Coprime (p ^ a) M :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  have hdvd2 : p ^ a ∣ (p ^ (f / r)) ^ 12 := hcopM.dvd_of_dvd_mul_right hdvd
  rw [← pow_mul] at hdvd2
  have hle : a ≤ f / r * 12 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd2
  have h3f : f * 3 ≤ a := by
    rw [ha, ← pow_mul] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hcard
  obtain ⟨d, hd⟩ := hrf
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · rw [h0, mul_zero] at hd
      omega
    · exact h0
  have hr5 : 5 ≤ r := by
    by_contra h
    have h4 : r = 4 := by omega
    rw [h4] at hr
    exact absurd hr (by norm_num)
  rw [hd, Nat.mul_div_cancel_left d hr.pos] at hle
  rw [hd] at h3f
  nlinarith

end CFSG.GH74.GLS.Stage2.Bender.Thm1
