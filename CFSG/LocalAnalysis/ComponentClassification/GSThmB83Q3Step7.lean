module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Step6c
public import CFSG.GroupTheory.ThompsonIndexTwo

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X}

namespace L83Hyp

variable {H : L83Hyp h}

namespace Q3Data

variable (d : Q3Data H)
include d

theorem a_not_conj_KE (hq : h.IsQ3) (hF : Cat8.Q3Facts) {k : X} (hkR : k ∈ d.RM)
    (hkK : k ∈ h.K) {e : X} (he : e ∈ d.E) (hke : k * e * (k * e) = 1) (g : X) :
    g⁻¹ * h.a * g ≠ k * e := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  have hnf := d.not_fused hq hF
  have ha1 : h.a ≠ 1 := fun h1 => H.a_not_mem_K hCF1 hCF2 (h1 ▸ one_mem _)
  obtain ⟨e₀, he₀, hee⟩ := d.mem_E_cases he
  have he₀R := d.E0_le_RM he₀
  have hke₀R : k * e₀ ∈ d.RM := mul_mem hkR he₀R
  have hke₀M := d.RM_le hke₀R
  have hke₀K : k * e₀ ∈ h.K := mul_mem hkK (d.E0_le_K hCF1 hCF2 he₀)
  have hke₀2 : k * e₀ * (k * e₀) = 1 := by
    rcases hee with rfl | rfl
    · exact hke
    · have hb1 : k * e₀ * d.b = d.b * (k * e₀) := d.b_comm_of_mem_M3 hke₀M
      have key : k * (e₀ * d.b) * (k * (e₀ * d.b)) = k * e₀ * (k * e₀) * (d.b * d.b) := by
        calc k * (e₀ * d.b) * (k * (e₀ * d.b)) = k * e₀ * (d.b * (k * e₀)) * d.b := by group
          _ = k * e₀ * ((k * e₀) * d.b) * d.b := by rw [hb1]
          _ = k * e₀ * (k * e₀) * (d.b * d.b) := by group
      rw [key, d.b_mul_self, mul_one] at hke
      exact hke
  have hcb : ∀ c : ↥h.M3, (c : X)⁻¹ * d.b * c = d.b := fun c => by
    rw [mul_assoc, ← d.b_comm_of_mem_M3 c.2, inv_mul_cancel_left]
  by_cases h1 : k * e₀ = 1
  ·
    rcases hee with rfl | rfl
    · rw [h1]
      intro h2
      apply ha1
      calc h.a = g * (g⁻¹ * h.a * g) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · rw [← mul_assoc, h1, one_mul]
      exact (hnf g).1
  ·
    set m : ↥h.M3 := ⟨k * e₀, hke₀M⟩ with hm
    have hm2 : m * m = 1 := Subtype.ext hke₀2
    have hv : IsPGroup 2 (zpowers m) := isPGroup_zpowers_of_mul_self hm2
    have hmI : H.rho m ∈ Cat8.Inn (h.K ⧸ pPrimeCore 2 h.K) := (H.mem_K_iff hCF1 hCF2 m).mp hke₀K
    have hrm2 : H.rho m * H.rho m = 1 := by rw [← map_mul, hm2, map_one]
    have hrm1 : H.rho m ≠ 1 := by
      intro h2
      apply h1
      exact d.rho_inj hCF1 hCF2 hke₀R (one_mem _) (h2.trans (map_one _).symm)
    have hz2 : IsPGroup 2 (zpowers (⟨d.z, d.z_mem_M3⟩ : ↥h.M3)) :=
      isPGroup_zpowers_of_mul_self (Subtype.ext d.z_sq)
    have hzt2 : IsPGroup 2 (zpowers (⟨d.z * d.tau, mul_mem d.z_mem_M3 d.tau_mem.2⟩ : ↥h.M3)) := by
      refine isPGroup_zpowers_of_mul_self (Subtype.ext ?_)
      show d.z * d.tau * (d.z * d.tau) = 1
      rw [show d.z * d.tau = d.tau * d.z from (d.tau_comm_z hCF1 hCF2).symm]
      exact d.tz_mul_self hCF1 hCF2
    obtain ⟨c₁, hc₁⟩ := d.exists_z_conj_tz hq hF
    have hzt : d.z * d.tau = d.tau * d.z := (d.tau_comm_z hCF1 hCF2).symm
    rcases d.c_props.inner_classes _ hmI hrm2 hrm1 with ⟨y, -, hy⟩ | ⟨y, -, hy⟩
    ·
      obtain ⟨y', rfl⟩ := H.rho_surjective hq hCF1 hCF2 hF.out y
      obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hz2 hv y' (by rw [← hy, d.c_z])
      have hc' : k * e₀ = (c : X)⁻¹ * d.z * c := congrArg Subtype.val hc
      rcases hee with rfl | rfl
      · intro h2
        apply (hnf (g * (c : X)⁻¹ * c₁)).2.2.1
        calc (g * (c : X)⁻¹ * c₁)⁻¹ * h.a * (g * (c : X)⁻¹ * c₁)
            = c₁⁻¹ * ((c : X) * (g⁻¹ * h.a * g) * (c : X)⁻¹) * c₁ := by group
          _ = c₁⁻¹ * ((c : X) * ((c : X)⁻¹ * d.z * c) * (c : X)⁻¹) * c₁ := by rw [h2, hc']
          _ = c₁⁻¹ * d.z * c₁ := by group
          _ = d.tau * d.z := hc₁
      · intro h2
        apply (hnf (g * (c : X)⁻¹)).2.1
        calc (g * (c : X)⁻¹)⁻¹ * h.a * (g * (c : X)⁻¹)
            = (c : X) * (g⁻¹ * h.a * g) * (c : X)⁻¹ := by group
          _ = (c : X) * (k * e₀ * d.b) * (c : X)⁻¹ := by rw [h2]; group
          _ = (c : X) * ((c : X)⁻¹ * d.z * c * ((c : X)⁻¹ * d.b * c)) * (c : X)⁻¹ := by
              rw [hc', hcb c]
          _ = d.z * d.b := by group
          _ = d.b * d.z := d.b_comm_z.symm
    ·
      obtain ⟨y', rfl⟩ := H.rho_surjective hq hCF1 hCF2 hF.out y
      obtain ⟨c, -, hc⟩ := Eight.exists_conj_eq_of_map hker hzt2 hv y' (by
        rw [← hy, show (⟨d.z * d.tau, mul_mem d.z_mem_M3 d.tau_mem.2⟩ : ↥h.M3) =
          ⟨d.z, d.z_mem_M3⟩ * ⟨d.tau, d.tau_mem.2⟩ from rfl, map_mul, ← d.c_z, d.rho_tau])
      have hc' : k * e₀ = (c : X)⁻¹ * (d.z * d.tau) * c := congrArg Subtype.val hc
      rcases hee with rfl | rfl
      · intro h2
        apply (hnf (g * (c : X)⁻¹)).2.2.1
        calc (g * (c : X)⁻¹)⁻¹ * h.a * (g * (c : X)⁻¹)
            = (c : X) * (g⁻¹ * h.a * g) * (c : X)⁻¹ := by group
          _ = (c : X) * ((c : X)⁻¹ * (d.z * d.tau) * c) * (c : X)⁻¹ := by rw [h2, hc']
          _ = d.z * d.tau := by group
          _ = d.tau * d.z := hzt
      · intro h2
        apply (hnf (g * (c : X)⁻¹ * (h.x * d.g * h.x)⁻¹)).1
        have hxgx := d.b_conj_xgx hq hF
        calc (g * (c : X)⁻¹ * (h.x * d.g * h.x)⁻¹)⁻¹ * h.a *
              (g * (c : X)⁻¹ * (h.x * d.g * h.x)⁻¹)
            = (h.x * d.g * h.x) * ((c : X) * (g⁻¹ * h.a * g) * (c : X)⁻¹) *
                (h.x * d.g * h.x)⁻¹ := by group
          _ = (h.x * d.g * h.x) * ((c : X) * (k * e₀ * d.b) * (c : X)⁻¹) *
                (h.x * d.g * h.x)⁻¹ := by rw [h2]; group
          _ = (h.x * d.g * h.x) * ((c : X) * ((c : X)⁻¹ * (d.z * d.tau) * c *
                ((c : X)⁻¹ * d.b * c)) * (c : X)⁻¹) * (h.x * d.g * h.x)⁻¹ := by
              rw [hc', hcb c]
          _ = (h.x * d.g * h.x) * (d.tau * d.z * d.b) * (h.x * d.g * h.x)⁻¹ := by
              rw [hzt]
              group
          _ = d.b := by rw [← hxgx]; group

theorem map_NME0 (hq : h.IsQ3) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hOut : CFQ3Out) : (d.NME0.subgroupOf h.M3).map H.rho = d.NE0hat := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    exact d.rho_mem_NE0hat hm
  · intro w hw
    obtain ⟨n, hn, rfl⟩ := d.exists_lift_NE0hat hq hCF1 hCF2 hOut hw
    exact mem_map_of_mem _ (show (⟨n, (Subgroup.mem_inf.mp hn).1⟩ : ↥h.M3) ∈
      d.NME0.subgroupOf h.M3 from hn)

theorem exists_k (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ k : X, k ∈ d.RM ∧ k ∈ h.K ∧ k * k = 1 ∧ (∃ e ∈ d.E0, k * e ≠ e * k) ∧
      ∃ k' ∈ ⁅d.NME0, d.NME0⁆, ∃ o : X, k' = k * o ∧ Odd (orderOf o) := by
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  have hker := H.not_two_dvd_card_ker_modelHom hCF1 hCF2
  obtain ⟨ê, hêRI, hêc, hê2, hêC⟩ := d.exists_e_E0hat
  obtain ⟨hêR, hêI⟩ := Subgroup.mem_inf.mp hêRI
  have hêR' := hêR
  rw [d.c_R] at hêR'
  obtain ⟨m, hm, rfl⟩ := mem_map.mp hêR'
  have hmR : (m : X) ∈ d.RM := hm
  have hmK : (m : X) ∈ h.K := (H.mem_K_iff hCF1 hCF2 m).mpr hêI
  have hm2 : (m : X) * m = 1 := by
    refine d.rho_inj hCF1 hCF2 (mul_mem hmR hmR) (one_mem _) ?_
    change H.rho (m * m) = H.rho 1
    rw [map_mul, hê2, map_one]
  refine ⟨m, hmR, hmK, hm2, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hêC
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨e, he, rfl⟩ := d.exists_rh_E0 hw
    exact ((d.comm_iff hCF1 hCF2 hmR (d.E0_le_RM he)).mp (hall e he)).symm
  ·
    rw [← d.map_NME0 hq hCF1 hCF2 hF.out, ← map_commutator] at hêc
    obtain ⟨k', hk', hk'e⟩ := mem_map.mp hêc
    refine ⟨k', ?_, (m : X)⁻¹ * k', by group, ?_⟩
    · have := mem_map_of_mem h.M3.subtype hk'
      rwa [map_commutator, map_subgroupOf_eq_of_le (inf_le_left : d.NME0 ≤ h.M3)] at this
    ·
      have hk1 : m⁻¹ * k' ∈ H.rho.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hk'e, inv_mul_cancel]
      have h1 := Subgroup.orderOf_dvd_natCard _ hk1
      have h2 : orderOf ((m : X)⁻¹ * k') = orderOf (m⁻¹ * k') :=
        (Subgroup.orderOf_coe (m⁻¹ * k'))
      rw [h2]
      exact Odd.of_dvd_nat (Eight.odd_card_ker hker) h1

namespace LClass

variable {d} (L : d.LClass)

theorem sign_πN_commutator {x : X} (hx : x ∈ ⁅d.NME0, d.NME0⁆) :
    ∃ hxN : x ∈ d.NE, Equiv.Perm.sign (L.πN ⟨x, hxN⟩) = 1 := by
  have hle : ⁅d.NME0, d.NME0⁆ ≤ (Equiv.Perm.sign.comp L.πN).ker.map d.NE.subtype := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    refine ⟨⁅(⟨g₁, d.NME0_le_NE hg₁⟩ : ↥d.NE), (⟨g₂, d.NME0_le_NE hg₂⟩ : ↥d.NE)⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  obtain ⟨y, hy, rfl⟩ := hle hx
  exact ⟨y.2, hy⟩

theorem sign_πN_of_odd {o : X} (ho : o ∈ d.NE) (hodd : Odd (orderOf o)) :
    Equiv.Perm.sign (L.πN ⟨o, ho⟩) = 1 := by
  have h1 : Equiv.Perm.sign (L.πN ⟨o, ho⟩) ^ orderOf o = 1 := by
    rw [← map_pow, ← map_pow]
    have : (⟨o, ho⟩ : ↥d.NE) ^ orderOf o = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (L.πN ⟨o, ho⟩)) with h2 | h2
  · exact h2
  · rw [h2, hodd.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem k_props (hq : h.IsQ3) (hF : Cat8.Q3Facts) :
    ∃ k : X, k ∈ d.RM ∧ k ∈ h.K ∧ k * k = 1 ∧ ∃ hkN : k ∈ d.NE, L.πN ⟨k, hkN⟩ ≠ 1 ∧
      Equiv.Perm.sign (L.πN ⟨k, hkN⟩) = 1 := by
  obtain ⟨k, hkR, hkK, hk2, ⟨e, he, hke⟩, k', hk', o, hk'o, hodd⟩ := d.exists_k hq hF
  have hkN : k ∈ d.NE := d.R_le_normalizer_E (d.RM_le_R hkR)
  refine ⟨k, hkR, hkK, hk2, hkN, ?_, ?_⟩
  · intro h1
    exact hke ((L.πN_eq_one_iff ⟨k, hkN⟩).mp h1 e (d.E0_le_E he)).symm
  · obtain ⟨hk'N, hk's⟩ := L.sign_πN_commutator hk'
    have hoN : o ∈ d.NE := by
      have : o = k⁻¹ * k' := by rw [hk'o]; group
      rw [this]
      exact mul_mem (inv_mem hkN) hk'N
    have hos := L.sign_πN_of_odd hoN hodd
    have h1 : (⟨k', hk'N⟩ : ↥d.NE) = ⟨k, hkN⟩ * ⟨o, hoN⟩ := Subtype.ext hk'o
    rw [h1, map_mul, map_mul, hos, mul_one] at hk's
    exact hk's

theorem W_ne (hq : h.IsQ3) (hF : Cat8.Q3Facts) {U : Sylow 2 X} (hRU : d.R ≤ U)
    (hW : ∀ n : ↥d.NE, (n : X) ∈ (U : Subgroup X) → L.πN n ∈ Eight.S6M.Wsub) :
    (U : Subgroup X) ⊓ d.NE ≠ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCF1 := hF.simple
  have hCF2 := hF.inner
  intro hUN
  have hUle : (U : Subgroup X) ≤ d.NE := by
    rw [← hUN]
    exact inf_le_right
  have haU : h.a ∈ (U : Subgroup X) := hRU (d.RM_le_R d.a_mem_RM)
  have haS := L.πa_isSwap hq hF (hW _ haU)
  let ψ : ↥(U : Subgroup X) →* ℤˣ := Equiv.Perm.sign.comp (L.πN.comp (inclusion hUle))
  have hψa : ψ ⟨h.a, haU⟩ = -1 := haS.sign_eq
  set U₀ : Subgroup X := ψ.ker.map (U : Subgroup X).subtype with hU₀
  have hU₀U : U₀ ≤ U := map_subtype_le _
  have hrange : ψ.range = ⊤ := by
    refine eq_top_iff.mpr fun z _ => ?_
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact one_mem _
    · exact ⟨⟨h.a, haU⟩, hψa⟩
  have hidx : U₀.relIndex U = 2 := by
    rw [Subgroup.relIndex, hU₀, show (ψ.ker.map (U : Subgroup X).subtype).subgroupOf
        (U : Subgroup X) = ψ.ker from
        comap_map_eq_self_of_injective (U : Subgroup X).subtype_injective _,
      Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have haU₀ : h.a ∉ U₀ := by
    rintro ⟨y, hy, hya⟩
    have : y = ⟨h.a, haU⟩ := Subtype.ext hya
    rw [this, SetLike.mem_coe, MonoidHom.mem_ker, hψa] at hy
    exact absurd hy (by decide)
  have hsimple : IsSimpleGroup X := H.setting.1
  obtain ⟨u₁, u₂, hu⟩ := H.setting.2.1
  by_cases hconj : ∀ g : X, g⁻¹ * h.a * g ∉ U₀
  · exfalso
    have hmin : ∀ y ∈ (U : Subgroup X), y ∉ U₀ → orderOf h.a ≤ orderOf y := by
      intro y _ hy
      rw [orderOf_eq_prime (by rw [pow_two]; exact Six.a_mul_a_self h)
        (fun h1 => H.a_not_mem_K hCF1 hCF2 (by rw [h1]; exact one_mem _))]
      have hy1 : y ≠ 1 := fun h1 => hy (h1 ▸ one_mem _)
      have h2 := orderOf_pos y
      have h3 : orderOf y ≠ 1 := fun h1 => hy1 (orderOf_eq_one_iff.mp h1)
      omega
    obtain ⟨N, hN, hNidx⟩ := CFSG.ThompsonIndexTwo.exists_normal_index_two_of_thompson
      U.isPGroup' (Sylow.not_dvd_index U) hU₀U hidx haU haU₀ hmin hconj
    have := hsimple
    have := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
    · rw [Subgroup.index_bot] at hNidx
      have : IsCyclic X := isCyclic_of_prime_card hNidx
      exact hu ((IsCyclic.isMulCommutative (α := X)).is_comm.comm u₁ u₂)
    · rw [Subgroup.index_top] at hNidx
      exact absurd hNidx (by norm_num)
  push Not at hconj
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨u₀, hu₀, hu₀a⟩ := hg
  set w : X := g⁻¹ * h.a * g with hw
  have hwU : w ∈ (U : Subgroup X) := hu₀a ▸ u₀.2
  have hwN : w ∈ d.NE := hUle hwU
  have hw2 : w * w = 1 := by
    rw [hw, show g⁻¹ * h.a * g * (g⁻¹ * h.a * g) = g⁻¹ * (h.a * h.a) * g by group,
      Six.a_mul_a_self h, mul_one, inv_mul_cancel]
  have hws : Equiv.Perm.sign (L.πN ⟨w, hwN⟩) = 1 := by
    have : u₀ = ⟨w, hwU⟩ := Subtype.ext hu₀a
    rw [this] at hu₀
    exact hu₀
  by_cases hw1 : L.πN ⟨w, hwN⟩ = 1
  ·
    have hwE := d.mem_E_of_comm hCF1 hCF2 (isPGroup_zpowers_of_mul_self hw2) fun e he =>
      ((L.πN_eq_one_iff ⟨w, hwN⟩).mp hw1 e he).symm
    exact d.a_not_conj_E hq hF g hwE rfl
  ·
    obtain ⟨k, hkR, hkK, hk2, hkN, hk1, hks⟩ := L.k_props hq hF
    have hπw2 : L.πN ⟨w, hwN⟩ * L.πN ⟨w, hwN⟩ = 1 := by
      rw [← map_mul, show (⟨w, hwN⟩ : ↥d.NE) * ⟨w, hwN⟩ = 1 from Subtype.ext hw2, map_one]
    have hπk2 : L.πN ⟨k, hkN⟩ * L.πN ⟨k, hkN⟩ = 1 := by
      rw [← map_mul, show (⟨k, hkN⟩ : ↥d.NE) * ⟨k, hkN⟩ = 1 from Subtype.ext hk2, map_one]
    obtain ⟨σ, hσ⟩ := isConj_iff.mp (Eight.isConj_of_even_involution hπw2 hw1 hws hπk2 hk1 hks)
    obtain ⟨m₁, hm₁⟩ := L.πN_surjective hq hF σ
    set w' : X := (m₁ : X) * w * (m₁ : X)⁻¹ with hw'
    have hw'N : w' ∈ d.NE := mul_mem (mul_mem m₁.2 hwN) (inv_mem m₁.2)
    have hπw' : L.πN ⟨w', hw'N⟩ = L.πN ⟨k, hkN⟩ := by
      rw [show (⟨w', hw'N⟩ : ↥d.NE) = m₁ * ⟨w, hwN⟩ * m₁⁻¹ from rfl, map_mul, map_mul, map_inv,
        hm₁, hσ]
    have hkw : k * w' ∈ d.CNE := by
      have hN : k * w' ∈ d.NE := mul_mem hkN hw'N
      refine Subgroup.mem_inf.mpr ⟨hN, mem_centralizer_iff.mpr fun e he => ?_⟩
      have h1 : L.πN ⟨k * w', hN⟩ = 1 := by
        rw [show (⟨k * w', hN⟩ : ↥d.NE) = ⟨k, hkN⟩ * ⟨w', hw'N⟩ from rfl, map_mul, hπw', hπk2]
      exact (L.πN_eq_one_iff _).mp h1 e he
    have hw'2 : w' * w' = 1 := by
      rw [hw', show (m₁ : X) * w * (m₁ : X)⁻¹ * ((m₁ : X) * w * (m₁ : X)⁻¹) =
        (m₁ : X) * (w * w) * (m₁ : X)⁻¹ by group, hw2, mul_one, mul_inv_cancel]
    obtain ⟨l, hl, e, he, hle⟩ := Eight.exists_conj_mem_mul (C₀ := d.CNE) (E := d.E)
      (fun x hx hx2 => d.mem_E_of_comm hCF1 hCF2 hx2 fun e he =>
        (mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 e he).symm) hk2 hw'2 hkw
    have hke2 : k * e * (k * e) = 1 := by
      rw [← hle, show (l : X) * w' * l⁻¹ * (l * w' * l⁻¹) = l * (w' * w') * l⁻¹ by group, hw'2,
        mul_one, mul_inv_cancel]
    apply d.a_not_conj_KE hq hF hkR hkK he hke2 (g * (l * m₁ : X)⁻¹)
    rw [← hle, hw', hw]
    group

end LClass

end Q3Data

end L83Hyp

end Hyp52

end CFSG.ComponentClassification.GSThmB
