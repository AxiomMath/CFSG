module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFusion
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma42B

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem exists_conj_of_mul_mem {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Nat.Coprime 2 (Nat.card N)) {y y' : G} (hy : y ^ 2 = 1) (hy' : y' ^ 2 = 1)
    (hc : y * y' ∈ N) : ∃ n ∈ N, n * y * n⁻¹ = y' := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq, hy])
  have hy'inv : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right (by rw [← sq, hy'])
  have hconj1 : y * (y * y') * y⁻¹ = (y * y')⁻¹ := by
    rw [hyinv, mul_inv_rev, hyinv, hy'inv, ← mul_assoc, ← sq, hy, one_mul]
  have hconj : ∀ k : ℕ, y * (y * y') ^ k * y⁻¹ = ((y * y') ^ k)⁻¹ := by
    intro k
    rw [← conj_pow, hconj1, inv_pow]
  have hdvd : orderOf (y * y') ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨y * y', hc⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hodd : orderOf (y * y') % 2 = 1 := by
    have hcop : Nat.Coprime 2 (orderOf (y * y')) := Nat.Coprime.coprime_dvd_right hdvd hN
    rcases Nat.even_or_odd (orderOf (y * y')) with he | ho
    · exact absurd (Nat.Coprime.eq_one_of_dvd hcop (even_iff_two_dvd.mp he)) (by norm_num)
    · exact Nat.odd_iff.mp ho
  set m := orderOf (y * y') with hm
  set n := (y * y') ^ ((m - 1) / 2) with hn
  have hn2 : n * n = (y * y')⁻¹ := by
    rw [hn, ← pow_add]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, show (m - 1) / 2 + (m - 1) / 2 + 1 = m by omega, hm, pow_orderOf_eq_one]
  refine ⟨n, pow_mem hc _, ?_⟩
  have hyn : y * n⁻¹ * y⁻¹ = n := by
    have h1 : y * n * y⁻¹ = n⁻¹ := hconj _
    calc y * n⁻¹ * y⁻¹ = (y * n * y⁻¹)⁻¹ := by group
      _ = n := by rw [h1, inv_inv]
  calc n * y * n⁻¹ = n * (y * n⁻¹ * y⁻¹) * y := by group
    _ = n * n * y := by rw [hyn]
    _ = (y * y')⁻¹ * y := by rw [hn2]
    _ = y' := by rw [mul_inv_rev, hyinv, hy'inv, mul_assoc, ← sq, hy, mul_one]

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem exists_conj_mem_X [Finite X] (hKF : AutPSL2FusionInput) (hσ : Setup42 h hS w z)
    {τ : X} (hτT : τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    ∃ g ∈ centralizer ({t} : Set X), g * τ * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := by
  have hτS := hσ.T_le hτT
  have hτH := hS.le hτS
  have hR := h.map_rho_inf_innAut hS
  have hSyl := h.isSylowOf_rho hS
  have hXH : closure {t, w ^ (orderOf w / 2), z} ≤ centralizer ({t} : Set X) :=
    (hσ.X_le_T.trans hσ.T_le).trans hS.le
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have huX : w ^ (orderOf w / 2) ∈ closure {t, w ^ (orderOf w / 2), z} :=
    subset_closure (by simp)
  have hzX : z ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  by_cases h1 : h.rho ⟨τ, hτH⟩ = 1
  ·
    have := h.mem_zpowers_of_rho_eq_one hS hτS h1
    exact ⟨1, one_mem _, by simpa using (zpowers_le.mpr htX) this⟩
  have hτ2' : (⟨τ, hτH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 := Subtype.ext hτ2
  have hρ2 : orderOf (h.rho ⟨τ, hτH⟩) = 2 :=
    orderOf_eq_prime (by rw [← map_pow, hτ2', map_one]) h1
  have hρT : h.rho ⟨τ, hτH⟩ ∈ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := by
    rw [← hσ.map_rho_T]
    exact ⟨⟨τ, hτH⟩, hτT, rfl⟩
  have hzH := hS.le hσ.z_mem.1
  have hzInn : h.rho ⟨z, hzH⟩ ∈ innAut (Bar L) :=
    ⟨QuotientGroup.mk ⟨z, hσ.z_mem.2⟩, (h.rho_of_mem ⟨z, hσ.z_mem.2⟩).symm⟩
  have hιR : h.rho ⟨z, hzH⟩ ∈ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊓ centralizer (((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
        innAut (Bar L) : Subgroup (MulAut (Bar L))) : Set (MulAut (Bar L))) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨⟨⟨z, hzH⟩, hσ.z_mem.1, rfl⟩, hzInn⟩,
      mem_centralizer_iff.mpr fun r hr => ?_⟩
    rw [hR] at hr
    obtain ⟨d, hd, rfl⟩ := hr
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hσ.z_comm_D hd)
  have hz2 : z ^ 2 = 1 := by rw [← hσ.z_order, pow_orderOf_eq_one]
  have hι2 : orderOf (h.rho ⟨z, hzH⟩) = 2 := by
    refine orderOf_eq_prime ?_ fun hz1 => ?_
    · rw [← map_pow]
      have : (⟨z, hzH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 := Subtype.ext hz2
      rw [this, map_one]
    · have hz := h.eq_one_of_mem_zpowers_of_mem
        (h.mem_zpowers_of_rho_eq_one hS hσ.z_mem.1 hz1) hσ.z_mem.2
      have := hσ.z_order
      rw [hz, orderOf_one] at this
      exact absurd this (by norm_num)
  obtain ⟨k, hkK, hk⟩ := hKF (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel h.rho.range h.innAut_le_range _ hSyl.le hSyl.exists_sylow_eq_subgroupOf
    _ hσ.lift.data _ hιR hι2 _ hρT hρ2
  obtain ⟨g, rfl⟩ := hkK
  have hgτ : h.rho ⟨(g : X) * τ * (g : X)⁻¹, mul_mem (mul_mem g.2 hτH) (inv_mem g.2)⟩ =
      h.rho g * h.rho ⟨τ, hτH⟩ * (h.rho g)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have huH := hS.le hσ.u_mem
  have hu2 := hσ.lift.sq_u
  have huz : w ^ (orderOf w / 2) * z = z * w ^ (orderOf w / 2) :=
    (hσ.lift.comm_D z hσ.z_mem).symm
  obtain ⟨x, hxX, hxH, hx2, hρx⟩ : ∃ x ∈ closure {t, w ^ (orderOf w / 2), z},
      ∃ hxH : x ∈ centralizer ({t} : Set X), x ^ 2 = 1 ∧
        h.rho ⟨(g : X) * τ * (g : X)⁻¹, mul_mem (mul_mem g.2 hτH) (inv_mem g.2)⟩ =
          h.rho ⟨x, hxH⟩ := by
    rw [hgτ]
    rcases hk with hk | hk | hk
    · exact ⟨z, hzX, hzH, hz2, hk⟩
    · refine ⟨w ^ (orderOf w / 2), huX, huH, hu2, ?_⟩
      rw [hk, hσ.rho_u]
    · refine ⟨w ^ (orderOf w / 2) * z, mul_mem huX hzX, mul_mem huH hzH, ?_, ?_⟩
      · rw [(show Commute (w ^ (orderOf w / 2)) z from huz).mul_pow, hu2, hz2, one_mul]
      · rw [hk, show (⟨w ^ (orderOf w / 2) * z, mul_mem huH hzH⟩ :
            ↥(centralizer ({t} : Set X))) = ⟨w ^ (orderOf w / 2), huH⟩ * ⟨z, hzH⟩ from rfl,
          map_mul, hσ.rho_u]
  set τ' := (g : X) * τ * (g : X)⁻¹ with hτ'
  have hτ'H : τ' ∈ centralizer ({t} : Set X) := mul_mem (mul_mem g.2 hτH) (inv_mem g.2)
  have hτ'2 : τ' ^ 2 = 1 := by
    rw [hτ', sq, show (g : X) * τ * (g : X)⁻¹ * ((g : X) * τ * (g : X)⁻¹) =
      (g : X) * τ ^ 2 * (g : X)⁻¹ by rw [sq]; group, hτ2, mul_one, mul_inv_cancel]
  have hker : x⁻¹ * τ' ∈ centralizer ({t} : Set X) ⊓ coreActionKernel L := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hxH) hτ'H, ?_⟩
    have h1 : h.rho ⟨x⁻¹ * τ', mul_mem (inv_mem hxH) hτ'H⟩ = 1 := by
      rw [show (⟨x⁻¹ * τ', mul_mem (inv_mem hxH) hτ'H⟩ : ↥(centralizer ({t} : Set X))) =
        (⟨x, hxH⟩)⁻¹ * ⟨τ', hτ'H⟩ from rfl, map_mul, map_inv, hρx, inv_mul_cancel]
    exact (h.mem_ker_rho _).mp h1
  rw [h.dihedral.kernel_eq] at hker
  have hOn : (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
      ≤ normalizer (zpowers t : Set X) := by
    rintro _ ⟨o, -, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact ((Commute.zpow_right (mem_centralizer_singleton_iff.mp o.2) j)).eq.symm
  have hker' : x⁻¹ * τ' ∈ ((pPrimeCore 2 ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype : Set X) * (zpowers t : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hOn]
    exact hker
  obtain ⟨_, ⟨o, ho, rfl⟩, _, ⟨j, rfl⟩, hoj⟩ := hker'
  beta_reduce at hoj
  have hxt : Commute x (t ^ j) :=
    (show Commute x t from mem_centralizer_singleton_iff.mp hxH).zpow_right j
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have htj2 : (t ^ j) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hy2 : (x * t ^ j) ^ 2 = 1 := by rw [hxt.mul_pow, hx2, htj2, one_mul]
  have hot : Commute (o : X) (t ^ j) :=
    (show Commute (o : X) t from mem_centralizer_singleton_iff.mp o.2).zpow_right j
  have hoj' : (o : X) * t ^ j = x⁻¹ * τ' := hoj
  have hyτ' : x * t ^ j * τ' = (o : X) := by
    have hτ'e : τ' = x * ((o : X) * t ^ j) := by rw [hoj']; group
    rw [hτ'e, show x * t ^ j * (x * ((o : X) * t ^ j)) =
      (t ^ j * x) * x * ((o : X) * t ^ j) by rw [hxt.eq]; group]
    rw [mul_assoc (t ^ j) x x, ← sq, hx2, mul_one, hot.eq, ← mul_assoc, ← sq, htj2, one_mul]
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype)) := by
    rw [Subgroup.card_map_of_injective (centralizer ({t} : Set X)).subtype_injective]
    exact pPrimeCore_coprime_card
  obtain ⟨n, hnO, hn⟩ := exists_conj_of_mul_mem hcop hy2 hτ'2 (by rw [hyτ']; exact ⟨o, ho, rfl⟩)
  have hnH : n ∈ centralizer ({t} : Set X) := by
    obtain ⟨o', -, rfl⟩ := hnO
    exact o'.2
  refine ⟨n⁻¹ * g, mul_mem (inv_mem hnH) g.2, ?_⟩
  have : n⁻¹ * (g : X) * τ * (n⁻¹ * (g : X))⁻¹ = x * t ^ j := by
    calc n⁻¹ * (g : X) * τ * (n⁻¹ * (g : X))⁻¹ = n⁻¹ * τ' * n := by rw [hτ']; group
      _ = n⁻¹ * (n * (x * t ^ j) * n⁻¹) * n := by rw [hn]
      _ = x * t ^ j := by group
  rw [this]
  exact mul_mem hxX (zpow_mem htX j)

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit
