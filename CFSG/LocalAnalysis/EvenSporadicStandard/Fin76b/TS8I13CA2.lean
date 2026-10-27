module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CA
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CB

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c in
theorem z_conj_yz_inv {y : G} (hy2 : y * y = 1) : z * (y * z) * z⁻¹ = (y * z)⁻¹ := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right c.h.z_sq
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  calc z * (y * z) * z⁻¹ = z * y := by group
    _ = (y * z)⁻¹ := by rw [mul_inv_rev, hzi, hyi]

theorem rho_snd_eq_inv {r : G} (hr : r ∈ c.N1) (hzr : z * r * z⁻¹ = r⁻¹) :
    (c.rho ⟨r, hr⟩).2 = (c.rho ⟨r, hr⟩).1⁻¹ := by
  have hzn : c.zconjN1 ⟨r, hr⟩ = (⟨r, hr⟩ : ↥c.N1)⁻¹ := Subtype.ext (by
    rw [zconjN1_coe, Subgroup.coe_inv]
    exact hzr)
  have h := c.rho_zconj ⟨r, hr⟩
  rw [hzn, map_inv] at h
  exact (congrArg Prod.fst h).symm

variable {c}

theorem IsRs.mul_z_mem {Rs : Subgroup G} (hR : c.IsRs Rs) {y : G} (hy : y ∈ Rs)
    (hyR : y ∉ Rs ⊓ c.N1) : y * z ∈ Rs ⊓ c.N1 := by
  have hidx : ((Rs ⊓ c.N1).subgroupOf Rs).index = 2 := hR.relIndex_R.1
  have hzR : z ∉ Rs ⊓ c.N1 := hR.relIndex_R.2
  have h2 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : ↥Rs))
    (b := (⟨z, hR.z_mem⟩ : ↥Rs))).2 ⟨fun h => absurd h hyR, fun h => absurd h hzR⟩
  exact h2

theorem IsRs.exists_conj_of_odd {Rs : Subgroup G} (hR : c.IsRs Rs) (hTRs : T ≤ Rs)
    {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    {y : G} (hy2 : y * y = 1) (hr : y * z ∈ Rs ⊓ c.N1)
    (hodd : Equiv.Perm.sign (π (c.rho ⟨y * z, hr.2⟩).1) ≠ 1) :
    ∃ u ∈ Rs ⊓ c.N1, y = u * (z * σ) * u⁻¹ := by
  have hzz : z * z = 1 := c.h.z_sq
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hrN : y * z ∈ c.N1 := hr.2
  have hrR : y * z ∈ Rs ⊓ c.N1 := hr
  have hρ2 : (c.rho ⟨y * z, hrN⟩).2 = (c.rho ⟨y * z, hrN⟩).1⁻¹ :=
    c.rho_snd_eq_inv hrN (c.z_conj_yz_inv hy2)
  obtain ⟨a, ha⟩ : ∃ a : MulAut ↥E, (c.rho ⟨y * z, hrN⟩).1 = a := ⟨_, rfl⟩
  rw [ha] at hρ2 hodd
  have hρr : c.rho ⟨y * z, hrN⟩ = (a, a⁻¹) := Prod.ext ha hρ2
  have hmem_a : (a, a⁻¹) ∈ c.Rhat (Rs ⊓ c.N1) :=
    c.mem_Rhat.2 ⟨⟨y * z, hrN⟩, hrR, hρr⟩
  obtain ⟨u₀', hu₀R, hu₀⟩ := c.mem_Rhat.1 (hR.Rhat_mem_odd hTRs hπ hA hmem_a hodd)
  obtain ⟨s, hs⟩ : ∃ s : MulAut ↥E, convN ⟨σ, c.hσ.norm_E⟩ = s := ⟨_, rfl⟩
  rw [hs] at hu₀
  have hss : s * s = 1 := by
    rw [← hs, ← convN_mul]
    have e : (⟨σ, c.hσ.norm_E⟩ * ⟨σ, c.hσ.norm_E⟩ : normalizer (E : Set G)) = 1 :=
      Subtype.ext c.hσ.sq
    rw [e]
    exact map_one _
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hρσ : c.rho ⟨σ, c.sigma_mem_N1⟩ = (s, s) := by
    rw [c.rho_sigma, hs]
  have hρz : c.rho (c.zconjN1 u₀') = (1, a * s) := by
    rw [c.rho_zconj, hu₀]
  have hσR : σ ∈ Rs ⊓ c.N1 := ⟨hTRs c.hσ.mem_T, c.sigma_mem_N1⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ↥c.N1, W = u₀' * ⟨σ, c.sigma_mem_N1⟩ * (c.zconjN1 u₀')⁻¹ :=
    ⟨_, rfl⟩
  have hWcoe : (W : G) = (u₀' : G) * σ * (z * (u₀' : G) * z⁻¹)⁻¹ := by
    rw [hWdef]
    rfl
  have hWR : (W : G) ∈ Rs ⊓ c.N1 := by
    rw [hWcoe]
    exact mul_mem (mul_mem hu₀R hσR) (inv_mem (hR.z_conj_R hu₀R))
  have hρW : c.rho W = (a, a⁻¹) := by
    rw [hWdef, map_mul, map_mul, map_inv, hu₀, hρσ, hρz]
    have e1 : a * s * s = a := by rw [mul_assoc, hss, mul_one]
    have e2 : s * (a * s)⁻¹ = a⁻¹ := by
      rw [mul_inv_rev, hsi, ← mul_assoc, hss, one_mul]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.fst_inv, inv_one, mul_one]
      exact e1
    · simp only [Prod.snd_mul, Prod.snd_inv, one_mul]
      exact e2
  obtain ⟨k, hkdef⟩ : ∃ k : G, k = (y * z)⁻¹ * (W : G) := ⟨_, rfl⟩
  have hkN : k ∈ c.N1 := by
    rw [hkdef]
    exact mul_mem (inv_mem hrN) W.2
  have hρk : c.rho ⟨k, hkN⟩ = 1 := by
    have e : (⟨k, hkN⟩ : ↥c.N1) = (⟨y * z, hrN⟩ : ↥c.N1)⁻¹ * W := Subtype.ext hkdef
    rw [e, map_mul, map_inv, hρr, hρW, inv_mul_cancel]
  have hkRs : k ∈ Rs := by
    rw [hkdef]
    exact mul_mem (inv_mem (Subgroup.mem_inf.1 hrR).1) (Subgroup.mem_inf.1 hWR).1
  have hkR : k ∈ Rs ⊓ c.N1 := Subgroup.mem_inf.2 ⟨hkRs, hkN⟩
  have hkZ : k ∈ c.Zs := hR.R_inf_KR_le ⟨hkR, c.mem_KR.2 ⟨hkN, hρk⟩⟩
  have hWk : (W : G) = (y * z) * k := by
    rw [hkdef]
    group
  have hu_eq : (u₀' : G) * (z * σ) * (u₀' : G)⁻¹ = y * z * k * z := by
    calc (u₀' : G) * (z * σ) * (u₀' : G)⁻¹ = (u₀' : G) * (σ * z) * (u₀' : G)⁻¹ := by
          rw [c.hσ.comm_z]
      _ = (W : G) * z := by
          rw [hWcoe]
          group
      _ = y * z * k * z := by rw [hWk]
  have hzσ : (z * σ) * (z * σ) = 1 := by
    calc (z * σ) * (z * σ) = z * (σ * z) * σ := by group
      _ = z * (z * σ) * σ := by rw [c.hσ.comm_z]
      _ = (z * z) * (σ * σ) := by group
      _ = 1 := by rw [hzz, c.hσ.sq, mul_one]
  have hinv : (y * z * k * z) * (y * z * k * z) = 1 := by
    rw [← hu_eq]
    calc (u₀' : G) * (z * σ) * (u₀' : G)⁻¹ * ((u₀' : G) * (z * σ) * (u₀' : G)⁻¹)
        = (u₀' : G) * ((z * σ) * (z * σ)) * (u₀' : G)⁻¹ := by group
      _ = 1 := by rw [hzσ]; group
  have hrk : y * z * k = k * (y * z) := c.Zs_comm_N1 hkZ hrN
  have hrkr : y * z * k * (y * z)⁻¹ = k := by
    rw [hrk]
    group
  have hzr' : z * (y * z) = (y * z)⁻¹ * z := by
    calc z * (y * z) = (z * (y * z) * z⁻¹) * z := by group
      _ = (y * z)⁻¹ * z := by rw [c.z_conj_yz_inv hy2]
  have hkz : k * z * (k * z) = 1 := by
    calc k * z * (k * z) = k * (z * k * z) := by group
      _ = ((y * z) * k * (y * z)⁻¹) * (z * k * z) := by rw [hrkr]
      _ = (y * z) * k * ((y * z)⁻¹ * z) * k * z := by group
      _ = (y * z) * k * (z * (y * z)) * k * z := by rw [hzr']
      _ = (y * z * k * z) * (y * z * k * z) := by group
      _ = 1 := hinv
  rcases c.eq_one_or_t_of_sq hkZ hkz with hk | hk
  ·
    refine ⟨(u₀' : G), hu₀R, ?_⟩
    rw [hu_eq, hk, mul_one, mul_assoc, hzz, mul_one]
  ·
    refine ⟨α * (u₀' : G), mul_mem (hR.Zs_le_R c.alpha_mem_Zs) hu₀R, ?_⟩
    have hαr : y * z * α = α * (y * z) := c.Zs_comm_N1 c.alpha_mem_Zs hrN
    have hαt : α * t = t * α := c.h.t_comm_S α c.hα.mem
    have hαrt : α * (y * z * t) * α⁻¹ = y * z * t := by
      have e : α * (y * z * t) = (y * z * t) * α := by
        calc α * (y * z * t) = (α * (y * z)) * t := by group
          _ = (y * z * α) * t := by rw [hαr]
          _ = (y * z) * (α * t) := by group
          _ = (y * z) * (t * α) := by rw [hαt]
          _ = (y * z * t) * α := by group
      rw [e]
      group
    calc y = (y * z) * z := by rw [mul_assoc, hzz, mul_one]
      _ = (y * z) * (t * t) * z := by rw [c.h.t_sq, mul_one]
      _ = ((y * z) * t) * (t * z) := by group
      _ = (α * ((y * z) * t) * α⁻¹) * (α * z * α⁻¹) := by rw [hαrt, ← c.t_mul_z]
      _ = α * ((y * z) * t * z) * α⁻¹ := by group
      _ = α * ((u₀' : G) * (z * σ) * (u₀' : G)⁻¹) * α⁻¹ := by rw [hu_eq, hk]
      _ = α * (u₀' : G) * (z * σ) * (α * (u₀' : G))⁻¹ := by group

theorem caseA_final {π : MulAut ↥E →* Equiv.Perm (Fin 5)} (hπ : EPi E π)
    (hA : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔ Equiv.Perm.sign (π a) = Equiv.Perm.sign (π b))
    (hE : EFacts614 E t) (hT : Nat.card T ≤ 512)
    (hX3 : ¬ ∃ g : G, g * z * g⁻¹ = z * σ) :
    ∃ Rs R : Subgroup G, IsPGroup 2 Rs ∧ R ≤ Rs ∧ R.relIndex Rs = 2 ∧ z ∈ Rs ∧ z ∉ R ∧
      (∀ g : G, g * z * g⁻¹ ∈ Rs → ∃ r ∈ Rs, g * z * g⁻¹ = r * z * r⁻¹) ∧
      ¬ 2 ∣ Rs.relIndex (centralizer ({z} : Set G)) := by
  obtain ⟨Rs, hR, hTRs⟩ := c.exists_isRs
  have hbig := c.hbigA hA hE
  refine ⟨Rs, Rs ⊓ c.N1, hR.pgroup, inf_le_left, hR.relIndex_R.1, hR.z_mem, hR.relIndex_R.2,
    ?_, ?_⟩
  · intro g hg
    have hgg : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
      calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [c.h.z_sq]; group
    by_cases hgR : g * z * g⁻¹ ∈ Rs ⊓ c.N1
    · exact (hR.not_conj_z_of_mem_R hbig hT hgR hgg ⟨g, rfl⟩).elim
    · obtain ⟨y, hydef⟩ : ∃ y : G, y = g * z * g⁻¹ := ⟨_, rfl⟩
      rw [← hydef] at hg hgR hgg
      have hr : y * z ∈ Rs ⊓ c.N1 := hR.mul_z_mem hg hgR
      have hρ2 : (c.rho ⟨y * z, hr.2⟩).2 = (c.rho ⟨y * z, hr.2⟩).1⁻¹ :=
        c.rho_snd_eq_inv hr.2 (c.z_conj_yz_inv hgg)
      have hmem : ((c.rho ⟨y * z, hr.2⟩).1, (c.rho ⟨y * z, hr.2⟩).1⁻¹) ∈
          c.Rhat (Rs ⊓ c.N1) :=
        c.mem_Rhat.2 ⟨⟨y * z, hr.2⟩, hr, Prod.ext rfl hρ2⟩
      by_cases hev : Equiv.Perm.sign (π (c.rho ⟨y * z, hr.2⟩).1) = 1
      ·
        have ha : ∀ r : G, ∀ hr' : r ∈ Rs ⊓ c.N1, y * z = r →
            ((c.rho ⟨r, hr'.2⟩).1, (1 : MulAut ↥E)) ∈ c.Rhat (Rs ⊓ c.N1) := by
          rintro r hr' rfl
          exact hR.Rhat_mem_even hπ hA hmem hev
        obtain ⟨u, hu, hueq⟩ := hR.exists_conj_of_not_mem_R hg hgR hgg ha
        refine ⟨u, hu.1, ?_⟩
        rw [← hydef]
        exact hueq
      ·
        obtain ⟨u, hu, hueq⟩ := hR.exists_conj_of_odd hTRs hπ hA hgg hr hev
        exfalso
        apply hX3
        refine ⟨u⁻¹ * g, ?_⟩
        calc u⁻¹ * g * z * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * z * g⁻¹) * u := by group
          _ = u⁻¹ * y * u := by rw [hydef]
          _ = u⁻¹ * (u * (z * σ) * u⁻¹) * u := by rw [hueq]
          _ = z * σ := by group
  · have hcard : Nat.card T ≤ Nat.card ↥(Rs ⊓ centralizer ({z} : Set G)) :=
      Subgroup.card_le_of_le (le_inf hTRs c.h.oe.cfg.T_le)
    exact c.h.relIndex_cent_z_odd hR.pgroup hcard

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
