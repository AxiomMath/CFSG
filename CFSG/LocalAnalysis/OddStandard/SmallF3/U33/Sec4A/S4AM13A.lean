module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR8D

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

section M13A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem m13_comm_R (h : L41GPh10 t L S x₁ x₂ lam rho) {a b : G} (ha : a ∈ l41R t x₁ x₂ rho)
    (hb : b ∈ l41R t x₁ x₂ rho) : a * b = b * a := by
  haveI := h.rab
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(l41R t x₁ x₂ rho)) ⟨b, hb⟩)

theorem m13_t_mem_N (h : L41GPh3 t L S x₁ x₂ lam rho) : t ∈ l41N t x₁ x₂ :=
  pCoreOf_two_le _ (n4_t_mem_O h)

theorem m13_t_inv (h : Hyp G t L) : t⁻¹ = t := inv_eq_of_mul_eq_one_right (t_mul_self h)

theorem m13_t_conj_R (h : L41GPh8 t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ l41R t x₁ x₂ rho) :
    t * r * t⁻¹ ∈ l41R t x₁ x₂ rho :=
  h.rfacts.normal_R.2 t (m13_t_mem_N h.toL41GPh3) r hr

theorem m13_conj_t_R (h : L41GPh8 t L S x₁ x₂ lam rho) {r : G} (hr : r ∈ l41R t x₁ x₂ rho) :
    ∃ f ∈ fourGrp x₁ x₂, t * r * t⁻¹ = f * r := by
  have hmem : r * t * r⁻¹ ∈ conjIn (l41R t x₁ x₂ rho) t := ⟨r, hr, rfl⟩
  rw [h.rfacts.orbit_t] at hmem
  obtain ⟨f, hf, hft⟩ := n4_mem_smul_iff.mp hmem
  refine ⟨f, hf, ?_⟩
  have ht := m13_t_inv h.hyp
  calc t * r * t⁻¹ = t⁻¹ * (r * t * r⁻¹) * r := by rw [ht]; group
    _ = t⁻¹ * (t * f) * r := by rw [hft]
    _ = f * r := by group

theorem m13_orbit_tk (h : L41GPh10 t L S x₁ x₂ lam rho) {k : G} (hk : k ∈ l41R t x₁ x₂ rho) :
    conjIn (l41R t x₁ x₂ rho) (t * k) = (t * k) • (fourGrp x₁ x₂ : Set G) := by
  have hF2R := h.rfacts.fourGrp_le
  apply Set.Subset.antisymm
  · rintro u ⟨r, hr, rfl⟩
    have hmem : r * t * r⁻¹ ∈ conjIn (l41R t x₁ x₂ rho) t := ⟨r, hr, rfl⟩
    rw [h.rfacts.orbit_t] at hmem
    obtain ⟨f, hf, hft⟩ := n4_mem_smul_iff.mp hmem
    refine n4_mem_smul_iff.mpr ⟨f, hf, ?_⟩
    have hfk : f * k = k * f := m13_comm_R h (hF2R hf) hk
    have hrk : r * k = k * r := m13_comm_R h hr hk
    calc r * (t * k) * r⁻¹ = (r * t * r⁻¹) * (r * k * r⁻¹) := by group
      _ = (t * f) * k := by rw [hft, hrk]; group
      _ = t * k * f := by rw [mul_assoc, hfk, ← mul_assoc]
  · intro u hu
    obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hu
    have hmem : t * f ∈ conjIn (l41R t x₁ x₂ rho) t := by
      rw [h.rfacts.orbit_t]
      exact n4_mem_smul_iff.mpr ⟨f, hf, rfl⟩
    obtain ⟨r, hr, hrt⟩ := hmem
    refine ⟨r, hr, ?_⟩
    have hfk : f * k = k * f := m13_comm_R h (hF2R hf) hk
    have hrk : r * k = k * r := m13_comm_R h hr hk
    calc r * (t * k) * r⁻¹ = (r * t * r⁻¹) * (r * k * r⁻¹) := by group
      _ = (t * f) * k := by rw [hrt, hrk]; group
      _ = t * k * f := by rw [mul_assoc, hfk, ← mul_assoc]

theorem m13_cent_tk (h : L41GPh10 t L S x₁ x₂ lam rho) {k : G} (hk : k ∈ l41R t x₁ x₂ rho) :
    l41R t x₁ x₂ rho ⊓ centralizer ({t * k} : Set G) = baseGrp x₁ x₂ := by
  rw [← h.rfacts.cent_t]
  ext r
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, mem_invCent_iff]
  constructor
  · rintro ⟨hr, hc⟩
    refine ⟨hr, ?_⟩
    have hrk : r * k = k * r := m13_comm_R h hr hk
    apply mul_right_cancel (b := k)
    calc r * t * k = r * (t * k) := mul_assoc _ _ _
      _ = t * k * r := hc
      _ = t * (k * r) := mul_assoc _ _ _
      _ = t * (r * k) := by rw [hrk]
      _ = t * r * k := (mul_assoc _ _ _).symm
  · rintro ⟨hr, hc⟩
    refine ⟨hr, ?_⟩
    have hrk : r * k = k * r := m13_comm_R h hr hk
    calc r * (t * k) = r * t * k := (mul_assoc _ _ _).symm
      _ = t * r * k := by rw [hc]
      _ = t * (r * k) := mul_assoc _ _ _
      _ = t * (k * r) := by rw [hrk]
      _ = t * k * r := (mul_assoc _ _ _).symm

@[expose] def m13Phi (h : L41GPh10 t L S x₁ x₂ lam rho) :
    ↥(l41R t x₁ x₂ rho) →* ↥(l41R t x₁ x₂ rho) :=
  MonoidHom.mk'
    (fun r => ⟨t * (r : G) * t⁻¹ * (r : G),
      Subgroup.mul_mem _ (m13_t_conj_R h.toL41GPh8 r.2) r.2⟩)
    (fun a b => by
      apply Subtype.ext
      have hc : (t * (b : G) * t⁻¹) * (a : G) = (a : G) * (t * (b : G) * t⁻¹) :=
        m13_comm_R h (m13_t_conj_R h.toL41GPh8 b.2) a.2
      show t * ((a : G) * (b : G)) * t⁻¹ * ((a : G) * (b : G)) =
        t * (a : G) * t⁻¹ * (a : G) * (t * (b : G) * t⁻¹ * (b : G))
      calc t * ((a : G) * (b : G)) * t⁻¹ * ((a : G) * (b : G))
          = (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) * ((a : G) * (b : G)) := by group
        _ = (t * (a : G) * t⁻¹) * ((t * (b : G) * t⁻¹) * (a : G)) * (b : G) := by group
        _ = (t * (a : G) * t⁻¹) * ((a : G) * (t * (b : G) * t⁻¹)) * (b : G) := by rw [hc]
        _ = t * (a : G) * t⁻¹ * (a : G) * (t * (b : G) * t⁻¹ * (b : G)) := by group)

theorem m13Phi_apply (h : L41GPh10 t L S x₁ x₂ lam rho) (r : ↥(l41R t x₁ x₂ rho)) :
    ((m13Phi h r : ↥(l41R t x₁ x₂ rho)) : G) = t * (r : G) * t⁻¹ * (r : G) := rfl

theorem m13Phi_eq_one_iff (h : L41GPh10 t L S x₁ x₂ lam rho) (r : ↥(l41R t x₁ x₂ rho)) :
    m13Phi h r = 1 ↔ (t * (r : G)) * (t * (r : G)) = 1 := by
  have ht := m13_t_inv h.hyp
  have e : t * (r : G) * t⁻¹ * (r : G) = (t * (r : G)) * (t * (r : G)) := by
    rw [ht]
    group
  constructor
  · intro h1
    have h2 := congrArg Subtype.val h1
    rw [m13Phi_apply, e] at h2
    exact h2
  · intro h1
    apply Subtype.ext
    rw [m13Phi_apply, e]
    exact h1

theorem m13_t_comm_L (h : L41GPh5 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ L) : t * g = g * t :=
  n4_zpowers_t_comm h (Subgroup.mem_zpowers t) hg

theorem m13_x_mem_R (h : L41GPh3 t L S x₁ x₂ lam rho) :
    x₁ ∈ l41R t x₁ x₂ rho ∧ x₂ ∈ l41R t x₁ x₂ rho :=
  ⟨n4_base_le_R h (Subgroup.subset_closure (by simp)),
    n4_base_le_R h (Subgroup.subset_closure (by simp))⟩

theorem m13_t_comm_base (h : L41GPh5 t L S x₁ x₂ lam rho) {b : G} (hb : b ∈ baseGrp x₁ x₂) :
    t * b = b * t :=
  m13_t_comm_L h (pt_base_le_L h.toCtx0 hb)

theorem m13Phi_range (h : L41GPh10 t L S x₁ x₂ lam rho) :
    (m13Phi h).range = (fourGrp x₁ x₂).subgroupOf (l41R t x₁ x₂ rho) := by
  apply le_antisymm
  · rintro _ ⟨r, rfl⟩
    rw [Subgroup.mem_subgroupOf, m13Phi_apply]
    obtain ⟨f, hf, hfr⟩ := m13_conj_t_R h.toL41GPh8 r.2
    have e : t * (r : G) * t⁻¹ * (r : G) = f * ((r : G) * (r : G)) := by
      rw [hfr]
      group
    rw [e]
    exact Subgroup.mul_mem _ hf (h.rfacts.sq_mem _ r.2)
  · intro u hu
    rw [Subgroup.mem_subgroupOf] at hu
    have hsq : ∀ b : G, b ∈ baseGrp x₁ x₂ →
        b * b ∈ (m13Phi h).range.map (l41R t x₁ x₂ rho).subtype :=
      fun b hb => by
        have hbR : b ∈ l41R t x₁ x₂ rho := n4_base_le_R h.toL41GPh3 hb
        refine Subgroup.mem_map.mpr ⟨m13Phi h ⟨b, hbR⟩, ⟨⟨b, hbR⟩, rfl⟩, ?_⟩
        show t * b * t⁻¹ * b = b * b
        have hcomm := m13_t_comm_base h.toL41GPh5 hb
        calc t * b * t⁻¹ * b = (b * t) * t⁻¹ * b := by rw [hcomm]
          _ = b * b := by group
    have hF : fourGrp x₁ x₂ ≤ (m13Phi h).range.map (l41R t x₁ x₂ rho).subtype := by
      refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · have := hsq x₁ (Subgroup.subset_closure (by simp))
        rwa [← pow_two] at this
      · have := hsq (x₁ * x₂) (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp)))
        rwa [← pow_two] at this
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp (hF hu)
    have : w = u := Subtype.ext hwu
    rwa [← this]

theorem m13_card_X (h : L41GPh10 t L S x₁ x₂ lam rho) :
    {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1}.ncard = 16 := by
  have hset : {u | u ∈ t • (l41R t x₁ x₂ rho : Set G) ∧ u * u = 1} =
      (fun r : ↥(l41R t x₁ x₂ rho) => t * (r : G)) ''
        ((m13Phi h).ker : Set ↥(l41R t x₁ x₂ rho)) := by
    ext u
    constructor
    · rintro ⟨hu, hu2⟩
      obtain ⟨r, hr, rfl⟩ := n4_mem_smul_iff.mp (by simpa using hu)
      exact ⟨⟨r, hr⟩, (m13Phi_eq_one_iff h ⟨r, hr⟩).mpr hu2, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      refine ⟨?_, (m13Phi_eq_one_iff h r).mp hr⟩
      simpa using n4_mem_smul_iff.mpr ⟨(r : G), r.2, rfl⟩
  have hinj : Function.Injective (fun r : ↥(l41R t x₁ x₂ rho) => t * (r : G)) :=
    fun a b hab => Subtype.ext (mul_left_cancel hab)
  rw [hset, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  have h1 := card_ker_mul_card_range (m13Phi h)
  have h2 : Nat.card (m13Phi h).range = 4 := by
    rw [m13Phi_range h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      h.rfacts.fourGrp_le).toEquiv]
    exact n4_card_four h.toCtx0
  rw [h2, h.rfacts.card_R] at h1
  show Nat.card (m13Phi h).ker = 16
  omega

theorem m13_mem_F (h : L41GPh8 t L S x₁ x₂ lam rho) {f : G} (hf : f ∈ l41F t x₁ x₂ rho) :
    f ∈ l41R t x₁ x₂ rho ∨ ∃ k ∈ l41R t x₁ x₂ rho, f = t * k := by
  have hNR := h.rfacts.normal_R
  have htN := m13_t_mem_N h.toL41GPh3
  have hzN : zpowers t ≤ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
    intro p hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    exact mem_normalizer_of_conj_mem fun r hr =>
      hNR.2 _ (Subgroup.zpow_mem _ htN j) r hr
  have hf' : f ∈ ((l41R t x₁ x₂ rho ⊔ zpowers t : Subgroup G) : Set G) := hf
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hzN] at hf'
  obtain ⟨r, hr, p, hp, rfl⟩ := Set.mem_mul.mp hf'
  rcases pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hp with h1 | h1
  · left
    rw [h1, mul_one]
    exact hr
  · right
    refine ⟨t⁻¹ * r * t, ?_, ?_⟩
    · have := hNR.2 t⁻¹ (Subgroup.inv_mem _ htN) r hr
      rwa [inv_inv] at this
    · rw [h1]
      group

theorem m13_card_F (h : L41GPh8 t L S x₁ x₂ lam rho) : Nat.card (l41F t x₁ x₂ rho) = 2 ^ 7 := by
  have h1 : l41F t x₁ x₂ rho = l41O2 t x₁ x₂ := h.rfacts.O2_eq.symm
  rw [h1, n4_card_O_R h.toL41GPh7, h.rfacts.card_R]
  norm_num

end M13A

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
