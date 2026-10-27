module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec4.Struct

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec4.M

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {O : Subgroup G → Subgroup G}
  {FA : G → Subgroup G → Prop} {SD : Subgroup G → Prop} {z : G} {S K₁ K₂ : Subgroup G}

@[expose] def Em (O : Subgroup G → Subgroup G) (z : G) (K₁ K₂ : Subgroup G) : Subgroup G :=
  secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂)) ⊓ centralizer ({z} : Set G)

theorem mem_normalizer_comp {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G)) :
    (∀ x ∈ X, g * x * g⁻¹ ∈ X) ∧ ∀ x ∈ X, g⁻¹ * x * g ∈ X := by
  rw [Subgroup.mem_normalizer_iff] at hg
  refine ⟨fun x hx => (hg x).1 hx, fun x hx => ?_⟩
  rw [hg]
  simpa [mul_assoc] using hx

theorem cj_eq_iff_normalizer {X : Subgroup G} {g : G} :
    cj X g = X ↔ g ∈ normalizer (X : Set G) := by
  constructor
  · intro h
    refine mem_normalizer_of_both (fun x hx => ?_) (fun x hx => ?_)
    · have : x ∈ cj X g := by rw [h]; exact hx
      simpa using this
    · have : g * (g⁻¹ * x * g) * g⁻¹ ∈ X := by simpa [mul_assoc] using hx
      have h2 : g⁻¹ * x * g ∈ cj X g := by simpa using this
      rwa [h] at h2
  · intro hg
    obtain ⟨h1, h2⟩ := mem_normalizer_comp hg
    ext x
    rw [mem_cj]
    constructor
    · intro hx
      have := h2 _ hx
      simpa [mul_assoc] using this
    · intro hx; exact h1 x hx

namespace M4

variable [Finite G]

omit [Finite G] in
theorem P_pgroup (h : M4 O FA SD z S K₁ K₂) : IsPGroup 2 ↥(Pm S K₁ K₂) :=
  h.S_pgroup.to_inf_left

omit [Finite G] in
theorem Pm_le_S : Pm S K₁ K₂ ≤ S := inf_le_left

omit [Finite G] in
theorem Pm_le_K : Pm S K₁ K₂ ≤ K₁ ⊔ K₂ := inf_le_right

theorem P_syl (h : M4 O FA SD z S K₁ K₂) : Syl2In (Pm S K₁ K₂) (K₁ ⊔ K₂) :=
  h.S_syl.inf_normal h.K_le_C (fun _ hc _ hk => h.C_norm_K hc hk)

theorem Pi_syl (h : M4 O FA SD z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    Syl2In (Pm S K₁ K₂ ⊓ K) K := by
  refine h.P_syl.inf_normal (h.comp_le hK) (fun x hx n hn => ?_)
  rcases hK with rfl | rfl
  · exact h.conj_comp₁ hx hn
  · exact h.conj_comp₂ hx hn

theorem P_eq (h : M4 O FA SD z S K₁ K₂) :
    Pm S K₁ K₂ = (Pm S K₁ K₂ ⊓ K₁) ⊔ (Pm S K₁ K₂ ⊓ K₂) :=
  Syl2In.eq_sup_of_normalizing h.n₂₁ (fun _ hx _ hn => h.conj_comp₁ hx hn)
    (fun _ hx _ hn => h.conj_comp₂ hx hn) h.P_syl
    (fun _ ha _ hb => h.comm_of_S ha.2 hb.2 ha.1.1 hb.1.1)

theorem P_inf_OK (h : M4 O FA SD z S K₁ K₂) : Pm S K₁ K₂ ⊓ O (K₁ ⊔ K₂) = ⊥ := by
  apply disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 h.P_pgroup
  rw [ha]
  exact Nat.Coprime.pow_left a (Nat.coprime_two_left.2 h.coreK.odd)

theorem z_mem_P (h : M4 O FA SD z S K₁ K₂) : z ∈ Pm S K₁ K₂ :=
  ⟨h.z_mem_S, mem_sup_left (h.z_mem_comp (Or.inl rfl))⟩

theorem z_mem_secCent (h : M4 O FA SD z S K₁ K₂) : z ∈ secCent (K₁ ⊔ K₂) (O (K₁ ⊔ K₂)) := by
  have hC := z_mem_centralizer (z := z)
  refine ⟨mem_normalizer_of_both (fun x hx => h.C_norm_K hC hx) (fun x hx => h.C_norm_K' hC hx),
    mem_normalizer_of_both (fun x hx => h.C_norm_OK hC hx) (fun x hx => ?_), ?_⟩
  · have := h.C_norm_OK (inv_mem hC) hx
    simpa using this
  · intro k hk
    have hkz : k * z = z * k := centralizer_comm (h.K_le_C hk)
    have : ⁅k, z⁆ = 1 := by
      simp only [commutatorElement_def]
      rw [hkz]; group
    rw [this]; exact one_mem _

theorem z_mem_Q (h : M4 O FA SD z S K₁ K₂) : z ∈ Qm O S K₁ K₂ := ⟨h.z_mem_S, h.z_mem_secCent⟩

theorem P_inf_Q (h : M4 O FA SD z S K₁ K₂) : Pm S K₁ K₂ ⊓ Qm O S K₁ K₂ ≤ zpowers z := by
  intro x hx
  have hxZ : x ∈ S ⊓ ZsM O (K₁ ⊔ K₂) := ⟨hx.1.1, hx.1.2, hx.2.2⟩
  rwa [h.S_inf_Zs] at hxZ

omit [Finite G] in
theorem Q_le_S : Qm O S K₁ K₂ ≤ S := inf_le_left

omit [Finite G] in
theorem Q_le_C (h : M4 O FA SD z S K₁ K₂) : Qm O S K₁ K₂ ≤ centralizer ({z} : Set G) :=
  inf_le_left.trans h.S_syl.1

theorem Q_comm_P (h : M4 O FA SD z S K₁ K₂) {q p : G} (hq : q ∈ Qm O S K₁ K₂)
    (hp : p ∈ Pm S K₁ K₂) : q * p = p * q := by
  have hcm : ⁅p, q⁆ ∈ O (K₁ ⊔ K₂) := hq.2.2.2 p hp.2
  have hqC : q ∈ centralizer ({z} : Set G) := h.Q_le_C hq
  have hP : ⁅p, q⁆ ∈ Pm S K₁ K₂ := by
    have e : ⁅p, q⁆ = p * (q * p⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
    have hpS : p ∈ S := hp.1
    have hqS : q ∈ S := hq.1
    have hpK : p ∈ K₁ ⊔ K₂ := hp.2
    rw [e]
    have h1 : q * p⁻¹ * q⁻¹ ∈ S := mul_mem (mul_mem hqS (inv_mem hpS)) (inv_mem hqS)
    have h2 : q * p⁻¹ * q⁻¹ ∈ K₁ ⊔ K₂ := h.C_norm_K hqC (inv_mem hpK)
    exact mul_mem hp ⟨h1, h2⟩
  have h1 : ⁅p, q⁆ ∈ Pm S K₁ K₂ ⊓ O (K₁ ⊔ K₂) := ⟨hP, hcm⟩
  rw [h.P_inf_OK, Subgroup.mem_bot] at h1
  have : p * q * p⁻¹ * q⁻¹ = 1 := h1
  have h2 : p * q = q * p := by
    calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
      _ = q * p := by rw [this, one_mul]
  exact h2.symm

omit [Finite G] in
theorem Q_cj_comp (h : M4 O FA SD z S K₁ K₂) {q : G} (hq : q ∈ Qm O S K₁ K₂)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : cj K q = K := by
  have hqC : q ∈ centralizer ({z} : Set G) := h.Q_le_C hq
  rcases h.perm q hqC with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hK with rfl | rfl
    · exact h1
    · exact h2
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := h.nonab K₁ (Or.inl rfl)
    apply hab
    obtain ⟨a', ha'def⟩ : ∃ a', a' = q * a⁻¹ * q⁻¹ := ⟨_, rfl⟩
    have ha' : a' ∈ K₂ := by
      have : a⁻¹ ∈ cj K₂ q := by rw [h2]; exact inv_mem ha
      rw [ha'def]
      exact mem_cj.1 this
    have hcm : ⁅a, q⁆ ∈ O (K₁ ⊔ K₂) := hq.2.2.2 a (mem_sup_left ha)
    obtain ⟨o, hodef⟩ : ∃ o, o = a * a' := ⟨_, rfl⟩
    have ho : o ∈ O (K₁ ⊔ K₂) := by
      have e : ⁅a, q⁆ = o := by simp only [commutatorElement_def, hodef, ha'def]; group
      rwa [← e]
    have h1 : ⁅a'⁻¹, b⁆ ∈ O (K₁ ⊔ K₂) :=
      h.O_le_OK (Or.inr rfl) ((h.cs₂ hb).2.2 a'⁻¹ (inv_mem ha'))
    have hao : a = o * a'⁻¹ := by rw [hodef]; group
    have e2 : ⁅a, b⁆ = o * ⁅a'⁻¹, b⁆ * o⁻¹ * (o * (b * o⁻¹ * b⁻¹)) := by
      rw [hao]
      simp only [commutatorElement_def]; group
    have hb' : b * o⁻¹ * b⁻¹ ∈ O (K₁ ⊔ K₂) :=
      h.coreK.normal b (mem_sup_left hb) _ (inv_mem ho)
    have hOK : ⁅a, b⁆ ∈ O (K₁ ⊔ K₂) := by
      rw [e2]
      exact mul_mem (mul_mem (mul_mem ho h1) (inv_mem ho)) (mul_mem ho hb')
    have hK₁ : ⁅a, b⁆ ∈ K₁ := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact h.inf_OK_le (Or.inl rfl) ⟨hK₁, hOK⟩

omit [Finite G] in
theorem Q_mem_secCent_comp (h : M4 O FA SD z S K₁ K₂) {q : G} (hq : q ∈ Qm O S K₁ K₂)
    {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : q ∈ secCent K (O K) := by
  have hn : q ∈ normalizer (K : Set G) := cj_eq_iff_normalizer.1 (h.Q_cj_comp hq hK)
  obtain ⟨hq1, hq2⟩ := mem_normalizer_comp hn
  refine ⟨hn, mem_normalizer_of_both (fun x hx => ((h.core K hK).conj_mem hq1 hq2 hx))
    (fun x hx => ?_), ?_⟩
  · have := (h.core K hK).conj_mem (c := q⁻¹) (by simpa using hq2) (by simpa using hq1) hx
    simpa using this
  · intro k hk
    have hkK : ⁅k, q⁆ ∈ K := by
      have e : ⁅k, q⁆ = k * (q * k⁻¹ * q⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hk (hq1 _ (inv_mem hk))
    have hkO : ⁅k, q⁆ ∈ O (K₁ ⊔ K₂) := hq.2.2.2 k (h.comp_le hK hk)
    exact h.inf_OK_le hK ⟨hkK, hkO⟩

end M4

end CFSG.GH74.GLS.Stage1.Thm3.Sec4.M
