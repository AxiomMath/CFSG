module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQF

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup CFSG.EvenSmallLie.UnitarySix.YamadaQ CFSG.EvenSmallLie.UnitarySix.LemmaQ
open scoped commutatorElement

set_option maxRecDepth 10000 in
theorem fixed_A₄_eq (w : Fin 8 → ZMod 2) (h1 : mU₁.mulVec w = w) (h2 : mU₂.mulVec w = w)
    (h3 : hiPart w = 0) : w = 0 ∨ w = vz := by
  revert w; decide

theorem mPhi_vz (l : Fin 4 → ZMod 2) : (mPhi l).mulVec vz = vz := by
  revert l; decide

variable {G : Type*} [Group G]

namespace Data

@[expose] def Qp (d : Data G) (φ : G) : Subgroup G := d.Q₁ ⊔ zpowers φ

end Data

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d) {φ : G} (hF : HypF d φ)
include h hF

theorem φ_mem_normalizer_X₁ : φ ∈ normalizer (d.X₁ : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  obtain ⟨k, rfl⟩ := h.exists_xs hx
  rw [h.φ_xs hF k]; exact h.xs_mem _

theorem φ_mem_normalizer_Q₁ : φ ∈ normalizer (d.Q₁ : Set G) := by
  refine mem_normalizer_sup (h.φ_mem_normalizer_X₁ hF) ?_
  rw [← h.withT_D₄, Data.withT]
  exact mem_normalizer_sup (h.φ_mem_normalizer_D₄ hF) (mem_normalizer_zpowers hF.φ_comm_t)

theorem φ_sq_mem_Q₁ : φ * φ ∈ d.Q₁ := by
  rcases hF.φ_sq with h1 | h1 <;> rw [h1]
  · exact one_mem _
  · exact h.t_mem_Q₁

omit [Finite G] h in
theorem φ_mem_H : φ ∈ d.H := mem_centralizer_singleton_iff.mpr hF.φ_comm_t

theorem φ_not_mem_Q₁ (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) : φ ∉ d.Q₁ := by
  obtain ⟨d₀, hd₀, hθ⟩ := h.exists_d₀
  intro hφ
  obtain ⟨k, v, ε, he⟩ := h.exists_Q₁_coords hd₀ hB hV hθ hφ
  have hxH : d.xs k ∈ d.H := h.L_le_H (h.xs_mem_L k)
  have hτH : (if ε then d.t else 1) ∈ d.H := by
    split_ifs
    · exact t_mem_H
    · exact one_mem _
  have hkap : h.kap hd₀ v ∈ d.A₄ := by
    rw [← h.D₄_inf_H]
    refine ⟨h.kap_mem hd₀ v, ?_⟩
    have e : h.kap hd₀ v = (d.xs k)⁻¹ * φ * (if ε then d.t else 1)⁻¹ := by rw [he]; group
    rw [e]
    exact d.H.mul_mem (d.H.mul_mem (d.H.inv_mem hxH) (φ_mem_H hF)) (d.H.inv_mem hτH)
  apply hF.φ_not_mem
  rw [he]
  refine mul_mem (mul_mem (mem_sup_left (h.xs_mem_L k)) (mem_sup_left (h.A₄_le_L hkap))) ?_
  split_ifs
  · exact mem_sup_right (mem_zpowers _)
  · exact one_mem _

theorem card_Qp (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) : Nat.card (d.Qp φ) = 2 ^ 12 := by
  obtain ⟨d₀, hd₀, hθ⟩ := h.exists_d₀
  have h1 := two_mul_card_le_card_sup (h.φ_not_mem_Q₁ hF hB hV)
  have h2 := card_sup_zpowers_le (h.φ_mem_normalizer_Q₁ hF) (h.φ_sq_mem_Q₁ hF)
  rw [h.card_Q₁ hB hV hd₀ hθ] at h1 h2
  rw [Data.Qp]
  omega

omit [Finite G] in
theorem isPGroup_zpowers_φ : IsPGroup 2 (zpowers φ) := by
  have h4 : φ ^ 4 = 1 := by
    rcases hF.φ_sq with h1 | h1
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq φ, h1, one_pow]
    · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq φ, h1, sq, h.t_sq]
  rintro ⟨g, k, rfl⟩
  refine ⟨2, Subtype.ext ?_⟩
  change (φ ^ k) ^ (2 ^ 2) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((2 ^ 2 : ℕ) : ℤ) = 4 by norm_num,
    show φ ^ (4 : ℤ) = 1 by rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast, h4],
    one_zpow]

theorem isPGroup_Qp : IsPGroup 2 (d.Qp φ) :=
  h.isPGroup_Q₁.to_sup_of_normal_left' (h.isPGroup_zpowers_φ hF)
    (zpowers_le.mpr (h.φ_mem_normalizer_Q₁ hF))

omit [Finite G] in
theorem Qp_le_cent_e (hQ : HypQ d) : d.Qp φ ≤ centralizer ({d.e} : Set G) :=
  sup_le (h.Q₁_le_cent_e hQ) (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hF.φ_comm_e))

theorem Qp_le_normalizer :
    d.Qp φ ≤ normalizer ((centInvSup d.D₄ d.t : Subgroup G) : Set G) := by
  refine sup_le h.Q₁_le_normalizer (zpowers_le.mpr ?_)
  rw [h.centInvSup_D₄]
  exact φ_mem_X₄ hF

omit hF in
theorem t_mem_Qp : d.t ∈ d.Qp φ := mem_sup_left h.t_mem_Q₁

omit [Finite G] in
theorem comm_xs_φ (k : Fin 4) : ⁅d.xs k, φ⁆ ∈ zpowers d.u₁ := by
  have e : ⁅d.xs k, φ⁆ = d.xs k * (d.xs (frobIdx k))⁻¹ := by
    rw [commutatorElement_def, ← h.φ_xs hF k]; group
  rw [e]
  have hu : d.u₁⁻¹ = d.u₁ := inv_eq_of_mul_eq_one_right h.u₁_sq
  fin_cases k
  · simp [Data.xs, frobIdx]
  · simp [Data.xs, frobIdx]
  · show d.u₂ * (d.u₁ * d.u₂)⁻¹ ∈ zpowers d.u₁
    rw [mul_inv_rev, mul_inv_cancel_left, hu]; exact mem_zpowers _
  · show d.u₁ * d.u₂ * d.u₂⁻¹ ∈ zpowers d.u₁
    rw [mul_inv_cancel_right]; exact mem_zpowers _

omit hF in
theorem Qp_eq_closure : d.Qp φ = closure ((d.X₁ : Set G) ∪ d.D₄ ∪ {d.t} ∪ {φ}) := by
  rw [Data.Qp, h.Q₁_eq_closure, zpowers_eq_closure, ← closure_union]

section W

variable {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)

@[expose] def M₁p : Subgroup G := h.M₁ hd₀ hB hV ⊔ zpowers d.u₁

variable (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {l : Fin 4 → ZMod 2}
  (hl : φ * d₀ * φ⁻¹ = d₀ * h.kap hd₀ (lo l))
include hB hV hd₀ hθ

omit hF in
theorem u₁_mem_normalizer_M₁ : d.u₁ ∈ normalizer (h.M₁ hd₀ hB hV : Set G) := by
  have := h.gens_le_normalizer_M₁ hd₀ hB hV hθ d.u₁ (Or.inl (Or.inl h.u₁_mem))
  exact this

omit hF in
theorem mem_M₁p_iff {g : G} : g ∈ h.M₁p hd₀ hB hV ↔ g ∈ h.M₁ hd₀ hB hV ∨
    g * d.u₁⁻¹ ∈ h.M₁ hd₀ hB hV := by
  unfold M₁p
  exact mem_sup_zpowers_of_normalizer (h.u₁_mem_normalizer_M₁ hd₀ hB hV hθ)
    (by rw [h.u₁_sq]; exact one_mem _)

omit hθ in
include hl in
theorem φ_mem_normalizer_M₁ : φ ∈ normalizer (h.M₁ hd₀ hB hV : Set G) :=
  h.conj_mem_M₁ hd₀ hB hV (h.conj_φ_kap hF hB hV hd₀ hl) (hiSum_mPhi l)

include hl in
theorem gens_le_normalizer_M₁p :
    ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t} ∪ {φ}, s ∈ normalizer (h.M₁p hd₀ hB hV : Set G) := by
  have hN := h.gens_le_normalizer_M₁ hd₀ hB hV hθ
  rintro s (((hs | hs) | hs) | hs)
  · exact mem_normalizer_sup (hN s (Or.inl (Or.inl hs)))
      (mem_normalizer_zpowers (h.X₁_comm hs h.u₁_mem))
  · apply mem_normalizer_of_conj_mem
    intro g hg
    rw [h.mem_M₁p_iff hd₀ hB hV hθ] at hg ⊢
    have hsN := hN s (Or.inl (Or.inr hs))
    rcases hg with hg | hg
    · exact Or.inl ((mem_normalizer_iff.mp hsN g).mp hg)
    · right
      have hc : ⁅s, d.u₁⁆ ∈ h.M₁ hd₀ hB hV :=
        h.commQ₁_le_M₁ hd₀ hB hV hθ (commutator_mem_commutator (h.D₄_le_Q₁ hs)
          (X₁_le_Q₁ h.u₁_mem))
      have e : s * g * s⁻¹ * d.u₁⁻¹ = s * (g * d.u₁⁻¹) * s⁻¹ * ⁅s, d.u₁⁆ := by
        rw [commutatorElement_def]; group
      rw [e]
      exact mul_mem ((mem_normalizer_iff.mp hsN _).mp hg) hc
  · rw [Set.mem_singleton_iff.mp hs]
    exact mem_normalizer_sup (hN d.t (Or.inr rfl))
      (mem_normalizer_zpowers (h.comm_of_mem_L (h.X₁_le_L h.u₁_mem)).symm)
  · rw [Set.mem_singleton_iff.mp hs]
    refine mem_normalizer_sup (h.φ_mem_normalizer_M₁ hF hd₀ hB hV hl) ?_
    apply mem_normalizer_zpowers
    have := hF.φ_u₁
    calc φ * d.u₁ = (φ * d.u₁ * φ⁻¹) * φ := by group
      _ = d.u₁ * φ := by rw [this]

include hl in
theorem commQp_le_M₁p : ⁅d.Qp φ, d.Qp φ⁆ ≤ h.M₁p hd₀ hB hV := by
  have hN := h.gens_le_normalizer_M₁p hF hd₀ hB hV hθ hl
  have hS₁ : ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, s ∈ d.Q₁ := by
    rintro s ((hs | hs) | hs)
    · exact X₁_le_Q₁ hs
    · exact h.D₄_le_Q₁ hs
    · rw [Set.mem_singleton_iff.mp hs]; exact h.t_mem_Q₁
  have h11 : ∀ m ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t},
      ⁅m, s⁆ ∈ h.M₁p hd₀ hB hV := fun m hm s hs =>
    mem_sup_left (h.commQ₁_le_M₁ hd₀ hB hV hθ (commutator_mem_commutator (hS₁ m hm) (hS₁ s hs)))
  have h1φ : ∀ m ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, ⁅m, φ⁆ ∈ h.M₁p hd₀ hB hV := by
    rintro m ((hm | hm) | hm)
    · obtain ⟨k, rfl⟩ := h.exists_xs hm
      exact mem_sup_right (h.comm_xs_φ hF k)
    · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hm
      rw [h.comm_kap_left hd₀ hB hV (h.conj_φ_kap hF hB hV hd₀ hl)]
      exact mem_sup_left ⟨_, hiSum_comm_mPhi l v, rfl⟩
    · rw [Set.mem_singleton_iff.mp hm,
        commutatorElement_eq_one_iff_mul_comm.mpr hF.φ_comm_t.symm]
      exact one_mem _
  rw [h.Qp_eq_closure]
  refine commutator_closure_le hN hN ?_
  rintro m (hm | hm) s (hs | hs)
  · exact h11 m hm s hs
  · rw [Set.mem_singleton_iff.mp hs]; exact h1φ m hm
  · rw [Set.mem_singleton_iff.mp hm, ← commutatorElement_inv]; exact inv_mem (h1φ s hs)
  · rw [Set.mem_singleton_iff.mp hm, Set.mem_singleton_iff.mp hs, commutatorElement_self]
    exact one_mem _

include hl in
theorem φ_mem_normalizer_V₂ : φ ∈ normalizer (d.V₂ : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro g hg
  obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ (h.V₂_le_D₄ hg)
  rw [h.conj_φ_kap hF hB hV hd₀ hl, h.kap_mem_V₂_iff hd₀ hB hV hθ, augZ_mPhi]
  exact (h.kap_mem_V₂_iff hd₀ hB hV hθ v).mp hg

include hl in
theorem commM₁p_le_V₂ : ⁅h.M₁p hd₀ hB hV, d.Qp φ⁆ ≤ d.V₂ := by
  have hM : h.M₁p hd₀ hB hV = closure ((h.M₁ hd₀ hB hV : Set G) ∪ {d.u₁}) := by
    rw [closure_union, closure_eq, ← zpowers_eq_closure]; rfl
  have hS : ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t} ∪ {φ}, s ∈ normalizer (d.V₂ : Set G) := by
    rintro s (hs | hs)
    · exact h.gens_le_normalizer_V₂ hV s hs
    · rw [Set.mem_singleton_iff.mp hs]; exact h.φ_mem_normalizer_V₂ hF hd₀ hB hV hθ hl
  have hT : ∀ m ∈ (h.M₁ hd₀ hB hV : Set G) ∪ {d.u₁}, m ∈ normalizer (d.V₂ : Set G) := by
    rintro m (hm | hm)
    · exact LemmaQ.mem_normalizer_of_le_comm h.D₄_comm' h.V₂_le_D₄ (h.M₁_le_D₄ hd₀ hB hV hm)
    · rw [Set.mem_singleton_iff.mp hm]; exact h.X₁_le_normalizer_V₂ hV h.u₁_mem
  have hS₁ : ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, s ∈ d.Q₁ := by
    rintro s ((hs | hs) | hs)
    · exact X₁_le_Q₁ hs
    · exact h.D₄_le_Q₁ hs
    · rw [Set.mem_singleton_iff.mp hs]; exact h.t_mem_Q₁
  rw [hM, h.Qp_eq_closure]
  refine commutator_closure_le hS hT ?_
  rintro m (hm | hm) s (hs | hs)
  · exact h.commM₁_le_V₂ hd₀ hB hV hθ (commutator_mem_commutator hm (hS₁ s hs))
  · obtain ⟨v, hv, rfl⟩ := hm
    rw [Set.mem_singleton_iff.mp hs, h.comm_kap_left hd₀ hB hV (h.conj_φ_kap hF hB hV hd₀ hl),
      h.kap_mem_V₂_iff hd₀ hB hV hθ]
    exact augZ_comm_mPhi l v hv
  · rw [Set.mem_singleton_iff.mp hm]
    rcases hs with (hs | hs) | hs
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.X₁_comm h.u₁_mem hs)]; exact one_mem _
    · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hs
      rw [← commutatorElement_inv, h.comm_kap_left hd₀ hB hV (h.conj_u₁_kap hd₀ hB hV)]
      refine inv_mem ((h.kap_mem_V₂_iff hd₀ hB hV hθ _).mpr ?_)
      simpa [mX] using augZ_comm_mX' 1 v
    · rw [Set.mem_singleton_iff.mp hs, commutatorElement_eq_one_iff_mul_comm.mpr
        (h.comm_of_mem_L (h.X₁_le_L h.u₁_mem))]
      exact one_mem _
  · rw [Set.mem_singleton_iff.mp hm, Set.mem_singleton_iff.mp hs,
      commutatorElement_eq_one_iff_mul_comm.mpr]
    · exact one_mem _
    · calc d.u₁ * φ = (φ * d.u₁ * φ⁻¹) * φ := by rw [hF.φ_u₁]
        _ = φ * d.u₁ := by group

include hl in
theorem Wp_le_V₂ : ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ ≤ d.V₂ :=
  (commutator_mono_left (h.commQp_le_M₁p hF hd₀ hB hV hθ hl)).trans
    (h.commM₁p_le_V₂ hF hd₀ hB hV hθ hl)

omit [Finite G] h hF hd₀ hB hV hθ in
theorem W₁_le_Wp : ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ ≤ ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ :=
  commutator_mono (commutator_mono le_sup_left le_sup_left) le_sup_left

include hl in
theorem mem_D₄_of_cent_p {q : G} (hq : q ∈ d.Qp φ)
    (hc : ∀ w ∈ d.Z₂S ⊔ d.V₁, q * w = w * q) : q ∈ d.D₄ := by
  rw [Data.Qp, mem_sup_zpowers_of_normalizer (h.φ_mem_normalizer_Q₁ hF) (h.φ_sq_mem_Q₁ hF)] at hq
  rcases hq with hq | hq
  · exact h.mem_D₄_of_cent hd₀ hB hV hθ hq hc
  exfalso
  obtain ⟨k, v, ε, he⟩ := h.exists_Q₁_coords hd₀ hB hV hθ hq
  have hq' : q = (d.xs k * h.kap hd₀ v * (if ε then d.t else 1)) * φ := by rw [← he]; group
  have hfix : ∀ w, h.kap hd₀ w ∈ d.Z₂S ⊔ d.V₁ →
      (mX k * mTe ε * mPhi l).mulVec w = w := fun w hw => by
    apply h.kap_injective hd₀ hB hV hθ
    have e1 : q * h.kap hd₀ w * q⁻¹ = h.kap hd₀ ((mX k * mTe ε * mPhi l).mulVec w) := by
      rw [hq', ← Matrix.mulVec_mulVec, ← h.conj_Q₁_kap hd₀ hB hV hθ k v ε,
        ← h.conj_φ_kap hF hB hV hd₀ hl]
      group
    rw [← e1, hc _ hw, mul_inv_cancel_right]
  have h₁ : h.kap hd₀ vw₁ ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_left ((h.kap_mem_Z₂S_iff hd₀ hB hV hθ _).mpr (by decide))
  have h₂ : h.kap hd₀ vw₂ ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_left ((h.kap_mem_Z₂S_iff hd₀ hB hV hθ _).mpr (by decide))
  have h₃ : h.kap hd₀ vn ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_right ((h.kap_mem_V₁_iff hd₀ hB hV hθ _).mpr (by decide))
  rcases moved_test_phi l k ε with hm | hm | hm
  · exact hm (hfix _ h₁)
  · exact hm (hfix _ h₂)
  · exact hm (hfix _ h₃)

include hl in
theorem Wp_le_D₄ : ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ ≤ d.D₄ :=
  (h.Wp_le_V₂ hF hd₀ hB hV hθ hl).trans h.V₂_le_D₄

include hl in
theorem D₄_eq_inf_cent_p :
    d.D₄ = d.Qp φ ⊓ centralizer ((⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ : Subgroup G) : Set G) := by
  refine le_antisymm (le_inf (h.D₄_le_Q₁.trans le_sup_left) fun x hx =>
    mem_centralizer_iff.mpr fun w hw => h.D₄_comm (h.Wp_le_D₄ hF hd₀ hB hV hθ hl hw) hx) ?_
  rintro q ⟨hq, hc⟩
  refine h.mem_D₄_of_cent_p hF hd₀ hB hV hθ hl hq fun w hw => ?_
  have hw' : w ∈ ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ := W₁_le_Wp
    (sup_le (h.Z₂S_le_W₁ hd₀ hB hV hθ) (h.V₁_le_W₁ hd₀ hB hV hθ) hw)
  exact ((mem_centralizer_iff.mp hc) w hw').symm

include hl in
theorem inf_H_Wp : ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ ⊓ d.H = d.Z₂S := by
  have hZW : d.Z₂S ≤ ⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ := fun _ hx =>
    W₁_le_Wp (h.Z₂S_le_W₁ hd₀ hB hV hθ hx)
  refine le_antisymm (fun x hx => ?_)
    (le_inf hZW (h.Z₂S_le_A₄.trans (h.A₄_le_L.trans h.L_le_H)))
  rw [← h.V₂_inf_H]
  exact ⟨h.Wp_le_V₂ hF hd₀ hB hV hθ hl hx.1, hx.2⟩

include hl in
theorem D₁_le_normalizer_Wp (hC : HypC d) :
    d.D₁ ≤ normalizer ((⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ : Subgroup G) : Set G) :=
  h.D₁_le_normalizer_of hB hC hV
    (fun _ hx => W₁_le_Wp (h.V₁_le_W₁ hd₀ hB hV hθ hx))
    ((h.Wp_le_V₂ hF hd₀ hB hV hθ hl).trans (h.V₂_le_D₁ hB hV))

include hl in
theorem φ_comm_z : φ * d.z = d.z * φ := by
  obtain ⟨w, hw⟩ := h.exists_kap hd₀ hB hV hθ (h.A₄_le_D₄ h.z_mem_A₄)
  have hzV : d.z ∈ d.V₁ := h.z_mem_V₁
  rw [← hw, h.kap_mem_V₁_iff hd₀ hB hV hθ] at hzV
  have hzA : hiPart w = 0 := by
    rw [← h.kap_mem_A₄_iff hd₀ hB hV hθ, hw]; exact h.z_mem_A₄
  rcases fixed_A₄_eq w hzV.1 hzV.2 hzA with rfl | rfl
  · exact absurd (hw.symm.trans (h.kap_zero hd₀)) h.z_ne_one
  · have e := h.conj_φ_kap hF hB hV hd₀ hl vz
    rw [mPhi_vz, hw] at e
    calc φ * d.z = φ * d.z * φ⁻¹ * φ := by group
      _ = d.z * φ := by rw [e]

include hl in
theorem φ_mem_normalizer_R₀ : φ ∈ normalizer (d.R₀ : Set G) := by
  have hz : φ ∈ centralizer ({d.z} : Set G) ⊓ d.H :=
    ⟨mem_centralizer_singleton_iff.mpr (h.φ_comm_z hF hd₀ hB hV hθ hl), φ_mem_H hF⟩
  have hE : φ ∈ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf (Hyp.XV_le_normalizer_D₁ (h.X_le_XV (CHz_le_X hz)))
      (mem_normalizer_cent_of_comm hF.φ_comm_e)
  have ha : φ * d.a₀ = d.a₀ * φ := by
    calc φ * d.a₀ = φ * d.a₀ * φ⁻¹ * φ := by group
      _ = d.a₀ * φ := by rw [hF.φ_a₀]
  rw [Data.R₀_def]
  exact mem_normalizer_sup (mem_normalizer_sup hE (mem_normalizer_zpowers ha))
    (mem_normalizer_zpowers hF.φ_comm_t)

include hl in
theorem not_sylow_Qp (hC : HypC d) (hQ : HypQ d) :
    ∃ R : Subgroup G, R ≤ centralizer ({d.e} : Set G) ∧ IsPGroup 2 R ∧
      Nat.card (d.Qp φ) < Nat.card R := by
  have hφN := h.φ_mem_normalizer_R₀ hF hd₀ hB hV hθ hl
  have hφ : φ ∉ d.R₀ := fun hφ => hF.φ_not_mem (h.R₀_inf_H hB hV hφ (φ_mem_H hF))
  refine ⟨d.R₀ ⊔ zpowers φ, sup_le h.R₀_le_cent_e (zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr hF.φ_comm_e)), (h.isPGroup_R₀ hB hV).to_sup_of_normal_left'
    (isPGroup_zpowers_φ h hF) (zpowers_le.mpr hφN), ?_⟩
  have c1 := two_mul_card_le_card_sup hφ
  have c2 := h.card_R₀ hB hV hC hQ hd₀ hθ
  rw [h.card_Qp hF hB hV]
  omega

omit hF hd₀ hB hV hθ in
theorem u₁_ne_one : d.u₁ ≠ 1 := by
  intro h1
  have hle : d.X₁ ≤ zpowers d.u₂ := by
    intro x hx
    rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · rw [h1]; exact one_mem _
    · exact mem_zpowers _
    · rw [h1, one_mul]; exact mem_zpowers _
  have hc := Subgroup.card_le_of_le hle
  rw [h.card_X₁, Nat.card_zpowers] at hc
  have := orderOf_le_of_pow_eq_one (x := d.u₂) (n := 2) (by norm_num)
    (by rw [sq]; exact h.u₂_sq)
  omega

omit hd₀ hB hV hθ in
theorem comm_t_Qp {s : G} (hs : s ∈ d.Qp φ) : ⁅d.t, s⁆ ∈ d.D₄ := by
  have hS : ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t} ∪ {φ}, s ∈ normalizer (d.D₄ : Set G) := by
    rintro s (((hs | hs) | hs) | hs)
    · exact h.X₁_le_normalizer_D₄ hs
    · exact le_normalizer hs
    · rw [Set.mem_singleton_iff.mp hs]; exact h.t_mem_normalizer_D₄
    · rw [Set.mem_singleton_iff.mp hs]; exact h.φ_mem_normalizer_D₄ hF
  have hT : ∀ m ∈ ({d.t} : Set G), m ∈ normalizer (d.D₄ : Set G) := by
    rintro m hm; rw [Set.mem_singleton_iff.mp hm]; exact h.t_mem_normalizer_D₄
  have key := commutator_closure_le hS hT (by
    rintro m hm s (((hs | hs) | hs) | hs) <;> rw [Set.mem_singleton_iff.mp hm]
    · rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.comm_of_mem_L (h.X₁_le_L hs)).symm]
      exact one_mem _
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp h.t_mem_normalizer_D₄ s).mp hs) (inv_mem hs)
    · rw [Set.mem_singleton_iff.mp hs, commutatorElement_self]; exact one_mem _
    · rw [Set.mem_singleton_iff.mp hs,
        commutatorElement_eq_one_iff_mul_comm.mpr hF.φ_comm_t.symm]
      exact one_mem _)
  rw [← h.Qp_eq_closure] at key
  exact key (commutator_mem_commutator (subset_closure rfl) hs)

theorem fusion_Qp (hQ : HypQ d) {x₀ : G} (hx₀Q : x₀ ∈ normalizer (d.Qp φ : Set G))
    (hx₀D : x₀ ∈ normalizer (d.D₄ : Set G)) (hq : x₀⁻¹ * d.t * x₀ ∈ d.Qp φ) :
    ∃ x ∈ d.X₁, ∃ c ∈ d.D₄, x₀⁻¹ * d.t * x₀ = x * c * d.t := by
  set q := x₀⁻¹ * d.t * x₀ with hqdef
  have hu₂ : d.u₂ ∈ d.Qp φ := mem_sup_left (X₁_le_Q₁ h.u₂_mem)
  have hcq : ⁅q, d.u₂⁆ ∈ d.D₄ := by
    have hs : x₀ * d.u₂ * x₀⁻¹ ∈ d.Qp φ := (mem_normalizer_iff.mp hx₀Q _).mp hu₂
    have h1 := h.comm_t_Qp hF hs
    have e : ⁅q, d.u₂⁆ = x₀⁻¹ * ⁅d.t, x₀ * d.u₂ * x₀⁻¹⁆ * x₀⁻¹⁻¹ := by
      rw [hqdef]; simp only [commutatorElement_def]; group
    rw [e]
    exact (mem_normalizer_iff.mp (inv_mem hx₀D) _).mp h1
  rw [Data.Qp, mem_sup_zpowers_of_normalizer (h.φ_mem_normalizer_Q₁ hF) (h.φ_sq_mem_Q₁ hF)] at hq
  rcases hq with hq | hq
  · exact h.fusion_Q₁ hB hV hQ hd₀ hθ hq
  exfalso
  obtain ⟨k, v, ε, he⟩ := h.exists_Q₁_coords hd₀ hB hV hθ hq
  set τ := (if ε then d.t else 1) with hτ
  have hτL : ∀ y ∈ d.X₁, τ * y * τ⁻¹ = y := fun y hy => by
    rw [hτ]; split_ifs
    · rw [← h.comm_of_mem_L (h.X₁_le_L hy), mul_inv_cancel_right]
    · group
  have hconj : ∀ y ∈ d.X₁, ∃ c ∈ d.D₄,
      (d.xs k * h.kap hd₀ v * τ) * y * (d.xs k * h.kap hd₀ v * τ)⁻¹ = c * y := by
    intro y hy
    set c₀ := h.kap hd₀ v * y * (h.kap hd₀ v)⁻¹ * y⁻¹ with hc₀
    have hc₀D : c₀ ∈ d.D₄ := by
      have e : c₀ = h.kap hd₀ v * (y * (h.kap hd₀ v)⁻¹ * y⁻¹) := by rw [hc₀]; group
      rw [e]
      exact mul_mem (h.kap_mem hd₀ v) ((mem_normalizer_iff.mp (h.X₁_le_normalizer_D₄ hy)
        _).mp (inv_mem (h.kap_mem hd₀ v)))
    refine ⟨d.xs k * c₀ * (d.xs k)⁻¹,
      (mem_normalizer_iff.mp (h.X₁_le_normalizer_D₄ (h.xs_mem k)) _).mp hc₀D, ?_⟩
    have hxy : d.xs k * y * (d.xs k)⁻¹ = y := by
      rw [h.X₁_comm (h.xs_mem k) hy, mul_inv_cancel_right]
    calc (d.xs k * h.kap hd₀ v * τ) * y * (d.xs k * h.kap hd₀ v * τ)⁻¹
        = d.xs k * (h.kap hd₀ v * (τ * y * τ⁻¹) * (h.kap hd₀ v)⁻¹) * (d.xs k)⁻¹ := by group
      _ = d.xs k * (c₀ * y) * (d.xs k)⁻¹ := by rw [hτL y hy, hc₀]; group
      _ = (d.xs k * c₀ * (d.xs k)⁻¹) * (d.xs k * y * (d.xs k)⁻¹) := by group
      _ = d.xs k * c₀ * (d.xs k)⁻¹ * y := by rw [hxy]
  obtain ⟨c, hc, hcy⟩ := hconj _ (mul_mem h.u₁_mem h.u₂_mem)
  have hq' : q = (d.xs k * h.kap hd₀ v * τ) * φ := by rw [← he]; group
  have e2 : ⁅q, d.u₂⁆ = c * d.u₁ := by
    rw [commutatorElement_def, hq']
    calc d.xs k * h.kap hd₀ v * τ * φ * d.u₂ * (d.xs k * h.kap hd₀ v * τ * φ)⁻¹ * d.u₂⁻¹
        = (d.xs k * h.kap hd₀ v * τ) * (φ * d.u₂ * φ⁻¹) * (d.xs k * h.kap hd₀ v * τ)⁻¹ *
          d.u₂⁻¹ := by group
      _ = c * d.u₁ := by rw [hF.φ_u₂, hcy]; group
  rw [e2] at hcq
  have hu₁D : d.u₁ ∈ d.D₄ := by
    have e3 : d.u₁ = c⁻¹ * (c * d.u₁) := by group
    rw [e3]; exact mul_mem (inv_mem hc) hcq
  exact h.u₁_ne_one (h.X₁_inf_D₄ hB hV hd₀ hθ h.u₁_mem hu₁D)

end W

theorem configN_f (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d)
    {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀) {l : Fin 4 → ZMod 2}
    (hl : φ * d₀ * φ⁻¹ = d₀ * h.kap hd₀ (lo l)) :
    ConfigN (centralizer ({d.e} : Set G)) d.D₄ d.X₁ (d.Qp φ) d.J (⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆)
      (d.D₁ ⊓ centralizer ({d.e} : Set G)) d.t := by
  have P := h.configPart hB hV hQ.CA₁e
  have hW : ∀ y : G, y ∈ normalizer (d.Qp φ : Set G) →
      y ∈ normalizer ((⁅⁅d.Qp φ, d.Qp φ⁆, d.Qp φ⁆ : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_commutator (mem_normalizer_commutator hy hy) hy
  have hD : ∀ y : G, y ∈ normalizer (d.Qp φ : Set G) → y ∈ normalizer (d.D₄ : Set G) :=
    fun y hy => by
      rw [h.D₄_eq_inf_cent_p hF hd₀ hB hV hθ hl]
      exact mem_normalizer_inf_centralizer hy (hW y hy)
  refine
    { t_sq := P.t_sq, D_le := P.D_le, D_comm := P.D_comm, D_sq := P.D_sq, t_normD := P.t_normD,
      D_conj := P.D_conj, normD_of_norm := P.normD_of_norm,
      Q_le := h.Qp_le_cent_e hF hQ, t_memQ := h.t_mem_Qp, Q_pGroup := h.isPGroup_Qp hF,
      Q_le_norm := h.Qp_le_normalizer hF,
      Q_max := Q_max_of_card_le fun R hR hRY hRN => ?_,
      Q_not_sylow := h.not_sylow_Qp hF hd₀ hB hV hθ hl hC hQ,
      normD_of_normQ := fun y _ hy => hD y hy,
      normW_of_normQ := fun y _ hy => hW y hy,
      fusion := fun y _ hyN hy => h.fusion_Qp hF hd₀ hB hV hθ hQ hyN (hD y hyN) hy,
      J_le := h.J_le_cent_e hQ, J_comm := fun j hj => h.J_comm_t hj,
      J_normX := h.J_le_normalizer_X₁, J_normD := h.J_le_normalizer_D₄, J_trans := h.J_trans,
      W_le := h.Wp_le_D₄ hF hd₀ hB hV hθ hl,
      E_le := P.E_le, E_t := P.E_t,
      E_normW := fun j hj u hu => ?_,
      normW_cent := fun j hj c hcY hct hcW => ?_ }
  ·
    rw [h.centInvSup_D₄] at hRN
    have h1 := h.card_le_of_normalizer R hRN
    have h2 : R ⊓ centralizer ({d.t} : Set G) ≤
        d.H ⊓ centralizer ({d.e} : Set G) ⊓ normalizer (d.A₄ : Set G) := fun x hx =>
      ⟨⟨hx.2, hRY hx.1⟩, h.X₄_le_normalizer_A₄ (hRN hx.1)⟩
    have h3 := hF.card_le _ h2 (hR.to_le inf_le_left)
    rw [h.card_Qp hF hB hV]
    calc Nat.card R ≤ 2 ^ 4 * Nat.card (R ⊓ centralizer ({d.t} : Set G) : Subgroup G) := h1
      _ ≤ 2 ^ 4 * 2 ^ 8 := by gcongr
      _ = 2 ^ 12 := by norm_num
  ·
    have hju := (mem_normalizer_iff.mp (h.J_le_normalizer_E₁ hQ hj) u).mp hu
    exact h.D₁_le_normalizer_Wp hF hd₀ hB hV hθ hl hC hju.1
  ·
    have hjH : j ∈ d.H := h.L_le_H (h.J_le_L hj)
    have hcH : c ∈ d.H := mem_centralizer_singleton_iff.mpr hct
    have hc'H : j * c * j⁻¹ ∈ d.H := d.H.mul_mem (d.H.mul_mem hjH hcH) (d.H.inv_mem hjH)
    have hc'e : j * c * j⁻¹ ∈ centralizer ({d.e} : Set G) :=
      mul_mem (mul_mem (h.J_le_cent_e hQ hj) hcY) (inv_mem (h.J_le_cent_e hQ hj))
    have hc'Z : j * c * j⁻¹ ∈ normalizer (d.Z₂S : Set G) := by
      rw [← h.inf_H_Wp hF hd₀ hB hV hθ hl]
      exact mem_normalizer_inf hcW (le_normalizer hc'H)
    have hc'A := hQ.NZ₂S _ hc'H (mem_centralizer_singleton_iff.mp hc'e) hc'Z
    have hjA : j ∈ normalizer (d.A₄ : Set G) := h.X₄_le_normalizer_A₄ (h.J_le_X₄ hj)
    have hcA : c ∈ normalizer (d.A₄ : Set G) := by
      have := mul_mem (mul_mem (inv_mem hjA) hc'A) hjA
      simpa [mul_assoc] using this
    rw [h.centInvSup_D₄, Data.withT]
    exact mem_normalizer_sup hcA (mem_normalizer_zpowers hct)

theorem lemmaQ_f (hB : HypB d) (hC : HypC d) (hV : ∀ v ∈ d.V₁, v * v = 1) (hQ : HypQ d) :
    d.D₁ ⊓ centralizer ({d.e} : Set G) ≤ normalizer (d.D₄ : Set G) ∧
      d.D₄ ≤ normalizer ((d.D₁ ⊓ centralizer ({d.e} : Set G) : Subgroup G) : Set G) ∧
      ⁅d.D₄, d.D₁ ⊓ centralizer ({d.e} : Set G)⁆ ≤ d.V₂ := by
  obtain ⟨d₀, hd₀, hθ⟩ := h.exists_d₀
  obtain ⟨l, hl⟩ := h.exists_twist hF hB hV hd₀ hθ
  exact (h.configN_f hF hB hC hV hQ hd₀ hθ hl).lemmaQ h.V₂_le_D₄ (h.V₂_le_E₁ hB hV)
    (h.E₁_le_normalizer_V₂ hB hC hV) h.J_le_normalizer_V₂ comm_D₄_J_mem_V₂
    (h.E₁_le_comm_sup hB hV hQ)

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
