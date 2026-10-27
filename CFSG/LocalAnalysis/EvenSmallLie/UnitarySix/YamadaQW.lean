module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQWData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.LemmaQ

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

namespace Data

theorem V₁_le_V₂ (d : Data G) : d.V₁ ≤ d.V₂ := le_sup_right

@[expose] def Q₁ (d : Data G) : Subgroup G := d.X₁ ⊔ d.D

end Data

namespace Hyp

variable [Finite G] {d : Data G} (h : Hyp d)
include h

theorem X₁_le_normalizer_D : d.X₁ ≤ normalizer (d.D : Set G) :=
  fun _ hx => h.X₄_le_normalizer_D (h.Λ_le_X₄ (h.X₁_le_Λ hx))

theorem mem_Q₁ {q : G} : q ∈ d.Q₁ ↔ ∃ x ∈ d.X₁, ∃ y ∈ d.D, q = x * y := by
  rw [Data.Q₁, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ h.X₁_le_normalizer_D]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩

theorem mem_D_iff {y : G} : y ∈ d.D ↔ y ∈ d.D₄ ∨ y * d.t ∈ d.D₄ := by
  rw [← h.withT_D₄, Data.withT, mem_sup_zpowers_of_normalizer h.t_mem_normalizer_D₄
    (by rw [h.t_sq]; exact one_mem _), h.t_inv]

omit [Finite G] h in
theorem D_le_Q₁ : d.D ≤ d.Q₁ := le_sup_right

omit [Finite G] h in
theorem X₁_le_Q₁ : d.X₁ ≤ d.Q₁ := le_sup_left

theorem D₄_le_Q₁ : d.D₄ ≤ d.Q₁ := h.D₄_le_D.trans D_le_Q₁

theorem t_mem_Q₁ : d.t ∈ d.Q₁ := D_le_Q₁ h.t_mem_D

omit [Finite G] in
theorem X₁_comm {x y : G} (hx : x ∈ d.X₁) (hy : y ∈ d.X₁) : x * y = y * x := by
  have hS : ∀ a ∈ ({d.u₁, d.u₂} : Set G), ∀ b ∈ ({d.u₁, d.u₂} : Set G), a * b = b * a := by
    rintro a (rfl | rfl) b (rfl | rfl)
    · rfl
    · exact h.u₁_comm_u₂
    · exact h.u₁_comm_u₂.symm
    · rfl
  exact comm_of_mem_closure hS (h.X₁_le_closure hx) (h.X₁_le_closure hy)

theorem Q₁_eq_closure : d.Q₁ = closure ((d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}) := by
  refine le_antisymm (sup_le (fun x hx => subset_closure (Or.inl (Or.inl hx))) ?_)
    ((closure_le _).mpr ?_)
  · rw [← h.withT_D₄]
    exact sup_le (fun x hx => subset_closure (Or.inl (Or.inr hx)))
      (zpowers_le.mpr (subset_closure (Or.inr rfl)))
  · rintro x ((hx | hx) | hx)
    · exact X₁_le_Q₁ hx
    · exact h.D₄_le_Q₁ hx
    · rw [Set.mem_singleton_iff.mp hx]; exact h.t_mem_Q₁

variable {d₀ : G} (hd₀ : d₀ ∈ d.D₄) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)

@[expose] def M₁ : Subgroup G := h.kapSub hd₀ hB hV (fun v => hiSum v = 0) hiSum_zero hiSum_add

variable (hθ : d₀⁻¹ * d.t * d₀ * d.t = d.a₀)
include hd₀ hB hV hθ

theorem exists_Q₁_coords {q : G} (hq : q ∈ d.Q₁) :
    ∃ k : Fin 4, ∃ v, ∃ ε : Bool, q = d.xs k * h.kap hd₀ v * (if ε then d.t else 1) := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h.mem_Q₁.mp hq
  obtain ⟨k, rfl⟩ := h.exists_xs hx
  rcases h.mem_D_iff.mp hy with hy | hy
  · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hy
    exact ⟨k, v, false, by simp⟩
  · obtain ⟨v, hv⟩ := h.exists_kap hd₀ hB hV hθ hy
    refine ⟨k, v, true, ?_⟩
    show d.xs k * y = d.xs k * h.kap hd₀ v * d.t
    rw [hv, mul_assoc, mul_assoc, h.t_sq, mul_one]

theorem conj_Q₁_kap (k : Fin 4) (v : Fin 8 → ZMod 2) (ε : Bool) (w : Fin 8 → ZMod 2) :
    (d.xs k * h.kap hd₀ v * (if ε then d.t else 1)) * h.kap hd₀ w *
      (d.xs k * h.kap hd₀ v * (if ε then d.t else 1))⁻¹ =
      h.kap hd₀ ((mX k * mTe ε).mulVec w) := by
  have hτ : (if ε then d.t else 1) * h.kap hd₀ w * (if ε then d.t else 1)⁻¹ =
      h.kap hd₀ ((mTe ε).mulVec w) := by
    cases ε
    · simp [mTe]
    · simpa [mTe] using h.conj_t_kap hd₀ hB hV hθ w
  have hc : h.kap hd₀ v * h.kap hd₀ ((mTe ε).mulVec w) * (h.kap hd₀ v)⁻¹ =
      h.kap hd₀ ((mTe ε).mulVec w) := by
    rw [h.D₄_comm (h.kap_mem hd₀ v) (h.kap_mem hd₀ _), mul_inv_cancel_right]
  rw [← Matrix.mulVec_mulVec, ← h.conj_xs_kap hd₀ hB hV, ← hc, ← hτ]
  group

omit hθ in
theorem mem_M₁_iff {g : G} : g ∈ h.M₁ hd₀ hB hV ↔ ∃ v, hiSum v = 0 ∧ h.kap hd₀ v = g :=
  Iff.rfl

omit hθ in
theorem M₁_le_D₄ : h.M₁ hd₀ hB hV ≤ d.D₄ := by
  rintro _ ⟨v, -, rfl⟩; exact h.kap_mem hd₀ v

omit hθ in
theorem conj_mem_M₁ {g : G} {M : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (hg : ∀ v, g * h.kap hd₀ v * g⁻¹ = h.kap hd₀ (M.mulVec v))
    (hM : ∀ v, hiSum (M.mulVec v) = hiSum v) : g ∈ normalizer (h.M₁ hd₀ hB hV : Set G) := by
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨M.mulVec v, by show hiSum (M.mulVec v) = 0; rw [hM, hv], (hg v).symm⟩

theorem gens_le_normalizer_M₁ :
    ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, s ∈ normalizer (h.M₁ hd₀ hB hV : Set G) := by
  rintro s ((hs | hs) | hs)
  · obtain ⟨k, rfl⟩ := h.exists_xs hs
    exact h.conj_mem_M₁ hd₀ hB hV (h.conj_xs_kap hd₀ hB hV k) (hiSum_mX k)
  · exact LemmaQ.mem_normalizer_of_le_comm h.D₄_comm' (h.M₁_le_D₄ hd₀ hB hV) hs
  · rw [Set.mem_singleton_iff.mp hs]
    exact h.conj_mem_M₁ hd₀ hB hV (h.conj_t_kap hd₀ hB hV hθ) hiSum_mT

omit [Finite G] hd₀ hB hV hθ in
theorem comm_xs_t (k : Fin 4) : ⁅d.xs k, d.t⁆ = 1 :=
  commutatorElement_eq_one_iff_mul_comm.mpr (h.comm_of_mem_L (h.xs_mem_L k))

theorem commQ₁_le_M₁ : ⁅d.Q₁, d.Q₁⁆ ≤ h.M₁ hd₀ hB hV := by
  have hN := h.gens_le_normalizer_M₁ hd₀ hB hV hθ
  have hX : ∀ k v, ⁅h.kap hd₀ v, d.xs k⁆ ∈ h.M₁ hd₀ hB hV := fun k v => by
    rw [h.comm_kap_left hd₀ hB hV (h.conj_xs_kap hd₀ hB hV k)]
    exact ⟨_, hiSum_comm_mX k v, rfl⟩
  have hT : ∀ v, ⁅h.kap hd₀ v, d.t⁆ ∈ h.M₁ hd₀ hB hV := fun v => by
    rw [h.comm_kap_left hd₀ hB hV (h.conj_t_kap hd₀ hB hV hθ)]
    exact ⟨_, hiSum_comm_mT v, rfl⟩
  have hD : ∀ {m s : G}, m ∈ d.D₄ → s ∈ d.D₄ → ⁅m, s⁆ ∈ h.M₁ hd₀ hB hV := fun hm hs => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.D₄_comm hm hs)]; exact one_mem _
  rw [h.Q₁_eq_closure]
  refine commutator_closure_le hN hN ?_
  rintro m ((hm | hm) | hm) s ((hs | hs) | hs)
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.X₁_comm hm hs)]; exact one_mem _
  · obtain ⟨k, rfl⟩ := h.exists_xs hm
    obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hs
    rw [← commutatorElement_inv]; exact inv_mem (hX k v)
  · obtain ⟨k, rfl⟩ := h.exists_xs hm
    rw [Set.mem_singleton_iff.mp hs, h.comm_xs_t]; exact one_mem _
  · obtain ⟨k, rfl⟩ := h.exists_xs hs
    obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hm
    exact hX k v
  · exact hD hm hs
  · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hm
    rw [Set.mem_singleton_iff.mp hs]; exact hT v
  · obtain ⟨k, rfl⟩ := h.exists_xs hs
    rw [Set.mem_singleton_iff.mp hm, ← commutatorElement_inv, h.comm_xs_t, inv_one]
    exact one_mem _
  · obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ hs
    rw [Set.mem_singleton_iff.mp hm, ← commutatorElement_inv]; exact inv_mem (hT v)
  · rw [Set.mem_singleton_iff.mp hm, Set.mem_singleton_iff.mp hs, commutatorElement_self]
    exact one_mem _

omit hd₀ hB hθ in
theorem X₁_le_normalizer_V₂ : d.X₁ ≤ normalizer (d.V₂ : Set G) := fun x hx =>
  mem_normalizer_of_conj_mem fun y hy => by
    have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (d.V₁_le_V₂ (h.comm_X₁_V₂ hV hx hy)) hy

omit hd₀ hB hθ in
theorem gens_le_normalizer_V₂ :
    ∀ s ∈ (d.X₁ : Set G) ∪ d.D₄ ∪ {d.t}, s ∈ normalizer (d.V₂ : Set G) := by
  rintro s ((hs | hs) | hs)
  · exact h.X₁_le_normalizer_V₂ hV hs
  · exact LemmaQ.mem_normalizer_of_le_comm h.D₄_comm' h.V₂_le_D₄ hs
  · rw [Set.mem_singleton_iff.mp hs]; exact h.t_mem_normalizer_V₂

theorem commM₁_le_V₂ : ⁅h.M₁ hd₀ hB hV, d.Q₁⁆ ≤ d.V₂ := by
  rw [h.Q₁_eq_closure, ← (h.M₁ hd₀ hB hV).closure_eq]
  refine commutator_closure_le (h.gens_le_normalizer_V₂ hV)
    (fun m hm => LemmaQ.mem_normalizer_of_le_comm h.D₄_comm' h.V₂_le_D₄
      (h.M₁_le_D₄ hd₀ hB hV hm)) ?_
  rintro _ ⟨v, hv, rfl⟩ s ((hs | hs) | hs)
  · obtain ⟨k, rfl⟩ := h.exists_xs hs
    rw [h.comm_kap_left hd₀ hB hV (h.conj_xs_kap hd₀ hB hV k), h.kap_mem_V₂_iff hd₀ hB hV hθ]
    exact augZ_comm_mX k v hv
  · rw [commutatorElement_eq_one_iff_mul_comm.mpr (h.D₄_comm (h.kap_mem hd₀ v) hs)]
    exact one_mem _
  · rw [Set.mem_singleton_iff.mp hs, h.comm_kap_left hd₀ hB hV (h.conj_t_kap hd₀ hB hV hθ),
      h.kap_mem_V₂_iff hd₀ hB hV hθ]
    exact augZ_comm_mT v hv

theorem W₁_le_V₂ : ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ ≤ d.V₂ :=
  (commutator_mono_left (h.commQ₁_le_M₁ hd₀ hB hV hθ)).trans (h.commM₁_le_V₂ hd₀ hB hV hθ)

omit hB hV hθ in
theorem kap_smul_mem {K : Subgroup G} (a : ZMod 2) {w : Fin 8 → ZMod 2}
    (hw : h.kap hd₀ w ∈ K) : h.kap hd₀ (a • w) ∈ K := by
  rcases zmod_two_cases a with rfl | rfl
  · rw [zero_smul, h.kap_zero]; exact one_mem _
  · rwa [one_smul]

omit hθ in
theorem kap_comm₂_mem {j : Fin 8} {g₁ g₂ : G} {M₁' M₂' : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h₁ : ∀ v, g₁ * h.kap hd₀ v * g₁⁻¹ = h.kap hd₀ (M₁'.mulVec v))
    (h₂ : ∀ v, g₂ * h.kap hd₀ v * g₂⁻¹ = h.kap hd₀ (M₂'.mulVec v))
    (hg₁ : g₁ ∈ d.Q₁) (hg₂ : g₂ ∈ d.Q₁) {w : Fin 8 → ZMod 2}
    (hw : Pi.single j 1 + M₁'.mulVec (Pi.single j 1) +
      M₂'.mulVec (Pi.single j 1 + M₁'.mulVec (Pi.single j 1)) = w) :
    h.kap hd₀ w ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ := by
  have hmem := commutator_mem_commutator (commutator_mem_commutator
    (h.D₄_le_Q₁ (h.kap_mem hd₀ (Pi.single j 1))) hg₁) hg₂
  rwa [h.comm_kap_left hd₀ hB hV h₁, h.comm_kap_left hd₀ hB hV h₂, hw] at hmem

theorem kap_vw₁_mem : h.kap hd₀ vw₁ ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ :=
  h.kap_comm₂_mem hd₀ hB hV (h.conj_t_kap hd₀ hB hV hθ) (h.conj_u₁_kap hd₀ hB hV)
    h.t_mem_Q₁ (X₁_le_Q₁ h.u₁_mem) comm_vw₁

theorem kap_vw₂_mem : h.kap hd₀ vw₂ ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ :=
  h.kap_comm₂_mem hd₀ hB hV (h.conj_t_kap hd₀ hB hV hθ) (h.conj_u₂_kap hd₀ hB hV)
    h.t_mem_Q₁ (X₁_le_Q₁ h.u₂_mem) comm_vw₂

omit hθ in
theorem kap_vz_mem : h.kap hd₀ vz ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ :=
  h.kap_comm₂_mem hd₀ hB hV (h.conj_u₂_kap hd₀ hB hV) (h.conj_u₁_kap hd₀ hB hV)
    (X₁_le_Q₁ h.u₂_mem) (X₁_le_Q₁ h.u₁_mem) comm_vz

omit hθ in
theorem kap_vn_mem : h.kap hd₀ vn ∈ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ :=
  h.kap_comm₂_mem hd₀ hB hV (h.conj_u₂_kap hd₀ hB hV) (h.conj_u₁_kap hd₀ hB hV)
    (X₁_le_Q₁ h.u₂_mem) (X₁_le_Q₁ h.u₁_mem) comm_vn

theorem Z₂S_le_W₁ : d.Z₂S ≤ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ := by
  intro g hg
  obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ (h.A₄_le_D₄ (h.Z₂S_le_A₄ hg))
  obtain ⟨a, b, c, rfl⟩ := span_Z₂S v ((h.kap_mem_Z₂S_iff hd₀ hB hV hθ v).mp hg)
  rw [h.kap_add hd₀ hB hV, h.kap_add hd₀ hB hV]
  exact mul_mem (mul_mem (h.kap_smul_mem hd₀ a (h.kap_vw₁_mem hd₀ hB hV hθ))
    (h.kap_smul_mem hd₀ b (h.kap_vw₂_mem hd₀ hB hV hθ)))
    (h.kap_smul_mem hd₀ c (h.kap_vz_mem hd₀ hB hV))

theorem V₁_le_W₁ : d.V₁ ≤ ⁅⁅d.Q₁, d.Q₁⁆, d.Q₁⁆ := by
  intro g hg
  obtain ⟨v, rfl⟩ := h.exists_kap hd₀ hB hV hθ (V₁_le_D₄ hg)
  obtain ⟨a, b, rfl⟩ := span_V₁ v ((h.kap_mem_V₁_iff hd₀ hB hV hθ v).mp hg)
  rw [h.kap_add hd₀ hB hV]
  exact mul_mem (h.kap_smul_mem hd₀ a (h.kap_vz_mem hd₀ hB hV))
    (h.kap_smul_mem hd₀ b (h.kap_vn_mem hd₀ hB hV))

theorem mem_D₄_of_cent {q : G} (hq : q ∈ d.Q₁)
    (hc : ∀ w ∈ d.Z₂S ⊔ d.V₁, q * w = w * q) : q ∈ d.D₄ := by
  obtain ⟨k, v, ε, rfl⟩ := h.exists_Q₁_coords hd₀ hB hV hθ hq
  by_cases hkε : k = 0 ∧ ε = false
  · obtain ⟨rfl, rfl⟩ := hkε
    simpa [Data.xs] using h.kap_mem hd₀ v
  have hfix : ∀ w, h.kap hd₀ w ∈ d.Z₂S ⊔ d.V₁ → (mX k * mTe ε).mulVec w = w := fun w hw => by
    apply h.kap_injective hd₀ hB hV hθ
    rw [← h.conj_Q₁_kap hd₀ hB hV hθ k v ε w, hc _ hw, mul_inv_cancel_right]
  have h₁ : h.kap hd₀ vw₁ ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_left ((h.kap_mem_Z₂S_iff hd₀ hB hV hθ _).mpr (by decide))
  have h₂ : h.kap hd₀ vw₂ ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_left ((h.kap_mem_Z₂S_iff hd₀ hB hV hθ _).mpr (by decide))
  have h₃ : h.kap hd₀ vn ∈ d.Z₂S ⊔ d.V₁ :=
    mem_sup_right ((h.kap_mem_V₁_iff hd₀ hB hV hθ _).mpr (by decide))
  rcases moved_test k ε hkε with hm | hm | hm
  · exact absurd (hfix _ h₁) hm
  · exact absurd (hfix _ h₂) hm
  · exact absurd (hfix _ h₃) hm

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
