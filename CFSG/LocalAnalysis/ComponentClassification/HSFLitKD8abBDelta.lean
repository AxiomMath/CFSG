module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBAct

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def inC (x : MB) : Bool := !bit x 0 && !bit x 1 && !bit x 2 && !bit x 4 && !bit x 5

@[expose] def Ch : Subgroup MB := ofPred inC (by decide +kernel) (by decide +kernel)
  (by decide +kernel)

@[expose] def A1c : List MB := [w₂, w₂ * k, w₂ * y, w₂ * y * k, w₂ * z, w₂ * z * k, w₂ * z * y,
  w₂ * z * y * k]

@[expose] def A2c : List MB := [w₂ * w₁, w₂ * w₁ * k, w₂ * w₁ * y, w₂ * w₁ * y * k, w₂ * w₁ * z,
  w₂ * w₁ * z * k, w₂ * w₁ * z * y, w₂ * w₁ * z * y * k]

@[expose] def dCand (a1 a2 : MB) : List MB := [a2, a1, v, y, z * y, t, k]

@[expose] def d3List : List (List MB) :=
  (A1c.flatMap fun a1 => A2c.map fun a2 => dCand a1 a2).filter fun f =>
    compQ1 f (compQ1 f f) == gensQ1

theorem mem_A1c : ∀ a : MB, inQ0 a = true → a * a = y → a ∈ A1c := by decide +kernel

theorem mem_A2c : ∀ a : MB, inQ0 a = true → a * a = z * y → a ∈ A2c := by decide +kernel

theorem dCand_order : ∀ a1 ∈ A1c, ∀ a2 ∈ A2c,
    compQ1 (compQ1 (dCand a1 a2) (compQ1 (dCand a1 a2) (dCand a1 a2)))
      (compQ1 (dCand a1 a2) (compQ1 (dCand a1 a2) (dCand a1 a2))) = gensQ1 := by decide +kernel

theorem dCand_mem : ∀ a1 ∈ A1c, ∀ a2 ∈ A2c, ∀ g ∈ dCand a1 a2, inQ1 g = true := by
  decide +kernel

theorem z_not_inC : inC z = false := by decide +kernel

theorem inC_t : inC t = true := by decide +kernel
theorem inC_k : inC k = true := by decide +kernel
theorem inC_v : inC v = true := by decide +kernel
theorem inC_vt : inC (v * t) = true := by decide +kernel

theorem inQ0_w₂ : inQ0 w₂ = true := by decide +kernel
theorem inQ0_w₁ : inQ0 w₁ = true := by decide +kernel
theorem inQ0_of_inE0 : ∀ x : MB, inE0 x = true → inQ0 x = true := by decide +kernel
theorem nfBitsQ1_gens : bitsQ1 w₂ = [true, false, false, false, false, false, false] ∧
    bitsQ1 w₁ = [false, true, false, false, false, false, false] ∧
    bitsQ1 v = [false, false, true, false, false, false, false] ∧
    bitsQ1 z = [false, false, false, true, false, false, false] ∧
    bitsQ1 y = [false, false, false, false, true, false, false] ∧
    bitsQ1 t = [false, false, false, false, false, true, false] ∧
    bitsQ1 k = [false, false, false, false, false, false, true] := by decide +kernel

theorem applyQ1_gens (f : List MB) (hf : f.length = 7) :
    gensQ1.map (applyQ1 f) = f := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := nfBitsQ1_gens
  match f, hf with
  | [a, b, c, d, e, f, g], _ =>
    simp [gensQ1, applyQ1, h1, h2, h3, h4, h5, h6, h7, nfProd]

theorem compQ1_mem {f g : List MB} (hf : ∀ x ∈ f, inQ1 x = true) :
    ∀ x ∈ compQ1 f g, inQ1 x = true := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact KD8abB.nfProd_mem (H := Q1h) f _ hf

theorem compQ1_gensQ1 (f : List MB) (hf : f.length = 7) : compQ1 f gensQ1 = f :=
  applyQ1_gens f hf

theorem gensQ1_length : gensQ1.length = 7 := rfl

theorem E0h_cases : ∀ e : MB, inE0 e = true →
    e ∈ [1, z, y, z * y] ∨ ∃ e' ∈ [1, z, y, z * y], e = e' * k := by decide +kernel

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable (B : BData S T₁)

theorem ι_mem_L_of {e : MB} (he : e ∈ [1, MB.z, MB.y, MB.z * MB.y]) : B.ι e ∈ L := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  have hz : S.z ∈ L := z_mem_L S
  have hy : S.y ∈ L := S.y_mem.2
  rcases he with rfl | rfl | rfl | rfl
  · rw [map_one]; exact one_mem L
  · rw [B.ι_z]; exact hz
  · rw [B.ι_y]; exact hy
  · rw [map_mul, B.ι_z, B.ι_y]; exact mul_mem hz hy

theorem mem_ZY_of {e : MB} (he : MB.inE0 e = true) (hL : B.ι e ∈ L) :
    e ∈ [1, MB.z, MB.y, MB.z * MB.y] := by
  rcases MB.E0h_cases e he with h | ⟨e', he', rfl⟩
  · exact h
  · exfalso
    apply k_not_mem_L (C := C)
    have := mul_mem (inv_mem (B.ι_mem_L_of he')) hL
    rwa [map_mul, B.ι_k, inv_mul_cancel_left] at this

theorem E0_eq : S.E0 S.y S.k = MB.E0h.map B.ι := by
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩
    exact B.ι_mem_E0 hx
  · rw [card_map_of_injective B.ι_injective, MB.card_E0h]
    exact (frame₁ S).card_E0.le

theorem mem_E0_iff {g : X} : g ∈ S.E0 S.y S.k ↔ ∃ x : MB, MB.inE0 x = true ∧ B.ι x = g := by
  rw [B.E0_eq]; exact Iff.rfl

theorem C_le : closure ({t, S.k, B.G.D₁.v} : Set X) ≤ MB.Ch.map B.ι := by
  rw [closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact ⟨MB.t, MB.inC_t, B.ι_t⟩
  · exact ⟨MB.k, MB.inC_k, B.ι_k⟩
  · rcases B.G.V₁.vN_eq with h | h
    · exact ⟨MB.v, MB.inC_v, by rw [B.ι_v]; exact h⟩
    · refine ⟨MB.v * MB.t, MB.inC_vt, ?_⟩
      rw [map_mul, B.ι_v, B.ι_t]
      change B.G.V₁.vN * t = B.G.V₁.D.v
      rw [h, mul_assoc, KD7.tt (A := A), mul_one]

theorem z_not_mem_C : S.z ∉ closure ({t, S.k, B.G.D₁.v} : Set X) := by
  intro h
  obtain ⟨x, hx, hxz⟩ := B.C_le h
  rw [← B.ι_z] at hxz
  have := B.ι_injective hxz
  subst this
  have : MB.inC MB.z = true := hx
  rw [MB.z_not_inC] at this
  exact Bool.false_ne_true this

theorem exists_D₁₁_moves_z : ∃ δ ∈ B.G.D₁.D₁₁, δ * S.z * δ⁻¹ ≠ S.z := by
  by_contra h
  push Not at h
  apply B.z_not_mem_C
  have hzQ : S.z ∈ B.G.D₁.Q₁ := B.G.D₁.Q0_le (B.G.V₁.E0_le_Q0 B.G.V₁.z_mem_E0)
  have hzC : S.z ∈ centralizer (B.G.D₁.D₁₁ : Set X) := by
    rw [mem_centralizer_iff]
    intro δ hδ
    have := h δ hδ
    calc δ * S.z = δ * S.z * δ⁻¹ * δ := by group
      _ = S.z * δ := by rw [this]
  have := B.G.D₁.C_eq ▸ (show S.z ∈ B.G.D₁.Q₁ ⊓ centralizer (B.G.D₁.D₁₁ : Set X) from ⟨hzQ, hzC⟩)
  exact this

theorem conj_ZY {n : X} (hnE : n ∈ normalizer (S.E S.y : Set X))
    (hnt : n ∈ centralizer ({t} : Set X)) {e : MB} (he : e ∈ [1, MB.z, MB.y, MB.z * MB.y]) :
    ∃ e' ∈ [1, MB.z, MB.y, MB.z * MB.y], n * B.ι e * n⁻¹ = B.ι e' := by
  have heE0 : B.ι e ∈ S.E0 S.y S.k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    refine B.ι_mem_E0 ?_
    rcases he with rfl | rfl | rfl | rfl <;> decide +kernel
  have h1 : n * B.ι e * n⁻¹ ∈ S.E0 S.y S.k := B.G.V₁.conj_mem_E0 hnE heE0
  have h2 : n * B.ι e * n⁻¹ ∈ L := L2K.conj_mem_L (A := A) hnt (B.ι_mem_L_of he)
  obtain ⟨e', he', hee⟩ := B.mem_E0_iff.mp h1
  exact ⟨e', B.mem_ZY_of he' (hee ▸ h2), hee.symm⟩

omit [Finite X] in
theorem eq_pow_sq_of_pow {g : X} {n : ℕ} (h : g ^ 3 ^ n = 1) :
    g = (g ^ 2) ^ ((3 ^ n + 1) / 2) := by
  obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
  rw [show (3 ^ n + 1) / 2 = m + 1 by omega, ← pow_mul, show 2 * (m + 1) = 3 ^ n + 1 by omega,
    pow_succ, h, one_mul]

theorem exists_delta_ZY : ∃ δ ∈ B.G.D₁.D₁₁, δ * S.z * δ⁻¹ = S.y ∧
    δ * S.y * δ⁻¹ = S.z * S.y := by
  obtain ⟨δ₀, hδ₀, hmove⟩ := B.exists_D₁₁_moves_z
  have hle := B.G.D₁.D₁₁_le hδ₀
  have hE : δ₀ ∈ normalizer (S.E S.y : Set X) := hle.1.1
  have ht : δ₀ ∈ centralizer ({t} : Set X) := hle.2
  obtain ⟨n, hn⟩ := B.G.D₁.isPGroup_D₁₁ ⟨δ₀, hδ₀⟩
  have hn' : δ₀ ^ 3 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hsq : δ₀ ^ 2 * S.z * (δ₀ ^ 2)⁻¹ ≠ S.z := by
    intro h2
    apply hmove
    have hfix : ∀ m : ℕ, (δ₀ ^ 2) ^ m * S.z * ((δ₀ ^ 2) ^ m)⁻¹ = S.z := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, show (δ₀ ^ 2) ^ m * δ₀ ^ 2 * S.z * ((δ₀ ^ 2) ^ m * δ₀ ^ 2)⁻¹ =
          (δ₀ ^ 2) ^ m * (δ₀ ^ 2 * S.z * (δ₀ ^ 2)⁻¹) * ((δ₀ ^ 2) ^ m)⁻¹ by group, h2, ih]
    rw [eq_pow_sq_of_pow hn']
    exact hfix _
  obtain ⟨e₁, he₁, hz⟩ := B.conj_ZY hE ht (e := MB.z) (by simp)
  obtain ⟨e₂, he₂, hy⟩ := B.conj_ZY hE ht (e := MB.y) (by simp)
  rw [B.ι_z] at hz
  rw [B.ι_y] at hy
  have hz' : δ₀ * S.z * δ₀⁻¹ = B.ι e₁ := hz
  have key : ∀ a b : MB, B.ι a = B.ι b → a = b := fun a b h => B.ι_injective h
  have hzy : δ₀ * (S.z * S.y) * δ₀⁻¹ = B.ι (e₁ * e₂) := by
    rw [map_mul, ← hz, ← hy]; group
  have hne1 : ∀ {a : X}, δ₀ * a * δ₀⁻¹ = 1 → a = 1 := fun {a} h => by
    calc a = δ₀⁻¹ * (δ₀ * a * δ₀⁻¹) * δ₀ := by group
      _ = 1 := by rw [h]; group
  have hzne : S.z ≠ 1 := z_ne_one S
  have hyne : S.y ≠ 1 := (isRefl_y S).ne_one
  have hzy_ne : S.z ≠ S.y := fun h => by
    have : MB.z = MB.y := B.ι_injective (by rw [B.ι_z, B.ι_y, h])
    exact absurd this (by decide +kernel)
  have hinj : ∀ {a b : X}, δ₀ * a * δ₀⁻¹ = δ₀ * b * δ₀⁻¹ → a = b := fun {a b} h => by
    calc a = δ₀⁻¹ * (δ₀ * a * δ₀⁻¹) * δ₀ := by group
      _ = δ₀⁻¹ * (δ₀ * b * δ₀⁻¹) * δ₀ := by rw [h]
      _ = b := by group
  have hsq' : ∀ {w : X}, δ₀ * S.z * δ₀⁻¹ = w → δ₀ * w * δ₀⁻¹ = S.z → False := fun {w} h1 h2 =>
    hsq (by rw [pow_two, show δ₀ * δ₀ * S.z * (δ₀ * δ₀)⁻¹ = δ₀ * (δ₀ * S.z * δ₀⁻¹) * δ₀⁻¹ by
      group, h1, h2])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he₁ he₂
  rcases he₁ with rfl | rfl | rfl | rfl
  · exact absurd (hne1 (by rw [hz', map_one])) hzne
  · exact absurd (by rw [hz', B.ι_z]) hmove
  · rcases he₂ with rfl | rfl | rfl | rfl
    · exact absurd (hne1 (by rw [hy, map_one])) hyne
    · exact (hsq' (by rw [hz', B.ι_y]) (by rw [hy, B.ι_z])).elim
    · exact absurd (hinj (by rw [hz', hy])) hzy_ne
    · exact ⟨δ₀, hδ₀, by rw [hz', B.ι_y], by rw [hy, map_mul, B.ι_z, B.ι_y]⟩
  · rcases he₂ with rfl | rfl | rfl | rfl
    · exact absurd (hne1 (by rw [hy, map_one])) hyne
    · refine ⟨δ₀⁻¹, inv_mem hδ₀, ?_, ?_⟩
      · rw [show S.z = δ₀ * S.y * δ₀⁻¹ by rw [hy, B.ι_z]]; group
      · have h1 : δ₀ * (S.z * S.y) * δ₀⁻¹ = S.y := by
          rw [hzy, show MB.z * MB.y * MB.z = MB.y by decide +kernel, B.ι_y]
        calc δ₀⁻¹ * S.y * δ₀⁻¹⁻¹ = δ₀⁻¹ * (δ₀ * (S.z * S.y) * δ₀⁻¹) * δ₀ := by rw [h1]; group
          _ = S.z * S.y := by group
    · have h1 : δ₀ * (S.z * S.y) * δ₀⁻¹ = S.z := by
        rw [hzy, show MB.z * MB.y * MB.y = MB.z by decide +kernel, B.ι_z]
      exact (hsq' (by rw [hz', map_mul, B.ι_z, B.ι_y]) h1).elim
    · exact absurd (hinj (by rw [hz', hy])) hzy_ne

theorem Q0_le : S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ ≤ MB.Q0h.map B.ι := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [B.E0_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, MB.inQ0_of_inE0 x hx, rfl⟩
  · refine zpowers_le.mpr ?_
    obtain ⟨c, hc, hw⟩ := B.G.V₁.w₁_eq
    obtain ⟨x, hx, rfl⟩ := B.mem_E0_iff.mp hc
    change B.G.V₁.D.w₁ ∈ _
    rw [hw, ← B.ι_w₁, ← map_mul]
    exact ⟨_, mul_mem (show MB.w₁ ∈ MB.Q0h from MB.inQ0_w₁)
      (show x ∈ MB.Q0h from MB.inQ0_of_inE0 x hx), rfl⟩
  · refine zpowers_le.mpr ⟨MB.w₂, MB.inQ0_w₂, B.ι_w₂⟩

theorem exists_delta : ∃ δ ∈ B.G.D₁.D₁₁, ∃ f ∈ MB.d3List, B.ActsQ1 δ f := by
  obtain ⟨δ, hδ, hz, hy⟩ := B.exists_delta_ZY
  have hle := B.G.D₁.D₁₁_le hδ
  have hE : δ ∈ normalizer (S.E S.y : Set X) := hle.1.1
  have hQ : δ ∈ normalizer (B.G.D₁.Q₁ : Set X) := hle.1.2
  have ht : δ ∈ centralizer ({t} : Set X) := hle.2
  have hQ0 := B.G.D₁.Q0_invariant δ ⟨hE, hQ⟩
  have hconjQ0 : ∀ q ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂,
      δ * q * δ⁻¹ ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ := fun q hq => by
    rw [← hQ0]; exact ⟨q, hq, rfl⟩
  have hw₁Q : B.ι MB.w₁ ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ := by
    rw [B.ι_w₁]; exact B.G.V₁.w₁N_mem_Q0
  have hw₂Q : B.ι MB.w₂ ∈ S.Q0 S.y S.k B.G.D₁.w₁ B.G.D₁.w₂ := by
    rw [B.ι_w₂]; exact B.G.V₁.w₂_mem_Q0
  obtain ⟨a₁, ha₁, he₁⟩ := B.Q0_le (hconjQ0 _ hw₁Q)
  obtain ⟨a₂, ha₂, he₂⟩ := B.Q0_le (hconjQ0 _ hw₂Q)
  have hsq₁ : a₁ * a₁ = MB.y := B.ι_injective (by
    rw [map_mul, he₁, B.ι_y, ← hz, ← B.G.V₁.w₁N_sq_of_homoc B.h₁, pow_two, ← B.ι_w₁]; group)
  have hw₂sq : B.ι MB.w₂ * B.ι MB.w₂ = S.y := by
    rw [← map_mul, show MB.w₂ * MB.w₂ = MB.y by decide +kernel, B.ι_y]
  have hsq₂ : a₂ * a₂ = MB.z * MB.y := B.ι_injective (by
    rw [map_mul, he₂, map_mul, B.ι_z, B.ι_y, ← hy, ← hw₂sq]; group)
  have hA1 := MB.mem_A1c a₁ ha₁ hsq₁
  have hA2 := MB.mem_A2c a₂ ha₂ hsq₂
  have hvC : B.G.V₁.vN ∈ centralizer (B.G.D₁.D₁₁ : Set X) := B.G.V₁.vN_mem_C.2
  have hkC : S.k ∈ centralizer (B.G.D₁.D₁₁ : Set X) := by
    have : S.k ∈ B.G.D₁.Q₁ ⊓ centralizer (B.G.D₁.D₁₁ : Set X) :=
      B.G.D₁.C_eq ▸ subset_closure (by simp)
    exact this.2
  have hcomm : ∀ {g : X}, g ∈ centralizer (B.G.D₁.D₁₁ : Set X) → δ * g * δ⁻¹ = g := by
    intro g hg
    rw [mem_centralizer_iff.mp hg δ hδ, mul_inv_cancel_right]
  have hact : B.ActsQ1 δ (MB.dCand a₁ a₂) := by
    refine actsQ1_of_map ?_
    simp only [MB.gensQ1, MB.dCand, List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨by rw [he₂], by rw [he₁], by rw [B.ι_v]; exact hcomm hvC, by rw [B.ι_z, hz, B.ι_y],
      by rw [B.ι_y, hy, map_mul, B.ι_z, B.ι_y], ?_, by rw [B.ι_k]; exact hcomm hkC⟩
    rw [B.ι_t, mem_centralizer_singleton_iff.mp ht, mul_inv_cancel_right]
  refine ⟨δ, hδ, MB.dCand a₁ a₂, ?_, hact⟩
  set f := MB.dCand a₁ a₂ with hfdef
  have hfm : ∀ x ∈ f, MB.inQ1 x = true := MB.dCand_mem a₁ hA1 a₂ hA2
  have hflen : f.length = 7 := rfl
  set g3 := MB.compQ1 f (MB.compQ1 f f) with hg3
  have h3 : B.ActsQ1 (δ * (δ * δ)) g3 := hact.mul (hact.mul hact hfm) (MB.compQ1_mem hfm)
  by_cases hid : g3 = MB.gensQ1
  · simp only [MB.d3List, List.mem_filter, List.mem_flatMap, List.mem_map]
    exact ⟨⟨a₁, hA1, a₂, hA2, rfl⟩, by rw [← hg3, hid]; exact beq_self_eq_true _⟩
  · exfalso
    have hsq3 : MB.compQ1 g3 g3 = MB.gensQ1 := MB.dCand_order a₁ hA1 a₂ hA2
    have hg3m : ∀ x ∈ g3, MB.inQ1 x = true := MB.compQ1_mem hfm
    have hg3len : g3.length = 7 := by simp [hg3, MB.compQ1, hflen]
    have hid1 : B.ActsQ1 1 MB.gensQ1 := fun x hx => by
      rw [one_mul, inv_one, mul_one, MB.applyQ1, ← MB.nf_Q1 hx]
    have hpow : ∀ m : ℕ, B.ActsQ1 ((δ * (δ * δ)) ^ (2 * m + 1)) g3 := by
      intro m
      induction m with
      | zero => simpa using h3
      | succ m ih =>
        have h6 : B.ActsQ1 ((δ * (δ * δ)) * (δ * (δ * δ))) MB.gensQ1 := by
          have := h3.mul h3 hg3m
          rwa [hsq3] at this
        have := ih.mul h6 (fun x hx => MB.gensQ1_mem x hx)
        rw [MB.compQ1_gensQ1 g3 hg3len] at this
        rwa [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, pow_add, pow_two]
    obtain ⟨n, hn⟩ := B.G.D₁.isPGroup_D₁₁ ⟨δ, hδ⟩
    have hn' : δ ^ 3 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    rcases n with _ | n
    · rw [pow_zero, pow_one] at hn'
      rw [hn', one_mul, inv_one, mul_one] at hz
      exact (isRefl_y S).ne_z hz.symm
    · obtain ⟨m, hm⟩ : Odd (3 ^ n) := Odd.pow (by decide)
      have he : δ ^ 3 ^ (n + 1) = (δ * (δ * δ)) ^ (2 * m + 1) := by
        rw [← hm, pow_succ, mul_comm, pow_mul, pow_three]
      have h1 := hpow m
      rw [← he, hn'] at h1
      apply hid
      have hmap : MB.gensQ1.map (MB.applyQ1 g3) = MB.gensQ1.map (MB.applyQ1 MB.gensQ1) :=
        List.map_congr_left fun x hx =>
          h1.eq_of_actsAs hid1 (ActsAs.refl _ _) x (MB.gensQ1_mem x hx)
      calc g3 = MB.gensQ1.map (MB.applyQ1 g3) := (MB.applyQ1_gens g3 hg3len).symm
        _ = MB.gensQ1.map (MB.applyQ1 MB.gensQ1) := hmap
        _ = MB.gensQ1 := MB.applyQ1_gens MB.gensQ1 MB.gensQ1_length

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
