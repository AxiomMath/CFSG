module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YSylow
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G]

private lemma le_normalizer_of_conj {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  refine ⟨fun hb => h a ha b hb, fun hb => ?_⟩
  have h' := h a⁻¹ (A.inv_mem ha) (a * b * a⁻¹) hb
  rwa [show a⁻¹ * (a * b * a⁻¹) * (a⁻¹)⁻¹ = b by group] at h'

private theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

theorem mem_sup_of_normalizes {T C : Subgroup G} (hTC : ∀ x ∈ T, ∀ c ∈ C, x * c * x⁻¹ ∈ C) :
    ∀ y ∈ T ⊔ C, ∃ x ∈ T, ∃ c ∈ C, y = x * c := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · rintro z (hz | hz)
    · exact ⟨z, hz, 1, C.one_mem, by simp⟩
    · exact ⟨1, T.one_mem, z, hz, by simp⟩
  · exact ⟨1, T.one_mem, 1, C.one_mem, by simp⟩
  · rintro a b _ _ ⟨x₁, hx₁, c₁, hc₁, rfl⟩ ⟨x₂, hx₂, c₂, hc₂, rfl⟩
    refine ⟨x₁ * x₂, T.mul_mem hx₁ hx₂, (x₂⁻¹ * c₁ * x₂) * c₂,
      C.mul_mem (by simpa using hTC x₂⁻¹ (T.inv_mem hx₂) c₁ hc₁) hc₂, ?_⟩
    group
  · rintro a _ ⟨x, hx, c, hc, rfl⟩
    refine ⟨x⁻¹, T.inv_mem hx, x * c⁻¹ * x⁻¹, hTC x hx c⁻¹ (C.inv_mem hc), ?_⟩
    group

theorem relIndex_sup_of_normalizes {T C : Subgroup G} (hTC : ∀ x ∈ T, ∀ c ∈ C, x * c * x⁻¹ ∈ C) :
    T.relIndex (T ⊔ C) = (T ⊓ C).relIndex C := by
  have hTCn : T ≤ Subgroup.normalizer (C : Set G) := le_normalizer_of_conj hTC
  have h3 : C.relIndex (T ⊔ C) = (T ⊓ C).relIndex T :=
    (relIndex_sup_eq_of_le_normalizer hTCn).trans (Subgroup.inf_relIndex_left T C).symm
  have h1 : (T ⊓ C).relIndex T * T.relIndex (T ⊔ C) = (T ⊓ C).relIndex (T ⊔ C) :=
    Subgroup.relIndex_mul_relIndex (T ⊓ C) T (T ⊔ C) inf_le_left le_sup_left
  have h2 : (T ⊓ C).relIndex C * C.relIndex (T ⊔ C) = (T ⊓ C).relIndex (T ⊔ C) :=
    Subgroup.relIndex_mul_relIndex (T ⊓ C) C (T ⊔ C) inf_le_right le_sup_right
  have h4 : 0 < (T ⊓ C).relIndex T :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := (T ⊓ C).subgroupOf T))
  have h5 : (T ⊓ C).relIndex C = T.relIndex (T ⊔ C) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((T ⊓ C).relIndex T) ((T ⊓ C).relIndex C), h2, ← h1]
  exact h5.symm

theorem sylow_sup_of_normal {X C N T : Subgroup G} (hCX : C ≤ X) (hNX : N ≤ X)
    (hCn : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) (hC2 : IsPGroup 2 ↥C)
    (hXe : ∀ x ∈ X, ∃ c ∈ C, ∃ n ∈ N, x = c * n) (hT : IsSylowIn 2 N T) (hCN : C ⊓ N ≤ T) :
    IsSylowIn 2 X (T ⊔ C) := by
  have hTN : T ≤ N := hT.1
  have hTX : T ≤ X := hTN.trans hNX
  have hTCn : T ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_conj fun x hx c hc => hCn x (hTX hx) c hc
  have hKX : T ⊔ C ≤ X := sup_le hTX hCX
  have hK2 : IsPGroup 2 ↥(T ⊔ C) := hT.2.1.to_sup_of_normal_right' hC2 hTCn
  have hNC : N ⊔ C = X := by
    refine le_antisymm (sup_le hNX hCX) ?_
    intro x hx
    obtain ⟨c, hc, n, hn, rfl⟩ := hXe x hx
    exact sup_comm C N ▸ Subgroup.mul_mem_sup hc hn
  have hTCeq : T ⊓ C = N ⊓ C :=
    le_antisymm (le_inf (inf_le_left.trans hTN) inf_le_right)
      (le_inf ((inf_comm N C).le.trans hCN) inf_le_right)
  have hrel : N.relIndex X = T.relIndex (T ⊔ C) := by
    rw [← hNC,
      relIndex_sup_of_normalizes (T := N) (C := C) (fun x hx c hc => hCn x (hNX hx) c hc),
      ← hTCeq,
      ← relIndex_sup_of_normalizes (T := T) (C := C) (fun x hx c hc => hCn x (hTX hx) c hc)]
  have h1 : T.relIndex (T ⊔ C) * (T ⊔ C).relIndex X = T.relIndex X :=
    Subgroup.relIndex_mul_relIndex T (T ⊔ C) X le_sup_left hKX
  have h2 : T.relIndex N * N.relIndex X = T.relIndex X :=
    Subgroup.relIndex_mul_relIndex T N X hTN hNX
  have hpos : 0 < N.relIndex X :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := N.subgroupOf X))
  have hidx : (T ⊔ C).relIndex X = T.relIndex N := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    rw [hrel, h1, mul_comm, ← hrel, h2]
  exact ⟨hKX, hK2, by rw [hidx]; exact hT.2.2⟩

theorem le_sup_of_sylow {X C T T₁ : Subgroup G} (hCX : C ≤ X)
    (hCn : ∀ x ∈ X, ∀ c ∈ C, x * c * x⁻¹ ∈ C) (hC2 : IsPGroup 2 ↥C)
    (hS : IsSylowIn 2 X (T ⊔ C)) (hT₁X : T₁ ≤ X) (hT₁ : IsPGroup 2 ↥T₁) (hTT₁ : T ≤ T₁) :
    T₁ ≤ T ⊔ C := by
  have hT₁Cn : T₁ ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_conj fun x hx c hc => hCn x (hT₁X hx) c hc
  have hT₁C2 : IsPGroup 2 ↥(T₁ ⊔ C) := hT₁.to_sup_of_normal_right' hC2 hT₁Cn
  have hT₁CX : T₁ ⊔ C ≤ X := sup_le hT₁X hCX
  have heq : T ⊔ C = T₁ ⊔ C :=
    sylowIn_eq_of_le (p := 2) hS hT₁C2 hT₁CX (sup_le (hTT₁.trans le_sup_left) le_sup_right)
  rw [heq]
  exact le_sup_left

theorem relIndex_cent_two {V U : Subgroup G} {z w : G} (hz : z ∈ V) (hw : w ∈ V) (hz1 : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hwz : w ≠ z)
    (hV : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = w ∨ v = z * w)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v * u⁻¹ ∈ V) (hUz : ∀ u ∈ U, u * z * u⁻¹ = z)
    {τ : G} (hτ : τ ∈ U) (hτw : τ * w * τ⁻¹ ≠ w) :
    (centIn U V).relIndex U = 2 := by
  have hw1 : w ≠ 1 := fun h => hτw (by rw [h]; simp)
  have hzw_ne_w : z * w ≠ w := by
    intro h
    have := congrArg (· * w⁻¹) h
    simp at this
    exact hz1 this
  have hUz_inv : ∀ u ∈ U, u⁻¹ * z * u = z := by
    intro u hu
    simpa using hUz u⁻¹ (U.inv_mem hu)
  have hconj : ∀ u ∈ U, u * w * u⁻¹ = w ∨ u * w * u⁻¹ = z * w := by
    intro u hu
    rcases hV (u * w * u⁻¹) (hUV u hu w hw) with h1 | hz' | hw' | hzw
    · exfalso
      have hw_eq : w = 1 := by
        have hw'' : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [h1] at hw''
        simpa using hw''
      exact hw1 hw_eq
    · exfalso
      have hw_eq : w = z := by
        have hw'' : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [hz'] at hw''
        rwa [hUz_inv u hu] at hw''
      exact hwz hw_eq
    · exact Or.inl hw'
    · exact Or.inr hzw
  have hτw' : τ * w * τ⁻¹ = z * w := by
    rcases hconj τ hτ with h | h
    · exact absurd h hτw
    · exact h
  have hcen : ∀ u ∈ U, u ∈ centIn U V ↔ u * w * u⁻¹ = w := by
    intro u hu
    refine ⟨fun hu' => ?_, fun hw' => ?_⟩
    · have hcomm := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu').2) w hw
      calc u * w * u⁻¹ = w * u * u⁻¹ := by rw [← hcomm]
        _ = w := by group
    · refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hfix : u * v * u⁻¹ = v := by
        rcases hV v hv with rfl | rfl | rfl | rfl
        · group
        · exact hUz u hu
        · exact hw'
        · calc u * (z * w) * u⁻¹ = (u * z * u⁻¹) * (u * w * u⁻¹) := by group
            _ = z * w := by rw [hUz u hu, hw']
      have hfix' := congrArg (· * u) hfix
      simpa [mul_assoc] using hfix'.symm
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨τ, hτ, fun b hb => ?_⟩
  rw [hcen b hb, hcen (b * τ) (U.mul_mem hb hτ)]
  rcases hconj b hb with hbw | hbw
  · right
    refine ⟨hbw, fun hcontra => ?_⟩
    have hzw : (b * τ) * w * (b * τ)⁻¹ = z * w := by
      calc (b * τ) * w * (b * τ)⁻¹ = b * (τ * w * τ⁻¹) * b⁻¹ := by group
        _ = b * (z * w) * b⁻¹ := by rw [hτw']
        _ = (b * z * b⁻¹) * (b * w * b⁻¹) := by group
        _ = z * (b * w * b⁻¹) := by rw [hUz b hb]
        _ = z * w := by rw [hbw]
    rw [hzw] at hcontra
    exact hzw_ne_w hcontra
  · left
    refine ⟨?_, fun hbcent => ?_⟩
    · calc (b * τ) * w * (b * τ)⁻¹ = b * (τ * w * τ⁻¹) * b⁻¹ := by group
        _ = b * (z * w) * b⁻¹ := by rw [hτw']
        _ = (b * z * b⁻¹) * (b * w * b⁻¹) := by group
        _ = z * (b * w * b⁻¹) := by rw [hUz b hb]
        _ = z * (z * w) := by rw [hbw]
        _ = w := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
    · rw [hbcent] at hbw
      exact hzw_ne_w hbw.symm

theorem sq_mem_cent {V : Subgroup G} {z w : G} (hz : z ∈ V) (hw : w ∈ V) (hz2 : z ^ 2 = 1)
    (hV : ∀ v ∈ V, v = 1 ∨ v = z ∨ v = w ∨ v = z * w) {u : G}
    (hu : ∀ v ∈ V, u * v * u⁻¹ ∈ V) (huz : u * z * u⁻¹ = z) :
    u ^ 2 ∈ centralizer (V : Set G) := by
  have huz_inv : u⁻¹ * z * u = z := by
    have := congrArg (fun x => u⁻¹ * x * u) huz
    simpa [mul_assoc] using this.symm
  have hsq : ∀ x : G, u ^ 2 * x * (u ^ 2)⁻¹ = u * (u * x * u⁻¹) * u⁻¹ := by
    intro x
    rw [pow_two, mul_inv_rev]
    group
  have huz2 : u ^ 2 * z * (u ^ 2)⁻¹ = z := by
    rw [hsq, huz]
    exact huz
  have huw2 : u ^ 2 * w * (u ^ 2)⁻¹ = w := by
    rw [hsq]
    rcases hV (u * w * u⁻¹) (hu w hw) with h1 | hz' | hw' | hzw
    · have hw1 : w = 1 := by
        have hw'' : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [h1] at hw''
        simpa using hw''
      rw [h1, hw1]
      group
    · have hwz' : w = z := by
        have hw'' : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [hz'] at hw''
        rwa [huz_inv] at hw''
      rw [hz', hwz']
      exact huz
    · rw [hw', hw']
    · rw [hzw]
      calc u * (z * w) * u⁻¹ = (u * z * u⁻¹) * (u * w * u⁻¹) := by group
        _ = z * (z * w) := by rw [huz, hzw]
        _ = w := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcomm_z : z * u ^ 2 = u ^ 2 * z := by
    have := congrArg (· * u ^ 2) huz2
    simpa [mul_assoc] using this.symm
  have hcomm_w : w * u ^ 2 = u ^ 2 * w := by
    have := congrArg (· * u ^ 2) huw2
    simpa [mul_assoc] using this.symm
  rcases hV v hv with rfl | rfl | rfl | rfl
  · simp
  · exact hcomm_z
  · exact hcomm_w
  · calc (z * w) * u ^ 2 = z * (w * u ^ 2) := by group
      _ = z * (u ^ 2 * w) := by rw [hcomm_w]
      _ = (z * u ^ 2) * w := by group
      _ = (u ^ 2 * z) * w := by rw [hcomm_z]
      _ = u ^ 2 * (z * w) := by group

end CFSG.OddStandard.HigherRank.YamadaG23
