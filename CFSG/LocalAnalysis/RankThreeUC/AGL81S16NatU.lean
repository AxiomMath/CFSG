module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Data

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem U4NatData.card_V {n : ℕ} {L V : Subgroup G} (d : U4NatData G n L V) :
    Nat.card ↥V = 2 ^ (8 * n) := by
  have h1 : Nat.card ↥V = Nat.card (Multiplicative (Fin 4 → d.F)) :=
    Nat.card_congr (Equiv.ofBijective d.φ d.φ_bij)
  have h2 : Nat.card (Multiplicative (Fin 4 → d.F)) = Nat.card d.F ^ 4 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → d.F) ≃ (Fin 4 → d.F))]
    simp [Nat.card_pi]
  rw [h1, h2, d.card_F, ← pow_mul, ← pow_mul]
  congr 1
  ring

theorem exists_mul_of_mem_sup_centralizer {M L V : Subgroup G} (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) {b : G} (hb : b ∈ L ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ l ∈ L, ∀ v ∈ V, b * v * b⁻¹ = l * v * l⁻¹ := by
  have hLN : L ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro l hl
    rw [mem_normalizer_iff]
    intro y
    have hlM : l ∈ M := hLM hl
    have hlV := hMV hlM
    constructor
    · rintro ⟨hyM, hyC⟩
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      · exact M.mul_mem (M.mul_mem hlM hyM) (M.inv_mem hlM)
      · have hv' : l⁻¹ * v * l ∈ V := by
          have := (mem_normalizer_iff.mp (inv_mem hlV) v).mp hv
          simpa using this
        have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hv'
        calc v * (l * y * l⁻¹) = l * ((l⁻¹ * v * l) * y) * l⁻¹ := by group
          _ = l * (y * (l⁻¹ * v * l)) * l⁻¹ := by rw [h1]
          _ = l * y * l⁻¹ * v := by group
    · rintro ⟨hyM, hyC⟩
      refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      · have := M.mul_mem (M.mul_mem (M.inv_mem hlM) hyM) hlM
        simpa [mul_assoc] using this
      · have hv' : l * v * l⁻¹ ∈ V := (mem_normalizer_iff.mp hlV v).mp hv
        have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hv'
        have h2 : v * y = y * v := by
          calc v * y = l⁻¹ * ((l * v * l⁻¹) * (l * y * l⁻¹)) * l := by group
            _ = l⁻¹ * ((l * y * l⁻¹) * (l * v * l⁻¹)) * l := by rw [h1]
            _ = y * v := by group
        exact h2
  have hmem : b ∈ ((L : Set G) * ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _ hLN]
    exact hb
  obtain ⟨l, hl, c, hc, rfl⟩ := hmem
  refine ⟨l, hl, fun v hv => ?_⟩
  have hcv : c * v * c⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp hc.2 v hv
    rw [← this]; group
  calc l * c * v * (l * c)⁻¹ = l * (c * v * c⁻¹) * l⁻¹ := by group
    _ = l * v * l⁻¹ := by rw [hcv]

theorem U4NatData.conj_smul {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) {b : G}
    (hb : b ∈ L ⊔ (M ⊓ centralizer (V : Set G))) (v₁ v₂ w₁ w₂ : ↥V) (c : d.F)
    (h : Multiplicative.toAdd (d.φ v₂) = c • Multiplicative.toAdd (d.φ v₁))
    (hw₁ : (w₁ : G) = b * (v₁ : G) * b⁻¹) (hw₂ : (w₂ : G) = b * (v₂ : G) * b⁻¹) :
    Multiplicative.toAdd (d.φ w₂) = c • Multiplicative.toAdd (d.φ w₁) := by
  obtain ⟨l, hl, hlb⟩ := exists_mul_of_mem_sup_centralizer hLM hMV hb
  have e1 := d.equiv ⟨l, hl⟩ v₁ w₁ (by rw [hw₁]; exact (hlb v₁ v₁.2).symm)
  have e2 := d.equiv ⟨l, hl⟩ v₂ w₂ (by rw [hw₂]; exact (hlb v₂ v₂.2).symm)
  rw [e1, e2, toAdd_ofAdd, toAdd_ofAdd, h, Matrix.mulVec_smul]

theorem U4NatData.dim_F {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) {B : Subgroup G} (hBM : B ≤ M)
    (hB : B ≤ L ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ j : ℕ, Nat.card ↥(V ⊓ centralizer (B : Set G)) = 2 ^ (2 * n * j) := by
  have hconj : ∀ b ∈ B, ∀ v : ↥V, ∃ w : ↥V, (w : G) = b * (v : G) * b⁻¹ := fun b hb v =>
    ⟨⟨b * (v : G) * b⁻¹, (mem_normalizer_iff.mp (hMV (hBM hb)) v).mp v.2⟩, rfl⟩
  let S : Submodule d.F (Fin 4 → d.F) :=
    { carrier := {w | ∃ v : ↥V, Multiplicative.toAdd (d.φ v) = w ∧
        ∀ b ∈ B, b * (v : G) * b⁻¹ = (v : G)}
      add_mem' := by
        rintro _ _ ⟨v₁, rfl, h₁⟩ ⟨v₂, rfl, h₂⟩
        refine ⟨v₁ * v₂, by simp, fun b hb => ?_⟩
        have := h₁ b hb
        have := h₂ b hb
        simp only [Subgroup.coe_mul]
        calc b * ((v₁ : G) * (v₂ : G)) * b⁻¹
            = (b * (v₁ : G) * b⁻¹) * (b * (v₂ : G) * b⁻¹) := by group
          _ = (v₁ : G) * (v₂ : G) := by rw [h₁ b hb, h₂ b hb]
      zero_mem' := ⟨1, by simp, fun b hb => by simp⟩
      smul_mem' := by
        rintro c _ ⟨v, rfl, hv⟩
        obtain ⟨v', hv'⟩ := d.φ_bij.2 (Multiplicative.ofAdd (c • Multiplicative.toAdd (d.φ v)))
        refine ⟨v', by rw [hv']; simp, fun b hb => ?_⟩
        obtain ⟨w', hw'⟩ := hconj b hb v'
        obtain ⟨w, hw⟩ := hconj b hb v
        have hwv : (w : G) = (v : G) := by rw [hw]; exact hv b hb
        have hwv' : w = v := Subtype.ext hwv
        have key := d.conj_smul hLM hMV (hB hb) v v' w w' c
          (by rw [hv']; simp) hw hw'
        have : d.φ w' = d.φ v' := by
          apply Multiplicative.toAdd.injective
          rw [key, hwv', hv']
          simp
        have hww : w' = v' := d.φ_bij.1 this
        rw [← hw', hww] }
  have hcard : Nat.card ↥(V ⊓ centralizer (B : Set G)) = Nat.card S := by
    let f : ↥(V ⊓ centralizer (B : Set G)) → S := fun v =>
      ⟨Multiplicative.toAdd (d.φ ⟨v, v.2.1⟩), ⟨v, v.2.1⟩, rfl, fun b hb => by
        have h1 : b * (v : G) = (v : G) * b := Subgroup.mem_centralizer_iff.mp v.2.2 b hb
        calc b * (v : G) * b⁻¹ = (v : G) * b * b⁻¹ := by rw [h1]
          _ = (v : G) := by group⟩
    refine Nat.card_congr (Equiv.ofBijective f ⟨fun v v' h => ?_, fun w => ?_⟩)
    · have h1 : Multiplicative.toAdd (d.φ ⟨v, v.2.1⟩) = Multiplicative.toAdd (d.φ ⟨v', v'.2.1⟩) :=
        congrArg Subtype.val h
      have h2 : d.φ ⟨v, v.2.1⟩ = d.φ ⟨v', v'.2.1⟩ := Multiplicative.toAdd.injective h1
      have h3 := d.φ_bij.1 h2
      exact Subtype.ext (congrArg (fun x : ↥V => (x : G)) h3)
    · obtain ⟨w, v, hv, hfix⟩ := w
      refine ⟨⟨(v : G), v.2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩, Subtype.ext hv⟩
      have := hfix b hb
      calc b * (v : G) = (b * (v : G) * b⁻¹) * b := by group
        _ = (v : G) * b := by rw [this]
  refine ⟨Module.finrank d.F S, ?_⟩
  rw [hcard, Module.natCard_eq_pow_finrank (K := d.F) (V := S), d.card_F, ← pow_mul, ← pow_mul]
  congr 1
  ring

end CFSG.LocalAnalysis.RankThreeUC
