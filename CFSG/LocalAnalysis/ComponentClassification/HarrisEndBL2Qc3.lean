module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2Qc2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

theorem Setting46e.le_normalizer_T (hs : Setting46e t L p f S w z V i j) {P : Subgroup X}
    (hTP : T₀ ≤ P) (hP : IsPGroup 2 P) (hPX : ∀ g ∈ P, ∀ x ∈ X₈, g * x * g⁻¹ ∈ X₈) :
    P ≤ normalizer ((T₀ : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTC : T₀ ≤ centralizer ((X₈ : Subgroup X) : Set X) := fun g hg =>
    mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hs.setup.X_le_center_T hx).2 g hg).symm
  have hCP : P ⊓ centralizer ((X₈ : Subgroup X) : Set X) = T₀ :=
    hs.lemma44a_X.2.eq_of_le (le_inf hTP hTC) inf_le_right (hP.to_le inf_le_left)
  have key : ∀ g ∈ P, ∀ x ∈ T₀, g * x * g⁻¹ ∈ T₀ := by
    intro g hg x hx
    rw [← hCP] at hx ⊢
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hg hx.1) (inv_mem hg),
      mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' := hPX g⁻¹ (inv_mem hg) y hy
    rw [inv_inv] at hy'
    have h1 := (mem_centralizer_iff.mp hx.2) _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * y := by group
  intro g hg
  refine EndB.mem_normalizer_of_conj (key g hg) fun x hx => ?_
  have := key g⁻¹ (inv_mem hg) x hx
  rwa [inv_inv] at this

namespace EndB.L2Ctx

variable {hs : Setting46e t L p f S w z V i j} {W : Subgroup X}

theorem qc_S_ne (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) :
    S ≠ T₀ := fun h => by
  have h1 := (hc.qc_structure hKF hSV).2.2.2
  have h2 : Nat.card S = Nat.card T₀ := congrArg (fun H : Subgroup X => Nat.card ↥H) h
  have hpos : 0 < Nat.card T₀ := Nat.card_pos
  omega

theorem qc_relIndex (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) :
    W ≤ V ∧ W.relIndex V = 2 := by
  obtain ⟨-, hUW, hWS, -⟩ := hc.qc_structure hKF hSV
  have hWV : W ≤ V := hUW ▸ inf_le_left
  refine ⟨hWV, ?_⟩
  have h1 := Subgroup.relIndex_mul_card W V
  have h2 := Subgroup.relIndex_mul_card S V
  rw [inf_of_le_left hWV] at h1
  rw [inf_of_le_left hs.le_V, hSV] at h2
  have hpos : 0 < Nat.card W := Nat.card_pos
  rw [hWS] at h1
  have : W.relIndex V * Nat.card S = 2 * Nat.card S := by rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right (hWS ▸ hpos) this

theorem qc_conj_beta (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) {v : X} (hv : v ∈ V) :
    v * β₀ * v⁻¹ = β₀ ∨ v * β₀ * v⁻¹ = β₀ * z := by
  obtain ⟨hWV, hidx⟩ := hc.qc_relIndex hKF hSV
  have hβZ : β₀ ∈ W ⊓ centralizer (W : Set X) := by
    rw [hc.center_eq hKC]
    exact subset_closure (Set.mem_insert _ _)
  have hmem : v * β₀ * v⁻¹ ∈ W ⊓ centralizer (W : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨EndB.conj_mem_of_relIndex_two hWV hidx hv hβZ.1,
      mem_centralizer_iff.mpr ?_⟩
    intro g hg
    have hg' : v⁻¹ * g * v ∈ W := by
      have := EndB.conj_mem_of_relIndex_two hWV hidx (inv_mem hv) hg
      rwa [inv_inv] at this
    have h1 := (mem_centralizer_iff.mp hβZ.2) _ hg'
    calc g * (v * β₀ * v⁻¹) = v * ((v⁻¹ * g * v) * β₀) * v⁻¹ := by group
      _ = v * (β₀ * (v⁻¹ * g * v)) * v⁻¹ := by rw [h1]
      _ = v * β₀ * v⁻¹ * g := by group
  rw [hc.center_eq hKC] at hmem
  have hβ2 : (β₀) ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hvz : v * z * v⁻¹ = z := hs.setup.conj_z_of_mem_normalizer_T (hs.sylow_V.le hv)
  rcases mem_closure_pair hβ2 hz2 hs.comm_tbz.2.2 hmem with h | h | h | h
  · exfalso
    apply hs.beta.ne_one
    have := congrArg (fun y => v⁻¹ * y * v) h
    simpa [mul_assoc] using this
  · exact Or.inl h
  · exfalso
    apply hs.setup.beta_ne_z hs.beta
    have h' : v * β₀ * v⁻¹ = v * z * v⁻¹ := by rw [h, hvz]
    simpa [mul_assoc] using congrArg (fun y => v⁻¹ * y * v) h'
  · exact Or.inr h

theorem qc_exists_v (hKF : AutPSL2FusionInput) (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) :
    ∃ v ∈ V, v * t * v⁻¹ = t * z := by
  have hlt : S < V := by
    refine lt_of_le_of_ne hs.le_V fun h => ?_
    rw [h, Subgroup.relIndex_self] at hSV
    omega
  obtain ⟨v, hv, hvS⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨v, hv, ?_⟩
  rcases hs.conj_t_of_qc hSV (hc.qc_S_ne hKF hSV) hv with h | h
  · exfalso
    apply hvS
    have hSC : V ⊓ centralizer ({t} : Set X) = S :=
      hs.sylow.eq_of_le (le_inf hs.le_V hs.sylow.le) inf_le_right
        (hs.sylow_V.isPGroup.to_le inf_le_left)
    rw [← hSC]
    refine Subgroup.mem_inf.mpr ⟨hv, mem_centralizer_singleton_iff.mpr ?_⟩
    calc v * t = v * t * v⁻¹ * v := by group
      _ = t * v := by rw [h]
  · exact h

theorem qc_exists_s (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hc : L2Ctx hs W) (hSV : S.relIndex V = 2) :
    ∃ s ∈ S, s * β₀ * s⁻¹ = β₀ * z := by
  obtain ⟨-, hUW, hWS, -⟩ := hc.qc_structure hKF hSV
  have hnle : ¬ S ≤ V ⊓ centralizer ({β₀} : Set X) := fun hle => by
    obtain ⟨v, hvU, hvS, -⟩ := hs.beta.exists_mem
    have heq : S = V ⊓ centralizer ({β₀} : Set X) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hUW, hWS])
    exact hvS (heq ▸ hvU)
  obtain ⟨s, hs', hsU⟩ := Set.not_subset.mp hnle
  refine ⟨s, hs', ?_⟩
  rcases hc.qc_conj_beta hKF hKC hSV (hs.le_V hs') with h | h
  · exfalso
    apply hsU
    refine Subgroup.mem_inf.mpr ⟨hs.le_V hs', mem_centralizer_singleton_iff.mpr ?_⟩
    calc s * β₀ = s * β₀ * s⁻¹ * s := by group
      _ = β₀ * s := by rw [h]
  · exact h

end EndB.L2Ctx

end CFSG.ComponentClassification.HarrisLit
