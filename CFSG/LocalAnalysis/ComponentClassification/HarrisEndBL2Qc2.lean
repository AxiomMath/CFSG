module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBL2D1
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Beta

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

local notation "β₀" => w ^ (orderOf w / 2) * t ^ i * z ^ j
local notation "T₀" => (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X)
local notation "X₈" => (closure {t, w ^ (orderOf w / 2), z} : Subgroup X)

namespace Setting46e

theorem conj_t_of_qc (hs : Setting46e t L p f S w z V i j) (hSV : S.relIndex V = 2)
    (hST : S ≠ T₀) {v : X} (hv : v ∈ V) : v * t * v⁻¹ = t ∨ v * t * v⁻¹ = t * z :=
  hs.setup.conj_t_eq hs.sylow_V.le hST
    (fun _ hv' _ hs' => EndB.conj_mem_of_relIndex_two hs.le_V hSV hv' hs') hv

theorem fus_of_qc (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    (hSV : S.relIndex V = 2) (hST : S ≠ T₀) (g : X) (hg : g * t * g⁻¹ ∈ X₈) :
    g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z := by
  obtain ⟨v, hv, hvt⟩ := hs.setup.exists_conj_V_of_mem_X hKF hs.sylow_V hg
  rw [← hvt]
  exact hs.conj_t_of_qc hSV hST hv

theorem twoPart_le_of_fus (hKF : AutPSL2FusionInput) (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j)
    (hfus : ∀ g : X, g * t * g⁻¹ ∈ X₈ → g * t * g⁻¹ = t ∨ g * t * g⁻¹ = t * z) {b : X}
    (hbX : b ∈ X₈) (hbD : b ∉ zpowers t ⊔ (S ⊓ L))
    (hlt : Nat.card T₀ < twoPart (centralizer ({t * b} : Set X)))
    (hle : twoPart (⊤ : Subgroup X) ≤ 4 * twoPart (centralizer ({t * b} : Set X))) :
    twoPart (centralizer ({t * b} : Set X)) ≤ twoPart (centralizer ({β₀} : Set X)) :=
  hs.max_beta _ (hs.setup.isBeta411_t_mul hKF hKC hs.sylow_V hs.le_V hbX hbD hfus hlt hle)

theorem comm_tbz (hs : Setting46e t L p f S w z V i j) :
    t * β₀ = β₀ * t ∧ t * z = z * t ∧ β₀ * z = z * β₀ := by
  have htX : t ∈ X₈ := subset_closure (by simp)
  have hzX : z ∈ X₈ := subset_closure (by simp)
  have hab : ∀ a ∈ X₈, ∀ b ∈ X₈, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hs.setup.X_le_center_T ha).2 b (hs.setup.X_le_T hb)).symm
  exact ⟨hab _ htX _ (beta_mem_X i j), hab _ htX _ hzX, hab _ (beta_mem_X i j) _ hzX⟩

theorem mem_X_cases (hs : Setting46e t L p f S w z V i j) {x : X} (hx : x ∈ X₈) :
    x = 1 ∨ x = β₀ ∨ x = z ∨ x = β₀ * z ∨ x = t ∨ x = t * β₀ ∨ x = t * z ∨
      x = t * (β₀ * z) := by
  have hβ2 : (β₀) ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hβzc : β₀ * z = z * β₀ := hs.comm_tbz.2.2
  rcases hs.setup.mem_closure_beta_z_or (beta_mem_X i j) hs.beta.not_mem hx with h | h
  · rcases mem_closure_pair hβ2 hz2 hβzc h with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · have e : x = t * (t⁻¹ * x) := by group
    rcases mem_closure_pair hβ2 hz2 hβzc h with h1 | h1 | h1 | h1 <;> rw [h1] at e
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [e, mul_one])))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))))

end Setting46e

theorem EndB.card_le_of_forall_mem_finset {G : Type*} [Group G] {F : Subgroup G}
    {s : Finset G} (h : ∀ x ∈ F, x ∈ s) : Nat.card F ≤ s.card := by
  have h1 : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (fun x hx => h x hx) (Finset.finite_toSet s)

namespace Setting46e

theorem tbeta_mem (hs : Setting46e t L p f S w z V i j) {F : Subgroup X} (hFX : F ≤ X₈)
    (hF4 : 4 ≤ Nat.card F) (ht : t ∉ F) (htz : t * z ∉ F) (hβ : β₀ ∉ F)
    (hβz : β₀ * z ∉ F) : t * β₀ ∈ F ∧ z ∈ F := by
  classical
  have hmem : ∀ x ∈ F, x = 1 ∨ x = z ∨ x = t * β₀ ∨ x = t * (β₀ * z) := by
    intro x hx
    rcases hs.mem_X_cases (hFX hx) with h | h | h | h | h | h | h | h <;> rw [h] at hx
    · exact Or.inl h
    · exact absurd hx hβ
    · exact Or.inr (Or.inl h)
    · exact absurd hx hβz
    · exact absurd hx ht
    · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd hx htz
    · exact Or.inr (Or.inr (Or.inr h))
  constructor
  · by_contra h
    have h1 := EndB.card_le_of_forall_mem_finset (s := ({1, z, t * (β₀ * z)} : Finset X))
      fun x hx => by
        rcases hmem x hx with h2 | h2 | h2 | h2
        · rw [h2]; simp
        · rw [h2]; simp
        · exact absurd (h2 ▸ hx) h
        · rw [h2]; simp
    have h2 : ({1, z, t * (β₀ * z)} : Finset X).card ≤ 3 := Finset.card_le_three
    omega
  · by_contra h
    have h1 := EndB.card_le_of_forall_mem_finset (s := ({1, t * β₀, t * (β₀ * z)} : Finset X))
      fun x hx => by
        rcases hmem x hx with h2 | h2 | h2 | h2
        · rw [h2]; simp
        · exact absurd (h2 ▸ hx) h
        · rw [h2]; simp
        · rw [h2]; simp
    have h2 : ({1, t * β₀, t * (β₀ * z)} : Finset X).card ≤ 3 := Finset.card_le_three
    omega

end Setting46e

end CFSG.ComponentClassification.HarrisLit
