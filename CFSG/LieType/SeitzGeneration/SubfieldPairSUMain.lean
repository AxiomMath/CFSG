module

public import CFSG.LieType.SeitzGeneration.SubfieldPairSUGram
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUCenter
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan

public section

namespace CFSG.LieType.SeitzGeneration.SUPair

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.LieType.SeitzGeneration.Centers

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem eq_top_of_center (hK : Nat.card K = (ℓ ^ f) ^ 2) (hq : ℓ ^ f ≠ 2) {m : ℕ} (hm : 2 ≤ m)
    {k : Subfield K} (hk : ∀ x ∈ k, unitaryInvolution K ℓ f x ∈ k) (σk : k ≃+* k)
    (hσk : ∀ x : k, ((σk x : k) : K) = unitaryInvolution K ℓ f (x : K))
    (hUk : IsUnitaryInvolution σk)
    (h3' : ∃ l₁ l₂ l₃ : k, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ σk l₁ * l₁ = -1 ∧ σk l₂ * l₂ = -1 ∧
      σk l₃ * l₃ = -1)
    {H : Subgroup (Su K ℓ f (m + 1))} (hH : ratSU (unitaryInvolution K ℓ f) k hk (m + 1) ≤ H)
    {e : Fin (m + 1) → K} (he : IsRat k e) (he0 : e ≠ 0)
    (hie : herm (unitaryInvolution K ℓ f) e e = 0) (hc : IsCenter H e) : H = ⊤ := by
  have hσ : ∀ c, unitaryInvolution K ℓ f (unitaryInvolution K ℓ f c) = c :=
    unitaryInvolution_involutive hK
  have hrat : ∀ a : Fin (m + 1) → K, IsRat k a → herm (unitaryInvolution K ℓ f) a a = 0 →
      IsCenter H a := fun a ha hia =>
    isCenter_of_isRat σk hσk hk hUk (by omega) hH he he0 hie hc ha hia
  obtain ⟨l₁, l₂, l₃, d₁₂, -, -, n₁, n₂, -⟩ := h3'
  have key : ∀ l : k, σk l * l = -1 → unitaryInvolution K ℓ f (l : K) * (l : K) = -1 := by
    intro l hl
    have := congrArg (fun z : k => (z : K)) hl
    simpa [hσk] using this
  refine eq_top_of_plane_centers hK hq H fun i a ha => ?_
  exact isCenter_embVec_of_rat hσ i hrat l₁.2 l₂.2 (fun h => d₁₂ (Subtype.ext h)) (key _ n₁)
    (key _ n₂) a ha

theorem ratSU_sup_conj_eq_top (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hq : ℓ ^ f ≠ 2) {k : Subfield K} (hk : ∀ x ∈ k, unitaryInvolution K ℓ f x ∈ k)
    (σk : k ≃+* k) (hσk : ∀ x : k, ((σk x : k) : K) = unitaryInvolution K ℓ f (x : K))
    (hUk : IsUnitaryInvolution σk) (K₀ : Subfield K)
    (hK₀ : ∀ x, x ∈ K₀ ↔ unitaryInvolution K ℓ f x = x) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hKk : Nat.card K = Nat.card k ^ p) (hKc : Nat.card K₀ = Nat.card (k.comap K₀.subtype) ^ p)
    (hk3 : 3 ≤ Nat.card (k.comap K₀.subtype)) {m : ℕ} (hm : 2 ≤ m)
    (h3 : m + 1 = 3 → ∃ s : k, s ≠ 0 ∧ σk s * s ≠ 1)
    (h3' : ∃ l₁ l₂ l₃ : k, l₁ ≠ l₂ ∧ l₁ ≠ l₃ ∧ l₂ ≠ l₃ ∧ σk l₁ * l₁ = -1 ∧ σk l₂ * l₂ = -1 ∧
      σk l₃ * l₃ = -1)
    (A : GL (Fin (m + 1)) K)
    (hA : conjTr (unitaryInvolution K ℓ f) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) *
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1)
    (hne : (ratSU (unitaryInvolution K ℓ f) k hk (m + 1)).map
      (suConj (unitaryInvolution_involutive hK) A hA) ≠
        ratSU (unitaryInvolution K ℓ f) k hk (m + 1)) :
    ratSU (unitaryInvolution K ℓ f) k hk (m + 1) ⊔
      (ratSU (unitaryInvolution K ℓ f) k hk (m + 1)).map
        (suConj (unitaryInvolution_involutive hK) A hA) = ⊤ := by
  have hσ := unitaryInvolution_involutive hK
  obtain ⟨a, e, ha, hia, he, hie, hN⟩ :=
    exists_pair_su hσ hk σk hσk hUk hp hp2 hKk (by omega) h3 h3' A hA hne
  obtain ⟨τ, hτ0, hτ⟩ := hUk.exists_traceZero
  have hεσ : unitaryInvolution K ℓ f (τ : K) = -(τ : K) := by
    have := congrArg (fun z : k => (z : K)) hτ
    simp only [Subfield.coe_add, hσk, ZeroMemClass.coe_zero] at this
    linear_combination this
  have hε0 : (τ : K) ≠ 0 := fun h => hτ0 (Subtype.ext h)
  have hcenter := isCenter_of_pair hσ hk K₀ hK₀ hp hp2 hKc hk3 τ.2 hε0 hεσ A hA
    (H := ratSU (unitaryInvolution K ℓ f) k hk (m + 1) ⊔
      (ratSU (unitaryInvolution K ℓ f) k hk (m + 1)).map (suConj hσ A hA))
    le_sup_left le_sup_right ha hia he hie hN
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hN
    rw [herm_zero_left, map_zero, zero_mul]
    exact k.zero_mem
  exact eq_top_of_center hK hq hm hk σk hσk hUk h3' le_sup_left he he0 hie hcenter

end CFSG.LieType.SeitzGeneration.SUPair
