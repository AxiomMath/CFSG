module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen

open scoped commutatorElement

theorem commutatorElement_mul_central {G : Type*} [Group G] {a b z w : G}
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have h1 : ∀ g : G, ⁅z, g⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hz g).symm
  have h2 : ∀ g : G, ⁅g, w⁆ = 1 := fun g =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_center_iff.1 hw g)
  simp [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj, h1, h2]

theorem eq_one_of_central_deviation {K : Type*} [Group K] (hK : commutator K = ⊤) (α : MulAut K)
    (h : ∀ x, x⁻¹ * α x ∈ Subgroup.center K) : α = 1 := by
  have h1 : ∀ x y : K, α ⁅x, y⁆ = ⁅x, y⁆ := by
    intro x y
    obtain ⟨z₁, hz₁, e₁⟩ : ∃ z ∈ Subgroup.center K, α x = x * z :=
      ⟨_, h x, (mul_inv_cancel_left _ _).symm⟩
    obtain ⟨z₂, hz₂, e₂⟩ : ∃ z ∈ Subgroup.center K, α y = y * z :=
      ⟨_, h y, (mul_inv_cancel_left _ _).symm⟩
    rw [map_commutatorElement, e₁, e₂]
    exact commutatorElement_mul_central hz₁ hz₂
  have hle : commutator K ≤ MonoidHom.eqLocus (α : K →* K) (MonoidHom.id K) :=
    Subgroup.commutator_le.2 fun a _ b _ => h1 a b
  ext x
  exact hle (hK ▸ Subgroup.mem_top x)

theorem apply_mem_center {K : Type*} [Group K] (e : MulAut K) {z : K}
    (hz : z ∈ Subgroup.center K) : e z ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  have := congrArg e (hz (e.symm g))
  simpa using this

theorem gen_lift {K G : Type*} [Group K] [Group G] (σ : K →* G)
    (hσ : σ.ker ≤ Subgroup.center K) (φ : MulAut K →* G)
    (hφ : ∀ (e : MulAut K) (k : K), φ e * σ k * (φ e)⁻¹ = σ (e k))
    (E : Subgroup (MulAut K)) (hE : E ≠ ⊥)
    (hgen : Subgroup.closure {s | s ∈ σ.range ∧ ∃ e ∈ E, e ≠ 1 ∧ φ e * s * (φ e)⁻¹ = s} =
      σ.range) :
    Subgroup.closure {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} = ⊤ := by
  set T : Set K := {k : K | ∃ e ∈ E, e ≠ 1 ∧ e k * k⁻¹ ∈ Subgroup.center K} with hT
  obtain ⟨e₀, he₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.1 hE)
  have hcenter : Subgroup.center K ≤ Subgroup.closure T := by
    intro z hz
    refine Subgroup.subset_closure ⟨e₀, e₀.2, fun h => he₀1 (Subtype.ext h), ?_⟩
    exact Subgroup.mul_mem _ (apply_mem_center e₀ hz) (Subgroup.inv_mem _ hz)
  have hfix : ∀ k : K,
      σ k ∈ {s | s ∈ σ.range ∧ ∃ e ∈ E, e ≠ 1 ∧ φ e * s * (φ e)⁻¹ = s} → k ∈ T := by
    rintro k ⟨-, e, he, he1, hfe⟩
    refine ⟨e, he, he1, hσ ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hφ, hfe, mul_inv_cancel]
  have hD : σ.range ≤ (Subgroup.closure T).map σ := by
    rw [← hgen, Subgroup.closure_le]
    rintro s hs
    obtain ⟨k, rfl⟩ := hs.1
    exact ⟨k, Subgroup.subset_closure (hfix k hs), rfl⟩
  rw [eq_top_iff]
  intro k _
  obtain ⟨c, hc, hck⟩ := hD ⟨k, rfl⟩
  have hker : c⁻¹ * k ∈ σ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
  have := Subgroup.mul_mem _ hc (hcenter (hσ hker))
  simpa using this

theorem eq_conj_of_apply_eq {K G : Type*} [Group K] [Group G] (hK : commutator K = ⊤)
    (σ : K →* G) (hσ : σ.ker ≤ Subgroup.center K) (φ : MulAut K →* G)
    (hφ : ∀ (e : MulAut K) (k : K), φ e * σ k * (φ e)⁻¹ = σ (e k)) {e : MulAut K} {k₀ : K}
    (hk₀ : σ k₀ = φ e) : MulAut.conj k₀ = e := by
  have hdev : ∀ x : K, x⁻¹ * ((MulAut.conj k₀)⁻¹ * e) x ∈ Subgroup.center K := by
    intro x
    have h1 : σ (e x) = σ (k₀ * x * k₀⁻¹) := by
      rw [← hφ e x, ← hk₀, map_mul, map_mul, map_inv]
    have h2 : (k₀ * x * k₀⁻¹)⁻¹ * e x ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := hσ h2
    have h4 : x⁻¹ * ((MulAut.conj k₀)⁻¹ * e) x = k₀⁻¹ * ((k₀ * x * k₀⁻¹)⁻¹ * e x) * k₀ := by
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
      group
    rw [h4]
    have h5 := Subgroup.mem_center_iff.1 h3 k₀⁻¹
    rw [h5, mul_assoc, inv_mul_cancel, mul_one]
    exact h3
  exact inv_mul_eq_one.1 (eq_one_of_central_deviation hK _ hdev)

theorem conj_eq_one_iff {K : Type*} [Group K] {k : K} :
    MulAut.conj k = 1 ↔ k ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h g
    have := congrArg (fun f : MulAut K => f g) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * k = (k * g * k⁻¹) * k := by rw [this]
      _ = k * g := by group
  · intro h
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc k * g * k⁻¹ = g * k * k⁻¹ := by rw [← h g]
      _ = g := by group

theorem exists_abelian_card_27 {K G : Type*} [Group K] [Finite K] [Group G]
    (hK : commutator K = ⊤) (σ : K →* G) (hσ : σ.ker ≤ Subgroup.center K) (φ : MulAut K →* G)
    (hφ : ∀ (e : MulAut K) (k : K), φ e * σ k * (φ e)⁻¹ = σ (e k))
    (E : Subgroup (MulAut K)) (hEcard : Nat.card E = 9) (hZ : Nat.card (Subgroup.center K) = 3)
    (hin : ∀ e ∈ E, φ e ∈ σ.range)
    (hcomm : ∀ k l : K, MulAut.conj k ∈ E → MulAut.conj l ∈ E → k * l = l * k) :
    ∃ P : Subgroup K, Nat.card P = 27 ∧ ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
  have hinner : ∀ e ∈ E, ∃ k : K, MulAut.conj k = e := by
    intro e he
    obtain ⟨k₀, hk₀⟩ := hin e he
    exact ⟨k₀, eq_conj_of_apply_eq hK σ hσ φ hφ hk₀⟩
  let P : Subgroup K := E.comap (MulAut.conj : K →* MulAut K)
  refine ⟨P, ?_, fun x hx y hy => hcomm x y hx hy⟩
  let ψ : P →* MulAut K := (MulAut.conj : K →* MulAut K).comp P.subtype
  have hrange : ψ.range = E := by
    ext e
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      exact hk
    · intro he
      obtain ⟨k, hk⟩ := hinner e he
      exact ⟨⟨k, by simpa [P, hk] using he⟩, hk⟩
  have hker : Nat.card ψ.ker = 3 := by
    rw [← hZ]
    refine Nat.card_congr
      { toFun := fun p => ⟨(p.1 : K), conj_eq_one_iff.1 p.2⟩
        invFun := fun c => ⟨⟨(c : K), by
          show MulAut.conj (c : K) ∈ E
          rw [conj_eq_one_iff.2 c.2]
          exact E.one_mem⟩, conj_eq_one_iff.2 c.2⟩
        left_inv := fun p => rfl
        right_inv := fun c => rfl }
  have := Subgroup.card_ker_mul_card_range ψ
  rw [hrange, hEcard, hker] at this
  omega

end CFSG.AGLEmbedding.KFactProofs.CoverThree.SL3FourGen
