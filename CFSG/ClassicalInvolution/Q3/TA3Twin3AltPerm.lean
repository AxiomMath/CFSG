module

public import CFSG.ClassicalInvolution.SmallCases.NobqAlt
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataLift

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Twin3

open Equiv Equiv.Perm CFSG.OddStandard.Solomon75.AhatData

theorem perm_apply_inv_self {α : Type*} (σ : Perm α) (x : α) : σ (σ⁻¹ x) = x :=
  σ.apply_symm_apply x

@[expose] def γ₀ : Perm (Fin 8) :=
  ⟨![1, 2, 3, 0, 5, 6, 7, 4], ![3, 0, 1, 2, 7, 4, 5, 6], by decide, by decide⟩

@[expose] def x₀ : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

@[expose] def u₀ : Perm (Fin 8) := swap 0 2 * swap 4 6

@[expose] def c₀ : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def Fpf8 (σ : Perm (Fin 8)) : Prop := σ * σ = 1 ∧ σ.support.card = 8

instance (σ : Perm (Fin 8)) : Decidable (Fpf8 σ) := inferInstanceAs (Decidable (_ ∧ _))

theorem fpf8_x₀ : Fpf8 x₀ := by decide
theorem u₀_facts : u₀ * u₀ = 1 ∧ u₀.support.card = 4 := by decide
theorem fpf8_w₀ : Fpf8 (u₀ * γ₀) := by decide
theorem fpf8_τ₀ : Fpf8 (γ₀ * γ₀) := by decide
theorem fpf8_c₀ : Fpf8 c₀ := by decide
theorem x₀_comm_u₀ : x₀ * u₀ = u₀ * x₀ := by decide
theorem x₀_comm_w₀ : x₀ * (u₀ * γ₀) = u₀ * γ₀ * x₀ := by decide
theorem x₀_comm_τ₀ : x₀ * (γ₀ * γ₀) = γ₀ * γ₀ * x₀ := by decide
theorem fpf8_x₀u₀ : Fpf8 (x₀ * u₀) := by decide
theorem fpf8_x₀w₀ : Fpf8 (x₀ * (u₀ * γ₀)) := by decide
theorem fpf8_x₀τ₀ : Fpf8 (x₀ * (γ₀ * γ₀)) := by decide
theorem sign_γ₀ : sign γ₀ = 1 := by decide
theorem u₀_inv : u₀⁻¹ = u₀ := by decide
theorem γ₀_sq_ne (i : Fin 8) : (γ₀ * γ₀) i ≠ i := by revert i; decide

theorem e8_fin8 : x₀ * c₀ = c₀ * x₀ ∧ γ₀ * γ₀ * c₀ = c₀ * (γ₀ * γ₀) ∧ Fpf8 (x₀ * c₀) ∧
    Fpf8 (γ₀ * γ₀ * c₀) ∧ Fpf8 (x₀ * (γ₀ * γ₀) * c₀) := by
  decide

variable {n : ℕ}

noncomputable abbrev via (ι : Fin 8 ↪ Fin n) : Perm (Fin 8) →* Perm (Fin n) :=
  Perm.viaEmbeddingHom ι

theorem card_support_via (ι : Fin 8 ↪ Fin n) (σ : Perm (Fin 8)) :
    (via ι σ).support.card = σ.support.card := by
  let : DecidablePred (· ∈ Set.range ι.toFun) := fun _ => Classical.propDecidable _
  exact Perm.card_support_extend_domain _

theorem sign_via (ι : Fin 8 ↪ Fin n) (σ : Perm (Fin 8)) : sign (via ι σ) = sign σ := by
  let : DecidablePred (· ∈ Set.range ι.toFun) := fun _ => Classical.propDecidable _
  exact Perm.sign_extendDomain _ _

theorem isoI_via (ι : Fin 8 ↪ Fin n) {σ : Perm (Fin 8)} (h : Fpf8 σ) : IsoI (via ι σ) :=
  ⟨by rw [← map_mul, h.1, map_one], by rw [card_support_via, h.2]⟩

theorem dblI_via (ι : Fin 8 ↪ Fin n) {σ : Perm (Fin 8)}
    (h : σ * σ = 1 ∧ σ.support.card = 4) : DblI (via ι σ) :=
  ⟨by rw [← map_mul, h.1, map_one], by rw [card_support_via, h.2]⟩

theorem exists_e8 (ι : Fin 8 ↪ Fin n) :
    ∃ a b c : Perm (Fin n), IsoI a ∧ IsoI b ∧ IsoI c ∧ Indep2 a b ∧ Indep3 a b c := by
  obtain ⟨h12, h13, h14, h15, h16⟩ := e8_fin8
  refine ⟨via ι x₀, via ι (γ₀ * γ₀), via ι c₀, isoI_via ι fpf8_x₀, isoI_via ι fpf8_τ₀,
    isoI_via ι fpf8_c₀, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [← map_mul, ← map_mul, x₀_comm_τ₀]
  · rw [← map_mul]; exact isoI_via ι fpf8_x₀τ₀
  · rw [← map_mul, ← map_mul, h12]
  · rw [← map_mul, ← map_mul, h13]
  · rw [← map_mul]; exact isoI_via ι h14
  · rw [← map_mul]; exact isoI_via ι h15
  · rw [← map_mul, ← map_mul]; exact isoI_via ι h16

open Nobq.AltWitness in
theorem exists_embedding (hn : n ≤ 11) {γ τ : Perm (Fin n)} (hγ : γ * γ = τ) (hτ : IsoI τ)
    (hs : sign γ = 1) : ∃ ι : Fin 8 ↪ Fin n, via ι γ₀ = γ := by
  obtain ⟨p, hp⟩ : ∃ p, τ p ≠ p := by
    by_contra h
    push Not at h
    exact hτ.ne_one (Equiv.ext h)
  obtain ⟨p', hp', hc⟩ : ∃ p', τ p' ≠ p' ∧ ¬ γ.SameCycle p p' := by
    by_contra h
    push Not at h
    have hsub : τ.support ⊆ {p, γ p, γ (γ p), γ (γ (γ p))} := by
      intro x hx
      simpa using moved_mem_orbit hγ hτ.1 h (Perm.mem_support.1 hx)
    have h1 := Finset.card_le_card hsub
    have h2 : ({p, γ p, γ (γ p), γ (γ (γ p))} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
    rw [hτ.2] at h1
    omega
  have hinj := caseI_inj hγ hτ.1 hp hp' hc
  set φ : Fin 8 → Fin n := ![p, γ p, γ (γ p), γ (γ (γ p)), p', γ p', γ (γ p'), γ (γ (γ p'))]
  let ι : Fin 8 ↪ Fin n := ⟨φ, hinj⟩
  have h4 := gamma_four hγ hτ.1
  have hγφ : ∀ i, γ (φ i) = φ (γ₀ i) := by
    intro i
    fin_cases i <;> simp [φ, γ₀, h4 p, h4 p']
  have hτφ : ∀ i, τ (φ i) ≠ φ i := fun i h => by
    rw [← hγ, Perm.mul_apply, hγφ, hγφ] at h
    exact γ₀_sq_ne i (hinj h)
  have hτz : ∀ z, z ∉ Set.range φ → τ z = z := by
    intro z hz
    by_contra hne
    have hsub : insert z (Finset.univ.image φ) ⊆ τ.support := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rw [Perm.mem_support]
      rcases hy with rfl | hy
      · exact hne
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hτφ i
    have hzn : z ∉ Finset.univ.image φ := fun h => hz (by simpa using h)
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hzn, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin, hτ.2] at this
    omega
  have hγz : ∀ z, z ∉ Set.range φ → γ z ∉ Set.range φ := by
    rintro z hz ⟨i, hi⟩
    exact hz ⟨γ₀⁻¹ i, γ.injective (by rw [hγφ, perm_apply_inv_self, hi])⟩
  refine ⟨ι, ?_⟩
  set γB := via ι γ₀ with hγB
  have hB : ∀ i, γB (φ i) = φ (γ₀ i) := fun i => Perm.viaEmbedding_apply γ₀ ι i
  have hBi : ∀ i, γB⁻¹ (φ i) = φ (γ₀⁻¹ i) := fun i => by
    rw [Perm.inv_eq_iff_eq, hB, perm_apply_inv_self]
  have hBz : ∀ z, z ∉ Set.range φ → γB⁻¹ z = z := fun z hz => by
    rw [Perm.inv_eq_iff_eq]
    exact (Perm.viaEmbedding_apply_of_notMem γ₀ ι z hz).symm
  set ρ := γ * γB⁻¹ with hρ
  have hρφ : ∀ i, ρ (φ i) = φ i := fun i => by
    rw [hρ, Perm.mul_apply, hBi, hγφ, perm_apply_inv_self]
  have hρz : ∀ z, z ∉ Set.range φ → ρ z = γ z := fun z hz => by
    rw [hρ, Perm.mul_apply, hBz z hz]
  have hρ2 : ρ * ρ = 1 := by
    ext z
    rw [Perm.mul_apply, Perm.one_apply]
    by_cases hz : z ∈ Set.range φ
    · obtain ⟨i, rfl⟩ := hz
      rw [hρφ, hρφ]
    · rw [hρz z hz, hρz _ (hγz z hz), ← Perm.mul_apply, hγ, hτz z hz]
  have hρs : sign ρ = 1 := by
    rw [hρ, Perm.sign_mul, Perm.sign_inv, hγB, sign_via, hs, sign_γ₀, mul_one]
  have hρ1 : ρ = 1 := by
    by_contra hne
    have hc := support_card_of_involution hn hρ2 hne hρs
    have hsub : ρ.support ⊆ (Finset.univ.image φ)ᶜ := by
      intro z hz
      rw [Finset.mem_compl, Finset.mem_image]
      rintro ⟨i, -, rfl⟩
      exact (Perm.mem_support.1 hz) (hρφ i)
    have := Finset.card_le_card hsub
    rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin] at this
    omega
  exact (mul_inv_eq_one.1 hρ1).symm

end CFSG.ClassicalInvolution.Q3.TA3.Twin3
