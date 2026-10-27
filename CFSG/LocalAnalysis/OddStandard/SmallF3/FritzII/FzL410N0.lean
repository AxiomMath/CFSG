module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Emb

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open _root_.Certificates

theorem fz410_normRho (hN : FzL410.NormSpec) (σ : FzL410.A →+ FzL410.A)
    (h3 : ∀ p, σ (σ (σ p)) = p) (hfpf : ∀ p, σ p = p → p = 0) :
    ∃ β : FzL410.A →+ FzL410.A, Function.Injective β ∧ ∀ p, σ (β p) = β (FzL410.rho p) := by
  have hgen3 : (2 : ℕ) • σ (0, 0, 1, 0) = 0 := (fz410_hom_gen_two σ).1
  have hgen4 : (2 : ℕ) • σ (0, 0, 0, 1) = 0 := (fz410_hom_gen_two σ).2
  have hev : ∀ q : FzL410.A,
      FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0)) (σ (0, 0, 0, 1)) q
        = σ q :=
    fun q => (fz410_hom_eq_ev σ q).symm
  have his : FzL410.IsRho3 (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0))
      (σ (0, 0, 0, 1)) := by
    constructor
    · intro p
      rw [hev, hev, hev]
      exact h3 p
    · intro p hp
      rw [hev] at hp
      exact hfpf p hp
  have hN' := hN
  unfold FzL410.NormSpec FzL410.NormRow at hN'
  obtain ⟨a, b, hab⟩ := hN' (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0)) hgen3
    (σ (0, 0, 0, 1)) hgen4 his
  unfold FzL410.ConjRho at hab
  obtain ⟨hb, hcomm, hinj⟩ := hab
  have hσb : (2 : ℕ) • σ b = 0 := by
    rw [← map_nsmul, hb, map_zero]
  have hb' : (2 : ℕ) • FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0))
      (σ (0, 0, 0, 1)) b = 0 := by
    rw [hev b]
    exact hσb
  let β : FzL410.A →+ FzL410.A :=
    fz410EvHom a (FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0))
      (σ (0, 0, 0, 1)) a) b (FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0))
      (σ (0, 0, 1, 0)) (σ (0, 0, 0, 1)) b) hb hb'
  have hβ : ∀ p : FzL410.A, β p = FzL410.ev a (FzL410.ev (σ (1, 0, 0, 0))
      (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0)) (σ (0, 0, 0, 1)) a) b
      (FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0))
        (σ (0, 0, 0, 1)) b) p :=
    fun p => rfl
  refine ⟨β, ?_, ?_⟩
  · intro p q hpq
    have h0 : β (p - q) = 0 := by
      rw [sub_eq_add_neg, map_add, map_neg, hpq]
      abel
    have hz : FzL410.ev a (FzL410.ev (σ (1, 0, 0, 0)) (σ (0, 1, 0, 0))
        (σ (0, 0, 1, 0)) (σ (0, 0, 0, 1)) a) b (FzL410.ev (σ (1, 0, 0, 0))
        (σ (0, 1, 0, 0)) (σ (0, 0, 1, 0)) (σ (0, 0, 0, 1)) b) (p - q) = 0 := by
      simpa only [hβ] using h0
    exact sub_eq_zero.mp (hinj (p - q) hz)
  · intro p
    rw [hβ p, ← hev, hβ (FzL410.rho p)]
    exact hcomm p

variable {G : Type} [Group G]

theorem fzl410_N0 (hN : FzL410.NormSpec) {P : Subgroup G} {rho : G} (hr3 : rho ^ 3 = 1)
    (hnrm : ∀ p ∈ P, rho * p * rho⁻¹ ∈ P) (hfpf : ∀ p ∈ P, rho * p * rho⁻¹ = p → p = 1)
    (φ₀ : ↥P ≃* Multiplicative FzL410.A) :
    ∃ emb : FzL410.A → G, Fz410EmbBase P rho emb := by
  obtain ⟨emb0, hcoord⟩ := Fz410Coord.of_iso φ₀
  obtain ⟨σ, hσ⟩ := hcoord.exists_act hnrm
  have h3 : ∀ a, σ (σ (σ a)) = a := by
    intro a
    apply hcoord.inj
    calc emb0 (σ (σ (σ a))) = rho * emb0 (σ (σ a)) * rho⁻¹ := (hσ (σ (σ a))).symm
      _ = rho * (rho * emb0 (σ a) * rho⁻¹) * rho⁻¹ := by rw [(hσ (σ a)).symm]
      _ = rho * (rho * (rho * emb0 a * rho⁻¹) * rho⁻¹) * rho⁻¹ := by rw [(hσ a).symm]
      _ = emb0 a := by
            have h1 : rho * (rho * (rho * emb0 a * rho⁻¹) * rho⁻¹) * rho⁻¹
                = (MulAut.conj rho ^ 3) (emb0 a) := by
              simp only [pow_succ, pow_one, pow_zero, MulAut.mul_apply, MulAut.conj_apply,
                MulAut.one_apply]
            rw [h1, ← map_pow, hr3, map_one, MulAut.one_apply]
  have hfpf' : ∀ p, σ p = p → p = 0 := by
    intro p hp
    apply hcoord.inj
    have heq : rho * emb0 p * rho⁻¹ = emb0 p := by rw [hσ p, hp]
    have h1 : emb0 p = 1 := hfpf (emb0 p) (hcoord.emb_mem p) heq
    rw [h1, hcoord.emb_zero]
  obtain ⟨β, hβinj, hβcomm⟩ := fz410_normRho hN σ h3 hfpf'
  have hcoordβ : Fz410Coord P (fun a => emb0 (β a)) := hcoord.comp (ψ := β) hβinj
  have hcj : ∀ a, rho * emb0 (β a) * rho⁻¹ = emb0 (β (FzL410.rho a)) := by
    intro a
    rw [hσ (β a), hβcomm a]
  exact ⟨fun a => emb0 (β a), ⟨hcoordβ, hcj⟩⟩

end CFSG.OddStandard.SmallF3.FritzII
