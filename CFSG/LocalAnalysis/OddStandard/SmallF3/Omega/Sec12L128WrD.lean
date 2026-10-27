module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123Hom

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem sec128_D_side {G : Type} [Group G] [Finite G] {D B X0 : Subgroup G}
    {φ₀ : (Fin 5 → ZMod 2) → G} (hXD : X0 ≤ D) (hXB : X0 ⊓ B = ⊥)
    (hX : Nonempty (↥X0 ≃* ↥(alternatingGroup (Fin 5))))
    (hP : IsPermModuleVia IsEvenVec φ₀ B D (alternatingGroup (Fin 5)))
    (hC : centralizer (B : Set G) ⊓ D = B) :
    ∃ χ : ↥(alternatingGroup (Fin 5)) →* ↥D, Function.Injective χ ∧
      (∀ a : ↥(alternatingGroup (Fin 5)), (χ a : G) ∈ X0) ∧
      (∀ (a : ↥(alternatingGroup (Fin 5))) (v : Fin 5 → ZMod 2), IsEvenVec v →
        (χ a : G) * φ₀ v * (χ a : G)⁻¹ = φ₀ (permVec (a : Equiv.Perm (Fin 5)) v)) ∧
      ∀ d : ↥D, ∃ (b : G) (a : ↥(alternatingGroup (Fin 5))), b ∈ B ∧
        (d : G) = b * (χ a : G) := by
  classical
  obtain ⟨-, hinj, hmem, hact, -⟩ := hP
  have hactD : ∀ x ∈ D, ∃ σ : Equiv.Perm (Fin 5), ∀ v, IsEvenVec v →
      x * φ₀ v * x⁻¹ = φ₀ (permVec σ v) := by
    intro x hx
    obtain ⟨σ, -, hσ⟩ := hact x hx
    exact ⟨σ, hσ⟩
  obtain ⟨Θ, hΘ⟩ := sec123_exists_hom (φ := φ₀) (H := D) hinj hactD
  have hΘalt : ∀ x : ↥D, Θ x ∈ alternatingGroup (Fin 5) := by
    intro x
    obtain ⟨σ, hσalt, hσ⟩ := hact (x : G) x.2
    have huniq := sec123_perm_unique (φ := φ₀) hinj (hΘ x) hσ
    rw [huniq]
    exact hσalt
  let θ : ↥X0 →* ↥(alternatingGroup (Fin 5)) :=
    { toFun := fun x => ⟨Θ ⟨(x : G), hXD x.2⟩, hΘalt ⟨(x : G), hXD x.2⟩⟩
      map_one' := Subtype.ext (map_one Θ)
      map_mul' := fun x y => Subtype.ext
        (map_mul Θ ⟨(x : G), hXD x.2⟩ ⟨(y : G), hXD y.2⟩) }
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hΘx : Θ ⟨(x : G), hXD x.2⟩ = 1 := by
      have h1 := congrArg Subtype.val hx
      simpa [θ] using h1
    have hcent : (x : G) ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨v, hv, rfl⟩ := (hmem c).mp hc
      have hx1 : (x : G) * φ₀ v * (x : G)⁻¹ = φ₀ v := by
        have h := hΘ ⟨(x : G), hXD x.2⟩ v hv
        rw [hΘx] at h
        simpa [permVec_one] using h
      show φ₀ v * (x : G) = (x : G) * φ₀ v
      calc φ₀ v * (x : G) = ((x : G) * φ₀ v * (x : G)⁻¹) * (x : G) := by rw [hx1]
        _ = (x : G) * φ₀ v := by group
    have hb : (x : G) ∈ B := by
      have h2 : (x : G) ∈ centralizer (B : Set G) ⊓ D := ⟨hcent, hXD x.2⟩
      rwa [hC] at h2
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      have h3 : (x : G) ∈ X0 ⊓ B := ⟨x.2, hb⟩
      rwa [hXB] at h3
    exact Subtype.ext (by simpa using hbot)
  have hcard : Nat.card ↥X0 = Nat.card ↥(alternatingGroup (Fin 5)) :=
    Nat.card_congr hX.some.toEquiv
  have hbij : Function.Bijective θ :=
    (Nat.bijective_iff_injective_and_card θ).mpr ⟨hθinj, hcard⟩
  let θe : ↥X0 ≃* ↥(alternatingGroup (Fin 5)) := MulEquiv.ofBijective θ hbij
  let χ : ↥(alternatingGroup (Fin 5)) →* ↥D :=
    (Subgroup.inclusion hXD).comp θe.symm.toMonoidHom
  have hΘχ : ∀ a : ↥(alternatingGroup (Fin 5)), Θ (χ a) = (a : Equiv.Perm (Fin 5)) := by
    intro a
    have h1 : Θ (χ a) = (θ (θe.symm a) : Equiv.Perm (Fin 5)) := rfl
    rw [h1]
    exact congrArg Subtype.val (MulEquiv.apply_symm_apply θe a)
  refine ⟨χ, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have hab' : (Subgroup.inclusion hXD) (θe.symm a) =
        (Subgroup.inclusion hXD) (θe.symm b) := by
      simpa [χ] using hab
    exact θe.symm.injective (Subgroup.inclusion_injective hXD hab')
  · intro a
    simpa [χ, Subgroup.coe_inclusion] using (θe.symm a).2
  · intro a v hv
    have h := hΘ (χ a) v hv
    rwa [hΘχ a] at h
  · intro d
    let a : ↥(alternatingGroup (Fin 5)) := ⟨Θ d, hΘalt d⟩
    have hΘd : Θ (χ a) = Θ d := by
      simpa only [a] using hΘχ a
    let b : ↥D := d * (χ a)⁻¹
    have hΘb : Θ b = 1 := by
      show Θ (d * (χ a)⁻¹) = 1
      rw [map_mul, map_inv, hΘd]
      group
    have hcentb : (b : G) ∈ centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨v, hv, rfl⟩ := (hmem c).mp hc
      have hb1 : (b : G) * φ₀ v * (b : G)⁻¹ = φ₀ v := by
        have h := hΘ b v hv
        rw [hΘb] at h
        simpa [permVec_one] using h
      show φ₀ v * (b : G) = (b : G) * φ₀ v
      calc φ₀ v * (b : G) = ((b : G) * φ₀ v * (b : G)⁻¹) * (b : G) := by rw [hb1]
        _ = (b : G) * φ₀ v := by group
    have hbB : (b : G) ∈ B := by
      have h2 : (b : G) ∈ centralizer (B : Set G) ⊓ D := ⟨hcentb, b.2⟩
      rwa [hC] at h2
    refine ⟨(b : G), a, hbB, ?_⟩
    show (d : G) = (b : G) * (χ a : G)
    have hbco : (b : G) = (d : G) * (χ a : G)⁻¹ := by simp [b]
    rw [hbco]
    group

end CFSG.OddStandard.SmallF3.Omega
