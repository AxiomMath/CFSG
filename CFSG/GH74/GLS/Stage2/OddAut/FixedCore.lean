module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67CoreTools

public section

namespace CFSG.GH74.GLS.Stage2.OddAut

open Subgroup CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {Y : Type} [Group Y]

theorem false_of_fixed_core {r : ℕ} {V Z : Subgroup (MulAut Y)} (hcen : Subgroup.center Y = ⊥)
    (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z) {φ : MulAut Y} (hφV : φ ∈ V) (hφ1 : φ ≠ 1)
    (hA : ∀ F₀ : Subgroup ↥(fixSub φ), F₀.Normal → (∀ x y : F₀, x * y = y * x) → F₀ = ⊥)
    (hB : ∀ ζ : MulAut Y, Odd (orderOf ζ) → Nat.Coprime (orderOf ζ) r → ζ * φ = φ * ζ →
      (∀ c ∈ fixSub φ, ζ c = c) → ζ = 1) : False := by
  obtain ⟨-, -, -, -, hZab, hZodd, hZcop, hZbot, hcomm⟩ := h2
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  set F₀ : Subgroup ↥(fixSub φ) :=
    ((Z.comap (MulAut.conj : Y →* MulAut Y)).subgroupOf (fixSub φ)) with hF₀
  have hF₀mem : ∀ x : ↥(fixSub φ), x ∈ F₀ ↔ MulAut.conj (x : Y) ∈ Z := fun x => Iff.rfl
  have hnormal : F₀.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxZ : MulAut.conj (x : Y) ∈ Z := (hF₀mem x).1 hx
    have hgN := h3 φ hφV hφ1 (g : Y) g.2
    have h1 := (Subgroup.mem_normalizer_iff.1 hgN _).1 hxZ
    rw [hF₀mem]
    simpa [map_mul, map_inv] using h1
  have habel : ∀ x y : F₀, x * y = y * x := by
    intro x y
    have hx : MulAut.conj ((x : ↥(fixSub φ)) : Y) ∈ Z := (hF₀mem x).1 x.2
    have hy : MulAut.conj ((y : ↥(fixSub φ)) : Y) ∈ Z := (hF₀mem y).1 y.2
    apply Subtype.ext
    apply Subtype.ext
    apply hinj
    simp only [Subgroup.coe_mul, map_mul]
    exact hZab _ hx _ hy
  have hbot : F₀ = ⊥ := hA F₀ hnormal habel
  have hfix : ∀ z ∈ Z, ∀ c ∈ fixSub φ, z c = c := by
    intro z hz c hc
    have hzF : z c ∈ fixSub φ := by
      rw [mem_fixSub] at hc ⊢
      have := hcomm φ hφV z hz
      have h1 := congrArg (fun t : MulAut Y => t c) this
      simp only [MulAut.mul_apply] at h1
      rw [h1, hc]
    have hnorm := h3 φ hφV hφ1 c hc
    have h1 := (Subgroup.mem_normalizer_iff.1 hnorm z).1 hz
    have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
    have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
      have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
        have := mulAut_conj_conj z c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
          = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
    rw [h5] at h4
    have hmemF : c * z c⁻¹ ∈ fixSub φ := by
      rw [map_inv]
      exact Subgroup.mul_mem _ hc (Subgroup.inv_mem _ hzF)
    have hx : (⟨c * z c⁻¹, hmemF⟩ : ↥(fixSub φ)) ∈ F₀ := (hF₀mem _).2 h4
    rw [hbot, Subgroup.mem_bot] at hx
    have h6 : c * z c⁻¹ = 1 := congrArg Subtype.val hx
    have h7 : z c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h6
      simpa using this
    have := congrArg (fun t => t⁻¹) h7
    simpa using this
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hdvd : orderOf (z : MulAut Y) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hodd : Odd (orderOf (z : MulAut Y)) := Odd.of_dvd_nat hZodd hdvd
  have hcop : Nat.Coprime (orderOf (z : MulAut Y)) r := Nat.Coprime.coprime_dvd_left hdvd hZcop
  have hzφ : (z : MulAut Y) * φ = φ * (z : MulAut Y) := (hcomm φ hφV z z.2).symm
  have := hB z hodd hcop hzφ (fun c hc => hfix z z.2 c hc)
  exact hz1 (Subtype.ext this)

end CFSG.GH74.GLS.Stage2.OddAut
