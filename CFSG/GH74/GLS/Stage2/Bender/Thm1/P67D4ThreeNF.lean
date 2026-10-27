module

public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Props

variable {Y : Type} [Group Y]

@[expose] def D4NoAbel (φ : MulAut Y) : Prop :=
  ∀ F₀ : Subgroup ↥(fixSub φ), F₀.Normal → (∀ x y : F₀, x * y = y * x) → F₀ = ⊥

@[expose] def D4PtKer (φ : MulAut Y) : Prop :=
  ∀ ζ : MulAut Y, Odd (orderOf ζ) → Nat.Coprime (orderOf ζ) 3 → ζ * φ = φ * ζ →
    (∀ c ∈ fixSub φ, ζ c = c) → ζ = 1

theorem fixSub_inv' (φ : MulAut Y) : fixSub φ⁻¹ = fixSub φ := by
  ext x
  rw [mem_fixSub, mem_fixSub]
  constructor
  · intro h
    have := congrArg (fun t => φ t) h
    simpa using this.symm
  · intro h
    have := congrArg (fun t => φ⁻¹ t) h
    simpa using this.symm

theorem mulAut_mul_conj_inv (δ : MulAut Y) (g : Y) :
    δ * (MulAut.conj g)⁻¹ = MulAut.conj (δ g⁻¹) * δ := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem D4NoAbel.conj {φ : MulAut Y} (h : D4NoAbel φ) (β : MulAut Y) :
    D4NoAbel (β * φ * β⁻¹) := by
  obtain ⟨e⟩ := fixSub_conj_equiv φ β
  exact noAbelNormal_of_equiv e.symm h

theorem D4NoAbel.inv {φ : MulAut Y} (h : D4NoAbel φ) : D4NoAbel φ⁻¹ :=
  noAbelNormal_of_equiv (MulEquiv.subgroupCongr (fixSub_inv' φ)) h

theorem D4PtKer.conj {φ : MulAut Y} (h : D4PtKer φ) (β : MulAut Y) :
    D4PtKer (β * φ * β⁻¹) := by
  intro ζ hodd hcop hcomm hfix
  have hord : orderOf (β⁻¹ * ζ * β) = orderOf ζ := by
    refine SemiconjBy.orderOf_eq β ?_
    show β * (β⁻¹ * ζ * β) = ζ * β
    group
  have h1 := h (β⁻¹ * ζ * β) (hord ▸ hodd) (hord ▸ hcop) ?_ ?_
  · have : ζ = β * (β⁻¹ * ζ * β) * β⁻¹ := by group
    rw [this, h1]
    group
  · calc β⁻¹ * ζ * β * φ = β⁻¹ * (ζ * (β * φ * β⁻¹)) * β := by group
      _ = β⁻¹ * ((β * φ * β⁻¹) * ζ) * β := by rw [hcomm]
      _ = φ * (β⁻¹ * ζ * β) := by group
  · intro c hc
    have hβc : β c ∈ fixSub (β * φ * β⁻¹) := by
      rw [mem_fixSub] at hc ⊢
      simp [MulAut.mul_apply, hc]
    have := hfix (β c) hβc
    simp only [MulAut.mul_apply]
    rw [this]
    simp

theorem D4PtKer.inv {φ : MulAut Y} (h : D4PtKer φ) : D4PtKer φ⁻¹ := by
  intro ζ hodd hcop hcomm hfix
  refine h ζ hodd hcop ?_ (fun c hc => hfix c (by rw [fixSub_inv']; exact hc))
  calc ζ * φ = φ * (φ⁻¹ * ζ) * φ := by group
    _ = φ * (ζ * φ⁻¹) * φ := by rw [← hcomm]
    _ = φ * ζ := by group

end Props

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem d4_outer_three_normal_form {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ : orderOf φ = 3)
    (hout : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      normSeq (fieldActor σ σ) g 3 = 1 ∧
      (φ = MulAut.conj g * fieldActor σ σ ∨ φ⁻¹ = MulAut.conj g * fieldActor σ σ) := by
  classical
  have hK3 : Nat.card K = p ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K p := finite_field_prime_power_characteristic hp (by omega) hK3
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, hΘker, -⟩, hcyc, hcard, -, hcen, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hNF φ
  have hφ3 : φ ^ 3 = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hΘφ : Θ φ = δ := hΘ φ g δ hgδ
  have hδ1 : δ ≠ 1 := by
    intro h
    apply hout
    rw [h, fieldActor_one, mul_one] at hgδ
    rw [hgδ]
    exact ⟨g, rfl⟩
  have hδ3 : δ ^ 3 = 1 := by rw [← hΘφ, ← map_pow, hφ3, map_one]
  have hδord : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  have hσ3 : σ ^ 3 = 1 := by
    refine RingEquiv.ext fun c => ?_
    have h := ringEquiv_cube_apply_eq hK hσ c
    simpa [pow_succ, RingAut.mul_apply] using h
  have hσ1 : σ ≠ 1 := by
    intro h
    have h3 : 3 * f ∣ f := dvd_of_forall_pow_prime_pow_eq hp K hK3 (fun x => by
      have := hσ x
      rw [h] at this
      exact this.symm)
    have := Nat.le_of_dvd (by omega) h3
    omega
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have := hcyc
  obtain ⟨k, hk3, hk⟩ := Finset.mem_image.1 (mem_zpowers_iff_mem_range_orderOf.1
    (mem_zpowers_of_pow_eq_one_of_isCyclic (by norm_num : 0 < 3) hσord hδ3))
  replace hk : σ ^ k = δ := hk
  have hk3' : k < 3 := by simpa [hσord] using hk3
  have hδ₀3 : fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
    have h := map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
    rw [hσ3, map_one] at h
    exact h.symm
  have hZ := hcen
  have hφeq : φ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ := hgδ
  interval_cases k
  · exact (hδ1 (by rw [← hk]; simp)).elim
  ·
    have hkσ : δ = σ := by rw [← hk, pow_one]
    rw [hkσ] at hφeq
    refine ⟨g, ?_, Or.inl hφeq⟩
    refine normSeq_eq_one_of_pow_eq_one hZ hδ₀3 ?_
    rw [← hφeq]; exact hφ3
  ·
    have hδsq : fieldActor (t := TwistTag.D4) σ δ = fieldActor σ σ ^ 2 := by
      rw [← hk]; exact map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 2
    have hinv : φ⁻¹ = MulAut.conj (fieldActor (t := TwistTag.D4) σ σ g⁻¹) *
        fieldActor σ σ := by
      have h1 : φ⁻¹ = (fieldActor (t := TwistTag.D4) σ σ ^ 2)⁻¹ * (MulAut.conj g)⁻¹ := by
        rw [hφeq, hδsq, mul_inv_rev]
      have h2 : (fieldActor (t := TwistTag.D4) σ σ ^ 2)⁻¹ = fieldActor σ σ := by
        have : fieldActor (t := TwistTag.D4) σ σ ^ 2 * fieldActor σ σ = 1 := by
          rw [← pow_succ]; exact hδ₀3
        exact inv_eq_of_mul_eq_one_left this
      rw [h1, h2]
      exact mulAut_mul_conj_inv _ g
    refine ⟨fieldActor σ σ g⁻¹, ?_, Or.inr hinv⟩
    refine normSeq_eq_one_of_pow_eq_one hZ hδ₀3 ?_
    rw [← hinv, inv_pow, hφ3, inv_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
