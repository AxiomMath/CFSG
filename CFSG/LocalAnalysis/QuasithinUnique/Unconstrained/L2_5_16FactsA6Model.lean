module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsS6
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21FinA6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSixCount

public section

namespace CFSG.QuasithinUnique.Unc25K1.A6Model

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

theorem card_alt6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem exists_pslEquiv :
    ∃ (θ : ↥s6 →* Perm (Fin 6)) (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6)),
      Function.Injective θ ∧ ∀ x : ↥A6Models.psl29,
        ((ψ x : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          θ (Subgroup.inclusion psl29_le_s6 x) := by
  obtain ⟨θ, hθinj, hθeven⟩ := exists_s6_hom
  let ψ₀ : ↥A6Models.psl29 →* alternatingGroup (Fin 6) :=
    (θ.comp (Subgroup.inclusion psl29_le_s6)).codRestrict _ (fun x => hθeven _ x.2)
  have hinj : Function.Injective ψ₀ := fun a b h =>
    Subgroup.inclusion_injective _ (hθinj (congrArg Subtype.val h))
  have hbij : Function.Bijective ψ₀ :=
    hinj.bijective_of_nat_card_le (by rw [card_psl29, card_alt6])
  exact ⟨θ, MulEquiv.ofBijective ψ₀ hbij, hθinj, fun x => rfl⟩

@[expose] def conjAut (a : ↥A6Models.autA6) : MulAut ↥A6Models.psl29 where
  toFun x := ⟨(a : P10) * (x : P10) * (a : P10)⁻¹, psl29_normal _ a.2 _ x.2⟩
  invFun x := ⟨(a : P10)⁻¹ * (x : P10) * (a : P10), by
    have h := psl29_normal _ (A6Models.autA6.inv_mem a.2) _ x.2
    simpa using h⟩
  left_inv x := by
    apply Subtype.ext
    show (a : P10)⁻¹ * ((a : P10) * (x : P10) * (a : P10)⁻¹) * (a : P10) = x
    group
  right_inv x := by
    apply Subtype.ext
    show (a : P10) * ((a : P10)⁻¹ * (x : P10) * (a : P10)) * (a : P10)⁻¹ = x
    group
  map_mul' x y := by
    apply Subtype.ext
    show (a : P10) * ((x : P10) * (y : P10)) * (a : P10)⁻¹ =
      ((a : P10) * (x : P10) * (a : P10)⁻¹) * ((a : P10) * (y : P10) * (a : P10)⁻¹)
    group

theorem conjAut_apply (a : ↥A6Models.autA6) (x : ↥A6Models.psl29) :
    ((conjAut a x : ↥A6Models.psl29) : P10) = (a : P10) * (x : P10) * (a : P10)⁻¹ := rfl

theorem conjAut_injective : Function.Injective conjAut := by
  intro a b h
  have hcomm : ∀ x ∈ A6Models.psl29,
      ((a : P10)⁻¹ * (b : P10)) * x = x * ((a : P10)⁻¹ * (b : P10)) := by
    intro x hx
    have hx' := congrArg
      (fun f : MulAut ↥A6Models.psl29 => ((f ⟨x, hx⟩ : ↥A6Models.psl29) : P10)) h
    simp only [conjAut_apply] at hx'
    calc (a : P10)⁻¹ * (b : P10) * x = (a : P10)⁻¹ * ((b : P10) * x * (b : P10)⁻¹) * (b : P10) := by
          group
      _ = (a : P10)⁻¹ * ((a : P10) * x * (a : P10)⁻¹) * (b : P10) := by rw [hx']
      _ = x * ((a : P10)⁻¹ * (b : P10)) := by group
  have hmem : (a : P10)⁻¹ * (b : P10) ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.inv_mem a.2) b.2
  have h1 := centralizer_psl29 hmem hcomm
  apply Subtype.ext
  calc (a : P10) = (a : P10) * ((a : P10)⁻¹ * (b : P10)) := by rw [h1, mul_one]
    _ = (b : P10) := by group

@[expose] def conjHom : ↥A6Models.autA6 →* MulAut ↥A6Models.psl29 where
  toFun := conjAut
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show (1 : P10) * (x : P10) * (1 : P10)⁻¹ = x
    group
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    show ((a * b : ↥A6Models.autA6) : P10) * (x : P10) * ((a * b : ↥A6Models.autA6) : P10)⁻¹ =
      (a : P10) * ((b : P10) * (x : P10) * (b : P10)⁻¹) * (a : P10)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem conjAut_surjective : Function.Surjective conjAut := by
  obtain ⟨-, ψ, -, -⟩ := exists_pslEquiv
  have hcard : Nat.card (MulAut ↥A6Models.psl29) ≤ 1440 := by
    have h :=
      CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    rwa [← Nat.card_congr (MulAut.congr ψ).toEquiv] at h
  have : Finite (MulAut ↥A6Models.psl29) :=
    Finite.of_injective (fun f : MulAut ↥A6Models.psl29 => (f : ↥A6Models.psl29 → ↥A6Models.psl29))
      DFunLike.coe_injective
  exact (conjAut_injective.bijective_of_nat_card_le (by rw [card_autA6]; exact hcard)).2

noncomputable def conjEquiv : ↥A6Models.autA6 ≃* MulAut ↥A6Models.psl29 :=
  MulEquiv.ofBijective conjHom ⟨conjAut_injective, conjAut_surjective⟩

noncomputable def thetaEquiv {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29) :
    MulAut K ≃* ↥A6Models.autA6 :=
  (MulAut.congr φ).trans conjEquiv.symm

theorem thetaEquiv_spec {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29) (γ : MulAut K) (k : K) :
    ((φ (γ k) : ↥A6Models.psl29) : P10) = ((thetaEquiv φ γ : ↥A6Models.autA6) : P10) *
      ((φ k : ↥A6Models.psl29) : P10) * ((thetaEquiv φ γ : ↥A6Models.autA6) : P10)⁻¹ := by
  have h : conjHom (thetaEquiv φ γ) = MulAut.congr φ γ := conjEquiv.apply_symm_apply _
  have h2 := congrArg (fun f : MulAut ↥A6Models.psl29 => ((f (φ k) : ↥A6Models.psl29) : P10)) h
  have h3 : (MulAut.congr φ γ) (φ k) = φ (γ k) := by
    show φ (γ (φ.symm (φ k))) = φ (γ k)
    rw [φ.symm_apply_apply]
  simp only [h3] at h2
  exact h2.symm

theorem thetaEquiv_eq {K : Type*} [Group K] (φ : K ≃* ↥A6Models.psl29) (γ : MulAut K)
    (b : ↥A6Models.autA6)
    (h : ∀ k : K, ((φ (γ k) : ↥A6Models.psl29) : P10) =
      (b : P10) * ((φ k : ↥A6Models.psl29) : P10) * (b : P10)⁻¹) :
    thetaEquiv φ γ = b := by
  apply conjAut_injective
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  obtain ⟨k, rfl⟩ := φ.surjective x
  rw [conjAut_apply, conjAut_apply, ← thetaEquiv_spec, h]

theorem s6_induces {K : Type*} [Group K] (θ : ↥s6 →* Perm (Fin 6))
    (ψ : ↥A6Models.psl29 ≃* alternatingGroup (Fin 6))
    (hψθ : ∀ x : ↥A6Models.psl29, ((ψ x : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      θ (Subgroup.inclusion psl29_le_s6 x))
    (e : K ≃* alternatingGroup (Fin 6)) (γ : MulAut K)
    (hb : ((thetaEquiv (e.trans ψ.symm) γ : ↥A6Models.autA6) : P10) ∈ s6) :
    ∃ τ : Perm (Fin 6), ∀ k : K, ((e (γ k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      τ * ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) * τ⁻¹ := by
  set φ : K ≃* ↥A6Models.psl29 := e.trans ψ.symm with hφ
  set b : ↥A6Models.autA6 := thetaEquiv φ γ with hbdef
  refine ⟨θ ⟨(b : P10), hb⟩, fun k => ?_⟩
  have hspec := thetaEquiv_spec φ γ k
  have h1 : Subgroup.inclusion psl29_le_s6 (φ (γ k)) =
      ⟨(b : P10), hb⟩ * Subgroup.inclusion psl29_le_s6 (φ k) * ⟨(b : P10), hb⟩⁻¹ := by
    apply Subtype.ext
    exact hspec
  have h2 : ψ (φ k) = e k := by simp [hφ]
  have h3 : ψ (φ (γ k)) = e (γ k) := by simp [hφ]
  have h4 : ((e (γ k) : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      θ (Subgroup.inclusion psl29_le_s6 (φ (γ k))) := by
    rw [← h3]
    exact hψθ _
  have h5 : ((e k : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      θ (Subgroup.inclusion psl29_le_s6 (φ k)) := by
    rw [← h2]
    exact hψθ _
  rw [h4, h1, map_mul, map_mul, map_inv, ← h5]

theorem classify (B : Subgroup P10) (hB : B ≤ A6Models.autA6) (hpsl : A6Models.psl29 ≤ B)
    (hσ : ∃ σ ∈ B, σ ∉ s6) :
    B = A6Models.pgl29 ∨ B = A6Models.m10 ∨ B = A6Models.autA6 := by
  obtain ⟨σ, hσB, hσs6⟩ := hσ
  have hσA : σ ∈ A6Models.autA6 := hB hσB
  obtain ⟨r, hr, hσr⟩ := (mem_autA6_iff_exists σ).1 hσA
  have finish : ∀ M : Subgroup P10, Nat.card M = 720 → M ≤ B → B = M ∨ B = A6Models.autA6 := by
    intro M hM720 hMB
    have hd1 : 720 ∣ Nat.card B := hM720 ▸ Subgroup.card_dvd_of_le hMB
    have hd2 : Nat.card B ∣ 1440 := card_autA6 ▸ Subgroup.card_dvd_of_le hB
    obtain ⟨k, hk⟩ := hd1
    have hk2 : k ≤ 2 := by
      have := Nat.le_of_dvd (by norm_num) hd2
      omega
    interval_cases k
    · have := Nat.card_pos (α := B)
      omega
    · left
      exact (Subgroup.eq_of_le_of_card_ge hMB (by omega)).symm
    · right
      exact Subgroup.eq_of_le_of_card_ge hB (by rw [card_autA6]; omega)
  simp only [autRepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact absurd (psl29_le_s6 (by simpa using hσr)) hσs6
  · have hM : A6Models.pgl29 ≤ B := by
      intro x hx
      obtain ⟨r', hr', hxr⟩ := (Out21.A6.mem_pgl29_iff x).1 hx
      simp only [Out21.A6.pglReps, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hpsl (by simpa using hxr)
      · have e : x = (x * A6Models.tMul⁻¹) * (σ * A6Models.tMul⁻¹)⁻¹ * σ := by group
        rw [e]
        exact B.mul_mem (B.mul_mem (hpsl hxr) (B.inv_mem (hpsl hσr))) hσB
    rcases finish _ Out21.A6.card_pgl29 hM with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · exact absurd ((mem_s6_iff_exists σ).2 ⟨A6Models.tFrob, by simp [s6RepsP], hσr⟩) hσs6
  · have hM : A6Models.m10 ≤ B := by
      intro x hx
      obtain ⟨r', hr', hxr⟩ := (Out21.A6.mem_m10_iff x).1 hx
      simp only [Out21.A6.m10Reps, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact hpsl (by simpa using hxr)
      · rw [Out21.A6.tMulFrob_eq] at hxr
        have e : x = (x * (A6Models.tMul * A6Models.tFrob)⁻¹) *
            (σ * (A6Models.tMul * A6Models.tFrob)⁻¹)⁻¹ * σ := by group
        rw [e]
        exact B.mul_mem (B.mul_mem (hpsl hxr) (B.inv_mem (hpsl hσr))) hσB
    rcases finish _ Out21.A6.card_m10 hM with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end CFSG.QuasithinUnique.Unc25K1.A6Model
