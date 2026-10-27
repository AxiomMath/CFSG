module

public import CFSG.Sporadic.Co1.Cover.Final

public section

namespace CFSG.EvenSporadicStandard.TwoCo1

open CFSG.Sporadic.Co1.Cover CFSG.Sporadic.Co1.CoverNative CFSG.Monster.Schur
  CFSG.Monster.Schur.M24 CFSG.Blueprint Matrix SemidirectProduct

attribute [local irreducible] eps0 ga gb regCov rrCov epsRows

section Ext

variable {n : ℕ} {P : Type} [Group P]
  (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)))
  {X : Type} [Group X] (ψ : X →* Multiplicative (Fin n → ZMod 2) ⋊[phiOf ρ] P)

@[expose] noncomputable def preVExt (hψ : Function.Surjective ψ) {z : X}
    (hzc : ∀ x, z * x = x * z) (hz2 : z * z = 1) (hzne : z ≠ 1)
    (hker : ψ.ker = Subgroup.zpowers z) : CentralExt n (preV ρ ψ) where
  ψ := projV ρ ψ
  surj := by
    intro v
    obtain ⟨x, hx⟩ := hψ (inl v)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show rightHom (ψ x) = 1
      rw [hx, rightHom_inl]
    · show (ψ x).left = v
      rw [hx]
      rfl
  z := ⟨z, z_mem_preV ρ ψ hker⟩
  central := fun t => Subtype.ext (hzc t.1)
  sq := Subtype.ext hz2
  ne_one := fun h => hzne (congrArg Subtype.val h)
  ker_eq := by
    ext t
    have h1 : t ∈ (projV ρ ψ).ker ↔ ψ t.1 = 1 := by
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        rw [psi_preV ρ ψ t]
        show inl (ψ t.1).left = 1
        rw [show (ψ t.1).left = 1 from h, map_one]
      · intro h
        show (ψ t.1).left = 1
        rw [h]
        rfl
    rw [h1, ← MonoidHom.mem_ker, hker]
    simp only [Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩

end Ext

theorem preV_comm_and_sq {n : ℕ} {P : Type} [Group P] [Group.IsPerfect P]
    (hND : NoPerfectDoubleCover P)
    (ρ : P →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)))
    {X : Type} [Group X] (ψ : X →* Multiplicative (Fin n → ZMod 2) ⋊[phiOf ρ] P)
    (a b : P) (A B : Matrix (Fin n) (Fin n) (ZMod 2)) (hA : ∀ v, ρ a v = A *ᵥ v)
    (hB : ∀ v, ρ b v = B *ᵥ v)
    (hC : ∀ c : Matrix (Fin n) (Fin n) (ZMod 2), cᵀ = c → (∀ i, c i i = 0) →
      Aᵀ * c * A = c → Bᵀ * c * B = c → c = 0)
    (hl : ∀ l : Fin n → ZMod 2, Aᵀ *ᵥ l = l → Bᵀ *ᵥ l = l → l = 0)
    (hψ : Function.Surjective ψ) {z : X} (hzc : ∀ x, z * x = x * z) (hz2 : z * z = 1)
    (hzne : z ≠ 1) (hker : ψ.ker = Subgroup.zpowers z) :
    (∀ t u : preV ρ ψ, t * u = u * t) ∧ ∀ t : preV ρ ψ, t * t = 1 := by
  obtain ⟨σ, hσ⟩ := exists_P_section ρ ψ hND hψ z hz2 hzne hker
  let E := preVExt ρ ψ hψ hzc hz2 hzne hker
  have hfixz : ∀ p, MulAut.conjNormal (σ p) E.z = E.z := fun p =>
    Subtype.ext (by
      show σ p * z * (σ p)⁻¹ = z
      rw [← hzc (σ p), mul_assoc, mul_inv_cancel, mul_one])
  let actA : E.Act A :=
    { γ := (MulAut.conjNormal (σ a)).toMonoidHom
      fix_z := hfixz a
      act := fun t => by
        show projV ρ ψ (MulAut.conjNormal (σ a) t) = _
        rw [projV_conj ρ ψ σ hσ, hA]
        rfl }
  let actB : E.Act B :=
    { γ := (MulAut.conjNormal (σ b)).toMonoidHom
      fix_z := hfixz b
      act := fun t => by
        show projV ρ ψ (MulAut.conjNormal (σ b) t) = _
        rw [projV_conj ρ ψ σ hσ, hB]
        rfl }
  have hcomm := E.comm_of_forms actA actB hC
  exact ⟨hcomm, E.sq_of_functionals hcomm actA actB hl⟩

theorem eps_preimage_comm_and_sq
    {C : Type} [Group C] (π : C →* NativeSporadic.Co1) (ζ : C) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.zpowers ζ) (hζc : ζ ∈ Subgroup.center C) (hζo : orderOf ζ = 2) :
    (∀ a b : C, π a ∈ epsHom.range → π b ∈ epsHom.range → a * b = b * a) ∧
      ∀ a : C, π a ∈ epsHom.range → a * a = 1 := by
  have hζ2 : ζ * ζ = 1 := by
    rw [← pow_two, ← hζo]
    exact pow_orderOf_eq_one ζ
  have hζne : ζ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hζo
    omega
  have hζcomm : ∀ x : C, ζ * x = x * ζ := fun x => (Subgroup.mem_center_iff.1 hζc x).symm
  have hζker : ζ ∈ π.ker := by
    rw [hker]
    exact Subgroup.mem_zpowers ζ
  let X : Subgroup (SM24 × C) :=
    (theta.comp (MonoidHom.fst SM24 C)).eqLocus (π.comp (MonoidHom.snd SM24 C))
  let ψ : X →* SM24 := (MonoidHom.fst SM24 C).comp X.subtype
  have hψ : Function.Surjective ψ := by
    intro s
    obtain ⟨y, hy⟩ := hπ (theta s)
    exact ⟨⟨(s, y), hy.symm⟩, rfl⟩
  let z : X := ⟨(1, ζ), by
    show theta 1 = π ζ
    rw [map_one, MonoidHom.mem_ker.1 hζker]⟩
  have hzc : ∀ x : X, z * x = x * z := fun x =>
    Subtype.ext (Prod.ext (by simp [z]) (hζcomm x.1.2))
  have hz2 : z * z = 1 := Subtype.ext (Prod.ext (one_mul 1) hζ2)
  have hzne : z ≠ 1 := fun h => hζne (congrArg (fun x : X => x.1.2) h)
  have hkerψ : ψ.ker = Subgroup.zpowers z := by
    ext x
    constructor
    · intro hx
      have hx1 : x.1.1 = 1 := hx
      have hmem : x.1.2 ∈ π.ker := by
        rw [MonoidHom.mem_ker, ← (show theta x.1.1 = π x.1.2 from x.2), hx1, map_one]
      rw [hker] at hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · simp [z, hx1]
      · simp [z, hk]
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      show ((z ^ k : X) : SM24 × C).1 = 1
      simp [z]
  have := perfect_PM24
  obtain ⟨hcomm, hsq⟩ := preV_comm_and_sq noPerfectDoubleCover_M24 rho ψ (gen 0) (gen 1) Amat Bmat
    rho_gen0 rho_gen1 hC_proof hl_proof hψ hzc hz2 hzne hkerψ
  have hmem : ∀ a : C, π a ∈ epsHom.range → ∃ t : preV rho ψ, t.1.1.2 = a := by
    rintro a ⟨x, hx⟩
    refine ⟨⟨⟨(inl x, a), ?_⟩, ?_⟩, rfl⟩
    · show theta (inl x) = π a
      rw [theta_inl, hx]
    · show rightHom (inl x : SM24) = 1
      rw [rightHom_inl]
  refine ⟨fun a b ha hb => ?_, fun a ha => ?_⟩
  · obtain ⟨t, rfl⟩ := hmem a ha
    obtain ⟨u, rfl⟩ := hmem b hb
    exact congrArg (fun w : preV rho ψ => w.1.1.2) (hcomm t u)
  · obtain ⟨t, rfl⟩ := hmem a ha
    exact congrArg (fun w : preV rho ψ => w.1.1.2) (hsq t)

end CFSG.EvenSporadicStandard.TwoCo1
