module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0A5Eq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0LiftIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FLTw

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Co

open Matrix

variable {A : Type*} [Group A]

@[expose] def ActsAs4 (e : A ≃* Multiplicative (Fin 4 → ZMod 4)) (h : MulAut A)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 4)) : Prop :=
  ∀ b : A, Multiplicative.toAdd (e (h b)) = M *ᵥ Multiplicative.toAdd (e b)

theorem ActsAs4.matrix_eq {e : A ≃* Multiplicative (Fin 4 → ZMod 4)} {h : MulAut A}
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 4)} (hh : ActsAs4 e h M) (hh' : ActsAs4 e h M') :
    M = M' := by
  have hv : ∀ v : Fin 4 → ZMod 4, M *ᵥ v = M' *ᵥ v := by
    intro v
    obtain ⟨b, hb⟩ := e.surjective (Multiplicative.ofAdd v)
    have hb' : Multiplicative.toAdd (e b) = v := by rw [hb]; rfl
    rw [← hb', ← hh b, ← hh' b]
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hv v)

theorem ActsAs4.mul {e : A ≃* Multiplicative (Fin 4 → ZMod 4)} {h h' : MulAut A}
    {M M' : Matrix (Fin 4) (Fin 4) (ZMod 4)} (hh : ActsAs4 e h M) (hh' : ActsAs4 e h' M') :
    ActsAs4 e (h * h') (M * M') := by
  intro b
  rw [MulAut.mul_apply, hh, hh', Matrix.mulVec_mulVec]

theorem actsAs4_one (e : A ≃* Multiplicative (Fin 4 → ZMod 4)) : ActsAs4 e (1 : MulAut A) 1 := by
  intro b
  simp

theorem exists_actsAs4 (e : A ≃* Multiplicative (Fin 4 → ZMod 4)) (h : MulAut A) :
    ∃ M : Matrix (Fin 4) (Fin 4) (ZMod 4), ActsAs4 e h M := by
  let f : (Fin 4 → ZMod 4) →+ (Fin 4 → ZMod 4) :=
    AddMonoidHom.mk' (fun v => Multiplicative.toAdd (e (h (e.symm (Multiplicative.ofAdd v)))))
      (fun v w => by simp)
  refine ⟨LinearMap.toMatrix' (f.toZModLinearMap 4), fun b => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [f]

end T84Co

theorem sec8t84FactLift_of_cert : Sec8T84FactLift := by
  intro G _ U hcomm hcard h4 hsq H hH hinv
  haveI : Finite ↥U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with
      mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  have h4' : ∀ x : ↥U, x ^ 4 = 1 := fun x => Subtype.ext (by simpa using h4 x x.2)
  have hcl : Subgroup.closure {u : G | ∃ x ∈ U, u = x * x} =
      (powMonoidHom 2 : ↥U →* ↥U).range.map U.subtype := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro u ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩ ^ 2, ⟨⟨x, hx⟩, rfl⟩, by simp [sq]⟩
    · rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
      exact Subgroup.subset_closure ⟨z, z.2, by simp [sq]⟩
  have hsq' : Nat.card (powMonoidHom 2 : ↥U →* ↥U).range = 16 := by
    rw [← hsq, hcl, Subgroup.card_map_of_injective U.subtype_injective]
  obtain ⟨e⟩ := T84Co.exists_mulEquiv_zmod4 h4' hcard hsq'
  obtain ⟨ι⟩ := hH
  let Φ : alternatingGroup (Fin 5) →* MulAut ↥U := H.subtype.comp ι.symm.toMonoidHom
  choose M hM using fun γ => T84Co.exists_actsAs4 e (Φ γ)
  let ρ : alternatingGroup (Fin 5) →* FL.M4 :=
    { toFun := M
      map_one' := by
        refine (hM 1).matrix_eq ?_
        rw [map_one]
        exact T84Co.actsAs4_one e
      map_mul' := fun γ γ' => by
        refine (hM (γ * γ')).matrix_eq ?_
        rw [map_mul]
        exact (hM γ).mul (hM γ') }
  have key : ∀ u : Certificates.A5GL42.Vec4, u ≠ 0 →
      ((e.symm (Multiplicative.ofAdd (FL.twice u)) : ↥U) : G) *
        (e.symm (Multiplicative.ofAdd (FL.twice u)) : ↥U) = 1 ∧
      e.symm (Multiplicative.ofAdd (FL.twice u)) ≠ 1 := by
    intro u hu
    refine ⟨?_, ?_⟩
    · have h2 : FL.twice u + FL.twice u = 0 := by
        funext i
        have : ∀ c : ZMod 4, 2 * c + 2 * c = 0 := by decide
        exact this _
      have h3 : e.symm (Multiplicative.ofAdd (FL.twice u)) *
          e.symm (Multiplicative.ofAdd (FL.twice u)) = 1 := by
        rw [← map_mul, ← ofAdd_add, h2]
        exact map_one _
      exact congrArg Subtype.val h3
    · intro h1
      apply FL.twice_ne_zero hu
      have h2 := congrArg (fun x => Multiplicative.toAdd (e x)) h1
      simpa using h2
  refine FL.no_lift_hom T84Co.a5a T84Co.a5b (by rw [pow_two]; exact T84Co.a5a_sq)
    T84Co.a5b_cube T84Co.a5ab_pow T84Co.closure_a5ab ρ ?_
  intro v w hv hw
  obtain ⟨h, hhH, hhxy⟩ := hinv _ (key v hv).1 (key v hv).2 _ (key w hw).1 (key w hw).2
  obtain ⟨γ, hγ⟩ : ∃ γ : alternatingGroup (Fin 5), Φ γ = h := ⟨ι ⟨h, hhH⟩, by simp [Φ]⟩
  refine ⟨γ, ?_⟩
  apply FL.twice_injective
  rw [← FL.mulVec_twice]
  have h1 := hM γ (e.symm (Multiplicative.ofAdd (FL.twice v)))
  rw [hγ, hhxy] at h1
  have h2 : (M γ).mulVec (FL.twice v) = FL.twice w := by simpa using h1.symm
  exact h2

end CFSG.OddStandard.SmallF3.Omega
