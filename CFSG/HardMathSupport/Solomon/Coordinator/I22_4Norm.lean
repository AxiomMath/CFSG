module

public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Tactic.Group

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement

variable {Ω : Type*} [Group Ω]

theorem i224_exists_norm [Finite Ω] (L R : Subgroup Ω)
    (hcomm : ∀ g ∈ R, ∀ g' ∈ R, g ≠ g' → ∀ x ∈ L, ∀ y ∈ L,
      (g * x * g⁻¹) * (g' * y * g'⁻¹) = (g' * y * g'⁻¹) * (g * x * g⁻¹)) :
    ∃ N : ↥L →* Ω,
      (∀ x, N x ∈ ⨆ g ∈ R, L.map (MulAut.conj g).toMonoidHom) ∧
      (∀ r ∈ R, ∀ x, r * N x * r⁻¹ = N x) ∧
      (∀ (f : Ω) (hf : f ∈ Subgroup.normalizer (L : Set Ω)), (∀ g ∈ R, f * g = g * f) →
        ∀ x : ↥L, f * N x * f⁻¹ = N (L.normalizerMonoidHom ⟨f, hf⟩ x)) ∧
      (∀ g₀ ∈ R, ∀ x : ↥L, ∃ z : Ω,
        (∀ y ∈ L, (g₀ * y * g₀⁻¹) * z = z * (g₀ * y * g₀⁻¹)) ∧
          (N x : Ω) = (g₀ * (x : Ω) * g₀⁻¹) * z) ∧
      (∀ Y : Subgroup Ω, (∀ g ∈ R, ∀ y ∈ Y, ∀ u ∈ L, y * (g * u * g⁻¹) = (g * u * g⁻¹) * y) →
        ∀ x : ↥L, ∀ y ∈ Y, y * N x = N x * y) := by
  classical
  haveI : Finite ↥R := inferInstance
  haveI : Fintype ↥R := Fintype.ofFinite _
  let ϕ : ↥R → (↥L →* Ω) := fun g => (MulAut.conj (g : Ω)).toMonoidHom.comp L.subtype
  have hϕ : ∀ (g : ↥R) (x : ↥L), ϕ g x = (g : Ω) * x * (g : Ω)⁻¹ := fun _ _ => rfl
  have hc : Pairwise fun i j : ↥R => ∀ x y, Commute (ϕ i x) (ϕ j y) := fun i j hij x y => by
    rw [hϕ, hϕ]
    exact hcomm i i.2 j j.2 (fun h => hij (Subtype.ext h)) x x.2 y y.2
  let Φ : (↥R → ↥L) →* Ω := MonoidHom.noncommPiCoprod ϕ hc
  let δ : ↥L →* (↥R → ↥L) :=
    { toFun := fun x _ => x
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hδ : ∀ (x : ↥L) (g : ↥R), δ x g = x := fun _ _ => rfl
  have hΦmul : ∀ (g : ↥R) (y : ↥L), Φ (Pi.mulSingle g y) = ϕ g y := fun g y =>
    MonoidHom.noncommPiCoprod_mulSingle ϕ g y
  refine ⟨Φ.comp δ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have h1 : Φ (δ x) ∈ Φ.range := ⟨_, rfl⟩
    rw [MonoidHom.noncommPiCoprod_range] at h1
    have hle : (⨆ i : ↥R, (ϕ i).range) ≤ ⨆ g ∈ R, L.map (MulAut.conj g).toMonoidHom := by
      refine iSup_le fun g => ?_
      refine le_iSup₂_of_le (g : Ω) g.2 ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    exact hle h1
  · intro r hr x
    let σ : ↥R → ↥R := fun g => ⟨r⁻¹ * g, R.mul_mem (R.inv_mem hr) g.2⟩
    let T : (↥R → ↥L) →* (↥R → ↥L) :=
      { toFun := fun v g => v (σ g)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hT : ∀ (i : ↥R) (y : ↥L),
        T (Pi.mulSingle i y) = Pi.mulSingle ⟨r * i, R.mul_mem hr i.2⟩ y := by
      intro i y
      funext g
      have hiff : σ g = i ↔ g = ⟨r * i, R.mul_mem hr i.2⟩ := by
        constructor
        · intro h
          apply Subtype.ext
          have := congrArg Subtype.val h
          simp only [σ] at this
          show (g : Ω) = r * i
          rw [← this]
          group
        · intro h
          subst h
          apply Subtype.ext
          simp [σ]
      show (Pi.mulSingle i y : ↥R → ↥L) (σ g) = _
      simp only [Pi.mulSingle_apply, hiff]
    have hmain : (MulAut.conj r).toMonoidHom.comp Φ = Φ.comp T := by
      refine MonoidHom.pi_ext fun i y => ?_
      simp only [MonoidHom.comp_apply, hΦmul, hT]
      show r * (ϕ i y) * r⁻¹ = ϕ ⟨r * i, _⟩ y
      rw [hϕ, hϕ]
      simp only [Subgroup.coe_mul, mul_inv_rev]
      group
    have hTδ : T (δ x) = δ x := rfl
    have := congrArg (fun F => F (δ x)) hmain
    simp only [MonoidHom.comp_apply, hTδ] at this
    exact this
  · intro f hf hfR x
    let σ : ↥L →* ↥L := (L.normalizerMonoidHom ⟨f, hf⟩).toMonoidHom
    let S : (↥R → ↥L) →* (↥R → ↥L) :=
      { toFun := fun v g => σ (v g)
        map_one' := by funext g; simp
        map_mul' := fun a b => by funext g; simp }
    have hS : ∀ (i : ↥R) (y : ↥L), S (Pi.mulSingle i y) = Pi.mulSingle i (σ y) := by
      intro i y
      funext g
      show σ ((Pi.mulSingle i y : ↥R → ↥L) g) = _
      by_cases h : g = i
      · subst h
        simp
      · simp [Pi.mulSingle_apply, h]
    have hmain : (MulAut.conj f).toMonoidHom.comp Φ = Φ.comp S := by
      refine MonoidHom.pi_ext fun i y => ?_
      simp only [MonoidHom.comp_apply, hΦmul, hS]
      show f * (ϕ i y) * f⁻¹ = ϕ i (σ y)
      rw [hϕ, hϕ]
      have hσ : ((σ y : ↥L) : Ω) = f * (y : Ω) * f⁻¹ := rfl
      rw [hσ]
      have := hfR i i.2
      calc f * ((i : Ω) * y * (i : Ω)⁻¹) * f⁻¹
          = (f * i) * y * (f * i)⁻¹ := by group
        _ = (i * f) * y * (i * f)⁻¹ := by rw [this]
        _ = (i : Ω) * (f * y * f⁻¹) * (i : Ω)⁻¹ := by group
    have hSδ : S (δ x) = δ (σ x) := rfl
    have := congrArg (fun F => F (δ x)) hmain
    simp only [MonoidHom.comp_apply, hSδ] at this
    exact this
  · intro g₀ hg₀ x
    let one : ↥R := ⟨g₀, hg₀⟩
    let w : ↥R → ↥L := fun g => if g = one then 1 else x
    have hdec : δ x = Pi.mulSingle one x * w := by
      funext g
      by_cases h : g = one
      · subst h
        simp [w, hδ]
      · simp [w, h, hδ, Pi.mulSingle_apply]
    refine ⟨Φ w, ?_, ?_⟩
    · intro y hy
      have hcomm' : ∀ i : ↥R, Commute (g₀ * y * g₀⁻¹) (ϕ i (w i)) := by
        intro i
        by_cases hi : i = one
        · subst hi
          simp [w]
        · have hw : w i = x := by simp [w, hi]
          rw [hw, hϕ]
          have hne : g₀ ≠ (i : Ω) := fun h => hi (Subtype.ext h.symm)
          exact hcomm g₀ hg₀ i i.2 hne y hy x x.2
      have hind : Commute (g₀ * y * g₀⁻¹) (Φ w) := by
        show Commute _ (MonoidHom.noncommPiCoprod ϕ hc w)
        rw [MonoidHom.noncommPiCoprod_apply]
        refine Finset.noncommProd_induction _ _ _ (fun m => Commute (g₀ * y * g₀⁻¹) m)
          (fun a b ha hb => ha.mul_right hb) (Commute.one_right _) (fun i _ => hcomm' i)
      exact hind.eq
    · have : (Φ (δ x) : Ω) = Φ (Pi.mulSingle one x) * Φ w := by
        rw [hdec, map_mul]
      show Φ (δ x) = _
      rw [this, hΦmul, hϕ]
  · intro Y hY x y hy
    have hh : Commute y (MonoidHom.noncommPiCoprod ϕ hc (δ x)) :=
      MonoidHom.commute_noncommPiCoprod ϕ (hcomm := hc) (m := y) (fun i t => by
        rw [hϕ]
        exact hY i i.2 y hy t t.2) (δ x)
    exact hh.eq

end CFSG.HardMathSupport.Solomon.Coordinator
