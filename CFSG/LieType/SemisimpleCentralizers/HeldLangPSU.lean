module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangSU
public import CFSG.Open.StatedDefs
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.HardMathSupport.Foote.ModuleExclusions CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.Open

variable {K : Type} [Field K] {d : ℕ} {bar σ : K ≃+* K}

theorem glFixEmb_scalar (σ : K ≃+* K) (c : (fixField σ)ˣ) :
    glFixEmb σ (Matrix.GeneralLinearGroup.scalar (Fin d) c) =
      Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (fixField σ).subtype.toMonoidHom c) := by
  apply Units.ext
  ext i j
  rw [glFixEmb_apply]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mem_scalars_of_glFixEmb [NeZero d] (x₀ : GL (Fin d) (fixField σ)) (c : Kˣ)
    (h : glFixEmb σ x₀ = Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    x₀ ∈ (Matrix.GeneralLinearGroup.scalar (Fin d) : (fixField σ)ˣ →* GL (Fin d) (fixField σ)).range := by
  have hent : ∀ i j, ((x₀ i j : fixField σ) : K) = if i = j then (c : K) else 0 := fun i j => by
    have := congrFun (congrFun (congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) h) i) j
    rw [glFixEmb_apply] at this
    rw [this]
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  have hdiag : ∀ i, x₀ i i = x₀ 0 0 := fun i => Subtype.ext (by rw [hent, hent]; simp)
  have hscal : (x₀ : Matrix (Fin d) (Fin d) (fixField σ)) ∈ Set.range (Matrix.scalar (Fin d)) := by
    refine ⟨x₀ 0 0, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply, hdiag]
    · rw [hent]
      simp [Matrix.scalar_apply, hij]
  have hcen := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 hscal
  rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen

theorem suScalars_le_center (S : Subgroup (GL (Fin d) K)) :
    (StatedScalars (Fin d) K).subgroupOf S ≤ Subgroup.center S := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hx' : (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Subgroup.mem_subgroupOf.1 hx
  exact Subtype.ext (Subgroup.mem_center_iff.1 hx' y)

@[expose] def suFixEmb (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hbb : ∀ x, bar (bar x) = x)
    (u : GL (Fin d) K) (hu : IsIso bar u) : SUid (barFix σ bar hcomm hbb) d →* SUid bar d where
  toFun x₀ := ⟨u⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * u, by
    have h1 : glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) ∈ SUid bar d :=
      (Subgroup.mem_inf.1 ((mem_SUid_inf_glFix_iff hcomm hbb).2 ⟨x₀, rfl⟩)).1
    have := conj_mem_SUid hbb (hu.inv hbb) h1
    rwa [inv_inv] at this⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul, map_mul]; group)

theorem exists_psu_fix {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hodd : Odd (orderOf σ))
    [NeZero d] (A : GL (Fin d) K) (hA : IsIso bar A) {c : K}
    (hc : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (β' : StatedProj (SUid bar d) →* StatedProj (SUid bar d))
    (hβ' : ∀ x x' : SUid bar d, (x' : GL (Fin d) K) = A * glMap σ x * A⁻¹ →
      β' (x : StatedProj (SUid bar d)) = x') :
    ∃ Y : Subgroup (StatedProj (SUid bar d)), Y ≤ fixHom β' ∧ (Y.subgroupOf (fixHom β')).Normal ∧
      ⁅fixHom β', fixHom β'⁆ ≤ Y ∧
      Nonempty (Y ≃* StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) := by
  obtain ⟨u, hu, -, hfix⟩ := exists_suTwist_fix hp he hK hbar hcomm hodd A hA hc
  set Z : Subgroup (SUid bar d) := (StatedScalars (Fin d) K).subgroupOf (SUid bar d) with hZdef
  set β := suTwist hcomm hbar.invol A hA with hβdef
  have hZc : Z ≤ Subgroup.center (SUid bar d) := suScalars_le_center _
  have hβ'' : ∀ x : SUid bar d,
      β' (x : StatedProj (SUid bar d)) = ((β x : SUid bar d) : StatedProj (SUid bar d)) :=
    fun x => hβ' x (β x) rfl
  refine ⟨(fixHom β).map (QuotientGroup.mk' Z), ?_, map_fixHom_normal β hZc β' hβ'',
    commutator_fixHom_le β hZc β' hβ'', ?_⟩
  · rw [fix_quot_eq_map β hZc β' hβ'']
    exact Subgroup.map_mono (fixHom_le_twistedFix β Z hZc)
  · let Φ := suFixEmb hcomm hbar.invol u hu
    let Z₀ : Subgroup (SUid (barFix σ bar hcomm hbar.invol) d) :=
      (StatedScalars (Fin d) (fixField σ)).subgroupOf _
    have hΦZ : Z₀ ≤ Z.comap Φ := by
      intro x₀ hx₀
      obtain ⟨c₀, hc₀⟩ := Subgroup.mem_subgroupOf.1 hx₀
      rw [Subgroup.mem_comap, hZdef, Subgroup.mem_subgroupOf]
      refine ⟨Units.map (fixField σ).subtype.toMonoidHom c₀, ?_⟩
      show Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map (fixField σ).subtype.toMonoidHom c₀) =
        u⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * u
      rw [← hc₀, glFixEmb_scalar, ← scalar_mul_comm _ u⁻¹]
      group
    let Ψ : StatedProj (SUid (barFix σ bar hcomm hbar.invol) d) →* StatedProj (SUid bar d) :=
      QuotientGroup.map Z₀ Z Φ hΦZ
    have hΨmk : ∀ x₀ : SUid (barFix σ bar hcomm hbar.invol) d,
        Ψ (x₀ : StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) = ((Φ x₀ : SUid bar d) : StatedProj (SUid bar d)) :=
      fun x₀ => QuotientGroup.map_mk _ _ _ _ x₀
    have hΨinj : Function.Injective Ψ := by
      rw [injective_iff_map_eq_one]
      intro a ha
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective a
      rw [hΨmk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
      obtain ⟨c, hcs⟩ := ha
      rw [QuotientGroup.eq_one_iff]
      show (x₀ : GL (Fin d) (fixField σ)) ∈ StatedScalars (Fin d) (fixField σ)
      refine mem_scalars_of_glFixEmb (x₀ : GL (Fin d) (fixField σ)) c ?_
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin d) c =
          u⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * u := hcs
      calc glFixEmb σ (x₀ : GL (Fin d) (fixField σ))
          = u * (u⁻¹ * glFixEmb σ (x₀ : GL (Fin d) (fixField σ)) * u) * u⁻¹ := by group
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
          rw [← h1, ← scalar_mul_comm c u]
          group
    have hrange : Ψ.range = (fixHom β).map (QuotientGroup.mk' Z) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective a
        refine ⟨Φ x₀, (hfix (Φ x₀)).2 ⟨x₀, rfl⟩, ?_⟩
        exact (hΨmk x₀).symm
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨x₀, hx₀⟩ := (hfix x).1 hx
        refine ⟨(x₀ : StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)), ?_⟩
        rw [hΨmk]
        have : Φ x₀ = x := Subtype.ext hx₀.symm
        rw [this]
        rfl
    exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hΨinj).symm⟩

theorem exists_psu_fix_of_eq {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hK : Nat.card K = p ^ e)
    (hbar : IsUnitaryInvolution bar) (hcomm : ∀ x, σ (bar x) = bar (σ x)) (hodd : Odd (orderOf σ))
    [NeZero d] (S : Subgroup (GL (Fin d) K)) (hS : S = SUid bar d) (A : GL (Fin d) K) (hA : IsIso bar A) {c : K}
    (hc : Ai σ (A : Matrix (Fin d) (Fin d) K) (orderOf σ) = c • (1 : Matrix (Fin d) (Fin d) K))
    (β' : StatedProj S →* StatedProj S)
    (hβ' : ∀ x x' : S, (x' : GL (Fin d) K) = A * glMap σ x * A⁻¹ → β' (x : StatedProj S) = x') :
    ∃ Y : Subgroup (StatedProj S), Y ≤ fixHom β' ∧ (Y.subgroupOf (fixHom β')).Normal ∧
      ⁅fixHom β', fixHom β'⁆ ≤ Y ∧
      Nonempty (Y ≃* StatedProj (SUid (barFix σ bar hcomm hbar.invol) d)) := by
  subst hS
  exact exists_psu_fix hp he hK hbar hcomm hodd A hA hc β' hβ'

end CFSG.LieType.SemisimpleCentralizers.HeldLang
