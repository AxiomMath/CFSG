module

public import CFSG.LieType.SemisimpleCentralizers.HeldLangSL
public import CFSG.Open.StatedCenterThree
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.LieType.SemisimpleCentralizers.HeldLang

open Matrix CFSG.LieType.Universal.Unitary CFSG.Open

variable {F : Type} [Field F] {N : ℕ}

@[expose] def diagGL {N : ℕ} (t : Fin N → Fˣ) : GL (Fin N) F :=
  ⟨Matrix.diagonal fun i => (t i : F), Matrix.diagonal fun i => (((t i)⁻¹ : Fˣ) : F),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩

theorem coe_diagGL {N : ℕ} (t : Fin N → Fˣ) :
    ((diagGL t : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = Matrix.diagonal fun i => (t i : F) := rfl

theorem diagGL_mul {N : ℕ} (t s : Fin N → Fˣ) : diagGL (t * s) = diagGL t * diagGL s :=
  Units.ext (by simp [coe_diagGL, diagonal_mul_diagonal])

theorem diagGL_one {N : ℕ} : diagGL (1 : Fin N → Fˣ) = (1 : GL (Fin N) F) :=
  Units.ext (by simp [coe_diagGL])

theorem diagGL_injective {N : ℕ} : Function.Injective (diagGL (F := F) (N := N)) := by
  intro t s h
  funext i
  have := congrFun (congrFun (congrArg (fun z : GL (Fin N) F => (z : Matrix (Fin N) (Fin N) F)) h) i) i
  exact Units.ext (by simpa [coe_diagGL] using this)

theorem exists_torus3_of_mem [Finite F] (H : Subgroup (GL (Fin N) F)) (h3 : 3 ∣ Nat.card F - 1)
    (hN : 1 ≤ N)
    (hmem : ∀ t : Fin N → Fˣ, (∀ i, t i ^ 3 = 1) → ∏ i, t i = 1 → diagGL t ∈ H) :
    ∃ D : Subgroup H, IsElemAbelian 3 D ∧ Nat.card D = 3 ^ (N - 1) := by
  classical
  let μ : Subgroup Fˣ := rootsOfUnity 3 F
  have hμcard : Nat.card μ = 3 := CFSG.Open.StatedCenterThree.card_rootsOfUnity_three h3
  have hμ3 : ∀ z : μ, z ^ 3 = 1 := fun z => Subtype.ext ((mem_rootsOfUnity 3 _).1 z.2)
  let prod : (Fin N → μ) →* μ :=
    { toFun := fun t => ∏ i, t i
      map_one' := by simp
      map_mul' := fun a b => by simp [Finset.prod_mul_distrib] }
  let T : Subgroup (Fin N → μ) := prod.ker
  let ψ : (Fin N → μ) →* GL (Fin N) F :=
    { toFun := fun t => diagGL fun i => (t i : Fˣ)
      map_one' := by
        rw [← diagGL_one]
        rfl
      map_mul' := fun a b => by
        rw [← diagGL_mul]
        rfl }
  have hψmem : ∀ t ∈ T, ψ t ∈ H := by
    intro t ht
    have ht1 : ∏ i, t i = 1 := ht
    refine hmem _ (fun i => (mem_rootsOfUnity 3 _).1 (t i).2) ?_
    have := congrArg (fun z : μ => (z : Fˣ)) ht1
    simpa [map_prod μ.subtype t Finset.univ] using this
  let ψ' : T →* H := (ψ.comp T.subtype).codRestrict H fun t => hψmem t t.2
  have hψ'inj : Function.Injective ψ' := by
    intro a b hab
    have h1 : ψ (a : Fin N → μ) = ψ (b : Fin N → μ) :=
      congrArg (fun z : H => (z : GL (Fin N) F)) hab
    have h2 := diagGL_injective h1
    exact Subtype.ext (funext fun i => Subtype.ext (congrFun h2 i))
  have hTcard : Nat.card T = 3 ^ (N - 1) := by
    have h1 := Subgroup.card_ker_mul_card_range prod
    have hrange : prod.range = ⊤ := by
      rw [eq_top_iff]
      intro z _
      refine ⟨Pi.mulSingle ⟨0, by omega⟩ z, ?_⟩
      show ∏ i, (Pi.mulSingle (⟨0, by omega⟩ : Fin N) z : Fin N → μ) i = z
      rw [Finset.prod_pi_mulSingle']
      simp
    have h2 : Nat.card (Fin N → μ) = 3 ^ N := by
      rw [Nat.card_fun, hμcard, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hrange, Subgroup.card_top, hμcard, h2] at h1
    have h3' : 3 ^ N = 3 ^ (N - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h3'] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  refine ⟨ψ'.range, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    apply Subtype.ext
    show ψ' a * ψ' b = ψ' b * ψ' a
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    funext i
    exact mul_comm _ _
  · rintro x ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (funext fun i => by simpa using hμ3 ((a : Fin N → μ) i))
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hψ'inj).toEquiv.symm, hTcard]

theorem exists_torus3 [Finite F] {bar₀ : F ≃+* F} (hbar : ∀ t : F, t ^ 3 = 1 → bar₀ t * t = 1)
    (h3 : 3 ∣ Nat.card F - 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ D : Subgroup (SUid bar₀ N), IsElemAbelian 3 D ∧ Nat.card D = 3 ^ (N - 1) := by
  refine exists_torus3_of_mem (SUid bar₀ N) h3 hN fun t ht hprod => mem_SUid.2 ⟨?_, ?_⟩
  · show (Matrix.diagonal fun i => (t i : F)).det = 1
    rw [det_diagonal]
    have := congrArg (fun z : Fˣ => (z : F)) hprod
    simpa [Units.coe_prod] using this
  · show conjTr bar₀ (Matrix.diagonal fun i => (t i : F)) * Matrix.diagonal (fun i => (t i : F)) = 1
    have hcube : ∀ i, (t i : F) ^ 3 = 1 := fun i => by
      have := congrArg (fun z : Fˣ => (z : F)) (ht i)
      simpa using this
    have : conjTr bar₀ (Matrix.diagonal fun i => (t i : F)) =
        Matrix.diagonal fun i => bar₀ (t i : F) := by
      rw [conjTr, diagonal_map (map_zero bar₀), diagonal_transpose]
    rw [this, diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hbar _ (hcube i)]
    · simp [hij]

theorem exists_torus3_sl [Finite F] (h3 : 3 ∣ Nat.card F - 1) {N : ℕ} (hN : 1 ≤ N) :
    ∃ D : Subgroup (slGL (Fin N) F), IsElemAbelian 3 D ∧ Nat.card D = 3 ^ (N - 1) := by
  refine exists_torus3_of_mem (slGL (Fin N) F) h3 hN fun t _ hprod => mem_slGL.2 ?_
  show (Matrix.diagonal fun i => (t i : F)).det = 1
  rw [det_diagonal]
  have := congrArg (fun z : Fˣ => (z : F)) hprod
  simpa [Units.coe_prod] using this

end CFSG.LieType.SemisimpleCentralizers.HeldLang
