module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOffenderNat

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups Matrix

section Unit

variable {F : Type*} [Field F] [Fintype F] [CharP F 2]

theorem unit_fix_e0_two_power (τ : (AddMonoid.End (Fin 2 → F))ˣ)
    (hN : τ ∈ Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ))
    (hfix : ∀ c : F, τ.val (Pi.single 0 c) = Pi.single 0 c) {k : ℕ} (hk : τ ^ (2 ^ k) = 1) :
    ∃ b : F, τ = natEnd F (uElt b) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, σ, rfl⟩ := exists_semilin_of_mem_normalizer τ hN
  have hsig : ∀ c : F, (fun i : Fin 2 => σ ((Pi.single 0 c : Fin 2 → F) i)) =
      Pi.single 0 (σ c) := by
    intro c
    funext i
    fin_cases i <;> simp
  have h0 : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) 0 0 * σ c = c := fun c => by
    have := congrFun (hfix c) 0
    rw [semilin_apply, hsig] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have h1 : ∀ c : F, (g : Matrix (Fin 2) (Fin 2) F) 1 0 * σ c = 0 := fun c => by
    have := congrFun (hfix c) 1
    rw [semilin_apply, hsig] at this
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hg00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by simpa using h0 1
  have hg10 : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by simpa using h1 1
  have hσ : σ = 1 := by
    ext c
    have := h0 c
    rw [hg00, one_mul] at this
    exact this
  subst hσ
  have hsec : ∀ (m : ℕ) (v : Fin 2 → F),
      (((semilin g 1) ^ m).val v) 1 = ((g : Matrix (Fin 2) (Fin 2) F) 1 1) ^ m * v 1 := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Units.val_mul]
      show (((semilin g 1) ^ m).val ((semilin g 1).val v)) 1 = _
      rw [ih, semilin_apply]
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hg10, pow_succ]
      ring
  have hd : ((g : Matrix (Fin 2) (Fin 2) F) 1 1) ^ (2 ^ k) = 1 := by
    have h := congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val (Pi.single 1 1) 1) hk
    simp only [hsec] at h
    simpa using h
  have hd0 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := fun h => by
    rw [h, zero_pow (by positivity)] at hd
    exact zero_ne_one hd
  have hd1 : (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    let dU : Fˣ := Units.mk0 _ hd0
    have hdU : dU ^ (2 ^ k) = 1 := Units.ext hd
    have hord : orderOf dU ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hdU
    have hord2 : orderOf dU ∣ Nat.card Fˣ := orderOf_dvd_natCard dU
    have hcop : Nat.Coprime (orderOf dU) (Nat.card Fˣ) :=
      Nat.Coprime.coprime_dvd_left hord (Nat.Coprime.pow_left k coprime_card_units)
    have : orderOf dU = 1 := Nat.Coprime.eq_one_of_dvd hcop hord2
    have := orderOf_eq_one_iff.mp this
    exact congrArg Units.val this
  refine ⟨(g : Matrix (Fin 2) (Fin 2) F) 0 1, Units.ext (AddMonoidHom.ext fun v => ?_)⟩
  show (semilin g 1).val v = (natEnd F (uElt ((g : Matrix (Fin 2) (Fin 2) F) 0 1))).val v
  rw [semilin_apply, natEnd_val, natEndHom_apply, coe_uElt]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hg00, hg10, hd1]

end Unit

section Element

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] {W : Type*} [AddCommGroup W]
  [Module (ZMod 2) W] {X : Type*} [Group X]

theorem exists_element_of_fix_line (φ : X →* (W ≃ₗ[ZMod 2] W)) (β : W ≃+ (Fin 2 → F))
    (Ls As Es : Subgroup X) (x : SL(2, F))
    (hLs : ∀ g : SL(2, F), ∃ l ∈ Ls, conjEnd β (φ l) = natEndHom F g)
    (hLs' : ∀ l ∈ Ls, ∃ g : SL(2, F), conjEnd β (φ l) = natEndHom F g)
    (hAs : ∀ g : SL(2, F), (∃ a ∈ As, conjEnd β (φ a) = natEndHom F g) ↔
      x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range)
    (hEn : ∀ e ∈ Es, ∀ l ∈ Ls, e * l * e⁻¹ ∈ Ls)
    {e : X} (he : e ∈ Es) {k : ℕ} (hek : e ^ (2 ^ k) = 1)
    (hfix : ∀ v ∈ rootLine x, conjEnd β (φ e) v = v) : ∃ a ∈ As, φ e = φ a := by
  let Ψ : X →* (AddMonoid.End (Fin 2 → F))ˣ := ((conjEnd β).comp φ).toHomUnits
  have hΨval : ∀ y, (Ψ y).val = conjEnd β (φ y) := fun y => rfl
  have hΨnat : ∀ y g, conjEnd β (φ y) = natEndHom F g → Ψ y = natEnd F g := fun y g h =>
    Units.ext (by rw [hΨval, natEnd_val]; exact h)
  have hfwd : ∀ e' ∈ Es, ∀ h ∈ (natEnd F).range, Ψ e' * h * (Ψ e')⁻¹ ∈ (natEnd F).range := by
    intro e' he' h hh
    obtain ⟨g, rfl⟩ := hh
    obtain ⟨l, hl, hlg⟩ := hLs g
    obtain ⟨g', hg'⟩ := hLs' _ (hEn e' he' l hl)
    refine ⟨g', ?_⟩
    rw [← hΨnat _ _ hg', ← hΨnat _ _ hlg, map_mul, map_mul, map_inv]
  have hnorm : Ψ e ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hfwd e he h
    · intro hh
      have h2 := hfwd e⁻¹ (Es.inv_mem he) _ hh
      rw [map_inv, inv_inv] at h2
      have e3 : (Ψ e)⁻¹ * (Ψ e * h * (Ψ e)⁻¹) * Ψ e = h := by group
      rw [e3] at h2
      exact h2
  set a : (AddMonoid.End (Fin 2 → F))ˣ := natEnd F x with ha
  have hnormrange : ∀ y : SL(2, F), natEnd F y ∈
      Subgroup.normalizer ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := fun y =>
    Subgroup.le_normalizer ⟨y, rfl⟩
  set τ : (AddMonoid.End (Fin 2 → F))ˣ := a⁻¹ * Ψ e * a with hτ
  have hτN : τ ∈ Subgroup.normalizer
      ((natEnd F).range : Set (AddMonoid.End (Fin 2 → F))ˣ) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ hnorm) (hnormrange x)
    exact Subgroup.inv_mem _ (hnormrange x)
  have haE : ∀ c : F, a.val (Pi.single 0 c) = c • (x • (Pi.single 0 1 : Fin 2 → F)) := by
    intro c
    have e : (Pi.single 0 c : Fin 2 → F) = c • (Pi.single 0 1 : Fin 2 → F) := by
      ext i
      fin_cases i <;> simp
    rw [ha, natEnd_val, natEndHom_apply, e, Matrix.mulVec_smul, smul_eq_mulVec']
  have hτfix : ∀ c : F, τ.val (Pi.single 0 c) = Pi.single 0 c := by
    intro c
    have h1 : (Ψ e).val (a.val (Pi.single 0 c)) = a.val (Pi.single 0 c) := by
      rw [haE c, hΨval]
      exact hfix _ (Submodule.smul_mem _ _ (smul_single_mem_rootLine x))
    have h2 : τ.val (Pi.single 0 c) = (a⁻¹).val ((Ψ e).val (a.val (Pi.single 0 c))) := rfl
    rw [h2, h1]
    exact congrArg (fun u : (AddMonoid.End (Fin 2 → F))ˣ => u.val (Pi.single 0 c))
      (inv_mul_cancel a)
  have hτ2 : τ ^ (2 ^ k) = 1 := by
    have h1 : τ = a⁻¹ * Ψ e * (a⁻¹)⁻¹ := by rw [hτ, inv_inv]
    rw [h1, conj_pow, ← map_pow, hek, map_one]
    group
  obtain ⟨b, hb⟩ := unit_fix_e0_two_power τ hτN hτfix hτ2
  set g : SL(2, F) := x * uElt b * x⁻¹ with hg
  have hgr : x⁻¹ * g * x ∈ (upperUnipotent (F := F)).range :=
    (mem_rootGroup_iff _).mpr ⟨b, by rw [hg]; group⟩
  obtain ⟨a', ha', hag⟩ := (hAs g).2 hgr
  refine ⟨a', ha', conjEnd_injective β ?_⟩
  have h3 : Ψ e = natEnd F g := by
    have h2 : Ψ e = a * τ * a⁻¹ := by rw [hτ]; group
    rw [h2, hb, hg, map_mul, map_mul, map_inv, ha]
  have h1 : conjEnd β (φ e) = natEndHom F g := by
    rw [← hΨval, h3, natEnd_val]
  rw [h1, hag]

end Element

end CFSG.QuasithinUnique.Setup.Lift
