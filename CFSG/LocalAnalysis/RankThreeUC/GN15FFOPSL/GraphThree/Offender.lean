module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSL.GraphThree.Duality

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL

open scoped MatrixGroups Matrix

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.K1
  CFSG.QuasithinUnique.Setup.X7a

theorem sl3_graph_offender_false {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ f)
    {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    (ρ : Representation (ZMod 2) SL(3, F) Z) (hirr : ρ.IsIrreducible)
    (hker : ∀ x, ρ x = 1 → x ∈ scalars 3 F)
    {D : Type} [Group D] [Finite D] (δ : Representation (ZMod 2) D Z)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hnorm : ∀ d x, ∃ y, ∀ z, δ d (ρ x z) = ρ y (δ d z))
    (hgraph : ∃ d, ∃ (A : GL (Fin 3) F) (σ : F ≃+* F),
      ∀ x z, δ d (ρ x z) = ρ (CFSG.QuasithinUnique.K1.stdAut A σ 1 x) (δ d z))
    (hoff : Nat.card Z * Nat.card δ.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δ d z = z}) :
    False := by
  classical
  let δu : D →* (Z ≃ₗ[ZMod 2] Z) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Z).toMonoidHom.comp
      δ.asGroupHom
  let Aim : Subgroup (Z ≃ₗ[ZMod 2] Z) := δu.range
  have hδu_val : ∀ (d : D) (z : Z), (δu d) z = δ d z := by
    intro d z
    have h : ((δu d : Z ≃ₗ[ZMod 2] Z) : Z →ₗ[ZMod 2] Z) = δ d := by
      simp [δu, Representation.asGroupHom_apply]
    exact congrArg (fun e : Z →ₗ[ZMod 2] Z => e z) h
  obtain ⟨d₀, A₀, σ₀, hd₀⟩ := hgraph
  have hb₀ : ∀ x z, (δu d₀) (ρ x z) = ρ (CFSG.QuasithinUnique.K1.stdAut A₀ σ₀ 1 x)
      ((δu d₀) z) := by
    intro x z
    rw [hδu_val, hδu_val]
    exact hd₀ x z
  have hne : δu d₀ ≠ LinearEquiv.refl (ZMod 2) Z :=
    ne_refl_of_graph ρ hker (δu d₀) A₀ σ₀ hb₀
  have hA1 : Aim ≠ ⊥ := by
    intro hbot
    have hmem : δu d₀ ∈ Aim := ⟨d₀, rfl⟩
    rw [hbot] at hmem
    have hone : (1 : Z ≃ₗ[ZMod 2] Z) = LinearEquiv.refl (ZMod 2) Z := by
      ext z
      rfl
    exact hne (hmem.trans hone)
  have hA2 : ∀ a ∈ Aim, a * a = 1 := by
    rintro a ⟨d, rfl⟩
    apply LinearEquiv.ext
    intro z
    show (δu d) ((δu d) z) = z
    rw [hδu_val, hδu_val]
    have h := congrArg (fun e : Module.End (ZMod 2) Z => e z) (hD2 d)
    simpa [Module.End.mul_apply] using h
  have hcomm : ∀ a ∈ Aim, ∀ b ∈ Aim, a * b = b * a := by
    intro a ha b hb
    have hab : a * b ∈ Aim := Aim.mul_mem ha hb
    have hsq : (a * b) * (a * b) = 1 := hA2 (a * b) hab
    have haa : a * a = 1 := hA2 a ha
    have hbb : b * b = 1 := hA2 b hb
    calc a * b = (a * b)⁻¹ := (eq_inv_iff_mul_eq_one).mpr hsq
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right hbb, inv_eq_of_mul_eq_one_right haa]
  have hAel : CFSG.IsElementaryAbelian 2 Aim :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
        exact Subtype.ext (by simpa [pow_two] using hA2 (x : Z ≃ₗ[ZMod 2] Z) x.2) }
  have hsd : Nonempty (ρ.Equiv ρ.dual) :=
    nonempty_equiv_dual_of_graph (by omega) hF ρ hirr (δu d₀) A₀ σ₀ hb₀
  have hA : ∀ a ∈ Aim, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y := by
    rintro a ⟨d, rfl⟩ x
    obtain ⟨y, hy⟩ := hnorm d x
    exact ⟨y, fun z => by rw [hδu_val, hδu_val]; exact hy z⟩
  have hX := CFSG.QuasithinUnique.Setup.X7a.self_dual_full_normalizer_no_offender
    CFSG.QuasithinUnique.Setup.X7a.selfDualInvolutionRank hf hF ρ hker hirr hsd Aim hA1 hA
  have hfix : Nat.card {z : Z // ∀ a ∈ Aim, a z = z} =
      Nat.card {z : Z // ∀ d, δ d z = z} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun z => ?_)
    constructor
    · intro hz d
      rw [← hδu_val d z]
      exact hz (δu d) ⟨d, rfl⟩
    · intro hz a ha
      obtain ⟨d, rfl⟩ := ha
      rw [hδu_val]
      exact hz d
  have hkerEq : Nat.card δu.ker = Nat.card δ.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun d => ?_)
    simp only [MonoidHom.mem_ker]
    constructor
    · intro h
      ext z
      have hz := congrArg (fun e : Z ≃ₗ[ZMod 2] Z => e z) h
      rw [← hδu_val]
      simpa using hz
    · intro h
      ext z
      rw [hδu_val]
      exact congrArg (fun e : Module.End (ZMod 2) Z => e z) h
  have hoff' : Nat.card Z * Nat.card δu.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ a ∈ Aim, a z = z} := by
    rw [hkerEq, hfix]
    exact hoff
  have hcard := Subgroup.card_ker_mul_card_range δu
  have hle : Nat.card Z ≤
      Nat.card Aim * Nat.card {z : Z // ∀ a ∈ Aim, a z = z} := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := δu.ker))
    calc Nat.card δu.ker * Nat.card Z = Nat.card Z * Nat.card δu.ker := Nat.mul_comm _ _
      _ ≤ Nat.card D * Nat.card {z : Z // ∀ a ∈ Aim, a z = z} := hoff'
      _ = (Nat.card δu.ker * Nat.card Aim) *
            Nat.card {z : Z // ∀ a ∈ Aim, a z = z} := by rw [hcard]
      _ = Nat.card δu.ker *
            (Nat.card Aim * Nat.card {z : Z // ∀ a ∈ Aim, a z = z}) :=
          Nat.mul_assoc _ _ _
  omega

theorem sl3_borel_offender_false {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ f)
    {Z : Type} [AddCommGroup Z] [Module (ZMod 2) Z] [Finite Z]
    (ρ : Representation (ZMod 2) SL(3, F) Z) (hirr : ρ.IsIrreducible)
    (hker : ∀ x, ρ x = 1 → x ∈ scalars 3 F)
    {D : Type} [Group D] [Finite D] (δ : Representation (ZMod 2) D Z)
    (hD2 : ∀ d, δ d * δ d = 1)
    (hnorm : ∀ d x, ∃ y, ∀ z, δ d (ρ x z) = ρ y (δ d z))
    (hgraph : ∃ d, ∃ (A : GL (Fin 3) F) (σ : F ≃+* F),
      ∀ x z, δ d (ρ x z) = ρ (CFSG.LieType.SpecialLinear.borelStd 3 F A σ 1 x) (δ d z))
    (hoff : Nat.card Z * Nat.card δ.ker ≤
      Nat.card D * Nat.card {z : Z // ∀ d, δ d z = z}) :
    False := by
  obtain ⟨d, A, σ, hd⟩ := hgraph
  refine sl3_graph_offender_false hf hF ρ hirr hker δ hD2 hnorm ?_ hoff
  refine ⟨d, A * CFSG.LieType.SpecialLinear.revGL 3 F, σ, ?_⟩
  intro x z
  rw [← CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL.borelStd_one_eq_stdAut]
  exact hd x z

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.PSL
