module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8b
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016Sp

open CFSG.Open CFSG.RankThree.Classical CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.LocalAnalysis.GLTheoremA.I2016

abbrev V8 : Type := Fin 4 ⊕ Fin 4 → ZMod 2

@[expose] def FpfIrrGap : Prop :=
  ∀ (g : StatedSp 4 (ZMod 2)) (A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))), g ^ 3 = 1 → g ≠ 1 →
    Sp8Class g 0 4 A₀ A₁ → ∀ M : Subgroup (StatedSp 4 (ZMod 2)), M ≤ A₁ → HasA6Quot M →
      ∀ U : Submodule (ZMod 2) V8,
        (∀ x ∈ M, ∀ u ∈ U, spEnd x u ∈ U) → (∀ u ∈ U, spEnd g u ∈ U) → U = ⊥ ∨ U = ⊤

theorem spEnd_mul (a b : StatedSp 4 (ZMod 2)) : spEnd (a * b) = spEnd a * spEnd b := by
  simp [spEnd, map_mul]

theorem spEnd_mul_apply (a b : StatedSp 4 (ZMod 2)) (v : V8) :
    spEnd (a * b) v = spEnd a (spEnd b v) := by
  rw [spEnd_mul, Module.End.mul_apply]

theorem spEnd_one : spEnd (1 : StatedSp 4 (ZMod 2)) = 1 := by
  simp [spEnd]

theorem spEnd_eq_one_iff {t : StatedSp 4 (ZMod 2)} : spEnd t = 1 ↔ t = 1 := by
  constructor
  · intro h
    apply spLin_injective (r := 4) (K := ZMod 2)
    apply Units.ext
    rw [map_one]
    apply LinearMap.ext
    intro v
    have := congrArg (fun f : Module.End (ZMod 2) V8 => f v) h
    simpa [spEnd] using this
  · rintro rfl
    exact spEnd_one

@[expose] def fixSpace (T : Subgroup (StatedSp 4 (ZMod 2))) : Submodule (ZMod 2) V8 where
  carrier := {v | ∀ t ∈ T, spEnd t v = v}
  add_mem' := by
    intro u v hu hv t ht
    simp only [Set.mem_setOf_eq, map_add] at hu hv ⊢
    rw [hu t ht, hv t ht]
  zero_mem' := by
    intro t _
    simp
  smul_mem' := by
    intro c v hv t ht
    simp only [Set.mem_setOf_eq, map_smul] at hv ⊢
    rw [hv t ht]

theorem mem_fixSpace {T : Subgroup (StatedSp 4 (ZMod 2))} {v : V8} :
    v ∈ fixSpace T ↔ ∀ t ∈ T, spEnd t v = v := Iff.rfl

theorem fixSpace_invariant {T : Subgroup (StatedSp 4 (ZMod 2))} {x : StatedSp 4 (ZMod 2)}
    (hx : ∀ t ∈ T, x⁻¹ * t * x ∈ T) {u : V8} (hu : u ∈ fixSpace T) :
    spEnd x u ∈ fixSpace T := by
  rw [mem_fixSpace]
  intro t ht
  have h1 : x⁻¹ * t * x ∈ T := hx t ht
  have hu' : spEnd (x⁻¹ * t * x) u = u := mem_fixSpace.1 hu _ h1
  calc spEnd t (spEnd x u) = spEnd (t * x) u := (spEnd_mul_apply t x u).symm
    _ = spEnd (x * (x⁻¹ * t * x)) u := by rw [show t * x = x * (x⁻¹ * t * x) by group]
    _ = spEnd x (spEnd (x⁻¹ * t * x) u) := spEnd_mul_apply x _ u
    _ = spEnd x u := by rw [hu']

theorem fixSpace_ne_top {T : Subgroup (StatedSp 4 (ZMod 2))} (hT1 : T ≠ ⊥) : fixSpace T ≠ ⊤ := by
  intro htop
  haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  obtain ⟨t, ht1⟩ := exists_ne (1 : T)
  have hfix : spEnd (t : StatedSp 4 (ZMod 2)) = 1 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ fixSpace T := htop ▸ Submodule.mem_top
    rw [Module.End.one_apply]
    exact mem_fixSpace.1 hv _ t.2
  exact ht1 (Subtype.ext (spEnd_eq_one_iff.1 hfix))

theorem card_V8 : Nat.card V8 = 256 := by
  simp [V8, Nat.card_fun, Nat.card_sum, ZMod.card]

theorem fixSpace_ne_bot {T : Subgroup (StatedSp 4 (ZMod 2))} (hT2 : IsPGroup 2 T) :
    fixSpace T ≠ ⊥ := by
  intro hbot
  letI : MulAction T V8 :=
    { smul := fun t v => spEnd (t : StatedSp 4 (ZMod 2)) v
      one_smul := fun v => by
        show spEnd ((1 : T) : StatedSp 4 (ZMod 2)) v = v
        rw [Subgroup.coe_one, spEnd_one, Module.End.one_apply]
      mul_smul := fun a b v => by
        show spEnd ((a * b : T) : StatedSp 4 (ZMod 2)) v =
          spEnd ((a : T) : StatedSp 4 (ZMod 2)) (spEnd ((b : T) : StatedSp 4 (ZMod 2)) v)
        rw [Subgroup.coe_mul, spEnd_mul_apply] }
  have hmod := hT2.card_modEq_card_fixedPoints V8
  have hfix0 : ∀ x : MulAction.fixedPoints T V8, (x : V8) = 0 := by
    intro x
    have hx : (x : V8) ∈ fixSpace T := fun t ht => x.2 ⟨t, ht⟩
    rw [hbot, Submodule.mem_bot] at hx
    exact hx
  have hcard1 : Nat.card (MulAction.fixedPoints T V8) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ((hfix0 x).trans (hfix0 y).symm)⟩, ⟨⟨0, fun t => ?_⟩⟩⟩
    show spEnd (t : StatedSp 4 (ZMod 2)) 0 = 0
    exact map_zero _
  rw [card_V8, hcard1] at hmod
  norm_num [Nat.ModEq] at hmod


theorem noT_of_fpf (hGap : FpfIrrGap) {g : StatedSp 4 (ZMod 2)} {A₀ A₁ : Subgroup (StatedSp 4 (ZMod 2))}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hC : Sp8Class g 0 4 A₀ A₁) {A : Subgroup (StatedSp 4 (ZMod 2))}
    (hAC : A ≤ Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))) (hA6 : HasA6Quot A)
    {T : Subgroup (StatedSp 4 (ZMod 2))} (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hTg : ∀ t ∈ T, g⁻¹ * t * g ∈ T)
    (hAT : A ≤ Subgroup.normalizer (T : Set (StatedSp 4 (ZMod 2)))) : False := by
  have hA0 : A₀ = ⊥ := by
    rcases hC.fixed with h | h
    · exact h.2
    · exact absurd h.1 (by norm_num)
  have hCA : Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))) = A₁ := by
    rw [hC.centralizer_eq, hA0, bot_sup_eq]
  have hMA₁ : A ≤ A₁ := hCA ▸ hAC
  have hinvA : ∀ x ∈ A, ∀ u ∈ fixSpace T, spEnd x u ∈ fixSpace T := by
    intro x hx u hu
    apply fixSpace_invariant _ hu
    intro t ht
    exact (Subgroup.mem_normalizer_iff''.1 (hAT hx) t).1 ht
  rcases hGap g A₀ A₁ hg3 hg1 hC A hMA₁ hA6 (fixSpace T) hinvA
      (fun u hu => fixSpace_invariant hTg hu) with h | h
  · exact fixSpace_ne_bot hT2 h
  · exact fixSpace_ne_top hT1 h

end CFSG.LocalAnalysis.GLTheoremA.I2016Sp

end
