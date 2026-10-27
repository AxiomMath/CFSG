module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173XDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem lin_two_stdVanishes_of_top (hV : 3 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} (h : innerClosure A g = ⊤) :
    StdVanishes A g := by
  rintro ⟨T, hTbot, hT2, hTN⟩
  let d := Module.finrank (ZMod 2) V
  let e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearEquiv.ofFinrankEq V _ (by simp [d, Module.finrank_fin_fun])
  have hsn : IsSimpleGroup (V ≃ₗ[ZMod 2] V) ∧
      ∃ a b : V ≃ₗ[ZMod 2] V, a * b ≠ b * a :=
    CFSG.LocalAnalysis.GLTheoremA.S172A.GL.simple_nonab_of_equiv
      (CFSG.LocalAnalysis.GLTheoremA.S172A.GL.conjEquiv e)
      (CFSG.LocalAnalysis.GLTheoremA.S172A.GL.vecAut_simple_nonab (k := d)
        (by simpa [d] using hV))
  haveI : IsSimpleGroup (V ≃ₗ[ZMod 2] V) := hsn.1
  have htop : Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V)) = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup (V ≃ₗ[ZMod 2] V)) = innerClosure A g ⊔ A := by rw [h, top_sup_eq]
      _ ≤ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V)) := hTN
  have hTnorm : T.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  haveI : T.Normal := hTnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hT | hT
  · exact hTbot hT
  · have hT2GL : IsPGroup 2 (V ≃ₗ[ZMod 2] V) :=
      hT2.of_equiv ((MulEquiv.subgroupCongr hT).trans Subgroup.topEquiv)
    haveI : Finite V := Module.finite_of_finite (ZMod 2)
    haveI : Finite (V ≃ₗ[ZMod 2] V) :=
      Finite.of_injective (fun f : V ≃ₗ[ZMod 2] V => (f : V → V)) DFunLike.coe_injective
    have hctr : Subgroup.center (V ≃ₗ[ZMod 2] V) = ⊥ :=
      CFSG.LocalAnalysis.GLTheoremA.S172A.GL.center_eq_bot_of_simple_nonab hsn.2
    haveI : Nontrivial (↥(⊥ : Subgroup (V ≃ₗ[ZMod 2] V))) :=
      hctr ▸ hT2GL.center_nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(⊥ : Subgroup (V ≃ₗ[ZMod 2] V)))
    exact hx (Subtype.ext (Subgroup.mem_bot.mp x.2))

theorem lin_two_stdVanishes_of_irreducible (hV : 0 < Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V}
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ h ∈ stdLayer g, ∀ w ∈ W, h w ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    StdVanishes A g := by
  rintro ⟨T, hTbot, hT2, hTN⟩
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  have hN : stdLayer g ≤ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V)) :=
    (le_closureIn_self (stdLayer g)
        (Subgroup.normalizer (A : Set (V ≃ₗ[ZMod 2] V)))).trans (le_sup_left.trans hTN)
  let W : Submodule (ZMod 2) V :=
    { carrier := MulAction.fixedPoints T V
      zero_mem' := by
        rw [MulAction.mem_fixedPoints]
        intro t
        exact smul_zero t
      add_mem' := by
        intro a b ha hb
        rw [MulAction.mem_fixedPoints] at ha hb ⊢
        intro t
        rw [smul_add, ha t, hb t]
      smul_mem' := by
        intro c a ha
        rw [MulAction.mem_fixedPoints] at ha ⊢
        intro t
        have hca : (t : V ≃ₗ[ZMod 2] V) a = a := by
          simpa [Subgroup.smul_def] using ha t
        rw [Subgroup.smul_def, LinearEquiv.smul_def, map_smul, hca] }
  have hWmem : ∀ v : V, v ∈ W ↔ ∀ t : T, t • v = v := by
    intro v
    change v ∈ MulAction.fixedPoints T V ↔ ∀ t : T, t • v = v
    exact MulAction.mem_fixedPoints
  have hWinv : ∀ h ∈ stdLayer g, ∀ w ∈ W, h w ∈ W := by
    intro h hh w hw
    rw [hWmem] at hw ⊢
    intro t
    have hhn : h ∈ Subgroup.normalizer (T : Set (V ≃ₗ[ZMod 2] V)) := hN hh
    have ht : h⁻¹ * (t : V ≃ₗ[ZMod 2] V) * h ∈ T :=
      (Subgroup.mem_normalizer_iff''.mp hhn (t : V ≃ₗ[ZMod 2] V)).mp t.2
    have hfix := hw ⟨h⁻¹ * (t : V ≃ₗ[ZMod 2] V) * h, ht⟩
    have hfix' : h⁻¹ ((t : V ≃ₗ[ZMod 2] V) (h w)) = w := by
      simpa [Subgroup.smul_def, LinearEquiv.smul_def, LinearEquiv.mul_apply] using hfix
    have h2 : (t : V ≃ₗ[ZMod 2] V) (h w) = h w := by
      have := congrArg (fun x => h x) hfix'
      simpa using this
    simpa [Subgroup.smul_def] using h2
  have hdvd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 hV.ne'
  have h0 : (0 : V) ∈ MulAction.fixedPoints T V := by
    rw [MulAction.mem_fixedPoints]
    intro t
    exact smul_zero t
  obtain ⟨b, hb, hb0⟩ :=
    hT2.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd h0
  have hbW : b ∈ W := by
    rw [hWmem]
    rw [MulAction.mem_fixedPoints] at hb
    exact hb
  have hbne : b ≠ 0 := fun h => hb0 h.symm
  have hWne : W ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hbW
    exact hbne hbW
  have hWne_top : W ≠ ⊤ := by
    intro htop
    apply hTbot
    rw [eq_bot_iff]
    intro t ht
    rw [Subgroup.mem_bot]
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ W := by rw [htop]; trivial
    have hv' : (⟨t, ht⟩ : T) • v = v := (hWmem v).mp hv ⟨t, ht⟩
    simpa [Subgroup.smul_def] using hv'
  rcases hirr W hWinv with hW | hW
  · exact hWne hW
  · exact hWne_top hW

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
