module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7TwoSevenLang
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SevenWeylSylow

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal)

theorem exists_pow_eq_of_pow_seven {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 7) {b : Lˣ}
    (hb : b ^ 7 = 1) : ∃ n : ℕ, b = ζ ^ n := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hprim : IsPrimitiveRoot ((ζ : Lˣ) : L) 7 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hi : ((b : Lˣ) : L) ^ 7 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hb, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
  exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩

theorem e7SevenPlaneWeyl_holds :
    E7SevenPlaneWeyl := by
  intro L _ a ha y hy
  by_cases hall : ∀ (s : Fin 2) (i : Fin Tag.E7.rank), a s i = 1
  ·
    have hone : ∀ (s : Fin 2) (α : Fin Tag.E7.rank → ℤ), rootChar (a s) α = 1 := fun s α => by
      simp [rootChar, hall s]
    have htop : (⊤ : Subgroup (WeylGroup Tag.E7)) ≤
        Subgroup.closure ((fun α => rootReflection α) '' familyKernel (τ := Tag.E7) a) := by
      rw [← closure_rootReflection_eq_top (τ := Tag.E7)]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨α, hα, rfl⟩
      exact ⟨α, ⟨hα, fun s => hone s α⟩, rfl⟩
    exact htop (Subgroup.mem_top y)
  ·
    push Not at hall
    obtain ⟨s₀, i₀, hne⟩ := hall
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hζ : orderOf (a s₀ i₀) = 7 := orderOf_eq_prime (ha s₀ i₀) hne
    have hexp : ∀ (s : Fin 2) (i : Fin Tag.E7.rank), ∃ n : ℕ, a s i = (a s₀ i₀) ^ n :=
      fun s i => exists_pow_eq_of_pow_seven hζ (ha s i)
    choose e he using hexp
    set z : Fin 2 → Fin Tag.E7.rank → ZMod 7 := fun s i => (e s i : ZMod 7) with hz
    have hchar : ∀ (s : Fin 2) (l l' : Fin Tag.E7.rank → ℤ),
        rootChar (a s) l = rootChar (a s) l' ↔ charVal (z s) l = charVal (z s) l' :=
      fun s l l' => rootChar_eq_rootChar_iff hζ (e s) (a s) (he s) l l'
    have hyU : y ∈ dualWeylStabilizer (z 0) ⊓ dualWeylStabilizer (z 1) :=
      ⟨fun x => (hchar 0 _ _).1 (hy 0 x), fun x => (hchar 1 _ _).1 (hy 1 x)⟩
    have hmain := e7_inf_dualWeylStabilizer_le_closure (z 0) (z 1) hyU
    have hker : familyKernel (τ := Tag.E7) a = rootKernel (z 0) ∩ rootKernel (z 1) := by
      ext α
      have h0 : ∀ s, rootChar (a s) α = 1 ↔ charVal (z s) α = 0 := fun s => by
        have h := hchar s α 0
        rw [rootChar_zero] at h
        have h00 : charVal (z s) (0 : Fin Tag.E7.rank → ℤ) = 0 := by simp [charVal]
        rw [h00] at h
        exact h
      constructor
      · rintro ⟨hα, hs⟩
        exact ⟨⟨hα, (h0 0).1 (hs 0)⟩, ⟨hα, (h0 1).1 (hs 1)⟩⟩
      · rintro ⟨⟨hα, h0'⟩, ⟨-, h1'⟩⟩
        refine ⟨hα, fun s => ?_⟩
        fin_cases s
        · exact (h0 0).2 h0'
        · exact (h0 1).2 h1'
    rw [hker]
    refine Subgroup.closure_mono ?_ hmain
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨α, hα, rfl⟩

end CFSG.LieType.SeitzGeneration.ExcHigh

end
