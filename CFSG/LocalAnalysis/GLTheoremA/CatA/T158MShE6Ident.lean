module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6ModelTw
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Core
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Head
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6D4
import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MShE6Short
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeShape
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeClass
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def T158IdentTwE6Pre : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ),
    PreSetup 3 L J A d b → catalogIs (PSimple 3 L) (S10.isTE6n n) → Odd n →
      catalogIs (PSimple 3 J) (S10.isU3n (3 * n))

theorem statedClassicalModel_rationalComponent_of_orbit_three
    {Lf : Type} [Field Lf] [IsAlgClosed Lf] [CharP Lf 2] {p₀ : ℕ} (S : LangSetup Tag.E6 Lf p₀) {n : ℕ}
    (hn : 0 < n) (hSq : S.D.q = 2 ^ n) (h3q : 3 ∣ S.D.q + 1) {a : Fin Tag.E6.rank → Lfˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus) (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1)
    (h18 : (kernelRoots (rootCharHom a)).ncard = 18) (i : KernelComponent (rootCharHom a))
    (hs3 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3) :
    StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) .PSU 3 2 (n * 3) := by
  have hL3 : ((3 : ℕ) : Lf) ≠ 0 := by
    intro h0
    have h23 := (CharP.cast_eq_zero_iff Lf 2 3).1 h0
    omega
  obtain ⟨c, hc, hc6⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.kernel_classes_of_ncard_eighteen hL3 hap
      h18
  have hi6 : (componentRoots (rootCharHom a) i).ncard = 6 := by
    obtain ⟨k, rfl⟩ := hc.2 i
    exact hc6 k
  obtain ⟨ψ, σ, π, hψ, hΨ, hπ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.exists_unitary_frame_of_odd_orbit S hL3 hT
      hap h1 i hi6 (by rw [hs3]) h3q
  have hQ : ((3 : ℕ), 2 ^ (n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) ≠ (3, 2) := by
    intro hc'
    have h2 : 2 ^ (n * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) = 2 := (Prod.mk.inj hc').2
    rw [hs3] at h2
    have h8 : 2 ^ 3 ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmodel := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.rationalComponent_suN_model S hT i
    (le_refl 3) hψ hΨ π hπ Nat.prime_two inferInstance hn hSq hQ
  rw [hs3] at hmodel
  exact hmodel

theorem t158IdentTwE6Pre_of
    (hK : T171Sh.ExcKernelCompAction) (hR2 : E6D4T2CosetAction) : T158IdentTwE6Pre := by
  intro G _ _ L J A d b n hP hcat hodd
  obtain ⟨C, _, _, θ, β, φ, Lf, _, _, _, S, a, ι, y, -, hβind, hφind, hshape, hT, hap, h1, hι, hrange,
    hβ, hφ, hyC, hyF, hout, hSq⟩ := t158E6ModelData_tw_of_isTE6n hP hcat hodd
  obtain ⟨i, hyStab, -, -, -, -, hqs, -, -, ⟨e⟩, hInn, -, -⟩ :=
    t158E6LangData_of_modelData hP hβind hφind hshape hT hap h1 hι hrange hβ hφ hyC hyF hout
  have hb3 : b ^ 3 = 1 := hP.elem.2 b hP.b_mem
  have hFG : FGOn 3 b J := hP.fg
  by_cases hyM : y ∈ torusGroup Tag.E6 Lf ⊔ rootSpan Tag.E6 Lf (kernelRoots (rootCharHom a))
  ·
    exfalso
    by_cases h360 : Nat.card (PSimple 3 J) = 360
    · exact not_fgOn_of_innAutDerived d4InnAutDerivedNotFG_holds hP.pcomp hP.chevJ hb3 hP.b_norm
        (Or.inr h360) hFG
    · have hR360 : Nat.card (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) ≠ 360 := fun h =>
        h360 ((Nat.card_congr e.toEquiv).trans h)
      have hmain := hK (τ := Tag.E6) (L := Lf) S Nat.prime_five (by norm_num) Nat.prime_three (by norm_num)
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hT hap
        (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rootDiagUnit_pow_eq_one_of_forall hap) h1
        (fun h => by cases h) i hqs hR360 hyM hyF hyStab
      exact not_fgOn_of_innAutDerived d4InnAutDerivedNotFG_holds hP.pcomp hP.chevJ hb3 hP.b_norm
        (Or.inl (hInn hmain)) hFG
  · rcases e6ShortOrbit_holds Lf 5 S a hT hap h1 i hqs y hyC hyF hyStab hyM with ⟨h18, hs3⟩ | h24
    ·
      have h3q : 3 ∣ S.D.q + 1 := by
        rw [hSq]
        obtain ⟨j, rfl⟩ := hodd
        rw [pow_succ, pow_mul]
        have h4 : (2 ^ 2) ^ j % 3 = 1 := by
          rw [Nat.pow_mod]
          norm_num
        omega
      obtain ⟨q, hv, hqp, hqe, ⟨e'⟩⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.exists_twistedA_of_statedClassicalModel_PSU
          (m := 2) (statedClassicalModel_rationalComponent_of_orbit_three S hodd.pos hSq h3q hT hap h1 h18 i hs3)
      exact ⟨.lie ⟨.twistedA 2 q, hv⟩, ⟨hqp, hqe.trans (mul_comm n 3)⟩, ⟨e.trans e'⟩⟩
    ·
      exfalso
      rcases hR2 Lf 5 S hshape a hT hap h24 i hqs y hyC hyF hyStab hyM with htd | hmem
      · exact not_fgOn_of_isTD4 ((CFSG.LocalAnalysis.GLTheoremA.catalogIs_congr e).2 htd) hFG
      · exact not_fgOn_of_innAutDerived d4InnAutDerivedNotFG_holds hP.pcomp hP.chevJ hb3 hP.b_norm
          (Or.inl (hInn hmem)) hFG

end CFSG.LocalAnalysis.GLTheoremA.T158

end
