module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLineRGenD4
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeGen
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenFin
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5Lang
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenD5SpinMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSLineR

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.Seitz
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24

set_option linter.unusedSectionVars false


theorem mem_layer_of_a2out {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hfo : f ∉ twistedE6Inn K σ) (hd : TwE6LineDim K σ f 24) {c : twistedE6RootGroup K σ}
    (hfc : f c = c) {m : ℕ} (hcm : c ^ (ringChar K ^ m) = 1) :
    c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} := by
  classical
  obtain ⟨h, rfl, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  obtain ⟨J, hJ, hidx, hnorm, -⟩ := D.exists_component_a2out hdim hE.three_dvd hE.ne_two hfo
  have hcfix : c ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)) := by
    have hle : Subgroup.zpowers (twistedE6InndiagConj K σ h) ≤
        MulAction.stabilizer (MulAut (twistedE6RootGroup K σ)) c :=
      Subgroup.zpowers_le.2 hfc
    intro φ hφ
    exact hle hφ
  have hr : (ringChar K).Coprime 3 :=
    (Nat.coprime_primes D.hℓ Nat.prime_three).2 hE.char_ne_three
  have hJle : J ≤ sSup {J | CFSG.Open.IsComponentOf J
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)))} := le_sSup hJ
  exact hJle (mem_of_relIndex_dvd_three hnorm hidx hcfix hr hcm)

theorem mem_layer_of_cube {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hty : ∀ s : twistedE6RootGroup K σ, f = MulAut.conj s → twE6FixDim K σ s ≠ 24)
    {c : twistedE6RootGroup K σ} (hfc : f c = c) {m : ℕ} (hcm : c ^ (ringChar K ^ m) = 1) :
    c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} := by
  classical
  obtain ⟨h, hh, -, hdim⟩ := twE6MatFixDim_mem_of_mem twE6Order3Dim_holds K σ q
    hE.char_ne_three hE.frob hE.card_field hE.three_dvd hE.ne_two hE.elemAbelian
    hE.le_inndiag hf hf1
  have hLD : ∀ d, twE6MatFixDim K σ h = d → TwE6LineDim K σ f d := fun d hd => ⟨h, hh, hd⟩
  have hN : ∀ n ∈ ({22, 30, 40} : Set ℕ), KSGen.TwE6ConnFixed n := fun n hn => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
    rcases hn with rfl | rfl | rfl
    · exact KSGen.twE6ConnFixed_A (Or.inl rfl)
    · exact KSGen.twE6ConnFixed_A (Or.inr rfl)
    · exact KSGen.twE6ConnFixed_40_of KSGen.d5TorusLang
        (KSGen.d5FixedRational_of_perfect KSGen.d5_fixedSpinPerfect)
  have hNsub : ∀ n ∈ ({22, 30, 40} : Set ℕ), n = 22 ∨ n = 30 ∨ n = 40 := fun n hn => by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hdim
  rcases hdim with h24 | h28 | h30 | h36 | h46
  ·
    have hout : f ∉ twistedE6Inn K σ := by
      rintro ⟨s, hs⟩
      have hq2 : 2 ≤ q := by
        have := Nat.le_of_dvd (by omega) hE.three_dvd
        omega
      have hfd := twE6MatFixDim_of_inner K σ q hE.frob hE.card_field hq2 s h
        (hh.trans hs.symm)
      exact hty s hs.symm (hfd ▸ h24)
    exact mem_layer_of_a2out hE hf hf1 hout (hLD 24 h24) hfc hcm
  · exact mem_layer_of_connFixed hN hNsub hE hf hf1 hh ⟨22, by simp, by omega⟩ hfc hcm
  · exact mem_layer_of_d4 hE hf hf1 (hLD 30 h30) hfc hcm
  · exact mem_layer_of_connFixed hN hNsub hE hf hf1 hh ⟨30, by simp, by omega⟩ hfc hcm
  · exact mem_layer_of_connFixed hN hNsub hE hf hf1 hh ⟨40, by simp, by omega⟩ hfc hcm

theorem twE6LineRGen_holds :
    ∀ (k : Type) [Field k] [Finite k] (σ : k ≃+* k) (q : ℕ)
      (E : Subgroup (MulAut (twistedE6RootGroup k σ))), TwE6Cube k σ q E → q ≠ 8 →
        ∀ f ∈ E, f ≠ 1 →
          (∀ s : twistedE6RootGroup k σ, f = MulAut.conj s → twE6FixDim k σ s ≠ 24) →
            ∀ c : twistedE6RootGroup k σ, f c = c → (∃ n : ℕ, c ^ (ringChar k ^ n) = 1) →
              c ∈ sSup {J | CFSG.Open.IsComponentOf J (fixedPoints (Subgroup.zpowers f))} := by
  intro k _ _ σ q E hE _ f hf hf1 hty c hfc ⟨n, hn⟩
  exact mem_layer_of_cube hE hf hf1 hty hfc hn

end KSLineR

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
