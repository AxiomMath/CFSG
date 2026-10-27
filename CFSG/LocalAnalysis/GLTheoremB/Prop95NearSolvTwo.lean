module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearPSU3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts

open CFSG.Open CFSG.SignalizerFunctorTheorem.McBride

namespace NearSolvTwo

variable {X : Type*} [Group X]

theorem pCore_two_fixedSubgroup_eq_bot [Finite X] (f : MulAut X) {ℓ : ℕ}
    (hℓ : Nat.Coprime 2 ℓ) (hF : IsPGroup ℓ (fixedFitting f)) :
    CFSG.pCore 2 ↥(signalizerFixedSubgroup f) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hfit : x ∈ CFSG.fittingSubgroup ↥(signalizerFixedSubgroup f) :=
    CFSG.pCore_le_fitting (↥(signalizerFixedSubgroup f)) 2 hx
  have hxX : (x : X) ∈ fixedFitting f :=
    Subgroup.mem_map_of_mem (signalizerFixedSubgroup f).subtype hfit
  obtain ⟨m, hm⟩ := hF ⟨(x : X), hxX⟩
  have hP : IsPGroup 2 (CFSG.pCore 2 ↥(signalizerFixedSubgroup f)) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hm' : (x : X) ^ ℓ ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hk' : (x : X) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val (congrArg Subtype.val hk)
  have h1 : (x : X) ^ Nat.gcd (2 ^ k) (ℓ ^ m) = 1 := pow_gcd_eq_one.mpr ⟨hk', hm'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k m hℓ), pow_one] at h1
  exact Subtype.ext (by simpa using h1)

theorem eq_one_of_itemC (f : MulAut X) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : ItemC p f) (g : MulAut X) (hg2 : IsPGroup 2 (Subgroup.zpowers g))
    (hfix : ∀ x ∈ signalizerFixedSubgroup f, g x = x) : g = 1 := by
  have hg : g ∈ fixingSubgroup (MulAut X) (signalizerFixedSubgroup f : Set X) :=
    (mem_fixingSubgroup_iff (MulAut X)).mpr fun x hx => by
      rw [MulAut.smul_def]
      exact hfix x hx
  obtain ⟨k, hk⟩ := hI ⟨g, hg⟩
  obtain ⟨j, hj⟩ := hg2 ⟨g, Subgroup.mem_zpowers g⟩
  have hk' : g ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hj' : g ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
    Nat.Coprime.pow k j ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h1 : g ^ Nat.gcd (p ^ k) (2 ^ j) = 1 := pow_gcd_eq_one.mpr ⟨hk', hj'⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h1
  exact h1

end NearSolvTwo

theorem nearSolvableTwoFacts_holds :
    NearSolvableTwoFacts := by
  unfold NearSolvableTwoFacts
  intro S _ _ p hp hp2 _hsimple hdvd hmodel hnot f hf
  have hcop : Nat.Coprime p (Nat.card S) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd
  obtain ⟨ℓ, hℓ, hF, hI⟩ : ∃ ℓ : ℕ, Nat.Coprime 2 ℓ ∧ IsPGroup ℓ (fixedFitting f) ∧
      ItemC p f := by
    rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨n, rfl, ⟨e⟩⟩ | ⟨⟨e⟩⟩
    · have hcopY : Nat.Coprime p
          (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p))) := by
        rw [← Nat.card_congr e.toEquiv]
        exact hcop
      exact ⟨3, by norm_num,
        (Frame.of_model e (fun f' hf' => frame_psl2Even hp hcopY f' hf') hf).C0_pgroup,
        ItemC.of_model e (fun f' hf' => itemC_psl2Even hp hcopY f' hf') hf⟩
    · exact (hnot ⟨e⟩).elim
    · have hcopY : Nat.Coprime (2 * n + 1) (Nat.card (CFSG.Open.Sz n)) := by
        rw [← Nat.card_congr e.toEquiv]
        exact hcop
      have : Finite (CFSG.Open.Sz n) := Finite.of_equiv S e.toEquiv
      have hY := CFSG.SignalizerFunctorTheorem.CatalogBridge.nearPSolvable_sz n hp hcopY
      exact ⟨5, by norm_num,
        (Frame.of_model e (fun f' hf' => frame_sz hp hcopY hY f' hf') hf).C0_pgroup,
        ItemC.of_model e (fun f' hf' => itemC_sz hp hcopY f' hf') hf⟩
    · have hcopY : Nat.Coprime p (Nat.card (CFSG.Open.PSU3 2 p)) := by
        rw [← Nat.card_congr e.toEquiv]
        exact hcop
      have : Finite (CFSG.Open.PSU3 2 p) := Finite.of_equiv S e.toEquiv
      have hY := CFSG.SignalizerFunctorTheorem.CatalogBridge.nearPSolvable_psu3 hp hcopY
      exact ⟨3, by norm_num,
        (Frame.of_model e (fun f' hf' => frame_psu3 hp hcopY hY f' hf') hf).C0_pgroup,
        ItemC.of_model e (fun f' hf' => itemC_psu3 hp hcopY f' hf') hf⟩
  exact ⟨NearSolvTwo.pCore_two_fixedSubgroup_eq_bot f hℓ hF,
    fun g hg2 hfix => NearSolvTwo.eq_one_of_itemC f hp hp2 hI g hg2 hfix⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
