module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveInspG2
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.HardMathSupport.Foote.ModuleExclusions

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.CGT6M

section Core

variable {K : Type} [Field K] [Finite K]

theorem charP_five_of_natCard {f : ℕ} (h : Nat.card K = 5 ^ f) : CharP K 5 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact charP_of_card_eq_prime_pow (p := 5) (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem invData_charFive_of_toral
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8) {f : ℕ} (hKc : Nat.card K = 5 ^ f)
    (htoral : ∀ (ι : K →+* AlgebraicClosure K) (w : ↥(adjointGroup τ K))
      (a : Fin τ.rank → (AlgebraicClosure K)ˣ), (∀ i, a i = 1 ∨ a i = -1) → a ≠ 1 →
        baseChangeGL ι (w : ModGL τ K) = rootDiagUnit τ a → InvData ↥(adjointGroup τ K) w)
    (t : ↥(adjointGroup τ K)) (ht1 : t ≠ 1) (ht2 : t * t = 1) :
    InvData ↥(adjointGroup τ K) t := by
  classical
  have h5K : CharP K 5 := charP_five_of_natCard hKc
  have hK : Odd (Nat.card K) := by rw [hKc]; exact Odd.pow (by decide)
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  set p := ringChar K with hp_def
  have hpK : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hp⟩
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  set Fr := iterateFrobenius L p n with hFr_def
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hFr_def, iterateFrobenius_def, Nat.card_eq_fintype_card, hcard]
  obtain ⟨hinj, -, -, -⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness τ K hK L (algebraMap K L)
  obtain ⟨-, hHR, -, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group τ K hK L Fr hFr
  set ι := algebraMap K L with hι
  let ι₀ : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hι₀ : Function.Injective ι₀ := hinj.comp (adjointGroup τ K).subtype_injective
  have hxR := hHR ⟨(t : ModGL τ K), t.2, rfl⟩
  have ht2' : (t : ModGL τ K) ^ 2 = 1 := by
    rw [sq]
    exact congrArg Subtype.val ht2
  have hx2 : (baseChangeGL ι (t : ModGL τ K)) ^ 2 = 1 := by
    rw [← map_pow, ht2', map_one]
  obtain ⟨h, -, a, ha, hhx, hHh, -, -⟩ :=
    G2_F4_E6_E8_rational_inner_diagonal_involution_fixed_p_components τ K L hτ hK Fr hFr hxR hx2
  have ha1 : a ≠ 1 := by
    intro h1
    apply ht1
    apply hι₀
    rw [h1, rootDiagUnit_one] at hhx
    rw [map_one]
    calc ι₀ t = h⁻¹ * (h * baseChangeGL ι (t : ModGL τ K) * h⁻¹) * h := by
          change baseChangeGL ι (t : ModGL τ K) = _
          group
      _ = 1 := by rw [hhx]; group
  set H := (adjointGroup τ K).map (baseChangeGL ι) with hH
  have hmemH : ∀ q : ↥(adjointGroup τ K), ι₀ q ∈ H := fun q => ⟨q, q.2, rfl⟩
  have hconj : ∀ q : ↥(adjointGroup τ K), h⁻¹ * ι₀ q * h ∈ H := by
    intro q
    have h1 : ι₀ q ∈ H.map (MulAut.conj h).toMonoidHom := by
      rw [hHh]
      exact hmemH q
    obtain ⟨z, hz, hzq⟩ := h1
    have e : z = h⁻¹ * ι₀ q * h := by
      have : h * z * h⁻¹ = ι₀ q := by simpa [MulAut.conj_apply] using hzq
      rw [← this]
      group
    exact e ▸ hz
  have hN : ∀ q : ↥(adjointGroup τ K), ∃ q' : ↥(adjointGroup τ K),
      ι₀ q' = h⁻¹ * ι₀ q * h := fun q => by
    obtain ⟨q', hq', e⟩ := hconj q
    exact ⟨⟨q', hq'⟩, e⟩
  have hd : rootDiagUnit τ a ∈ H := by
    rw [← hhx]
    have h1 : h * baseChangeGL ι (t : ModGL τ K) * h⁻¹ ∈ H.map (MulAut.conj h).toMonoidHom :=
      ⟨_, hmemH t, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; rfl⟩
    rwa [hHh] at h1
  obtain ⟨w', hw', hw'e⟩ := hd
  let w : ↥(adjointGroup τ K) := ⟨w', hw'⟩
  have hw : baseChangeGL ι (w : ModGL τ K) = rootDiagUnit τ a := hw'e
  have htw : ι₀ t = h⁻¹ * ι₀ w * h := by
    change baseChangeGL ι (t : ModGL τ K) = h⁻¹ * baseChangeGL ι (w : ModGL τ K) * h
    rw [hw, ← hhx]
    group
  exact invData_of_conj ι₀ hι₀ h hN htw (htoral ι w a ha ha1 hw)

theorem coverInv_of_invData (hECS : ExceptionalCenterSmallPrimes) {Q : Type} [Group Q]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {f : ℕ} (ht : t ∈ chevalleyExceptionalTags)
    (hmod : ∀ (L : Type) [Group L], Nonempty (L ⧸ Subgroup.center L ≃* Q) →
      ChevalleyExceptionalModel (L ⧸ Subgroup.center L) t 5 f)
    (hinv : ∀ w : Q, w ≠ 1 → w * w = 1 → InvData Q w) : CoverInv Q :=
  coverInv_of_data hinv fun L _ _ hq _ he =>
    hECS L (isQuasisimple_of_open hq) (Or.inl ⟨t, 5, f, ht, hmod L he⟩) 5 Nat.prime_five
      (by norm_num)

end Core

section G2

variable {K : Type} [Field K] [Finite K]

theorem g2_invData_charFive
    {f : ℕ} (hKc : Nat.card K = 5 ^ f) (t : ↥(adjointGroup Tag.G2 K))
    (ht1 : t ≠ 1) (ht2 : t * t = 1) : InvData ↥(adjointGroup Tag.G2 K) t := by
  have : CharP K 5 := charP_five_of_natCard hKc
  exact invData_charFive_of_toral (τ := Tag.G2) (Or.inl rfl) hKc
    (fun ι w a ha ha1 hw => g2_invData_of_toral ι w a ha ha1 hw) t ht1 ht2

theorem coverInv_g2_charFive
    (hECS : ExceptionalCenterSmallPrimes) {f : ℕ} (Q : Type) [Group Q]
    (hQ : ChevalleyExceptionalModel Q .G2 5 f) : CoverInv Q := by
  obtain ⟨hadm, K, hKf, hKfin, hKc, ⟨e0⟩⟩ := hQ
  obtain ⟨K', hK'f, hK'fin, hK'c, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup Tag.G2
    (⟨K, hKf, hKfin, hKc, ⟨e0⟩⟩ : UntwistedChevalleyModel Q .G2 (5 ^ f))
  refine coverInv_of_invData hECS (t := .G2) (f := f) (by simp [chevalleyExceptionalTags])
    (fun L _ ⟨e'⟩ => ⟨hadm, K, hKf, hKfin, hKc, ⟨e'.trans e0⟩⟩) (fun w hw1 hw2 => ?_)
  have hew1 : e w ≠ 1 := fun h => hw1 (e.injective (by rw [h, map_one]))
  have hew2 : e w * e w = 1 := by rw [← map_mul, hw2, map_one]
  exact invData_of_equiv e (g2_invData_charFive hK'c (e w) hew1 hew2)

end G2

end CFSG.HardMathSupport.Foote.ModuleExclusions
