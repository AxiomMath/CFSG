module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodInner
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Layer
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6 CFSG.RankThree.E6
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open scoped Matrix

section Six


theorem perfectCentralizerPlanes_adjointGroup_E6_six (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1) :
    PerfectCentralizerPlanes p (adjointGroup Tag.E6 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ℓ, f, hℓ, hcharK, hf, hK⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := hcharK
  let L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr c
  have hq0 : ((ℓ ^ f : ℕ) : L) = 0 := by
    rw [Nat.cast_pow, CharP.cast_eq_zero, zero_pow (by omega)]
  have hpq' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    rw [hK] at hpd
    exact hpd
  obtain ⟨hpL, ⟨ζ, hζ⟩, hr⟩ := phi6_prime_setup hq0 hp hpq'
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := e6_six_frame K hf hK hp hp3 hpd L
  intro A hA hAcard
  have hAexp : ∀ q ∈ A, q ^ p = 1 := hA.2
  obtain ⟨c, hc⟩ := hconj A (IsPGroup.of_card hAcard)
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := adjEmb Tag.E6 K L with hιdef
  set g1 : ModGL Tag.E6 L := (ι c)⁻¹ * g0 with hg1
  have hg1C : g1 ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem (adjEmb_mem c)) hg0C
  have hg1n : Units.map (entrywiseHom Fr) g1 = g1 * phi6N L := by
    have hΦι : Units.map (entrywiseHom Fr) (ι c) = ι c := adjEmb_frobenius Fr hFrK c
    rw [hg1, map_mul, map_inv, hΦι, hg0]
    group
  have hc1 : ∀ q ∈ A, g1⁻¹ * ι q * g1 ∈ twistedTorus (phi6N L) Fr := fun q hq => by
    have h := hc q hq
    have e : g1⁻¹ * ι q * g1 = g0⁻¹ * ι (c * q * c⁻¹) * g0 := by
      rw [hg1]
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
      group
    rw [e]
    exact h
  set ψ1 : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := (MulAut.conj g1⁻¹).toMonoidHom.comp ι
    with hψ1def
  have hψ1 : ∀ d, ψ1 d = g1⁻¹ * ι d * g1 := fun d => by simp [ψ1, MulAut.conj_apply]
  have hψ1inj : Function.Injective ψ1 :=
    (MulAut.conj g1⁻¹).injective.comp adjEmb_injective
  have hAT : A.map ψ1 = phi6TorusTorsion L Fr p := by
    have hle : A.map ψ1 ≤ phi6TorusTorsion L Fr p := by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨by rw [hψ1]; exact hc1 q hq, ?_⟩
      rw [← map_pow, hAexp q hq, map_one]
    have hTcard : Nat.card (phi6TorusTorsion L Fr p) = p ^ 2 :=
      natCard_phi6TorusTorsion hFr hq0 hp hpq'
    have hcardA : Nat.card (A.map ψ1) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hψ1inj]
      exact hAcard
    haveI : Finite (phi6TorusTorsion L Fr p) :=
      Nat.finite_of_card_ne_zero (by rw [hTcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hTcard, hcardA])
  set r : ZMod p := ((ℓ ^ f : ℕ) : ZMod p) with hrdef
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, -, hA2A2l, -⟩ := h8 p hp3 r hr
  obtain ⟨x, hxA, hx1, hxp, hxA2⟩ : ∃ x ∈ A, x ≠ 1 ∧ orderOf x = p ∧
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (g1⁻¹ * ι x * g1) = parabolicRoots Tag.E6 supportA2A2) := by
    set yk := phi3TorsionHom ζ hζ.pow_eq_one r (Multiplicative.ofAdd (eisLinePoint r 0)) with hyk
    have hykT : yk ∈ phi6TorusTorsion L Fr p :=
      (mem_phi6TorusTorsion_iff hFr hζ hr yk).2 ⟨_, rfl⟩
    rw [← hAT] at hykT
    obtain ⟨x, hxA, hx⟩ := hykT
    have hy1 : yk ≠ 1 := fun h => by
      rw [← map_one (phi3TorsionHom ζ hζ.pow_eq_one r)] at h
      exact eisLinePoint_ne_zero r 0
        (Multiplicative.ofAdd.injective (phi3TorsionHom_injective hζ r h))
    have hx1 : x ≠ 1 := fun h => hy1 (by rw [← hx, h, map_one])
    have hker : torusRootKernel yk = CFSG.RankThree.E6.rootKernel (eisensteinColumn r
        (eisLinePoint r 0).1 (eisLinePoint r 0).2) :=
      torusRootKernel_phi3TorsionHom hζ r _ _
    have hxy : g1⁻¹ * ι x * g1 = yk := by rw [← hψ1, hx]
    have hab0 : ((eisLinePoint r 0).1, (eisLinePoint r 0).2) ≠ 0 := eisLinePoint_ne_zero r 0
    refine ⟨x, hxA, hx1, orderOf_eq_prime (hAexp x hxA) hx1, ?_⟩
    rw [hxy]
    obtain ⟨w, hw, -⟩ := hA2A2l 0 (by decide)
    refine ⟨w, ?_⟩
    rw [hker]
    exact (hw _ _ hab0 (eisensteinLineForm_eisLinePoint r 0)).1
  obtain ⟨hquasi, hpR, -⟩ := e6_six_layer K hf hK hp hp3 hpd L hg1C hg1n hperf hxp (hc1 x hxA)
    hxA2
  refine ⟨x, hxA, hx1, (CFSG.perfectResidual (Subgroup.centralizer ({x} :
    Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
      Set (adjointGroup Tag.E6 K))).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · haveI : Group.IsPerfect ↥((CFSG.perfectResidual (Subgroup.centralizer ({x} :
      Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
        Set (adjointGroup Tag.E6 K))).subtype) := hquasi.1
    exact Subgroup.commutator_eq_self
  · exact (Nat.Prime.dvd_iff_not_coprime hp).2 hpR

end Six

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
