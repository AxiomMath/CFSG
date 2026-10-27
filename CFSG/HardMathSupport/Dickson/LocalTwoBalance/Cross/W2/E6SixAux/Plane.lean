module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Layer
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6SixAux.Normal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TwistedE6ThreeAux.Layer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossBase
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.E6 CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


theorem innerPlaneBalance_adjointE6_six_R3 (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpd : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 - (Nat.card K : ℤ) + 1) :
    InnerPlaneBalance p (adjointGroup Tag.E6 K) := by
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
  intro E hEin hE hcard H hH
  have hC : Subgroup.center (adjointGroup Tag.E6 K) = ⊥ := center_adjointGroup_eq_bot
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup Tag.E6 K) := E.comap
    (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup Tag.E6 K →*
      MulAut (adjointGroup Tag.E6 K)) = E := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hq
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  set ι : adjointGroup Tag.E6 K →* ModGL Tag.E6 L := adjEmb Tag.E6 K L with hιdef
  set g1 : ModGL Tag.E6 L := (ι c)⁻¹ * g0 with hg1
  have hg1C : g1 ∈ adjointGroup Tag.E6 L := mul_mem (inv_mem (adjEmb_mem c)) hg0C
  have hg1n : Units.map (entrywiseHom Fr) g1 = g1 * phi6N L := by
    have hΦι : Units.map (entrywiseHom Fr) (ι c) = ι c := adjEmb_frobenius Fr hFrK c
    rw [hg1, map_mul, map_inv, hΦι, hg0]
    group
  have hc1 : ∀ q ∈ A₀, g1⁻¹ * ι q * g1 ∈ twistedTorus (phi6N L) Fr := fun q hq => by
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
  have hAT : A₀.map ψ1 = phi6TorusTorsion L Fr p := by
    have hle : A₀.map ψ1 ≤ phi6TorusTorsion L Fr p := by
      rintro _ ⟨q, hq, rfl⟩
      refine ⟨by rw [hψ1]; exact hc1 q hq, ?_⟩
      rw [← map_pow, hA₀exp q hq, map_one]
    have hTcard : Nat.card (phi6TorusTorsion L Fr p) = p ^ 2 :=
      natCard_phi6TorusTorsion hFr hq0 hp hpq'
    have hcardA : Nat.card (A₀.map ψ1) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hψ1inj]
      exact hA₀card
    haveI : Finite (phi6TorusTorsion L Fr p) :=
      Nat.finite_of_card_ne_zero (by rw [hTcard]; positivity)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hTcard, hcardA])
  set r : ZMod p := ((ℓ ^ f : ℕ) : ZMod p) with hrdef
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨-, -, -, -, h8⟩ := E6_Coxeter_square_eight_Eisenstein_root_kernel_lines
  obtain ⟨-, -, -, -, -, hA2A2l, -⟩ := h8 p hp3 r hr
  have hline : ∀ k : Fin 8, k.val < 4 → ∃ x ∈ A₀, x ≠ 1 ∧ orderOf x = p ∧
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (g1⁻¹ * ι x * g1) = parabolicRoots Tag.E6 supportA2A2) ∧
      ∀ α, IsRoot Tag.E6 α → OnEisLine k α → α ∈ torusRootKernel (g1⁻¹ * ι x * g1) := by
    intro k hk
    set yk := phi3TorsionHom ζ hζ.pow_eq_one r (Multiplicative.ofAdd (eisLinePoint r k)) with hyk
    have hykT : yk ∈ phi6TorusTorsion L Fr p :=
      (mem_phi6TorusTorsion_iff hFr hζ hr yk).2 ⟨_, rfl⟩
    rw [← hAT] at hykT
    obtain ⟨x, hxA, hx⟩ := hykT
    have hy1 : yk ≠ 1 := fun h => by
      rw [← map_one (phi3TorsionHom ζ hζ.pow_eq_one r)] at h
      exact eisLinePoint_ne_zero r k
        (Multiplicative.ofAdd.injective (phi3TorsionHom_injective hζ r h))
    have hx1 : x ≠ 1 := fun h => hy1 (by rw [← hx, h, map_one])
    have hker : torusRootKernel yk = CFSG.RankThree.E6.rootKernel (eisensteinColumn r (eisLinePoint r k).1
        (eisLinePoint r k).2) := torusRootKernel_phi3TorsionHom hζ r _ _
    have hxy : g1⁻¹ * ι x * g1 = yk := by rw [← hψ1, hx]
    have hab0 : ((eisLinePoint r k).1, (eisLinePoint r k).2) ≠ 0 := eisLinePoint_ne_zero r k
    refine ⟨x, hxA, hx1, orderOf_eq_prime (hA₀exp x hxA) hx1, ?_, ?_⟩
    · rw [hxy]
      obtain ⟨w, hw, -⟩ := hA2A2l k hk
      refine ⟨w, ?_⟩
      rw [hker]
      exact (hw _ _ hab0 (eisensteinLineForm_eisLinePoint r k)).1
    · intro α hα hon
      rw [hxy, hker, rootKernel_eisensteinColumn hp3 hr hab0
        (eisensteinLineForm_eisLinePoint r k)]
      exact ⟨hα, hon⟩
  obtain ⟨x0, hx0A, hx01, hx0p, hx0A2, hx0roots⟩ := hline 0 (by decide)
  obtain ⟨x1, hx1A, hx11, hx1p, hx1A2, hx1roots⟩ := hline 1 (by decide)
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  have hfix : ∀ x ∈ A₀, x ≠ 1 → orderOf x = p →
      (∃ w : WeylGroup Tag.E6,
        (w • ·) '' torusRootKernel (g1⁻¹ * ι x * g1) = parabolicRoots Tag.E6 supportA2A2) →
      z x = x ∧ ∀ d ∈ (CFSG.perfectResidual (Subgroup.centralizer ({x} :
        Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer ({x} :
          Set (adjointGroup Tag.E6 K))).subtype, z d = d := by
    intro x hxA hx1 hxp hA2
    obtain ⟨hq, hpR, -⟩ := e6_six_layer K hf hK hp hp3 hpd L hg1C hg1n hperf hxp (hc1 x hxA) hA2
    exact fixes_of_mem_localDeltaIn_of_stable hp hinj hH hz hxA hx1 _
      (map_perfectResidual_le_self _)
      (fun η hη r hr => apply_mem_perfectResidual_centralizer hη hr) hq hpR
  obtain ⟨hz0x, hz0D⟩ := hfix x0 hx0A hx01 hx0p hx0A2
  obtain ⟨hz1x, hz1D⟩ := hfix x1 hx1A hx11 hx1p hx1A2
  obtain ⟨G, hGT, hG⟩ := e6_six_normal_of_fixes K hf hK hp hp3 hpd L hg1C hg1n hperf hx0p
    (hc1 x0 hx0A) hx0A2 hz0x hz0D
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hGT).1
  have hcomm : ∀ x : adjointGroup Tag.E6 K, (∀ d ∈ (CFSG.perfectResidual
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)))).map (Subgroup.centralizer
        ({x} : Set (adjointGroup Tag.E6 K))).subtype, z d = d) →
      ∀ d ∈ (CFSG.perfectResidual (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K)))).map
        (Subgroup.centralizer ({x} : Set (adjointGroup Tag.E6 K))).subtype,
        rootDiagUnit Tag.E6 a * (g1⁻¹ * ι d * g1) = (g1⁻¹ * ι d * g1) * rootDiagUnit Tag.E6 a := by
    intro x hzx d hd
    have h := hG d
    rw [hzx d hd, ha] at h
    have h' : (g1⁻¹ * ι d * g1) * rootDiagUnit Tag.E6 a =
        rootDiagUnit Tag.E6 a * (g1⁻¹ * ι d * g1) := by
      calc (g1⁻¹ * ι d * g1) * rootDiagUnit Tag.E6 a
          = (rootDiagUnit Tag.E6 a * (g1⁻¹ * ι d * g1) * (rootDiagUnit Tag.E6 a)⁻¹) *
              rootDiagUnit Tag.E6 a := by rw [← h]
        _ = _ := by group
    exact h'.symm
  obtain ⟨-, -, hkill0⟩ := e6_six_layer K hf hK hp hp3 hpd L hg1C hg1n hperf hx0p (hc1 x0 hx0A)
    hx0A2
  obtain ⟨-, -, hkill1⟩ := e6_six_layer K hf hK hp hp3 hpd L hg1C hg1n hperf hx1p (hc1 x1 hx1A)
    hx1A2
  have h0 := hkill0 a (hcomm x0 hz0D)
  have h1 := hkill1 a (hcomm x1 hz1D)
  have hχ0 : rootChar a (Pi.single (e6Index 0) 1) = 1 := h1 _ (hx1roots _ (isRoot_single Tag.E6 _)
    (by decide +kernel))
  have hχ2 : rootChar a (Pi.single (e6Index 2) 1) = 1 := h0 _ (hx0roots _ (isRoot_single Tag.E6 _)
    (by decide +kernel))
  have hχ3 : rootChar a (Pi.single (e6Index 3) 1) = 1 := h0 _ (hx0roots _ (isRoot_single Tag.E6 _)
    (by decide +kernel))
  have hχ4 : rootChar a (Pi.single (e6Index 4) 1) = 1 := h1 _ (hx1roots _ (isRoot_single Tag.E6 _)
    (by decide +kernel))
  have hχ5 : rootChar a (Pi.single (e6Index 5) 1) = 1 := h0 _ (hx0roots _ (isRoot_single Tag.E6 _)
    (by decide +kernel))
  have hroot13 : IsRoot Tag.E6 (Pi.single (e6Index 1) 1 + Pi.single (e6Index 3) 1) :=
    isRoot_iff_mem_artifactRoots.2 (by decide +kernel)
  have hχ13 : rootChar a (Pi.single (e6Index 1) 1 + Pi.single (e6Index 3) 1) = 1 :=
    h1 _ (hx1roots _ hroot13 (by decide +kernel))
  have hχ1 : rootChar a (Pi.single (e6Index 1) 1) = 1 := by
    rw [rootChar_add, hχ3, mul_one] at hχ13
    exact hχ13
  have ha1 : a = 1 := by
    funext i
    have key : ∀ j : Fin Tag.E6.rank, rootChar a (Pi.single j 1) = 1 → a j = 1 := fun j hj => by
      rw [← CTTorus.rootChar_single a j]
      exact hj
    fin_cases i
    · exact key _ hχ0
    · exact key _ hχ1
    · exact key _ hχ2
    · exact key _ hχ3
    · exact key _ hχ4
    · exact key _ hχ5
  apply MulEquiv.ext
  intro d
  have h := hG d
  rw [ha, ha1, rootDiagUnit_one, one_mul, inv_one, mul_one] at h
  have h2 : ι (z d) = ι d := by
    have h3 : g1 * (g1⁻¹ * ι (z d) * g1) * g1⁻¹ = g1 * (g1⁻¹ * ι d * g1) * g1⁻¹ := by rw [h]
    simpa [mul_assoc] using h3
  exact adjEmb_injective h2

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
