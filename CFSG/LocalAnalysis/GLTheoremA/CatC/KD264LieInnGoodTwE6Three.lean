module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTwE6Frame
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.FamOpen
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Pair
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.Rigid
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.TwLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwE6Three

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE CFSG.LieType.SeitzGeneration
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

set_option linter.unusedSectionVars false


theorem exists_good_twistedE6_three {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hq2 : ℓ ^ f ≠ 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (D : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hDd : D ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 3 ^ 2) :
    ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (twistedE6RootGroup K σ), P ≤ fixSubgroup β ∧
      ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h => hℓ3
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hq4 : 4 ≤ ℓ ^ f :=
    four_le_of_not_three_dvd (le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)) h3 hq2
  have hinj := twistedE6InndiagConj_injective hℓ hf hK σ hσ
  have hDr : D ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hDd
  set D₀ : Subgroup ↥(twistedE6InndiagGL K σ) := D.comap (twistedE6InndiagConj K σ) with hD₀
  have hmap : D₀.map (twistedE6InndiagConj K σ) = D := Subgroup.map_comap_eq_self hDr
  have hpow : ∀ x ∈ D₀, x ^ 3 = 1 := fun x hx =>
    hinj (by rw [map_pow, map_one]; exact hD.2 _ hx)
  have hcard₀ : Nat.card D₀ = 3 ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have key : ∀ g₁ ∈ D₀, ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K),
      (∀ c, Fr c = c ^ (ℓ ^ f)) → ∀ {w' : WeylGroup TwistTag.E6.tag}
      {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
      (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
      (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
      (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ), (∀ i, a i ^ 3 = 1) →
      rootDiagUnit TwistTag.E6.tag a ∈ twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w')
        (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) →
      rootDiagUnit TwistTag.E6.tag a ≠ 1 →
      (∃ β, IsRoot TwistTag.E6.tag β ∧ rootChar a β = 1) →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (g₁ : ModGL TwistTag.E6.tag K) *
        g0 = rootDiagUnit TwistTag.E6.tag a →
      ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup (twistedE6RootGroup K σ), P ≤ fixSubgroup β ∧
        ⁅P, P⁆ = P ∧ 3 ∣ Nat.card P := by
    intro g₁ hg₁ Fr hFr w' g0 hg0C hg0 a ha3 hT ha1 ⟨β, hβ, hχ⟩ hg
    obtain ⟨P, hPfix, hPperf, hPdvd⟩ := exists_perfect_of_twistedE6_langFrame_three hℓ hf hK σ hσ
      h3 hq4 hFr hg0C hg0 a ha3 hT ha1 hβ hχ g₁ hg
    refine ⟨twistedE6InndiagConj K σ g₁, hg₁, fun h1 => ?_, P, hPfix, hPperf, hPdvd⟩
    have hg1 : g₁ = 1 := hinj (h1.trans (map_one _).symm)
    apply ha1
    rw [← hg, hg1]
    simp
  obtain ⟨K₁, hK₁fin, hroot⟩ := exists_cubeExt K
  haveI : Finite K₁ := hK₁fin
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  by_cases hiso : TwistedE6DiagIsotropic K σ K₁ D
  ·
    have hC₁ : ∀ x ∈ D₀, baseChangeGL (algebraMap K K₁) (x : ModGL TwistTag.E6.tag K) ∈
        adjointGroup Tag.E6 K₁ := fun x _ =>
      map_twistedE6InndiagGL_le σ _ hroot (Subgroup.mem_map_of_mem _ x.2)
    obtain ⟨v, Fr, hFr, g0, hg0C, hg0, hmem⟩ :=
      twistedE6IsotropicToralInndiag_of_planeToralLang twistedE6PlaneToralLang_proved ℓ f hℓ hℓ3
        hf K hK σ hσ K₁ D₀ hpow hcard₀ hC₁ hiso
    set L := AlgebraicClosure K with hL
    set ι : K →+* L := algebraMap K L with hι
    let θ : ↥(twistedE6InndiagGL K σ) →* ModGL TwistTag.E6.tag L :=
      (MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL ι).comp (twistedE6InndiagGL K σ).subtype)
    have hθ : ∀ x : ↥(twistedE6InndiagGL K σ),
        θ x = g0⁻¹ * baseChangeGL ι (x : ModGL TwistTag.E6.tag K) * g0 := fun x => by
      change (MulAut.conj g0⁻¹) (baseChangeGL ι (x : ModGL TwistTag.E6.tag K)) = _
      rw [MulAut.conj_apply, inv_inv]
    have hθinj : Function.Injective θ :=
      (MulAut.conj g0⁻¹).injective.comp ((baseChangeGL_injective ι).comp Subtype.val_injective)
    have hD₀fin : Finite D₀ := Nat.finite_of_card_ne_zero (by rw [hcard₀]; norm_num)
    have hT : ∀ x ∈ D₀, θ x ∈ twistedTorusOf
        (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
        (twistHom TwistTag.E6 L Fr) := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hmem x hx
      rw [hθ, ← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show g0⁻¹ * (g0 * y * g0⁻¹) * g0 = y by group]
      exact hy
    set B : Subgroup (ModGL TwistTag.E6.tag L) := D₀.map θ with hB
    have hBfin : Finite B := Finite.of_surjective (fun x : D₀ => (⟨θ x, x, x.2, rfl⟩ : B))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
    have hBT : B ≤ torusGroup TwistTag.E6.tag L := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_twistedTorusOf.1 (hT x hx)).1
    have hBpow : ∀ y ∈ B, y ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hpow x hx, map_one]
    have hBcard : 3 < Nat.card B := by
      rw [hB, Subgroup.card_map_of_injective hθinj, hcard₀]
      norm_num
    obtain ⟨a, haB, ha1, hχ⟩ := exists_rootChar_eq_one_of_finite Nat.prime_three hBT hBpow hBcard
      (Pi.single 0 1)
    obtain ⟨x, hx, hxa⟩ := haB
    have hd3 : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1 := hBpow _ ⟨x, hx, hxa⟩
    have ha3 : ∀ i, a i ^ 3 = 1 := by
      have hpow' : a ^ 3 = 1 := by
        apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := TwistTag.E6.tag) (K := L)
        rw [← rootDiagUnit_pow, hd3, rootDiagUnit_one]
      exact fun i => by simpa using congrFun hpow' i
    exact key x hx Fr hFr hg0C hg0 a ha3 (hxa ▸ hT x hx) ha1
      ⟨_, isRoot_single _ 0, hχ⟩ ((hθ x).symm.trans hxa)
  ·
    have hnoniso' : ∃ s t : ↥(e6Data_valid.minGroup K₁),
        (e6Isogeny K₁ s : ModGL Tag.E6 K₁) ∈
          (D₀.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL (algebraMap K K₁)) ∧
        (e6Isogeny K₁ t : ModGL Tag.E6 K₁) ∈
          (D₀.map (twistedE6InndiagGL K σ).subtype).map (baseChangeGL (algebraMap K K₁)) ∧
        s * t ≠ t * s := by
      unfold TwistedE6DiagIsotropic at hiso
      push Not at hiso
      exact hiso
    obtain ⟨s, t, hs, ht, hst⟩ := hnoniso'
    obtain ⟨_, ⟨g₁, hg₁, rfl⟩, hs1⟩ := hs
    obtain ⟨_, ⟨g₂, hg₂, rfl⟩, ht1⟩ := ht
    have hg₁3 : g₁ ^ 3 = 1 := hpow g₁ hg₁
    have hg₂3 : g₂ ^ 3 = 1 := hpow g₂ hg₂
    have hcomm₀ : g₁ * g₂ = g₂ * g₁ := by
      refine hinj ?_
      have := congrArg Subtype.val
        (hD.1.is_comm.comm ⟨twistedE6InndiagConj K σ g₁, hg₁⟩
          ⟨twistedE6InndiagConj K σ g₂, hg₂⟩)
      rw [map_mul, map_mul]
      exact this
    have hd₁3 : (g₁ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hg₁3
    have hd₂3 : (g₂ : ModGL TwistTag.E6.tag K) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hg₂3
    have hcomm : (g₁ : ModGL TwistTag.E6.tag K) * g₂ = g₂ * g₁ := by
      simpa using congrArg Subtype.val hcomm₀
    have h3K : ¬ 3 ∣ Nat.card K := by
      rw [hK]
      intro h
      exact h3 (Nat.prime_three.dvd_of_dvd_pow h)
    obtain ⟨c₂, hc₂, a, b, w, ha3, hw, hsh, hca, hcb⟩ :=
      E6Heis.pair_normal_form_tw h3K K₁ (g₁ : ModGL TwistTag.E6.tag K)
        (g₂ : ModGL TwistTag.E6.tag K) (twistedE6InndiagGL_le_e6InndiagGL K σ g₁.2)
        (twistedE6InndiagGL_le_e6InndiagGL K σ g₂.2) hd₁3 hd₂3 hcomm s t hs1.symm ht1.symm hst
    set L := AlgebraicClosure K with hL
    have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
    set ι₀ : K →+* L := algebraMap K L with hι₀
    set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
    have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => by rw [hFrdef, iterateFrobenius_def]
    have hFix : twistHom TwistTag.E6 L Fr (baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K)) =
        baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) :=
      ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 L Fr).1
        (map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf hK σ hσ Fr hFr
          (Subgroup.mem_map_of_mem _ g₁.2))).2
    have hga : (c₂⁻¹)⁻¹ * baseChangeGL ι₀ (g₁ : ModGL TwistTag.E6.tag K) * c₂⁻¹ =
        rootDiagUnit Tag.E6 a := by
      rw [inv_inv]
      exact hca
    obtain ⟨w', z, hz, hu, hga', hT⟩ :=
      E6Heis.lang_step_single_tw (L := L) (ℓ := ℓ) f hf (inv_mem hc₂) a ha3 hga hFix
    have hzC : z ∈ adjointGroup TwistTag.E6.tag L :=
      sup_le torusGroup_le_adjointGroup' (rootSpan_le_adjointGroup L _) hz
    have hg0C : c₂⁻¹ * z ∈ adjointGroup TwistTag.E6.tag L := mul_mem (inv_mem hc₂) hzC
    have ha1 : rootDiagUnit Tag.E6 a ≠ 1 := by
      intro h1
      apply hsh
      have : a = 1 :=
        CFSG.LieType.Chevalley.rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
      subst this
      simp [rootChar]
    exact key g₁ hg₁ Fr hFr hg0C hu a ha3 hT ha1 (E6Heis.exists_kernelRoot a ha3 hw hsh) hga'

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
