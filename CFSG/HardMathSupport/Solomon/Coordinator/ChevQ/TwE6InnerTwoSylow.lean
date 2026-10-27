module

public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.Canonical
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Order
import CFSG.HardMathSupport.Malle.E27Lie.ExcTwisted.SylowN
import CFSG.HardMathSupport.Malle.E27Lie.ExcTwisted.OrdTwoMod
import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
import CFSG.LieType.Chevalley.WeylNormalizerQuotient
import CFSG.LieType.SeitzGeneration.ExcTorusThreeTw
import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
import CFSG.RankThree.Chevalley.SteinbergBTE6HighestRootGraph
import CFSG.RankThree.PartOne.KE.CTLangData
import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
import CFSG.LieType.SeitzGeneration.ExcTorusTw
import CFSG.LieType.SeitzGeneration.Lift
import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Chevalley CFSG.HardMathSupport.Malle.E27Lie.ExcCross

set_option linter.unusedSectionVars false

private theorem twE6Sylow_hv (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    e6HRReflProd • permLattice TwistTag.E6.perm γ = -γ := by
  rw [e6HRReflProd_smul]
  congr 1
  funext i
  simp only [permLattice, Function.comp_apply, e6_perm_symm_apply, perm6_perm6]

private theorem twE6Sylow_not_three_dvd_index {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hq3 : ℓ ^ f % 3 = 2) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) e6HRReflProd) :
    ¬ 3 ∣ ((X6 (AlgebraicClosure K) Fr e6HRReflProd).comap
      ((MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (twistedE6RootGroup K σ).subtype))).index := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  set L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hq1 : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  have hw0 : ∀ u : Fin TwistTag.E6.tag.rank → ℤ,
      e6HRReflProd • u = -permLattice TwistTag.E6.perm u := fun u => e6HRReflProd_smul u
  set J := twistedE6RootGroup K σ
  haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  haveI hJfin : Finite J := inferInstance
  set X := X6 L Fr e6HRReflProd
  set R := twistedFixedGroup TwistTag.E6 L Fr
  set C' := J.map (baseChangeGL (algebraMap K L))
  let fc : ModGL TwistTag.E6.tag L →* ModGL TwistTag.E6.tag L := (MulAut.conj g0).toMonoidHom
  have hfc_apply : ∀ x, fc x = g0 * x * g0⁻¹ := fun x => rfl
  have hXR : ∀ x ∈ X, fc x ∈ R := by
    intro x hx
    refine (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨?_, ?_⟩
    · rw [hfc_apply]
      exact mul_mem (mul_mem hg0C (X6_le_adjoint Fr _ hx)) (inv_mem hg0C)
    · have h1 := X6_fix hw0 hx
      rw [hfc_apply, map_mul, map_mul, map_inv, hg0]
      calc g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd *
            twistHom TwistTag.E6 L Fr x *
            (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd)⁻¹ =
          g0 * (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd *
            twistHom TwistTag.E6 L Fr x *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) L e6HRReflProd)⁻¹) * g0⁻¹ := by group
        _ = g0 * x * g0⁻¹ := by rw [h1]
  set Y : Subgroup (ModGL TwistTag.E6.tag L) := C'.comap fc
  have hrel : Y.relIndex X ∣ 3 := by
    have h := CFSG.LieType.SeitzGeneration.twisted_E6_relIndex_dvd_three hℓ hf K hK σ.toRingHom
      hσ' L Fr hFr (X := X.map fc) (by
        rintro _ ⟨x, hx, rfl⟩
        exact hXR x hx)
    rwa [← Subgroup.relIndex_comap] at h
  set ι' : ↥J →* ModGL TwistTag.E6.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((baseChangeGL (algebraMap K L)).comp J.subtype)
  have hι'inj : Function.Injective ι' :=
    (MulAut.conj g0⁻¹).injective.comp
      ((baseChangeGL_injective _).comp (Subgroup.subtype_injective _))
  have hrange : ι'.range = Y := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨(z : ModGL TwistTag.E6.tag K), z.2, ?_⟩
      change baseChangeGL (algebraMap K L) (z : ModGL TwistTag.E6.tag K) =
        g0 * ((MulAut.conj g0⁻¹)
          (baseChangeGL (algebraMap K L) (z : ModGL TwistTag.E6.tag K))) * g0⁻¹
      rw [MulAut.conj_apply, inv_inv]
      group
    · rintro ⟨c, hc, hcy⟩
      refine ⟨⟨c, hc⟩, ?_⟩
      change (MulAut.conj g0⁻¹) (baseChangeGL (algebraMap K L) c) = y
      rw [MulAut.conj_apply, inv_inv]
      change baseChangeGL (algebraMap K L) c = g0 * y * g0⁻¹ at hcy
      rw [hcy]
      group
  set Z := X.comap ι' with hZ
  have hcardZ : Nat.card Z = Nat.card ↥(Y ⊓ X) := by
    rw [← Subgroup.card_map_of_injective hι'inj, hZ, Subgroup.map_comap_eq, hrange]
  have hz0 : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  have hm0 : Nat.card ↥(Y ⊓ X) ≠ 0 := hcardZ ▸ hz0
  have hr0 : Y.relIndex X ≠ 0 := fun h => by
    rw [h] at hrel
    exact absurd (Nat.eq_zero_of_zero_dvd hrel) (by norm_num)
  have hcardX : Y.relIndex X * Nat.card ↥(Y ⊓ X) = Nat.card X := Subgroup.relIndex_mul_card Y X
  have hq_ne : (((ℓ ^ f + 1 : ℕ)) : L) ≠ 0 := by
    have hz : ((ℓ : ℕ) : L) = 0 := CharP.cast_eq_zero L ℓ
    have : (((ℓ ^ f + 1 : ℕ)) : L) = 1 := by
      push_cast
      rw [hz, zero_pow (by omega), zero_add]
    rw [this]
    exact one_ne_zero
  have hT := card_twistedTorus6 (L := L) hFr hq_ne hw0
  have hdvdX := twistedTorus6_card_mul_dvd (L := L) Fr e6HRReflProd
  rw [hT] at hdvdX
  set v := padicValNat 3 (ℓ ^ f + 1)
  have hn0 : Nat.card X ≠ 0 := by
    rw [← hcardX]
    exact mul_ne_zero hr0 hm0
  have h3pow : 3 ^ (6 * v + 4) ∣ Nat.card X := by
    refine Dvd.dvd.trans ?_ hdvdX
    have h1 : 3 ^ v ∣ ℓ ^ f + 1 := pow_padicValNat_dvd
    have h2 : 3 ^ (6 * v) ∣ (ℓ ^ f + 1) ^ 6 := by
      rw [mul_comm, pow_mul]
      exact pow_dvd_pow_of_dvd h1 6
    have h3 : 3 ^ 4 ∣ 51840 := by norm_num
    rw [pow_add]
    exact mul_dvd_mul h2 h3
  have hvX : 6 * v + 4 ≤ padicValNat 3 (Nat.card X) := (padicValNat_dvd_iff_le hn0).1 h3pow
  have hvsplit : padicValNat 3 (Nat.card X) =
      padicValNat 3 (Y.relIndex X) + padicValNat 3 (Nat.card ↥(Y ⊓ X)) := by
    rw [← hcardX, padicValNat.mul hr0 hm0]
  have hvr : padicValNat 3 (Y.relIndex X) ≤ 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hrel with h | h
    · rw [h]
      simp
    · rw [h, padicValNat_self]
  have hJcard : Nat.card J = CFSG.Open.ordTwistedE6 (ℓ ^ f) :=
    CFSG.HardMathSupport.Malle.E27Lie.card_graphFixedRootGroup_E6 hℓ hf hK σ.toRingHom hσ'
  have hvJ : padicValNat 3 (Nat.card J) = 6 * v + 3 := by
    rw [hJcard, CFSG.HardMathSupport.Malle.E27Lie.padicValNat_three_ordTwistedE6_of_mod_two hq1 hq3]
  have hidx : Z.index * Nat.card Z = Nat.card J := Subgroup.index_mul_card Z
  have hi0 : Z.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hvidx : padicValNat 3 (Nat.card J) = padicValNat 3 Z.index + padicValNat 3 (Nat.card Z) := by
    rw [← hidx, padicValNat.mul hi0 hz0]
  rw [hcardZ] at hvidx
  intro h3
  have h1 : padicValNat 3 Z.index ≠ 0 := (dvd_iff_padicValNat_ne_zero hi0).1 h3
  omega

theorem twE6SylowMonoTwo_holds :
    ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
      (∀ c, σ c = c ^ q) → q % 3 = 2 →
      ∀ E : Subgroup (twistedE6RootGroup K σ), IsPGroup 3 E →
      ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) ∧
      ∃ v : WeylGroup TwistTag.E6.tag,
        (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) ∧
      ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
        ∀ x ∈ E, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
          ∃ w : WeylGroup TwistTag.E6.tag,
            g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL TwistTag.E6.tag K) * g0 =
              t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
  intro K _ _ σ q hK hσ hq E hE
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hK]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, rfl⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  set ℓ := ringChar K
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hq
      omega
    · exact h0
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := ringChar.charP K
  set L := AlgebraicClosure K
  haveI : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  set Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hσ' : ∀ c, σ.toRingHom c = c ^ (ℓ ^ f) := fun c => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) hf L e6HRReflProd
  have hidx := twE6Sylow_not_three_dvd_index hℓ hf hq hK σ hσ Fr hFr hg0C hg0
  haveI : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  haveI : Finite (twistedE6RootGroup K σ) := inferInstance
  obtain ⟨g, hg⟩ :=
    CFSG.StandardType.TableBF4.exists_conj_le_of_not_dvd_index Nat.prime_three hidx hE
  set b : ModGL TwistTag.E6.tag L := baseChangeGL (algebraMap K L) (g : ModGL TwistTag.E6.tag K)
  obtain ⟨-, hle, -⟩ := exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf
    K hK σ.toRingHom hσ' L Fr hFr
  have hbR : b ∈ twistedFixedGroup TwistTag.E6 L Fr := hle ⟨g, g.2, rfl⟩
  obtain ⟨hbC, hbF⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hbR
  refine ⟨Fr, hFr, e6HRReflProd, twE6Sylow_hv, b⁻¹ * g0, mul_mem (inv_mem hbC) hg0C, ?_,
    fun x hx => ?_⟩
  · rw [map_mul, map_inv, hbF, hg0, mul_assoc]
  · have hm := hg (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
    rw [Subgroup.mem_comap] at hm
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype,
      MulAut.conj_apply, inv_inv] at hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] at hm
    obtain ⟨w, t, ht, hmt⟩ := monomialSubgroup_le_torusWeylCosets
      (X6_le_monomial Fr e6HRReflProd hm)
    refine ⟨t, ht, w, ?_⟩
    rw [← hmt]
    have key : ∀ a c d : ModGL TwistTag.E6.tag L,
        (c⁻¹ * a)⁻¹ * d * (c⁻¹ * a) = a⁻¹ * (c * d * c⁻¹) * a := fun a c d => by group
    exact key g0 b _

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
