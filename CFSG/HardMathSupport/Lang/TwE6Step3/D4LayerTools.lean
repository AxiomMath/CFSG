module

public import CFSG.HardMathSupport.Lang.TwE6Step3.D4Lines
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWPlane
public import CFSG.HardMathSupport.Malle.SeitzCube.D4LayerBridgeCat

public noncomputable section

namespace CFSG.HardMathSupport.Lang.TwE6Step3

open CFSG.Open TauCeti CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Malle.SeitzCube
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.K128
open CFSG.RankThree.PartOne.Census3 (IsoLie)

open CFSG.RankThree.Chevalley (d4Layer)

open CFSG.RankThree.PartOne.KGD (d4T36d)

open CFSG.RankThree.PartOne.CTP (ExtSeitzAtInnerFor)

open CFSG.HardMathSupport.Seitz.TrialityOdd.Coordinator (PhiPlaneGenAt)


theorem exists_subfield_card {ℓ n : ℕ} [Fact ℓ.Prime] (hn : n ≠ 0) {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ] :
    ∃ (K₃ : Type) (_ : Field K₃) (_ : Finite K₃) (_ : Algebra K₃ Ω) (_ : IsAlgClosure K₃ Ω),
      Nat.card K₃ = ℓ ^ n := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  let S : Subfield Ω := RingHom.eqLocusField (iterateFrobenius Ω ℓ n) (RingHom.id Ω)
  have hmem : ∀ y, y ∈ S ↔ y ^ ℓ ^ n = y := fun y => by
    rw [RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hcard : Nat.card S = ℓ ^ n := by
    rw [← CFSG.RankThree.Classical2.natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) hn]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  have hfin : Finite S := Nat.finite_of_card_ne_zero (by
    rw [hcard]; exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have hS : Algebra.IsAlgebraic S Ω := by
    refine ⟨fun x => ?_⟩
    have hx : IsIntegral K x :=
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
    haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) := IntermediateField.adjoin.finiteDimensional hx
    haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
    haveI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
    have hpow : x ^ Fintype.card (IntermediateField.adjoin K {x}) = x := by
      have h := FiniteField.pow_card (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : (IntermediateField.adjoin K {x}))
      exact congrArg Subtype.val h
    have hN : 1 < Fintype.card (IntermediateField.adjoin K {x}) := Fintype.one_lt_card
    refine ⟨Polynomial.X ^ Fintype.card (IntermediateField.adjoin K {x}) - Polynomial.X,
      FiniteField.X_pow_card_sub_X_ne_zero S hN, ?_⟩
    simp [hpow]
  exact ⟨S, inferInstance, hfin, inferInstance, ⟨inferInstance, hS⟩, hcard⟩

theorem exists_plane_of_sylowShape {X : Type*} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (h : SylowShape p 2 e X) :
    ∃ F : Subgroup X, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  obtain ⟨S⟩ : Nonempty (Sylow p X) := inferInstance
  obtain ⟨φ⟩ := h S S.isPGroup' S.not_dvd_index
  obtain ⟨E, hES, hEp, hEc⟩ :=
    CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.exists_plane_of_sylowShape_gen he
      (S : Subgroup X) φ
  refine ⟨E, ⟨IsMulCommutative.of_comm fun a b => ?_, hEp⟩, hEc⟩
  have ha : (a : X) ∈ (S : Subgroup X) := hES a.2
  have hb : (b : X) ∈ (S : Subgroup X) := hES b.2
  have hcomm : (⟨a, ha⟩ : (S : Subgroup X)) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    apply φ.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  exact Subtype.ext (congrArg (fun z : (S : Subgroup X) => (z : X)) hcomm)

section D4Facts



theorem d4_layer_facts {ℓ f : ℕ} [hℓ : Fact ℓ.Prime] (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharP Ω ℓ]
    {e : ℕ} (he : e = 1 ∨ e = 2) {Y : Type} [Group Y] [Finite Y]
    (φ : Y ≃* ↥(d4Layer (iterateFrobenius Ω ℓ f) e))
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ)
    (hd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (hphi : ℓ ≠ 2 → PhiPlaneGenAt (-1) p)
    (hext : ℓ = 2 → ExtSeitzAtInnerFor (.trialityD4 ⟨ℓ, f, hℓ.out, hf⟩) fun _ => True) :
    PlaneGen Y p ∧ (∃ F : Subgroup Y, IsElemAbelian p F ∧ Nat.card F = p ^ 2) ∧
      ∀ z : Y, (∀ g : Y, g * z = z * g) → z = 1 := by
  classical
  have hℓp : ℓ.Prime := hℓ.out
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨K₃, _, _, _, _, hK₃⟩ :=
    exists_subfield_card (ℓ := ℓ) (n := f * 3) (by omega) (K := K) (Ω := Ω)
  have hK3 : Nat.card K₃ = (ℓ ^ f) ^ 3 := by rw [hK₃, pow_mul]
  haveI hchar : CharP K₃ ℓ := ⟨fun x => by
    rw [← (algebraMap K₃ Ω).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff Ω ℓ x⟩
  let σ : K₃ →+* K₃ := iterateFrobenius K₃ ℓ f
  have hσ : ∀ c, σ c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hFr : ∀ c : Ω, iterateFrobenius Ω ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  let σe : K₃ ≃+* K₃ := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσe : ∀ c, σe c = c ^ (ℓ ^ f) := fun c => hσ c
  have hσe' : ∀ c, σe.toRingHom c = c ^ (ℓ ^ f) := hσe
  have hv : (LieTypeIndex.trialityD4 ⟨ℓ, f, hℓp, hf⟩).Valid := LieTypeIndex.valid_trialityD4 _
  obtain ⟨m⟩ := nonempty_d4Layer_equiv (Ω := Ω) hℓp hf hK3 he hσe' hFr
  obtain ⟨c⟩ := nonempty_d4Layer_equiv_cat (Ω := Ω) hℓp hf hK3 he hσe' hFr hv
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓp.pos
  have hle : ℓ ^ f ≤ (ℓ ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hcast : (((ℓ ^ f) ^ 2 - ℓ ^ f + 1 : ℕ) : ℤ) =
      ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    push_cast [Nat.cast_sub hle]
    ring
  have hpN : p ∣ (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := Int.natCast_dvd_natCast.1 (by rw [hcast]; exact hd)
  have hd' : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 := by
    have : ((ℓ ^ f : ℕ) : ℤ) ^ 2 + (-1) * ((ℓ ^ f : ℕ) : ℤ) + 1 =
        ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by ring
    rw [this]
    exact hd
  have hiso : IsoLie Y (.trialityD4 ⟨ℓ, f, hℓp, hf⟩) := ⟨hv, ⟨φ.trans c⟩⟩
  have hsimple : IsSimpleGroup Y := by
    obtain ⟨-, hsimp⟩ := finite_isSimpleGroup_cat_trialityD4 (q := ⟨ℓ, f, hℓp, hf⟩) hv
    haveI := hsimp
    exact (φ.trans c).isSimpleGroup
  have hplane : ∃ F : Subgroup Y, IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
    have hshape := sylowShape_D4_36 hf K₃ hK3 σe hσe (ε := -1) (Or.inr rfl) hp.out
      (by omega) hd'
    have he1 : 1 ≤ ((d4T36d (-1) (ℓ ^ f)).factorization p) := by
      rw [d4T36d_neg_eq hq1]
      exact (hp.out.factorization_pos_of_dvd (by
        have : 0 < (ℓ ^ f) ^ 2 - ℓ ^ f + 1 := by omega
        omega) hpN)
    exact exists_plane_of_sylowShape he1 (hshape.of_mulEquiv (φ.trans m))
  refine ⟨?_, hplane, ?_⟩
  · refine planeGen_of_isoLie_neg (q := ⟨ℓ, f, hℓp, hf⟩) hiso hp5 hpℓ ?_ hphi hext ?_
    · simpa [TauCeti.PrimePower.card_def] using hd'
    · intro _
      exact ⟨inferInstance, hsimple⟩
  · intro z hz
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · have hzc : z ∈ Subgroup.center Y := Subgroup.mem_center_iff.2 fun g => hz g
      rw [h] at hzc
      exact Subgroup.mem_bot.1 hzc
    · exfalso
      obtain ⟨F, hF, hFc⟩ := hplane
      have hcommY : ∀ a b : Y, a * b = b * a := fun a b => by
        have : a ∈ Subgroup.center Y := by rw [h]; trivial
        exact (Subgroup.mem_center_iff.1 this b).symm
      let : CommGroup Y := { ‹Group Y› with mul_comm := hcommY }
      have hprime := IsSimpleGroup.prime_card (α := Y)
      have hpdvd : p ^ 2 ∣ Nat.card Y := hFc ▸ Subgroup.card_subgroup_dvd_card F
      have hp1 : p ∣ Nat.card Y := dvd_trans (dvd_pow_self p two_ne_zero) hpdvd
      rcases (Nat.dvd_prime hprime).1 hp1 with h1 | h1
      · exact hp.out.one_lt.ne' h1
      · rw [← h1] at hpdvd
        have := Nat.le_of_dvd hp.out.pos hpdvd
        nlinarith [hp5]

end D4Facts

end CFSG.HardMathSupport.Lang.TwE6Step3
