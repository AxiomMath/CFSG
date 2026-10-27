module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.BT2Basic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpInner

public noncomputable section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag SymplecticHigher
open CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

theorem involutionCentralizersCharTwo_statedProj_statedSp {f r : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r)
    {k : Type} [Field k] (hk : Nat.card k = 2 ^ f) :
    InvolutionCentralizersCharTwo (StatedProj (StatedSp r k)) := by
  intro t ht
  classical
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : NeZero r := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := UnitaryHigher.proj_bijective_of_charTwo (r := r) (K := k)
  have hιinj := spInner_injective (r := r) (K := k)
  have : Finite (StatedSp r k) := inferInstance
  have : Finite (StatedProj (StatedSp r k)) := Finite.of_surjective _ hbij.2
  have : Finite (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp r k)))) := inferInstance
  obtain ⟨s, rfl⟩ := hbij.2 t
  have hsord : orderOf s = 2 := by rw [← orderOf_injective _ hbij.1 s, ht]
  have hs : s * s = 1 := by rw [← sq, ← hsord, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hsord
    exact absurd hsord (by norm_num)
  set W := displacement s with hWdef
  set L := (pairedSympForm k r).orthogonal W with hLdef
  set R := flagKernel W L with hRdef
  have hW0 : W ≠ ⊥ := by
    intro hbot
    refine hs1 (statedSp_ext fun v => ?_)
    have h1 : spMat s *ᵥ v - v ∈ W := mem_displacement.mpr ⟨v, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at h1
    rw [h1]
    exact (one_mulVec v).symm
  obtain ⟨-, hRp, hnorm, hcentEq, -⟩ :=
    even_symplectic_isotropic_radical_centralizer hr hf hk W hW0
      (isTotallyIsotropic_displacement hs)
  set Q := R.map (proj r k) with hQdef
  have hlift : ∀ c ∈ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∃ g : StatedSp r k, proj r k g = c ∧ g * s = s * g := by
    intro c hc
    obtain ⟨g, rfl⟩ := hbij.2 c
    refine ⟨g, rfl, hbij.1 ?_⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hc
  have hQC : Q ≤ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      commute_of_mem_flagKernel hs hh]
  have hQp : IsPGroup 2 Q := hRp.map (proj r k)
  have hconjR : ∀ g : StatedSp r k, g * s = s * g → ∀ h ∈ R, g * h * g⁻¹ ∈ R := by
    intro g hgs h hh
    have hgW : ∀ w ∈ W, ((g : GL (Fin r ⊕ Fin r) k) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k)
        *ᵥ (fun i => (1 : k ≃+* k) (w i)) ∈ W := by
      intro w hw
      obtain ⟨v, rfl⟩ := mem_displacement.mp hw
      refine mem_displacement.mpr ⟨spMat g *ᵥ v, ?_⟩
      change spMat s *ᵥ (spMat g *ᵥ v) - spMat g *ᵥ v = spMat g *ᵥ (spMat s *ᵥ v - v)
      rw [mulVec_sub, ← spMat_mul_mulVec, ← spMat_mul_mulVec, hgs]
    have hgn := hnorm g 1 hgW
    rw [map_one, mul_one] at hgn
    have hmem : spInner r k g * spInner r k h * (spInner r k g)⁻¹ ∈ R.map (spInner r k) :=
      (Subgroup.mem_normalizer_iff.mp hgn _).mp ⟨h, hh, rfl⟩
    obtain ⟨h', hh', hh'eq⟩ := hmem
    rw [← map_inv, ← map_mul, ← map_mul] at hh'eq
    rw [← hιinj hh'eq]
    exact hh'
  have hnormQ : ∀ c ∈ Subgroup.centralizer ({proj r k s} : Set (StatedProj (StatedSp r k))),
      ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨g, rfl, hgs⟩ := hlift c hc
    obtain ⟨h, hh, rfl⟩ := hq
    exact ⟨g * h * g⁻¹, hconjR g hgs h hh, by rw [map_mul, map_mul, map_inv]⟩
  refine isCharacteristicP_two_centralizer_of_le hQC hQp hnormQ (fun c hc hcQ => ?_)
  obtain ⟨g, rfl, -⟩ := hlift c hc
  have hgR : ∀ h ∈ R, g * h = h * g := by
    intro h hh
    exact hbij.1 (by rw [map_mul, map_mul]; exact hcQ _ ⟨h, hh, rfl⟩)
  have hmem : spInner r k g ∈ spSemilinearAutGroup r k ⊓ Subgroup.centralizer
      ((R.map (spInner r k) : Subgroup (MulAut (StatedProj (StatedSp r k)))) : Set _) := by
    refine Subgroup.mem_inf.mpr ⟨spInner_mem_spSemilinearAutGroup g,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hgR h hh]
  rw [hcentEq] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  have hzg : (z : StatedSp r k) = g := hιinj hz
  exact ⟨z, hzg ▸ z.2, by rw [hzg]⟩


theorem involutionCentralizersCharTwo_of_psp_model {X : Type} [Group X] {n f : ℕ}
    (h : StatedClassicalModel X .PSp n 2 f) : InvolutionCentralizersCharTwo X := by
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eT⟩⟩ := h
  exact InvolutionCentralizersCharTwo.of_mulEquiv eT
    (involutionCentralizersCharTwo_statedProj_statedSp hf (by omega) hK)

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
