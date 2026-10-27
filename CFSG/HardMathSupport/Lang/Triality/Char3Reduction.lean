module

public import CFSG.LieType.Chevalley.OddTrialityAutomorphismNormalForm
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.Triality

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem fixedSubgroup_inv_eq {G : Type*} [Group G] (α : MulAut G) :
    fixedSubgroup α⁻¹ = fixedSubgroup α := by
  ext x
  change α⁻¹ x = x ↔ α x = x
  constructor
  · intro h
    have h' := congrArg α h
    rw [MulAut.apply_inv_self] at h'
    exact h'.symm
  · intro h
    calc α⁻¹ x = α⁻¹ (α x) := by rw [h]
      _ = x := by simp


theorem exists_conj_fieldActor_of_order_three {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f))
    (α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hα3 : α ^ 3 = 1)
    (hαin : α ∉ inner (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      fixedSubgroup α = fixedSubgroup (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) ∧
        (MulAut.conj g * fieldActor (t := TwistTag.D4) σ σ) ^ 3 = 1 := by
  classical
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, -⟩, hcyc, hcard, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have hσ1 : σ ≠ 1 := by
    intro h
    have hc := CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube hp hf hK σ hσ
    have htop : fixSubfield σ = ⊤ := by
      ext c
      simp [h]
    rw [htop] at hc
    have hc' : Nat.card K = p ^ f := by
      rw [← hc]
      exact (Nat.card_congr Subfield.topEquiv.toEquiv).symm
    have hp1 : 1 < p ^ f := Nat.one_lt_pow (by omega) hp.one_lt
    rw [hK] at hc'
    nlinarith [hp1, pow_pos (lt_trans Nat.zero_lt_one hp1) 2]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  set δ : K ≃+* K := Θ α with hδ
  have hδ3 : δ ^ 3 = 1 := (map_pow Θ α 3).symm.trans ((congrArg Θ hα3).trans (map_one Θ))
  have hδ1 : δ ≠ 1 := fun h => hαin (by
    have hmem : α ∈ Θ.ker := h
    rwa [hker] at hmem)
  have hδord : orderOf δ = 3 := orderOf_eq_prime hδ3 hδ1
  have hδσ : δ = σ ∨ δ = σ⁻¹ := by
    have hfin : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have : Fintype (K ≃+* K) := Fintype.ofFinite _
    have h3dvd : 3 ∣ Fintype.card (K ≃+* K) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      exact Dvd.intro _ rfl
    have hcnt := IsCyclic.card_orderOf_eq_totient (α := K ≃+* K) h3dvd
    have hφ : Nat.totient 3 = 2 := by decide
    set S : Finset (K ≃+* K) := Finset.univ.filter fun a => orderOf a = 3 with hS
    have hσinv : σ ≠ σ⁻¹ := by
      intro h
      have h2 : σ ^ 2 = 1 := by
        calc σ ^ 2 = σ * σ := sq σ
          _ = σ * σ⁻¹ := by rw [← h]
          _ = 1 := mul_inv_cancel σ
      apply hσ1
      calc σ = σ ^ 3 * (σ ^ 2)⁻¹ := by group
        _ = 1 := by rw [hσ3, h2]; simp
    have hsub : ({σ, σ⁻¹} : Finset (K ≃+* K)) ⊆ S := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ha with rfl | rfl
      · exact hσord
      · rw [orderOf_inv]
        exact hσord
    have hSeq : ({σ, σ⁻¹} : Finset (K ≃+* K)) = S :=
      Finset.eq_of_subset_of_card_le hsub (by
        rw [Finset.card_pair hσinv]
        have : S.card = 2 := by rw [hS, hcnt, hφ]
        omega)
    have hδS : δ ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hδord
    rw [← hSeq] at hδS
    simpa using hδS
  obtain ⟨⟨g, δ'⟩, hgδ, -⟩ := hex α
  have hα : α = MulAut.conj g * fieldActor (t := TwistTag.D4) σ δ' := hgδ
  have hδ'eq : δ = δ' := hΘ α g δ' hα
  rcases hδσ with h | h
  · rw [← hδ'eq, h] at hα
    exact ⟨g, by rw [← hα], by rw [← hα]; exact hα3⟩
  · rw [← hδ'eq, h] at hα
    have hEinv : (fieldActor (t := TwistTag.D4) σ σ⁻¹)⁻¹ = fieldActor (t := TwistTag.D4) σ σ := by
      have h1 := fieldActor_mul (t := TwistTag.D4) σ σ⁻¹ σ
      rw [inv_mul_cancel, fieldActor_one] at h1
      exact inv_eq_of_mul_eq_one_right h1.symm
    have hα' : α⁻¹ = MulAut.conj (fieldActor (t := TwistTag.D4) σ σ g⁻¹) *
        fieldActor (t := TwistTag.D4) σ σ := by
      rw [hα, mul_inv_rev, hEinv,
        ← map_inv (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* _) g]
      refine MulEquiv.ext fun x => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul]
      simp only [map_inv]
    refine ⟨fieldActor (t := TwistTag.D4) σ σ g⁻¹, ?_, ?_⟩
    · rw [← hα', fixedSubgroup_inv_eq]
    · rw [← hα', inv_pow, hα3, inv_one]

end CFSG.HardMathSupport.Lang.Triality
