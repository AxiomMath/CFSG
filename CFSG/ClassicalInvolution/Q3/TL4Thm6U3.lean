module

public import CFSG.ClassicalInvolution.Q3.TL4Thm6Out
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Exit
public import CFSG.ClassicalInvolution.Q3.TL4MF163Gam
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L5U5
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import CFSG.ClassicalInvolution.Q3.TL4Thm6Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Thm6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic QuaternionGroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exitIdent_u3Ne3 : ExitIdent TA3.SmallU3Ne3 := by
  intro Y _ _ _ hnab hPF R S t hD hc
  obtain ⟨p, f, hp, hp2, hf, h3, hm⟩ := hPF
  have hL : CFSG.Blueprint.LieModel ↥(genFittingFStar Y) .PSU 3 p f := Or.inl ⟨by decide, hm⟩
  have : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hC := Nobq.centralizer_genFittingFStar_eq_bot hnab
  set N := genFittingFStar Y with hN
  have hg : Odd (Nat.gcd 3 (p ^ f + 1)) := (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  obtain ⟨htN, -⟩ :=
    TA3.TightDatum.exists_cyclic4_of_outTwoCyclic hD hC (TA3.outTwoCyclic_PSU hm hg)
  obtain ⟨⟨hℓ, hm1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hU : UnitaryFieldData p f K := ⟨hℓ, hm1, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(3 = 3 ∧ p ^ f = 2) := fun ⟨_, h2⟩ => hne (by rw [h2])
  have : Finite K := hU.finite
  have hCg : IsPrimeFormGram (1 : GL (Fin 3) K) := isPrimeFormGram_one
  obtain ⟨⟨eT⟩, -, -, -, -, -, -, hFker, -, hinn, -⟩ :=
    unitary_prime_form_full_semilinear_realization hU hCg le_rfl hq
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order hU le_rfl hq
  set P := primeFormP hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hP
  let e' : ↥N ≃* P := (e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner P with hI
  set D := primeFormD hU ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hDdef
  set F := primeFormFieldFactor hU hCg le_rfl hq with hFdef
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hU.prime K hU.card).2
  have : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun _ _ h => RingEquiv.ext (congrFun h)
  have hFc : ∀ σ τ : RingAut K, σ * τ = τ * σ := fun σ τ => IsCyclic.commGroup.mul_comm σ τ
  set ι : Y →* MulAut P := transConj N e' with hι
  have hιN : ∀ y, ι y ∈ I ↔ y ∈ N := transConj_mem_inner_iff e' hC
  obtain ⟨eS⟩ := hc.1
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  let eQ : S₀ ≃* QuaternionGroup 2 :=
    ((S : Subgroup R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans eS
  have hS₀R : S₀ ≤ R := Subgroup.map_subtype_le _
  have hsq : ∀ s ∈ S₀, s ^ 2 ∈ N := by
    intro s hs
    have hq8 : ∀ q : QuaternionGroup 2, q ^ 2 = 1 ∨ q ^ 2 = a 2 := by decide
    have h2 : orderOf ((eQ.symm (a 2) : S₀) : Y) = 2 := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by decide) (by decide)
    have hta : ((eQ.symm (a 2) : S₀) : Y) = t :=
      hD.eq_of_orderOf_eq_two (hS₀R (eQ.symm (a 2)).2) h2
    have hs' : s ^ 2 = ((eQ.symm ((eQ ⟨s, hs⟩) ^ 2) : S₀) : Y) := by
      rw [map_pow, MulEquiv.symm_apply_apply]
      rfl
    rcases hq8 (eQ ⟨s, hs⟩) with h | h
    · rw [hs', h, map_one]
      exact N.one_mem
    · rw [hs', h, hta]
      exact htN
  have : Finite P := Finite.of_equiv _ e'.toEquiv
  have : Finite (MulAut P) :=
    Finite.of_injective (fun α : MulAut P => (α : P → P)) fun _ _ h => MulEquiv.ext (congrFun h)
  set Ω : Y →* Outer P := (QuotientGroup.mk' I).comp ι with hΩ
  set Dbar := D.map (QuotientGroup.mk' I) with hDbar
  have hker : Ω.ker = N := by
    ext y
    rw [MonoidHom.mem_ker, hΩ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hιN y
  have hDin : ∀ y, ι y ∈ D → Ω y ∈ Dbar := fun y hy => ⟨ι y, hy, rfl⟩
  have hD3 : Nat.card Dbar ∣ 3 := by
    have hk : ((QuotientGroup.mk' I).comp D.subtype).ker = I.subgroupOf D := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hr : ((QuotientGroup.mk' I).comp D.subtype).range = Dbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hcD : Nat.card Dbar = Nat.card (D ⧸ I.subgroupOf D) := by
      rw [← hr]
      exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk).symm.trans
        (QuotientGroup.quotientKerEquivRange _)).toEquiv).symm
    rw [hcD, hcard]
    exact Nat.gcd_dvd_left 3 _
  have hcomm : ∀ x y : Outer P, x * y * x⁻¹ * y⁻¹ ∈ Dbar := by
    intro x y
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨β, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : α * β * α⁻¹ * β⁻¹ ∈ D := by
      rw [← hFker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
        hFc (F α) (F β)]
      group
    exact ⟨_, hmem, rfl⟩
  have hF2 : ∀ s ∈ S₀, F (ι s) * F (ι s) = 1 := fun s hs => by
    have h1 : ι (s ^ 2) ∈ D := hID ((hιN _).mpr (hsq s hs))
    rw [← hFker, MonoidHom.mem_ker, map_pow, map_pow, sq] at h1
    exact h1
  have hS : ∀ s₁ ∈ S₀, ∀ s₂ ∈ S₀, Ω s₁ ∉ Dbar → Ω s₂ ∉ Dbar → Ω (s₁⁻¹ * s₂) ∈ Dbar := by
    intro s₁ h₁ s₂ h₂ hn₁ hn₂
    have hF1 : ∀ s, Ω s ∉ Dbar → F (ι s) ≠ 1 := fun s hn h =>
      hn (hDin s (by rw [← hFker]; exact h))
    have heq := MF163.eq_of_mul_self_eq_one (hF2 s₁ h₁) (hF2 s₂ h₂) (hF1 s₁ hn₁) (hF1 s₂ hn₂)
    apply hDin
    rw [← hFker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, heq, inv_mul_cancel]
  have hS2 : ∀ s ∈ S₀, Ω (s ^ 2) ∈ Dbar := fun s hs => by
    have h := hsq s hs
    rw [← hker, MonoidHom.mem_ker] at h
    rw [h]
    exact Dbar.one_mem
  have hidx := index_dvd_six_of_hom Ω hker Dbar hD3 hcomm
    (fun M h => hD.eq_top_of_conj hc.2.1 h) hS hS2
  exact Or.inl ⟨p, f, hp, hp2, Or.inr ⟨Or.inr (lieModel_fstarQuot hnab (Or.inr rfl) hL), hidx⟩⟩

end CFSG.ClassicalInvolution.Q3.TL4.Thm6
