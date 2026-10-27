module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutE6Untw
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6IsoPlaneLarge
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieI5LowTw

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms
  (inner innAutDerived inner_map_congr mem_innAutDerived_congr)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration
open CFSG.LieType.SeitzGeneration.ExcHighThree

section Certificates


theorem inner_of_twistedE6_of_not_dvd {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (h3 : ¬ 3 ∣ ℓ ^ f + 1) {x : MulAut (twistedE6RootGroup K σ)}
    (hx : x ∈ innAutDerived (twistedE6RootGroup K σ)) : x ∈ inner (twistedE6RootGroup K σ) := by
  classical
  haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  haveI : Finite (twistedE6RootGroup K σ) := Subtype.finite
  have hKf : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  haveI : IsCyclic (RingAut K) := (card_ringAut_and_isCyclic hℓ K hKf).2
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hinn : inner (twistedE6RootGroup K σ) ≤ Θ.ker := by
    rw [hker]
    exact le_sup_left
  have hxk : x ∈ Θ.ker :=
    y1out_innAutDerived_le_ker_of_comm Θ (fun a b => y1out_mul_comm_of_isCyclic a b) hinn hx
  rw [hker] at hxk
  have hdiag : twistedE6Diag K σ ≤ inner (twistedE6RootGroup K σ) := by
    have hq := card_twistedE6Diag_map_le_gcd (q := ℓ ^ f) K hK σ hσ
    have hg : Nat.gcd 3 (ℓ ^ f + 1) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    rw [hg] at hq
    have hbot : (twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ)) = ⊥ :=
      (Subgroup.card_le_one_iff_eq_bot _).1 hq
    intro d hd
    have hmem : (QuotientGroup.mk' (twistedE6Inn K σ)) d ∈
        (twistedE6Diag K σ).map (QuotientGroup.mk' (twistedE6Inn K σ)) := ⟨d, hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff d).1 hmem
  rwa [sup_eq_left.2 hdiag] at hxk

theorem kd264Y1OutE6_twisted (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    [Finite (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group]
    (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) ≤ 3)
    {a : MulAut (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group}
    (ha : a ∈ innAutDerived (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group) :
    a ∈ inner (TauCeti.CFSGIndex.lie ⟨.twistedE6 q, hv⟩).Group := by
  classical
  by_cases h3 : 3 ∣ q.card + 1
  · exfalso
    obtain ⟨E, hE, h243⟩ := exists_elemAbelian_243_twistedE6 q hv h3
    have := y1out_five_le_pRank_top_of_card_ge hE h243
    omega
  · obtain ⟨K, hfield, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
    letI := hfield
    haveI : Finite K := Nat.finite_of_card_ne_zero (by
      rw [hK]
      exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
    have h3' : ¬ 3 ∣ q.p ^ q.exponent + 1 := by
      rw [← TauCeti.PrimePower.card_def]
      exact h3
    have ha' : MulAut.congr e a ∈ innAutDerived (twistedE6RootGroup K σ) :=
      (mem_innAutDerived_congr e).2 ha
    have hin := inner_of_twistedE6_of_not_dvd q.prime_p q.exponent_pos hK σ hσ h3' ha'
    rw [← inner_map_congr e] at hin
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hin
    have hb' : b = a := (MulAut.congr e).injective hba
    rw [hb'] at hb
    exact hb

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
