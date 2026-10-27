module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6KLFixed
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6KLFusion
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6KLLevi

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.GF2n.Stroth80


variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem false_of_isKLConfig_stdRepC_zero [CharP K 2] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {a : ℕ}
    {N A : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)}
    (h : IsKLConfig (stdRepC (apply_apply_eq hK hσ) 0) a N A) : False := by
  have hLN := su6Levi_subgroupOf_le_of_isA2PlaneKernel hf hk hK hσ h.kernel
  have hAU := le_rootSubgroup_of_isKLConfig_twistedE6 hf hk hK hσ h hLN
    (le_tRadical_of_isKLConfig hf hk hK hσ h hLN)
  obtain ⟨u, huL, hu3, huθ⟩ := exists_mem_su6Levi_orderOf_eq_three (K := K) σ
  have hu1 : u = 1 := h.eq_one u (hLN huL) (by rw [hu3]; exact ⟨1, rfl⟩) fun x hx => by
    obtain ⟨c, hc⟩ := mem_rootSubgroup.1 (hAU x hx)
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
    exact huθ c
  rw [hu1, orderOf_one] at hu3
  omega

end CFSG.SeitzReduction.TwistedE6Pilot

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SeitzReduction

theorem false_of_isKLConfig_of_lieModel_twistedE6
    {X : Type} [Group X] [Finite X] {m x a : ℕ}
    (hX : LieModel X .twistedE6 m 2 x) {t : X} {N A : Subgroup X}
    (h : IsKLConfig t a N A) : False := by
  have hM := hX.chevalleyExceptionalModel (by decide)
  obtain ⟨-, hf, -⟩ := hM.1
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hM
  have : CharP K 2 := TwistedE6Pilot.charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk := CFSG.LieType.Steinberg.card_fixedSubfield (p := 2) (f := x) hK
  have hσ' : ∀ c, σ.toRingHom c = c ^ 2 ^ x := hσ
  obtain ⟨g, hg⟩ := TwistedE6Pilot.exists_conj_eq_stdRepC_zero_of_isStrothInvolution hf hK hσ'
    (h.map e).involution
  have h' := (h.map e).map (MulAut.conj g)
  rw [MulAut.conj_apply, hg] at h'
  exact TwistedE6Pilot.false_of_isKLConfig_stdRepC_zero hf hk hK hσ' h'

end CFSG.RankThree.GF2n.Stroth80
