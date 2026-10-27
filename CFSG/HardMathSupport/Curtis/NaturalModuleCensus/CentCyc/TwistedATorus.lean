module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.TwistedACover
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.TwistedAStable
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedA
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc.Reduce

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.QuasithinUnique CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ToralCensus
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect le_perfectJoin)
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus
open CFSG.LinearGroups Matrix
open scoped commutatorElement Pointwise

theorem forall_commute_mem_of_no_perfect {f : ℕ} {K : Type} [Field K] [Finite K] {r ε : ℕ}
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) (hr : 1 ≤ r) (hε : ε ≤ 1) (T : Sylow 2 (hypSU h r ε))
    {J : Subgroup (hypSU h r ε)}
    (hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J)
    {t : hypSU h r ε} (htJ : t ∈ J)
    (hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))))
    (hperf : ∀ V : Subgroup (hypSU h r ε), (∀ w ∈ V, Commute w t) → ⁅V, V⁆ = V → V = ⊥) :
    ∀ y : hypSU h r ε, Commute y t → y ∈ J := by
  have : CharP K 2 := h.charP
  obtain ⟨g, I, hI, hJI⟩ := exists_eq_stab_hypFlag_of_normalizer_le h hr hε T J hTJ
  intro y hy
  rw [hJI]
  intro i hi
  set W : Submodule K (HypIndex r ε → K) := g • hypFlag h r ε i with hW
  have hWt : ∀ w ∈ W, ((t : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈
      W := fun w hw => mulVec_mem_hypFlag_of_mem_stab h hJI hi htJ hw
  have hle : y • W ≤ W := by
    intro m hm
    obtain ⟨w, hw, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    exact forall_mulVec_mem_of_no_perfect h hf t hsq hperf hWt hy w hw
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.finrank_smul (h := h)])

theorem false_of_centCycBar_torus_twistedA {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hX : IsLieOfTorus IdxTwistedA p X) {J : Subgroup X} {v : X}
    (h : CentCycBar J p v) : False := by
  obtain ⟨d, hd, hnt, ⟨e⟩⟩ := hX
  obtain ⟨r₀, q, hdq⟩ := exists_eq_twistedA hd
  obtain ⟨K, _, _, f, hK, r, ε, cov, hr, hε, hq, hcov, hπker⟩ := exists_hypCoverBar d hd e
  have hqf : q.card = 2 ^ f := hq r₀ q hdq
  rw [hdq] at hnt
  simp only [IndexTorusFree, not_or, not_not] at hnt
  obtain ⟨hq2, hpq⟩ := hnt
  rw [hqf] at hq2 hpq
  have hf2 : 2 ≤ f := by
    have := hK.one_le
    by_contra hlt
    exact hq2 (by rw [show f = 1 by omega]; norm_num)
  have hp2 : p ≠ 2 := by omega
  have : CharP K 2 := hK.charP
  have hZc : hypScalars hK r ε ≤ Subgroup.center (hypSU hK r ε) :=
    normOneScalars_le_center hK (hypSU hK r ε) (2 * r + ε)
  have hkereq : cov.ker = hypScalars hK r ε := by
    ext g
    rw [MonoidHom.mem_ker, hπker]
  have hker : cov.ker ≤ Subgroup.center (hypSU hK r ε) := hkereq ▸ hZc
  obtain ⟨S₀, hS₀, -⟩ := h.parab
  obtain ⟨T, hT⟩ := exists_sylow_normalizer_le_comap_bar hcov S₀ hS₀
  obtain ⟨t, htv⟩ := hcov v
  have htm : t ^ p ∈ hypScalars hK r ε := by
    rw [← hπker, map_pow, htv]
    exact h.pow
  have hJtop : J.comap cov ≠ ⊤ := by
    intro htop
    apply h.ne_top
    rw [← Subgroup.map_comap_eq_self_of_surjective hcov J, htop, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hcov]
  have htJ : t ∈ J.comap cov := by
    rw [Subgroup.mem_comap, htv]
    exact perfectJoin_le J h.join
  have hsq : Squarefree (minpoly K
      (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K))) := by
    obtain ⟨c, hcn, -, hc⟩ := htm
    have htc : (t : GL (HypIndex r ε) K) ^ p = GeneralLinearGroup.scalar (HypIndex r ε) c := by
      rw [← hc, Subgroup.coe_pow]
    exact squarefree_minpoly_toLin_of_pow_eq_scalar (t : GL (HypIndex r ε) K)
      (natCast_ne_zero_of_odd_of_charTwo (hp.odd_of_ne_two hp2)) htc
  have hfix : ∀ y : hypSU hK r ε, Commute y t → y ∈ J.comap cov :=
    forall_commute_mem_of_no_perfect hK hf2 hr hε T hT htJ hsq fun V hVc hV =>
      eq_bot_of_perfect_commute hker htv h.triv hVc hV
  rcases prime_dvd_sub_or_add_of_dvd_sq_sub_one hp hpq with h1 | h1
  · refine false_of_dvd_sub_one_hyp hK hr hε hp hp2 h1 T hT hJtop htm hfix ?_ ?_
    · have := mem_perfectJoin_comap_sup hcov hker (J := J) (t := t) (htv ▸ h.join)
      rwa [hkereq] at this
    · refine cycPerfect_comap_bar (Z := hypScalars hK r ε) hπker ?_ h.cyc
      rw [card_hypScalars hK (by omega)]
      exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _)
        (coprime_two_pow_add_one_of_dvd_sub_one hp hp2 h1)
  · exact false_of_dvd_add_one_hyp hK hr hε hp hp2 h1 T hT hJtop htm hfix

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
