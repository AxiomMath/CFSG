module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedASmall
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedALevi
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusTwistedAKit
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.AGLEmbedding.ToralCensus

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LinearGroups
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary Polynomial Matrix
open CFSG.AGLEmbedding.ParabPrime (perfectJoin perfectJoin_le perfectJoin_perfect)
open scoped Pointwise commutatorElement

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem det_restrict_congr {V : Type*} [AddCommGroup V] [Module K V] {x y : Module.End K V}
    (hxy : x = y) {W : Submodule K V} (hx : ∀ w ∈ W, x w ∈ W) (hy : ∀ w ∈ W, y w ∈ W) :
    LinearMap.det (x.restrict hx) = LinearMap.det (y.restrict hy) := by
  subst hxy
  rfl

theorem det_restrict_of_mem_perfectJoin_sup (h : UnitaryFieldData p f K)
    {J : Subgroup (hypSU h r ε)} {W : Submodule K (HypIndex r ε → K)}
    (hJW : ∀ y ∈ J, ∀ w ∈ W,
      ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈ W)
    {t : hypSU h r ε} (ht : t ∈ perfectJoin J ⊔ hypScalars h r ε)
    (htW : ∀ w ∈ W, (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K)) w ∈ W) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧
      LinearMap.det ((GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
        Module.End K (HypIndex r ε → K)).restrict htW) = (c : K) ^ Module.finrank K W := by
  have hJW' : ∀ y : J, ∀ w ∈ W, (GeneralLinearGroup.toLin ((y : hypSU h r ε) :
      GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)) w ∈ W := by
    intro y w hw
    rw [GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply]
    exact hJW y y.2 w hw
  have hres : ∀ (a b : Module.End K (HypIndex r ε → K)) (ha : ∀ w ∈ W, a w ∈ W)
      (hb : ∀ w ∈ W, b w ∈ W) (hab : ∀ w ∈ W, (a * b) w ∈ W),
      (a * b).restrict hab = a.restrict ha * b.restrict hb :=
    fun _ _ _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl
  let χ : J →* K :=
    { toFun := fun y => LinearMap.det ((GeneralLinearGroup.toLin ((y : hypSU h r ε) :
        GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)).restrict (hJW' y))
      map_one' := by
        rw [det_restrict_congr (y := 1) (by simp) _ (fun w hw => hw)]
        rw [show (1 : Module.End K (HypIndex r ε → K)).restrict (fun w hw => hw) = 1 from
          LinearMap.ext fun _ => Subtype.ext rfl, map_one]
      map_mul' := fun a b => by
        rw [det_restrict_congr (y := (GeneralLinearGroup.toLin ((a : hypSU h r ε) :
          GL (HypIndex r ε) K) : Module.End K (HypIndex r ε → K)) *
            (GeneralLinearGroup.toLin ((b : hypSU h r ε) : GL (HypIndex r ε) K) :
              Module.End K (HypIndex r ε → K))) (by simp) _
          (fun w hw => hJW' a _ (hJW' b w hw)), hres _ _ (hJW' a) (hJW' b), map_mul] }
  have hcomm : ∀ a ∈ ⁅J, J⁆, ∀ haJ : a ∈ J, χ ⟨a, haJ⟩ = 1 := by
    have hle : ⁅J, J⁆ ≤ (χ.toHomUnits.ker).map J.subtype := by
      rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      refine ⟨⁅(⟨g₁, h₁⟩ : J), ⟨g₂, h₂⟩⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
    intro a ha haJ
    obtain ⟨a', ha', rfl⟩ := hle ha
    have := congrArg Units.val ha'
    simpa using this
  have hPJ : perfectJoin J ≤ ⁅J, J⁆ := by
    conv_lhs => rw [← perfectJoin_perfect J]
    exact Subgroup.commutator_mono (perfectJoin_le J) (perfectJoin_le J)
  have ht' : t ∈ (perfectJoin J : Set (hypSU h r ε)) * (hypScalars h r ε : Set (hypSU h r ε)) := by
    rw [← Subgroup.mul_normal]
    exact ht
  obtain ⟨a, haP, z, hz, rfl⟩ := ht'
  obtain ⟨c, hc, -, hzc⟩ := hz
  refine ⟨c, hc, ?_⟩
  have haJ : a ∈ J := perfectJoin_le J haP
  have hzv : ∀ v, (GeneralLinearGroup.toLin (z : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K)) v = (c : K) • v := by
    intro v
    rw [hzc]
    ext i
    simp [GeneralLinearGroup.coe_toLin, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.mulVec_diagonal]
  have hzW : ∀ w ∈ W, (GeneralLinearGroup.toLin (z : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K)) w ∈ W := fun w hw => by rw [hzv]; exact W.smul_mem _ hw
  rw [det_restrict_congr (y := (GeneralLinearGroup.toLin (a : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K)) * (GeneralLinearGroup.toLin (z : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K))) (by simp) _ (fun w hw => hJW' ⟨a, haJ⟩ _ (hzW w hw)),
    hres _ _ (hJW' ⟨a, haJ⟩) hzW, map_mul]
  have hχa : χ ⟨a, haJ⟩ = 1 := hcomm a (hPJ haP) haJ
  have hz1 : (GeneralLinearGroup.toLin (z : GL (HypIndex r ε) K) :
      Module.End K (HypIndex r ε → K)).restrict hzW = (c : K) • LinearMap.id :=
    LinearMap.ext fun w => Subtype.ext (hzv w)
  change χ ⟨a, haJ⟩ * _ = _
  rw [hχa, one_mul, hz1, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem natCast_ne_zero_of_odd_of_charTwo [CharP K 2] {m : ℕ} (hm : Odd m) : (m : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  exact fun h2 => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

theorem pow_add_one_eq_one_of_norm (h : UnitaryFieldData p f K) {c : K} (hc : h.norm c = 1) :
    c ^ (p ^ f + 1) = 1 := by
  rw [pow_succ, mul_comm, ← hc, UnitaryFieldData.norm, h.bar_apply]

theorem nonempty_of_ne_top (h : UnitaryFieldData p f K) {J : Subgroup (hypSU h r ε)}
    (hJ : J ≠ ⊤) {g : hypSU h r ε} {I : Set ℕ}
    (hJI : ∀ y : hypSU h r ε, y ∈ J ↔ ∀ i ∈ I, y • (g • hypFlag h r ε i) = g • hypFlag h r ε i) :
    ∃ i, i ∈ I := by
  by_contra hne
  push Not at hne
  exact hJ (eq_top_iff.mpr fun y _ => (hJI y).mpr fun i hi => absurd hi (hne i))

theorem mulVec_mem_hypFlag_of_mem_stab (h : UnitaryFieldData p f K) {J : Subgroup (hypSU h r ε)}
    {g : hypSU h r ε} {I : Set ℕ}
    (hJI : ∀ y : hypSU h r ε, y ∈ J ↔ ∀ i ∈ I, y • (g • hypFlag h r ε i) = g • hypFlag h r ε i)
    {i : ℕ} (hi : i ∈ I) {y : hypSU h r ε} (hy : y ∈ J) {w : HypIndex r ε → K}
    (hw : w ∈ g • hypFlag h r ε i) :
    ((y : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ w ∈
      g • hypFlag h r ε i := by
  have hyW : y • (g • hypFlag h r ε i) = g • hypFlag h r ε i := (hJI y).mp hy i hi
  rw [← hyW]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, hw, rfl⟩

theorem hypFlag_smul_facts (h : UnitaryFieldData p f K) (hε : ε ≤ 1) (g : hypSU h r ε) {i : ℕ}
    (hi1 : 1 ≤ i) (hir : i ≤ r) :
    (∀ v ∈ g • hypFlag h r ε i, ∀ w ∈ g • hypFlag h r ε i, hypForm h r ε v w = 0) ∧
      Module.finrank K ↥(g • hypFlag h r ε i) = i ∧
        (g • hypFlag h r ε i : Submodule K (HypIndex r ε → K)) ≠ ⊥ := by
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  have hdim : Module.finrank K ↥(g • hypFlag h r ε i) = i := by
    rw [finrank_smul, hchain.1 i hir]
  refine ⟨smul_isotropic g (hchain.2.2 i hir), hdim, fun hbot => ?_⟩
  rw [hbot, finrank_bot] at hdim
  omega

variable [Finite K]

theorem false_of_dvd_add_one_hyp (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmq : m ∣ 2 ^ f + 1)
    {J : Subgroup (hypSU h r ε)} (T : Sylow 2 (hypSU h r ε))
    (hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J)
    (hJ : J ≠ ⊤) {t : hypSU h r ε} (ht : t ^ m ∈ hypScalars h r ε)
    (hfix : ∀ y : hypSU h r ε, Commute y t → y ∈ J) : False := by
  have : CharP K 2 := h.charP
  have : Nonempty (HypIndex r ε) := ⟨.inl ⟨0, hr⟩⟩
  obtain ⟨g, I, hI, hJI⟩ := exists_eq_stab_hypFlag_of_normalizer_le h hr hε T J hTJ
  obtain ⟨i, hi⟩ := nonempty_of_ne_top h hJ hJI
  obtain ⟨hi1, hir⟩ := hI hi
  obtain ⟨hWt, -, hW0⟩ := hypFlag_smul_facts h hε g hi1 hir
  obtain ⟨c, hcn, -, hc⟩ := ht
  have htc : (t : GL (HypIndex r ε) K) ^ m = GeneralLinearGroup.scalar (HypIndex r ε) c := by
    rw [← hc, Subgroup.coe_pow]
  have hsq := squarefree_minpoly_toLin_of_pow_eq_scalar (t : GL (HypIndex r ε) K)
    (natCast_ne_zero_of_odd_of_charTwo (hm.odd_of_ne_two hm2)) htc
  have hself := dualPoly_eq_of_dvd_add_one h (hypPrimaryData h t hsq) hm hm2 hmq
    (pow_add_one_eq_one_of_norm h hcn) (aeval_toLin_X_pow_sub_C _ htc)
  exact hW0 (eq_bot_of_forall_dualPoly_eq h hsq hself hWt
    fun y hy w hw => mulVec_mem_hypFlag_of_mem_stab h hJI hi (hfix y hy) hw)

theorem false_of_dvd_sub_one_of_pow_eq_one (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) {m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmq : m ∣ 2 ^ f - 1)
    {J : Subgroup (hypSU h r ε)} (T : Sylow 2 (hypSU h r ε))
    (hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J)
    (hJ : J ≠ ⊤) {t : hypSU h r ε} (ht : t ^ m = 1)
    (hfix : ∀ y : hypSU h r ε, Commute y t → y ∈ J)
    (hjoin : t ∈ perfectJoin J ⊔ hypScalars h r ε)
    (hcyc : ∀ V : Subgroup (hypSU h r ε), V ≤ J → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (hypSU h r ε), Q ≤ V → IsPGroup m Q → IsCyclic Q) : False := by
  have : CharP K 2 := h.charP
  obtain ⟨g, I, hI, hJI⟩ := exists_eq_stab_hypFlag_of_normalizer_le h hr hε T J hTJ
  have hIne := nonempty_of_ne_top h hJ hJI
  classical
  have hi₀ : Nat.find hIne ∈ I := Nat.find_spec hIne
  have hmin : ∀ i ∈ I, Nat.find hIne ≤ i := fun i hi => Nat.find_min' hIne hi
  obtain ⟨hi₀1, hi₀r⟩ := hI hi₀
  by_cases h3 : 3 ≤ Nat.find hIne
  · obtain ⟨s, rfl⟩ : ∃ s, r = 3 + s := ⟨r - 3, by omega⟩
    obtain ⟨η, hη⟩ := exists_isPrimitiveRoot_twistedA hm (dvd_card_sub_one_of_dvd h (Or.inr hmq))
    exact false_of_levi_three h hε
      (CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le le_rfl) g hJI
      (fun i hi => ⟨h3.trans (hmin i hi), (hI hi).2⟩) hm hη hcyc
  · set i₀ := Nat.find hIne
    obtain ⟨hWt, hdim, hW0⟩ := hypFlag_smul_facts h hε g hi₀1 hi₀r
    have htc : (t : GL (HypIndex r ε) K) ^ m = GeneralLinearGroup.scalar (HypIndex r ε) 1 := by
      rw [map_one, ← Subgroup.coe_pow, ht]
      rfl
    have hsq := squarefree_minpoly_toLin_of_pow_eq_scalar (t : GL (HypIndex r ε) K)
      (natCast_ne_zero_of_odd_of_charTwo (hm.odd_of_ne_two hm2)) htc
    have hx := aeval_toLin_X_pow_sub_C _ htc
    rw [Units.val_one] at hx
    have hxS := toLin_mem_sesqSpecialUnitaryGroup_hyp h t
    have hC := forall_commute_of_hyp h (W := g • hypFlag h r ε i₀)
      fun y hy w hw => mulVec_mem_hypFlag_of_mem_stab h hJI hi₀ (hfix y hy) hw
    have hWx := hC _ hxS (Commute.refl _)
    obtain ⟨c, hcn, hdetW⟩ := det_restrict_of_mem_perfectJoin_sup h
      (fun y hy w hw => mulVec_mem_hypFlag_of_mem_stab h hJI hi₀ hy hw) hjoin hWx
    have hcop : Nat.Coprime m (2 ^ f + 1) := by
      refine (Nat.Prime.coprime_iff_not_dvd hm).mpr fun hd => hm2 ?_
      have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2 : m ∣ 2 := by
        have := Nat.dvd_sub hd hmq
        rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at this
      exact (Nat.prime_dvd_prime_iff_eq hm Nat.prime_two).mp h2
    have hdet1 : LinearMap.det ((GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
        Module.End K (HypIndex r ε → K)).restrict hWx) = 1 := by
      have hx1 : (GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
          Module.End K (HypIndex r ε → K)) ^ m = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← map_pow, ← Subgroup.coe_pow, ht, OneMemClass.coe_one,
          map_one, Units.val_one]
      have h1 : (LinearMap.det ((GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
          Module.End K (HypIndex r ε → K)).restrict hWx)) ^ m = 1 := by
        rw [← map_pow, Module.End.pow_restrict m hWx (fun w hw => by rw [hx1]; exact hw)]
        rw [det_restrict_congr (y := 1) hx1 _ (fun w hw => hw)]
        rw [show (1 : Module.End K (HypIndex r ε → K)).restrict (fun w hw => hw) = 1 from
          LinearMap.ext fun _ => Subtype.ext rfl, map_one]
      have h2 : (LinearMap.det ((GeneralLinearGroup.toLin (t : GL (HypIndex r ε) K) :
          Module.End K (HypIndex r ε → K)).restrict hWx)) ^ (2 ^ f + 1) = 1 := by
        rw [hdetW, ← pow_mul, mul_comm, pow_mul, pow_add_one_eq_one_of_norm h hcn, one_pow]
      have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
      rwa [hcop.gcd_eq_one, pow_one] at this
    exact false_of_finrank_le_two h (hypPrimaryData h t hsq)
      (mem_sesqSpecialUnitaryGroup.mp hxS).2 hm hmq hx hWt hC hW0 (by omega) hWx hdet1

theorem false_of_dvd_sub_one_hyp (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmq : m ∣ 2 ^ f - 1)
    {J : Subgroup (hypSU h r ε)} (T : Sylow 2 (hypSU h r ε))
    (hTJ : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set (hypSU h r ε)) ≤ J)
    (hJ : J ≠ ⊤) {t : hypSU h r ε} (ht : t ^ m ∈ hypScalars h r ε)
    (hfix : ∀ y : hypSU h r ε, Commute y t → y ∈ J)
    (hjoin : t ∈ perfectJoin J ⊔ hypScalars h r ε)
    (hcyc : ∀ V : Subgroup (hypSU h r ε), V ≤ J → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (hypSU h r ε), Q ≤ V → IsPGroup m Q → IsCyclic Q) : False := by
  have hcop : (Nat.card (hypScalars h r ε)).Coprime m := by
    rw [card_hypScalars h (by omega)]
    refine Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right _ _) ?_
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).mpr fun hd => hm2 ?_)
    have hq : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have h2 : m ∣ 2 := by
      have := Nat.dvd_sub hd hmq
      rwa [show 2 ^ f + 1 - (2 ^ f - 1) = 2 by omega] at this
    exact (Nat.prime_dvd_prime_iff_eq hm Nat.prime_two).mp h2
  set s := (powCoprime hcop).symm ⟨t ^ m, ht⟩
  have hs : (s : hypSU h r ε) ^ m = t ^ m := by
    have := (powCoprime hcop).apply_symm_apply ⟨t ^ m, ht⟩
    rw [powCoprime_apply] at this
    rw [← Subgroup.coe_pow, this]
  have hsc : ∀ y : hypSU h r ε, Commute y (s : hypSU h r ε) := fun y =>
    ((Subgroup.mem_center_iff.mp (normOneScalars_le_center h _ _ s.2)) y)
  refine false_of_dvd_sub_one_of_pow_eq_one h hr hε hm hm2 hmq T hTJ hJ
    (t := t * (s : hypSU h r ε)⁻¹) ?_ (fun y hy => hfix y ?_) ?_ hcyc
  · rw [(hsc t).inv_right.mul_pow, inv_pow, hs, mul_inv_cancel]
  · simpa using hy.mul_right (hsc y)
  · exact Subgroup.mul_mem _ hjoin (Subgroup.mem_sup_right (Subgroup.inv_mem _ s.2))

end CFSG.AGLEmbedding.ToralCensus
