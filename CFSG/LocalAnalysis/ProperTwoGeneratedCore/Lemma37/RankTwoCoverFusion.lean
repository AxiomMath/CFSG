module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverSetup

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {J : Type*} [Group J] [Finite J]

theorem exists_conj_of_card_le (Q : Sylow 2 J) {P' : Subgroup J} (hP' : IsPGroup 2 P')
    (hcard : Nat.card (Q : Subgroup J) ≤ Nat.card P') :
    ∃ x : J, (∀ q ∈ (Q : Subgroup J), x * q * x⁻¹ ∈ P') ∧
      ∀ g ∈ P', x⁻¹ * g * x ∈ (Q : Subgroup J) := by
  obtain ⟨S, hS⟩ := hP'.exists_le_sylow
  have hSQ : Nat.card (S : Subgroup J) = Nat.card (Q : Subgroup J) := by
    rw [S.card_eq_multiplicity, Q.card_eq_multiplicity]
  have hPS : P' = S := Subgroup.eq_of_le_of_card_ge hS (hSQ ▸ hcard)
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq J Q S
  refine ⟨x, fun q hq => ?_, fun g hg => ?_⟩
  · rw [hPS, ← hx, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul q (MulAut.conj x) _ hq
  · rw [hPS, ← hx, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg
    simpa [MulAut.smul_def, MulAut.conj_apply] using hg

variable {Q : Sylow 2 J} {X : Type*} [Group X]
  {e : (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) ≃* X}

theorem coverHom_mem_center (y : (Q : Subgroup J))
    (hy : ∀ q : (Q : Subgroup J), (q : J) * y * (q : J)⁻¹ * (y : J)⁻¹ ∈ Subgroup.center J) :
    coverHom Q e y ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨q, rfl⟩ := coverHom_surjective (e := e) x
  have h1 : coverHom Q e (q * y * q⁻¹ * y⁻¹) = 1 := (coverHom_eq_one_iff _).mpr (hy q)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem orderOf_coverHom_eq_two {y : (Q : Subgroup J)}
    (hy2 : (y : J) * y ∈ Subgroup.center J) (hyZ : (y : J) ∉ Subgroup.center J) :
    orderOf (coverHom Q e y) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow, pow_two]
    exact (coverHom_eq_one_iff _).mpr hy2
  · rw [Ne, coverHom_eq_one_iff]
    exact hyZ

theorem sq_mem_center_of_orderOf_coverHom {y : (Q : Subgroup J)}
    (hy : orderOf (coverHom Q e y) = 2) :
    (y : J) * y ∈ Subgroup.center J ∧ (y : J) ∉ Subgroup.center J := by
  have hsq : coverHom Q e y ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (coverHom Q e y)
    rwa [hy] at h
  constructor
  · exact (coverHom_eq_one_iff (e := e) (y * y)).mp (by rw [map_mul, ← pow_two, hsq])
  · rw [← coverHom_eq_one_iff (e := e)]
    intro h
    rw [h, orderOf_one] at hy
    exact absurd hy (by norm_num)

omit [Finite J] in
theorem commutator_quotient_center_eq_top (hperf : commutator J = ⊤) :
    commutator (J ⧸ Subgroup.center J) = ⊤ := by
  rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective
    (Subgroup.center J)), ← Subgroup.map_commutator, ← commutator_def, hperf]

theorem exists_conj_coverHom_mem (hperf : commutator J = ⊤) (hZ : IsPGroup 2 (Subgroup.center J))
    {B : Subgroup X} (hB : B.index = 2)
    {t : (Q : Subgroup J)} (ht2 : (t : J) * t ∈ Subgroup.center J)
    (htZ : (t : J) ∉ Subgroup.center J) :
    ∃ g : J, ∃ hy : g⁻¹ * t * g ∈ (Q : Subgroup J), coverHom Q e ⟨g⁻¹ * t * g, hy⟩ ∈ B := by
  set H : Subgroup (J ⧸ Subgroup.center J) :=
    (B.comap e.toMonoidHom).map (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)).subtype with hH
  have hHS : H ≤ (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) := Subgroup.map_subtype_le _
  have hHidx : H.relIndex (centralSylow Q : Subgroup (J ⧸ Subgroup.center J)) = 2 := by
    rw [Subgroup.relIndex, hH, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _),
      Subgroup.index_comap_of_surjective _ e.surjective, hB]
  have hτ : orderOf ((t : J) : J ⧸ Subgroup.center J) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact ht2
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact htZ
  obtain ⟨g', hg'⟩ := exists_conj_mem_of_relIndex_eq_two
    (commutator_quotient_center_eq_top hperf) (centralSylow Q) hHS hHidx hτ
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
  obtain ⟨⟨s, hsS⟩, hsB, hs⟩ := hg'
  change s = _ at hs
  obtain ⟨q, hq, hqs⟩ := id hsS
  have hmk : ((g⁻¹ * t * g : J) : J ⧸ Subgroup.center J) = s := by
    rw [hs, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hyq : q⁻¹ * (g⁻¹ * t * g) ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk, ← hqs,
      QuotientGroup.mk'_apply, inv_mul_cancel]
  have hyQ : g⁻¹ * t * g ∈ (Q : Subgroup J) := by
    have := (Q : Subgroup J).mul_mem hq (hZ.le_sylow_of_normal Q hyq)
    rwa [mul_inv_cancel_left] at this
  refine ⟨g, hyQ, ?_⟩
  rw [coverHom_apply]
  have heq : (⟨((g⁻¹ * t * g : J) : J ⧸ Subgroup.center J), mk_mem_centralSylow Q ⟨_, hyQ⟩⟩ :
      (centralSylow Q : Subgroup (J ⧸ Subgroup.center J))) = ⟨s, hsS⟩ := Subtype.ext hmk
  rw [heq]
  exact Subgroup.mem_comap.mp hsB

end CFSG.ProperTwoGeneratedCore.Lemma37
