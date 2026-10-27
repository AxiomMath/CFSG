module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsDihedral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup

theorem sylow_two_dihedral_of_equiv {Y : Type*} [Group Y] [Finite Y] {F : Type*} [Field F]
    [Finite F] (e : Y ≃* PSL2 F) (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 Y) :
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((T : Subgroup Y) ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 (PSL2 F) := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective T
  obtain ⟨m, hm, ⟨ψ⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hodd T'
  have hT' : (T' : Subgroup (PSL2 F)) = (T : Subgroup Y).map e.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  refine ⟨m, hm, ⟨(e.subgroupMap (T : Subgroup Y)).trans ?_⟩⟩
  exact (MulEquiv.subgroupCongr hT'.symm).trans ψ

theorem card_inf_centralizer_eq {G D : Type*} [Group G] [Group D] (H : Subgroup G)
    (φ : H ≃* D) : Nat.card ↥(H ⊓ centralizer (H : Set G)) = Nat.card (center D) := by
  rw [← Nat.card_congr (centerCongr φ).toEquiv]
  refine Nat.card_congr ⟨fun x => ⟨⟨x, x.2.1⟩, mem_center_iff.mpr fun g => Subtype.ext ?_⟩,
    fun x => ⟨x.1, x.1.2, mem_centralizer_iff.mpr fun g hg => ?_⟩, fun x => rfl, fun x => rfl⟩
  · exact mem_centralizer_iff.mp x.2.2 g g.2
  · exact congrArg Subtype.val (mem_center_iff.mp x.2 ⟨g, hg⟩)

theorem dihedral_sylow_conclusions {G : Type*} [Group G] (T : Subgroup G) {m : ℕ} (hm : 2 ≤ m)
    (φ : T ≃* DihedralGroup (2 ^ m)) :
    Nat.card ↥(T ⊓ centralizer (T : Set G)) = 2 ∧
      (∃ t ∈ T, t * t ≠ 1 ∧ t * t ∈ centralizer (T : Set G)) ∧
      ∀ t ∈ T, ∃ i ∈ T, ∃ j ∈ T, i * i = 1 ∧ j * j = 1 ∧ t = i * j := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_inf_centralizer_eq T φ]
    apply card_center_dihedral
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    · rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
  · obtain ⟨d, hd1, hdc⟩ := dihedral_exists_sq_central hm
    refine ⟨(φ.symm d : G), (φ.symm d).2, ?_, ?_⟩
    · intro h
      apply hd1
      have h' : φ.symm d * φ.symm d = 1 := Subtype.ext h
      rw [← map_mul, ← map_one φ.symm] at h'
      exact φ.symm.injective h'
    · rw [mem_centralizer_iff]
      intro g hg
      have hc := mem_center_iff.mp hdc (φ ⟨g, hg⟩)
      have hc' : φ.symm (φ ⟨g, hg⟩ * (d * d)) = φ.symm (d * d * φ ⟨g, hg⟩) := by rw [hc]
      simp only [map_mul, MulEquiv.symm_apply_apply] at hc'
      exact congrArg Subtype.val hc'
  · intro t ht
    obtain ⟨i, j, hi, hj, hij⟩ := dihedral_eq_mul_involutions (φ ⟨t, ht⟩)
    refine ⟨(φ.symm i : G), (φ.symm i).2, (φ.symm j : G), (φ.symm j).2, ?_, ?_, ?_⟩
    · have : φ.symm i * φ.symm i = 1 := by rw [← map_mul, hi, map_one]
      exact congrArg Subtype.val this
    · have : φ.symm j * φ.symm j = 1 := by rw [← map_mul, hj, map_one]
      exact congrArg Subtype.val this
    · have : (⟨t, ht⟩ : T) = φ.symm i * φ.symm j := by
        rw [← map_mul, ← hij, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this

theorem l2Sylow_conclusions {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel Y .PSL 2 p f) (T : Sylow 2 Y) (hT : 8 ≤ Nat.card T) :
    Nat.card ↥((T : Subgroup Y) ⊓ centralizer ((T : Subgroup Y) : Set Y)) = 2 ∧
      (∃ t ∈ (T : Subgroup Y), t * t ≠ 1 ∧ t * t ∈ centralizer ((T : Subgroup Y) : Set Y)) ∧
      ∀ t ∈ (T : Subgroup Y), ∃ i ∈ (T : Subgroup Y), ∃ j ∈ (T : Subgroup Y),
        i * i = 1 ∧ j * j = 1 ∧ t = i * j := by
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  obtain ⟨m, -, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv e (isOddPrimePower_of hp hp2 hf hF) T
  have hcard : Nat.card T = 2 ^ (m + 1) := by
    rw [Nat.card_congr φ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  have hm : 2 ≤ m := by
    rw [hcard] at hT
    by_contra h
    push Not at h
    interval_cases m <;> simp_all
  exact dihedral_sylow_conclusions (T : Subgroup Y) hm φ

theorem l2InvPair_conclusion {Y : Type} [Group Y] [Finite Y] {p f : ℕ} (hp2 : p ≠ 2)
    (hY : Blueprint.LieModel Y .PSL 2 p f) (t : Y) (ht : orderOf t = 2) :
    ∃ u : Y, orderOf u = 2 ∧ u ≠ t ∧ u * t = t * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hY
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨T, hT⟩ := hz.exists_le_sylow
  have htT : t ∈ (T : Subgroup Y) := hT (mem_zpowers t)
  obtain ⟨m, hm, ⟨φ⟩⟩ := sylow_two_dihedral_of_equiv e (isOddPrimePower_of hp hp2 hf hF) T
  have hx : φ ⟨t, htT⟩ * φ ⟨t, htT⟩ = 1 := by
    rw [← map_mul, ← map_one φ]
    congr 1
    exact Subtype.ext htt
  have hx1 : φ ⟨t, htT⟩ ≠ 1 := by
    intro h
    rw [← map_one φ] at h
    have := congrArg Subtype.val (φ.injective h)
    simp only [OneMemClass.coe_one] at this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨y, hy, hy1, hyx, hyc⟩ := dihedral_exists_commuting_involution
    (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩)
    (by calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm) _ hx hx1
  refine ⟨(φ.symm y : Y), ?_, ?_, ?_⟩
  · have hyy : (φ.symm y : Y) * φ.symm y = 1 := by
      have : φ.symm y * φ.symm y = 1 := by rw [← map_mul, hy, map_one]
      exact congrArg Subtype.val this
    have hy1' : (φ.symm y : Y) ≠ 1 := by
      intro h
      apply hy1
      have : φ.symm y = 1 := Subtype.ext h
      rw [← map_one φ.symm] at this
      exact φ.symm.injective this
    exact orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1'
  · intro h
    apply hyx
    have : φ.symm y = ⟨t, htT⟩ := Subtype.ext h
    rw [← this, MulEquiv.apply_symm_apply]
  · have : φ.symm y * ⟨t, htT⟩ = ⟨t, htT⟩ * φ.symm y := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hyc]
    exact congrArg Subtype.val this

end CFSG.ComponentClassification.AutL2Facts
