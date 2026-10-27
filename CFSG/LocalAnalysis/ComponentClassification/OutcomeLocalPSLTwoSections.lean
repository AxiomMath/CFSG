module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

public section

namespace CFSG.ComponentClassification.OutcomeLocal

open CFSG.Assembly.LowTwoRank

theorem card_le_two_of_isCyclic_of_sq_eq_one {Z : Type*} [Group Z] [IsCyclic Z]
    (h : ∀ z : Z, z ^ 2 = 1) : Nat.card Z ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h)

theorem card_le_four_of_sylow_two_cyclic {G H Q : Type*} [Group G] [Group H] [Group Q]
    [Finite G] [IsElementaryAbelian 2 Q]
    (hS : ∀ P : Sylow 2 G, ∃ C : Subgroup G, C ≤ P ∧ IsCyclic C ∧ C.relIndex P ≤ 2)
    {ι : H →* G} (hι : Function.Injective ι) {ψ : H →* Q} (hψ : Function.Surjective ψ) :
    Nat.card Q ≤ 4 := by
  have : Finite H := Finite.of_injective ι hι
  have : Finite Q := Finite.of_surjective ψ hψ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 Q := IsElementaryAbelian.isPGroup 2 Q
  obtain ⟨U⟩ : Nonempty (Sylow 2 H) := inferInstance
  have hUQ : (U : Subgroup H).map ψ = ⊤ := by
    obtain ⟨n, hn⟩ := hQ.index ((U : Subgroup H).map ψ)
    have hdvd : ((U : Subgroup H).map ψ).index ∣ (U : Subgroup H).index :=
      Subgroup.index_map_dvd _ hψ
    rw [← Subgroup.index_eq_one, hn]
    cases n with
    | zero => rfl
    | succ n =>
      exact absurd ((dvd_pow_self 2 n.succ_ne_zero).trans (hn ▸ hdvd)) U.not_dvd_index
  obtain ⟨P, hP⟩ := (U.isPGroup'.map ι).exists_le_sylow
  obtain ⟨C, -, hC, hCidx⟩ := hS P
  set CU : Subgroup H := (U : Subgroup H) ⊓ C.comap ι with hCU
  have hCUcyc : IsCyclic CU := by
    have hle : CU.map ι ≤ C := Subgroup.map_le_iff_le_comap.mpr inf_le_right
    have : IsCyclic (CU.map ι) := Subgroup.isCyclic_of_le hle
    exact isCyclic_of_injective (CU.equivMapOfInjective ι hι).toMonoidHom
      (CU.equivMapOfInjective ι hι).injective
  have hCUidx : CU.relIndex U ≤ 2 := by
    rw [hCU, Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
    exact (Subgroup.relIndex_le_of_le_right hP (Subgroup.index_ne_zero_of_finite)).trans hCidx
  set CQ : Subgroup Q := CU.map ψ with hCQ
  have hCQcyc : IsCyclic CQ :=
    isCyclic_of_surjective (ψ.subgroupMap CU) (ψ.subgroupMap_surjective CU)
  have hCQcard : Nat.card CQ ≤ 2 := by
    refine card_le_two_of_isCyclic_of_sq_eq_one fun z => Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 Q) z
  have hψU : Function.Surjective (ψ.comp (U : Subgroup H).subtype) := by
    intro q
    have hq : q ∈ (U : Subgroup H).map ψ := hUQ ▸ Subgroup.mem_top q
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨⟨u, hu⟩, rfl⟩
  have hmap : (CU.subgroupOf U).map (ψ.comp (U : Subgroup H).subtype) = CQ := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hCQidx : CQ.index ≤ 2 := by
    have hdvd := Subgroup.index_map_dvd (CU.subgroupOf U) hψU
    rw [hmap] at hdvd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd).trans
      hCUidx
  rw [← CQ.card_mul_index]
  exact Nat.mul_le_mul hCQcard hCQidx

open DihedralGroup in
theorem dihedral_rotations_data (n : ℕ) [NeZero n] :
    IsCyclic (Subgroup.zpowers (r 1 : DihedralGroup n)) ∧
      (Subgroup.zpowers (r 1 : DihedralGroup n)).Normal ∧
      (Subgroup.zpowers (r 1 : DihedralGroup n)).index = 2 ∧
      (sr 0 : DihedralGroup n) ∉ Subgroup.zpowers (r 1) ∧ orderOf (sr 0 : DihedralGroup n) = 2 ∧
      ∀ c ∈ Subgroup.zpowers (r 1 : DihedralGroup n), sr 0 * c * (sr 0)⁻¹ = c⁻¹ := by
  have hidx : (Subgroup.zpowers (r 1 : DihedralGroup n)).index = 2 := by
    have h := (Subgroup.zpowers (r 1 : DihedralGroup n)).card_mul_index
    rw [Nat.card_zpowers, orderOf_r_one, DihedralGroup.nat_card, mul_comm 2 n] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) h
  refine ⟨inferInstance, Subgroup.normal_of_index_eq_two hidx, hidx, ?_, orderOf_sr 0, ?_⟩
  · rintro ⟨k, hk⟩
    simp only [r_one_zpow] at hk
    cases hk
  · rintro c ⟨k, rfl⟩
    simp only [r_one_zpow, inv_sr, sr_mul_r, sr_mul_sr, inv_r, zero_add, zero_sub]

theorem exists_cyclic_index_two_inverted_of_mulEquiv_dihedral {P : Type*} [Group P] {n : ℕ}
    [NeZero n] (φ : P ≃* DihedralGroup n) :
    ∃ C : Subgroup P, IsCyclic C ∧ C.Normal ∧ C.index = 2 ∧
      ∃ t : P, t ∉ C ∧ orderOf t = 2 ∧ ∀ c ∈ C, t * c * t⁻¹ = c⁻¹ := by
  obtain ⟨hcyc, hnorm, hidx, hout, hord, hinv⟩ := dihedral_rotations_data n
  refine ⟨(Subgroup.zpowers (DihedralGroup.r 1)).comap φ.toMonoidHom, ?_, hnorm.comap _, ?_,
    φ.symm (DihedralGroup.sr 0), ?_, ?_, ?_⟩
  · exact isCyclic_of_injective (φ.toMonoidHom.subgroupComap _)
      fun x y h => Subtype.ext (φ.injective (congrArg Subtype.val h))
  · rw [Subgroup.index_comap_of_surjective _ φ.surjective]
    exact hidx
  · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact hout
  · exact (orderOf_injective φ.symm.toMonoidHom φ.symm.injective _).trans hord
  · intro c hc
    apply φ.injective
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hc
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
    exact hinv _ hc

theorem hasDihedralSylowTwo_of_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G]
    (e : G ≃* G') (h : GorensteinWalter.HasDihedralSylowTwo G') :
    GorensteinWalter.HasDihedralSylowTwo G := by
  intro P
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, ⟨φ⟩⟩ := h (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  refine ⟨m, hm, ⟨((P : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective).trans
    ((MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm).trans φ)⟩⟩

theorem odd_projective_linear_two_elementary_two_sections {k : Type} [Field k] [Finite k]
    (hq : Odd (Nat.card k)) :
    (∀ x : StatedSL 2 k, x ∈ (StatedScalars (Fin 2) k).subgroupOf (StatedSL 2 k) ↔
      ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = 1 ∨
        ((x : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = -1) ∧
    (∀ P : Sylow 2 (StatedProj (StatedSL 2 k)), ∃ C : Subgroup P, IsCyclic C ∧ C.Normal ∧
      C.index = 2 ∧ ∃ t : P, t ∉ C ∧ orderOf t = 2 ∧ ∀ c ∈ C, t * c * t⁻¹ = c⁻¹) ∧
    (∀ (A : Subgroup (StatedProj (StatedSL 2 k))) (N : Subgroup A) [N.Normal],
      IsElementaryAbelian 2 (A ⧸ N) → Nat.card (A ⧸ N) ≤ 4) ∧
    ∀ (A : Subgroup (StatedProj (StatedSL 2 k))) (N : Subgroup A) [N.Normal]
      (J : Subgroup (A ⧸ N)) (V : Subgroup J) [V.Normal],
      IsElementaryAbelian 2 (J ⧸ V) → Nat.card (J ⧸ V) ≤ 4 := by
  have := Fintype.ofFinite k
  obtain ⟨p, -, f, hp, hcard⟩ := FiniteField.card' k
  rw [← Nat.card_eq_fintype_card] at hcard
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := by
    rw [hcard] at hq
    exact (Nat.odd_pow_iff f.ne_zero).mp hq
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hpodd
    exact absurd hpodd (by decide)
  have hD := (SectionRank.OddCover.odd_psl_two_sylow_data (K := k) hp2 hcard).1
  have hdih : GorensteinWalter.HasDihedralSylowTwo (StatedProj (StatedSL 2 k)) :=
    hasDihedralSylowTwo_of_mulEquiv (projectiveSpecialLinearGroupEquivStatedProj 2 k).symm
      (GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model k
        ⟨p, f, hp, hpodd, f.pos, hcard⟩)
  have hSyl : ∀ P : Sylow 2 (StatedProj (StatedSL 2 k)), ∃ C : Subgroup P, IsCyclic C ∧
      C.Normal ∧ C.index = 2 ∧ ∃ t : P, t ∉ C ∧ orderOf t = 2 ∧ ∀ c ∈ C, t * c * t⁻¹ = c⁻¹ := by
    intro P
    obtain ⟨m, -, ⟨φ⟩⟩ := hdih P
    have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
    exact exists_cyclic_index_two_inverted_of_mulEquiv_dihedral φ
  have hS : ∀ P : Sylow 2 (StatedProj (StatedSL 2 k)), ∃ C : Subgroup (StatedProj (StatedSL 2 k)),
      C ≤ P ∧ IsCyclic C ∧ C.relIndex P ≤ 2 := by
    intro P
    obtain ⟨C, hC, -, hidx, -⟩ := hSyl P
    have hC' : (C.map (P : Subgroup (StatedProj (StatedSL 2 k))).subtype).subgroupOf P = C :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) C
    refine ⟨C.map (P : Subgroup (StatedProj (StatedSL 2 k))).subtype, Subgroup.map_subtype_le C,
      isCyclic_of_surjective (MonoidHom.subgroupMap _ C) (MonoidHom.subgroupMap_surjective _ C),
      ?_⟩
    rw [Subgroup.relIndex, hC', hidx]
  refine ⟨hD, hSyl, fun A N _ hAN => ?_, fun A N _ J V _ hJV => ?_⟩
  · exact card_le_four_of_sylow_two_cyclic hS A.subtype_injective
      (QuotientGroup.mk'_surjective N)
  · exact card_le_four_of_sylow_two_cyclic hS
      (ι := A.subtype.comp (J.comap (QuotientGroup.mk' N)).subtype)
      (A.subtype_injective.comp (J.comap (QuotientGroup.mk' N)).subtype_injective)
      (ψ := (QuotientGroup.mk' V).comp ((QuotientGroup.mk' N).subgroupComap J))
      ((QuotientGroup.mk'_surjective V).comp
        ((QuotientGroup.mk' N).subgroupComap_surjective J
          (QuotientGroup.mk'_surjective N)))

end CFSG.ComponentClassification.OutcomeLocal
