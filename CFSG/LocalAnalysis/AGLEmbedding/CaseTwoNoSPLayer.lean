module

public import CFSG.LocalAnalysis.AGLEmbedding.ReducedNotConstrained

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

namespace ReducedNongeneration

variable {p : ℕ} {X : Type*} [Group X] [Finite X] {R : Sylow p X} {X₀ : Subgroup X}

theorem layer_ne_bot_of_surjective_of_card (h : ReducedNongeneration p X R X₀) {L : Type*}
    [Group L] [Finite L] [IsSimpleGroup L] (hLn : ∃ a b : L, a * b ≠ b * a) (TL : Sylow p L)
    (hTL : p ^ 2 ≤ Nat.card TL) {A : Subgroup X} (f : A →* L)
    (hf : Function.Surjective f) : CFSG.layer X ≠ ⊥ := by
  intro hlayer
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore p X with hQdef
  have hQ : IsPGroup p Q := CFSG.pCore_isPGroup
  have hQc : Subgroup.centralizer (Q : Set X) ≤ Q :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot X p h.core_eq_bot hlayer
  obtain ⟨C, hC, hfrat, -, hcent, hcyc, -⟩ :=
    cyclic_characteristic_abelian_pGroup_has_cyclic_critical_quotient p h.ne_two hQ
      fun A hAc hA => by
        have := hAc
        exact h.isCyclic_of_characteristic_of_isMulCommutative A hA
  have hrank : ∀ N : Subgroup X, N.Normal → IsPGroup p N → Open.pRank p N ≤ 2 := fun N hN hNp => by
    have := hN
    exact h.pRank_le_two_of_normal_isPGroup hNp
  have hCxn : (C.map Q.subtype).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    exact top_unique ((Subgroup.normalizer_eq_top Q).symm.le.trans
      (normalizer_le_normalizer_characteristic C hC))
  have hZx := map_map_center_eq_inf_centralizer C
  have hZxn : (((Subgroup.center C).map C.subtype).map Q.subtype).Normal := by
    rw [hZx]
    infer_instance
  have hZC : ((Subgroup.center C).map C.subtype).map Q.subtype ≤ C.map Q.subtype :=
    hZx.le.trans inf_le_left
  have hCQ : C.map Q.subtype ≤ Q := Subgroup.map_subtype_le C
  have hZp : IsPGroup p (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    hQ.to_le (hZC.trans hCQ)
  have hZcyc : IsCyclic (((Subgroup.center C).map C.subtype).map Q.subtype) :=
    (((Subgroup.center C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (((Subgroup.center C).map C.subtype).equivMapOfInjective Q.subtype
        Q.subtype_injective)).isCyclic.mp hcyc
  have hQZ : Q ⊓ Subgroup.centralizer ((C.map Q.subtype : Subgroup X) : Set X) ≤
      ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x ⟨hxQ, hxc⟩
    have hmem : (⟨x, hxQ⟩ : Q) ∈ Subgroup.centralizer (C : Set Q) :=
      Subgroup.mem_centralizer_iff.mpr fun c hc =>
        Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) _ ⟨c, hc, rfl⟩)
    rw [hcent] at hmem
    exact ⟨_, hmem, rfl⟩
  have hK := isPGroup_centralizer_of_selfCentralizing hp hQ hQc hZC (hZC.trans hCQ) hQZ
  have hfratC : frattini C ≤ Subgroup.center C :=
    (Subgroup.map_le_map_iff_of_injective C.subtype_injective).mp hfrat
  have hCp : IsPGroup p C := hQ.to_subgroup C
  have hcommC : commutator C ≤ Subgroup.center C :=
    (pGroup_commutator_le_frattini p hCp).trans hfratC
  have hpowC : ∀ c : C, c ^ p ∈ Subgroup.center C :=
    fun c => hfratC (pGroup_pow_mem_frattini p hCp c)
  have hCrank : Open.pRank p (⊤ : Subgroup C) ≤ 2 := by
    rw [← pRank_map_of_injective p hp (Q.subtype.comp C.subtype)
      (Q.subtype_injective.comp C.subtype_injective), ← Subgroup.map_map,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hrank _ hCxn (hQ.to_le hCQ)
  have hVcard := card_center_quotient_eq_one_or_sq h.ne_two hCp hcyc hcommC hpowC hCrank
  let : MulDistribMulAction X Q := MulDistribMulAction.compHom Q (MulAut.conjNormal (H := Q))
  let := characteristic_subgroup_mulDistribMulAction (acting := X) C
  let := characteristic_quotient_mulDistribMulAction (acting := X) (Subgroup.center C)
  have hρ : ∀ x ∈ (MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C)).ker,
      ∀ c ∈ C.map Q.subtype, c⁻¹ * (x * c * x⁻¹) ∈
        ((Subgroup.center C).map C.subtype).map Q.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have hfix := congrArg (fun σ : MulAut (C ⧸ Subgroup.center C) =>
      σ (QuotientGroup.mk (⟨q, hq⟩ : C))) (MonoidHom.mem_ker.mp hx)
    change (QuotientGroup.mk (x • (⟨q, hq⟩ : C)) : C ⧸ Subgroup.center C) =
      QuotientGroup.mk ⟨q, hq⟩ at hfix
    exact ⟨_, ⟨_, QuotientGroup.eq.mp hfix.symm, rfl⟩, rfl⟩
  have hL := isPGroup_inf_centralizer_of_displacement hp hK hZp hρ
  set ρ := MulDistribMulAction.toMulAut X (C ⧸ Subgroup.center C) with hρdef
  set N₁ : Subgroup A := ρ.ker.comap A.subtype with hN₁
  set P₀ : Subgroup A := (ρ.ker ⊓ Subgroup.centralizer
    ((((Subgroup.center C).map C.subtype).map Q.subtype : Subgroup X) : Set X)).comap
      A.subtype with hP₀
  have hP₀n : P₀.Normal := by
    have : (ρ.ker ⊓ Subgroup.centralizer
      ((((Subgroup.center C).map C.subtype).map Q.subtype : Subgroup X) : Set X)).Normal :=
      Subgroup.normal_inf_normal _ _
    exact Subgroup.Normal.comap this _
  have hN₁n : N₁.Normal := Subgroup.Normal.comap (MonoidHom.normal_ker ρ) _
  have hP₀p : IsPGroup p P₀ := hL.comap_of_injective _ A.subtype_injective
  have hNP : ⁅N₁, N₁⁆ ≤ P₀ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨?_, ?_⟩
    · have : (⁅a, b⁆ : A) = a * b * a⁻¹ * b⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    · exact commutatorElement_mem_centralizer_of_isCyclic hZcyc (a : X) (b : X)
  have hN₁f : N₁.map f = ⊥ := map_eq_bot_of_commutator_le hLn f hf hP₀p hNP
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p A))
  let : IsMulCommutative (C ⧸ Subgroup.center C) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcommC
  let : CommGroup (C ⧸ Subgroup.center C) := IsMulCommutative.instCommGroup
  let : MulDistribMulAction (S : Subgroup A) (C ⧸ Subgroup.center C) :=
    MulDistribMulAction.compHom (C ⧸ Subgroup.center C) (A.subtype.comp (S : Subgroup A).subtype)
  have hVpow : ∀ v : C ⧸ Subgroup.center C, v ^ p = 1 := by
    intro v
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center C) v
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hpowC c)
  obtain ⟨k, hkindex, hkfix⟩ := exists_kernel_of_card_eq_one_or_sq S.isPGroup' hVcard hVpow
  set g : (S : Subgroup A) →* L := f.comp (S : Subgroup A).subtype with hg
  have hkg : k ≤ g.ker := by
    intro e he
    have heN : (e : A) ∈ N₁ := MonoidHom.mem_ker.mpr (MulEquiv.ext (hkfix e he))
    have : f (e : A) ∈ N₁.map f := Subgroup.mem_map_of_mem f heN
    rw [hN₁f, Subgroup.mem_bot] at this
    exact this
  have hle : Nat.card g.range ≤ p := by
    rw [← Subgroup.index_ker]
    have hdvd := Subgroup.index_dvd_of_le hkg
    rcases hkindex with h1 | h1 <;> rw [h1] at hdvd
    · exact (Nat.le_of_dvd one_pos hdvd).trans hp.one_lt.le
    · exact Nat.le_of_dvd hp.pos hdvd
  have hrange : g.range = (S.mapSurjective hf : Subgroup L) := by
    rw [Sylow.coe_mapSurjective, hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (S.mapSurjective hf) = Nat.card TL := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have h2 := hTL
  rw [← hcard, ← hrange] at h2
  have := hp.two_le
  nlinarith

end ReducedNongeneration

end CFSG.AGLEmbedding
