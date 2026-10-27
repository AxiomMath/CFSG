module

public import CFSG.GF2Type.Smith1979W3.TypeA2
public import CFSG.LargeExtraspecial.S12T36Core
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.LargeExtraspecial.BridgeForms
public import CFSG.LargeExtraspecial.S3bWeak
public import CFSG.Sporadic.Schreier.TitsIso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.LargeExtraspecial CFSG.Open

@[expose] def QtPlusType {G : Type*} [Group G] [Finite G] (S : Setting G) : Prop :=
  ∃ W : Submodule (ZMod 2) S.Qt,
    2 * Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) S.Qt ∧ ∀ v ∈ W, S.q v = 0

@[expose] def T1216W3Census : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        (QtPlusType S ∧
            (Nat.card S.Mbar = 336 ∨ Nat.card S.Mbar = 20160 ∨ Nat.card S.Mbar = 40320)) ∨
          (¬ QtPlusType S ∧ (Nat.card S.Mbar = 25920 ∨ Nat.card S.Mbar = 51840))

@[expose] def T1216W3NoPGL27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        Nat.card S.Mbar ≠ 336

@[expose] def T1216W3NoA8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        Nat.card S.Mbar ≠ 20160

@[expose] def T1216W3Minus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G),
    S.width = 3 → ¬ S.IsReducible →
      (∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧ S.HasTypeAInL g) →
        ¬ QtPlusType S →
          (Nat.card S.Mbar = 25920 ∨ Nat.card S.Mbar = 51840) →
            (¬ ∃ U : Subgroup G, U ≤ S.QG ∧ IsElemAbelian 2 U ∧ Nat.card U = 16) ∧
              ∃ q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2),
                timmesfeldNondegenerate q ∧ ¬ timmesfeldPlusType q ∧
                  (Nonempty (S.Mbar ≃* timmesfeldOmega q) ∨
                    Nonempty (S.Mbar ≃* timmesfeldIsometries q))

theorem t1216WidthThree_of (h1 : T1216W3Census) (h2 : T1216W3NoPGL27)
    (h3 : T1216W3NoA8) (h5 : T1216W3Minus) : T1216WidthThree := by
  intro G _ _ _ S hw hirr hb
  rcases h1 G S hw hirr hb with ⟨hp, h336 | h20160 | h40320⟩ | ⟨hm, hc⟩
  · exact absurd h336 (h2 G S hw hirr hb)
  · exact absurd h20160 (h3 G S hw hirr hb)
  · exfalso
    have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType S.q := by
      simpa only [QtPlusType, CFSG.GroupTheory.WeirSylow.IsPlusType] using hp
    have hdim : Module.finrank (ZMod 2) S.Qt = 2 * (2 + 1) := by
      rw [S.finrank_Qt_eq_two_mul_width, hw]
    have h2z : (Nat.card (ZMod 2) : ℤ) = 2 := by rw [Nat.card_zmod]; rfl
    have hOcard : Nat.card S.O = 40320 := by
      have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
        (ε := 1) (Or.inl ⟨rfl, hplus⟩)
      rw [h2z] at h
      generalize Nat.card S.O = N at h ⊢
      norm_num [Finset.prod_Icc_succ_top] at h
      omega
    have htop : S.Mbar = ⊤ :=
      Subgroup.eq_top_of_card_eq S.Mbar (by rw [h40320, hOcard])
    exact S.Mbar_ne_top (by omega) htop
  · exact h5 G S hw hirr hb hm hc

theorem t1216W3Minus : T1216W3Minus := by
  intro G _ _ _ S hw _ _ hminus hcard
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  have hnotplus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType S.q := by
    simpa only [QtPlusType, CFSG.GroupTheory.WeirSylow.IsPlusType] using hminus
  have hdim : Module.finrank (ZMod 2) S.Qt = 2 * (2 + 1) := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hO : Nat.card S.O = 51840 := by
    have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type S.q_nondegenerate hdim
      (ε := -1) (Or.inr ⟨rfl, hnotplus⟩)
    rw [Nat.card_zmod] at h
    generalize Nat.card S.O = N at h ⊢
    norm_num [Finset.prod_Icc_succ_top] at h
    omega
  haveI : Nontrivial S.Qt :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
      rw [S.finrank_Qt_eq_two_mul_width, hw]; norm_num)
  have hΩ : Nat.card (CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate) =
      25920 := by
    have h := CFSG.LargeExtraspecial.S12DW.card_orthogonalGroup_eq S.q_nondegenerate (Q := S.q)
    rw [hO] at h
    omega
  have h6 : 6 ≤ Module.finrank (ZMod 2) S.Qt := by
    rw [S.finrank_Qt_eq_two_mul_width, hw]
  have hMΩ : S.Mbar.map S.O.subtype =
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate := by
    rcases hcard with hM | hM
    · have hidx : S.Mbar.index = 2 := by
        have h1 := Subgroup.card_mul_index S.Mbar
        rw [hM, hO] at h1
        omega
      haveI : S.Mbar.Normal := Subgroup.normal_of_index_eq_two hidx
      have hcardq : Nat.card (S.O ⧸ S.Mbar) = 2 := by
        rw [← Subgroup.index_eq_card]
        exact hidx
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : IsCyclic (S.O ⧸ S.Mbar) := isCyclic_of_prime_card hcardq
      have hcomm : _root_.commutator S.O ≤ S.Mbar :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mp IsCyclic.isMulCommutative
      rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_subgroupOf
        S.q_nondegenerate h6] at hcomm
      have hle : CFSG.RankThree.OrthogonalInvolutions.omegaGroup S.q S.q_nondegenerate ≤
          S.Mbar.map S.O.subtype := fun g hg =>
        ⟨⟨g, CFSG.RankThree.OrthogonalInvolutions.omegaGroup_le S.q S.q_nondegenerate hg⟩,
          hcomm hg, rfl⟩
      have hcardmap : Nat.card (S.Mbar.map S.O.subtype) = 25920 := by
        rw [Subgroup.card_map_of_injective S.O.subtype_injective, hM]
      haveI : Finite ↥(S.Mbar.map S.O.subtype) :=
        Nat.finite_of_card_ne_zero (by rw [hcardmap]; norm_num)
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardmap, hΩ])).symm
    · exfalso
      have htop : S.Mbar = ⊤ :=
        Subgroup.eq_top_of_card_eq S.Mbar (by rw [hM, hO])
      exact S.Mbar_ne_top (by omega) htop
  refine ⟨?_, ?_⟩
  ·
    rintro ⟨U, hU, hUab, hUcard⟩
    let W : Submodule (ZMod 2) S.Qt := S.clSub U
    have hWsing : ∀ v ∈ W, S.q v = 0 := by
      intro v hv
      obtain ⟨x, hxU, hxQ, hxv⟩ := S.mem_clSub_iff.mp hv
      rw [← hxv, S.q_cl_eq_zero_iff hxQ]
      exact hUab.2 x hxU
    have hdimW : 3 ≤ Module.finrank (ZMod 2) W := by
      have hcardW : Nat.card U ≤ 2 * Nat.card W := by
        calc Nat.card U ≤ Nat.card (S.clPre W) := Subgroup.card_le_of_le (S.le_clPre_clSub hU)
          _ = 2 * Nat.card W := S.card_clPre W
      rw [hUcard, S.card_submodule] at hcardW
      have hpow : 2 * 2 ^ Module.finrank (ZMod 2) W =
          2 ^ (Module.finrank (ZMod 2) W + 1) := by
        rw [pow_succ]
        exact Nat.mul_comm _ _
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, hpow] at hcardW
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcardW
      omega
    obtain ⟨v, hv⟩ :=
      exists_linearIndependent_of_le_finrank (R := ZMod 2) (M := W) (n := 3) hdimW
    let W' : Submodule (ZMod 2) S.Qt := (Submodule.span (ZMod 2) (Set.range v)).map W.subtype
    have hW'dim : Module.finrank (ZMod 2) W' = 3 := by
      dsimp only [W']
      rw [Submodule.finrank_map_subtype_eq, finrank_span_eq_card hv, Fintype.card_fin]
    have hW'le : W' ≤ W := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hW'sing : ∀ v ∈ W', S.q v = 0 := fun v hv' => hWsing v (hW'le hv')
    exact hminus ⟨W', by rw [hW'dim, S.finrank_Qt_eq_two_mul_width, hw], hW'sing⟩
  ·
    let e : S.Qt ≃ₗ[ZMod 2] (Fin (2 * S.width) → ZMod 2) :=
      (Module.finBasisOfFinrankEq (ZMod 2) S.Qt S.finrank_Qt_eq_two_mul_width).equivFun
    let q : QuadraticForm (ZMod 2) (Fin (2 * S.width) → ZMod 2) :=
      S.q.comp (e.symm : (Fin (2 * S.width) → ZMod 2) →ₗ[ZMod 2] S.Qt)
    have hq : ∀ v, q (e v) = S.q v := fun v => by simp [q]
    have hqnd : timmesfeldNondegenerate q :=
      CFSG.LargeExtraspecial.Bridge.nondegenerate_of_map e hq
        ((CFSG.LargeExtraspecial.Bridge.polarBilin_nondegenerate_iff S.q).mp S.q_nondegenerate)
    have hqnotplus : ¬ timmesfeldPlusType q := by
      rintro ⟨W₂, hW₂dim, hW₂sing⟩
      let W₂' : Submodule (ZMod 2) S.Qt :=
        W₂.map (e.symm : (Fin (2 * S.width) → ZMod 2) →ₗ[ZMod 2] S.Qt)
      have hW₂'dim : 2 * Module.finrank (ZMod 2) W₂' = Module.finrank (ZMod 2) S.Qt := by
        dsimp only [W₂']
        rw [LinearEquiv.finrank_map_eq, hW₂dim, S.finrank_Qt_eq_two_mul_width]
      have hW₂'sing : ∀ v ∈ W₂', S.q v = 0 := by
        rintro _ ⟨w, hw, rfl⟩
        have := hW₂sing w hw
        simpa [q] using this
      exact hminus ⟨W₂', hW₂'dim, hW₂'sing⟩
    have hΩiso : Nonempty (S.Mbar ≃* timmesfeldOmega S.q) :=
      ⟨(Subgroup.equivMapOfInjective S.Mbar S.O.subtype S.O.subtype_injective).trans
        ((MulEquiv.subgroupCongr hMΩ).trans
          (MulEquiv.subgroupCongr (s12_timmesfeldOmega_eq S.q S.q_nondegenerate)).symm)⟩
    obtain ⟨eΩ⟩ := hΩiso
    exact ⟨q, hqnd, hqnotplus,
      Or.inl ⟨eΩ.trans (CFSG.LargeExtraspecial.Bridge.omegaEquiv e hq)⟩⟩

end CFSG.GF2Type.Smith1979W3
