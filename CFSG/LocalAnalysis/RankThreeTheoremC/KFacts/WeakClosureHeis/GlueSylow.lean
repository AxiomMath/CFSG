module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open Subgroup
open scoped commutatorElement

section Glue

variable {p : ℕ}

private theorem w5_isMulCommutative_map_iff {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (S : Subgroup G) :
    IsMulCommutative (S.map f) ↔ IsMulCommutative S := by
  rw [isMulCommutative_iff, isMulCommutative_iff]
  constructor
  · intro h a b
    have h1 := h ⟨f a, Subgroup.mem_map_of_mem f a.2⟩ ⟨f b, Subgroup.mem_map_of_mem f b.2⟩
    have h2 : f ((a : G) * b) = f ((b : G) * a) := by
      simpa [map_mul] using congrArg Subtype.val h1
    exact Subtype.ext (hf h2)
  · intro h a b
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    show (a : H) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    have := congrArg (fun z : S => f z) (h ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this

private theorem w5_isElemAbelian_map_iff {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (E : Subgroup G) :
    IsElemAbelian p (E.map f) ↔ IsElemAbelian p E := by
  unfold IsElemAbelian
  rw [w5_isMulCommutative_map_iff f hf E]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h x hx
    apply hf
    rw [map_pow, map_one]
    exact h _ (Subgroup.mem_map_of_mem f hx)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_pow, h x hx, map_one]

theorem exists_sylow_map_subtype [Fact p.Prime] {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    (Q : Sylow p X) (hKQ : K ⊔ (Q : Subgroup X) = ⊤) :
    ∃ S : Sylow p ↥K, (S : Subgroup ↥K).map K.subtype = (Q : Subgroup X) ⊓ K := by
  have h1 : K.relIndex (Q : Subgroup X) = K.index := by
    rw [← Subgroup.relIndex_sup_right, sup_comm, hKQ, Subgroup.relIndex_top_right]
  have h2 : ((Q : Subgroup X) ⊓ K).relIndex (Q : Subgroup X) * (Q : Subgroup X).index =
      ((Q : Subgroup X) ⊓ K).index := Subgroup.relIndex_mul_index inf_le_left
  have h3 : ((Q : Subgroup X) ⊓ K).relIndex K * K.index = ((Q : Subgroup X) ⊓ K).index :=
    Subgroup.relIndex_mul_index inf_le_right
  have h4 : ((Q : Subgroup X) ⊓ K).relIndex (Q : Subgroup X) = K.relIndex (Q : Subgroup X) :=
    Subgroup.inf_relIndex_left _ _
  have hK0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h5 : ((Q : Subgroup X) ⊓ K).relIndex K = (Q : Subgroup X).index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hK0)
    rw [h3, ← h2, h4, h1, mul_comm]
  have hidx : ((Q : Subgroup X).subgroupOf K).index = (Q : Subgroup X).index := by
    rw [← Subgroup.relIndex, ← Subgroup.inf_relIndex_right]
    exact h5
  have hpg : IsPGroup p ((Q : Subgroup X).subgroupOf K) := by
    rw [← Subgroup.comap_subtype]
    exact Q.isPGroup'.comap_subtype
  have hnd : ¬ p ∣ ((Q : Subgroup X).subgroupOf K).index := by
    rw [hidx]
    exact Q.not_dvd_index
  exact ⟨hpg.toSylow hnd, Subgroup.subgroupOf_map_subtype _ _⟩

theorem pRank_top_eq_of_sylow [Fact p.Prime] {K : Type*} [Group K] [Finite K] (S : Sylow p K) :
    CFSG.Open.pRank p (⊤ : Subgroup K) = CFSG.Open.pRank p (S : Subgroup K) := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  ·
    rintro ⟨E, -, hE, hcard⟩
    have hEp : IsPGroup p E := IsPGroup.of_card hcard
    obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q S
    refine ⟨E.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_⟩
    · open scoped Pointwise in
      rintro _ ⟨x, hx, rfl⟩
      have hmem : (MulAut.conj g) x ∈ MulAut.conj g • (Q : Subgroup K) :=
        Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _ (hEQ hx)
      have : (g • Q : Sylow p K) = S := hg
      have h2 : ((g • Q : Sylow p K) : Subgroup K) = (S : Subgroup K) := congrArg _ this
      rw [← h2, Sylow.coe_subgroup_smul]
      exact hmem
    · exact (w5_isElemAbelian_map_iff _ (MulAut.conj g).injective E).2 hE
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hcard
  · rintro ⟨E, -, hE, hcard⟩
    exact ⟨E, le_top, hE, hcard⟩

theorem pRank_map_subtype_eq (hp : p.Prime) {X : Type*} [Group X] [Finite X] (K : Subgroup X) (S : Subgroup ↥K) :
    CFSG.Open.pRank p (S.map K.subtype) = CFSG.Open.pRank p S := by
  unfold CFSG.Open.pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E, hES, hE, hcard⟩
    have hEK : E ≤ K := hES.trans (Subgroup.map_subtype_le S)
    have hmap : (E.comap K.subtype).map K.subtype = E := by
      rw [Subgroup.map_comap_eq, K.range_subtype, inf_of_le_right hEK]
    refine ⟨E.comap K.subtype, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : K.subtype x ∈ S.map K.subtype := hES hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx'
      have : y = x := K.subtype_injective hyx
      exact this ▸ hy
    · rw [← w5_isElemAbelian_map_iff K.subtype K.subtype_injective, hmap]
      exact hE
    · rw [← Subgroup.card_map_of_injective K.subtype_injective, hmap]
      exact hcard
  · rintro ⟨E, hES, hE, hcard⟩
    refine ⟨E.map K.subtype, Subgroup.map_mono hES,
      (w5_isElemAbelian_map_iff _ K.subtype_injective E).2 hE, ?_⟩
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hcard

theorem isMulCommutative_map_subtype_iff {X : Type*} [Group X] (K : Subgroup X) (S : Subgroup ↥K) :
    IsMulCommutative (S.map K.subtype) ↔ IsMulCommutative S :=
  w5_isMulCommutative_map_iff K.subtype K.subtype_injective S

theorem violation_map {X : Type*} [Group X] [Finite X] (hp : p.Prime) (K : Subgroup X) (U : Subgroup ↥K)
    (hv : 4 ≤ CFSG.Open.pRank p U ∨ ¬ IsCyclic ↥⁅U, U⁆ ∨ ((∀ u ∈ U, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card U)) :
    4 ≤ CFSG.Open.pRank p (U.map K.subtype) ∨ ¬ IsCyclic ↥⁅U.map K.subtype, U.map K.subtype⁆ ∨
      ((∀ u ∈ U.map K.subtype, u ^ p = 1) ∧ p ^ 5 ≤ Nat.card (U.map K.subtype)) := by
  rcases hv with h | h | ⟨h1, h2⟩
  · left
    rwa [pRank_map_subtype_eq hp]
  · right; left
    intro hcyc
    apply h
    rw [← Subgroup.map_commutator] at hcyc
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective ⁅U, U⁆ K.subtype K.subtype_injective).symm
      (Subgroup.equivMapOfInjective ⁅U, U⁆ K.subtype K.subtype_injective).symm.surjective
  · right; right
    refine ⟨?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, h1 u hu, map_one]
    · rwa [Subgroup.card_map_of_injective K.subtype_injective]

end Glue

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
