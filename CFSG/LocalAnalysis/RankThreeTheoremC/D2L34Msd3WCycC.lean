module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3WY

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPGroup_of_not_dvd_relIndex {Ω : Type*} [Group Ω] [Finite Ω]
    {Q₂ Q H : Subgroup Ω} (hQ₂Q : Q₂ ≤ Q) (hQH : Q ≤ H) (hQp : IsPGroup 3 Q)
    (hidx : ¬ 3 ∣ (Q₂.subgroupOf H).index) : Q ≤ Q₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrel := Subgroup.relIndex_mul_relIndex Q₂ Q H hQ₂Q hQH
  have hdvd : Q₂.relIndex Q ∣ Q₂.relIndex H := Dvd.intro _ hrel
  obtain ⟨n, hn⟩ := hQp.index (Q₂.subgroupOf Q)
  have hn0 : n = 0 := by
    by_contra hn0
    apply hidx
    have h3 : 3 ∣ Q₂.relIndex Q := by
      rw [Subgroup.relIndex, hn]
      exact dvd_pow_self 3 hn0
    exact h3.trans hdvd
  have h1 : Q₂.relIndex Q = 1 := by
    rw [Subgroup.relIndex, hn, hn0, pow_zero]
  exact Subgroup.relIndex_eq_one.mp h1

section Autom

variable {V : Subgroup G} {hU : IsElemAbelian 2 V}

omit [Finite G] in
theorem relIndex_autI_dvd {K W : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G))
    (hWK : W ≤ K) :
    ((autI hU W).subgroupOf (autI hU K)).index ∣ (W.subgroupOf K).index := by
  have h := Subgroup.relIndex_map_map (convHom hU K hKN) (W.subgroupOf K) ⊤
  rw [← autI_eq_map_convHom hU hKN hWK, ← MonoidHom.range_eq_map, range_convHom, top_sup_eq,
    Subgroup.relIndex_top_right] at h
  have h2 : ((autI hU W).subgroupOf (autI hU K)).index =
      (W.subgroupOf K ⊔ (convHom hU K hKN).ker).index := h
  rw [h2]
  exact Subgroup.index_dvd_of_le le_sup_left

end Autom

section Zcl

variable {Ω : Type*} [Group Ω]

@[expose] def r3 (L : Subgroup Ω) : Subgroup Ω := Subgroup.closure {x | x ∈ L ∧ x ^ 3 = 1}

theorem r3_le (L : Subgroup Ω) : r3 L ≤ L := (Subgroup.closure_le L).2 fun _ hx => hx.1

theorem r3_le_zcl {I : Finset (Subgroup Ω)} {L : Subgroup Ω} (hL : L ∈ I) : r3 L ≤ zcl I :=
  (Subgroup.closure_le _).2 fun _ hx => Subgroup.subset_closure ⟨L, hL, hx.1, hx.2⟩

theorem mem_map_conj_iff_aux (g : Ω) (A : Subgroup Ω) (x : Ω) :
    x ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ A := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem conjAut_eq_map_conj {W : Type*} [CommGroup W] (g : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut g A = A.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [B1.mem_conjAut, mem_map_conj_iff_aux]

theorem conj_pow_three_eq_one (g : Ω) {y : Ω} (hy : y ^ 3 = 1) : (g * y * g⁻¹) ^ 3 = 1 := by
  have h3 : y * y * y = 1 := by rw [← pow_three']; exact hy
  calc (g * y * g⁻¹) ^ 3 = g * (y * y * y) * g⁻¹ := by
        rw [pow_succ, pow_succ, pow_one]
        group
    _ = 1 := by rw [h3]; group

theorem conj_mem_r3 (g : Ω) (L : Subgroup Ω) {x : Ω} (hx : x ∈ r3 L) :
    g * x * g⁻¹ ∈ r3 (L.map (MulAut.conj g).toMonoidHom) := by
  have h : r3 L ≤ (r3 (L.map (MulAut.conj g).toMonoidHom)).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨?_, conj_pow_three_eq_one g hy.2⟩
    rw [mem_map_conj_iff_aux]
    simpa [mul_assoc] using hy.1
  have := h hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem zcl_conj_mem {I : Finset (Subgroup Ω)} {g : Ω}
    (hg : ∀ L ∈ I, L.map (MulAut.conj g).toMonoidHom ∈ I) {z : Ω} (hz : z ∈ zcl I) :
    g * z * g⁻¹ ∈ zcl I := by
  have h : zcl I ≤ (zcl I).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun y ⟨L, hL, hyL, hy3⟩ => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨L.map (MulAut.conj g).toMonoidHom, hg L hL, ?_,
      conj_pow_three_eq_one g hy3⟩
    rw [mem_map_conj_iff_aux]
    simpa [mul_assoc] using hyL
  have := h hz
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

end Zcl

theorem weakly_closed_of_normal_inf {M W N P₁ : Subgroup G}
    (hMN : M ≤ Subgroup.normalizer (N : Set G)) (hNW : Nat.card (N ⊓ W : Subgroup G) ≤ 3)
    (hP₁ : Nat.card P₁ = 3) (hP₁NW : P₁ ≤ N ⊓ W) {m p : G} (hm : m ∈ M) (hp : p ∈ P₁)
    (hmp : m * p * m⁻¹ ∈ W) : m * p * m⁻¹ ∈ P₁ := by
  have hEq : P₁ = N ⊓ W := Subgroup.eq_of_le_of_card_ge hP₁NW (by rw [hP₁]; exact hNW)
  have hpN : p ∈ N := (hP₁NW hp).1
  have hmpN : m * p * m⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hMN hm) p).mp hpN
  rw [hEq]
  exact ⟨hmpN, hmp⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
