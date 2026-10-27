module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFHeis
public import CFSG.LargeExtraspecial.OutSixBasic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF

open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def OneClassE (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ B U : Subgroup G, Nat.card B = p ^ 2 → Nat.card U = p ^ 2 → Heis.ConjSub B U

theorem OneClassE.of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : OneClassE p G) : OneClassE p H := by
  intro B U hB hU
  have hB0 : Nat.card (B.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hB
  have hU0 : Nat.card (U.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hU
  obtain ⟨g, hg⟩ := h _ _ hB0 hU0
  refine ⟨e g, ?_⟩
  ext x
  rw [Heis.mem_map_conj]
  have hx : x ∈ U ↔ e.symm x ∈ U.map e.symm.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [hx, ← hg, Heis.mem_map_conj, Subgroup.mem_map_equiv]
  simp [map_mul, mul_assoc]

theorem le_of_card_sq {p : ℕ} {Z : Type*} [Group Z] [Finite Z] (K : Subgroup Z)
    [K.Normal] (hidx : Nat.Coprime p K.index) (B : Subgroup Z) (hB : Nat.card B = p ^ 2) :
    B ≤ K := by
  intro b hb
  have hbp : b ^ (p ^ 2) = 1 := by
    have := pow_card_eq_one' (x := (⟨b, hb⟩ : B))
    rw [hB] at this
    exact congrArg Subtype.val this
  have h1 : orderOf (b : Z ⧸ K) ∣ p ^ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hbp, QuotientGroup.mk_one]
  have h2 : orderOf (b : Z ⧸ K) ∣ K.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (b : Z ⧸ K) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left 2 hidx) h1 h2
  exact (QuotientGroup.eq_one_iff b).1 (orderOf_eq_one_iff.1 h3)

theorem oneClassE_of_normal {p : ℕ} {Z : Type*} [Group Z] [Finite Z]
    (K : Subgroup Z) [K.Normal] (hidx : Nat.Coprime p K.index) (hK : OneClassE p K) :
    OneClassE p Z := by
  intro B U hB hU
  have hBK : B ≤ K := le_of_card_sq K hidx B hB
  have hUK : U ≤ K := le_of_card_sq K hidx U hU
  have hB' : Nat.card (B.subgroupOf K) = p ^ 2 := by
    rw [← hB, ← Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
  have hU' : Nat.card (U.subgroupOf K) = p ^ 2 := by
    rw [← hU, ← Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hUK]
  obtain ⟨k, hk⟩ := hK _ _ hB' hU'
  refine ⟨(k : Z), ?_⟩
  have hcomm : (MulAut.conj (k : Z)).toMonoidHom.comp K.subtype =
      K.subtype.comp (MulAut.conj k).toMonoidHom := by
    ext t
    simp
  calc B.map (MulAut.conj (k : Z)).toMonoidHom
      = ((B.subgroupOf K).map K.subtype).map (MulAut.conj (k : Z)).toMonoidHom := by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
    _ = ((B.subgroupOf K).map (MulAut.conj k).toMonoidHom).map K.subtype := by
        rw [Subgroup.map_map, Subgroup.map_map, hcomm]
    _ = (U.subgroupOf K).map K.subtype := by rw [hk]
    _ = U := by rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hUK]

theorem oneClassE_of_model {p : ℕ} (hp : p.Prime) {Z : Type*} [Group Z] [Finite Z]
    (K : Subgroup Z) [K.Normal] (hC : Subgroup.centralizer (K : Set Z) = ⊥)
    {T : Type*} [Group T] (e : K ≃* T) (hOut : ¬ p ∣ Nat.card (Outer T)) (hOne : OneClassE p T) :
    OneClassE p Z := by
  have hdvd : K.index ∣ Nat.card (Outer T) :=
    CFSG.LargeExtraspecial.S14.index_dvd_card_outer_of_mulEquiv K (by rw [hC]; exact bot_le) e
  have hcop : Nat.Coprime p K.index := by
    rw [hp.coprime_iff_not_dvd]
    exact fun hpd => hOut (hpd.trans hdvd)
  exact oneClassE_of_normal K hcop (hOne.of_mulEquiv e.symm)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKF
