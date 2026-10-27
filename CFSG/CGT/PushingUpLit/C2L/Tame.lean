module

public import CFSG.CGT.PushingUpLit.C2L.Gomi0
public import CFSG.CGT.PushingUpLit.C2L.TameBridge

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.ABGLocalTools CFSG.CGT.PushingUpLit.T2KSW

variable {G : Type} [Group G]

@[expose] def TameLink (D P Q : Subgroup G) : Prop :=
  IsSylowOf 2 P ⊤ ∧ IsSylowOf 2 Q ⊤ ∧ P ≠ Q ∧ D ≤ P ⊓ Q ∧ IsTameIntersection P Q ∧
    GomiH0 (P ⊓ Q)

theorem TameLink.mono {D D' P Q : Subgroup G} (hD : D' ≤ D) (h : TameLink D P Q) :
    TameLink D' P Q :=
  ⟨h.1, h.2.1, h.2.2.1, hD.trans h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

namespace Tame

variable [Finite G]

theorem oTwoIn_le_sylow {N S : Subgroup G} (hS : IsSylowOf 2 S N) : oTwoIn N ≤ S := by
  obtain ⟨h, hh, hhK⟩ := exists_mem_conj_mem_of_isSylowOf hS (oTwoIn_le N) (isPGroup_oTwoIn N)
  intro y hy
  have h1 : h * y * h⁻¹ ∈ oTwoIn N :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oTwoIn N hh) y).1 hy
  have h2 := hhK _ h1
  simpa [mul_assoc] using h2

theorem inf_lt_left {P Q : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hQ : IsSylowOf 2 Q ⊤)
    (hne : P ≠ Q) : P ⊓ Q < P := by
  refine lt_of_le_of_ne inf_le_left fun h => hne ?_
  have hPQ : P ≤ Q := by rw [← h]; exact inf_le_right
  exact (hP.eq_of_le hPQ le_top hQ.isPGroup).symm

theorem chain_aux (H : Subgroup G) :
    ∀ P Q : Subgroup G, IsSylowOf 2 P ⊤ → IsSylowOf 2 Q ⊤ → P ⊓ Q = H → H ≠ ⊥ →
      Relation.ReflTransGen (TameLink H) P Q := by
  induction H using WellFoundedGT.induction with
  | _ H ih =>
  intro P Q hP hQ hPQH hH
  by_cases hPQ : P = Q
  · rw [hPQ]
  have hHP : H < P := hPQH ▸ inf_lt_left hP hQ hPQ
  have hHQ : H < Q := by
    have := inf_lt_left hQ hP (Ne.symm hPQ)
    rwa [inf_comm, hPQH] at this
  have hP2 : IsPGroup 2 P := hP.isPGroup
  have hQ2 : IsPGroup 2 Q := hQ.isPGroup
  have hH2 : IsPGroup 2 H := hP2.to_le hHP.le
  set N : Subgroup G := Subgroup.normalizer (H : Set G) with hN
  have IH : ∀ S S' : Subgroup G, IsSylowOf 2 S ⊤ → IsSylowOf 2 S' ⊤ → H < S ⊓ S' →
      Relation.ReflTransGen (TameLink H) S S' := by
    intro S S' hS hS' hlt
    have hne : S ⊓ S' ≠ ⊥ := fun h => by
      rw [h] at hlt
      exact not_lt_bot hlt
    exact Relation.ReflTransGen.mono (r := TameLink (S ⊓ S')) (p := TameLink H)
      (fun _ _ hAB => hAB.mono hlt.le) S S' (ih (S ⊓ S') hlt S S' hS hS' rfl hne)
  have hPN : H < P ⊓ N := Tame.lt_inf_normalizer_of_lt hP2 hHP
  have hQN : H < Q ⊓ N := Tame.lt_inf_normalizer_of_lt hQ2 hHQ
  obtain ⟨A, hA, hPNA⟩ := exists_isSylowOf_ge (inf_le_right : P ⊓ N ≤ N) hP2.to_inf_left
  obtain ⟨B, hB, hQNB⟩ := exists_isSylowOf_ge (inf_le_right : Q ⊓ N ≤ N) hQ2.to_inf_left
  obtain ⟨R, hR, hRA⟩ := Tame.exists_sylow_inf_eq hA
  obtain ⟨S, hS, hSB⟩ := Tame.exists_sylow_inf_eq hB
  have hAR : A ≤ R := by rw [← hRA]; exact inf_le_left
  have hBS : B ≤ S := by rw [← hSB]; exact inf_le_left
  have hHA : H < A := lt_of_lt_of_le hPN hPNA
  have hHB : H < B := lt_of_lt_of_le hQN hQNB
  have hPR : Relation.ReflTransGen (TameLink H) P R :=
    IH P R hP hR (lt_of_lt_of_le hPN (le_inf inf_le_left (hPNA.trans hAR)))
  have hSQ : Relation.ReflTransGen (TameLink H) S Q :=
    IH S Q hS hQ (lt_of_lt_of_le hQN (le_inf (hQNB.trans hBS) inf_le_left))
  have hHRS : H ≤ R ⊓ S := le_inf (hHA.le.trans hAR) (hHB.le.trans hBS)
  have hRS : Relation.ReflTransGen (TameLink H) R S := by
    by_cases hlt : H < R ⊓ S
    · exact IH R S hR hS hlt
    have hRSH : R ⊓ S = H := (eq_of_le_of_not_lt hHRS hlt).symm
    have hAB : A ≠ B := by
      intro hAB
      have h1 : A ≤ R ⊓ S := le_inf hAR (hAB ▸ hBS)
      rw [hRSH] at h1
      exact hHA.not_ge h1
    have hRneS : R ≠ S := by
      intro h
      have h1 : A ≤ R ⊓ S := le_inf hAR (h ▸ hAR)
      rw [hRSH] at h1
      exact hHA.not_ge h1
    by_cases hse : StronglyEmbeddedMod H
    ·
      have htame : IsTameIntersection R S := by
        rw [IsTameIntersection, hRSH]
        exact ⟨hRA ▸ hA, hSB ▸ hB⟩
      have hnc : ¬ TwoClosed N := fun hTC => hAB ((twoClosed_iff_forall_eq.1 hTC) A B hA hB)
      have hO : oTwoIn N = H := by
        refine le_antisymm ?_ (le_oTwoIn_of_normal Subgroup.le_normalizer le_rfl hH2)
        have h1 := le_inf ((oTwoIn_le_sylow hA).trans hAR) ((oTwoIn_le_sylow hB).trans hBS)
        rwa [hRSH] at h1
      refine Relation.ReflTransGen.single ⟨hR, hS, hRneS, hHRS, htame, ?_⟩
      rw [hRSH]
      exact ⟨⟨hH, hnc, hO⟩, hse⟩
    · exact Tame.lift_conn (TameLink H) IH (Tame.sylowOf_normalizer_conn hH2 hse hA hB) hHA hR
        hRA S hS hSB
  exact hPR.trans (hRS.trans hSQ)

end Tame

theorem tameChain_of_inf_ne_bot [Finite G] {P Q : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hQ : IsSylowOf 2 Q ⊤) (h : P ⊓ Q ≠ ⊥) :
    Relation.ReflTransGen (TameLink (P ⊓ Q)) P Q :=
  Tame.chain_aux (P ⊓ Q) P Q hP hQ rfl h

end CFSG.CGT.PushingUpLit.C2L
