module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

@[expose] def KFactWeakClosureInner : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → IsCatalogGroup K → ∀ P : Sylow p K,
      IsMulCommutative (P : Subgroup K) → 2 ≤ CFSG.Open.pRank p (P : Subgroup K) →
      ∀ A : Subgroup K, A ≤ (P : Subgroup K) → Nat.card A = p →
        ∃ g : K, A.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup K) ∧
          A.map (MulAut.conj g).toMonoidHom ≠ A

private theorem relIndex_eq_relIndex_sup {G : Type} [Group G] [Finite G] (S N : Subgroup G)
    [N.Normal] : S.relIndex N = S.relIndex (S ⊔ N) := by
  have h1 : N.relIndex (S ⊔ N) = N.relIndex S := Subgroup.relIndex_sup_right S N
  have h2 := Subgroup.relIndex_mul_card S N
  have h3 := Subgroup.relIndex_mul_card S (S ⊔ N)
  have h4 := Subgroup.relIndex_mul_card N (S ⊔ N)
  have h5 := Subgroup.relIndex_mul_card N S
  rw [inf_eq_left.mpr le_sup_left] at h3
  rw [inf_eq_left.mpr le_sup_right, h1] at h4
  rw [inf_comm N S] at h5
  have hs : 0 < Nat.card S := Nat.card_pos
  have hd : 0 < Nat.card ↥(S ⊓ N) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hs hd)
  calc S.relIndex N * (Nat.card S * Nat.card ↥(S ⊓ N))
      = Nat.card N * Nat.card S := by rw [← h2]; ring
    _ = (N.relIndex S * Nat.card ↥(S ⊓ N)) * Nat.card N := by rw [h5]; ring
    _ = (N.relIndex S * Nat.card N) * Nat.card ↥(S ⊓ N) := by ring
    _ = Nat.card ↥(S ⊔ N) * Nat.card ↥(S ⊓ N) := by rw [h4]
    _ = (S.relIndex (S ⊔ N) * Nat.card S) * Nat.card ↥(S ⊓ N) := by rw [h3]
    _ = S.relIndex (S ⊔ N) * (Nat.card S * Nat.card ↥(S ⊓ N)) := by ring

theorem kFactWeakClosure_of_inner (hIA : KFactInnerAction) (hWC : KFactWeakClosureInner) :
    KFactWeakClosure := by
  intro p hp hp2 X _ _ K hKn hs hnab hcat hC hpK Q hKQ hQab hrank A hAQ hA
  haveI := hKn
  haveI : Fact p.Prime := ⟨hp⟩
  have hidx : ¬ p ∣ ((Q : Subgroup X).subgroupOf K).index := by
    have e : ((Q : Subgroup X).subgroupOf K).index = (Q : Subgroup X).index := by
      rw [← Subgroup.relIndex, relIndex_eq_relIndex_sup, sup_comm, hKQ,
        Subgroup.relIndex_top_right]
    rw [e]
    exact Q.not_dvd_index
  let PK : Sylow p ↥K := (Q.isPGroup'.comap_subtype (K := K)).toSylow hidx
  have hPK : (PK : Subgroup K) = (Q : Subgroup X).subgroupOf K := IsPGroup.toSylow_coe _ _
  have hmemPK : ∀ g : ↥K, g ∈ (PK : Subgroup K) ↔ (g : X) ∈ (Q : Subgroup X) := by
    intro g
    rw [hPK, Subgroup.mem_subgroupOf]
  have hPab : IsMulCommutative (PK : Subgroup K) := by
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have h := hQab.is_comm.comm ⟨((a : ↥K) : X), (hmemPK a).1 a.2⟩ ⟨((b : ↥K) : X), (hmemPK b).1 b.2⟩
    have h' : ((a : ↥K) : X) * ((b : ↥K) : X) = ((b : ↥K) : X) * ((a : ↥K) : X) :=
      congrArg Subtype.val h
    simpa only [Subgroup.coe_mul] using h'
  have hPne : (PK : Subgroup K) ≠ ⊥ := PK.ne_bot_of_dvd_card hpK
  have hQK : (Q : Subgroup X) ≤ K := by
    intro a ha
    obtain ⟨n, hn⟩ := Q.isPGroup' ⟨a, ha⟩
    have han : a ^ p ^ n = 1 := congrArg Subtype.val hn
    let φ : MulAut ↥K := MulAut.conjNormal a
    have hφ : φ ^ p ^ n = 1 := by
      show (MulAut.conjNormal a) ^ p ^ n = 1
      rw [← map_pow, han, map_one]
    have hcomm : ∀ g ∈ (PK : Subgroup K), φ * MulAut.conj g = MulAut.conj g * φ := by
      intro g hg
      have hag : a * (g : X) = (g : X) * a :=
        congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨(g : X), (hmemPK g).1 hg⟩)
      refine MulEquiv.ext fun k => Subtype.ext ?_
      show a * ((g : X) * (k : X) * (g : X)⁻¹) * a⁻¹ = (g : X) * (a * (k : X) * a⁻¹) * (g : X)⁻¹
      have hag' : a⁻¹ * (g : X)⁻¹ = (g : X)⁻¹ * a⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hag]
      calc a * ((g : X) * (k : X) * (g : X)⁻¹) * a⁻¹
          = (a * (g : X)) * (k : X) * ((g : X)⁻¹ * a⁻¹) := by group
        _ = ((g : X) * a) * (k : X) * (a⁻¹ * (g : X)⁻¹) := by rw [hag, hag']
        _ = (g : X) * (a * (k : X) * a⁻¹) * (g : X)⁻¹ := by group
    obtain ⟨g, hg, hφg⟩ := hIA p hp hp2 ↥K hs hnab hcat PK hPne hPab φ ⟨n, hφ⟩ hcomm
    have hcent : (g : X)⁻¹ * a ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : a * k * a⁻¹ = (g : X) * k * (g : X)⁻¹ :=
        congrArg (fun α : MulAut ↥K => ((α ⟨k, hk⟩ : ↥K) : X)) hφg
      calc k * ((g : X)⁻¹ * a) = (g : X)⁻¹ * ((g : X) * k * (g : X)⁻¹) * a := by group
        _ = (g : X)⁻¹ * (a * k * a⁻¹) * a := by rw [h1]
        _ = ((g : X)⁻¹ * a) * k := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
    rw [← hcent]
    exact g.2
  have hrank' : 2 ≤ CFSG.Open.pRank p (PK : Subgroup K) := by
    rw [hPK, CFSG.RankThreeEvenClassification.Helpers.pRank_subgroupOf p hp _ _ hQK]
    rwa [inf_of_le_left hQK] at hrank
  have hAK : A ≤ K := hAQ.trans hQK
  have hA'P : A.subgroupOf K ≤ (PK : Subgroup K) := by
    intro k hk
    rw [hmemPK]
    exact hAQ (Subgroup.mem_subgroupOf.1 hk)
  have hA'c : Nat.card (A.subgroupOf K) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hA]
  obtain ⟨g, hgP, hgA⟩ := hWC p hp hp2 ↥K hs hnab hcat PK hPab hrank' _ hA'P hA'c
  refine ⟨(g : X), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    have h1 := hgP ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    rw [hmemPK] at h1
    exact h1
  · intro heq
    apply hgA
    ext k
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      rw [← heq]
      exact ⟨(a : X), Subgroup.mem_subgroupOf.1 ha, rfl⟩
    · intro hk
      have hk' : (k : X) ∈ A.map (MulAut.conj (g : X)).toMonoidHom := by
        rw [heq]
        exact Subgroup.mem_subgroupOf.1 hk
      obtain ⟨a, ha, hak⟩ := hk'
      refine ⟨⟨a, hAK ha⟩, Subgroup.mem_subgroupOf.2 ha, Subtype.ext ?_⟩
      exact hak

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
