module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdBal
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdBarComp
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011AdSet

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizes_of_comm {K₁ K₂ : Subgroup G} (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) :
    K₂ ≤ normalizer (K₁ : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    have h1 : m * a = a * m := (hc a ha m hm).symm
    rwa [h1, mul_inv_cancel_right]
  · intro hb
    have h2 := hc _ hb m hm
    have e : m * a * m⁻¹ = a := by
      have h3 : m * a = m * (m * a * m⁻¹) := by
        calc m * a = (m * a * m⁻¹) * m := by group
          _ = m * (m * a * m⁻¹) := h2
      exact (mul_left_cancel h3).symm
    rwa [e] at hb

omit [Finite G] in
theorem subnormal_of_norm {x : G} {K₁ K₂ : Subgroup G} (hle₁ : K₁ ≤ centralizer ({x} : Set G))
    (hle₂ : K₂ ≤ centralizer ({x} : Set G)) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hn : ∀ c ∈ centralizer ({x} : Set G), ∀ a ∈ K₁ ⊔ K₂, c * a * c⁻¹ ∈ K₁ ⊔ K₂) :
    (K₁.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hsupC : K₁ ⊔ K₂ ≤ C := sup_le hle₁ hle₂
  have hnorm : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
    sup_le Subgroup.le_normalizer (normalizes_of_comm hc)
  have hLn : ((K₁ ⊔ K₂).subgroupOf C).Normal := ⟨fun a ha c => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hn c c.2 a ha⟩
  have hL : ((K₁ ⊔ K₂).subgroupOf C).IsSubnormal :=
    Subgroup.IsSubnormal.step _ ⊤ le_top Subgroup.IsSubnormal.top (hLn.subgroupOf ⊤)
  refine Subgroup.IsSubnormal.step _ ((K₁ ⊔ K₂).subgroupOf C)
    (Subgroup.comap_mono le_sup_left) hL ⟨fun a ha l => ?_⟩
  have ha' : ((a : ↥C) : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ha)
  have hl' : ((l : ↥C) : G) ∈ K₁ ⊔ K₂ := Subgroup.mem_subgroupOf.mp l.2
  have := (Subgroup.mem_normalizer_iff.mp (hnorm hl') ((a : ↥C) : G)).mp ha'
  exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr this)

omit [Finite G] in
theorem PairG.sub₁ {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) :
    (K₁.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
  subnormal_of_norm h.le₁ h.le₂ h.comm h.norm

omit [Finite G] in
theorem PairG.sub₂ {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) :
    (K₂.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
  subnormal_of_norm h.le₂ h.le₁ (fun a ha b hb => (h.comm b hb a ha).symm)
    (by rw [sup_comm]; exact h.norm)

theorem isQuasisimple_hat {K : Subgroup G} (hq : IsQuasisimple ↥K) :
    IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K) := by
  have h := isQuasisimple_barIn (le_refl K) hq
  have htop : barIn K K = ⊤ := by
    unfold barIn
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [htop] at h
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv h

theorem barIn_pLayerOf (H : Subgroup G) : barIn H (pLayerOf 2 H) = layer (HBar H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pLayerOf 2 H = (CFSG.pLayer ↥H 2).map H.subtype := by
    rw [TwoThin.pLayerOf_two_eq_map,
      CFSG.ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer]
  have h2 : ((CFSG.pLayer ↥H 2).map H.subtype).subgroupOf H = CFSG.pLayer ↥H 2 :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  unfold barIn
  rw [h1, h2]
  exact CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient

theorem PairG.le_pLayerOf₁ {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) {H : Subgroup G}
    (hxH : x ∈ H) (hK₁H : K₁ ≤ H) : K₁ ≤ pLayerOf 2 H :=
  le_pLayerOf_of_comp hxH h.ord hK₁H h.le₁ (Subgroup.isPerfect_iff.mp h.quasi₁.1)
    (isQuasisimple_hat h.quasi₁) h.sub₁

theorem PairG.le_pLayerOf₂ {x : G} {K₁ K₂ : Subgroup G} {q : ℕ} (h : PairG x K₁ K₂ q) {H : Subgroup G}
    (hxH : x ∈ H) (hK₂H : K₂ ≤ H) : K₂ ≤ pLayerOf 2 H :=
  le_pLayerOf_of_comp hxH h.ord hK₂H h.le₂ (Subgroup.isPerfect_iff.mp h.quasi₂.1)
    (isQuasisimple_hat h.quasi₂) h.sub₂

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.Ad
