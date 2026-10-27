module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4M2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4G3

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem le_normalizer_of_conj {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B) : A ≤ normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => h a ha b hb, fun hb => ?_⟩
  have h' := h a⁻¹ (A.inv_mem ha) (a * b * a⁻¹) hb
  rwa [show a⁻¹ * (a * b * a⁻¹) * (a⁻¹)⁻¹ = b by group] at h'

private theorem card_sup_mul_card_inf_of_normalizes {A C : Subgroup G}
    (hC : C ≤ normalizer (A : Set G)) :
    Nat.card (C ⊔ A : Subgroup G) * Nat.card (A ⊓ C : Subgroup G) =
      Nat.card A * Nat.card C := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hC
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hC
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient C A hC
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf (C ⊔ A))
  have h3 : Nat.card (A.subgroupOf (C ⊔ A)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card (A.subgroupOf C) = Nat.card (A ⊓ C : Subgroup G) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have h5 := Nat.card_congr e.toEquiv
  rw [h2, h3, ← h5, ← h4, mul_comm (Nat.card _) (Nat.card A), mul_assoc, ← h1]

private theorem isCyclic_quotient_of_le_sup {V N : Subgroup G} [(N.subgroupOf V).Normal]
    (hNV : N ≤ V) {q : G} (hqV : q ∈ V)
    (hle : V ≤ N ⊔ zpowers q) : IsCyclic (↥V ⧸ N.subgroupOf V) := by
  have hVnorm : V ≤ normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mp inferInstance
  have hqZpV : zpowers q ≤ V := zpowers_le.mpr hqV
  have hnorm' : ∀ a ∈ zpowers q, ∀ c ∈ N, a * c * a⁻¹ ∈ N := fun a ha c hc =>
    (Subgroup.mem_normalizer_iff.mp (hVnorm (hqZpV ha)) c).mp hc
  refine ⟨⟨QuotientGroup.mk' (N.subgroupOf V) ⟨q, hqV⟩, fun z => ?_⟩⟩
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf V) z
  obtain ⟨w, hw, c, hc, hwc⟩ := mem_sup_of_normalizes (T := zpowers q) (C := N) hnorm'
    (u : G) (by rw [sup_comm]; exact hle u.2)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨k, ?_⟩
  change (QuotientGroup.mk' (N.subgroupOf V) ⟨q, hqV⟩) ^ k =
    QuotientGroup.mk' (N.subgroupOf V) u
  rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  have : ((((⟨q, hqV⟩ : V) ^ k)⁻¹ * u : V) : G) = c := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
    rw [hwc]
    group
  rw [this]
  exact hc

theorem y4_S2_le_T2 (c : Ctx4 s e) : y4S2 s ≤ s.T₂ :=
  sup_le ((y4_M2_le_C2 c.toF33).trans (y4_C2_le_T2 s)) (y4_S_le_T2 s)

theorem y4_T2_le_norm_S2 (c : Ctx4 s e) : s.T₂ ≤ normalizer (y4S2 s : Set G) := by
  have hTM : s.T ≤ normalizer (M2 s : Set G) :=
    le_normalizer_of_conj fun x hx m hm =>
      y54_M2_inv c.toF33 x (f3_T_le_N c.toF33 hx) m hm
  have hTS : s.T ≤ normalizer (s.fr.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s3_S_le_T s)).mp (s3_S_normal_T s c.hS)
  have hT : s.T ≤ normalizer (y4S2 s : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup (M2 s) s.fr.S
      (Subgroup.mem_inf.mpr ⟨hTM hx, hTS hx⟩)
  have htN : s.t ∈ normalizer (y4S2 s : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup (M2 s) s.fr.S
      (Subgroup.mem_inf.mpr ⟨hTM (s3_t_mem_T s), hTS (s3_t_mem_T s)⟩)
  have hC2N : s.C₂ ≤ normalizer (y4S2 s : Set G) := by
    intro x hx
    rcases y4_C2_cases c x hx with hxM | ⟨m, hm, rfl⟩
    · exact Subgroup.le_normalizer (H := y4S2 s) (Subgroup.mem_sup_left hxM)
    · exact (Subgroup.normalizer (y4S2 s : Set G)).mul_mem
        (Subgroup.le_normalizer (H := y4S2 s) (Subgroup.mem_sup_left hm)) htN
  exact sup_le hT hC2N

theorem y4_M2_inf_S (c : Ctx4 s e) : M2 s ⊓ s.fr.S = s.fr.B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM2, hxS⟩ := hx
    have hxY : x ∈ f3Y s := f3_C₂_le_Y c.toF33 (y4_M2_le_C2 c.toF33 hxM2)
    have hphi : f3phi s x = 1 := by
      unfold f3phi
      rw [s3_comm_t_of_mem_L s (s3_S_le_L s hxS)]
      group
    have hxC2 : x ∈ s.C₂ := y4_M2_le_C2 c.toF33 hxM2
    have hxY1 : x ∈ f3Y1 s := by rwa [f3_C₂_eq_Y1 c.toF33] at hxC2
    have hxX0 : x ∈ f3X0 s := (f3_phi_eq_one c.toF33 x hxY).mp hphi
    have hxP : x ∈ f3P s := by
      rw [← f3_Y1_inf_X0 c.toF33]
      exact ⟨hxY1, hxX0⟩
    rw [← y4_M2_inf_P c]
    exact ⟨hxM2, hxP⟩
  · exact le_inf le_sup_right (s3_B_le_S s)

theorem y4_card_S2 (c : Ctx4 s e) : Nat.card ↥(y4S2 s) = 256 := by
  have hSM : s.fr.S ≤ normalizer (M2 s : Set G) :=
    le_normalizer_of_conj fun x hx m hm =>
      y54_M2_inv c.toF33 x (f3_T_le_N c.toF33 (s3_S_le_T s hx)) m hm
  have h := card_sup_mul_card_inf_of_normalizes (A := M2 s) (C := s.fr.S) hSM
  rw [show (s.fr.S ⊔ M2 s : Subgroup G) = y4S2 s by rw [sup_comm]; rfl,
    y4_M2_inf_S c, y4_card_M2 c, y54_card_S c.toF33, y54_card_B c.toF33] at h
  omega

theorem y4_relIndex_M2_S2 (c : Ctx4 s e) : (M2 s).relIndex (y4S2 s) = 2 := by
  have h := Subgroup.relIndex_mul_card (H := M2 s) (K := y4S2 s)
  have hinf : M2 s ⊓ y4S2 s = M2 s := inf_eq_left.mpr (le_sup_left : M2 s ≤ y4S2 s)
  rw [hinf, y4_card_M2 c, y4_card_S2 c] at h
  omega

theorem y4_S2_secProp (c : Ctx4 s e) (h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂) :
    SecProp s.T₂ (y4S2 s) (fun Y _ _ _ => IsCyclic Y) := by
  have hn : ((y4S2 s).subgroupOf s.T₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (y4_S2_le_T2 c)).mpr (y4_T2_le_norm_S2 c)
  refine ⟨hn, ?_⟩
  obtain ⟨q, hqT2, hgen⟩ : ∃ q : G, q ∈ s.T₂ ∧ s.T₂ ≤ y4S2 s ⊔ zpowers q := by
    by_cases hRT : s.R = s.T
    · refine ⟨s.t, y4_t_mem_T2 s, ?_⟩
      have hT : s.T ≤ y4S2 s ⊔ zpowers s.t :=
        (y4_T_le_St c.toF33 hRT).trans
          (sup_le ((le_sup_right : s.fr.S ≤ y4S2 s).trans le_sup_left) le_sup_right)
      have hC2 : s.C₂ ≤ y4S2 s ⊔ zpowers s.t := by
        intro x hx
        rcases y4_C2_cases c x hx with hxM | ⟨m, hm, rfl⟩
        · exact Subgroup.mem_sup_left (show x ∈ y4S2 s from Subgroup.mem_sup_left hxM)
        · exact Subgroup.mul_mem_sup
            (show m ∈ y4S2 s from Subgroup.mem_sup_left hm)
            (Subgroup.mem_zpowers s.t)
      exact sup_le hT hC2
    · obtain ⟨g, hgT, hgR, hgσ, hg2⟩ := (c.hDef.1 hRT).2
      have hg_sq : g ^ 2 = s.t := y4_g_sq c h42 hgT hgR hgσ hg2
      have htZp : s.t ∈ zpowers g := by
        rw [← hg_sq]
        exact Subgroup.pow_mem (zpowers g) (Subgroup.mem_zpowers g) 2
      refine ⟨g, y4_T_le_T2 s hgT, ?_⟩
      have hT : s.T ≤ y4S2 s ⊔ zpowers g :=
        (y4_T_le_Sgt c.toF33 hRT hgT hgσ).trans
          (sup_le (sup_le ((le_sup_right : s.fr.S ≤ y4S2 s).trans le_sup_left) le_sup_right)
            ((Subgroup.zpowers_le.mpr htZp).trans le_sup_right))
      have hC2 : s.C₂ ≤ y4S2 s ⊔ zpowers g := by
        intro x hx
        rcases y4_C2_cases c x hx with hxM | ⟨m, hm, rfl⟩
        · exact Subgroup.mem_sup_left (show x ∈ y4S2 s from Subgroup.mem_sup_left hxM)
        · exact Subgroup.mul_mem_sup
            (show m ∈ y4S2 s from Subgroup.mem_sup_left hm)
            htZp
      exact sup_le hT hC2
  exact isCyclic_quotient_of_le_sup (y4_S2_le_T2 c) hqT2 hgen

end CFSG.OddStandard.HigherRank.YamadaG23
