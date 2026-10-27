module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S5Chain
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem1
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.Asc76.Sec5

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b

variable {G : Type} [Group G]

theorem card_subgroupOf {X H : Subgroup G} (hXH : X ≤ H) :
    Nat.card (X.subgroupOf H) = Nat.card X :=
  Nat.card_congr (subgroupOfEquivOfLe hXH).toEquiv

theorem subgroupOf_inf_subgroupOf (X Y H : Subgroup G) :
    X.subgroupOf H ⊓ Y.subgroupOf H = (X ⊓ Y).subgroupOf H := by
  ext x
  simp [mem_subgroupOf]

theorem rightConjugate_subgroupOf (X H : Subgroup G) (h : H) :
    rightConjugate (X.subgroupOf H) h = (rightConjugate X h).subgroupOf H := by
  ext y
  rw [mem_rightConjugate_iff, mem_subgroupOf, mem_subgroupOf, mem_rightConjugate_iff]
  simp

theorem mem_normalizer_subgroupOf_iff {X H : Subgroup G} (hXH : X ≤ H) (h : H) :
    h ∈ normalizer ((X.subgroupOf H : Subgroup H) : Set H) ↔
      (h : G) ∈ normalizer (X : Set G) := by
  constructor
  · intro hh
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := (mem_normalizer_iff.mp hh ⟨x, hXH hx⟩).mp (show (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H
        from hx)
      exact this
    · intro hx
      have hxH : x ∈ H := by
        have h1 := H.mul_mem (H.mul_mem (H.inv_mem h.2) (hXH hx)) h.2
        simpa [mul_assoc] using h1
      have := (mem_normalizer_iff.mp hh ⟨x, hxH⟩).mpr (show h * ⟨x, hxH⟩ * h⁻¹ ∈ X.subgroupOf H
        from hx)
      exact this
  · intro hh
    rw [mem_normalizer_iff]
    intro y
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hh y

theorem normalizer_subgroupOf {X H : Subgroup G} (hXH : X ≤ H) :
    normalizer ((X.subgroupOf H : Subgroup H) : Set H) = (normalizer (X : Set G)).subgroupOf H := by
  ext h
  rw [mem_normalizer_subgroupOf_iff hXH, mem_subgroupOf]

theorem isSylowOf_subgroupOf_iff [Finite G] {P X H : Subgroup G} (hPH : P ≤ H) (hXH : X ≤ H) :
    IsSylowOf 2 (P.subgroupOf H) (X.subgroupOf H) ↔ IsSylowOf 2 P X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isSylowOf_map_subtype_iff H, subgroupOf_map_subtype, subgroupOf_map_subtype,
    inf_eq_left.mpr hPH, inf_eq_left.mpr hXH]

theorem oUpperTwoPrime_subgroupOf {X H : Subgroup G} (hXH : X ≤ H) :
    oUpperTwoPrime (X.subgroupOf H) = (oUpperTwoPrime X).subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [subgroupOf_map_subtype, inf_eq_left.mpr ((oUpperTwoPrime_le X).trans hXH), oUpperTwoPrime,
    oUpperTwoPrime, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, mem_subgroupOf, coe_subtype]
  constructor
  · rintro ⟨y, ⟨hy, k, hk⟩, rfl⟩
    exact ⟨hy, k, by simpa using congrArg Subtype.val hk⟩
  · rintro ⟨hx, k, hk⟩
    exact ⟨⟨x, hXH hx⟩, ⟨hx, k, Subtype.ext (by simpa using hk)⟩, rfl⟩

theorem tightlyEmbedded_subgroupOf {K₀ H : Subgroup G} (hK : TightlyEmbedded K₀)
    (hKH : K₀ ≤ H) : TightlyEmbedded (K₀.subgroupOf H) :=
  StandardSubgroupAPI.tightlyEmbedded_subgroupOf hKH hK

theorem normalClosure_subgroupOf_eq_top {K₀ H : Subgroup G} (hKH : K₀ ≤ H)
    (hst : ncIn K₀ H = H) : normalClosure ((K₀.subgroupOf H : Subgroup H) : Set H) = ⊤ := by
  set N := normalClosure ((K₀.subgroupOf H : Subgroup H) : Set H) with hN
  have hle : ncIn K₀ H ≤ N.map H.subtype := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨h, hh, k, hk, rfl⟩
    have hk' : (⟨k, hKH hk⟩ : H) ∈ N :=
      subset_normalClosure (show (⟨k, hKH hk⟩ : H) ∈ ((K₀.subgroupOf H : Subgroup H) : Set H)
        from hk)
    have hmem : (⟨h, hh⟩ : H) * ⟨k, hKH hk⟩ * (⟨h, hh⟩ : H)⁻¹ ∈ N :=
      (normalClosure_normal (s := ((K₀.subgroupOf H : Subgroup H) : Set H))).conj_mem _ hk' _
    exact ⟨_, hmem, rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx : (x : G) ∈ N.map H.subtype := hle (hst.symm ▸ x.2)
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

theorem isSzOrU3_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : IsSzOrU3 Y) :
    IsSzOrU3 X := by
  rcases h with ⟨a, ha, ⟨f⟩⟩ | ⟨b, hb, ⟨f⟩⟩
  · exact Or.inl ⟨a, ha, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨b, hb, ⟨e.trans f⟩⟩

variable [Finite G]

theorem standardComponentOddCore_eq_bot_of {H : Subgroup G}
    (hO : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → Odd (Nat.card N) → N = ⊥) :
    standardComponentOddCore H = ⊥ := by
  rw [standardComponentOddCore, sSup_eq_bot]
  rintro M ⟨hM, hodd⟩
  have hNH : H ≤ normalizer ((M.map H.subtype : Subgroup G) : Set G) := by
    intro h hh
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨⟨h, hh⟩ * m * (⟨h, hh⟩ : H)⁻¹, hM.conj_mem m hm _, ?_⟩
    simp [MulAut.conj_apply]
  have h := hO (M.map H.subtype) (map_subtype_le M) hNH
    (by rwa [card_map_of_injective H.subtype_injective])
  exact (map_eq_bot_iff_of_injective _ H.subtype_injective).mp h

theorem normal_or_isSzOrU3_of_theorem4 (h4 : Asc76Theorem4) {K₀ H : Subgroup G}
    (hK : TightlyEmbedded K₀) (hKH : K₀ ≤ H) (hst : ncIn K₀ H = H)
    (hO : ∀ N : Subgroup G, N ≤ H → H ≤ normalizer (N : Set G) → Odd (Nat.card N) → N = ⊥)
    (hK2 : oUpperTwoPrime K₀ = K₀)
    (hstar : ∀ g ∈ H, Even (Nat.card (rightConjugate K₀ g ⊓ normalizer (K₀ : Set G) :
      Subgroup G)) → ∃ S, IsSylowOf 2 S (rightConjugate K₀ g) ∧ S ≤ normalizer (K₀ : Set G))
    {R : Subgroup G} (hR : IsSylowOf 2 R K₀) (hm : 1 < Open.pRank 2 R)
    (hΦ : ¬ IsElemAbelian 2 R) :
    H ≤ normalizer (K₀ : Set G) ∨ (IsSzOrU3 H ∧ IsSylowOf 2 R H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := K₀.subgroupOf H with hK'def
  have hRH : R ≤ H := hR.le.trans hKH
  have hR' : IsSylowOf 2 (R.subgroupOf H) K' := (isSylowOf_subgroupOf_iff hRH hKH).mpr hR
  have hm' : 1 < Open.pRank 2 (R.subgroupOf H) := by
    obtain ⟨E, hER, hE, hE4⟩ := Asc76X.exists_fourGroup_le hm
    refine Asc76X.one_lt_pRank_of_fourGroup (E := E.subgroupOf H) (fun x hx => hER hx) ?_ ?_
    · exact Asc76X.isElemAbelian_of_mulEquiv (subgroupOfEquivOfLe (hER.trans hRH)).symm hE
    · rw [card_subgroupOf (hER.trans hRH), hE4]
  have hΦ' : ¬ IsElemAbelian 2 (R.subgroupOf H) := fun h =>
    hΦ (Asc76X.isElemAbelian_of_mulEquiv (subgroupOfEquivOfLe hRH) h)
  have hK' : TightlyEmbedded K' := tightlyEmbedded_subgroupOf hK hKH
  have hG' : normalClosure (K' : Set H) = ⊤ := normalClosure_subgroupOf_eq_top hKH hst
  have hK2' : oUpperTwoPrime K' = K' := by rw [hK'def, oUpperTwoPrime_subgroupOf hKH, hK2]
  have hO' : standardComponentOddCore H = ⊥ := standardComponentOddCore_eq_bot_of hO
  have hstar' : ∀ g : H, Even (Nat.card (rightConjugate K' g ⊓ normalizer (K' : Set H) :
      Subgroup H)) → SylowNormalizes (rightConjugate K' g) K' := by
    intro g heven
    have hKgH : rightConjugate K₀ g ≤ H := AschbacherTheorem3.rightConjugate_le_of_mem hKH g.2
    rw [hK'def, rightConjugate_subgroupOf, normalizer_subgroupOf hKH, subgroupOf_inf_subgroupOf,
      card_subgroupOf (inf_le_left.trans hKgH)] at heven
    obtain ⟨S, hS, hSN⟩ := hstar g g.2 heven
    refine ⟨S.subgroupOf H, ?_, fun x hx => (mem_normalizer_subgroupOf_iff hKH x).mpr (hSN hx)⟩
    rw [hK'def, rightConjugate_subgroupOf]
    exact (isSylowOf_subgroupOf_iff (hS.le.trans hKgH) hKgH).mpr hS
  have hset := Asc76X.sec3Setting_of_tightlyEmbedded hK' hG' hK2' hO' hstar' hR' hm' hΦ'
  obtain ⟨-, h2⟩ := h4 H _ hset K' ⟨1, rightConjugate_one K'⟩
  rcases h2 with hn | ⟨hsz, hsyl⟩
  · left
    intro h hh
    refine (mem_normalizer_subgroupOf_iff hKH ⟨h, hh⟩).mp ?_
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hn.conj_mem y hy _
    · intro hy
      have := hn.conj_mem _ hy (⟨h, hh⟩ : H)⁻¹
      simpa [mul_assoc] using this
  · right
    have hsz' : IsSzOrU3 (⊤ : Subgroup H) := hG' ▸ hsz
    refine ⟨isSzOrU3_of_mulEquiv (Subgroup.topEquiv (G := H)).symm hsz', ?_⟩
    have h' : IsSylowOf 2 (R.subgroupOf H) (H.subgroupOf H) := by
      rw [subgroupOf_self]
      exact hG' ▸ hsyl _ hR'
    exact (isSylowOf_subgroupOf_iff hRH le_rfl).mp h'

end CFSG.ComponentClassification.Asc76.Sec5
