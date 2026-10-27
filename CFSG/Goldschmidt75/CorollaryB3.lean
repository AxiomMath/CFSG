module

public import CFSG.Goldschmidt75.B3Steps
public import CFSG.ClassicalInvolution.Asc77.WP1Defs
public import CFSG.Goldschmidt75.TheoremA
public import CFSG.Goldschmidt75.TheoremBb
public import CFSG.Goldschmidt75.TheoremBc

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

@[expose] def B3For (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (T : Sylow 2 G) (S : Subgroup G), S ≤ T → fusionStronglyClosed (S : Set G) T →
    (∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G)) →
    fusionIsSylowIn 2 S (normalClosure (S : Set G))

variable {G : Type} [Group G] [Finite G]

theorem le_of_b3For_quotient {N : Subgroup G} [N.Normal] (hB : B3For (G ⧸ N)) (T : Sylow 2 G)
    {S : Subgroup G} (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T)
    (hN : ∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G))
    (htop : normalClosure (S : Set G) = ⊤) (hNT : N ⊓ T ≤ S) : (T : Subgroup G) ≤ S := by
  have hsurj := QuotientGroup.mk'_surjective N
  have hN' : ∀ n ∈ normalizer ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)),
      ∃ k : ℕ, n ^ (2 ^ k) ∈
        centralizer ((S.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    intro n hn
    rw [normalizer_map N T hST hS] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    obtain ⟨k, hk⟩ := hN m hm
    refine ⟨k, ?_⟩
    rw [← map_pow, mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hk y hy]
  have h := hB (sylowMap N T) (S.map (QuotientGroup.mk' N))
    (by rw [coe_sylowMap]; exact map_mono hST) (stronglyClosed_map N T hST hS) hN'
  rw [show (S.map (QuotientGroup.mk' N) : Set (G ⧸ N)) = QuotientGroup.mk' N '' (S : Set G) from
    coe_map _ _, ← Subgroup.map_normalClosure _ _ hsurj, htop, map_top_of_surjective _ hsurj] at h
  have hTS := h.2.2 _ le_top (sylowMap N T).isPGroup'
    (by rw [coe_sylowMap]; exact map_mono hST)
  intro t ht
  have h1 : QuotientGroup.mk' N t ∈ S.map (QuotientGroup.mk' N) := by
    rw [← hTS, coe_sylowMap]
    exact ⟨t, ht, rfl⟩
  obtain ⟨s, hs, hst⟩ := h1
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
  have h2 : s⁻¹ * t ∈ S := hNT (mem_inf.mpr ⟨hst, mul_mem (inv_mem (hST hs)) ht⟩)
  have e : t = s * (s⁻¹ * t) := by group
  rw [e]
  exact mul_mem hs h2

theorem fusionIsSylowIn_of_b3For_normalClosure (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T)
    (hN : ∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G))
    (hB : B3For (normalClosure (S : Set G))) :
    fusionIsSylowIn 2 S (normalClosure (S : Set G)) := by
  set H := normalClosure (S : Set G) with hH
  have hSH : S ≤ H := le_normalClosure
  obtain ⟨TH, hTH, -, hcl, -⟩ := exists_sylow_subgroupOf T hST hST hS hS (sup_le hSH hSH)
  have hN' : ∀ n ∈ normalizer ((S.subgroupOf H : Subgroup H) : Set H), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ centralizer ((S.subgroupOf H : Subgroup H) : Set H) := by
    intro n hn
    have hnG : (n : G) ∈ normalizer (S : Set G) := by
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := (mem_normalizer_iff.mp hn ⟨x, hSH hx⟩).mp (mem_subgroupOf.mpr hx)
        exact mem_subgroupOf.mp this
      · intro hx
        have hxH : x ∈ H := by
          have e : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * n := by group
          rw [e]
          exact mul_mem (mul_mem (inv_mem n.2) (hSH hx)) n.2
        have := (mem_normalizer_iff.mp hn ⟨x, hxH⟩).mpr (mem_subgroupOf.mpr hx)
        exact mem_subgroupOf.mp this
    obtain ⟨k, hk⟩ := hN n hnG
    refine ⟨k, mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_⟩
    exact mem_centralizer_iff.mp hk y (mem_subgroupOf.mp hy)
  have h := hB TH _ hTH hcl hN'
  rw [normalClosure_subgroupOf_eq_top T hST hS rfl] at h
  refine ⟨hSH, T.isPGroup'.to_le hST, fun P hPH hP hSP => ?_⟩
  have h1 := h.2.2 (P.subgroupOf H) le_top hP.comap_subtype
    (fun x hx => mem_subgroupOf.mpr (hSP (mem_subgroupOf.mp hx)))
  have h2 := congrArg (Subgroup.map H.subtype) h1
  rwa [map_subgroupOf_eq_of_le hPH, map_subgroupOf_eq_of_le hSH] at h2

theorem le_of_b3_main
    (ih : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → B3For H)
    (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T)
    (hN : ∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G))
    (htop : normalClosure (S : Set G) = ⊤) (hO : goldschmidtOddCore G = ⊥) :
    (T : Subgroup G) ≤ S := by
  set C := centralizer (S : Set G) with hC
  have hGS : (⊤ : Subgroup G) ≤ S ⊔ commutator G := by
    have hn : (S ⊔ commutator G).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have e : g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
      rw [e]
      refine mul_mem (mem_sup_right ?_) hx
      rw [← commutatorElement_def]
      exact commutator_mem_commutator (mem_top g) (mem_top x)
    rw [← htop]
    exact normalClosure_le_normal fun x hx => mem_sup_left hx
  have hT1 : (T : Subgroup G) ≤ (commutator G ⊓ T) ⊔ S := by
    intro t ht
    have ht' : t ∈ ((S ⊔ commutator G : Subgroup G) : Set G) := hGS (mem_top t)
    rw [mul_normal] at ht'
    obtain ⟨s, hs, a, ha, rfl⟩ := ht'
    have haT : a ∈ (T : Subgroup G) := by
      have := mul_mem (inv_mem (hST hs)) ht
      simpa using this
    exact mul_mem (mem_sup_right hs) (mem_sup_left (mem_inf.mpr ⟨ha, haT⟩))
  have hT2 : (T : Subgroup G) ≤ (⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ⊓ T) ⊔ S := by
    rw [← theoremB_b T hST hS]
    exact hT1
  have hNSC := normalizer_le_sup_centralizer T hST hS hN hT2
  have hTRS : (T : Subgroup G) ≤ (⁅C, C⁆ ⊓ T) ⊔ S :=
    hT2.trans (sup_le (commutator_inf_le_of_le_sup hST hNSC) le_sup_right)
  have hRcl : fusionStronglyClosed ((⁅C, C⁆ ⊓ T : Subgroup G) : Set G) T := theoremB_c T hST hS
  have hRC : ⁅C, C⁆ ⊓ (T : Subgroup G) ≤ C := inf_le_left.trans (commutator_le_self C)
  by_cases hA : ⁅C, C⁆ ⊓ (T : Subgroup G) ⊓ S = ⊥
  ·
    have hcomm : ⁅⁅C, C⁆ ⊓ (T : Subgroup G), S⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr hRC
    have hA' := theoremA T T inf_le_right hST hRcl hS hcomm hA
    rw [hO, le_bot_iff, htop] at hA'
    have hRZ : ⁅C, C⁆ ⊓ (T : Subgroup G) ≤ center G := by
      have h1 := commutator_eq_bot_iff_le_centralizer.mp hA'
      rw [coe_top, centralizer_univ] at h1
      exact le_normalClosure.trans h1
    have hR1 := eq_bot_of_le_center T hST hS hTRS hRZ
    rw [hR1, bot_sup_eq] at hTRS
    exact hTRS
  ·
    obtain ⟨z, hzA, hz2, -⟩ := exists_central_involution_of_isPGroup
      (T.isPGroup'.to_le (inf_le_right.trans hST)) hA
    have hzc := mem_center_of_mem_inf T hST hS hRcl hRC hNSC hO (mem_inf.mp hzA).1
      (mem_inf.mp hzA).2 hz2
    have : (zpowers z).Normal := normal_of_le_center (zpowers_le.mpr hzc)
    exact le_of_b3For_quotient (ih _ (card_quotient_lt (zpowers_ne_bot hz2))) T hST hS hN htop
      (inf_le_left.trans (zpowers_le.mpr (mem_inf.mp hzA).2))

theorem b3For
    (G : Type) [Group G] [Finite G] : B3For G := by
  suffices key : ∀ n, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n → B3For G from
    key _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn T S hST hS hN
  have ih' : ∀ (H : Type) [Group H] [Finite H], Nat.card H < Nat.card G → B3For H :=
    fun H _ _ hH => ih _ (hn ▸ hH) H rfl
  by_cases htop : normalClosure (S : Set G) = ⊤
  · have hTS : (T : Subgroup G) ≤ S := by
      by_cases hO : goldschmidtOddCore G = ⊥
      · exact le_of_b3_main ih' T hST hS hN htop hO
      · refine le_of_b3For_quotient (ih' _ (card_quotient_lt hO)) T hST hS hN htop ?_
        intro x hx
        rw [eq_one_of_mem_odd_of_mem_sylow T odd_card_oddCore (mem_inf.mp hx).1
          (mem_inf.mp hx).2]
        exact one_mem _
    rw [htop]
    refine ⟨le_top, T.isPGroup'.to_le hST, fun P _ hP hSP => ?_⟩
    have h1 : P = T := T.is_maximal' hP (hTS.trans hSP)
    exact le_antisymm (h1.le.trans hTS) hSP
  · exact fusionIsSylowIn_of_b3For_normalClosure T hST hS hN (ih' _ (card_lt_of_ne_top htop))

theorem corollaryB3
    {G : Type} [Group G] [Finite G] (T : Sylow 2 G) {S : Subgroup G}
    (hST : S ≤ T) (hS : fusionStronglyClosed (S : Set G) T)
    (hN : ∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G)) :
    fusionIsSylowIn 2 S (normalClosure (S : Set G)) :=
  b3For G T S hST hS hN

theorem goldschmidtB3
    : ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (A : Subgroup G),
    A ≤ (S : Subgroup G) → fusionStronglyClosed (A : Set G) S →
    (∀ n ∈ Subgroup.normalizer (A : Set G), ∃ k : ℕ,
      n ^ (2 ^ k) ∈ Subgroup.centralizer (A : Set G)) →
    CFSG.ClassicalInvolution.Asc77.IsSylow2In A (Subgroup.normalClosure (A : Set G)) :=
  fun G _ _ S _ hAS hA hN => corollaryB3 (G := G) S hAS hA hN

end CFSG.Goldschmidt75
