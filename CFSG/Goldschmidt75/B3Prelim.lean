module

public import CFSG.Goldschmidt75.Sec42K

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped commutatorElement

theorem eq_top_of_le_commutator_sup {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) {H : Subgroup Q} (h : ⊤ ≤ ⁅(⊤ : Subgroup Q), ⊤⁆ ⊔ H) : H = ⊤ := by
  by_contra hH
  obtain ⟨M, hMc, hHM⟩ := (eq_top_or_exists_le_coatom H).resolve_left hH
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := Q)
  have hMn : M.Normal := by
    have h1 : M < normalizer (M : Set Q) := hnc M hMc.1.lt_top
    have h2 : normalizer (M : Set Q) = ⊤ := hMc.2 _ h1
    exact normalizer_eq_top_iff.mp h2
  have hcomm : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ M := by
    have hnt : Nontrivial (Q ⧸ M) := by
      obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hMc.1.lt_top
      exact ⟨⟨QuotientGroup.mk x, 1, fun e => hx ((QuotientGroup.eq_one_iff x).mp e)⟩⟩
    have hp : IsPGroup p (Q ⧸ M) := hQ.to_quotient M
    obtain ⟨k, hk, hcard⟩ := hp.nontrivial_iff_card.mp hnt
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Q ⧸ M) p
      (by rw [hcard]; exact dvd_pow_self p (by omega))
    have htop : zpowers y = ⊤ := by
      have h1 : M ≤ (zpowers y).comap (QuotientGroup.mk' M) := fun m hm => by
        rw [mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff m).mpr hm]
        exact one_mem _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M y
      have h2 : (zpowers (QuotientGroup.mk' M x)).comap (QuotientGroup.mk' M) ≠ M := by
        intro e
        have hx : x ∈ (zpowers (QuotientGroup.mk' M x)).comap (QuotientGroup.mk' M) :=
          mem_comap.mpr (mem_zpowers _)
        rw [e] at hx
        have := (QuotientGroup.eq_one_iff x).mpr hx
        rw [QuotientGroup.mk'_apply, this, orderOf_one] at hy
        exact (Nat.Prime.one_lt Fact.out).ne hy
      have h3 := (hMc.2 _ (lt_of_le_of_ne h1 (Ne.symm h2)))
      rw [eq_top_iff]
      intro z _
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective M z
      exact (h3 ▸ mem_top w : w ∈ (zpowers (QuotientGroup.mk' M x)).comap (QuotientGroup.mk' M))
    rw [commutator_le]
    intro a _ b _
    rw [← QuotientGroup.eq_one_iff]
    have ha : (QuotientGroup.mk a : Q ⧸ M) ∈ zpowers y := htop ▸ mem_top _
    have hb : (QuotientGroup.mk b : Q ⧸ M) ∈ zpowers y := htop ▸ mem_top _
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hb
    rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hi, ← hj, ← zpow_neg, ← zpow_neg,
      ← zpow_add, ← zpow_add, ← zpow_add]
    rw [show i + j + -i + -j = 0 by ring, zpow_zero]
  exact hMc.1 (top_le_iff.mp (h.trans (sup_le hcomm hHM)))

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem fusionIsSylowIn_normalizer (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T) :
    fusionIsSylowIn 2 (T : Subgroup G) (normalizer (S : Set G)) :=
  ⟨sylow_le_normalizer T hST hS, T.isPGroup', fun _ _ hP hTP => T.is_maximal' hP hTP⟩

theorem normalizer_le_sup_centralizer (T : Sylow 2 G) {S : Subgroup G} (hST : S ≤ T)
    (hS : fusionStronglyClosed (S : Set G) T)
    (hN : ∀ n ∈ normalizer (S : Set G), ∃ k : ℕ, n ^ (2 ^ k) ∈ centralizer (S : Set G))
    (hT : (T : Subgroup G) ≤ (⁅normalizer (S : Set G), normalizer (S : Set G)⁆ ⊓ T) ⊔ S) :
    normalizer (S : Set G) ≤ S ⊔ centralizer (S : Set G) := by
  set N := normalizer (S : Set G) with hNdef
  set C := centralizer (S : Set G) with hCdef
  have hSN : S ≤ N := le_normalizer
  have hTN : (T : Subgroup G) ≤ N := sylow_le_normalizer T hST hS
  have hCn : (C.subgroupOf N).Normal := normal_centralizer_subgroupOf S
  set q := QuotientGroup.mk' (C.subgroupOf N) with hq
  have hQ : IsPGroup 2 (N ⧸ C.subgroupOf N) := by
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨k, hk⟩ := hN n n.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.mpr hk
  have hTtop : (T.subgroupOf N).map q = ⊤ := by
    let TQ := (T.subtype hTN).mapSurjective (QuotientGroup.mk'_surjective (C.subgroupOf N))
    have h1 := TQ.is_maximal' (hQ.to_subgroup ⊤) le_top
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype] at h1
    exact h1.symm
  have hNN : ⁅N, N⁆.subgroupOf N = ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ := by
    rw [G37.subgroupOf_commutator le_rfl le_rfl, subgroupOf_self]
  have hcN : ⁅N, N⁆ ≤ N := commutator_le_self N
  have hle : ⊤ ≤ ⁅(⊤ : Subgroup (N ⧸ C.subgroupOf N)), ⊤⁆ ⊔ (S.subgroupOf N).map q := by
    refine hTtop.symm.le.trans ?_
    have h2 : T.subgroupOf N ≤ (⁅N, N⁆ ⊓ T ⊔ S).subgroupOf N :=
      fun x hx => mem_subgroupOf.mpr (hT (mem_subgroupOf.mp hx))
    refine (map_mono h2).trans ?_
    rw [subgroupOf_sup (inf_le_left.trans hcN) hSN, Subgroup.map_sup]
    refine sup_le_sup ?_ le_rfl
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ ⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆ := by
      rw [← hNN]
      exact mem_subgroupOf.mpr (mem_subgroupOf.mp hx).1
    have h3 : q x ∈ (⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map q := ⟨x, hx', rfl⟩
    rw [map_commutator] at h3
    exact commutator_mono le_top le_top h3
  have hStop := eq_top_of_le_commutator_sup hQ hle
  intro n hn
  have h4 : q ⟨n, hn⟩ ∈ (S.subgroupOf N).map q := hStop ▸ mem_top _
  obtain ⟨s, hs, hsn⟩ := h4
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf] at hsn
  have e : n = (s : G) * ((s : G)⁻¹ * n) := by group
  rw [e]
  exact mul_mem_sup (mem_subgroupOf.mp hs) (by simpa using hsn)

end CFSG.Goldschmidt75
