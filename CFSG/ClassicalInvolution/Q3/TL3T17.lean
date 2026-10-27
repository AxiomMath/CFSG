module

public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

@[expose] def WIn (P : Set (Subgroup G)) (X : Subgroup G) : Set (Subgroup G) :=
  (fun W' : Subgroup X => W'.map X.subtype) '' WSet (restrictFamily P X)

theorem conjInvariant_restrictFamily {P : Set (Subgroup G)} {X : Subgroup G}
    (hinv : ∀ L ∈ P, ∀ x ∈ X, conjSub x L ∈ P) : ConjInvariant (restrictFamily P X) := by
  rintro n _ ⟨L, hL, hLX, rfl⟩
  refine ⟨conjSub (n : G) L, hinv L hL n n.2, ?_, conjSub_subgroupOf X n L⟩
  have := conjSub_mono (n := (n : G)) hLX
  rwa [conjSub_eq_self_of_mem n.2] at this

variable [Finite G]

theorem zpowers_mem_USet {P : Set (Subgroup G)} {N : Subgroup G} (hN : N ∈ P)
    (h2 : IsPGroup 2 N) (h8 : Nat.card N = 8)
    (hnc : ∃ Q : Subgroup G, IsSylow2In Q N ∧ ¬ IsMulCommutative ↥Q) {x : G} (hxN : x ∈ N)
    (hx2 : x * x ≠ 1) : Subgroup.zpowers x ∈ USet P ∧ Nat.card ↥(Subgroup.zpowers x) = 4 := by
  have hxord : orderOf x = 4 := by
    have hdvd : orderOf x ∣ 8 := by
      rw [← h8]
      exact Subgroup.orderOf_dvd_natCard N hxN
    have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, one_mul])
    have hne2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
    have hne1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have hne8 : orderOf x ≠ 8 := by
      intro h
      obtain ⟨Q, hQN, hQnc⟩ := hnc
      have hzN : Subgroup.zpowers x = N := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxN) ?_
        rw [Nat.card_zpowers, h, h8]
      apply hQnc
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have ha : (a : G) ∈ Subgroup.zpowers x := hzN ▸ hQN.1 a.2
      have hb : (b : G) ∈ Subgroup.zpowers x := hzN ▸ hQN.1 b.2
      obtain ⟨i, hi⟩ := ha
      obtain ⟨j, hj⟩ := hb
      show (a : G) * b = b * a
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have : orderOf x ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hUcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by rw [Nat.card_zpowers, hxord]
  refine ⟨⟨N, mem_RSet_of_isPGroup hN h2, Subgroup.zpowers_le.mpr hxN, inferInstance, ?_⟩, hUcard⟩
  have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers x) N
  rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hxN), hUcard, h8] at h1
  omega

theorem exists_sq_ne_one {N : Subgroup G} {z : G} (hz : IsUniqueInvolution N z)
    (h8 : Nat.card N = 8) : ∃ x ∈ N, x * x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsub : (N : Set G) ⊆ ({1, z} : Set G) := by
    intro x hx
    rcases hz.unique x hx (hcon x hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : Nat.card N ≤ ({1, z} : Set G).ncard := by
    rw [← SetLike.coe_sort_coe, ← Nat.card_coe_set_eq]
    exact Nat.card_mono (Set.toFinite _) hsub
  have h3 : ({1, z} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({z} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  omega

theorem false_of_WIn_eq {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (h8 : ∀ J ∈ Ω, Nat.card J = 8) {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω) (hPne : P.Nonempty)
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hthin : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∀ Q : Subgroup G, Q ≤ pSpan P →
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → ∀ x ∈ L, x ∈ Q →
        x = 1 ∨ x = u)
    {W : Subgroup G} (hW : WIn P (pSpan P) = {W}) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pSpan P with hX
  have hc' : ConjInvariant (restrictFamily P X) :=
    conjInvariant_restrictFamily fun L hL x hx => hinv L hL x hx
  have hWmem : W ∈ WIn P X := by rw [hW]; rfl
  obtain ⟨W', hW'mem, rfl⟩ := hWmem
  have hW'uniq : ∀ W'' ∈ WSet (restrictFamily P X), W'' = W' := by
    intro W'' h
    have h1 : W''.map X.subtype ∈ WIn P X := ⟨W'', h, rfl⟩
    rw [hW] at h1
    exact Subgroup.map_injective X.subtype_injective h1
  have hnorm' : ∀ g : X, conjSub g W' = W' := fun g => hW'uniq _ (WSet.conj hc' hW'mem g)
  obtain ⟨η, ⟨S, hη, -⟩, hW'eq⟩ := hW'mem
  have hWS : W' ≤ (S : Subgroup X) := by
    rw [hW'eq]
    exact iSup₂_le fun U hU => (hη.1 hU).2
  have hW2 : IsPGroup 2 ↥(W'.map X.subtype) := (S.isPGroup'.to_le hWS).map _
  have hWX : W'.map X.subtype ≤ X := Subgroup.map_subtype_le _
  have hnorm : ∀ x ∈ X, ∀ q ∈ W'.map X.subtype, x * q * x⁻¹ ∈ W'.map X.subtype := by
    rintro x hx _ ⟨q, hq, rfl⟩
    have h1 : (⟨x, hx⟩ : X) * q * (⟨x, hx⟩ : X)⁻¹ ∈ conjSub (⟨x, hx⟩ : X) W' :=
      conj_mem_conjSub hq
    rw [hnorm'] at h1
    exact ⟨_, h1, rfl⟩
  obtain ⟨L, hL⟩ := hPne
  have hL'2 : IsPGroup 2 ↥(L.subgroupOf X) := (h2 L (hPΩ hL)).comap_subtype
  obtain ⟨S'', hS''⟩ := hL'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S'' S
  have hgS : conjSub g (L.subgroupOf X) ≤ (S : Subgroup X) := by
    rw [← hg, Sec7.coe_smul_sylow]
    exact conjSub_mono hS''
  rw [conjSub_subgroupOf] at hgS
  set L₁ := conjSub (g : G) L with hL₁
  have hL₁P : L₁ ∈ P := hinv L hL g g.2
  have hL₁X : L₁ ≤ X := le_pSpan hL₁P
  obtain ⟨⟨z₁, hz₁⟩, Q₁, hQ₁, hQ₁nc⟩ := hΩ.omega1 L₁ (hPΩ hL₁P)
  have hN'8 : Nat.card ↥(L₁.subgroupOf X) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv]
    exact h8 L₁ (hPΩ hL₁P)
  have hz₁' := isUniqueInvolution_subgroupOf hz₁ hL₁X
  obtain ⟨x', hx'N, hx'2⟩ := exists_sq_ne_one hz₁' hN'8
  have hnc' : ∃ Q : Subgroup X, IsSylow2In Q (L₁.subgroupOf X) ∧ ¬ IsMulCommutative ↥Q := by
    refine ⟨Q₁.subgroupOf X, hQ₁.subgroupOf hL₁X, fun hc => hQ₁nc ?_⟩
    let e : Q₁.subgroupOf X ≃* Q₁ := Subgroup.subgroupOfEquivOfLe (hQ₁.1.trans hL₁X)
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := hc.is_comm.comm _ _
    have h2' := congrArg e h1
    simpa using h2'
  obtain ⟨hU1, -⟩ := zpowers_mem_USet (P := restrictFamily P X) ⟨L₁, hL₁P, hL₁X, rfl⟩
    (h2 L₁ (hPΩ hL₁P)).comap_subtype hN'8 hnc' hx'N hx'2
  have hU1S : Subgroup.zpowers x' ≤ (S : Subgroup X) :=
    (Subgroup.zpowers_le.mpr hx'N).trans hgS
  have hηpos : η.ncard ≠ 0 := by
    have h1 := hη.2.2 {Subgroup.zpowers x'} (by
      intro U hU
      rw [Set.mem_singleton_iff.mp hU]
      exact ⟨hU1, hU1S⟩) (by
      intro U hU U' hU' hne
      exact absurd ((Set.mem_singleton_iff.mp hU).trans (Set.mem_singleton_iff.mp hU').symm) hne)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨U₀, hU₀⟩ := Set.nonempty_of_ncard_ne_zero hηpos
  obtain ⟨hU₀U, -⟩ := hη.1 hU₀
  obtain ⟨R₀, hR₀, hU₀R₀, -, hidx⟩ := hU₀U
  obtain ⟨J₀', hJ₀', hR₀J₀, -, hmax⟩ := mem_RSet_iff.mp hR₀
  obtain ⟨J₀, hJ₀, hJ₀X, rfl⟩ := hJ₀'
  have hJ₀'2 : IsPGroup 2 ↥(J₀.subgroupOf X) := (h2 J₀ (hPΩ hJ₀)).comap_subtype
  have hR₀eq : J₀.subgroupOf X = R₀ := hmax _ le_rfl hJ₀'2 hR₀J₀
  have hU₀card : Nat.card U₀ = 4 := by
    have h1 := Subgroup.relIndex_mul_card U₀ R₀
    rw [inf_eq_left.mpr hU₀R₀, hidx, ← hR₀eq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ₀X).toEquiv, h8 J₀ (hPΩ hJ₀)] at h1
    omega
  obtain ⟨⟨z₀, hz₀⟩, -⟩ := hΩ.omega1 J₀ (hPΩ hJ₀)
  have hU₀W : U₀ ≤ W' := by
    rw [hW'eq]
    exact le_biSup (fun U => U) hU₀
  have hsub : ((U₀.map X.subtype : Subgroup G) : Set G) ⊆ ({1, z₀} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : (u : G) ∈ J₀ := Subgroup.mem_subgroupOf.mp (hR₀J₀ (hU₀R₀ hu))
    rcases hthin J₀ hJ₀ z₀ hz₀ _ hWX hnorm hW2 (u : G) hu' ⟨u, hU₀W hu, rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : Nat.card ↥(U₀.map X.subtype) ≤ ({1, z₀} : Set G).ncard := by
    rw [← SetLike.coe_sort_coe, ← Nat.card_coe_set_eq]
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [Subgroup.card_map_of_injective X.subtype_injective, hU₀card] at hle
  have h3 : ({1, z₀} : Set G).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : G) ({z₀} : Set G)
    rw [Set.ncard_singleton] at this
    exact this
  omega

end CFSG.ClassicalInvolution.Q3.TC.Thin
