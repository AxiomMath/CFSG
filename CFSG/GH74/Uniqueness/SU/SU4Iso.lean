module

public import CFSG.GH74.Uniqueness.SU.SU4Sylow
public import CFSG.GH74.Uniqueness.SU.SU1Graph2
public import CFSG.GH74.Uniqueness.SU.SU1BgTwoRank

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G]

theorem conjSub_eq_of_comm {c : G} {V : Subgroup G} (h : ∀ v ∈ V, v * c = c * v) :
    conjSub c V = V := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro hy
    have h1 := h _ hy
    have h2 : c⁻¹ * y * c = y := by
      apply mul_right_cancel (b := c)
      calc c⁻¹ * y * c * c = c * (c⁻¹ * y * c) := h1
        _ = y * c := by group
    rw [h2] at hy
    exact hy
  · intro hy
    have h1 := h _ hy
    have : c⁻¹ * y * c = y := by
      calc c⁻¹ * y * c = c⁻¹ * (c * y) := by rw [← h1]; group
        _ = y := by group
    rw [this]
    exact hy

section Finite

variable [Finite G]

theorem IsIsolatedVertex.absorbs {X V F : Subgroup G} (hV : IsIsolatedVertex X V) (hFX : F ≤ X)
    (hF : Open.IsElemAbelian 2 F) (hcomm : ∀ f ∈ F, ∀ v ∈ V, f * v = v * f)
    (hcard : 4 ≤ Nat.card F) : F = V := by
  obtain ⟨h4, hiso⟩ := hV
  exact SU1.isolated_absorbs Nat.prime_two (A := ⟨V, h4⟩) hiso hFX hF hcomm (by simpa using hcard)

theorem IsIsolatedVertex.mem_of_commute {X V : Subgroup G} (hV : IsIsolatedVertex X V) {c : G}
    (hcX : c ∈ X) (hc2 : c * c = 1) (hcomm : ∀ v ∈ V, c * v = v * c) : c ∈ V := by
  have hV4 := hV.isFour
  have hFel : Open.IsElemAbelian 2 (V ⊔ zpowers c) :=
    SU1.IsElemAbelian.sup hV4.2.1 (SU1.isElemAbelian_zpowers (by rw [pow_two]; exact hc2))
      (by
        rintro a ha b ⟨n, rfl⟩
        exact (Commute.zpow_right (show Commute a c from (hcomm a ha).symm) n).eq)
  have hFX : V ⊔ zpowers c ≤ X := sup_le hV4.1 (Subgroup.zpowers_le.mpr hcX)
  have hFcomm : ∀ f ∈ V ⊔ zpowers c, ∀ v ∈ V, f * v = v * f := fun f hf v hv =>
    (SU1.isElemAbelian_iff.mp hFel).1 f hf v (Subgroup.mem_sup_left hv)
  have hcard : 4 ≤ Nat.card ↥(V ⊔ zpowers c) := by
    have := Subgroup.card_le_of_le (le_sup_left : V ≤ V ⊔ zpowers c)
    rw [hV4.2.2] at this
    simpa using this
  have h := hV.absorbs hFX hFel hFcomm hcard
  have hc : c ∈ V ⊔ zpowers c := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  rwa [h] at hc

omit [Finite G] in
theorem le_normalizer_zpowers_of_central {S : Subgroup G} {z : G} (hz : ∀ s ∈ S, s * z = z * s) :
    S ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc : Commute s z := hz s hs
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have := (Commute.zpow_right hc n).eq
    show z ^ n = s * z ^ n * s⁻¹
    rw [this]; group
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : z ^ n = s * y * s⁻¹ := hn
    show z ^ n = y
    calc z ^ n = s⁻¹ * z ^ n * s := by
          have := (Commute.zpow_right hc.inv_left n).eq
          rw [this]; group
      _ = s⁻¹ * (s * y * s⁻¹) * s := by rw [hn']
      _ = y := by group

end Finite

variable {G : Type} [Group G]

section Finite

variable [Finite G]

theorem ne_bot_of_rank_three {S : Subgroup G} (h3 : 3 ≤ Open.pRank 2 S) : S ≠ ⊥ := by
  obtain ⟨E, hES, hE, hEc⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two h3
  intro h
  have := Subgroup.card_le_of_le hES
  rw [hEc, h, Subgroup.card_bot] at this
  omega

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers {w y : G} (hw : w * w = 1) (hy : y ∈ zpowers w) :
    y = 1 ∨ y = w := by
  obtain ⟨n, hn⟩ := hy
  have hn' : w ^ n = y := hn
  have h2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hw
  have : w ^ n = w ^ (n % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv n 2, zpow_add, zpow_mul, h2]
    simp
  have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hm with h | h
  · left; rw [← hn', this, h]; simp
  · right; rw [← hn', this, h]; simp

omit [Finite G] in
theorem exists_mem_ne_one {V : Subgroup G} (h : 1 < Nat.card V) : ∃ x ∈ V, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr hcon
  rw [this, Subgroup.card_bot] at h
  omega

theorem exists_mem_not_mem_zpowers {V : Subgroup G} {x : G} (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hV : Nat.card V = 4) : ∃ w ∈ V, w ∉ zpowers x := by
  by_contra hcon
  push Not at hcon
  have hle : V ≤ zpowers x := hcon
  have h1 := Subgroup.card_le_of_le hle
  have hord : orderOf x = 2 := by
    have : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  rw [Nat.card_zpowers, hord, hV] at h1
  omega

theorem four_lt_card_centralizer {S W : Subgroup G} (hS : IsPGroup 2 S)
    (h3 : 3 ≤ Open.pRank 2 S) (hW : IsIsolatedVertex S W) :
    4 < Nat.card ↥(centralizer (W : Set G) ⊓ S) := by
  by_contra hcon
  have hle : Nat.card ↥(centralizer (W : Set G) ⊓ S) ≤ 4 := not_lt.mp hcon
  obtain ⟨h4, hiso⟩ := hW
  obtain ⟨z₀, hz₀S, hz₀2, hz₀1, hz₀c⟩ := exists_central_involution hS (ne_bot_of_rank_three h3)
  have hz₀2' : z₀ ^ 2 = 1 := by rw [pow_two]; exact hz₀2
  obtain ⟨hnot, hall⟩ := SU1.ig10_21_iii Nat.prime_two hS h3 (exists_isNormalEp2 hS h3)
    ⟨W, h4⟩ hiso (E := zpowers z₀) (Subgroup.zpowers_le.mpr hz₀S)
    (le_normalizer_zpowers_of_central hz₀c) (SU1.isElemAbelian_zpowers hz₀2')
    (by rwa [Ne, Subgroup.zpowers_eq_bot])
  obtain ⟨a, haW, haE⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hcent := (hall a haW haE).2.1
  have hc4 : Nat.card ↥(S ⊓ centralizer ({a} : Set G)) ≤ 4 := by
    rw [inf_comm, ← hcent]
    exact hle
  have haS : a ∈ S := h4.1 haW
  have h8 := eight_lt_card_of_rank_three h3 haS hc4
  have := SU1.ig10_24_25 hS h8 haS hc4
  omega

theorem le_of_isSylowIn_centralizer {X V S₁ : Subgroup G} (hV : IsFour X V)
    (hS₁ : IsSylowIn (centralizer (V : Set G) ⊓ X) S₁) : V ≤ S₁ := by
  have hVel := SU1.isElemAbelian_iff.mp hV.2.1
  have hVC : V ≤ centralizer (V : Set G) ⊓ X := by
    refine le_inf (fun v hv => ?_) hV.1
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact hVel.1 w hw v hv
  have hVp : IsPGroup 2 V := IsPGroup.of_card hV.2.2
  obtain ⟨c, hc, hcV⟩ := hS₁.exists_conj_le hVC hVp
  have hcomm : ∀ v ∈ V, v * c⁻¹ = c⁻¹ * v := by
    intro v hv
    have h1 : v * c = c * v := Subgroup.mem_centralizer_iff.mp hc.1 v hv
    have := (Commute.inv_right (show Commute v c from h1)).eq
    exact this
  rwa [conjSub_eq_of_comm hcomm] at hcV

theorem mem_of_mul_self_eq_one {X V S₁ : Subgroup G} (hV : IsIsolatedVertex X V)
    (hS₁ : IsSylowIn (centralizer (V : Set G) ⊓ X) S₁) {s : G} (hs : s ∈ S₁)
    (hs2 : s * s = 1) : s ∈ V := by
  have hsC := hS₁.1 hs
  exact hV.mem_of_commute hsC.2 hs2 (fun v hv => (Subgroup.mem_centralizer_iff.mp hsC.1 v hv).symm)

theorem lt_of_isSylowIn_centralizer {X V S₁ : Subgroup G}
    (hX : 3 ≤ Open.pRank 2 X) (hV : IsIsolatedVertex X V)
    (hS₁ : IsSylowIn (centralizer (V : Set G) ⊓ X) S₁) : V < S₁ := by
  have hV4 := hV.isFour
  have hVS₁ := le_of_isSylowIn_centralizer hV4 hS₁
  refine lt_of_le_of_ne hVS₁ (fun hEq => ?_)
  obtain ⟨S, hS, hS₁S⟩ := exists_isSylowIn_ge (hS₁.1.trans inf_le_right) hS₁.2.1
  have hSX := hS.1
  have hSrk : 3 ≤ Open.pRank 2 S := by rw [hS.pRank_eq]; exact hX
  have hVS : IsIsolatedVertex S V := hV.mono hSX (hVS₁.trans hS₁S)
  have h4 := four_lt_card_centralizer hS.2.1 hSrk hVS
  have hle : Nat.card ↥(centralizer (V : Set G) ⊓ S) ≤ Nat.card S₁ :=
    hS₁.card_le (inf_le_inf_left _ hSX) (hS.2.1.to_le inf_le_right)
  rw [← hEq, hV4.2.2] at hle
  omega

end Finite

variable {G : Type} [Group G] [Finite G]

theorem exists_x_rank_two {X V S₁ : Subgroup G} (hX : 3 ≤ Open.pRank 2 X)
    (hV : IsIsolatedVertex X V) (hS₁ : IsSylowIn (centralizer (V : Set G) ⊓ X) S₁) :
    ∃ x ∈ V, x ≠ 1 ∧ Open.pRank 2 (centralizer ({x} : Set G) ⊓ X) = 2 := by
  by_contra hcon
  push Not at hcon
  have hV4 := hV.isFour
  have hVel := SU1.isElemAbelian_iff.mp hV4.2.1
  have hlt := lt_of_isSylowIn_centralizer hX hV hS₁
  have hVS₁ : V ≤ S₁ := hlt.le
  obtain ⟨s, hsS₁, hsV⟩ : ∃ s ∈ S₁, s ∉ V := by
    by_contra h
    push Not at h
    exact hlt.ne (le_antisymm hVS₁ h)
  obtain ⟨y, hyS₁, -, -, hyyV, hyy1⟩ := exists_orderOf_four hS₁.2.1
    (fun v hv => by rw [← pow_two]; exact hVel.2 v hv)
    (fun t ht h => mem_of_mul_self_eq_one hV hS₁ ht h) hsS₁ hsV
  have key : ∀ x ∈ V, x ≠ 1 → y * y = x := by
    intro x hxV hx1
    have hxC : V ≤ centralizer ({x} : Set G) ⊓ X := by
      refine le_inf (fun v hv => ?_) hV4.1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hVel.1 v hv x hxV
    have hrk3 : 3 ≤ Open.pRank 2 (centralizer ({x} : Set G) ⊓ X) := by
      have h2 : 2 ≤ Open.pRank 2 (centralizer ({x} : Set G) ⊓ X) :=
        SU1.le_pRank (by norm_num) hxC hV4.2.1 hV4.2.2
      have := hcon x hxV hx1
      omega
    have hS₁C : S₁ ≤ centralizer ({x} : Set G) ⊓ X :=
      hS₁.1.trans (inf_le_inf_right X (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxV)))
    obtain ⟨Sx, hSx, hS₁Sx⟩ := exists_isSylowIn_ge hS₁C hS₁.2.1
    have hSxX : Sx ≤ X := hSx.1.trans inf_le_right
    have hSxC : Sx ≤ centralizer ({x} : Set G) := hSx.1.trans inf_le_left
    have hrkSx : 3 ≤ Open.pRank 2 Sx := by rw [hSx.pRank_eq]; exact hrk3
    have hVSx : IsIsolatedVertex Sx V := hV.mono hSxX (hVS₁.trans hS₁Sx)
    obtain ⟨Ux, hUx⟩ := exists_isNormalEp2 hSx.2.1 hrkSx
    have hnc : ∃ v ∈ V, ∃ u ∈ Ux, v * u ≠ u * v := by
      by_contra hc
      push Not at hc
      have hUx4 : IsFour Sx Ux := ⟨hUx.1, hUx.2.2.1, hUx.2.2.2⟩
      have heq : Ux = V := hVSx.eq_of_commute hUx4 hc
      obtain ⟨h4, hiso⟩ := hVSx
      exact SU1.not_isIsolated_of_isNormalEp2 Nat.prime_two hSx.2.1 hrkSx hUx ⟨V, h4⟩ heq.symm hiso
    have hrel : (centralizer (Ux : Set G)).relIndex Sx ≤ 2 :=
      (SU1.ig10_20_ii Nat.prime_two hSx.2.1 hUx).2.1
    have hyyC : y * y ∈ centralizer (Ux : Set G) := sq_mem_of_relIndex_le_two hrel (hS₁Sx hyS₁)
    by_contra hne
    obtain ⟨v, hv, u, hu, hvu⟩ := hnc
    have hxu : x ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_singleton_iff.mp (hSxC (hUx.1 hu)))).symm
    have hyyu : y * y ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hyyC u hu).symm
    have hx2 : x * x = 1 := by rw [← pow_two]; exact hVel.2 x hxV
    have hyy2 : (y * y) ^ 2 = 1 := hVel.2 _ hyyV
    have hyyn : y * y ∉ zpowers x := by
      intro hm
      rcases eq_one_or_eq_of_mem_zpowers hx2 hm with h | h
      · exact hyy1 h
      · exact hne h
    obtain ⟨hel, hcard⟩ := SU1.isElemAbelian_card_sup_zpowers Nat.prime_two
      (by rw [pow_two]; exact hx2) hyy2 hx1 hyyn (hVel.1 x hxV _ hyyV)
    have hgen : zpowers x ⊔ zpowers (y * y) = V :=
      Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hxV)
        (Subgroup.zpowers_le.mpr hyyV)) (by rw [hcard, hV4.2.2])
    have hle : zpowers x ⊔ zpowers (y * y) ≤ centralizer ({u} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr hxu) (Subgroup.zpowers_le.mpr hyyu)
    rw [hgen] at hle
    exact hvu (Subgroup.mem_centralizer_singleton_iff.mp (hle hv))
  obtain ⟨x₁, hx₁V, hx₁1⟩ := exists_mem_ne_one (V := V) (by rw [hV4.2.2]; norm_num)
  have hx₁2 : x₁ * x₁ = 1 := by rw [← pow_two]; exact hVel.2 x₁ hx₁V
  obtain ⟨x₂, hx₂V, hx₂n⟩ := exists_mem_not_mem_zpowers hx₁2 hx₁1
    (by rw [hV4.2.2]; norm_num)
  have hx₂1 : x₂ ≠ 1 := fun h => hx₂n (h ▸ Subgroup.one_mem _)
  have h1 := key x₁ hx₁V hx₁1
  have h2 := key x₂ hx₂V hx₂1
  exact hx₂n (by rw [← h2, h1]; exact Subgroup.mem_zpowers x₁)

end CFSG.GH74.Uniqueness.SU.SU4
