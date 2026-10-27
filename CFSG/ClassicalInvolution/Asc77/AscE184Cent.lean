module

public import CFSG.ClassicalInvolution.Asc77.AscE184Layer

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem isSylow2In_inf_of_le_normalizer {V X Y : Subgroup G} (hV : IsSylow2In V X) (hYX : Y ≤ X)
    (hn : X ≤ Subgroup.normalizer (Y : Set G)) : IsSylow2In (V ⊓ Y) Y := by
  refine ⟨inf_le_right, hV.2.1.to_le inf_le_left, ?_⟩
  intro T hTY hT2 hle
  obtain ⟨V', hV', hTV'⟩ := IsSylow2In.exists_ge hT2 (hTY.trans hYX)
  obtain ⟨x, hx⟩ := exists_conjSub_eq_of_sylow (G := ↥X) (AscQuot.sylowOfIsSylow2In' hV)
    (AscQuot.sylowOfIsSylow2In' hV')
  have hVx : conjSub (x : G) V ≤ X := by
    have := conjSub_mono (n := (x : G)) hV.1
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hV'eq : V' = conjSub (x : G) V := by
    have h1 : (conjSub (x : G) V).subgroupOf X = V'.subgroupOf X := by
      rw [← conjSub_subgroupOf X x V]
      exact hx
    have h2 := Subgroup.subgroupOf_inj.mp h1
    rwa [inf_eq_left.mpr hVx, inf_eq_left.mpr hV'.1, eq_comm] at h2
  have hxY : conjSub (x : G)⁻¹ Y = Y :=
    mem_normalizer_iff_conjSub_eq.mp ((Subgroup.normalizer (Y : Set G)).inv_mem (hn x.2))
  have hTV : conjSub (x : G)⁻¹ T ≤ V ⊓ Y := by
    refine le_inf ?_ ?_
    · have := conjSub_mono (n := (x : G)⁻¹) (hTV'.trans hV'eq.le)
      rwa [conjSub_inv_conjSub] at this
    · have := conjSub_mono (n := (x : G)⁻¹) hTY
      rwa [hxY] at this
  have hcard : Nat.card T ≤ Nat.card ↥(V ⊓ Y) := by
    have h1 : Nat.card ↥(conjSub (x : G)⁻¹ T) = Nat.card T :=
      (Nat.card_congr (Subgroup.equivMapOfInjective T (MulAut.conj (x : G)⁻¹).toMonoidHom
        (MulAut.conj (x : G)⁻¹).injective).toEquiv).symm
    rw [← h1]
    exact Subgroup.card_le_of_le hTV
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

section Hull

variable {X : Subgroup G}

@[expose] def memberHull (Ω : Set (Subgroup G)) (X : Subgroup G) : Subgroup G :=
  ⨆ J ∈ {J | J ∈ Ω ∧ J ≤ X}, J

omit [Finite G] in
theorem le_memberHull {J : Subgroup G} (hJ : J ∈ Ω) (hJX : J ≤ X) : J ≤ memberHull Ω X :=
  le_iSup₂_of_le J ⟨hJ, hJX⟩ le_rfl

omit [Finite G] in
theorem memberHull_le : memberHull Ω X ≤ X :=
  iSup₂_le fun _ hJ => hJ.2

omit [Finite G] in
theorem conjSub_memberHull_le (hΩ : ConjInvariant Ω) {x : G} (hx : x ∈ X) :
    conjSub x (memberHull Ω X) ≤ memberHull Ω X := by
  unfold memberHull conjSub
  rw [Subgroup.map_iSup]
  refine iSup_le fun L => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hL => ?_
  refine le_memberHull (hΩ x L hL.1) ?_
  have := conjSub_mono (n := x) hL.2
  rwa [conjSub_eq_self_of_mem hx] at this

omit [Finite G] in
theorem le_normalizer_memberHull (hΩ : ConjInvariant Ω) :
    X ≤ Subgroup.normalizer (memberHull Ω X : Set G) := by
  intro x hx
  refine mem_normalizer_iff_conjSub_eq.mpr (le_antisymm (conjSub_memberHull_le hΩ hx) ?_)
  have := conjSub_mono (n := x) (conjSub_memberHull_le hΩ (X.inv_mem hx))
  rwa [conjSub_conjSub_inv] at this

end Hull

variable (p f)

@[expose] def E18_4M : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ X : Subgroup G, K ≤ X → K' ≤ X → X ≠ ⊤ → IsSylow2In ((S : Subgroup G) ⊓ X) X → X ≤ H

theorem e18_4M (h3 : E18_3 p f) (h69 : L6_9 p f) (h611 : L6_11 p f) : E18_4M p f := by
  intro G _ _ Ω K S R W H c K' hK'tw hK'ne R' hR' hR'K' hR'S X hKX hK'X hX hS
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hp hq hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hp hq hΩ
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  set Y : Subgroup G := memberHull Ω X with hYdef
  have hYX : Y ≤ X := memberHull_le
  have hKY : K ≤ Y := le_memberHull hK hKX
  have hK'Y : K' ≤ Y := le_memberHull hK'tw.1 hK'X
  have hYtop : Y ≠ ⊤ := fun h => hX (top_le_iff.mp (h ▸ hYX))
  have hgen : Y ≤ ⨆ J ∈ {J | J ∈ Ω ∧ J ≤ Y}, J :=
    iSup₂_le fun L hL => le_iSup₂_of_le L ⟨hL.1, le_memberHull hL.1 hL.2⟩ le_rfl
  have hnorm : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_memberHull hΩ.conjInvariant
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ Y) Y := by
    have := isSylow2In_inf_of_le_normalizer hS hYX hnorm
    rwa [inf_assoc, inf_eq_right.mpr hYX] at this
  have hYH : Y ≤ H :=
    c.layer_le_H hEA hEM (h3 G Ω K S R W H c) hK'tw hK'ne hR' hR'K' hR'S hYtop
      hKY hK'Y hgen hSY
  exact fun x hx => c.normalizer_le_of_le hEA hEM (hRK.trans hKY) hYH (hnorm hx)

@[expose] def E18_4C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCex p f Ω K S R W H →
      ∀ K' ∈ twinSet Ω K, K' ≠ K → ∀ R' ∈ RSet Ω, R' ≤ K' → R' ≤ (S : Subgroup G) →
        ∀ A : Subgroup G, IsPGroup 2 A → R ⊔ R' ≤ Subgroup.centralizer (A : Set G) →
          Subgroup.centralizer (A : Set G) ≠ ⊤ →
          IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer (A : Set G))
            (Subgroup.centralizer (A : Set G)) → Subgroup.centralizer (A : Set G) ≤ H

omit [Finite G] in
private theorem centralizer_zpowers_eq_singleton (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) =
      Subgroup.centralizer ({x} : Set G) := by
  ext y
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq, SetLike.mem_coe]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (show Commute x y from h) k).eq

theorem e18_4C_element (h : E18_4C p f) {Ω : Set (Subgroup G)} {K : Subgroup G} {S : Sylow 2 G}
    {R W H : Subgroup G} (c : MinCex p f Ω K S R W H) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K)
    (hK'ne : K' ≠ K) {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) {x : G} (hx : ∃ n : ℕ, orderOf x = 2 ^ n)
    (hRx : R ⊔ R' ≤ Subgroup.centralizer ({x} : Set G))
    (hX : Subgroup.centralizer ({x} : Set G) ≠ ⊤)
    (hS : IsSylow2In ((S : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
      (Subgroup.centralizer ({x} : Set G))) : Subgroup.centralizer ({x} : Set G) ≤ H := by
  obtain ⟨n, hn⟩ := hx
  have hA : IsPGroup 2 ↥(Subgroup.zpowers x) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have key := h G Ω K S R W H c K' hK' hK'ne R' hR' hR'K' hR'S (Subgroup.zpowers x) hA
  rw [centralizer_zpowers_eq_singleton] at key
  exact key hRx hX hS

theorem e18_5_of_layer (h3 : E18_3 p f) (h69 : L6_9 p f) (h611 : L6_11 p f) : E18_5 p f := by
  intro G _ _ Ω K S R W H c
  by_contra hX
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hEA : EtaAbelian Ω := EtaAbelian.of_l6_9 h69 hp hq hΩ
  have hEM : EtaMeet Ω := EtaMeet.of_l6_11 h611 hp hq hΩ
  obtain ⟨K', hK'tw, hK'ne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hKX : K ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K c.stand.mem le_rfl
  have hK'X : K' ≤ ⨆ J ∈ Ω, J := le_iSup₂_of_le K' hK'tw.1 le_rfl
  have hnorm : (⨆ J ∈ Ω, J : Subgroup G).Normal := omegaGen_normal hΩ.conjInvariant
  have hgen : (⨆ J ∈ Ω, J : Subgroup G) ≤ ⨆ J ∈ {J | J ∈ Ω ∧ J ≤ (⨆ J ∈ Ω, J : Subgroup G)}, J :=
    iSup₂_le fun J hJ => le_iSup₂_of_le J ⟨hJ, le_iSup₂_of_le J hJ le_rfl⟩ le_rfl
  have hSY : IsSylow2In ((S : Subgroup G) ⊓ (⨆ J ∈ Ω, J : Subgroup G))
      (⨆ J ∈ Ω, J : Subgroup G) := by
    refine isSylow2In_inf_of_le_normalizer ?_ le_top ?_
    · exact ⟨le_top, S.isPGroup', fun V' _ hV'2 hSV' => (S.is_maximal' hV'2 hSV')⟩
    · intro x _
      have := hnorm
      exact mem_normalizer_iff_conjSub_eq.mpr (AscQuot.conjSub_eq_of_normal _ x)
  have hYH : (⨆ J ∈ Ω, J : Subgroup G) ≤ H :=
    c.layer_le_H hEA hEM (h3 G Ω K S R W H c) hK'tw hK'ne hR' hR'K' hR'S hX hKX
      hK'X hgen hSY
  obtain ⟨u, huR, hu4⟩ := hΩ.exists_orderOf_eq_four_of_mem_RSet hp hRR
  refine c.proper (eq_top_iff.mpr fun g _ => ?_)
  have hle : conjSub g K ≤ ⨆ J ∈ Ω, J :=
    le_iSup₂_of_le (conjSub g K) (hΩ.conjInvariant g K c.stand.mem) le_rfl
  exact c.mem_of_conj_mem hEA hEM (hRK huR) hu4 (hYH (hle (conj_mem_conjSub (hRK huR))))

end CFSG.ClassicalInvolution.Asc77
