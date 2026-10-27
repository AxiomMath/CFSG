module

public import CFSG.ClassicalInvolution.RouteD.LocalMembers
public import CFSG.ClassicalInvolution.RouteD.GapsPerfect
public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.RouteD.LocalLift

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def FundNoncentral (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (t : StatedLieTag) (n e : ℕ), IsFundTag t → StatedLieAdmissible t n p e →
    ¬ (t = .PSL ∧ n = 2) →
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∀ r ∈ R,
      (∀ y : (modelUniv t n p e Fact.out).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p e Fact.out).K) → r = 1

theorem eq_top_of_psl_two {t : StatedLieTag} {n e : ℕ} (ht : t = .PSL) (hn : n = 2)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) : R = ⊤ := by
  subst ht hn
  have := fundamentalSubgroups_psl_subset (F := GaloisField p e) (m := 1) (by norm_num) hR
  exact longRootSet_two_subset (by norm_num) this

theorem exists_range_of_mem {f : ℕ} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) {L : Subgroup X} (hL : L ∈ Φ) :
    ∃ i, L ≤ (D.hom i).range := by
  obtain ⟨i, R, -, rfl⟩ := D.fundamental L hL
  exact ⟨i, Subgroup.map_le_range _ _⟩

theorem commutes_range {f : ℕ} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) {i j : Fin D.card} (h : i ≠ j) :
    Commutes (D.hom i).range (D.hom j).range := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  exact D.commute i j h a b

theorem locImg_eq_range_of_involution {f : ℕ} (hMFZ : FundNoncentral p) [Finite G]
    {Ω : Set (Subgroup G)} {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) (hx : IsClassicalMember p f N x) :
    ∃ i, D.tag i = .PSL ∧ D.rank i = 2 ∧ locImg Ω x N = (D.hom i).range := by
  have hNY : N ≤ locLayer Ω x := le_centralizingLayer hN
  have hmem : locImg Ω x N ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨N, hN, rfl⟩
  obtain ⟨i, R, hR, hRN⟩ := D.fundamental _ hmem
  set xY : ↥(locLayer Ω x) := ⟨x, hNY hx.mem⟩ with hxY
  set xbar : locQuot Ω x := QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) xY
    with hxbar
  have hxN : xbar ∈ locImg Ω x N := ⟨xY, Subgroup.mem_subgroupOf.mpr hx.mem, rfl⟩
  have hcent : ∀ q : locQuot Ω x, xbar * q = q * xbar := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    show QuotientGroup.mk' _ (xY * y) = QuotientGroup.mk' _ (y * xY)
    congr 1
    apply Subtype.ext
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {x} y.2)
    exact this.symm
  rw [hRN] at hxN
  obtain ⟨r, hrR, hr⟩ := hxN
  by_cases hpsl : D.tag i = .PSL ∧ D.rank i = 2
  · refine ⟨i, hpsl.1, hpsl.2, ?_⟩
    have := eq_top_of_psl_two (p := p) (e := D.exp i) hpsl.1 hpsl.2 hR
    rw [hRN, this, Subgroup.map_top]
  · exfalso
    have hr1 : r = 1 := by
      refine hMFZ (D.tag i) (D.rank i) (D.exp i) (D.isFundTag i) (D.admissible i) hpsl R hR r hrR
        fun y => D.ker_le_center i ?_
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hr]
      have := hcent (D.hom i y)
      calc xbar * D.hom i y * xbar⁻¹ * (D.hom i y)⁻¹
          = (D.hom i y * xbar) * xbar⁻¹ * (D.hom i y)⁻¹ := by rw [this]
        _ = 1 := by group
    rw [hr1, map_one] at hr
    have hO : xY ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := by
      rw [← QuotientGroup.eq_one_iff]
      exact hr.symm
    have h2 : orderOf xY = 2 := by
      rw [hxY, Subgroup.orderOf_mk]; exact hx.orderOf_eq_two
    have h3 : orderOf (⟨xY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    have h4 := orderOf_dvd_natCard (⟨xY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    rw [h3] at h4
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _))
      (even_iff_two_dvd.mpr h4)

theorem le_of_locImg_le {f : ℕ} [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L N : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (h : locImg Ω x L ≤ locImg Ω x N) : L ≤ N := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hperf : L.subgroupOf (locLayer Ω x) ≤ ⁅L.subgroupOf (locLayer Ω x),
      L.subgroupOf (locLayer Ω x)⁆ :=
    (commutator_eq_of_isClassicalMember (hz.subgroupOf p f (le_centralizingLayer hL))).ge
  have hsup : L.subgroupOf (locLayer Ω x) ≤ N.subgroupOf (locLayer Ω x) ⊔
      classicalInvolutionOddCore ↥(locLayer Ω x) := by
    intro a ha
    have : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) a ∈ locImg Ω x N :=
      h ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    have hmem : b⁻¹ * a ∈ classicalInvolutionOddCore ↥(locLayer Ω x) := QuotientGroup.eq.mp hba
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hmem)
  have := le_of_perfect_of_le_sup_center hP1 hperf hsup
  intro l hl
  have hlY : l ∈ locLayer Ω x := le_centralizingLayer hL hl
  exact Subgroup.mem_subgroupOf.mp (this (Subgroup.mem_subgroupOf.mpr
    (show (⟨l, hlY⟩ : ↥(locLayer Ω x)).1 ∈ L from hl)))

theorem commutes_or_eq_of_involution {f : ℕ} (hMFZ : FundNoncentral p) [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {N L : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) (hL : L ∈ centralizingMembers Ω {x})
    (hx : IsClassicalMember p f N x) : Commutes N L ∨ L = N := by
  obtain ⟨i, -, -, hi⟩ := locImg_eq_range_of_involution hMFZ D hN hx
  have hLmem : locImg Ω x L ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  obtain ⟨j, hj⟩ := exists_range_of_mem D hLmem
  by_cases hij : j = i
  · subst hij
    right
    have hle : L ≤ N := le_of_locImg_le hΩ hP1 hL (hi ▸ hj)
    obtain ⟨zL, hzL⟩ := hΩ.classical L hL.1
    obtain ⟨eL⟩ := hzL.nonempty_equiv_sl2 (hex L hL.1)
    obtain ⟨eN⟩ := hx.nonempty_equiv_sl2 (hex N hN.1)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_congr eL.toEquiv, Nat.card_congr eN.toEquiv])
  · left
    refine commutes_of_commutes_locImg hΩ hP1 hN hL ?_
    intro a ha b hb
    exact commutes_range D (Ne.symm hij) a (hi ▸ ha) b (hj hb)

@[expose] def involutionMembers (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) :
    Set (Subgroup G) :=
  {N | N ∈ Ω ∧ IsClassicalMember p f N x}

theorem ncard_involutionMembers_le {f : ℕ} (hMFZ : FundNoncentral p) [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) :
    (involutionMembers p f Ω x).Finite ∧ (involutionMembers p f Ω x).ncard ≤ D.card := by
  have hmem : ∀ N ∈ involutionMembers p f Ω x, N ∈ centralizingMembers Ω {x} := fun N hN =>
    ⟨hN.1, le_centralizer_of_isClassicalMember hN.2⟩
  let g : ↥(involutionMembers p f Ω x) → Fin D.card := fun N =>
    Classical.choose (locImg_eq_range_of_involution hMFZ D (hmem N.1 N.2) N.2.2)
  have hg : ∀ N : ↥(involutionMembers p f Ω x),
      locImg Ω x N.1 = (D.hom (g N)).range := fun N =>
    (Classical.choose_spec (locImg_eq_range_of_involution hMFZ D (hmem N.1 N.2) N.2.2)).2.2
  have hinj : Function.Injective g := by
    intro N N' h
    apply Subtype.ext
    exact locImg_injOn hΩ hP1 (hmem N.1 N.2) (hmem N'.1 N'.2) ((hg N).trans (h ▸ (hg N').symm))
  have : Finite ↥(involutionMembers p f Ω x) := Finite.of_injective g hinj
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_le_card_of_injective g hinj).trans (by simp)

theorem perfect_le_normalizer_of_involution {f : ℕ} (hMFZ : FundNoncentral p) [Finite G]
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hD : D.card ≤ 4) {S : Subgroup G}
    (hS : S ≤ Subgroup.centralizer ({x} : Set G)) (hSp : ⁅S, S⁆ = S) {K : Subgroup G}
    (hK : K ∈ Ω) (hxK : IsClassicalMember p f K x) : S ≤ Subgroup.normalizer (K : Set G) := by
  have : Group.IsPerfect ↥S := Subgroup.isPerfect_iff.mpr hSp
  obtain ⟨hfin, hcard⟩ := ncard_involutionMembers_le hMFZ hΩ hP1 D
  refine perfect_le_normalizer_of_card_le_four S (involutionMembers p f Ω x) hfin
    (hcard.trans hD) ?_ (⟨hK, hxK⟩ : K ∈ involutionMembers p f Ω x)
  intro g hg N hN
  have hgx : g * x * g⁻¹ = x := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hS hg)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  refine ⟨hΩ.conjInvariant g N hN.1, ?_⟩
  have := hN.2.conj g
  rwa [hgx] at this

theorem le_group_of_standardPair {F : Type} [Field F] {X : Type} [Group X]
    {W U V : Subgroup X} (h : LinearBlockStandardPair F W U V) : U ≤ W ∧ V ≤ W := by
  obtain ⟨θ, c, hrange, -, hcases⟩ := h
  rw [← hrange]
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2]
    exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩
  · rw [← h1, ← h2]
    exact ⟨Subgroup.map_le_range _ _, Subgroup.map_le_range _ _⟩

@[expose] def StandardPairAutAbelian (F : Type) [Field F] [Finite F] : Prop :=
  ∀ {X : Type} [Group X] (W K₀ K : Subgroup X), LinearBlockStandardPair F W K₀ K →
    ∀ α β : MulAut ↥W,
      (∀ w : ↥W, (w : X) ∈ K₀ → α w = w) → (∀ w : ↥W, (w : X) ∈ K₀ → β w = w) →
      (∀ w : ↥W, (w : X) ∈ K → ((α w : ↥W) : X) ∈ K) →
      (∀ w : ↥W, (w : X) ∈ K → ((β w : ↥W) : X) ∈ K) → α * β = β * α

theorem perfect_le_centralizer_of_standard_pair {F : Type} [Field F] [Finite F]
    (hF : StandardPairAutAbelian F) {H : Type} [Group H] {W K₀ K : Subgroup H}
    (hWK : LinearBlockStandardPair F W K₀ K) {S : Subgroup H} (hS : ⁅S, S⁆ = S)
    (hS₀ : S ≤ Subgroup.centralizer (K₀ : Set H)) (hSK : S ≤ Subgroup.normalizer (K : Set H)) :
    S ≤ Subgroup.centralizer (K : Set H) := by
  obtain ⟨hK₀W, hKW⟩ := le_group_of_standardPair hWK
  have hWsup : W = K₀ ⊔ K :=
    le_antisymm (linearBlockStandardPair_le_sup' hWK) (sup_le hK₀W hKW)
  have hS₀N : ∀ s ∈ S, K₀.map ((MulAut.conj s : H ≃* H) : H →* H) = K₀ := fun s hs => by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp (hS₀ hs) k hk
      show s * k * s⁻¹ ∈ K₀
      rw [mul_inv_eq_iff_eq_mul.mpr this.symm]
      exact hk
    · intro k hk
      refine ⟨k, hk, ?_⟩
      have := Subgroup.mem_centralizer_iff.mp (hS₀ hs) k hk
      show s * k * s⁻¹ = k
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
  have hSW : S ≤ Subgroup.normalizer (W : Set H) := fun s hs => by
    have hK := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSK hs)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hWsup, Subgroup.map_sup, hS₀N s hs]
    congr 1
  have hcomm : ∀ s ∈ S, ∀ s' ∈ S, ∀ q ∈ W,
      s * (s' * q * s'⁻¹) * s⁻¹ = s' * (s * q * s⁻¹) * s'⁻¹ := by
    intro s hs s' hs' q hq
    let α : MulAut ↥W := W.normalizerMonoidHom ⟨s, hSW hs⟩
    let β : MulAut ↥W := W.normalizerMonoidHom ⟨s', hSW hs'⟩
    have hα : ∀ w : ↥W, ((α w : ↥W) : H) = s * w * s⁻¹ := fun w => rfl
    have hβ : ∀ w : ↥W, ((β w : ↥W) : H) = s' * w * s'⁻¹ := fun w => rfl
    have hfix : ∀ t ∈ S, ∀ w : ↥W, (w : H) ∈ K₀ → t * (w : H) * t⁻¹ = w := fun t ht w hw => by
      have := Subgroup.mem_centralizer_iff.mp (hS₀ ht) w hw
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have hstab : ∀ t ∈ S, ∀ w : ↥W, (w : H) ∈ K → t * (w : H) * t⁻¹ ∈ K := fun t ht w hw =>
      (Subgroup.mem_normalizer_iff.mp (hSK ht) w).mp hw
    have key := hF W K₀ K hWK α β (fun w hw => Subtype.ext (by rw [hα]; exact hfix s hs w hw))
      (fun w hw => Subtype.ext (by rw [hβ]; exact hfix s' hs' w hw))
      (fun w hw => by rw [hα]; exact hstab s hs w hw)
      (fun w hw => by rw [hβ]; exact hstab s' hs' w hw)
    have := congrArg (fun γ : MulAut ↥W => ((γ ⟨q, hq⟩ : ↥W) : H)) key
    simpa [MulAut.mul_apply, hα, hβ] using this
  exact (perfect_le_centralizer_of_commuting_conj S W hS hSW hcomm).trans
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKW))

theorem perfect_le_centralizer_of_partner {f : ℕ} (hMFZ : FundNoncentral p) [Finite G]
    {F : Type} [Field F] [Finite F] (hF : StandardPairAutAbelian F)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {t : G} (hP1 : LocalOddCentral Ω {t})
    (D : LieSystemData p f (locQuot Ω t) (locFamily Ω t)) (hD : D.card ≤ 4)
    {W K₀ K : Subgroup G} (hK : K ∈ Ω) (hxK : IsClassicalMember p f K t)
    (hWK : LinearBlockStandardPair F W K₀ K) {S : Subgroup G} (hS : ⁅S, S⁆ = S)
    (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) (hS₀ : S ≤ Subgroup.centralizer (K₀ : Set G)) :
    S ≤ Subgroup.centralizer (K : Set G) :=
  perfect_le_centralizer_of_standard_pair hF hWK hS hS₀
    (perfect_le_normalizer_of_involution hMFZ hΩ hP1 D hD hSt hS hK hxK)

theorem attached_in_same_component {f : ℕ} [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    {x : G} (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {K₀ K N : Subgroup G}
    (h0 : K₀ ∈ centralizingMembers Ω {x}) (hK : K ∈ centralizingMembers Ω {x})
    (hN : N ∈ centralizingMembers Ω {x}) (hnc : ¬ Commutes K₀ K) (hatt : ¬ Commutes N K) :
    ∃ i, locImg Ω x K₀ ≤ (D.hom i).range ∧ locImg Ω x K ≤ (D.hom i).range ∧
      locImg Ω x N ≤ (D.hom i).range := by
  have hmem : ∀ M, M ∈ centralizingMembers Ω {x} → ∃ i, locImg Ω x M ≤ (D.hom i).range := fun M hM =>
    exists_range_of_mem D (mem_locFamily_iff.mpr ⟨M, hM, rfl⟩)
  have hsame : ∀ (M M' : Subgroup G), M ∈ centralizingMembers Ω {x} →
      M' ∈ centralizingMembers Ω {x} → ¬ Commutes M M' → ∀ i j,
      locImg Ω x M ≤ (D.hom i).range → locImg Ω x M' ≤ (D.hom j).range → i = j := by
    intro M M' hM hM' hnc' i j hi hj
    by_contra hij
    apply hnc'
    refine commutes_of_commutes_locImg hΩ hP1 hM hM' ?_
    intro a ha b hb
    exact commutes_range D hij a (hi ha) b (hj hb)
  obtain ⟨i, hi⟩ := hmem K hK
  obtain ⟨j, hj⟩ := hmem K₀ h0
  obtain ⟨k, hk⟩ := hmem N hN
  have e1 := hsame K₀ K h0 hK hnc j i hj hi
  have e2 := hsame N K hN hK hatt k i hk hi
  exact ⟨i, e1 ▸ hj, hi, e2 ▸ hk⟩

end CFSG.ClassicalInvolution.RouteD.Gaps
