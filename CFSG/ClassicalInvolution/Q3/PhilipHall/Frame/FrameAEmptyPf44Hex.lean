module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf44Block

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Hex

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem natCard_eq_eight (hΩ : TypeRHyp Ω) {M R : Subgroup G} (hM : M ∈ Ω)
    (hR : IsSylow2In R M) : Nat.card R = 8 := by
  obtain ⟨e⟩ := hΩ.sylow M hM R hR
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

private theorem not_forall_commute_of_isSylow2In (hΩ : HypOmegaGen Ω) {M R : Subgroup G}
    (hM : M ∈ Ω) (hR : IsSylow2In R M) : ¬ ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
  obtain ⟨-, -, -, -, hnc⟩ := TwinEdge.Fam.member_data hΩ hM hR le_top
  intro h
  exact hnc ⟨⟨fun a b => Subtype.ext (h a a.2 b b.2)⟩⟩

omit [Finite G] in
private theorem commute_of_mem_closure_sup {x y : G} (hxy : x * y = y * x) {a b : G}
    (ha : a ∈ Subgroup.closure {y} ⊔ Subgroup.zpowers x)
    (hb : b ∈ Subgroup.closure {y} ⊔ Subgroup.zpowers x) : a * b = b * a := by
  have hca : ∀ c : G, c * x = x * c → c * y = y * c →
      Subgroup.closure {y} ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({c} : Set G) := by
    intro c hcx hcy
    refine sup_le ((Subgroup.closure_le _).mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rintro _ rfl
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcy.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hcx.symm
  have hax : a * x = x * a := Subgroup.mem_centralizer_singleton_iff.mp (hca x rfl hxy ha)
  have hay : a * y = y * a := Subgroup.mem_centralizer_singleton_iff.mp (hca y hxy.symm rfl ha)
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hca a hax hay hb)).symm

private theorem mul_ne_mul_of_not_mem_zpowers {R : Subgroup G} (h8 : Nat.card R = 8)
    (hnc : ¬ ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) {x y : G} (hx : x ∈ R) (hx4 : orderOf x = 4)
    (hy : y ∈ R) (hyx : y ∉ Subgroup.zpowers x) : x * y ≠ y * x := by
  intro hxy
  apply hnc
  have hcard : Nat.card R = 2 * Nat.card (Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, hx4, h8]
  have hR := Sec6Gen.closure_sup_eq (Subgroup.zpowers_le.mpr hx) hcard hy hyx
  intro a ha b hb
  rw [← hR] at ha hb
  exact commute_of_mem_closure_sup hxy ha hb

private theorem exists_mem_not_mem_zpowers {R : Subgroup G} {x : G} (h8 : Nat.card R = 8)
    (hx4 : orderOf x = 4) : ∃ w ∈ R, w ∉ Subgroup.zpowers x := by
  by_contra hcon
  push Not at hcon
  have h := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers x from hcon)
  rw [h8, Nat.card_zpowers, hx4] at h
  omega

private theorem not_forall_commute_of_orderOf_four (hΩ : TypeRHyp Ω) {M : Subgroup G} (hM : M ∈ Ω)
    {u : G} (hu : u ∈ M) (hu4 : orderOf u = 4) : ¬ ∀ w ∈ M, u * w = w * u := by
  intro hc
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)
  obtain ⟨R, hR, huR⟩ := IsSylow2In.exists_ge hu2 (Subgroup.zpowers_le.mpr hu)
  have h8 := natCard_eq_eight hΩ hM hR
  obtain ⟨w, hwR, hwu⟩ := exists_mem_not_mem_zpowers h8 hu4
  exact mul_ne_mul_of_not_mem_zpowers h8 (not_forall_commute_of_isSylow2In hΩ.hyp hM hR)
    (huR (Subgroup.mem_zpowers u)) hu4 hwR hwu (hc w (hR.1 hwR))

omit [Finite G] in
private theorem mem_normalizer_inf_of_mem {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro h
  exact ⟨fun hh => ⟨(hA h).mp hh.1, (hB h).mp hh.2⟩,
    fun hh => ⟨(hA h).mpr hh.1, (hB h).mpr hh.2⟩⟩

private theorem inf_le_of_isSylow2In_of_le_normalizer {W M R : Subgroup G} (hW2 : IsPGroup 2 W)
    (hR : IsSylow2In R M) (hRW : R ≤ Subgroup.normalizer (W : Set G)) : W ⊓ M ≤ R := by
  have hRN : R ≤ Subgroup.normalizer ((W ⊓ M : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf_of_mem (hRW hx) (Subgroup.le_normalizer (hR.1 hx))
  have h2 : IsPGroup 2 ↥(R ⊔ (W ⊓ M)) :=
    IsPGroup.to_sup_of_normal_right' hR.2.1 (hW2.to_le inf_le_left) hRN
  have heq := hR.2.2 (R ⊔ (W ⊓ M)) (sup_le hR.1 inf_le_right) h2 le_sup_left
  rw [← heq]
  exact le_sup_right

theorem conj_involution_eq_mul_of_not_omegaNbr (hΩ : TypeRHyp Ω) {W : Subgroup G}
    (hW2 : IsPGroup 2 W) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {M₁ M₂ R₂ : Subgroup G}
    (hM₁ : M₁ ∈ Ω) (hM₂ : M₂ ∈ Ω) {k₁ k₂ : G} (hk₁ : IsUniqueInvolution M₁ k₁)
    (hk₂ : IsUniqueInvolution M₂ k₂) (hkk : k₁ ≠ k₂) (hR₂ : IsSylow2In R₂ M₂)
    (hR₂W : R₂ ≤ Subgroup.normalizer (W : Set G)) {u₁ u₂ : G} (hu₁ : u₁ ∈ M₁) (hu₁W : u₁ ∈ W)
    (hu₁4 : orderOf u₁ = 4) (hu₂ : u₂ ∈ R₂) (hu₂W : u₂ ∈ W) (hu₂4 : orderOf u₂ = 4)
    (hnot : M₂ ∉ omegaNbr Ω M₁) {s : G} (hs : s ∈ R₂) (hsu : s ∉ Subgroup.zpowers u₂) :
    s * k₁ * s⁻¹ = k₁ * k₂ := by
  have hΩg := hΩ.hyp
  have hne : M₁ ≠ M₂ := by
    rintro rfl
    exact hkk (hk₁.eq hk₂)
  have hk₁u : u₁ * u₁ = k₁ := Asc77.T7B.mul_self_eq_of_orderOf_four hk₁ hu₁ hu₁4
  have hk₂u : u₂ * u₂ = k₂ := Asc77.T7B.mul_self_eq_of_orderOf_four hk₂ (hR₂.1 hu₂) hu₂4
  have hc12 : Commute u₁ u₂ := hWc u₁ hu₁W u₂ hu₂W
  have h8 : Nat.card R₂ = 8 := natCard_eq_eight hΩ hM₂ hR₂
  have hnc₂ := not_forall_commute_of_isSylow2In hΩg hM₂ hR₂
  have hsu₂ : u₂ * s ≠ s * u₂ := mul_ne_mul_of_not_mem_zpowers h8 hnc₂ hu₂ hu₂4 hs hsu
  have hu₁2 : IsPGroup 2 (Subgroup.zpowers u₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu₁4]; norm_num)
  have hu₁k₂ : u₁ * k₂ = k₂ * u₁ := by
    rw [← hk₂u]
    exact (hc12.mul_right hc12).eq
  have hu₁N : u₁ ∈ Subgroup.normalizer (M₂ : Set G) :=
    hΩg.omega5 M₂ hM₂ M₁ hM₁ hne.symm k₂ hk₂ u₁ hu₁
      (not_forall_commute_of_orderOf_four hΩ hM₁ hu₁ hu₁4) hu₁2 hu₁k₂
  have hRW2 : IsPGroup 2 ↥(R₂ ⊔ W) := IsPGroup.to_sup_of_normal_right' hR₂.2.1 hW2 hR₂W
  have hRWM : (R₂ ⊔ W) ⊓ M₂ = R₂ :=
    hR₂.2.2 ((R₂ ⊔ W) ⊓ M₂) inf_le_right (hRW2.to_le inf_le_left) (le_inf le_sup_left hR₂.1)
  have hu₁R : u₁ ∈ Subgroup.normalizer (R₂ : Set G) := by
    have h := mem_normalizer_inf_of_mem
      (Subgroup.le_normalizer ((le_sup_right : W ≤ R₂ ⊔ W) hu₁W)) hu₁N
    rwa [hRWM] at h
  have hcR : s * u₁ * s⁻¹ * u₁⁻¹ ∈ R₂ := by
    have h1 : u₁ * s⁻¹ * u₁⁻¹ ∈ R₂ :=
      (Subgroup.mem_normalizer_iff.mp hu₁R s⁻¹).mp (R₂.inv_mem hs)
    have e : s * u₁ * s⁻¹ * u₁⁻¹ = s * (u₁ * s⁻¹ * u₁⁻¹) := by group
    rw [e]
    exact R₂.mul_mem hs h1
  have hcW : s * u₁ * s⁻¹ * u₁⁻¹ ∈ W := by
    have h1 : s * u₁ * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hR₂W hs) u₁).mp hu₁W
    exact W.mul_mem h1 (W.inv_mem hu₁W)
  have hcU : s * u₁ * s⁻¹ * u₁⁻¹ ∈ Subgroup.zpowers u₂ := by
    by_contra hc
    exact mul_ne_mul_of_not_mem_zpowers h8 hnc₂ hu₂ hu₂4 hcR hc (hWc u₂ hu₂W _ hcW)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hcU
  have hsu₁ : s * u₁ * s⁻¹ = u₂ ^ m * u₁ := by
    rw [hm]
    group
  have hcm : u₁ * u₂ ^ m = u₂ ^ m * u₁ := (hc12.zpow_right m).eq
  have hsk : s * k₁ * s⁻¹ = k₂ ^ m * k₁ := by
    calc s * k₁ * s⁻¹ = (s * u₁ * s⁻¹) * (s * u₁ * s⁻¹) := by rw [← hk₁u]; group
      _ = (u₂ ^ m * u₁) * (u₂ ^ m * u₁) := by rw [hsu₁]
      _ = u₂ ^ m * (u₁ * u₂ ^ m) * u₁ := by group
      _ = u₂ ^ m * (u₂ ^ m * u₁) * u₁ := by rw [hcm]
      _ = (u₂ ^ m * u₂ ^ m) * (u₁ * u₁) := by group
      _ = k₂ ^ m * k₁ := by rw [← (Commute.refl u₂).mul_zpow m, hk₂u, hk₁u]
  have hk₂sq : k₂ ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hk₂.sq
  rcases Int.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
  ·
    exfalso
    have hk₂m : k₂ ^ m = 1 := by rw [ht, ← two_mul, zpow_mul, hk₂sq, one_zpow]
    rw [hk₂m, one_mul] at hsk
    have hsk₁ : s * k₁ = k₁ * s := by
      calc s * k₁ = (s * k₁ * s⁻¹) * s := by group
        _ = k₁ * s := by rw [hsk]
    have hs2 : IsPGroup 2 (Subgroup.zpowers s) := hR₂.2.1.to_le (Subgroup.zpowers_le.mpr hs)
    have hu₂2 : IsPGroup 2 (Subgroup.zpowers u₂) := hR₂.2.1.to_le (Subgroup.zpowers_le.mpr hu₂)
    have hsN : s ∈ Subgroup.normalizer (M₁ : Set G) :=
      hΩg.omega5 M₁ hM₁ M₂ hM₂ hne k₁ hk₁ s (hR₂.1 hs)
        (fun h => hsu₂ (h u₂ (hR₂.1 hu₂)).symm) hs2 hsk₁
    have hu₂k₁ : u₂ * k₁ = k₁ * u₂ := by
      rw [← hk₁u]
      exact ((hc12.symm).mul_right hc12.symm).eq
    have hu₂N : u₂ ∈ Subgroup.normalizer (M₁ : Set G) :=
      hΩg.omega5 M₁ hM₁ M₂ hM₂ hne k₁ hk₁ u₂ (hR₂.1 hu₂)
        (fun h => hsu₂ (h s (hR₂.1 hs))) hu₂2 hu₂k₁
    have hcard : Nat.card R₂ = 2 * Nat.card (Subgroup.zpowers u₂) := by
      rw [Nat.card_zpowers, hu₂4, h8]
    have hRgen := Sec6Gen.closure_sup_eq (Subgroup.zpowers_le.mpr hu₂) hcard hs hsu
    have hRN : R₂ ≤ Subgroup.normalizer (M₁ : Set G) := by
      rw [← hRgen]
      exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hsN))
        (Subgroup.zpowers_le.mpr hu₂N)
    exact hnot ⟨hM₂, hne.symm, R₂, mem_RSet_of_isSylow2In hM₂ hR₂, hR₂.1, hRN⟩
  ·
    have hk₂m : k₂ ^ m = k₂ := by
      rw [ht, zpow_add, zpow_mul, hk₂sq, one_zpow, one_mul, zpow_one]
    rw [hsk, hk₂m]
    rw [← hk₁u, ← hk₂u]
    exact ((hc12.mul_right hc12).mul_left (hc12.mul_right hc12)).eq.symm

private theorem exists_orderOf_four_mem (hΩ : TypeRHyp Ω) (S : Sylow 2 G) {η : Set (Subgroup G)}
    (hη : η ∈ etaG Ω) (hηS : ∀ V ∈ η, V ≤ (S : Subgroup G)) {M U : Subgroup G} (hM : M ∈ Ω)
    (hU : U ∈ USet Ω) (hUM : U ≤ M) (hUS : U ≤ (S : Subgroup G)) :
    ∃ u : G, u ∈ M ∧ (∃ V ∈ η, u ∈ V) ∧ orderOf u = 4 := by
  have hΩg := hΩ.hyp
  obtain ⟨V, ⟨hVη, hUV⟩, -⟩ := Sec6Gen.six_eight hΩg S hU hUS hη hηS
  have hVU : V ∈ USet Ω := by
    obtain ⟨S', hS', -⟩ := hη
    exact (hS'.1 hVη).1
  have hVM : V ≤ M := by
    rcases hUV with h | h
    · rw [← h]
      exact hUM
    · obtain ⟨M'', hM'', hsyl⟩ := exists_isSylow2In_of_mem_RSet h
      obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩg hU
      have hMM : M = M'' := Sec6Gen.eq_of_le_of_le hΩg hM hM''
        (Sec6Gen.isPGroup_of_mem_USet hΩg hU) h4 hUM (le_sup_left.trans hsyl.1)
      rw [hMM]
      exact le_sup_right.trans hsyl.1
  obtain ⟨R', -, J', hJ', hR'J', -, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩg hVU
  have h8 := natCard_eq_eight hΩ hJ' hR'J'
  have hV4 : Nat.card V = 4 := by omega
  haveI := hcyc
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := ↥V)
  have hu4 : orderOf (u : G) = 4 := by
    rw [Subgroup.orderOf_coe, ← hV4, orderOf_eq_card_of_forall_mem_zpowers hu]
  exact ⟨u, hVM u.2, ⟨V, hVη, u.2⟩, hu4⟩

theorem false_of_hexagon (hΩ : TypeRHyp Ω) {L P J₀ : Subgroup G} {zL zJ₀ : G}
    (hL : L ∈ Ω) (hP : P ∈ omegaStarNbr Ω L) (hv : AViol Ω L J₀ zL zJ₀)
    (hstep0 : ∀ M ∈ insert L (aSet Ω L), P ∉ omegaNbr Ω M)
    (hzne : ∀ M ∈ insert L (aSet Ω L), ∀ w : G, IsUniqueInvolution M w →
      ¬ IsUniqueInvolution P w) :
    False := by
  have hΩg := hΩ.hyp
  have hΩc := hΩg.conjInvariant
  have hPΩ : P ∈ Ω := hP.1
  obtain ⟨p, hp⟩ := Sec6Gen.exists_uniqueInvolution hΩg hPΩ
  obtain ⟨-, -, UP, hUP, hUPP, hUPN⟩ := hP
  obtain ⟨-, -, UJ, hUJ, hUJJ, hUJN⟩ := hv.star
  obtain ⟨SL, hSL, hUPS⟩ := IsSylow2In.exists_ge (Sec6Gen.isPGroup_of_mem_USet hΩg hUP) hUPN
  obtain ⟨S', hS', hUJS'⟩ := IsSylow2In.exists_ge (Sec6Gen.isPGroup_of_mem_USet hΩg hUJ) hUJN
  obtain ⟨n, hn, hnS⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hS' hSL
  have hnL : conjSub n L = L := conjSub_eq_of_mem_normalizer hn
  have hzLn : n * zL * n⁻¹ = zL := hv.hzK.conj_eq hnL
  have hv' : AViol Ω L (conjSub n J₀) zL (n * zJ₀ * n⁻¹) := by
    have h := hv.conj hΩc n
    rwa [hnL, hzLn] at h
  have hJ'B : conjSub n J₀ ∈ insert L (aSet Ω L) := Set.mem_insert_of_mem _ ⟨_, _, hv'⟩
  have hUJ'S : conjSub n UJ ≤ SL := by
    rw [← hnS]
    exact conjSub_mono hUJS'
  have hR : IsSylow2In (SL ⊓ L) L :=
    isSylow2In_inf_of_le_normalizer hSL Subgroup.le_normalizer le_rfl
  obtain ⟨S, hSLS⟩ := hSL.2.1.exists_le_sylow
  obtain ⟨W, hW, hWS, hSW⟩ := Q3CP.exists_W_of_hypOmegaGen hΩg S
  have hWc := Q3CL.Thompson.commutes_of_mem_WSet hΩg hW
  have hW2 : IsPGroup 2 W := S.isPGroup'.to_le hWS
  have hSN : ∀ x ∈ (S : Subgroup G), x ∈ Subgroup.normalizer (W : Set G) :=
    fun x hx => mem_normalizer_of_conjSub_eq (hSW x hx)
  obtain ⟨η, hη, hWη⟩ := id hW
  have hηW : ∀ V ∈ η, V ≤ W := fun V hV => by
    rw [hWη]
    exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hηW V hV).trans hWS
  have hRR : SL ⊓ L ∈ RSet Ω := mem_RSet_of_isSylow2In hL hR
  obtain ⟨UL, hULR, hULc, hULcard⟩ :=
    (Sec6Gen.isQuatSub_of_mem_RSet hΩg hRR).exists_cyclic_index_two
  have hUL : UL ∈ USet Ω := mem_USet_of_natCard hL hR hULR hULc hULcard
  obtain ⟨uL, huLL, ⟨VL, hVLη, huLV⟩, huL4⟩ := exists_orderOf_four_mem hΩ S hη hηS hL hUL
    (hULR.trans inf_le_right) (hULR.trans (inf_le_left.trans hSLS))
  obtain ⟨uJ, huJJ, ⟨VJ, hVJη, huJV⟩, huJ4⟩ := exists_orderOf_four_mem hΩ S hη hηS hv'.mem
    (USet.conj hΩc hUJ n) (conjSub_mono hUJJ) (hUJ'S.trans hSLS)
  obtain ⟨uP, huPP, ⟨VP, hVPη, huPV⟩, huP4⟩ := exists_orderOf_four_mem hΩ S hη hηS hPΩ hUP hUPP
    (hUPS.trans hSLS)
  have huLW : uL ∈ W := hηW VL hVLη huLV
  have huJW : uJ ∈ W := hηW VJ hVJη huJV
  have huPW : uP ∈ W := hηW VP hVPη huPV
  have hRW : SL ⊓ L ≤ Subgroup.normalizer (W : Set G) := fun x hx => hSN x (hSLS hx.1)
  have huLR : uL ∈ SL ⊓ L := inf_le_of_isSylow2In_of_le_normalizer hW2 hR hRW ⟨huLW, huLL⟩
  obtain ⟨TP, hTPD, hTPs⟩ :=
    Q3CL.Thompson.exists_sylow_mem_DSet hΩg hW hWS hPΩ hUP hUPP (hUPS.trans hSLS)
  have huPT : uP ∈ TP := inf_le_of_isSylow2In_of_le_normalizer hW2 hTPs hTPD.2 ⟨huPW, huPP⟩
  have hjz : n * zJ₀ * n⁻¹ ≠ zL := aViol_involution_ne hΩg hL hv'
  have hLJ' : L ∉ omegaNbr Ω (conjSub n J₀) := fun h =>
    hv'.not_nbr (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩg hv'.mem hL h)
  obtain ⟨r, hr, hru⟩ := exists_mem_not_mem_zpowers (natCard_eq_eight hΩ hL hR) huL4
  have hrj : r * (n * zJ₀ * n⁻¹) * r⁻¹ = n * zJ₀ * n⁻¹ * zL :=
    conj_involution_eq_mul_of_not_omegaNbr hΩ hW2 hWc hv'.mem hL hv'.hzJ hv.hzK hjz hR hRW huJJ
      huJW huJ4 huLR huLW huL4 hLJ' hr hru
  have hQB : conjSub r (conjSub n J₀) ∈ insert L (aSet Ω L) := by
    have h := hv'.conj hΩc r
    rw [conjSub_eq_self_of_mem hr.2, hv.hzK.conj_eq (conjSub_eq_self_of_mem hr.2)] at h
    exact Set.mem_insert_of_mem _ ⟨_, _, h⟩
  have hzQ : IsUniqueInvolution (conjSub r (conjSub n J₀)) (n * zJ₀ * n⁻¹ * zL) := by
    have h := hv'.hzJ.conj r
    rwa [hrj] at h
  have huQ : r * uJ * r⁻¹ ∈ conjSub r (conjSub n J₀) := conj_mem_conjSub huJJ
  have huQW : r * uJ * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRW hr) uJ).mp huJW
  have huQ4 : orderOf (r * uJ * r⁻¹) = 4 := by
    have e : r * uJ * r⁻¹ = MulAut.conj r uJ := by rw [MulAut.conj_apply]
    rw [e, MulEquiv.orderOf_eq, huJ4]
  obtain ⟨s, hs, hsu⟩ := exists_mem_not_mem_zpowers (natCard_eq_eight hΩ hPΩ hTPs) huP4
  have hpne : ∀ {M : Subgroup G} {w : G}, M ∈ insert L (aSet Ω L) → IsUniqueInvolution M w →
      w ≠ p :=
    fun hM hw h => hzne _ hM _ hw (h ▸ hp)
  have h1 : s * zL * s⁻¹ = zL * p :=
    conj_involution_eq_mul_of_not_omegaNbr hΩ hW2 hWc hL hPΩ hv.hzK hp
      (hpne (Set.mem_insert L _) hv.hzK) hTPs hTPD.2 huLL huLW huL4 huPT huPW huP4
      (hstep0 L (Set.mem_insert L _)) hs hsu
  have h2 : s * (n * zJ₀ * n⁻¹) * s⁻¹ = n * zJ₀ * n⁻¹ * p :=
    conj_involution_eq_mul_of_not_omegaNbr hΩ hW2 hWc hv'.mem hPΩ hv'.hzJ hp
      (hpne hJ'B hv'.hzJ) hTPs hTPD.2 huJJ huJW huJ4 huPT huPW huP4 (hstep0 _ hJ'B) hs hsu
  have h3 : s * (n * zJ₀ * n⁻¹ * zL) * s⁻¹ = n * zJ₀ * n⁻¹ * zL * p :=
    conj_involution_eq_mul_of_not_omegaNbr hΩ hW2 hWc (hΩc r _ hv'.mem) hPΩ hzQ hp
      (hpne hQB hzQ) hTPs hTPD.2 huQ huQW huQ4 huPT huPW huP4 (hstep0 _ hQB) hs hsu
  have hzLW : zL ∈ W := by
    rw [← Asc77.T7B.mul_self_eq_of_orderOf_four hv.hzK huLL huL4]
    exact W.mul_mem huLW huLW
  have hpW : p ∈ W := by
    rw [← Asc77.T7B.mul_self_eq_of_orderOf_four hp huPP huP4]
    exact W.mul_mem huPW huPW
  have hpzL : p * zL = zL * p := hWc p hpW zL hzLW
  have e3 : s * (n * zJ₀ * n⁻¹ * zL) * s⁻¹ = (s * (n * zJ₀ * n⁻¹) * s⁻¹) * (s * zL * s⁻¹) := by
    group
  rw [e3, h1, h2] at h3
  have e4 : n * zJ₀ * n⁻¹ * p * (zL * p) = n * zJ₀ * n⁻¹ * zL * (p * p) := by
    calc n * zJ₀ * n⁻¹ * p * (zL * p) = n * zJ₀ * n⁻¹ * (p * zL) * p := by group
      _ = n * zJ₀ * n⁻¹ * (zL * p) * p := by rw [hpzL]
      _ = n * zJ₀ * n⁻¹ * zL * (p * p) := by group
  rw [e4, hp.sq, mul_one] at h3
  have h4 : (n * zJ₀ * n⁻¹ * zL) * 1 = (n * zJ₀ * n⁻¹ * zL) * p := by
    rw [mul_one]
    exact h3
  exact hp.ne_one (mul_left_cancel h4).symm

end Hex

section Frame

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}

theorem exists_omegaNbr_of_omegaStarNbr (hs : FrameStd K z J zJ) {L P : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hP : P ∈ omegaStarNbr (CoreAssembly.conjClass K) L)
    (hPB : P ∉ aStar (CoreAssembly.conjClass K) L) :
    ∃ M ∈ aStar (CoreAssembly.conjClass K) L, P ∈ omegaNbr (CoreAssembly.conjClass K) M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨J₀, zL, zJ₀, hv⟩ := hs.exists_aViol hL
  have hsub : insert L (aSet (CoreAssembly.conjClass K) L) ⊆
      aStar (CoreAssembly.conjClass K) L := by
    rintro M (rfl | ⟨_, _, hvM⟩)
    · exact Relation.ReflTransGen.refl
    · exact mem_aStar_of_aViol hvM
  refine false_of_hexagon hs.typeRHyp hL hP hv (fun M hM => hcon M (hsub hM)) ?_
  intro M hM w hwM hwP
  exact hPB (mem_aStar_of_twin (hsub hM) hP.1 hwM hwP)

end Frame

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
