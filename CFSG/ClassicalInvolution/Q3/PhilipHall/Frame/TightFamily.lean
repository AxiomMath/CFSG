module

public import CFSG.ClassicalInvolution.Q3.TL3GlueJ
public import CFSG.ClassicalInvolution.Asc77.AscT8V4

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement MatrixGroups

section Restrict

variable {G : Type} [Group G] [Finite G]

theorem hypOmegaGen_restrict {Λ : Set (Subgroup G)} (hΛ : HypOmegaGen Λ) (X : Subgroup G) :
    HypOmegaGen (restrictFamily Λ X) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLX, rfl⟩
    refine ⟨conjSub (n : G) L, hΛ.conjInvariant _ L hL, ?_, conjSub_subgroupOf X n L⟩
    have := conjSub_mono (n := (n : G)) hLX
    rwa [conjSub_eq_self_of_mem n.2] at this
  omega1 := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    obtain ⟨⟨z, hz⟩, P, hP, hPnc⟩ := hΛ.omega1 L hL
    refine ⟨⟨_, isUniqueInvolution_subgroupOf hz hLX⟩, P.subgroupOf X, hP.subgroupOf hLX, ?_⟩
    intro hc
    apply hPnc
    let e : P.subgroupOf X ≃* P := Subgroup.subgroupOfEquivOfLe (hP.1.trans hLX)
    refine ⟨⟨fun a b => ?_⟩⟩
    have h1 : e.symm a * e.symm b = e.symm b * e.symm a := hc.is_comm.comm _ _
    have h2 := congrArg e h1
    simpa using h2
  omega2 := by
    rintro _ ⟨L, hL, hLX, rfl⟩
    rcases hΛ.omega2 L hL with h | h
    · left
      apply Subgroup.map_injective X.subtype_injective
      rw [MonoidHom.map_closure, Subgroup.map_subgroupOf_eq_of_le hLX]
      conv_rhs => rw [← h]
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
      constructor
      · rintro ⟨x, ⟨hxL, hx2⟩, rfl⟩
        exact ⟨hxL, isPGroup_zpowers_coe_iff.mpr hx2⟩
      · rintro ⟨hyL, hy2⟩
        exact ⟨⟨y, hLX hyL⟩, ⟨hyL, isPGroup_zpowers_coe_iff.mp hy2⟩, rfl⟩
    · right
      obtain ⟨e⟩ := h
      let φ : L.subgroupOf X ≃* L := Subgroup.subgroupOfEquivOfLe hLX
      exact ⟨(QuotientGroup.congr _ _ φ
        (CFSG.ComponentClassification.OddCore.equiv_invariant φ)).trans e⟩
  omega3 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ P Q hP hQ
    have hP' : IsSylow2In (P.map X.subtype) K := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hKX] at this
    have hQ' : IsSylow2In (Q.map X.subtype) J := by
      have := isSylow2In_map_subtype_iff.mpr hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hJX] at this
    have h := hΛ.omega3 K hK J hJ _ _ hP' hQ'
    rwa [Subgroup.card_map_of_injective X.subtype_injective,
      Subgroup.card_map_of_injective X.subtype_injective] at h
  omega4 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΛ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf X ⊓ J.subgroupOf X) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKX)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKX, oddCoreOf_subgroupOf hJX]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKX, rfl⟩ _ ⟨J, hJ, hJX, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKX
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΛ.omega5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2'
      (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKX).mp hn

end Restrict

section TightFamily

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def tightFamily (Ω : Set (Subgroup Y)) : Set (Subgroup Y) :=
  {R | ∃ J ∈ Ω, tightCore J = R}

omit [Finite Y] in
theorem tightCore_tightCore (R : Subgroup Y) : tightCore (tightCore R) = tightCore R := by
  refine le_antisymm (tightCore_le _) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxR, hx2⟩
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hxR, hx2⟩, hx2⟩

omit [Finite Y] in
theorem isUniqueInvolution_mono {J R : Subgroup Y} {z : Y} (h : IsUniqueInvolution J z)
    (hRJ : R ≤ J) (hz : z ∈ R) : IsUniqueInvolution R z :=
  ⟨hz, h.ne_one, h.sq, fun y hy hyy => h.unique y (hRJ hy) hyy⟩

omit [Finite Y] in
theorem isSylow2In_tightCore {P J : Subgroup Y} (h : IsSylow2In P J) :
    IsSylow2In P (tightCore J) :=
  ⟨le_tightCore_of_isPGroup h.1 h.2.1, h.2.1,
    fun V' hV' h2 hle => h.2.2 V' (hV'.trans (tightCore_le J)) h2 hle⟩

omit [Finite Y] in
theorem isSylow2In_of_tightCore {P J : Subgroup Y} (h : IsSylow2In P (tightCore J)) :
    IsSylow2In P J :=
  ⟨h.1.trans (tightCore_le J), h.2.1,
    fun V' hV' h2 hle => h.2.2 V' (le_tightCore_of_isPGroup hV' h2) h2 hle⟩

theorem mem_tightCore_of_member {J : Subgroup Y} {z : Y}
    (hz : Uniform.IsClassicalMemberU (.sl2 3 1) J z) : z ∈ tightCore J :=
  Subgroup.subset_closure ⟨hz.mem, IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz.orderOf_eq_two]; norm_num)⟩

theorem isUniqueInvolution_tightCore {J : Subgroup Y} {z : Y}
    (hz : Uniform.IsClassicalMemberU (.sl2 3 1) J z) : IsUniqueInvolution (tightCore J) z :=
  isUniqueInvolution_mono (hz.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1))
    (tightCore_le J) (mem_tightCore_of_member hz)

omit [Finite Y] in
theorem le_normalizer_of_conj_mem {M H : Subgroup Y}
    (h : ∀ m ∈ M, ∀ x ∈ H, m * x * m⁻¹ ∈ H) : M ≤ Subgroup.normalizer (H : Set Y) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h m hm x hx, fun hx => ?_⟩
  have := h m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

omit [Finite Y] in
theorem conj_mem_oddCoreOf {J : Subgroup Y} {j x : Y} (hj : j ∈ J) (hx : x ∈ oddCoreOf J) :
    j * x * j⁻¹ ∈ oddCoreOf J := by
  obtain ⟨x', hx', rfl⟩ := hx
  refine ⟨⟨j, hj⟩ * x' * ⟨j, hj⟩⁻¹,
    (inferInstance : (classicalInvolutionOddCore ↥J).Normal).conj_mem x' hx' ⟨j, hj⟩, ?_⟩
  simp

theorem inf_oddCoreOf_le {R J : Subgroup Y} (hRJ : R ≤ J) : R ⊓ oddCoreOf J ≤ oddCoreOf R := by
  refine T8V.le_oddCoreOf_of_normal_odd' inf_le_left
    (le_normalizer_of_conj_mem fun r hr x hx =>
      ⟨R.mul_mem (R.mul_mem hr hx.1) (R.inv_mem hr), conj_mem_oddCoreOf (hRJ hr) hx.2⟩) ?_
  exact (oddCoreOf_odd_natCard J).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

variable {Ω : Set (Subgroup Y)}

theorem mem_normalizer_of_twin (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) {J J' : Subgroup Y}
    (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') {z : Y} (hzJ : IsUniqueInvolution J z)
    (hzJ' : Uniform.IsClassicalMemberU (.sl2 3 1) J' z) {v : Y} (hv : v ∈ J')
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) :
    v ∈ Subgroup.normalizer (J : Set Y) := by
  have h5 := hΩ.omega5 J hJ J' hJ' hne z hzJ
  have hzc : ∀ w ∈ J', w * z = z * w := fun w hw => (hzJ'.comm_of_mem hw).symm
  by_cases hc : ∀ w ∈ J', v * w = w * v
  · obtain ⟨-, P, hP, hPnc⟩ :=
      (Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΩ).omega1 J' hJ'
    obtain ⟨x, y, hxy⟩ : ∃ x y : P, x * y ≠ y * x := by
      by_contra hcon
      push Not at hcon
      exact hPnc ⟨⟨hcon⟩⟩
    have hxJ' : (x : Y) ∈ J' := hP.1 x.2
    have hyJ' : (y : Y) ∈ J' := hP.1 y.2
    have hxy' : (x : Y) * y ≠ y * x := fun h => hxy (Subtype.ext h)
    have hx2 : IsPGroup 2 (Subgroup.zpowers (x : Y)) :=
      hP.2.1.to_le (Subgroup.zpowers_le.mpr x.2)
    have hxn : ¬ ∀ w ∈ J', (x : Y) * w = w * x := fun h => hxy' (h y hyJ')
    have hxv : Commute (x : Y) v := (hc x hxJ').symm
    have hxv2 : IsPGroup 2 (Subgroup.zpowers ((x : Y) * v)) := isPGroup_zpowers_mul hxv hx2 hv2
    have hxvn : ¬ ∀ w ∈ J', ((x : Y) * v) * w = w * ((x : Y) * v) := by
      intro h
      apply hxy'
      have h1 := h y hyJ'
      have hvy : v * y = y * v := hc y hyJ'
      have : (x : Y) * y * v = y * x * v := by
        calc (x : Y) * y * v = (x : Y) * (v * y) := by rw [mul_assoc, hvy]
          _ = ((x : Y) * v) * y := by group
          _ = y * ((x : Y) * v) := h1
          _ = y * x * v := by group
      exact mul_right_cancel this
    have hx := h5 (x : Y) hxJ' hxn hx2 (hzc _ hxJ')
    have hxvN := h5 ((x : Y) * v) (J'.mul_mem hxJ' hv) hxvn hxv2 (hzc _ (J'.mul_mem hxJ' hv))
    have hv' : v = (x : Y)⁻¹ * ((x : Y) * v) := by group
    rw [hv']
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hxvN
  · exact h5 v hv hc hv2 (hzc v hv)

theorem tightCore_le_normalizer_of_twin (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω)
    {J J' : Subgroup Y} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) (hne : J ≠ J') {z : Y}
    (hzJ : IsUniqueInvolution J z) (hzJ' : Uniform.IsClassicalMemberU (.sl2 3 1) J' z) :
    tightCore J' ≤ Subgroup.normalizer (tightCore J : Set Y) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro v ⟨hv, hv2⟩
  exact mem_normalizer_of_conjSub_eq
    (conjSub_tightCore_of_mem_normalizer (mem_normalizer_of_twin hΩ hJ hJ' hne hzJ hzJ' hv hv2))

theorem hypOmegaGen_tightFamily (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) :
    HypOmegaGen (tightFamily Ω) := by
  have hG := Uniform.hypOmegaGenU_of_modU (Uniform.MemberType.cert_sl2 3 1) hΩ
  refine
    { conjInvariant := ?_
      omega1 := ?_
      omega2 := ?_
      omega3 := ?_
      omega4 := ?_
      omega5 := ?_ }
  · rintro g _ ⟨J, hJ, rfl⟩
    exact ⟨conjSub g J, hΩ.conjInvariant g J hJ, (conjSub_tightCore J g).symm⟩
  · rintro _ ⟨J, hJ, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical J hJ
    obtain ⟨-, P, hP, hPnc⟩ := hG.omega1 J hJ
    exact ⟨⟨z, isUniqueInvolution_tightCore hz⟩, P, isSylow2In_tightCore hP, hPnc⟩
  · rintro _ ⟨J, hJ, rfl⟩
    exact Or.inl (tightCore_tightCore J)
  · rintro _ ⟨J, hJ, rfl⟩ _ ⟨J', hJ', rfl⟩ P Q hP hQ
    exact hG.omega3 J hJ J' hJ' P Q (isSylow2In_of_tightCore hP) (isSylow2In_of_tightCore hQ)
  · rintro _ ⟨J, hJ, rfl⟩ _ ⟨J', hJ', rfl⟩ hne
    have hJJ' : J ≠ J' := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 J hJ J' hJ' hJJ'
    have hle : tightCore J ⊓ tightCore J' ≤ J ⊓ J' :=
      inf_le_inf (tightCore_le J) (tightCore_le J')
    have hdvd : Nat.card ↥(tightCore J ⊓ tightCore J') ∣ Nat.card ↥(J ⊓ J') :=
      Subgroup.card_dvd_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpos : Nat.card ↥(tightCore J ⊓ tightCore J') ≠ 0 := Nat.card_pos.ne'
    have hpos' : Nat.card ↥(J ⊓ J') ≠ 0 := Nat.card_pos.ne'
    have hval : padicValNat 2 (Nat.card ↥(tightCore J ⊓ tightCore J')) ≤
        padicValNat 2 (Nat.card ↥(J ⊓ J')) := by
      rw [← padicValNat_dvd_iff_le hpos']
      exact (pow_padicValNat_dvd).trans hdvd
    refine ⟨hval.trans h1, fun heq => ?_⟩
    have h2dvd : 2 ∣ Nat.card ↥(tightCore J ⊓ tightCore J') :=
      dvd_of_one_le_padicValNat heq.ge
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    obtain ⟨z, hz⟩ := hΩ.classical J hJ
    obtain ⟨z', hz'⟩ := hΩ.classical J' hJ'
    have hu := hz.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)
    have hu' := hz'.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)
    have hw2 : (w : Y) * w = 1 := by
      have := pow_orderOf_eq_one (w : Y)
      rwa [Subgroup.orderOf_coe, hw, pow_two] at this
    have hw1 : (w : Y) ≠ 1 := by
      intro h1
      have : orderOf (w : Y) = 1 := by rw [h1, orderOf_one]
      rw [Subgroup.orderOf_coe, hw] at this
      exact absurd this (by norm_num)
    have hwz : (w : Y) = z :=
      (hu.unique w (tightCore_le J w.2.1) hw2).resolve_left hw1
    have hwz' : (w : Y) = z' :=
      (hu'.unique w (tightCore_le J' w.2.2) hw2).resolve_left hw1
    have hzz : z' = z := hwz'.symm.trans hwz
    subst hzz
    have hJJ'1 : padicValNat 2 (Nat.card ↥(J ⊓ J')) = 1 :=
      le_antisymm h1 (one_le_padicValNat_of_dvd hpos' (h2dvd.trans hdvd))
    have hcomm := h2 hJJ'1
    have hN1 : tightCore J' ≤ Subgroup.normalizer (tightCore J : Set Y) :=
      tightCore_le_normalizer_of_twin hΩ hJ hJ' hJJ' hu hz'
    have hN2 : tightCore J ≤ Subgroup.normalizer (tightCore J' : Set Y) :=
      tightCore_le_normalizer_of_twin hΩ hJ' hJ hJJ'.symm hu' hz
    have hcR : ⁅tightCore J, tightCore J'⁆ ≤ tightCore J ⊓ tightCore J' := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have hb' : b * a⁻¹ * b⁻¹ ∈ tightCore J :=
          (Subgroup.mem_normalizer_iff.mp (hN1 hb) a⁻¹).mp (Subgroup.inv_mem _ ha)
        have := Subgroup.mul_mem _ ha hb'
        simpa [mul_assoc] using this
      · have ha' : a * b * a⁻¹ ∈ tightCore J' :=
          (Subgroup.mem_normalizer_iff.mp (hN2 ha) b).mp hb
        exact Subgroup.mul_mem _ ha' (Subgroup.inv_mem _ hb)
    have hcJ : ⁅tightCore J, tightCore J'⁆ ≤ oddCoreOf J ⊓ oddCoreOf J' :=
      (Subgroup.commutator_mono (tightCore_le J) (tightCore_le J')).trans hcomm
    have hRo : ⁅tightCore J, tightCore J'⁆ ≤ oddCoreOf (tightCore J) :=
      (le_inf (hcR.trans inf_le_left) (hcJ.trans inf_le_left)).trans
        (inf_oddCoreOf_le (tightCore_le J))
    have hRo' : ⁅tightCore J, tightCore J'⁆ ≤ oddCoreOf (tightCore J') :=
      (le_inf (hcR.trans inf_le_right) (hcJ.trans inf_le_right)).trans
        (inf_oddCoreOf_le (tightCore_le J'))
    exact le_inf hRo hRo'
  · rintro _ ⟨J, hJ, rfl⟩ _ ⟨J', hJ', rfl⟩ hne z hz v hv hnc hv2 hvz
    have hJJ' : J ≠ J' := fun h => hne (by rw [h])
    obtain ⟨z0, hz0⟩ := hΩ.classical J hJ
    have hzeq : z = z0 := hz.eq (isUniqueInvolution_tightCore hz0)
    subst hzeq
    have hnc' : ¬ ∀ w ∈ J', v * w = w * v := fun h => hnc fun w hw => h w (tightCore_le J' hw)
    have hn := hΩ.omega5 J hJ J' hJ' hJJ' z
      (hz0.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)) v (tightCore_le J' hv) hnc' hv2
      hvz
    exact mem_normalizer_of_conjSub_eq (conjSub_tightCore_of_mem_normalizer hn)

end TightFamily

section Quotient

variable {Y : Type} [Group Y] [Finite Y]

private theorem sl2Three_pow_four_mul :
    ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

private theorem sl2Three_pow_four_of_pow_eight :
    ∀ a : SL(2, ZMod 3), a ^ 8 = 1 → a ^ 4 = 1 := by
  decide +kernel

private theorem natCard_sl2Three' : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem pow_four_mem_oddCoreOf_tightCore {J : Subgroup Y} {z : Y} (hz : IsClassicalMember3 J z)
    {g : Y} (hg : g ∈ tightCore J) : g ^ 4 ∈ oddCoreOf (tightCore J) := by
  obtain ⟨e⟩ := hz.nonempty_equiv
  set O := classicalInvolutionOddCore ↥J with hO
  let φ : ↥J →* SL(2, ZMod 3) := (e : ↥J ⧸ O →* SL(2, ZMod 3)).comp (QuotientGroup.mk' O)
  have hker : ∀ x : ↥J, φ x = 1 ↔ x ∈ O := by
    intro x
    change e (QuotientGroup.mk' O x) = 1 ↔ x ∈ O
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let H : Subgroup Y :=
    { carrier := {g | ∃ hg : g ∈ J, φ ⟨g, hg⟩ ^ 4 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha4⟩ ⟨hb, hb4⟩
        refine ⟨J.mul_mem ha hb, ?_⟩
        have := sl2Three_pow_four_mul _ _ ha4 hb4
        rwa [← map_mul] at this
      one_mem' := ⟨J.one_mem, by
        change φ 1 ^ 4 = 1
        rw [map_one, one_pow]⟩
      inv_mem' := by
        rintro a ⟨ha, ha4⟩
        refine ⟨J.inv_mem ha, ?_⟩
        change φ (⟨a, ha⟩ : ↥J)⁻¹ ^ 4 = 1
        rw [map_inv, inv_pow, ha4, inv_one] }
  have hTH : tightCore J ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxJ, hx2⟩
    refine ⟨hxJ, sl2Three_pow_four_of_pow_eight _ ?_⟩
    obtain ⟨n, hn⟩ := hx2.exists_card_eq
    rw [Nat.card_zpowers] at hn
    have h1 : orderOf (φ ⟨x, hxJ⟩) ∣ 2 ^ n := by
      have := orderOf_map_dvd φ (⟨x, hxJ⟩ : ↥J)
      rwa [Subgroup.orderOf_mk, hn] at this
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have h2 : orderOf (φ ⟨x, hxJ⟩) ∣ 24 := natCard_sl2Three' ▸ orderOf_dvd_natCard _
    have hi3 : i ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h16 : 2 ^ 4 ∣ orderOf (φ ⟨x, hxJ⟩) := by
        rw [hi]
        exact pow_dvd_pow 2 hlt
      have := h16.trans h2
      norm_num at this
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hi]
    exact pow_dvd_pow 2 hi3
  obtain ⟨hgJ, hg4⟩ := hTH hg
  have hmem : (g ^ 4 : Y) ∈ oddCoreOf J := by
    refine mem_oddCoreOf_iff.mpr ⟨J.pow_mem hgJ 4, ?_⟩
    have : φ ⟨g ^ 4, J.pow_mem hgJ 4⟩ = 1 := by
      have h := hg4
      rwa [← map_pow] at h
    exact (hker _).mp this
  exact inf_oddCoreOf_le (tightCore_le J) ⟨(tightCore J).pow_mem hg 4, hmem⟩

theorem isPGroup_tightCore_quotient {J : Subgroup Y} {z : Y} (hz : IsClassicalMember3 J z) :
    IsPGroup 2 (↥(tightCore J) ⧸ classicalInvolutionOddCore ↥(tightCore J)) := by
  refine isPGroup_iff_pow_pow_eq_one.mpr fun q => ⟨2, ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  obtain ⟨h, hh⟩ := mem_oddCoreOf_iff.mp (pow_four_mem_oddCoreOf_tightCore hz g.2)
  have : g ^ 2 ^ 2 = ⟨(g : Y) ^ 4, h⟩ := Subtype.ext (by simp)
  rw [this]
  exact hh

end Quotient

section Datum

variable {Y : Type} [Group Y] [Finite Y]

theorem map_subtype_tightCore {X : Subgroup Y} (R : Subgroup X) :
    (tightCore R).map X.subtype = tightCore (R.map X.subtype) := by
  unfold tightCore
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, ⟨hxR, hx2⟩, rfl⟩
    exact ⟨⟨x, hxR, rfl⟩, isPGroup_zpowers_coe_iff.mpr hx2⟩
  · rintro ⟨⟨x, hxR, rfl⟩, hy2⟩
    exact ⟨x, ⟨hxR, isPGroup_zpowers_coe_iff.mp hy2⟩, rfl⟩

theorem tightCore_subgroupOf {X R : Subgroup Y} (hRX : R ≤ X) :
    tightCore (R.subgroupOf X) = (tightCore R).subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [map_subtype_tightCore, Subgroup.map_subgroupOf_eq_of_le hRX,
    Subgroup.map_subgroupOf_eq_of_le ((tightCore_le R).trans hRX)]

theorem tightCore_le_of_odd_index {T : Subgroup Y} [T.Normal] (hT : Odd T.index)
    (J : Subgroup Y) : tightCore J ≤ T :=
  (Subgroup.closure_le _).mpr fun x hx =>
    Q3T.MFS.isPGroup_two_le_of_odd_index hT hx.2 (Subgroup.mem_zpowers x)

omit [Finite Y] in
theorem exists_conj_of_sup {T K : Subgroup Y} [hT : T.Normal] (hsup : T ⊔ K = ⊤) (g : Y) :
    ∃ t ∈ T, conjSub g K = conjSub t K := by
  obtain ⟨t, ht, k, hk, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (show g ∈ T ⊔ K by rw [hsup]; exact Subgroup.mem_top g)
  exact ⟨t, ht, by rw [conjSub_mul, conjSub_eq_self_of_mem hk]⟩

structure FrameTightDatum {T : Type} [Group T] (R : Subgroup T) (t : T) : Prop where
  tightCore_eq : tightCore R = R
  unique : IsUniqueInvolution R t
  quat : ∀ P : Subgroup T, IsSylow2In P R → Nonempty (↥P ≃* QuaternionGroup 2)
  twoGroup : IsPGroup 2 (↥R ⧸ classicalInvolutionOddCore ↥R)
  subnormal : IsSubnormal R (Subgroup.centralizer ({t} : Set T))
  hyp : HypOmegaGen (CoreAssembly.conjClass R)
  selfGen : (⨆ g : T, conjSub g R) = ⊤
  twin : ∃ R' ∈ twinSet (CoreAssembly.conjClass R) R, R' ≠ R

omit [Finite Y] in
theorem normal_tightCore_subgroupOf (K : Subgroup Y) : ((tightCore K).subgroupOf K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : conjSub (g : Y) (tightCore K) = tightCore K := by
    rw [conjSub_tightCore, conjSub_eq_self_of_mem g.2]
  have h2 := conj_mem_conjSub (n := (g : Y)) hn
  rw [h1] at h2
  simpa using h2

theorem frameTightDatum_of_frame {T : Subgroup Y} [hTn : T.Normal] [IsSimpleGroup T]
    (hodd : Odd T.index) {Ω : Set (Subgroup Y)} {K : Subgroup Y}
    (hΩ : Uniform.HypOmegaModU (.sl2 3 1) Ω) (hK : K ∈ Ω)
    (htrans : ∀ J ∈ Ω, ∃ g : Y, conjSub g K = J) (hsup : T ⊔ K = ⊤)
    (htwin : ∃ K' ∈ twinSet Ω K, K' ≠ K) {z : Y}
    (hz : Uniform.IsClassicalMemberU (.sl2 3 1) K z) :
    FrameTightDatum ((tightCore K).subgroupOf T)
      (⟨z, tightCore_le_of_odd_index hodd K (mem_tightCore_of_member hz)⟩ : T) := by
  have hKT : tightCore K ≤ T := tightCore_le_of_odd_index hodd K
  have hz3 : IsClassicalMember3 K z := hz.toQ3 (by norm_num)
  have hu : IsUniqueInvolution ((tightCore K).subgroupOf T)
      (⟨z, tightCore_le_of_odd_index hodd K (mem_tightCore_of_member hz)⟩ : T) :=
    isUniqueInvolution_subgroupOf (isUniqueInvolution_tightCore hz) hKT
  have hcl : CoreAssembly.conjClass ((tightCore K).subgroupOf T) =
      restrictFamily (tightFamily Ω) T := by
    ext R'
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨tightCore (conjSub (t : Y) K),
        ⟨conjSub (t : Y) K, hΩ.conjInvariant _ K hK, rfl⟩, tightCore_le_of_odd_index hodd _, ?_⟩
      show conjSub t ((tightCore K).subgroupOf T) = (tightCore (conjSub (t : Y) K)).subgroupOf T
      rw [conjSub_subgroupOf, conjSub_tightCore]
    · rintro ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩
      obtain ⟨g, rfl⟩ := htrans J hJ
      obtain ⟨t, ht, hgt⟩ := exists_conj_of_sup hsup g
      refine ⟨⟨t, ht⟩, ?_⟩
      show conjSub (⟨t, ht⟩ : T) ((tightCore K).subgroupOf T) =
        (tightCore (conjSub g K)).subgroupOf T
      rw [conjSub_subgroupOf, conjSub_tightCore, hgt]
  refine
    { tightCore_eq := ?_
      unique := hu
      quat := ?_
      twoGroup := ?_
      subnormal := ?_
      hyp := ?_
      selfGen := ?_
      twin := ?_ }
  · rw [tightCore_subgroupOf hKT, tightCore_tightCore]
  · intro P hP
    have h1 : IsSylow2In (P.map T.subtype) (tightCore K) := by
      have := isSylow2In_map_subtype_iff.mpr hP
      rwa [Subgroup.map_subgroupOf_eq_of_le hKT] at this
    have h2 : IsSylow2In (P.map T.subtype) K := isSylow2In_of_tightCore h1
    obtain ⟨S', hS'⟩ := exists_sylow_map_eq h2
    obtain ⟨e⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 hz3 S'
    exact ⟨(((Subgroup.equivMapOfInjective P T.subtype T.subtype_injective).trans
      (MulEquiv.subgroupCongr hS'.symm)).trans
      (Subgroup.equivMapOfInjective (S' : Subgroup K) K.subtype K.subtype_injective).symm).trans
      e⟩
  · let φ : ↥((tightCore K).subgroupOf T) ≃* ↥(tightCore K) := Subgroup.subgroupOfEquivOfLe hKT
    exact (isPGroup_tightCore_quotient hz3).of_equiv
      (QuotientGroup.congr _ _ φ.symm (CFSG.ComponentClassification.OddCore.equiv_invariant φ.symm))
  · have hcK : IsSubnormal (tightCore K) K :=
      isSubnormal_of_normal_subgroupOf (tightCore_le K) (normal_tightCore_subgroupOf K)
    have h0 : IsSubnormal (tightCore K) (Subgroup.centralizer ({z} : Set Y)) :=
      isSubnormal_trans hcK hz.subnormal
    have h1 : IsSubnormal (tightCore K) (Subgroup.centralizer ({z} : Set Y) ⊓ T) := by
      have := isSubnormal_inf h0 T
      rwa [inf_eq_left.mpr hKT] at this
    have h2 : (Subgroup.centralizer ({z} : Set Y) ⊓ T).subgroupOf T =
        Subgroup.centralizer
          ({(⟨z, tightCore_le_of_odd_index hodd K (mem_tightCore_of_member hz)⟩ : T)} : Set T) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        Set.mem_singleton_iff, forall_eq]
      exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩
    rw [← h2]
    exact isSubnormal_subgroupOf h1 T
  · rw [hcl]
    exact hypOmegaGen_restrict (hypOmegaGen_tightFamily hΩ) T
  · set R : Subgroup T := (tightCore K).subgroupOf T with hR
    set N : Subgroup T := ⨆ g : T, conjSub g R with hN
    have hle : ∀ h : T, conjSub h N ≤ N := by
      intro h
      have hc : conjSub h N = ⨆ g : T, conjSub (h * g) R := by
        change (⨆ g : T, conjSub g R).map (MulAut.conj h).toMonoidHom = _
        rw [Subgroup.map_iSup]
        congr 1
        funext g
        exact (conjSub_mul h g R).symm
      rw [hc]
      exact iSup_le fun g => le_iSup (fun g : T => conjSub g R) (h * g)
    have hNn : N.Normal := ⟨fun n hn h => hle h (conj_mem_conjSub hn)⟩
    rcases hNn.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hRN : R ≤ N := by
        have := le_iSup (fun g : T => conjSub g R) 1
        simpa using this
      have hmem := hRN hu.mem
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hu.ne_one hmem
    · exact htop
  · obtain ⟨K', ⟨hK'Ω, w, hwK, hwK'⟩, hne⟩ := htwin
    have hw : w = z := hwK.eq (hz.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1))
    subst hw
    obtain ⟨g, rfl⟩ := htrans K' hK'Ω
    obtain ⟨t, ht, hgt⟩ := exists_conj_of_sup hsup g
    obtain ⟨z', hz'⟩ := hΩ.classical _ hK'Ω
    have hzz : z' = w := (hz'.isUniqueInvolution (Uniform.MemberType.cert_sl2 3 1)).eq hwK'
    subst hzz
    have hK'T : tightCore (conjSub g K) ≤ T := tightCore_le_of_odd_index hodd _
    have hR' : conjSub (⟨t, ht⟩ : T) ((tightCore K).subgroupOf T) =
        (tightCore (conjSub g K)).subgroupOf T := by
      rw [conjSub_subgroupOf, conjSub_tightCore, hgt]
    refine ⟨conjSub (⟨t, ht⟩ : T) ((tightCore K).subgroupOf T),
      ⟨⟨⟨t, ht⟩, rfl⟩, _, hu, ?_⟩, ?_⟩
    · rw [hR']
      exact isUniqueInvolution_subgroupOf (isUniqueInvolution_tightCore hz') hK'T
    · intro heq
      rw [hR'] at heq
      have heq' : tightCore (conjSub g K) = tightCore K := by
        have := congrArg (Subgroup.map T.subtype) heq
        rwa [Subgroup.map_subgroupOf_eq_of_le hK'T, Subgroup.map_subgroupOf_eq_of_le hKT] at this
      obtain ⟨P, hP⟩ := Uniform.exists_isSylow2In K
      obtain ⟨S', hS'⟩ := exists_sylow_map_eq hP
      obtain ⟨e⟩ := Q3T6.quaternion_sylow_of_isClassicalMember3 hz3 S'
      have hP8 : Nat.card ↥P = 8 := by
        have h1 : Nat.card ↥(S' : Subgroup ↥K) = 8 := by
          rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
        have h2 : Nat.card ↥(S' : Subgroup ↥K) = Nat.card ↥P := by
          rw [← hS', Subgroup.card_map_of_injective K.subtype_injective]
        rw [← h2, h1]
      have hPK' : P ≤ conjSub g K :=
        (le_tightCore_of_isPGroup hP.1 hP.2.1).trans (heq'.symm ▸ tightCore_le _)
      have hPKK : P ≤ K ⊓ conjSub g K := le_inf hP.1 hPK'
      have hdvd : 2 ^ 3 ∣ Nat.card ↥(K ⊓ conjSub g K) := by
        rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hP8]
        exact Subgroup.card_dvd_of_le hPKK
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hval := (padicValNat_dvd_iff_le (Nat.card_pos (α := ↥(K ⊓ conjSub g K))).ne').mp hdvd
      have h1 := (hΩ.omega4 K hK (conjSub g K) hK'Ω (Ne.symm hne)).1
      omega

end Datum

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
