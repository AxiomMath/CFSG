module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3M
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3S3N
public import CFSG.ClassicalInvolution.Q3.TL4E3S3ZB
public import CFSG.ClassicalInvolution.Q3.TL4MF163M12A

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def SecIdE3S3M12Center : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    EdgelessMember3 R S t → MuS3Member R → ¬ TightInO2 t → CFSG.Open.IsQuasisimple Y →
      Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12) →
        Subgroup.center Y = ⊥

namespace E3S3P

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem mem_genFittingFStar (hd : TightDatum R S t)
    (hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2))
    (hi : (genFittingFStar Y).index ∣ 6) : t ∈ genFittingFStar Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : Subgroup Y := genFittingFStar Y with hFdef
  have hFn : F.Normal := genFittingFStar_normal Y
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hS₀K : S₀ ≤ tightCore R := hd.sylow_core.1
  have hut := hd.isUniqueInvolution_core
  have hS₀8 : Nat.card ↥S₀ = 8 := by
    obtain ⟨e⟩ := hq
    rw [hS₀, Subgroup.card_map_of_injective R.subtype_injective, Nat.card_congr e.toEquiv,
      Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h1 : F.relIndex S₀ ∣ 6 := (Subgroup.relIndex_dvd_index_of_normal F S₀).trans hi
  have h2 : F.relIndex S₀ ∣ 8 := hS₀8 ▸ Subgroup.relIndex_dvd_card F S₀
  have h3 : F.relIndex S₀ ∣ 2 := by
    have := Nat.dvd_gcd h1 h2
    simpa using this
  have hmul := Subgroup.relIndex_mul_card (H := F) (K := S₀)
  rw [hS₀8] at hmul
  have hcard : 2 ∣ Nat.card ↥(F ⊓ S₀) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h <;> rw [h] at hmul <;> omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(F ⊓ S₀)) 2 hcard
  have hxF : (x : Y) ∈ F := (Subgroup.mem_inf.mp x.2).1
  have hxK : (x : Y) ∈ tightCore R := hS₀K (Subgroup.mem_inf.mp x.2).2
  have hx2 : (x : Y) * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx, pow_two] at h
    exact congrArg Subtype.val h
  have hx1 : (x : Y) ≠ 1 := by
    intro h
    have h' : x = 1 := Subtype.ext h
    rw [h', orderOf_one] at hx
    exact absurd hx (by norm_num)
  rcases hut.unique _ hxK hx2 with h | h
  · exact absurd h hx1
  · rw [← h]
    exact hxF

theorem center_le_genFittingFStar : Subgroup.center Y ≤ genFittingFStar Y := fun _ hz =>
  centralizer_genFittingFStar_le (Subgroup.mem_centralizer_iff.mpr fun f _ =>
    Subgroup.mem_center_iff.mp hz f)

theorem genFittingFStar_eq_top_of_simple (hS : IsSimpleGroup (Y ⧸ Subgroup.center Y)) :
    genFittingFStar Y = ⊤ := by
  have hZ : Subgroup.center Y ≠ ⊤ := by
    intro h
    obtain ⟨x, y, hxy⟩ := hS.toNontrivial.exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    exact hxy (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))
  have hFn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have := hFn.map _ (QuotientGroup.mk'_surjective (Subgroup.center Y))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
  · exfalso
    have hFZ : genFittingFStar Y ≤ Subgroup.center Y := by
      intro f hf
      have h1 : QuotientGroup.mk' (Subgroup.center Y) f ∈
          (genFittingFStar Y).map (QuotientGroup.mk' _) := ⟨f, hf, rfl⟩
      rwa [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hZ
    rw [eq_top_iff]
    intro g _
    exact hFZ (centralizer_genFittingFStar_le (Subgroup.mem_centralizer_iff.mpr fun f hf =>
      (Subgroup.mem_center_iff.mp (hFZ hf) g).symm))
  · rw [eq_top_iff]
    intro g _
    have h1 : QuotientGroup.mk' (Subgroup.center Y) g ∈
        (genFittingFStar Y).map (QuotientGroup.mk' _) := h ▸ Subgroup.mem_top _
    obtain ⟨f, hf, hfg⟩ := h1
    have h2 := (genFittingFStar Y).mul_mem hf (center_le_genFittingFStar (QuotientGroup.eq.mp hfg))
    rwa [mul_inv_cancel_left] at h2

omit [Finite Y] in
theorem nonempty_fstarQuot_equiv_map
    (hZle : (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype ≤
      Subgroup.center Y) :
    Nonempty (FStarQuot Y ≃*
      ↥((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)))) := by
  let φ : ↥(genFittingFStar Y) →* Y ⧸ Subgroup.center Y :=
    (QuotientGroup.mk' (Subgroup.center Y)).comp (genFittingFStar Y).subtype
  have hker : Subgroup.center ↥(genFittingFStar Y) = φ.ker := by
    ext x
    rw [MonoidHom.mem_ker]
    change x ∈ Subgroup.center ↥(genFittingFStar Y) ↔
      QuotientGroup.mk' (Subgroup.center Y) (x : Y) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      exact hZle (Subgroup.mem_map_of_mem _ hx)
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp hx g)
  have hrange : φ.range = (genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange)⟩

theorem quot_fstar (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : ¬ TightInO2 t)
    (hE : TightEdgeless R) :
    TightFStarQuasisimple (Y ⧸ Subgroup.center Y) ∧
      Subgroup.center ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) = ⊥ ∧
        IsSimpleGroup ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) := by
  have hN2 := E3S3Z.isPGroup_center hc
  have htN := E3S3Z.not_mem_center hc hO2
  have hm := E3S3Z.edgelessMember3_quot hd hc hO2 hE
  have hcb := TwistQ.cls hd le_rfl hN2 htN hc
  have hE2b : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Y) t) :=
    fun h => hO2 (TwistQ.inO2_of hN2 h)
  have hZb := E3S3Z.center_quot_eq_bot hd hc hO2
  have hq : TightFStarQuasisimple (Y ⧸ Subgroup.center Y) := by
    rcases tightDichotomy_of hm.datum hcb with h | h | ⟨L, -, -, -, -, -, hFc, hFL⟩
    · exact absurd h hE2b
    · exact h
    · rw [hZb] at hFc
      exact absurd (hFc.trans bot_le) hFL
  have hZF : Subgroup.center ↥(genFittingFStar (Y ⧸ Subgroup.center Y)) = ⊥ := by
    have h1 := TightDatum.center_genFittingFStar_le hm.datum hcb hE2b
    rw [hZb, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar _).subtype_injective).mp h1
  exact ⟨hq, hZF, (isSimpleGroup_of_quasisimple_of_center_eq_bot hq hZF).1⟩

theorem fstar_quot_eq_map (hQ : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y))
    (hZle : (Subgroup.center ↥(genFittingFStar Y)).map (genFittingFStar Y).subtype ≤
      Subgroup.center Y)
    (hs : IsSimpleGroup ↥(genFittingFStar (Y ⧸ Subgroup.center Y))) :
    genFittingFStar (Y ⧸ Subgroup.center Y) =
      (genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) := by
  have hFn : (genFittingFStar Y).Normal := genFittingFStar_normal Y
  have hMn : ((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    hFn.map _ (QuotientGroup.mk'_surjective _)
  have hGn : (genFittingFStar (Y ⧸ Subgroup.center Y)).Normal := genFittingFStar_normal _
  obtain ⟨e⟩ := nonempty_fstarQuot_equiv_map hZle
  have : IsSimpleGroup (FStarQuot Y) := hQ.2
  have hMs : IsSimpleGroup ↥((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y))) :=
    e.symm.isSimpleGroup
  have hMne : (genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hMs.toNontrivial
  have hGne : genFittingFStar (Y ⧸ Subgroup.center Y) ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp hs.toNontrivial
  have hGM : genFittingFStar (Y ⧸ Subgroup.center Y) ≤
      (genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) := by
    have hne : (genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) ⊓
        genFittingFStar (Y ⧸ Subgroup.center Y) ≠ ⊥ := by
      intro h
      have hc : ⁅(genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)),
          genFittingFStar (Y ⧸ Subgroup.center Y)⁆ = ⊥ :=
        le_bot_iff.mp (h ▸ le_inf (Subgroup.commutator_le_left _ _)
          (Subgroup.commutator_le_right _ _))
      have hMG := ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc).trans
        centralizer_genFittingFStar_le
      exact hMne (le_bot_iff.mp (h ▸ le_inf le_rfl hMG))
    have : ((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) ⊓
        genFittingFStar (Y ⧸ Subgroup.center Y)).Normal := Subgroup.normal_inf_normal _ _
    have hN := this.subgroupOf (genFittingFStar (Y ⧸ Subgroup.center Y))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)) ⊓
        genFittingFStar (Y ⧸ Subgroup.center Y)).subgroupOf
          (genFittingFStar (Y ⧸ Subgroup.center Y))) with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      exact hne (disjoint_self.mp (h.mono_right inf_le_right))
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact h.trans inf_le_left
  have hN := hGn.subgroupOf ((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((genFittingFStar (Y ⧸ Subgroup.center Y)).subgroupOf
      ((genFittingFStar Y).map (QuotientGroup.mk' (Subgroup.center Y)))) with h | h
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact hGne (disjoint_self.mp (h.mono_right hGM))
  · rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hGM h

theorem acts3_of_m12 (hm : EdgelessMember3 R S t) (hO2 : ¬ TightInO2 t)
    (hQ : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y))
    (hm12 : NativeSporadic.IsSporadic (FStarQuot Y) .M12)
    (hi : (genFittingFStar Y).index ≤ 2) : TightActs3 R t := by
  have hd := hm.datum
  have hc : TightCls Y R S t := hm.cls
  have hE := hm.edgeless
  have hN2 := E3S3Z.isPGroup_center hc
  have htN := E3S3Z.not_mem_center hc hO2
  have hnt := E3S3Z.noTwin hd hE
  have hmb := E3S3Z.edgelessMember3_quot hd hc hO2 hE
  obtain ⟨-, hZ', hs⟩ := quot_fstar hd hc hO2 hE
  have hZle := TightDatum.center_genFittingFStar_le hd hc hO2
  have heq := fstar_quot_eq_map hQ hZle hs
  obtain ⟨e⟩ := nonempty_fstarQuot_equiv_map hZle
  obtain ⟨e12⟩ := hm12
  have hidx : (genFittingFStar (Y ⧸ Subgroup.center Y)).index ≤ 2 := by
    rw [heq, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact center_le_genFittingFStar)]
    exact hi
  have hspor : NativeSporadic.IsSporadic (FStarQuot (Y ⧸ Subgroup.center Y)) .M12 :=
    ⟨(((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).trans
      (MulEquiv.subgroupCongr heq)).trans (e.symm.trans e12)⟩
  exact E3S3Z.acts3_of_map hd le_rfl hN2 htN hnt
    (modelM12Acts3_proved _ _ _ _ hmb hs hidx hspor)

end E3S3P


theorem secIdE3MuS3_of_not_twisted (hM12 : SecIdE3S3M12Center) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      EdgelessMember3 R S t → MuS3Member R → ¬ TightInO2 t →
        ((¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
          Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) →
        ¬ TightTwisted Y t →
        IsSimpleGroup ↥(genFittingFStar Y) ∧ (genFittingFStar Y).index ∣ 6 := by
  intro Y _ _ R S t hm hmu hO2 hx hnt
  have hd := hm.datum
  have hq : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hm.cls.1
  have hnc : t ∉ Subgroup.center Y := fun h => by
    refine hO2 ⟨Subgroup.zpowers t, Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr h),
      IsPGroup.of_card (n := 1) ?_, Subgroup.mem_zpowers t⟩
    rw [Nat.card_zpowers, hd.order, pow_one]
  have hZle := TightDatum.center_genFittingFStar_le hd hm.cls hO2
  have hcenF : ∀ {x : ↥(genFittingFStar Y)}, x ∈ Subgroup.center ↥(genFittingFStar Y) →
      (x : Y) ∈ Subgroup.center Y := fun hx => hZle (Subgroup.mem_map_of_mem _ hx)
  have hZF2 : IsPGroup 2 ↥(Subgroup.center ↥(genFittingFStar Y)) :=
    ((E3S3Z.isPGroup_center (t := t) hm.cls).to_le hZle).of_equiv
      ((Subgroup.center ↥(genFittingFStar Y)).equivMapOfInjective _
        (genFittingFStar Y).subtype_injective).symm
  have hQo : CFSG.Open.IsQuasisimple ↥(genFittingFStar Y) := by
    rcases tightDichotomy_holds (Nat.card Y) Y rfl R S t hd hm.cls with h | h | h
    · exact absurd h hO2
    · exact h
    · exact absurd h hnt
  have hQ : CFSG.IsQuasisimple ↥(genFittingFStar Y) := by
    have : Group.IsPerfect ↥(genFittingFStar Y) := ⟨hQo.1⟩
    have := hQo.2
    refine ⟨inferInstance, hQo.2, ?_⟩
    simpa only [isMulCommutative_iff, not_forall] using
      Group.IsPerfect.not_isMulCommutative
        (↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y))
  have hsimp : Subgroup.center ↥(genFittingFStar Y) = ⊥ →
      IsSimpleGroup ↥(genFittingFStar Y) := fun hZ =>
    (isSimpleGroup_of_quasisimple_of_center_eq_bot hQo hZ).1
  have hi6 : (genFittingFStar Y).index ≤ 2 → (genFittingFStar Y).index ∣ 6 := fun hi => by
    have h0 := (genFittingFStar Y).index_ne_zero_of_finite
    rcases (show (genFittingFStar Y).index = 1 ∨ (genFittingFStar Y).index = 2 by omega)
      with h | h <;> rw [h] <;> norm_num
  have hM : IsSimpleGroup (NativeSporadic.Carrier .M12) :=
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
  rcases hx with ⟨h3, hX | hTw⟩ | hE
  · rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl, hi⟩ | ⟨hl, hi⟩⟩ | ⟨hm12, hi⟩
    ·
      have htF := E3S3P.mem_genFittingFStar hd hq (hi6 hi)
      have h5 : 5 ≤ p ^ f := by
        obtain ⟨k, rfl⟩ := hf
        have hk : 1 ≤ k + k := (CFSG.GH74.Generic.lieModel_psl_data hl).2.1
        have h3 : 3 ≤ p := by have := hp.two_le; omega
        calc 5 ≤ 3 ^ 2 := by norm_num
          _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
          _ ≤ p ^ (k + k) := Nat.pow_le_pow_right (by omega) (by omega)
      exact ⟨hsimp (E3S3M.center_eq_bot_of_psl2 hQ (MulEquiv.refl _) hl hp2 h5 hZF2
        (x := ⟨t, htF⟩) (Subtype.ext hd.isUniqueInvolution_core.sq) fun h => hnc (hcenF h)),
        hi6 hi⟩
    ·
      rcases hl with hl | hl
      · exact ⟨hsimp (E3S3M.center_eq_bot_of_odd hQ (MulEquiv.refl _) hZF2
          (E3S3M.odd_natCard_hopf_psl3 hl hp2)), hi⟩
      · exact ⟨hsimp (E3S3M.center_eq_bot_of_odd hQ (MulEquiv.refl _) hZF2
          (E3S3M.odd_natCard_hopf_psu3 hl hp2)), hi⟩
    ·
      exact absurd (E3S3P.acts3_of_m12 hm hO2 hQo hm12 hi) h3
  · exact absurd hTw hnt
  ·
    obtain ⟨e⟩ := hE
    have hS : IsSimpleGroup (Y ⧸ Subgroup.center Y) := e.isSimpleGroup
    have hFtop := E3S3P.genFittingFStar_eq_top_of_simple hS
    have hperf : Group.IsPerfect Y := by
      have : Group.IsPerfect ↥(genFittingFStar Y) := ⟨hQo.1⟩
      refine Group.IsPerfect.ofSurjective (f := (genFittingFStar Y).subtype) fun y => ?_
      exact ⟨⟨y, hFtop ▸ Subgroup.mem_top y⟩, rfl⟩
    have hY := hM12 Y R S t hm hmu hO2 ⟨hperf.commutator_eq_top, hS⟩ ⟨e⟩
    have hZ : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
      have h1 := hZle
      rw [hY, le_bot_iff] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar Y).subtype_injective).mp h1
    exact ⟨hsimp hZ, by rw [hFtop, Subgroup.index_top]; exact one_dvd 6⟩

theorem secIdE3MuS3_of (hM12 : SecIdE3S3M12Center) (hTw : SecIdE3S3NoTwist) :
    SecIdE3MuS3 := by
  intro Y _ _ h6 R S t hm hmu hO2 hx
  have hd := hm.datum
  have hc : TightCls Y R S t := hm.cls
  have hE := hm.edgeless
  have hnt : ¬ TightTwisted Y t := by
    intro htw
    rcases hx with ⟨h3, -⟩ | hE3b
    ·
      have hN2 := E3S3Z.isPGroup_center hc
      have htN := E3S3Z.not_mem_center hc hO2
      have hnt' := E3S3Z.noTwin hd hE
      have hmb := E3S3Z.edgelessMember3_quot hd hc hO2 hE
      have hE2b : ¬ TightInO2 (QuotientGroup.mk' (Subgroup.center Y) t) :=
        fun h => hO2 (TwistQ.inO2_of hN2 h)
      obtain ⟨hq, -, -⟩ := E3S3P.quot_fstar hd hc hO2 hE
      have hZne : Subgroup.center Y ≠ ⊥ := by
        obtain ⟨L, -, -, -, -, -, hFc, hFL⟩ := htw
        intro h
        rw [h] at hFc
        exact hFL (hFc.trans bot_le)
      have hlt : Nat.card (Y ⧸ Subgroup.center Y) < Nat.card Y := by
        have hZ1 : 1 < Nat.card ↥(Subgroup.center Y) :=
          (Subgroup.one_lt_card_iff_ne_bot _).mpr hZne
        have hpos : 0 < Nat.card (Y ⧸ Subgroup.center Y) := Nat.card_pos
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)]
        exact lt_mul_of_one_lt_right hpos hZ1
      rcases h6 _ hlt _ _ _ hmb.datum hmb.cls hE2b hq hmb.edgeless with hg | hX
      · obtain ⟨x, k, hxC, hx3, hxR, -⟩ := TwistQ.good_of hd le_rfl hN2 htN hnt' hg
        exact h3 ⟨x, k, hxC, hx3, hxR⟩
      · exact hTw Y R S t hm hmu hO2 htw (Or.inl ⟨h3, hX⟩)
    · exact hTw Y R S t hm hmu hO2 htw (Or.inr hE3b)
  obtain ⟨h1, h2⟩ := secIdE3MuS3_of_not_twisted hM12 Y R S t hm hmu hO2 hx hnt
  exact ⟨h1, h2, hnt⟩

end CFSG.ClassicalInvolution.Q3.TL4
