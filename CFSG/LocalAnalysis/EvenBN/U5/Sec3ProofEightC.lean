module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightV

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups
open scoped commutatorElement

section Generic

theorem sec38c_comm_of_normal {H : Type*} [Group H] [Finite H] {O : Subgroup H} [O.Normal]
    {A : Subgroup H} {tb : H}
    (hnorm : (A.map (QuotientGroup.mk' O)).Normal)
    (hinj : ∀ Q : Subgroup H, IsPGroup 2 Q → Set.InjOn (QuotientGroup.mk' O) (Q : Set H))
    (hord : orderOf (QuotientGroup.mk' O tb) = 2)
    (hcard : ∀ S : Sylow 2 (centralizer ((A.map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) :
      Set (H ⧸ O))), Nat.card S = 2)
    (htA : tb ∈ centralizer (A : Set H))
    {X : Subgroup H} (hX : IsPGroup 2 X) (htX : tb ∈ X) {x : H} (hx : x ∈ X) :
    x * tb = tb * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ := QuotientGroup.mk' O with hθ
  set Ct : Subgroup (H ⧸ O) :=
    centralizer ((A.map θ : Subgroup (H ⧸ O)) : Set (H ⧸ O)) with hCt
  have hconj : ∀ y : H, θ (y⁻¹ * tb * y) ∈ Ct := by
    intro y
    rw [hCt, mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨a', ha', ha'e⟩ := hnorm.conj_mem (θ a) ⟨a, ha, rfl⟩ (θ y)
    have hc : θ a' * θ tb = θ tb * θ a' := by
      rw [← map_mul, ← map_mul]
      exact congrArg θ (mem_centralizer_iff.1 htA a' ha')
    have ha_eq : θ a = (θ y)⁻¹ * θ a' * θ y := by rw [ha'e]; group
    rw [map_mul, map_mul, map_inv, ha_eq]
    calc (θ y)⁻¹ * θ a' * θ y * ((θ y)⁻¹ * θ tb * θ y)
        = (θ y)⁻¹ * (θ a' * θ tb) * θ y := by group
      _ = (θ y)⁻¹ * (θ tb * θ a') * θ y := by rw [hc]
      _ = (θ y)⁻¹ * θ tb * θ y * ((θ y)⁻¹ * θ a' * θ y) := by group
  set Q : Subgroup (H ⧸ O) := X.map θ ⊓ Ct with hQ
  have hQ2 : IsPGroup 2 Q := (hX.map θ).to_le inf_le_left
  have hQC : Q ≤ Ct := inf_le_right
  have hQcard : Nat.card Q ≤ 2 := by
    have hQ' : IsPGroup 2 (Q.subgroupOf Ct) := hQ2.of_equiv (subgroupOfEquivOfLe hQC).symm
    obtain ⟨S', hS'⟩ := hQ'.exists_le_sylow
    calc Nat.card Q = Nat.card (Q.subgroupOf Ct) :=
          Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv.symm
      _ ≤ Nat.card S' := Subgroup.card_le_of_le hS'
      _ = 2 := hcard S'
  have htC : θ tb ∈ Ct := by
    have := hconj 1
    simpa using this
  have htQ : θ tb ∈ Q := ⟨mem_map_of_mem θ htX, htC⟩
  have hyX : x⁻¹ * tb * x ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hx) htX) hx
  have hyQ : θ (x⁻¹ * tb * x) ∈ Q := ⟨mem_map_of_mem θ hyX, hconj x⟩
  have hQeq : zpowers (θ tb) = Q := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 htQ) ?_
    rw [Nat.card_zpowers, hord]
    exact hQcard
  have hmem : θ (x⁻¹ * tb * x) ∈ zpowers (θ tb) := hQeq ▸ hyQ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have htb1 : tb ≠ 1 := fun h1 => by
    rw [h1, map_one, orderOf_one] at hord
    omega
  have hy1 : x⁻¹ * tb * x ≠ 1 := fun h1 => htb1 (by
    have := congrArg (fun z => x * z * x⁻¹) h1
    simpa [mul_assoc] using this)
  have hθy1 : θ (x⁻¹ * tb * x) ≠ 1 := fun h1 => hy1 (hinj X hX hyX (one_mem X) (by rw [h1, map_one]))
  have hθeq : θ (x⁻¹ * tb * x) = θ tb := by
    have hk' : θ tb ^ (k % 2) = θ (x⁻¹ * tb * x) := by
      have := zpow_mod_orderOf (θ tb) k
      rw [hord, Nat.cast_ofNat] at this
      exact this.trans hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk'
      exact absurd hk'.symm hθy1
    · rw [h1, zpow_one] at hk'
      exact hk'.symm
  have hyt : x⁻¹ * tb * x = tb := hinj X hX hyX htX hθeq
  calc x * tb = x * (x⁻¹ * tb * x) := by rw [hyt]
    _ = tb * x := by group

theorem sec38c_normal_two_group_eq_bot {X : Type*} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X)
    (hZ : ∀ z ∈ center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (Y : Subgroup X) [hYn : Y.Normal] (hY : IsPGroup 2 Y) : Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (X ⧸ center X) := hX.2
  have hmapN : (Y.map (QuotientGroup.mk' (center X))).Normal :=
    hYn.map _ (QuotientGroup.mk'_surjective _)
  haveI := hmapN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' (center X))) with hb | ht
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, hk⟩ := hY ⟨y, hy⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.2 (hZ y (hb hy) k hyk)
  · exfalso
    have hdec : ∀ x : X, ∃ z ∈ center X, QuotientGroup.mk' Y x = QuotientGroup.mk' Y z := by
      intro x
      have : QuotientGroup.mk' (center X) x ∈ Y.map (QuotientGroup.mk' (center X)) := by
        rw [ht]; exact mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      have hz : y⁻¹ * x ∈ center X := by
        rw [← QuotientGroup.ker_mk' (center X), MonoidHom.mem_ker, map_mul, map_inv, hyx,
          inv_mul_cancel]
      refine ⟨y⁻¹ * x, hz, ?_⟩
      have hy1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [map_mul, map_inv, hy1, inv_one, one_mul]
    have hcomm : commutator X ≤ Y := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun g1 _ g2 _ => ?_
      obtain ⟨z1, hz1, e1⟩ := hdec g1
      obtain ⟨z2, hz2, e2⟩ := hdec g2
      have hz12 : ⁅z1, z2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hz2 z1)
      have h1 : QuotientGroup.mk' Y ⁅g1, g2⁆ = 1 := by
        rw [map_commutatorElement, e1, e2, ← map_commutatorElement, hz12, map_one]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hYtop : Y = ⊤ := top_le_iff.1 (hX.1 ▸ hcomm)
    haveI : IsPGroup 2 X := by
      subst hYtop
      exact hY.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent X := IsPGroup.isNilpotent this
    haveI : Group.IsPerfect X := ⟨hX.1⟩
    haveI : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
    exact Group.IsPerfect.not_isNilpotent X inferInstance

theorem sec38c_map_conj_le_iff {G : Type*} [Group G] (y : G) {Y Z : Subgroup G} :
    Y.map (MulAut.conj y).toMonoidHom ≤ Z ↔ Y ≤ Z.map (MulAut.conj y⁻¹).toMonoidHom := by
  constructor
  · intro hle s hs
    refine ⟨y * s * y⁻¹, hle ⟨s, hs, rfl⟩, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  · rintro hle _ ⟨s, hs, rfl⟩
    obtain ⟨z, hz, hzs⟩ := hle hs
    have : y * s * y⁻¹ = z := by
      rw [← hzs]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      group
    change y * s * y⁻¹ ∈ Z
    rwa [this]

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec38c_center_N₂ (d : Data G h) :
    ∀ z ∈ center ↥d.N₂, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  intro z hz k hk
  have hzN : (z : G) ∈ d.N₂ := z.2
  have hI₂ : (z : G) ∈ d.I₂ := d.mem_I₂_of_comm_N₂ hzN fun n hn =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨n, hn⟩).symm
  have hI : (z : G) ∈ d.I := d.pull_mono (torusEq_le _) hI₂
  set zI : ↥d.I := ⟨z, hI⟩ with hzI
  have h1 : orderOf zI ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    simpa using congrArg Subtype.val hk))
  have h2 : orderOf zI ∣ Nat.card ↥d.I := orderOf_dvd_natCard zI
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥d.I) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 d.odd_card_I)
  have h3 : orderOf zI = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : zI = 1 := orderOf_eq_one_iff.1 h3
  have h5 : (z : G) = 1 := congrArg Subtype.val h4
  exact Subtype.ext h5

theorem sec38c_E_inf_N₂ (hp : d.CaseHyp) : d.E ⊓ d.N₂ = ⊥ := by
  have hq : CFSG.Open.IsQuasisimple ↥d.N₂ :=
    (hp.hyp.quasisimple_lieModel_N₂ (X := ↥d.N₂) ⟨MulEquiv.refl _⟩).1
  set Y : Subgroup ↥d.N₂ := (d.E ⊓ d.N₂).subgroupOf d.N₂ with hY
  haveI hYn : Y.Normal := ⟨fun y hy n => by
    rw [hY, mem_subgroupOf] at hy ⊢
    refine ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 (d.N₂_le_normalizer_E n.2) y).1 hy.1
      simpa using this
    · exact (n * y * n⁻¹).2⟩
  have hYp : IsPGroup 2 Y :=
    ((hp.hyp.isPGroup_E hp.gms).to_le (inf_le_left : d.E ⊓ d.N₂ ≤ d.E)).of_equiv
      (subgroupOfEquivOfLe (inf_le_right : d.E ⊓ d.N₂ ≤ d.N₂)).symm
  have hY1 := sec38c_normal_two_group_eq_bot hq (sec38c_center_N₂ d) Y hYp
  refine eq_bot_iff.2 fun x hx => ?_
  have hxY : (⟨x, hx.2⟩ : ↥d.N₂) ∈ Y := mem_subgroupOf.2 hx
  rw [hY1, mem_bot] at hxY
  exact congrArg Subtype.val hxY

theorem sec38c_barEquiv (hp : d.CaseHyp) : Nonempty (↥(bar d.E d.N₂) ≃* ↥d.N₂) := by
  set φ : ↥d.N₂ →* Bar d.E :=
    (proj d.E).comp (Subgroup.inclusion (d.N₂_le_normalizer_E)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : (n : G) ∈ d.E :=
      (proj_eq_one_iff (A := d.E) (x := Subgroup.inclusion d.N₂_le_normalizer_E n)).1 hn
    have h2 : (n : G) ∈ d.E ⊓ d.N₂ := ⟨h1, n.2⟩
    rw [sec38c_E_inf_N₂ hp, mem_bot] at h2
    exact Subtype.ext h2
  have hrange : bar d.E d.N₂ = φ.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Subgroup.inclusion d.N₂_le_normalizer_E n, n.2, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩

theorem sec38c_card_center_odd (hp : d.CaseHyp) :
    Odd (Nat.card (center ↥(bar d.E d.N₂))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := sec38c_barEquiv hp
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥(bar d.E d.N₂)) 2 h2
  have hzc : ∀ a : ↥(bar d.E d.N₂), a * (z : ↥(bar d.E d.N₂)) = (z : ↥(bar d.E d.N₂)) * a :=
    fun a => Subgroup.mem_center_iff.1 z.2 a
  have hn : e (z : ↥(bar d.E d.N₂)) ∈ center ↥d.N₂ := Subgroup.mem_center_iff.2 fun m => by
    apply e.symm.injective
    rw [map_mul, map_mul, e.symm_apply_apply]
    exact hzc _
  have hz2 : z ^ 2 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have hn2 : (e (z : ↥(bar d.E d.N₂))) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← map_pow, ← Subgroup.coe_pow, hz2]
    exact map_one e
  have h1 := sec38c_center_N₂ d _ hn 1 hn2
  have hz1 : (z : ↥(bar d.E d.N₂)) = 1 := e.injective (by rw [h1, map_one])
  have : orderOf z = 1 := by
    rw [orderOf_eq_one_iff]
    exact Subtype.ext hz1
  omega

theorem sec38c_centre_le (hp : d.CaseHyp) (hi : d.Sec38Input)
    (hnorm : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal) :
    (center ↥(bar d.E d.N₂)).map (bar d.E d.N₂).subtype ≤ OE d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := bar d.E d.N₂ with hA
  set θ := QuotientGroup.mk' (OE d) with hθ
  have hAq : CFSG.IsQuasisimple ↥A :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native A).1 hi.quasisimple
  have hZodd : Odd (Nat.card (center ↥A)) := sec38c_card_center_odd hp
  have hAO : (OE d).subgroupOf A ≤ center ↥A := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hAq
      (Subgroup.Normal.subgroupOf (GMSK.standardComponentOddCore_normal _) A) with htop | hle
    · exfalso
      have hAO' : A ≤ OE d := fun a ha => by
        have : (⟨a, ha⟩ : ↥A) ∈ (OE d).subgroupOf A := by rw [htop]; exact mem_top _
        exact this
      have hodd : Odd (Nat.card ↥A) :=
        (GMSK.odd_card_standardComponentOddCore _).of_dvd_nat (Subgroup.card_dvd_of_le hAO')
      obtain ⟨A4, -, h4⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
        (CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hAq hZodd)
      have h4' := Subgroup.card_subgroup_dvd_card A4
      rw [h4] at h4'
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((by norm_num : 2 ∣ 4).trans h4'))
    · exact hle
  obtain ⟨hperf, hsimple, hnonab⟩ := hAq
  have hbot : center (↥A ⧸ center ↥A) = ⊥ := by
    haveI := hsimple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥A ⧸ center ↥A)) with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnonab
      exact hxy (Subgroup.mem_center_iff.1 (h ▸ mem_top y) x)
  set At : Subgroup (Bar d.E ⧸ OE d) := A.map θ with hAt
  set Zt : Subgroup (Bar d.E ⧸ OE d) := At ⊓ centralizer (At : Set (Bar d.E ⧸ OE d)) with hZt
  have hZt_le : Zt ≤ ((center ↥A).map A.subtype).map θ := by
    rintro z ⟨⟨a, ha, rfl⟩, hzc⟩
    refine ⟨a, ⟨⟨a, ha⟩, ?_, rfl⟩, rfl⟩
    have hmk : (QuotientGroup.mk ⟨a, ha⟩ : ↥A ⧸ center ↥A) ∈ center (↥A ⧸ center ↥A) := by
      rw [Subgroup.mem_center_iff]
      intro b
      induction b using QuotientGroup.induction_on with | H b' =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      apply hAO
      rw [mem_subgroupOf]
      have hc := mem_centralizer_iff.1 hzc (θ b') (mem_map_of_mem θ b'.2)
      have : θ ((b' * ⟨a, ha⟩ : ↥A) : Bar d.E) = θ ((⟨a, ha⟩ * b' : ↥A) : Bar d.E) := by
        simp only [Subgroup.coe_mul, map_mul]
        exact hc
      exact QuotientGroup.eq.1 this
    rw [hbot, Subgroup.mem_bot] at hmk
    exact (QuotientGroup.eq_one_iff _).1 hmk
  haveI hZtn : Zt.Normal := ⟨fun n hn g => by
    obtain ⟨hnA, hnC⟩ := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨hnorm.conj_mem n hnA g, ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : g⁻¹ * w * g ∈ At := by simpa using hnorm.conj_mem w hw g⁻¹
    have hc := mem_centralizer_iff.1 hnC _ hw'
    calc w * (g * n * g⁻¹) = g * ((g⁻¹ * w * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * w * g)) * g⁻¹ := by rw [hc]
      _ = (g * n * g⁻¹) * w := by group⟩
  have hZtodd : Odd (Nat.card Zt) := by
    have h1 := Subgroup.card_dvd_of_le hZt_le
    have h2 := Subgroup.card_map_dvd (H := (center ↥A).map A.subtype) θ
    have h3 : Nat.card ((center ↥A).map A.subtype) = Nat.card (center ↥A) :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [h3] at h2
    exact hZodd.of_dvd_nat (h1.trans h2)
  have hZt_bot : Zt ≤ CFSG.Open.standardComponentOddCore (Bar d.E ⧸ OE d) :=
    le_sSup ⟨hZtn, hZtodd⟩
  rw [GMSK.standardComponentOddCore_quotient_eq_bot] at hZt_bot
  rintro _ ⟨⟨a, ha⟩, hac, rfl⟩
  have hθa : θ a ∈ Zt := by
    refine ⟨mem_map_of_mem θ ha, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hac ⟨b, hb⟩)
    simp only [Subgroup.coe_mul] at this
    rw [← map_mul, ← map_mul, this]
  have := hZt_bot hθa
  rw [Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff a).1 this

theorem sec38c_gms (hp : d.CaseHyp) (hi : d.Sec38Input)
    (hnorm : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal) :
    (∀ Q : Subgroup (Bar d.E), IsPGroup 2 Q →
      Set.InjOn (QuotientGroup.mk' (OE d)) (Q : Set (Bar d.E))) ∧
    orderOf (QuotientGroup.mk' (OE d) (proj d.E ⟨d.t, hi.t_mem⟩)) = 2 ∧
    ∀ S : Sylow 2 (centralizer (((bar d.E d.N₂).map (QuotientGroup.mk' (OE d)) :
      Subgroup (Bar d.E ⧸ OE d)) : Set (Bar d.E ⧸ OE d))), Nat.card S = 2 := by
  have hJa : bar d.E d.N₂ ≤ centralizer ({proj d.E ⟨d.t, hi.t_mem⟩} : Set (Bar d.E)) :=
    fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hi.centralizes x hx)
  have hsyl := GMSK.exists_sylow_inf_centralizer_eq_zpowers hi.order_two hi.centralizes hi.rank
  have key := GMSK.quasisimple_involution_centralizer_odd_normal_quotient_standardness
    hi.quasisimple hi.order_two hJa hi.normal hsyl (OE d)
    (GMSK.odd_card_standardComponentOddCore _) (sec38c_centre_le hp hi hnorm)
  obtain ⟨-, -, hinj, hord, -, -, -, -, -, -, -, -, hcard, -⟩ := key
  exact ⟨hinj, hord, hcard⟩

theorem sec38c_t_notMem_E (hi : d.Sec38Input) : d.t ∉ d.E := fun htE => by
  have h1 : proj d.E ⟨d.t, hi.t_mem⟩ = 1 := proj_eq_one_iff.2 htE
  have := hi.order_two
  rw [h1, orderOf_one] at this
  omega

theorem sec38c_family_conj (hp : d.CaseHyp) {y : G} (hyV : y ∈ normalizer (d.V : Set G))
    (hyM : y ∈ normalizer ((d.E ⊔ zpowers d.t : Subgroup G) : Set G)) {Y : Subgroup G}
    (hY : d.V ≤ Y ∧ Y ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V Y) :
    d.V ≤ Y.map (MulAut.conj y).toMonoidHom ∧
      Y.map (MulAut.conj y).toMonoidHom ≤ d.E ⊔ zpowers d.t ∧
      ElemAbMod d.V (Y.map (MulAut.conj y).toMonoidHom) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_conj_eq_of_mem_normalizer hyV]
    exact Subgroup.map_mono hY.1
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hyM x).1 (hY.2.1 hx)
  · have := hY.2.2.map_conj y
    rwa [map_conj_eq_of_mem_normalizer hyV] at this

theorem sec38c_normalizer_B₄ (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input) {y : G}
    (hyE : y ∈ normalizer (d.E : Set G))
    (hyM : y ∈ normalizer ((d.E ⊔ zpowers d.t : Subgroup G) : Set G)) :
    y ∈ normalizer (d.B₄ : Set G) := by
  have hyV : y ∈ normalizer (d.V : Set G) := by
    rw [← hp.hyp.centerIn_E hp.gms]
    exact Common.mem_normalizer_inf hyE (Prelim.normalizer_le_normalizer_centralizer d.E hyE)
  have hmax0 := (ha.maximal (d.V ⊔ d.B₂)).2 (Or.inr rfl)
  rw [hp.hyp.B₄_eq_V_sup_B₂]
  have hmax := hmax0
  have hmax' : Maximal (fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V Y)
      ((d.V ⊔ d.B₂).map (MulAut.conj y).toMonoidHom) := by
    refine ⟨sec38c_family_conj hp hyV hyM hmax0.1, fun Z hZ hle => ?_⟩
    have hZ' := sec38c_family_conj hp (y := y⁻¹) (inv_mem hyV) (inv_mem hyM) hZ
    have hle' := (sec38c_map_conj_le_iff y).1 hle
    have h2 := hmax0.2 hZ' hle'
    have h3 := (sec38c_map_conj_le_iff y⁻¹).1 h2
    rwa [inv_inv] at h3
  rcases (ha.maximal _).1 hmax' with h | h
  · exfalso
    have htB : d.t ∈ d.V ⊔ d.B₂ := mem_sup_right (mem_sup_left (mem_zpowers d.t))
    have h1 : y * d.t * y⁻¹ ∈ d.E := h ▸ ⟨d.t, htB, rfl⟩
    have h2 : d.t ∈ d.E := by
      have := (mem_normalizer_iff.1 (inv_mem hyE) _).1 h1
      rwa [show y⁻¹ * (y * d.t * y⁻¹) * y⁻¹⁻¹ = d.t by group] at this
    exact sec38c_t_notMem_E hi h2
  · exact Data.mem_normalizer_of_map_conj_eq h

theorem sec38c_partA (hp : d.CaseHyp) (ha : d.Sec38a)
    (h3 : ∀ y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G), y ∈ normalizer (d.V : Set G)) :
    ¬ IsSylowOf 2 (d.E ⊔ d.T) (normalizer (d.E : Set G)) := by
  intro hS
  obtain ⟨hM2, hnot⟩ := ha.notSylow
  obtain ⟨R, hMR⟩ := hM2.exists_le_sylow
  have hlt : Nat.card (d.E ⊔ d.T : Subgroup G) < Nat.card (R : Subgroup G) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hMR) fun heq => ?_
    apply hnot
    refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, heq, Sylow.card_eq_multiplicity]
  obtain ⟨y, hyN, hyM, hy2⟩ :=
    exists_mem_normalizer_not_mem_of_card_lt hM2 R.isPGroup' hlt
  have hyV := h3 y hyN
  have hyE : y ∈ normalizer (d.E : Set G) := by
    set E' := d.E.map (MulAut.conj y).toMonoidHom with hE'
    have hVE' : d.V ≤ E' := by
      rw [← map_conj_eq_of_mem_normalizer hyV]
      exact Subgroup.map_mono d.V_le_E
    have hE'M : E' ≤ d.E ⊔ d.T := by
      rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hyN x).1 (mem_sup_left hx)
    have hel : ElemAbMod d.V E' := by
      have := (hp.hyp.elemAbMod_V_E hp.gms).map_conj y
      rwa [map_conj_eq_of_mem_normalizer hyV] at this
    have hcard : Nat.card E' = (2 ^ f) ^ 14 := by
      rw [hE', Subgroup.card_map_of_injective (MulAut.conj y).injective, hp.hyp.card_E hp.gms]
    exact Data.mem_normalizer_of_map_conj_eq ((ha.jr E' hVE' hE'M hel).2 hcard)
  have hMN : d.E ⊔ d.T ≤ normalizer (d.E : Set G) :=
    sup_le le_normalizer (hp.hyp.T_le_normalizer_E hp.gms)
  have hle : d.E ⊔ d.T ⊔ zpowers y ≤ normalizer (d.E : Set G) :=
    sup_le hMN (zpowers_le.2 hyE)
  have := hS.eq_of_le le_sup_left hle hy2
  exact hyM (this ▸ mem_sup_right (mem_zpowers y))


theorem sec38c_X_le (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input)
    (hnorm : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal)
    {X : Subgroup G} (hXN : X ≤ normalizer (d.E : Set G)) (hX2 : IsPGroup 2 X)
    (hMX : d.E ⊔ d.T ≤ X) : X ≤ d.E ⊔ d.T := by
  have hd := hp.hyp
  obtain ⟨hinj, hord, hcard⟩ := sec38c_gms hp hi hnorm
  have htX : d.t ∈ X := hMX (mem_sup_right hd.t_mem_T)
  have hcomm : ∀ x ∈ X, (x * d.t)⁻¹ * (d.t * x) ∈ d.E := by
    intro x hx
    have h := sec38c_comm_of_normal (O := OE d) (A := bar d.E d.N₂) hnorm hinj hord hcard
      hi.centralizes (isPGroup_bar hX2) (proj_mem_bar (x := ⟨d.t, hi.t_mem⟩) htX)
      (proj_mem_bar (x := ⟨x, hXN hx⟩) hx)
    rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h
    exact h
  have hxM : ∀ x ∈ X, x ∈ normalizer ((d.E ⊔ zpowers d.t : Subgroup G) : Set G) := by
    intro x hx
    have he' := hcomm x⁻¹ (X.inv_mem hx)
    have hxt : x * d.t * x⁻¹ ∈ d.E ⊔ zpowers d.t := by
      rw [show x * d.t * x⁻¹ = d.t * ((x⁻¹ * d.t)⁻¹ * (d.t * x⁻¹)) by group]
      exact mul_mem (mem_sup_right (mem_zpowers d.t)) (mem_sup_left he')
    have hle : d.E ⊔ zpowers d.t ≤ (d.E ⊔ zpowers d.t).comap (MulAut.conj x).toMonoidHom :=
      sup_le (fun e he => mem_sup_left ((mem_normalizer_iff.1 (hXN hx) e).1 he))
        (zpowers_le.2 hxt)
    exact mem_normalizer_fintype fun s hs => hle hs
  intro x hx
  obtain ⟨e, he, c, hc, rfl⟩ := hd.exists_E_mul_of_mem_normalizer hp.gms
    (sec38c_normalizer_B₄ hp ha hi (hXN hx) (hxM x hx))
  have hEX : d.E ≤ X := le_sup_left.trans hMX
  have hTX : d.T ≤ X := le_sup_right.trans hMX
  have hcX : c ∈ X := by
    have := X.mul_mem (X.inv_mem (hEX he)) hx
    rwa [inv_mul_cancel_left] at this
  have hXC : X ⊓ centralizer ({d.t} : Set G) = d.T :=
    hd.T_syl.eq_of_le (le_inf hTX hd.T_le_centralizer) inf_le_right (hX2.to_le inf_le_left)
  have hcT : c ∈ d.T := hXC ▸ ⟨hcX, hc.2⟩
  exact mul_mem (mem_sup_left he) (mem_sup_right hcT)

theorem sec38c_partB (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input)
    (hnorm : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal) :
    IsSylowOf 2 (d.E ⊔ d.T) (normalizer (d.E : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 ↥(d.E ⊔ d.T) := ha.notSylow.1
  have hMN : d.E ⊔ d.T ≤ normalizer (d.E : Set G) :=
    sup_le le_normalizer (hp.hyp.T_le_normalizer_E hp.gms)
  obtain ⟨S, hS⟩ := (hM2.of_equiv (subgroupOfEquivOfLe hMN).symm).exists_le_sylow
  have hXS : IsSylowOf 2 ((S : Subgroup ↥(normalizer (d.E : Set G))).map
      (normalizer (d.E : Set G)).subtype) (normalizer (d.E : Set G)) := ⟨S, rfl⟩
  have hMX : d.E ⊔ d.T ≤ (S : Subgroup ↥(normalizer (d.E : Set G))).map
      (normalizer (d.E : Set G)).subtype := fun m hm =>
    ⟨⟨m, hMN hm⟩, hS (mem_subgroupOf.2 hm), rfl⟩
  have hXM := sec38c_X_le hp ha hi hnorm hXS.le hXS.isPGroup hMX
  have heq : (S : Subgroup ↥(normalizer (d.E : Set G))).map (normalizer (d.E : Set G)).subtype =
      d.E ⊔ d.T := le_antisymm hXM hMX
  rw [← heq]
  exact hXS

theorem sec38c_notNormal_of_h3 (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input)
    (h3 : ∀ y ∈ normalizer ((d.E ⊔ d.T : Subgroup G) : Set G), y ∈ normalizer (d.V : Set G)) :
    d.Sec38NotNormal := fun hnorm =>
  sec38c_partA hp ha h3 (sec38c_partB hp ha hi hnorm)

theorem sec38_notNormal (hp : d.CaseHyp) (ha : d.Sec38a) (hi : d.Sec38Input) :
    d.Sec38NotNormal :=
  sec38c_notNormal_of_h3 hp ha hi (sec38a3 hp)

end Data

namespace CaseBParts

theorem sec38NotNormal : Sec38NotNormalStatement :=
  fun _ _ _ _ _ _ _ _ hp ha hi => Data.sec38_notNormal hp ha hi

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5
