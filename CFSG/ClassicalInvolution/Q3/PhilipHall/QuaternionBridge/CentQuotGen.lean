module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotCongr

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace CentQ

theorem omega4_quot_gen (hΩ : HypOmegaGen Ω) (h62 : L6_2On Ω) (X : Subgroup G) [X.Normal]
    (hXc : X ≤ Subgroup.center G) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K J : Subgroup G}
    (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) :
    padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) = 1 →
        ⁅K.map (QuotientGroup.mk' X), J.map (QuotientGroup.mk' X)⁆ ≤
          oddCoreOf (K.map (QuotientGroup.mk' X)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' X))) := by
  by_cases heven : 2 ∣ Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))
  swap
  · rw [padicValNat.eq_zero_of_not_dvd heven]
    exact ⟨zero_le_one, fun h => absurd h (by norm_num)⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hz' := isUniqueInvolution_map_mk_of_odd (hXK K hK) hz
  have ht' := isUniqueInvolution_map_mk_of_odd (hXK J hJ) ht
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X))) 2 heven
  have haG : orderOf (a : G ⧸ X) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
  have hasq : (a : G ⧸ X) * (a : G ⧸ X) = 1 := by
    have := pow_orderOf_eq_one (a : G ⧸ X)
    rwa [haG, pow_two] at this
  have hane : (a : G ⧸ X) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at haG
    omega
  have haz : (a : G ⧸ X) = QuotientGroup.mk' X z :=
    (hz'.unique _ a.2.1 hasq).resolve_left hane
  have hat : (a : G ⧸ X) = QuotientGroup.mk' X t :=
    (ht'.unique _ a.2.2 hasq).resolve_left hane
  have hzt : t⁻¹ * z ∈ X := by
    have := hat.symm.trans haz
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  have hcomm : ⁅K, J⁆ ≤ oddCoreOf K ⊓ oddCoreOf J :=
    commutes_of_congr_gen hΩ h62 hXc hK hJ hKJ hz ht hzt
  have hKX : Commutes K X := fun k _ x hx => Subgroup.mem_center_iff.mp (hXc hx) k
  have hsub : ∀ b ∈ K.map (QuotientGroup.mk' X) ⊓ J.map (QuotientGroup.mk' X),
      IsPGroup 2 (Subgroup.zpowers b) → b = 1 ∨ b = QuotientGroup.mk' X z := by
    intro b hb hb2
    obtain ⟨hbK, ⟨j, hj, hjb⟩⟩ := Subgroup.mem_inf.mp hb
    have hb2' : IsPGroup 2 (Subgroup.zpowers (⟨b, hbK⟩ : ↥(K.map (QuotientGroup.mk' X)))) := by
      obtain ⟨n, hn⟩ := hb2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
      exact hn
    obtain ⟨k, hkb, hk2⟩ := exists_isPGroup_zpowers_lift (AscQuot.quotRestrict K X)
      (AscQuot.quotRestrict_surjective K X) hb2'
    have hkb' : QuotientGroup.mk' X (k : G) = b := congrArg Subtype.val hkb
    have hxX : (j⁻¹ * (k : G)) ∈ X := by
      have : QuotientGroup.mk' X j = QuotientGroup.mk' X (k : G) := hjb.trans hkb'.symm
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hkc : ∀ k' ∈ K, ⁅(k : G), k'⁆ ∈ oddCoreOf K := by
      intro k' hk'
      have h1 : ⁅j⁻¹ * (k : G), k'⁆ = 1 :=
        commutatorElement_eq_one_iff_mul_comm.mpr (hKX k' hk' _ hxX).symm
      have h2 : ⁅j, k'⁆ ∈ oddCoreOf K := by
        rw [← commutatorElement_inv]
        exact (oddCoreOf K).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hk' hj)).1
      have e : ⁅(k : G), k'⁆ = ⁅j, k'⁆ := by
        have e1 : (k : G) = j * (j⁻¹ * (k : G)) := by group
        rw [e1]
        simp only [commutatorElement_def] at h1 ⊢
        have : (j * (j⁻¹ * (k : G))) * k' * (j * (j⁻¹ * (k : G)))⁻¹ * k'⁻¹ =
            j * ((j⁻¹ * (k : G)) * k' * (j⁻¹ * (k : G))⁻¹ * k'⁻¹) * j⁻¹ *
              (j * k' * j⁻¹ * k'⁻¹) := by
          group
        rw [this, h1]
        group
      rw [e]
      exact h2
    have hk2' : IsPGroup 2 (Subgroup.zpowers (k : G)) := by
      obtain ⟨n, hn⟩ := hk2.exists_card_eq
      refine IsPGroup.of_card (n := n) ?_
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
      exact hn
    rcases Sec6Gen.center_two hΩ hK hz (k : G) k.2 hk2' hkc with h | h
    · left
      rw [← hkb', h, map_one]
    · right
      rw [← hkb', h]
  have hv2 : padicValNat 2 (Nat.card ↥(K.map (QuotientGroup.mk' X) ⊓
      J.map (QuotientGroup.mk' X))) ≤ 1 :=
    padicValNat_natCard_le_one_of_forall_isPGroup hsub
  refine ⟨hv2, fun _ => ?_⟩
  rw [← Subgroup.map_commutator]
  calc Subgroup.map (QuotientGroup.mk' X) ⁅K, J⁆
      ≤ Subgroup.map (QuotientGroup.mk' X) (oddCoreOf K ⊓ oddCoreOf J) := Subgroup.map_mono hcomm
    _ ≤ Subgroup.map (QuotientGroup.mk' X) (oddCoreOf K) ⊓
        Subgroup.map (QuotientGroup.mk' X) (oddCoreOf J) := Subgroup.map_inf_le _ _ _
    _ = oddCoreOf (K.map (QuotientGroup.mk' X)) ⊓ oddCoreOf (J.map (QuotientGroup.mk' X)) := by
      rw [oddCoreOf_map_mk_of_odd (hXK K hK), oddCoreOf_map_mk_of_odd (hXK J hJ)]

private theorem isSylowOf_of_isSylow2In {V P : Subgroup G} (h : IsSylow2In V P) :
    CFSG.ABGLocalTools.IsSylowOf 2 V P :=
  ⟨AscQuot.sylowOfIsSylow2In' h, by
    show (V.subgroupOf P).map P.subtype = V
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h.1]⟩

private theorem isSylow2In_of_isSylowOf {V P : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf 2 V P) : IsSylow2In V P :=
  ⟨h.le, h.isPGroup, fun _ hV'P hV'2 hle => h.eq_of_le hle hV'P hV'2⟩

theorem commutes_of_quot_gen (hΩ : HypOmegaGen Ω) (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω)
    (h611 : L6_11On Ω) (X : Subgroup G) [X.Normal] (hXc : X ≤ Subgroup.center G)
    {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hKJ : K ≠ J) {z : G}
    (hz : IsUniqueInvolution K z) {v : G} (hvJ : v ∈ J)
    (hvnc : ¬ ∀ w ∈ J, v * w = w * v) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hvz : QuotientGroup.mk' X v * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X v) :
    v * z = z * v := by
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have hcentral : ∀ w ∈ J, t * w = w * t := fun w hw => ht.commute_of_mem hw
  have hv3 : 3 ≤ orderOf v := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < orderOf v := orderOf_pos v
    have hv1 : v = 1 := by
      rcases (by omega : orderOf v = 1 ∨ orderOf v = 2) with h | h
      · exact orderOf_eq_one_iff.mp h
      · have hvv : v * v = 1 := by
          have := pow_orderOf_eq_one v
          rwa [h, pow_two] at this
        rcases ht.unique v hvJ hvv with h1 | h1
        · exact h1
        · exfalso
          apply hvnc
          intro w hw
          rw [h1]
          exact hcentral w hw
    apply hvnc
    intro w _
    rw [hv1, one_mul, mul_one]
  obtain ⟨Kk, hKk⟩ : ∃ Kk : ℤ → Subgroup G, ∀ k, Kk k = conjSub (v ^ k) K :=
    ⟨fun k => conjSub (v ^ k) K, fun _ => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = ⨆ k : ℤ, Kk k := ⟨_, rfl⟩
  have hKkΩ : ∀ k : ℤ, Kk k ∈ Ω := fun k => by
    rw [hKk]
    exact hΩ.conjInvariant _ K hK
  have hzk : ∀ k : ℤ, IsUniqueInvolution (Kk k) (v ^ k * z * (v ^ k)⁻¹) := fun k => by
    rw [hKk]
    exact hz.conj _
  have hcong : ∀ k : ℤ, QuotientGroup.mk' X (v ^ k * z * (v ^ k)⁻¹) = QuotientGroup.mk' X z := by
    intro k
    have hc : Commute (QuotientGroup.mk' X v) (QuotientGroup.mk' X z) := hvz
    have hck := (hc.zpow_left k).eq
    rw [map_mul, map_mul, map_inv, map_zpow, hck, mul_inv_cancel_right]
  have hKkN : ∀ k : ℤ, Kk k ≤ Subgroup.normalizer (K : Set G) := by
    intro k
    by_cases hk : Kk k = K
    · rw [hk]
      exact Subgroup.le_normalizer
    · have hzt : (v ^ k * z * (v ^ k)⁻¹)⁻¹ * z ∈ X := by
        have := hcong k
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
        exact this
      have hcomm : ⁅K, Kk k⁆ ≤ oddCoreOf K ⊓ oddCoreOf (Kk k) :=
        commutes_of_congr_gen hΩ h62 hXc hK (hKkΩ k) (Ne.symm hk) hz (hzk k) hzt
      exact le_normalizer_of_commutator_le_oddCoreOf
        (by rw [Subgroup.commutator_comm]; exact hcomm.trans inf_le_left)
  have hMN : M ≤ Subgroup.normalizer (K : Set G) := by
    rw [hM]
    exact iSup_le hKkN
  have hKM : K ≤ M := by
    have h0 : Kk 0 = K := by rw [hKk]; simp
    rw [hM]
    calc K = Kk 0 := h0.symm
      _ ≤ ⨆ k : ℤ, Kk k := le_iSup Kk 0
  have hvM : conjSub v M = M := by
    have h1 : conjSub v (⨆ k : ℤ, Kk k) = ⨆ k : ℤ, conjSub v (Kk k) := Subgroup.map_iSup _ _
    have h2 : ∀ k : ℤ, conjSub v (Kk k) = Kk (1 + k) := by
      intro k
      rw [hKk, hKk, ← conjSub_mul, zpow_one_add]
    rw [hM, h1]
    calc ⨆ k : ℤ, conjSub v (Kk k) = ⨆ k : ℤ, Kk (1 + k) := by simp only [h2]
      _ = ⨆ k : ℤ, Kk k := Equiv.iSup_comp (g := Kk) (Equiv.addLeft (1 : ℤ))
  have hvN : v ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_conjSub_eq.mpr hvM
  have hW : Subgroup.zpowers v ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.zpowers_le.mpr hvN
  obtain ⟨P, hP, hPfix⟩ := AscQuot.exists_sylow_normalized' hv2 hW
  have hvP : Subgroup.zpowers v ≤ Subgroup.normalizer (P : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hPfix w hw)
  have hQ2 : IsPGroup 2 ↥(Subgroup.zpowers v ⊔ P) :=
    IsPGroup.to_sup_of_normal_right' hv2 hP.2.1 hvP
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hQ2
  have hvS : v ∈ (S : Subgroup G) := hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers v))
  have hPS : P ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hRsyl' : IsSylow2In (P ⊓ K) K :=
    isSylow2In_of_isSylowOf (CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer
      (isSylowOf_of_isSylow2In hP) hKM hMN)
  obtain ⟨R, hRsyl, hRP⟩ : ∃ R : Subgroup G, IsSylow2In R K ∧ R ≤ P :=
    ⟨P ⊓ K, hRsyl', inf_le_left⟩
  have hRΩ : R ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRsyl
  have hRS : R ≤ (S : Subgroup G) := hRP.trans hPS
  have hR8 := Sec6Gen.eight_le_of_mem_RSet hΩ hRΩ
  have hzR : z ∈ R := AscQuot.mem_of_uniqueInvolution hz hRsyl.1 hRsyl.2.1 (by omega)
  obtain ⟨⟨η, hη, hηinv⟩, hab⟩ := h69 S
  obtain ⟨habel, -⟩ := hab η hη hηinv
  have hηG : η ∈ etaG Ω := ⟨S, hη, hηinv⟩
  have hηS : ∀ V ∈ η, V ≤ (S : Subgroup G) := fun V hV => (hη.1 hV).2
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = ⨆ V ∈ η, V := ⟨_, rfl⟩
  have hWS : W ≤ (S : Subgroup G) := by
    rw [hWdef]
    exact iSup₂_le fun V hV => hηS V hV
  have hKS : 2 < Nat.card ↥(K ⊓ (S : Subgroup G)) := by
    have := Subgroup.card_le_of_le (le_inf hRsyl.1 hRS)
    omega
  have hJS : 2 < Nat.card ↥(J ⊓ (S : Subgroup G)) := by
    have h1 : Subgroup.zpowers v ≤ J ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hvJ) (Subgroup.zpowers_le.mpr hvS)
    have h2 := Subgroup.card_le_of_le h1
    rw [Nat.card_zpowers] at h2
    omega
  have hUKη : K ⊓ W ∈ η := by
    rw [hWdef]
    exact h611 S η hηG hηS K hK hKS
  have hUJη : J ⊓ W ∈ η := by
    rw [hWdef]
    exact h611 S η hηG hηS J hJ hJS
  obtain ⟨-, -, -, -, -, -, -, -, hUK4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ (hη.1 hUKη).1
  have hUK2 : IsPGroup 2 ↥(K ⊓ W) := (S.isPGroup'.to_le hWS).to_inf_right
  have hzW : z ∈ W := (AscQuot.mem_of_uniqueInvolution hz inf_le_left hUK2 (by omega)).2
  obtain ⟨R', -, J', hJ', hR'J', hUJR', -, hR'card, hUJ4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ (hη.1 hUJη).1
  have hJJ' : J' = J :=
    Sec6Gen.eq_of_mem_USet hΩ (hη.1 hUJη).1 hJ' hJ (hUJR'.trans hR'J'.1) inf_le_left
  rw [hJJ'] at hR'J'
  have hTS : (J ⊓ W) ⊔ Subgroup.zpowers v ≤ (S : Subgroup G) :=
    sup_le (inf_le_right.trans hWS) (Subgroup.zpowers_le.mpr hvS)
  have hT2 : IsPGroup 2 ↥((J ⊓ W) ⊔ Subgroup.zpowers v) := S.isPGroup'.to_le hTS
  have hTJ : (J ⊓ W) ⊔ Subgroup.zpowers v ≤ J :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hvJ)
  obtain ⟨V₁, hV₁, hTV₁⟩ := IsSylow2In.exists_ge hT2 hTJ
  have hV₁card : Nat.card V₁ = 2 * Nat.card ↥(J ⊓ W) := by
    rw [← hR'card, hV₁.natCard_eq hR'J']
  have hvT : v ∈ (J ⊓ W) ⊔ Subgroup.zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  rcases eq_or_eq_of_natCard_eq_two_mul le_sup_left hTV₁ hV₁card with hT | hT
  · have hvW : v ∈ W := by
      rw [hT] at hvT
      exact hvT.2
    exact habel v (hWdef ▸ hvW) z (hWdef ▸ hzW)
  · have hV₁S : V₁ ≤ (S : Subgroup G) := hT ▸ hTS
    have hV₁Ω : V₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hJ hV₁
    have hne : R ≠ V₁ := by
      intro h
      have h2 := Sec6Gen.card_le_two_of_le_inf hΩ hK hJ hKJ hRsyl.2.1 hRsyl.1
        ((le_of_eq h).trans hV₁.1)
      omega
    have hcomm := h67 S R hRΩ V₁ hV₁Ω hRS hV₁S hne
    rw [hT] at hvT
    exact (hcomm z hzR v hvT).symm

theorem omega5_quot_gen (hΩ : HypOmegaGen Ω) (h67 : L6_7On Ω) (h62 : L6_2On Ω) (h69 : L6_9On Ω)
    (h611 : L6_11On Ω) (X : Subgroup G) [X.Normal] (hXc : X ≤ Subgroup.center G)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    ∀ L ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω,
      ∀ L' ∈ Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω, L ≠ L' →
        ∀ z : G ⧸ X, IsUniqueInvolution L z → ∀ v ∈ L',
          (¬ ∀ w ∈ L', v * w = w * v) → IsPGroup 2 (Subgroup.zpowers v) → v * z = z * v →
            v ∈ Subgroup.normalizer (L : Set (G ⧸ X)) := by
  rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne z' hz' _ ⟨v₀, hv₀J, rfl⟩ hvnc hv2 hcomm
  have hKJ : K ≠ J := fun h => hne (by rw [h])
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hz'eq : z' = QuotientGroup.mk' X z :=
    hz'.eq (isUniqueInvolution_map_mk_of_odd (hXK K hK) hz)
  have hv2a : IsPGroup 2 (Subgroup.zpowers
      (⟨QuotientGroup.mk' X v₀, Subgroup.mem_map_of_mem _ hv₀J⟩ :
        ↥(J.map (QuotientGroup.mk' X)))) := by
    obtain ⟨n, hn⟩ := hv2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Nat.card_zpowers]
    exact hn
  obtain ⟨v, hvb, hv2b⟩ := exists_isPGroup_zpowers_lift (AscQuot.quotRestrict J X)
    (AscQuot.quotRestrict_surjective J X) hv2a
  have hvc : QuotientGroup.mk' X (v : G) = QuotientGroup.mk' X v₀ := congrArg Subtype.val hvb
  have hv2c : IsPGroup 2 (Subgroup.zpowers (v : G)) := by
    obtain ⟨n, hn⟩ := hv2b.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ← Nat.card_zpowers]
    exact hn
  have hvnc' : ¬ ∀ w ∈ J, (v : G) * w = w * v := fun h => hvnc (by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hvc, ← map_mul, ← map_mul, h w hw])
  have hvz : QuotientGroup.mk' X (v : G) * QuotientGroup.mk' X z =
      QuotientGroup.mk' X z * QuotientGroup.mk' X (v : G) := by
    rw [hvc]
    exact hz'eq ▸ hcomm
  have hvz' : (v : G) * z = z * v :=
    commutes_of_quot_gen hΩ h67 h62 h69 h611 X hXc hK hJ hKJ hz v.2 hvnc' hv2c hvz
  have hvK : (v : G) ∈ Subgroup.normalizer (K : Set G) :=
    hΩ.omega5 K hK J hJ hKJ z hz v v.2 hvnc' hv2c hvz'
  rw [← hvc, mem_normalizer_iff_conjSub_eq, ← AscQuot.map_conjSub,
    mem_normalizer_iff_conjSub_eq.mp hvK]

theorem omega1_quot_gen (hΩ : HypOmegaGen Ω) (X : Subgroup G) [X.Normal]
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K : Subgroup G} (hK : K ∈ Ω) :
    (∃ z : G ⧸ X, IsUniqueInvolution (K.map (QuotientGroup.mk' X)) z) ∧
      ∃ P : Subgroup (G ⧸ X), IsSylow2In P (K.map (QuotientGroup.mk' X)) ∧
        ¬ IsMulCommutative ↥P := by
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨-, P, hP, hPnc⟩ := hΩ.omega1 K hK
  refine ⟨⟨QuotientGroup.mk' X z, isUniqueInvolution_map_mk_of_odd (hXK K hK) hz⟩,
    P.map (QuotientGroup.mk' X), Hall196.isSylow2In_map_hom (QuotientGroup.mk' X) hP,
    fun hc => hPnc ?_⟩
  have hPX : P ⊓ X = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd X hP.2.1 hP.1 (hXK K hK)
  exact ⟨⟨fun a b => AscQuot.quotRestrict_injective hPX
    (by rw [map_mul, map_mul]; exact hc.is_comm.comm _ _)⟩⟩

theorem omega2_quot_gen (hΩ : HypOmegaGen Ω) (X : Subgroup G) [X.Normal]
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K : Subgroup G} (hK : K ∈ Ω) :
    Subgroup.closure {x : G ⧸ X | x ∈ K.map (QuotientGroup.mk' X) ∧
        IsPGroup 2 (Subgroup.zpowers x)} = K.map (QuotientGroup.mk' X) ∨
      Nonempty (↥(K.map (QuotientGroup.mk' X)) ⧸
        classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' X)) ≃* SL(2, ZMod 3)) := by
  rcases hΩ.omega2 K hK with h | he
  · left
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
    calc K.map (QuotientGroup.mk' X)
        = (Subgroup.closure {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)}).map
            (QuotientGroup.mk' X) := by rw [h]
      _ = Subgroup.closure ((QuotientGroup.mk' X) ''
            {x : G | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)}) := MonoidHom.map_closure _ _
      _ ≤ _ := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨x, ⟨hxK, hx2⟩, rfl⟩
        exact ⟨Subgroup.mem_map_of_mem _ hxK, by rw [← MonoidHom.map_zpowers]; exact hx2.map _⟩
  · right
    obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := AscQuot.nonempty_quotOddCoreEquiv (hXK K hK)
    exact ⟨e'.symm.trans e⟩

theorem omega3_quot_gen (hΩ : HypOmegaGen Ω) (X : Subgroup G) [X.Normal]
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    {P Q : Subgroup (G ⧸ X)} (hP : IsSylow2In P (K.map (QuotientGroup.mk' X)))
    (hQ : IsSylow2In Q (J.map (QuotientGroup.mk' X))) : Nat.card ↥P = Nat.card ↥Q := by
  obtain ⟨P₀, hP₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := K) IsPGroup.of_bot bot_le
  obtain ⟨Q₀, hQ₀, -⟩ := IsSylow2In.exists_ge (T := ⊥) (P := J) IsPGroup.of_bot bot_le
  have hP₀X : P₀ ⊓ X = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd X hP₀.2.1 hP₀.1 (hXK K hK)
  have hQ₀X : Q₀ ⊓ X = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd X hQ₀.2.1 hQ₀.1 (hXK J hJ)
  have h1 : Nat.card ↥P = Nat.card ↥P₀ := by
    rw [hP.natCard_eq (Hall196.isSylow2In_map_hom (QuotientGroup.mk' X) hP₀)]
    exact (Nat.card_congr (AscQuot.quotRestrictEquiv hP₀X).toEquiv).symm
  have h2 : Nat.card ↥Q = Nat.card ↥Q₀ := by
    rw [hQ.natCard_eq (Hall196.isSylow2In_map_hom (QuotientGroup.mk' X) hQ₀)]
    exact (Nat.card_congr (AscQuot.quotRestrictEquiv hQ₀X).toEquiv).symm
  rw [h1, h2]
  exact hΩ.omega3 K hK J hJ P₀ Q₀ hP₀ hQ₀

theorem quotient_hypOmegaGen (hΩ : HypOmegaGen Ω) (X : Subgroup G) [X.Normal]
    (hXc : X ≤ Subgroup.center G) (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(X ⊓ K))) :
    HypOmegaGen (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' X)) Ω) := by
  have h62 : L6_2On Ω := Sec6Gen.l6_2Gen G Ω hΩ
  have h67 : L6_7On Ω := Q3CP.l67Gen G Ω hΩ
  have h69 : L6_9On Ω := Q3T8.Asc77.l6_9_proved G Ω hΩ
  have h611 : L6_11On Ω := Sec6Gen.l6_11Gen G Ω hΩ
  refine
    { conjInvariant := AscQuot.conjInvariant_quot hΩ.conjInvariant X
      omega1 := ?_
      omega2 := ?_
      omega3 := ?_
      omega4 := ?_
      omega5 := omega5_quot_gen hΩ h67 h62 h69 h611 X hXc hXK }
  · rintro _ ⟨K, hK, rfl⟩
    exact omega1_quot_gen hΩ X hXK hK
  · rintro _ ⟨K, hK, rfl⟩
    exact omega2_quot_gen hΩ X hXK hK
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ P Q hP hQ
    exact omega3_quot_gen hΩ X hXK hK hJ hP hQ
  · rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ hne
    exact omega4_quot_gen hΩ h62 X hXc hXK hK hJ (fun h => hne (by rw [h]))

end CentQ

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
