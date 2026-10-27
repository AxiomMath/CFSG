module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Aux
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Shape
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_23

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section CaseA

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.outSetting (h : Lv2520 N t zK) (hfam : OutFamily N.K N.H) :
    OutSetting N.K N.H N.S where
  K_le_H := N.K_le_H
  H_le_normalizer := h.hKH
  simple := h.facts258.simple
  sylow := N.tuple.sylow
  join := N.join
  fam := hfam

theorem Lv2520.card_S_le (h : Lv2520 N t zK)
    (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥(N.S ⊓ N.K) *
      Nat.card ↥(N.S ⊓ Subgroup.centralizer (N.K : Set G)))) :
    Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC) := by
  have h1 : N.SC = N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
    unfold Notation25.SC
    rw [h.concl2520]
  rw [h1]
  exact hidx

theorem Lv2520.exists_four_SK (h : Lv2520 N t zK) :
    ∃ E : Subgroup G, E ≤ N.SK ∧ IsFourSubgroup E := by
  obtain ⟨U, HU, hpair, hUS⟩ := N.exists_ustar_pair_le_S
  obtain ⟨E, hE, hE4, -⟩ := ((h.concl2512 h.hKH).1 U HU hpair hUS).1
  exact ⟨E, hE, hE4⟩

theorem Lv2520.hK0 (h : Lv2520 N t zK) : N.K0 = N.K := h.concl2520

theorem Lv2520.zK_ne_one (h : Lv2520 N t zK) : zK ≠ 1 := by
  intro h1
  have := h.facts2511.zK_proj
  rw [h1, inv_one, one_mul] at this
  exact h.facts254.z_not_mem this

theorem Lv2520.K_inf_SC_eq_bot_mem (h : Lv2520 N t zK) {a : G} (haK : a ∈ N.K) (haC : a ∈ N.SC) :
    a = 1 := by
  have : a ∈ N.K ⊓ N.SC := ⟨haK, haC⟩
  rw [h.K_inf_SC, Subgroup.mem_bot] at this
  exact this

theorem Lv2520.zK_not_mem_SC (h : Lv2520 N t zK) : zK ∉ N.SC := fun hc =>
  h.zK_ne_one (h.K_inf_SC_eq_bot_mem (h.hK0 ▸ h.facts2511.zK_mem) hc)

theorem Lv2520.not_SK_le_Rt (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)}
    (hR : DS.DSData R) : ¬ N.SK ≤ (h.sBar hR).Rt := by
  obtain ⟨E, hE, hE4⟩ := h.exists_four_SK
  have hSB := h.sBar hR
  have hES : E ≤ N.S := hE.trans N.SK_le_S
  have hEA : E ⊓ N.SC = ⊥ := by
    refine le_bot_iff.mp ?_
    calc E ⊓ N.SC ≤ N.K ⊓ N.SC := inf_le_inf_right _ (hE.trans N.SK_le_K)
      _ = ⊥ := h.K_inf_SC
  obtain ⟨g, hgE, hgR⟩ := hR.exists_not_mem_four (hSB.isFour_img hES hEA hE4)
  obtain ⟨e, heE, heS, rfl⟩ := hSB.mem_img.mp hgE
  intro hle
  have := hle (hE heE)
  rw [hSB.mem_Rt] at this
  exact hgR this.2

theorem Lv2520.SK_inf_SC (h : Lv2520 N t zK) : N.SK ⊓ N.SC = ⊥ := by
  refine le_bot_iff.mp ?_
  calc N.SK ⊓ N.SC ≤ N.K ⊓ N.SC := inf_le_inf_right _ N.SK_le_K
    _ = ⊥ := h.K_inf_SC

theorem Lv2520.caseA_zK_fixed (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)}
    (hR : DS.DSData R) (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hA2 : Nat.card ↥N.SC = 2) : N.x⁻¹ * zK * N.x = zK := by
  have hSB := h.sBar hR
  have h258 := h.facts258
  have hf := h.facts2511
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hcomm : ⁅N.S, N.S⁆ ≤ N.SK := by
    refine DS.commutator_le_of_card_le N.SK_le_S (fun s hs q hq => h.SK_normal_in_S hs hq) hS2 ?_
    rw [hA2] at hidx
    omega
  have hzKS : zK ∈ N.S := hf.zK_mem_center.1
  have hzKSK : zK ∈ N.SK := hf.zK_mem_SK h.hK0
  have hQA : N.SK ⊓ N.SC = ⊥ := h.SK_inf_SC
  obtain ⟨ρ, hρQ, hρR, hρ⟩ := hSB.exists_sq_ne_one N.SK_le_S hQA h258.eight_le_card_SK
  obtain ⟨w, hwc, hwz⟩ := hSB.exists_mem_commutator N.SK_le_S hQA (h.not_SK_le_Rt hR) hρQ hρR hρ
  have hπz : actS N.K N.S h.S_le_normalizer zK = hSB.ds.z :=
    hSB.pi_eq_z hzKS (fun s hs => (Subgroup.mem_centralizer_iff.mp hf.zK_mem_center.2 s hs).symm)
      (by rw [hf.zK_sq]; exact N.SC.one_mem) h.zK_not_mem_SC
  have hcl : ⁅N.SK, N.SK⁆ ≤ N.SK := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact N.SK.mul_mem (N.SK.mul_mem (N.SK.mul_mem ha hb) (N.SK.inv_mem ha)) (N.SK.inv_mem hb)
  have hwSK : w ∈ N.SK := hcl hwc
  have hwS : w ∈ N.S := N.SK_le_S hwSK
  have hzKw : zK = w := by
    have hmem : w⁻¹ * zK ∈ N.SC := (hSB.pi_eq_iff hwS hzKS).mp (hwz.trans hπz.symm)
    have hK : w⁻¹ * zK ∈ N.K :=
      N.K.mul_mem (N.K.inv_mem (N.SK_le_K hwSK)) (h.hK0 ▸ hf.zK_mem)
    have := h.K_inf_SC_eq_bot_mem hK hmem
    exact (inv_mul_eq_one.mp this).symm
  have hzKc : zK ∈ ⁅N.SK, N.SK⁆ := hzKw ▸ hwc
  have hzKSS : zK ∈ ⁅N.S, N.S⁆ := Subgroup.commutator_mono N.SK_le_S N.SK_le_S hzKc
  have hconj : N.x⁻¹ * zK * N.x ∈ ⁅N.S, N.S⁆ := inv_conj_mem_commutator N.x_mem.2 hzKSS
  have hSK : N.x⁻¹ * zK * N.x ∈ N.SK := hcomm hconj
  have hZ : N.x⁻¹ * zK * N.x ∈ centerOf N.S := inv_conj_mem_centerOf N.x_mem.2 hf.zK_mem_center
  have hmem : N.x⁻¹ * zK * N.x ∈ Subgroup.zpowers zK := by
    rw [← Notation25.center_inf_SK_eq h.hK0 h258 hf]
    exact ⟨hZ, hSK⟩
  rcases mem_zpowers_involution hf.zK_sq hmem with h1 | h1
  · exfalso
    apply h.zK_ne_one
    calc zK = N.x * (N.x⁻¹ * zK * N.x) * N.x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · exact h1

theorem Lv2520.pi_zK (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)} (hR : DS.DSData R) :
    actS N.K N.S h.S_le_normalizer zK = (h.sBar hR).ds.z :=
  (h.sBar hR).pi_eq_z h.facts2511.zK_mem_center.1
    (fun s hs => (Subgroup.mem_centralizer_iff.mp h.facts2511.zK_mem_center.2 s hs).symm)
    (by rw [h.facts2511.zK_sq]; exact N.SC.one_mem) h.zK_not_mem_SC

theorem Lv2520.zK_mem_four (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)} (hR : DS.DSData R)
    {E : Subgroup G} (hE : E ≤ N.SK) (hE4 : IsFourSubgroup E) : zK ∈ E := by
  have hSB := h.sBar hR
  have hES : E ≤ N.S := hE.trans N.SK_le_S
  have hEA : E ⊓ N.SC = ⊥ := le_bot_iff.mp (h.SK_inf_SC ▸ inf_le_inf_right _ hE)
  have hz := hR.z_mem_four (hSB.isFour_img hES hEA hE4)
  obtain ⟨e, heE, heS, hez⟩ := hSB.mem_img.mp hz
  have hzK := h.pi_zK hR
  have hzKS : zK ∈ N.S := h.facts2511.zK_mem_center.1
  have h1 : e⁻¹ * zK ∈ N.SC := (hSB.pi_eq_iff heS hzKS).mp (hez.trans hzK.symm)
  have hK : e⁻¹ * zK ∈ N.K :=
    N.K.mul_mem (N.K.inv_mem (N.SK_le_K (hE heE))) (h.hK0 ▸ h.facts2511.zK_mem)
  have := h.K_inf_SC_eq_bot_mem hK h1
  rw [(inv_mul_eq_one.mp this).symm]
  exact heE

theorem Lv2520.H_le_normalizer_SC (h : Lv2520 N t zK) :
    N.H ≤ Subgroup.normalizer (N.SC : Set G) := by
  rw [h.facts254.SC_eq]
  exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N.H

structure CaseAData (N : Notation25 hs) (zK : G) (E : Subgroup G) : Prop where
  le_SK : E ≤ N.SK
  four : IsFourSubgroup E
  zK_mem : zK ∈ E
  sylow : IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G))
    (Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G))

theorem Lv2520.exists_caseAData (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)}
    (hR : DS.DSData R) (hz : N.z = zK) : ∃ E : Subgroup G, CaseAData N zK E := by
  obtain ⟨U, HU, hpair, hUS⟩ := N.exists_ustar_pair_le_S
  have h2512 := (h.concl2512 h.hKH).1 U HU hpair hUS
  obtain ⟨E, hE, hE4, hHU, hU, -⟩ := h2512.1
  have hzE := h.zK_mem_four hR hE hE4
  refine ⟨E, hE, hE4, hzE, ?_⟩
  have hES : E ≤ N.S := hE.trans N.SK_le_S
  have hEK : E ≤ N.K := hE.trans N.SK_le_K
  have hQ2 : IsPGroup 2 ↥(E ⊔ N.SC) :=
    N.tuple.sylow.isPGroup.to_le (sup_le hES N.SC_le_S)
  have hcomm : ∀ a ∈ N.SC, ∀ n ∈ E, a * n * a⁻¹ = n := by
    intro a ha n hn
    have := h.SC_commutes ha n (hEK hn)
    calc a * n * a⁻¹ = n * a * a⁻¹ := by rw [this]
      _ = n := by group
  have hSCnorm : N.SC ≤ Subgroup.normalizer (E : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [hcomm a ha n hn]
      exact hn
    · intro hn
      have h1 := hcomm a⁻¹ (N.SC.inv_mem ha) _ hn
      have h2 : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
      rw [h2] at h1
      have h3 : a * n * a⁻¹ = n := h1.symm
      rw [h3] at hn
      exact hn
  have hQHU : E ⊔ N.SC ≤ HU := by
    rw [hHU]
    exact le_inf (sup_le (hEK.trans N.K_le_H) (N.SC_le_S.trans N.S_le_H))
      (sup_le Subgroup.le_normalizer hSCnorm)
  have hHUN : HU ≤ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) := by
    rw [hHU]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup E N.SC ⟨hx.2, h.H_le_normalizer_SC hx.1⟩
  have hzQ : N.z ∈ E ⊔ N.SC := hz ▸ Subgroup.mem_sup_left hzE
  have := (h2512.2 (E ⊔ N.SC) hQ2 hzQ hQHU hHUN).2
  rw [hU] at this
  exact this

omit [Finite G] in
theorem IsSylowTwoOf.le_of_le [Finite G] {U X V : Subgroup G} (hU : IsSylowTwoOf U X)
    (hVX : V ≤ X) (hV : IsPGroup 2 ↥V) (hUV : U ≤ V) : V ≤ U := by
  have h1 : U.relIndex V * V.relIndex X = U.relIndex X :=
    Subgroup.relIndex_mul_relIndex U V X hUV hVX
  have h2 : U.relIndex X = (U.subgroupOf X).index := rfl
  have h3 : ¬ 2 ∣ U.relIndex X := hU.2.2
  obtain ⟨n, hn⟩ := hV.index (U.subgroupOf V)
  have h4 : U.relIndex V = 2 ^ n := hn
  by_contra hne
  have h5 : U.relIndex V ≠ 1 := fun h6 => hne (Subgroup.relIndex_eq_one.mp h6)
  have h6 : n ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at h4
    exact h5 h4
  apply h3
  rw [← h1, h4]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 h6) _

theorem CaseAData.normalizer_T_le {E : Subgroup G} (hd : CaseAData N zK E) :
    T ⊓ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) ≤ N.S := by
  have hU := hd.sylow
  have hUT : N.S ⊓ Subgroup.normalizer (E : Set G) ≤
      T ⊓ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) :=
    le_inf (inf_le_left.trans N.S_le_T) hU.1
  have hV2 : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G)) :=
    hs.setting.isPGroup.to_le inf_le_left
  exact (hU.le_of_le inf_le_right hV2 hUT).trans inf_le_left

theorem CaseAData.conjugate_x_ne {E : Subgroup G} (hd : CaseAData N zK E) {s : G} (hs' : s ∈ N.S) :
    CFSG.conjugate (E ⊔ N.SC) N.x ≠ CFSG.conjugate (E ⊔ N.SC) s := by
  intro hconj
  have hyN : N.x * s⁻¹ ∈ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) := by
    apply BenderBranch.conjugate_eq_iff_mem_normalizer.mp
    have h1 : CFSG.conjugate (E ⊔ N.SC) (N.x * s⁻¹) =
        CFSG.conjugate (CFSG.conjugate (E ⊔ N.SC) N.x) s⁻¹ :=
      (BenderBranch.conjugate_conjugate _ _ _).symm
    rw [h1, hconj, BenderBranch.conjugate_conjugate, mul_inv_cancel, BenderBranch.conjugate_one]
  have hy : N.x * s⁻¹ ∈ T ⊓ Subgroup.normalizer ((E ⊔ N.SC : Subgroup G) : Set G) :=
    ⟨T.mul_mem N.x_mem.1 (T.inv_mem (N.S_le_T hs')), hyN⟩
  have hyS := hd.normalizer_T_le hy
  apply N.x_not_mem
  have : N.x = (N.x * s⁻¹) * s := by group
  rw [this]
  exact N.S.mul_mem hyS hs'

end CaseA

section Generic

variable {G : Type} [Group G]

theorem card_le_two_mul_of_cosets [Finite G] {X Y : Subgroup G} (hYX : Y ≤ X) {f₀ : G}
    (hf₀ : f₀ ∈ X) (h : ∀ w ∈ X, w ∈ Y ∨ w * f₀⁻¹ ∈ Y) : Nat.card X ≤ 2 * Nat.card Y := by
  have hsurj : Function.Surjective (fun p : Y ⊕ Y => (Sum.elim
      (fun y : Y => (⟨(y : G), hYX y.2⟩ : X))
      (fun y : Y => (⟨(y : G) * f₀, X.mul_mem (hYX y.2) hf₀⟩ : X)) p)) := by
    intro w
    rcases h w w.2 with h1 | h1
    · exact ⟨Sum.inl ⟨w, h1⟩, rfl⟩
    · refine ⟨Sum.inr ⟨w * f₀⁻¹, h1⟩, ?_⟩
      apply Subtype.ext
      simp
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_sum] at this
  omega

theorem isElemAbelian_of_forall {E : Subgroup G} (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hsq : ∀ x ∈ E, x * x = 1) : IsElemAbelian 2 E :=
  ⟨IsMulCommutative.mk (Std.Commutative.mk fun a b => Subtype.ext (hcomm a a.2 b b.2)),
    fun x hx => by rw [pow_two]; exact hsq x hx⟩

theorem elemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

theorem elemAbelian_sq {E : Subgroup G} (hE : IsElemAbelian 2 E) {a : G} (ha : a ∈ E) :
    a * a = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hE ha

theorem isElemAbelian_conjugate {E : Subgroup G} (hE : IsElemAbelian 2 E) (g : G) :
    IsElemAbelian 2 (CFSG.conjugate E g) := by
  refine isElemAbelian_of_forall (fun a ha b hb => ?_) (fun a ha => ?_)
  · rw [BenderBranch.mem_conjugate_iff] at ha hb
    have := elemAbelian_comm hE ha hb
    have h2 : (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := this
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h2]
      _ = b * a := by group
  · rw [BenderBranch.mem_conjugate_iff] at ha
    have := elemAbelian_sq hE ha
    calc a * a = g⁻¹ * ((g * a * g⁻¹) * (g * a * g⁻¹)) * g := by group
      _ = 1 := by rw [this]; group

end Generic

section CaseA2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

structure CaseAParams (N : Notation25 hs) (t zK : G) (R : Subgroup ↥(autOn N.S N.K)) : Prop where
  ds : DS.DSData R
  idx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC)
  SC_eq : N.SC = Subgroup.zpowers t
  hz : N.z = zK
  hfix : N.x⁻¹ * zK * N.x = zK
  htx : N.x⁻¹ * t * N.x = t * zK

theorem Lv2520.caseAParams (h : Lv2520 N t zK) {R : Subgroup ↥(autOn N.S N.K)}
    (hR : DS.DSData R) (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hA2 : Nat.card ↥N.SC = 2) : CaseAParams N t zK R := by
  have hf := h.facts2511
  have hfix := h.caseA_zK_fixed hR hidx hA2
  obtain ⟨hz, htx⟩ := h.concl2513.2.1 hfix
  refine ⟨hR, hidx, ?_, hz, hfix, htx⟩
  have hle : Subgroup.zpowers t ≤ N.SC := Subgroup.zpowers_le.mpr hf.t_mem
  have hcard : Nat.card (Subgroup.zpowers t) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hf.t_sq hf.t_ne_one
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hA2, hcard])).symm

theorem CaseAParams.F_elemAbelian {R : Subgroup ↥(autOn N.S N.K)} (hp : CaseAParams N t zK R)
    (h : Lv2520 N t zK) {E : Subgroup G} (hd : CaseAData N zK E) :
    IsElemAbelian 2 (E ⊔ N.SC) := by
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hcomm : ∀ e ∈ E, ∀ a ∈ N.SC, e * a = a * e := fun e he a ha =>
    (h.SC_commutes ha e (hEK he)).symm
  have ht2 : t * t = 1 := h.facts2511.t_mul_t
  have hSCinv : ∀ a ∈ N.SC, a = 1 ∨ a = t := fun a ha => by
    rw [hp.SC_eq] at ha
    exact mem_zpowers_involution ht2 ha
  have hSCcomm : ∀ a ∈ N.SC, ∀ a' ∈ N.SC, a * a' = a' * a := by
    intro a ha a' ha'
    rcases hSCinv a ha with rfl | rfl <;> rcases hSCinv a' ha' with rfl | rfl <;> simp
  have hSCsq : ∀ a ∈ N.SC, a * a = 1 := by
    intro a ha
    rcases hSCinv a ha with rfl | rfl
    · simp
    · exact ht2
  refine isElemAbelian_of_forall ?_ ?_
  · intro f hf f' hf'
    obtain ⟨e, he, a, ha, rfl⟩ := mem_sup_of_commute hcomm hf
    obtain ⟨e', he', a', ha', rfl⟩ := mem_sup_of_commute hcomm hf'
    have hee' : e * e' = e' * e := hd.four.comm he he'
    have haa' : a * a' = a' * a := hSCcomm a ha a' ha'
    have hae' : a * e' = e' * a := (hcomm e' he' a ha).symm
    have hea' : e * a' = a' * e := hcomm e he a' ha'
    calc e * a * (e' * a') = e * (a * e') * a' := by group
      _ = e * (e' * a) * a' := by rw [hae']
      _ = (e * e') * (a * a') := by group
      _ = (e' * e) * (a' * a) := by rw [hee', haa']
      _ = e' * (e * a') * a := by group
      _ = e' * (a' * e) * a := by rw [hea']
      _ = e' * a' * (e * a) := by group
  · intro f hf
    obtain ⟨e, he, a, ha, rfl⟩ := mem_sup_of_commute hcomm hf
    have hae : a * e = e * a := (hcomm e he a ha).symm
    calc e * a * (e * a) = e * (a * e) * a := by group
      _ = e * (e * a) * a := by rw [hae]
      _ = (e * e) * (a * a) := by group
      _ = 1 := by rw [hd.four.sq he, hSCsq a ha]; group

theorem Lv2520.caseA_conj_le_false {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) {E : Subgroup G} (hd : CaseAData N zK E)
    (hQi : ((h.sBar hp.ds).img N.SK).index = 2)
    (hW : ∀ e ∈ E, N.x⁻¹ * e * N.x ∈ N.K ⊔ N.SC) : False := by
  have hSB := h.sBar hp.ds
  have hf := h.facts2511
  have hxS : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  set F : Subgroup G := E ⊔ N.SC with hF
  set Fx : Subgroup G := CFSG.conjugate F N.x with hFx
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hES : E ≤ N.S := hd.le_SK.trans N.SK_le_S
  have hcommES : ∀ e ∈ E, ∀ a ∈ N.SC, e * a = a * e := fun e he a ha =>
    (h.SC_commutes ha e (hEK he)).symm
  have hFelem : IsElemAbelian 2 F := hp.F_elemAbelian h hd
  have hFxelem : IsElemAbelian 2 Fx := isElemAbelian_conjugate hFelem N.x
  have hmemFx : ∀ y : G, y ∈ Fx ↔ N.x * y * N.x⁻¹ ∈ F := fun y => BenderBranch.mem_conjugate_iff
  have hFS : F ≤ N.S := sup_le hES N.SC_le_S
  have htSC : t ∈ N.SC := hf.t_mem
  have ht2 : t * t = 1 := hf.t_mul_t
  have hzK2 : zK * zK = 1 := hf.zK_sq
  have hzKK : zK ∈ N.K := h.hK0 ▸ hf.zK_mem
  have htzK : t * zK = zK * t := hf.t_mul_zK
  have htK : t ∉ N.K := fun htK => hf.t_ne_one (h.K_inf_SC_eq_bot_mem htK htSC)
  set W : Subgroup G := N.K ⊔ N.SC with hWdef
  have hKW : N.K ≤ W := le_sup_left
  have hSCW : N.SC ≤ W := le_sup_right
  have hFxW : Fx ≤ W := by
    intro y hy
    rw [hmemFx] at hy
    obtain ⟨e, he, a, ha, hea⟩ := mem_sup_of_commute hcommES hy
    have hy' : y = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * a * N.x) := by
      calc y = N.x⁻¹ * (N.x * y * N.x⁻¹) * N.x := by group
        _ = N.x⁻¹ * (e * a) * N.x := by rw [hea]
        _ = (N.x⁻¹ * e * N.x) * (N.x⁻¹ * a * N.x) := by group
    have hax : N.x⁻¹ * a * N.x ∈ W := by
      rw [hp.SC_eq] at ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have : N.x⁻¹ * t ^ n * N.x = (t * zK) ^ n := by
        rw [← hp.htx]
        have := conj_zpow (a := N.x⁻¹) (b := t) (i := n)
        simpa using this.symm
      rw [this]
      exact W.zpow_mem (W.mul_mem (hSCW htSC) (hKW hzKK)) n
    rw [hy']
    exact W.mul_mem (hW e he) hax
  have hFxS : Fx ≤ N.S := by
    intro y hy
    rw [hmemFx] at hy
    exact (Subgroup.mem_normalizer_iff.mp hxS y).mpr (hFS hy)
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : G, f₀ = t * zK := ⟨_, rfl⟩
  have hf₀Fx : f₀ ∈ Fx := by
    rw [hmemFx]
    have : N.x * f₀ * N.x⁻¹ = t := by
      rw [hf₀, ← hp.htx]; group
    rw [this]
    exact Subgroup.mem_sup_right htSC
  have hf₀K : f₀ ∉ N.K := by
    intro hK
    apply htK
    have : t = f₀ * zK⁻¹ := by rw [hf₀]; group
    rw [this]
    exact N.K.mul_mem hK (N.K.inv_mem hzKK)
  have hzKFx : zK ∈ Fx := by
    rw [hmemFx]
    have : N.x * zK * N.x⁻¹ = zK := by
      have h1 : zK * N.x = N.x * zK := by
        calc zK * N.x = N.x * (N.x⁻¹ * zK * N.x) := by group
          _ = N.x * zK := by rw [hp.hfix]
      calc N.x * zK * N.x⁻¹ = (N.x * zK) * N.x⁻¹ := rfl
        _ = zK * N.x * N.x⁻¹ := by rw [h1]
        _ = zK := by group
    rw [this]
    exact Subgroup.mem_sup_left hd.zK_mem
  set E2 : Subgroup G := Fx ⊓ N.K with hE2
  have hE2SK : E2 ≤ N.SK := fun y hy => ⟨hFxS hy.1, hy.2⟩
  have hE2A : E2 ⊓ N.SC = ⊥ := by
    refine le_bot_iff.mp ?_
    calc E2 ⊓ N.SC ≤ N.K ⊓ N.SC := inf_le_inf_right _ inf_le_right
      _ = ⊥ := h.K_inf_SC
  have hE2elem : IsElemAbelian 2 E2 :=
    isElemAbelian_of_forall (fun a ha b hb => elemAbelian_comm hFxelem ha.1 hb.1)
      (fun a ha => elemAbelian_sq hFxelem ha.1)
  have hE2le4 : Nat.card E2 ≤ 4 := hSB.card_le_four (hE2SK.trans N.SK_le_S) hE2A hE2elem
  have hcoset : ∀ w ∈ Fx, w ∈ E2 ∨ w * f₀⁻¹ ∈ E2 := by
    intro w hw
    have hwW := hFxW hw
    obtain ⟨k, hk, a, ha, hwka⟩ := mem_sup_of_commute (A := N.K) (B := N.SC)
      (fun k hk a ha => (h.SC_commutes ha k hk).symm) hwW
    rcases mem_zpowers_involution ht2 (hp.SC_eq ▸ ha) with h1 | h1
    · left
      refine ⟨hw, ?_⟩
      rw [← hwka, h1, mul_one]
      exact hk
    · right
      refine ⟨Fx.mul_mem hw (Fx.inv_mem hf₀Fx), ?_⟩
      have hzKi : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK2
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      have : w * f₀⁻¹ = k * zK := by
        rw [← hwka, h1, hf₀, mul_inv_rev, hzKi, hti]
        calc k * t * (zK * t) = k * (t * zK) * t := by group
          _ = k * (zK * t) * t := by rw [htzK]
          _ = k * zK * (t * t) := by group
          _ = k * zK := by rw [ht2]; group
      rw [this]
      exact N.K.mul_mem hk hzKK
  have hF8 : 8 ≤ Nat.card F := by
    have h4 : Nat.card E = 4 := hd.four.2
    have hdvd : Nat.card E ∣ Nat.card F := Subgroup.card_dvd_of_le le_sup_left
    have hne : Nat.card F ≠ 4 := by
      intro hc
      have heq : E = F := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hc, h4])
      have : t ∈ E := heq ▸ Subgroup.mem_sup_right htSC
      exact htK (hEK this)
    obtain ⟨m, hm⟩ := hdvd
    rw [h4] at hm
    have hge : 4 ≤ Nat.card F := by
      rw [← h4]
      exact Subgroup.card_le_of_le (le_sup_left : E ≤ F)
    omega
  have hFx8 : 8 ≤ Nat.card Fx := by
    rw [hFx, BenderBranch.card_conjugate]
    exact hF8
  have hE2card4 : Nat.card E2 = 4 := by
    have h2 : Nat.card Fx ≤ 2 * Nat.card E2 := card_le_two_mul_of_cosets inf_le_left hf₀Fx hcoset
    omega
  have hE2four : IsFourSubgroup E2 := ⟨hE2elem, hE2card4⟩
  have htFx : t ∈ Fx := by
    have : t = f₀ * zK := by
      rw [hf₀]
      calc t = t * (zK * zK) := by rw [hzK2]; group
        _ = t * zK * zK := by group
    rw [this]
    exact Fx.mul_mem hf₀Fx hzKFx
  have hSCFx : N.SC ≤ Fx := by
    rw [hp.SC_eq]
    exact Subgroup.zpowers_le.mpr htFx
  have hzKE2 : zK ∈ E2 := ⟨hzKFx, hzKK⟩
  have hFxeq : Fx = E2 ⊔ N.SC := by
    apply le_antisymm
    · intro w hw
      rcases hcoset w hw with h1 | h1
      · exact Subgroup.mem_sup_left h1
      · have hf₀' : f₀ ∈ E2 ⊔ N.SC := by
          rw [hf₀]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htSC) (Subgroup.mem_sup_left hzKE2)
        have : w = (w * f₀⁻¹) * f₀ := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) hf₀'
    · exact sup_le inf_le_left hSCFx
  obtain ⟨s, hsS, hs⟩ := hSB.exists_conj_four N.SK_le_S h.SK_inf_SC
    (fun s hs q hq => h.SK_normal_in_S hs hq) (h.not_SK_le_Rt hp.ds) hQi hd.four hE2four
    hd.le_SK hE2SK
  have hcE : CFSG.conjugate E s⁻¹ ≤ E2 := by
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have := hs _ hy
    have e : s * (s⁻¹ * y * s⁻¹⁻¹) * s⁻¹ = y := by group
    rwa [e] at this
  have hE2eq : CFSG.conjugate E s⁻¹ = E2 :=
    Subgroup.eq_of_le_of_card_ge hcE (by rw [hE2card4, BenderBranch.card_conjugate, hd.four.2])
  have hSCn : CFSG.conjugate N.SC s⁻¹ = N.SC :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
      ((Subgroup.normalizer (N.SC : Set G)).inv_mem (h.H_le_normalizer_SC (N.S_le_H hsS)))
  have hmapsup : ∀ (A B : Subgroup G) (g : G),
      CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g :=
    fun A B g => Subgroup.map_sup _ _ _
  have hconjF : CFSG.conjugate F s⁻¹ = Fx := by
    rw [hF, hmapsup, hE2eq, hSCn, hFxeq]
  exact hd.conjugate_x_ne (N.S.inv_mem hsS) (by rw [← hconjF] at hFx; exact hFx.symm)

theorem Lv2520.index_img_SK {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hR : DS.DSData R) (hidx : Nat.card ↥N.S ≤ 2 * (Nat.card ↥N.SK * Nat.card ↥N.SC))
    (hout : ¬ N.S ≤ N.K ⊔ N.SC) :
    ((h.sBar hR).img N.SK).index = 2 := by
  have hSB := h.sBar hR
  have h1 := hSB.card_S N.SC_le_S
  have h2 := hSB.index_img_mul N.SK_le_S h.SK_inf_SC
  have hSKpos : 0 < Nat.card N.SK := Nat.card_pos
  have hSCpos : 0 < Nat.card N.SC := Nat.card_pos
  have hle : (hSB.img N.SK).index ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have h3 : Nat.card N.S = Nat.card N.SC * ((hSB.img N.SK).index * Nat.card N.SK) := by
      rw [h2, h1]
    have h4 : 3 * (Nat.card N.SC * Nat.card N.SK) ≤ Nat.card N.S := by
      rw [h3]
      calc 3 * (Nat.card N.SC * Nat.card N.SK)
          ≤ (hSB.img N.SK).index * (Nat.card N.SC * Nat.card N.SK) :=
            Nat.mul_le_mul_right _ hgt
        _ = Nat.card N.SC * ((hSB.img N.SK).index * Nat.card N.SK) := by ring
    have h5 : Nat.card N.SK * Nat.card N.SC = Nat.card N.SC * Nat.card N.SK := mul_comm _ _
    nlinarith [Nat.mul_pos hSKpos hSCpos]
  have hne : (hSB.img N.SK).index ≠ 1 := by
    intro h1'
    apply hout
    intro s hs
    have hmem : (hSB.hom ⟨s, hs⟩ : ↥(autOn N.S N.K)) ∈ hSB.img N.SK := by
      have : hSB.img N.SK = ⊤ := Subgroup.index_eq_one.mp h1'
      rw [this]; trivial
    obtain ⟨q, hqSK, hqS, hq⟩ := hSB.mem_img.mp hmem
    have h6 : q⁻¹ * s ∈ N.SC := (hSB.pi_eq_iff hqS hs).mp hq
    have : s = q * (q⁻¹ * s) := by group
    rw [this]
    exact Subgroup.mul_mem_sup (N.SK_le_K hqSK) h6
  have hpos : (hSB.img N.SK).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem oddCoreIn_eq_bot_of_charTwo {X : Subgroup G} (hX : CharTwo X) : oddCoreIn X = ⊥ := by
  have h1 := oddCoreIn_inf_eq_bot hX (le_refl X)
  rwa [inf_eq_left.mpr (oddCoreIn_le X)] at h1

theorem Lv2520.caseA1_false {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (houter : OutOuter)
    (hfam : OutFamily N.K N.H) (hout : ¬ N.S ≤ N.K ⊔ N.SC) : False := by
  have hf := h.facts2511
  obtain ⟨E, hd⟩ := h.exists_caseAData hp.ds hp.hz
  have hQi := h.index_img_SK hp.ds hp.idx hout
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hES : E ≤ N.S := hd.le_SK.trans N.SK_le_S
  have hex : ∃ e ∈ E, N.x⁻¹ * e * N.x ∉ N.K ⊔ N.SC := by
    by_contra hall
    push Not at hall
    exact h.caseA_conj_le_false hp hd hQi hall
  obtain ⟨e, heE, heW⟩ := hex
  have hzK2 : zK * zK = 1 := hf.zK_sq
  have hzKK : zK ∈ N.K := h.hK0 ▸ hf.zK_mem
  have he2 : e * e = 1 := hd.four.sq heE
  have he1 : e ≠ 1 := by
    rintro rfl
    apply heW
    have : N.x⁻¹ * 1 * N.x = 1 := by group
    rw [this]
    exact Subgroup.one_mem _
  obtain ⟨k, hkK, hk⟩ := hone G N.K N.H N.S (h.outSetting hfam) zK e hzKK (hEK heE) hzK2 he2
    h.zK_ne_one he1
  set u : G := N.x⁻¹ * e * N.x with hu
  have huS : u ∈ N.S := by
    have hxi : N.x⁻¹ ∈ Subgroup.normalizer (N.S : Set G) :=
      (Subgroup.normalizer (N.S : Set G)).inv_mem N.x_mem.2
    have := (Subgroup.mem_normalizer_iff.mp hxi e).mp (hES heE)
    simpa using this
  have hu2 : u * u = 1 := by
    rw [hu]
    calc N.x⁻¹ * e * N.x * (N.x⁻¹ * e * N.x) = N.x⁻¹ * (e * e) * N.x := by group
      _ = 1 := by rw [he2]; group
  have hug : (k⁻¹ * N.x)⁻¹ * N.z * (k⁻¹ * N.x) = u := by
    rw [hp.hz, hu, ← hk]
    group
  have hchar := h.charTwo_K_inf_centralizer_conj (g := k⁻¹ * N.x) (by rw [hug]; exact huS)
  rw [hug] at hchar
  have hle : N.K ⊔ (N.H ⊓ Subgroup.centralizer (N.K : Set G)) ≤ N.K ⊔ N.SC := by
    refine sup_le_sup_left ?_ N.K
    intro c hc
    exact h.mem_SC_of_commutes hc.1 (fun f hf' => (Subgroup.mem_centralizer_iff.mp hc.2 f hf').symm)
  have hnot : u ∉ N.K ⊔ (N.H ⊓ Subgroup.centralizer (N.K : Set G)) := fun hmem => heW (hle hmem)
  obtain ⟨-, hodd⟩ := houter G N.K N.H N.S (h.outSetting hfam) u (N.S_le_H huS) hu2 hnot
  exact hodd (oddCoreIn_eq_bot_of_charTwo hchar)

theorem Lv2520.centralizer_t_le_normalizer (h : Lv2520 N t zK) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
  have hK0 := h.hK0
  rw [h.concl2518.2.1]
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [hK0]; exact Subgroup.le_normalizer
  · exact N.S_le_normalizer_K h.hKH
  · rw [← hK0]
    exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)

theorem Lv2520.centralizer_t_le_normalizer_C (h : Lv2520 N t zK) :
    Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer (N.K0 : Set G) : Subgroup G) : Set G) := by
  have hK0 := h.hK0
  have hGt := h.centralizer_t_le_normalizer
  refine CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
    Subgroup.le_normalizer ?_
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  rw [hK0]
  have hgK := (Subgroup.mem_normalizer_iff.mp (hGt hg))
  have key : ∀ g' ∈ Subgroup.normalizer (N.K : Set G), ∀ c : G,
      c ∈ Subgroup.centralizer (N.K : Set G) → g' * c * g'⁻¹ ∈ Subgroup.centralizer (N.K : Set G) := by
    intro g' hg' c hc
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : g'⁻¹ * k * g' ∈ N.K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N.K : Set G)).inv_mem hg') k).mp hk
      simpa using this
    have hc' := Subgroup.mem_centralizer_iff.mp hc _ hk'
    calc k * (g' * c * g'⁻¹) = g' * ((g'⁻¹ * k * g') * c) * g'⁻¹ := by group
      _ = g' * (c * (g'⁻¹ * k * g')) * g'⁻¹ := by rw [hc']
      _ = g' * c * g'⁻¹ * k := by group
  constructor
  · intro hc
    exact key g (Subgroup.mem_normalizer_iff.mpr (hGt hg |> fun h' => (Subgroup.mem_normalizer_iff.mp h'))) c hc
  · intro hc
    have h1 := key g⁻¹ ((Subgroup.normalizer (N.K : Set G)).inv_mem (hGt hg)) _ hc
    have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
    rw [e] at h1
    exact h1

theorem Lv2520.caseA2_Gt_eq (h : Lv2520 N t zK) (hSC : N.SC = Subgroup.zpowers t) :
    Subgroup.centralizer ({t} : Set G) = N.H := by
  have hf := h.facts2511
  refine le_antisymm ?_ hf.H_le
  have hCchar : CharTwo (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer (N.K0 : Set G)) := h.concl2518.2.2.2.1
  have hCnorm : ((Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)).subgroupOf
      (Subgroup.centralizer ({t} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr h.centralizer_t_le_normalizer_C
  have hC1 := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le_of_normal_subgroupOf 2
    (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G))
    (Subgroup.centralizer ({t} : Set G)) inf_le_left hCnorm
  have hC2 : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≤ N.S := hf.sylow.pCoreOf_le
  have hC3 : pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) ≤
      Subgroup.centralizer (N.K0 : Set G) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _).trans inf_le_right
  have hCcore : pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer (N.K0 : Set G)) ≤ N.SC := le_inf (hC1.trans hC2) hC3
  have hCcent : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) ≤
      Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer (N.K0 : Set G)) : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : r ∈ Subgroup.zpowers t := hSC ▸ hCcore hr
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr'
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc.1
    exact ((Commute.zpow_right (show Commute c t from hct) n).eq).symm
  have hCle : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G) ≤ N.SC :=
    fun c hc => hCcore (hCchar ⟨hc, hCcent hc⟩)
  calc Subgroup.centralizer ({t} : Set G) =
      N.K0 ⊔ N.S ⊔ (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (N.K0 : Set G)) :=
        h.concl2518.2.1
    _ ≤ N.H := sup_le (sup_le N.K0_le_H N.S_le_H) (hCle.trans (N.SC_le_S.trans N.S_le_H))

theorem Lv2520.tw_conj {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H)
    {E : Subgroup G} (hd : CaseAData N zK E) :
    ∀ w ∈ E, ∃ c : G, c⁻¹ * t * c = t * w := by
  intro w hw
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hzKK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
  by_cases hw1 : w = 1
  · exact ⟨1, by rw [hw1]; group⟩
  · obtain ⟨κ, hκK, hκ⟩ := hone G N.K N.H N.S (h.outSetting hfam) zK w hzKK (hEK hw)
      h.facts2511.zK_sq (hd.four.sq hw) h.zK_ne_one hw1
    refine ⟨N.x * κ⁻¹, ?_⟩
    have hκt : κ * t = t * κ := by
      have := h.SC_commutes h.facts2511.t_mem κ hκK
      exact this.symm
    calc (N.x * κ⁻¹)⁻¹ * t * (N.x * κ⁻¹) = κ * (N.x⁻¹ * t * N.x) * κ⁻¹ := by group
      _ = κ * (t * zK) * κ⁻¹ := by rw [hp.htx]
      _ = (κ * t) * (zK * κ⁻¹) := by group
      _ = (t * κ) * (zK * κ⁻¹) := by rw [hκt]
      _ = t * (κ * zK * κ⁻¹) := by group
      _ = t * w := by rw [hκ]

theorem Lv2520.involution_conj_z {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H) {w : G}
    (hwK : w ∈ N.K) (hw2 : w * w = 1) (hw1 : w ≠ 1) : ∃ c : G, c⁻¹ * N.z * c = w := by
  have hzKK : zK ∈ N.K := h.hK0 ▸ h.facts2511.zK_mem
  obtain ⟨κ, hκK, hκ⟩ := hone G N.K N.H N.S (h.outSetting hfam) zK w hzKK hwK
    h.facts2511.zK_sq hw2 h.zK_ne_one hw1
  refine ⟨κ⁻¹, ?_⟩
  rw [hp.hz, ← hκ]
  group

theorem Lv2520.caseA2_E_le_conj {R : Subgroup ↥(autOn N.S N.K)} (h : Lv2520 N t zK)
    (hp : CaseAParams N t zK R) (hone : OutOneClass) (hfam : OutFamily N.K N.H)
    (hin : N.S ≤ N.K ⊔ N.SC) {E : Subgroup G} (hd : CaseAData N zK E) {e g : G} (heE : e ∈ E)
    (hge : g⁻¹ * t * g = t * e) : E ≤ CFSG.conjugate N.K g := by
  have hf := h.facts2511
  have hEK : E ≤ N.K := hd.le_SK.trans N.SK_le_K
  have hGt := h.caseA2_Gt_eq hp.SC_eq
  have hH : N.H = N.K ⊔ N.SC := by
    refine le_antisymm ?_ (sup_le N.K_le_H (N.SC_le_S.trans N.S_le_H))
    rw [N.join]
    exact sup_le le_sup_left hin
  have hFel := hp.F_elemAbelian h hd
  have htSC := hf.t_mem
  have ht2 := hf.t_mul_t
  have htK : t ∉ N.K := fun htK => hf.t_ne_one (h.K_inf_SC_eq_bot_mem htK htSC)
  have hcommtE : ∀ w ∈ E, t * w = w * t := fun w hw =>
    h.SC_commutes htSC w (hEK hw)
  obtain ⟨t', ht'⟩ : ∃ t' : G, t' = t * e := ⟨_, rfl⟩
  have ht'F : t' ∈ E ⊔ N.SC := by
    rw [ht']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htSC) (Subgroup.mem_sup_left heE)
  have ht'2 : t' * t' = 1 := elemAbelian_sq hFel ht'F
  have hFcent : E ⊔ N.SC ≤ Subgroup.centralizer ({t'} : Set G) := by
    intro f hf'
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact elemAbelian_comm hFel hf' ht'F
  have hge' : g⁻¹ * t * g = t' := by rw [ht']; exact hge
  have hcent : Subgroup.centralizer ({t'} : Set G) = CFSG.conjugate N.H g := by
    rw [← hge', centralizer_conj_singleton, hGt]
    rfl
  have hK'comm : ∀ y ∈ CFSG.conjugate N.K g, ∀ a ∈ Subgroup.zpowers t', y * a = a * y := by
    intro y hy a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    refine (Commute.zpow_right ?_ n).eq
    rw [BenderBranch.mem_conjugate_iff] at hy
    have hkt : (g * y * g⁻¹) * t = t * (g * y * g⁻¹) := (h.SC_commutes htSC _ hy).symm
    show y * t' = t' * y
    rw [← hge']
    calc y * (g⁻¹ * t * g) = g⁻¹ * ((g * y * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * y * g⁻¹)) * g := by rw [hkt]
      _ = g⁻¹ * t * g * y := by group
  have hmapsup : ∀ (A B : Subgroup G) (g : G),
      CFSG.conjugate (A ⊔ B) g = CFSG.conjugate A g ⊔ CFSG.conjugate B g :=
    fun A B g => Subgroup.map_sup _ _ _
  have hconjSC : CFSG.conjugate N.SC g = Subgroup.zpowers t' := by
    rw [hp.SC_eq, ← hge']
    have := MonoidHom.map_zpowers (MulAut.conj g⁻¹).toMonoidHom t
    rw [show ((MulAut.conj g⁻¹).toMonoidHom t) = g⁻¹ * t * g by simp] at this
    exact this
  have hFle : E ⊔ N.SC ≤ CFSG.conjugate N.K g ⊔ Subgroup.zpowers t' := by
    intro f hf'
    have := hFcent hf'
    rw [hcent, hH, hmapsup, hconjSC] at this
    exact this
  intro e' he'
  obtain ⟨k', hk', a, ha, hka⟩ := mem_sup_of_commute hK'comm (hFle (Subgroup.mem_sup_left he'))
  rcases mem_zpowers_involution ht'2 ha with h1 | h1
  · rw [← hka, h1, mul_one]
    exact hk'
  · exfalso
    rw [h1] at hka
    have hk'e : k' = e' * t' := by
      calc k' = (k' * t') * t' := by rw [mul_assoc, ht'2, mul_one]
        _ = e' * t' := by rw [hka]
    have hk'F : k' ∈ E ⊔ N.SC := by
      rw [hk'e]; exact (E ⊔ N.SC).mul_mem (Subgroup.mem_sup_left he') ht'F
    have hk'2 : k' * k' = 1 := elemAbelian_sq hFel hk'F
    have hk'w : k' = t * (e' * e) := by
      rw [hk'e, ht']
      calc e' * (t * e) = (e' * t) * e := by group
        _ = (t * e') * e := by rw [hcommtE e' he']
        _ = t * (e' * e) := by group
    obtain ⟨c₂, hc₂⟩ := h.tw_conj hp hone hfam hd (e' * e) (E.mul_mem he' heE)
    have hk'1 : k' ≠ 1 := by
      intro hk1
      apply hf.t_ne_one
      have : c₂⁻¹ * t * c₂ = 1 := by rw [hc₂, ← hk'w, hk1]
      calc t = c₂ * (c₂⁻¹ * t * c₂) * c₂⁻¹ := by group
        _ = 1 := by rw [this]; group
    have hk''K : g * k' * g⁻¹ ∈ N.K := by
      have := hk'
      rw [BenderBranch.mem_conjugate_iff] at this
      exact this
    have hk''2 : (g * k' * g⁻¹) * (g * k' * g⁻¹) = 1 := by
      calc (g * k' * g⁻¹) * (g * k' * g⁻¹) = g * (k' * k') * g⁻¹ := by group
        _ = 1 := by rw [hk'2]; group
    have hk''1 : g * k' * g⁻¹ ≠ 1 := by
      intro hk1
      apply hk'1
      calc k' = g⁻¹ * (g * k' * g⁻¹) * g := by group
        _ = 1 := by rw [hk1]; group
    obtain ⟨c, hc⟩ := h.involution_conj_z hp hone hfam hk''K hk''2 hk''1
    have h3 : (c * g)⁻¹ * N.z * (c * g) = k' := by
      calc (c * g)⁻¹ * N.z * (c * g) = g⁻¹ * (c⁻¹ * N.z * c) * g := by group
        _ = g⁻¹ * (g * k' * g⁻¹) * g := by rw [hc]
        _ = k' := by group
    have h4 : (c * g * c₂⁻¹)⁻¹ * N.z * (c * g * c₂⁻¹) = t := by
      calc (c * g * c₂⁻¹)⁻¹ * N.z * (c * g * c₂⁻¹) = c₂ * ((c * g)⁻¹ * N.z * (c * g)) * c₂⁻¹ := by group
        _ = c₂ * k' * c₂⁻¹ := by rw [h3]
        _ = c₂ * (c₂⁻¹ * t * c₂) * c₂⁻¹ := by rw [hc₂, hk'w]
        _ = t := by group
    exact hf.not_conj (c * g * c₂⁻¹) h4

end CaseA2

end CFSG.QuasithinUnique
