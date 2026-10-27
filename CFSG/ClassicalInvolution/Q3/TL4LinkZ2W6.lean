module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3Conn
import CFSG.ClassicalInvolution.Q3.TL4C264OmX
import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G3
public import CFSG.ClassicalInvolution.Q3.TL4Conn264F
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (XMem)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

private theorem eq_of_isSylow2In_le {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)}
    (hΦ : TypeRFam 3 Φ) {M M' T : Subgroup Q} (hM : M ∈ Φ) (hM' : M' ∈ Φ)
    (hT : IsSylow2In T M) (hTM' : T ≤ M') : M' = M := by
  by_contra hne
  obtain ⟨h1, -⟩ := hΦ.hyp.omega4 M hM M' hM' (Ne.symm hne)
  obtain ⟨e⟩ : Nonempty (↥T ≃* QuaternionGroup 2) := hΦ.quat M hM T hT
  have hT8 : Nat.card T = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hdvd : 2 ^ 3 ∣ Nat.card ↥(M ⊓ M') := by
    rw [show 2 ^ 3 = 8 by norm_num, ← hT8]
    exact Subgroup.card_dvd_of_le (le_inf hT.1 hTM')
  have := (padicValNat_dvd_iff_le Nat.card_pos.ne').mp hdvd
  omega

private theorem not_sixteen_dvd_natCard {Q : Type} [Group Q] [Finite Q] {Φ : Set (Subgroup Q)}
    (hΦ : TypeRFam 3 Φ) {M : Subgroup Q} (hM : M ∈ Φ) : ¬ 16 ∣ Nat.card M := by
  intro h16
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 4) (G := ↥M)
    (by norm_num; exact h16)
  have hK2 : IsPGroup 2 ↥(K.map M.subtype) := (IsPGroup.of_card hK).map _
  obtain ⟨V, hV, hKV⟩ := IsSylow2In.exists_ge hK2 (Subgroup.map_subtype_le K)
  obtain ⟨e⟩ : Nonempty (↥V ≃* QuaternionGroup 2) := hΦ.quat M hM V hV
  have hV8 : Nat.card V = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hd := Subgroup.card_dvd_of_le hKV
  rw [Subgroup.card_map_of_injective M.subtype_injective, hK, hV8] at hd
  norm_num at hd

private theorem quat_two_eq_mul_noncomm : ∀ g : QuaternionGroup 2, ∃ a b : QuaternionGroup 2,
    g = a * b ∧ (∃ w, a * w ≠ w * a) ∧ ∃ w, b * w ≠ w * b := by
  decide

private theorem le_linkLayerAt_sup {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (h : TypeRFam 3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {s : G} (hKs : IsUniqueInvolution K s)
    {M Rq : Subgroup G} (hM : M ∈ Ω) (hRq : IsSylow2In Rq M)
    (hRs : Rq ≤ Subgroup.centralizer ({s} : Set G)) : Rq ≤ linkLayerAt Ω K s ⊔ K := by
  by_cases hMK : M = K
  · subst hMK
    exact hRq.1.trans le_sup_right
  obtain ⟨e⟩ : Nonempty (↥Rq ≃* QuaternionGroup 2) := h.quat M hM Rq hRq
  have hnc : ∀ v : ↥Rq, (∃ w : ↥Rq, v * w ≠ w * v) →
      (v : G) ∈ Subgroup.normalizer (K : Set G) := by
    rintro v ⟨w, hvw⟩
    refine h.hyp.omega5 K hK M hM (Ne.symm hMK) s hKs v (hRq.1 v.2) (fun hall => hvw ?_)
      (hRq.2.1.to_le (Subgroup.zpowers_le.mpr v.2))
      (Subgroup.mem_centralizer_singleton_iff.mp (hRs v.2))
    exact Subtype.ext (hall w (hRq.1 w.2))
  have hRN : Rq ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    obtain ⟨a, b, hab, ⟨wa, hwa⟩, ⟨wb, hwb⟩⟩ := quat_two_eq_mul_noncomm (e ⟨r, hr⟩)
    have hr' : (⟨r, hr⟩ : ↥Rq) = e.symm a * e.symm b := by
      rw [← map_mul, ← hab, MulEquiv.symm_apply_apply]
    have hnc' : ∀ c w : QuaternionGroup 2, c * w ≠ w * c →
        (e.symm c : G) ∈ Subgroup.normalizer (K : Set G) := fun c w hcw =>
      hnc _ ⟨e.symm w, fun h1 => hcw (by simpa using congrArg e h1)⟩
    have e2 : r = (e.symm a : G) * (e.symm b : G) := congrArg Subtype.val hr'
    rw [e2]
    exact Subgroup.mul_mem _ (hnc' a wa hwa) (hnc' b wb hwb)
  have hMn : M ∈ omegaNbr Ω K := ⟨hM, hMK, Rq, mem_RSet_of_isSylow2In hM hRq, hRq.1, hRN⟩
  exact (le_coreAt s hRq.2.1 hRq.1 hRs).trans ((coreAt_le_linkLayerAt hMn).trans le_sup_left)

private theorem exists_sylow_lift_of_fixed {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (h : TypeRFam 3 Ω) (hcl : ConjInvariant Ω) {x s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1)
    {Mb Qb : Subgroup (SecQuot Ω x)} (hMb : Mb ∈ secFam Ω x) (hQb : IsSylow2In Qb Mb)
    (hfix : ∀ y ∈ Qb, secAct hcl hs y = y) :
    ∃ Rq : Subgroup G, (∃ M ∈ Ω, IsSylow2In Rq M) ∧ Rq ≤ layerY Ω x ∧
      Rq ≤ Subgroup.centralizer ({s} : Set G) ∧
      (Rq.subgroupOf (layerY Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Qb := by
  classical
  have hΦ : TypeRFam 3 (secFam Ω x) := h.secFam
  obtain ⟨M₀, hM₀, rfl⟩ := mem_secFam_iff.mp hMb
  have hsY := mem_normalizer_layerY hcl hs
  have hMσ : (secImg Ω x M₀).map (secAct hcl hs).toMonoidHom = secImg Ω x M₀ := by
    have hmem : (secImg Ω x M₀).map (secAct hcl hs).toMonoidHom ∈ secFam Ω x := by
      rw [← secImg_conjSub_eq_map hcl hs]
      exact secImg_mem (XMem.conj' hcl hM₀ hs)
    exact eq_of_isSylow2In_le hΦ hMb hmem hQb fun y hy => ⟨y, hQb.1 hy, hfix y hy⟩
  have hs2' : IsPGroup 2 (Subgroup.zpowers s) := Balance.isPGroup_zpowers_of_mul_self_eq_one hs2
  have hVN : Subgroup.zpowers s ≤ Subgroup.normalizer (oddCoreOf (layerY Ω x) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_oddCore_of_mem_normalizer hsY)
  have hperm : ∀ v ∈ Subgroup.zpowers s, ∃ m ∈ oddCoreOf (layerY Ω x),
      conjSub v M₀ = conjSub m M₀ := by
    intro v hv
    rcases Balance.Bootstrap.mem_zpowers_involution hs2 hv with rfl | rfl
    · exact ⟨1, (oddCoreOf _).one_mem, rfl⟩
    · have himg : secImg Ω x M₀ = secImg Ω x (conjSub v M₀) := by
        rw [secImg_conjSub_eq_map hcl hs, hMσ]
      obtain ⟨ν, hν, hνM⟩ := exists_conj_of_secImg_eq h hM₀ (XMem.conj' hcl hM₀ hs) himg
      exact ⟨ν, mem_oddCoreOf_iff.mpr ⟨ν.2, hν⟩, hνM⟩
  obtain ⟨m, hm, hsN⟩ :=
    E3S3O.exists_conj_normalizer_of_perm (oddCoreOf_odd_natCard _) M₀ hs2' hVN hperm
  obtain ⟨hmY, hmO⟩ := mem_oddCoreOf_iff.mp hm
  have hM₁ : XMem Ω x (conjSub m M₀) := XMem.conj' hcl hM₀ (layerY_le_centralizer hmY)
  have himg : secImg Ω x (conjSub m M₀) = secImg Ω x M₀ :=
    secImg_conj_of_mem (ν := ⟨m, hmY⟩) hmO M₀
  have hsC : s ∈ Subgroup.normalizer (coreAt x (conjSub m M₀) : Set G) :=
    mem_normalizer_coreAt x (hsN (Subgroup.mem_zpowers s)) hs
  have hCY : coreAt x (conjSub m M₀) ≤ layerY Ω x := coreAt_le_layerY hM₁
  have hact : ∀ w : ↥(layerY Ω x), ∃ hw : s * (w : G) * s⁻¹ ∈ layerY Ω x,
      ((⟨s * (w : G) * s⁻¹, hw⟩ : ↥(layerY Ω x)) : SecQuot Ω x) =
        secAct hcl hs (w : SecQuot Ω x) := by
    intro w
    have hw : s * (w : G) * s⁻¹ ∈ layerY Ω x :=
      (Subgroup.mem_normalizer_iff.mp hsY (w : G)).mp w.2
    exact ⟨hw, (s26Act_mk (layerY Ω x) ⟨s, hsY⟩ w ⟨s * (w : G) * s⁻¹, hw⟩ rfl).symm⟩
  have hsE : ∀ y ∈ (Qb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).map
      (layerY Ω x).subtype, s * y * s⁻¹ ∈
        (Qb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).map
          (layerY Ω x).subtype := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨hw', he⟩ := hact w
    refine ⟨⟨s * (w : G) * s⁻¹, hw'⟩, ?_, rfl⟩
    show ((⟨s * (w : G) * s⁻¹, hw'⟩ : ↥(layerY Ω x)) : SecQuot Ω x) ∈ Qb
    have e1 : secAct hcl hs (w : SecQuot Ω x) = (w : SecQuot Ω x) := hfix _ hw
    rw [he, e1]
    exact hw
  have hss : ∀ y : G, s * (s * y * s⁻¹) * s⁻¹ = y := by
    intro y
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
    rw [hsinv]
    calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
      _ = y := by rw [hs2, one_mul, mul_one]
  have hsD : Subgroup.zpowers s ≤ Subgroup.normalizer ((coreAt x (conjSub m M₀) ⊓
      (Qb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).map
        (layerY Ω x).subtype : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hsC y).mp hy1, hsE y hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hsC y).mpr hy1, ?_⟩
      have h1 := hsE _ hy2
      rwa [hss] at h1
  obtain ⟨Rq, hRq, hRqN⟩ := E3S3O.exists_isSylow2In_normalized hs2' hsD
  have hRqC : Rq ≤ coreAt x (conjSub m M₀) := hRq.1.trans inf_le_left
  have hRqY : Rq ≤ layerY Ω x := hRqC.trans hCY
  have hRqM : Rq ≤ conjSub m M₀ := hRqC.trans (coreAt_le x _)
  have hRqs : Rq ≤ Subgroup.centralizer ({s} : Set G) := by
    intro r hr
    have hrY := hRqY hr
    obtain ⟨hw', he⟩ := hact ⟨r, hrY⟩
    have hsr : s * r * s⁻¹ ∈ Rq :=
      (Subgroup.mem_normalizer_iff.mp (hRqN (Subgroup.mem_zpowers s)) r).mp hr
    obtain ⟨w, hwQ, hwr⟩ := (hRq.1 hr).2
    have hπr : ((⟨r, hrY⟩ : ↥(layerY Ω x)) : SecQuot Ω x) ∈ Qb := by
      have e : w = ⟨r, hrY⟩ := Subtype.ext hwr
      rw [← e]
      exact hwQ
    have h2 : ((⟨s * r * s⁻¹, hw'⟩ : ↥(layerY Ω x)) : SecQuot Ω x) =
        ((⟨r, hrY⟩ : ↥(layerY Ω x)) : SecQuot Ω x) := by
      rw [he, hfix _ hπr]
    have h3 := QuotientGroup.eq.mp h2
    have h4 : (s * r * s⁻¹)⁻¹ * r ∈ oddCoreOf (layerY Ω x) :=
      mem_oddCoreOf_iff.mpr ⟨(layerY Ω x).mul_mem ((layerY Ω x).inv_mem hw') hrY, by
        convert h3 using 1⟩
    have h5 : (s * r * s⁻¹)⁻¹ * r = 1 := eq_one_of_isPGroup_of_mem_odd
      (oddCoreOf_odd_natCard _) h4
      (hRq.2.1.to_le (Subgroup.zpowers_le.mpr (Rq.mul_mem (Rq.inv_mem hsr) hr)))
    have hc : s * r * s⁻¹ = r := inv_mul_eq_one.mp h5
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc r * s = s * r * s⁻¹ * s := by rw [hc]
      _ = s * r := by group
  have hDY : (coreAt x (conjSub m M₀) ⊓
      (Qb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).map
        (layerY Ω x).subtype : Subgroup G) ≤ layerY Ω x := inf_le_left.trans hCY
  have hDimg : ((coreAt x (conjSub m M₀) ⊓
      (Qb.comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).map
        (layerY Ω x).subtype : Subgroup G).subgroupOf (layerY Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Qb := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨-, w', hw'Q, hw'w⟩ := Subgroup.mem_subgroupOf.mp hw
      have e : w' = w := Subtype.ext hw'w
      rw [← e]
      exact hw'Q
    · intro q hq
      have hq' : q ∈ secImg Ω x (conjSub m M₀) := by
        rw [himg]
        exact hQb.1 hq
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hq'
      exact ⟨w, Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hw, w, hq, rfl⟩, rfl⟩
  have hRqsyl := hRq.subgroupOf hDY
  have hmap := Hall196.isSylow2In_map_hom
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) hRqsyl
  rw [hDimg] at hmap
  have hRqimg : (Rq.subgroupOf (layerY Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Qb :=
    (hmap.2.2 Qb le_rfl hQb.2.1 hmap.1).symm
  obtain ⟨eQ⟩ : Nonempty (↥Qb ≃* QuaternionGroup 2) := hΦ.quat _ hMb Qb hQb
  have hbot : Rq.subgroupOf (layerY Ω x) ⊓ classicalInvolutionOddCore ↥(layerY Ω x) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    exact eq_one_of_isPGroup_of_mem_odd (CFSG.ComponentClassification.OddCore.odd_card _) hw.2
      (hRqsyl.2.1.to_le (Subgroup.zpowers_le.mpr hw.1))
  have hRq8 : Nat.card Rq = 8 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRqY).toEquiv,
      Nat.card_congr (AscQuot.quotRestrictEquiv hbot).toEquiv, hRqimg,
      Nat.card_congr eQ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (P := conjSub m M₀) (IsPGroup.of_bot (p := 2)) bot_le
  obtain ⟨eV⟩ : Nonempty (↥V ≃* QuaternionGroup 2) := h.quat _ hM₁.1 V hV
  have hV8 : Nat.card V = 8 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact ⟨Rq, ⟨_, hM₁.1, hV.of_natCard_le hRq.2.1 hRqM (by rw [hV8, hRq8])⟩, hRqY, hRqs,
    hRqimg⟩

private theorem exists_lift_fixSylGen {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (h : TypeRFam 3 Ω) (hcl : ConjInvariant Ω) {x s : G}
    (hs : s ∈ Subgroup.centralizer ({x} : Set G)) (hs2 : s * s = 1)
    {X : Subgroup (SecQuot Ω x)} {σ' : MulAut ↥X}
    (hσ' : ∀ c : ↥X, ((σ' c : ↥X) : SecQuot Ω x) = secAct hcl hs c)
    {K : Subgroup G} (hK : K ∈ Ω) (hKs : IsUniqueInvolution K s) :
    ∃ (L : Subgroup G) (ψ : ↥L →* ↥(fixSylGen (restrictFamily (secFam Ω x) X) σ')),
      Function.Surjective ψ ∧ L ≤ linkLayerAt Ω K s ⊔ K := by
  classical
  have hlift : ∀ Q : Subgroup ↥X, (∃ M ∈ restrictFamily (secFam Ω x) X, IsSylow2In Q M) →
      (∀ y ∈ Q, σ' y = y) → ∃ Rq : Subgroup G, (∃ M ∈ Ω, IsSylow2In Rq M) ∧
        Rq ≤ layerY Ω x ∧ Rq ≤ Subgroup.centralizer ({s} : Set G) ∧
        (Rq.subgroupOf (layerY Ω x)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Q.map X.subtype := by
    rintro Q ⟨_, ⟨Mb, hMb, hMbX, rfl⟩, hQ⟩ hQf
    have hQb : IsSylow2In (Q.map X.subtype) Mb := by
      have h1 := (isSylow2In_map_subtype_iff (Y := X)).mpr hQ
      rwa [Subgroup.map_subgroupOf_eq_of_le hMbX] at h1
    refine exists_sylow_lift_of_fixed h hcl hs hs2 hMb hQb ?_
    rintro _ ⟨q, hq, rfl⟩
    show secAct hcl hs (q : SecQuot Ω x) = (q : SecQuot Ω x)
    rw [← hσ' q, hQf q hq]
  obtain ⟨L, hLdef⟩ : ∃ L : Subgroup G, L = ⨆ Rq ∈ {Rq : Subgroup G |
      (∃ M ∈ Ω, IsSylow2In Rq M) ∧ Rq ≤ layerY Ω x ∧ Rq ≤ Subgroup.centralizer ({s} : Set G) ∧
        ∃ Q : Subgroup ↥X, ((∃ M ∈ restrictFamily (secFam Ω x) X, IsSylow2In Q M) ∧
          ∀ y ∈ Q, σ' y = y) ∧ (Rq.subgroupOf (layerY Ω x)).map
            (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) = Q.map X.subtype},
        Rq := ⟨_, rfl⟩
  have hLY : L ≤ layerY Ω x := by
    rw [hLdef]
    exact iSup₂_le fun Rq hRq => hRq.2.1
  have hLK : L ≤ linkLayerAt Ω K s ⊔ K := by
    rw [hLdef]
    refine iSup₂_le fun Rq hRq => ?_
    obtain ⟨⟨M, hM, hRqM⟩, -, hRqs, -⟩ := hRq
    exact le_linkLayerAt_sup h hK hKs hM hRqM hRqs
  have himage : (L.subgroupOf (layerY Ω x)).map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) =
        (fixSylGen (restrictFamily (secFam Ω x) X) σ').map X.subtype := by
    rw [hLdef, iSup₂_subgroupOf _ (fun Rq => Rq) fun Rq hRq => hRq.2.1]
    simp only [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup₂_le fun Rq hRq => ?_
      obtain ⟨Q, hQ, hQe⟩ := hRq.2.2.2
      rw [hQe]
      exact le_iSup₂_of_le Q hQ le_rfl
    · refine iSup₂_le fun Q hQ => ?_
      obtain ⟨Rq, hR1, hR2, hR3, hR4⟩ := hlift Q hQ.1 hQ.2
      rw [← hR4]
      exact le_iSup₂_of_le Rq ⟨hR1, hR2, hR3, Q, hQ, hR4⟩ le_rfl
  have hρmem : ∀ l : ↥L, ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))).comp
      (Subgroup.inclusion hLY)) l ∈
        (fixSylGen (restrictFamily (secFam Ω x) X) σ').map X.subtype := by
    intro l
    rw [← himage]
    exact ⟨Subgroup.inclusion hLY l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  let e := Subgroup.equivMapOfInjective (fixSylGen (restrictFamily (secFam Ω x) X) σ') X.subtype
    X.subtype_injective
  refine ⟨L, e.symm.toMonoidHom.comp
    (((QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))).comp
      (Subgroup.inclusion hLY)).codRestrict _ hρmem), fun y => ?_, hLK⟩
  have hy : ((e y : ↥((fixSylGen (restrictFamily (secFam Ω x) X) σ').map X.subtype)) :
      SecQuot Ω x) ∈ (L.subgroupOf (layerY Ω x)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x))) := by
    rw [himage]
    exact (e y).2
  obtain ⟨w, hw, hwy⟩ := hy
  refine ⟨⟨w, Subgroup.mem_subgroupOf.mp hw⟩, ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [← hwy]
  rfl

section Cit3


variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ W : Subgroup Y} {P : Sylow 2 Y}

theorem std8_twinSProp3 (h4 : Thm4RBelow 3 n) (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t)
    {σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}
    (hσ : SPropSec (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) J σ) :
    ∃ (k k' : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
      (σ' : MulAut ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))),
      TwinSProp3 (restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
        ((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R)).subgroupOf
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
        ((secImg (CoreAssembly.conjClass (tightCore R)) (t * u) J).subgroupOf
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) k k' σ' ∧
      (∀ c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)),
        c ∈ Subgroup.zpowers (k * k') ↔
          (c : SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) ∈
            secCyc (CoreAssembly.conjClass (tightCore R)) (t * u) (t * u)) ∧
      ∀ c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)),
        ((σ' c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
          SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) = σ c := by
  classical
  revert σ
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set K := tightCore R with hKdef
  set Φ := secFam Ω (t * u) with hΦdef
  set X := secOrb Ω K (t * u) with hXdef
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω (t * u))) with hπdef
  intro σ hσ
  have h := TightLargeHypR.typeRFam hs.large
  have hΦ : TypeRFam 3 Φ := h.secFam
  have hcl := hΦ.hyp.conjInvariant
  have hO : classicalInvolutionOddCore (SecQuot Ω (t * u)) = ⊥ := secQuot_oddCore_eq_bot
  have hn : Nat.card (SecQuot Ω (t * u)) < n := hs.natCard_secQuot_lt
  have hgen : omegaGen Φ = ⊤ := omegaGen_secFam
  have hKb : secImg Ω (t * u) K ∈ Φ := secImg_mem hs.xMem_K
  have hzY := mem_layerY_of_isUniqueInvolution h hs.xMem_K hs.hz
  have htY := mem_layerY_of_isUniqueInvolution h hs.xMem_J hs.ht
  have hzb := isUniqueInvolution_secImg h hs.xMem_K hs.hz
  have htb := isUniqueInvolution_secImg h hs.xMem_J hs.ht
  have hcomm := Vtx.commute_conj_of_not_conj h4 hΦ hO hn hKb
  obtain ⟨g, hg⟩ := hcj
  have hgG : g ∈ omegaGen Φ := by
    rw [hgen]
    exact Subgroup.mem_top g
  obtain ⟨k, hk, ek⟩ := Vtx.exists_orbGrp_conj hcl hKb hcomm hgG
  have hKX : secImg Ω (t * u) K ≤ X := Vtx.le_orbGrp _
  have hJX : secImg Ω (t * u) J ≤ X := by
    rw [← hg, ek]
    exact Vtx.conjSub_le_orbGrp _ ⟨k, Vtx.orbGrp_le hcl hKb hk⟩
  have hΦX : TypeRFam 3 (restrictFamily Φ X) := hΦ.restrict X
  have hOX : classicalInvolutionOddCore ↥X = ⊥ :=
    oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hKb) hO
  have hA : (secImg Ω (t * u) K).subgroupOf X ∈ restrictFamily Φ X := ⟨_, hKb, hKX, rfl⟩
  have hgenA : (⨆ c : ↥X, conjSub c ((secImg Ω (t * u) K).subgroupOf X)) = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ c : ↥X, (conjSub c ((secImg Ω (t * u) K).subgroupOf X)).map X.subtype =
        conjSub (c : SecQuot Ω (t * u)) (secImg Ω (t * u) K) := by
      intro c
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact Vtx.conjSub_le_orbGrp _ ⟨(c : SecQuot Ω (t * u)), Vtx.orbGrp_le hcl hKb c.2⟩
    simp_rw [e2]
    exact (Vtx.orbGrp_eq_iSup hcl hKb hcomm).symm
  have hAB : ∃ c : ↥X, conjSub c ((secImg Ω (t * u) K).subgroupOf X) =
      (secImg Ω (t * u) J).subgroupOf X :=
    ⟨⟨k, hk⟩, by rw [conjSub_subgroupOf]; congr 1; rw [← ek, hg]⟩
  set x : ↥X := ⟨π ⟨t, hzY⟩, hKX hzb.mem⟩ with hxdef
  set x' : ↥X := ⟨π ⟨u, htY⟩, hJX htb.mem⟩ with hx'def
  have hx : IsUniqueInvolution ((secImg Ω (t * u) K).subgroupOf X) x :=
    isUniqueInvolution_subgroupOf hzb hKX
  have hx' : IsUniqueInvolution ((secImg Ω (t * u) J).subgroupOf X) x' :=
    isUniqueInvolution_subgroupOf htb hJX
  have hcenZ := hs.mk_mul_mk_mem_center hzY htY
  have hcen : x * x' ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcenZ (c : SecQuot Ω (t * u)))
  have haY : t * u ∈ layerY Ω (t * u) := (layerY Ω (t * u)).mul_mem hzY htY
  have hxx' : ((x * x' : ↥X) : SecQuot Ω (t * u)) = π ⟨t * u, haY⟩ := by
    show π ⟨t, hzY⟩ * π ⟨u, htY⟩ = π ⟨t * u, haY⟩
    rw [← map_mul]
    rfl
  have hzt : t * u = u * t := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  have hztne : t ≠ u := T8.ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hab1 : π ⟨t * u, haY⟩ ≠ 1 := by
    intro h1
    have hmem := (QuotientGroup.eq_one_iff _).mp h1
    have hne1 : (⟨t * u, haY⟩ : ↥(layerY Ω (t * u))) ≠ 1 := by
      intro e
      apply hztne
      have e' : t * u = 1 := congrArg Subtype.val e
      calc t = t * u * u := by rw [mul_assoc, hs.ht.sq, mul_one]
        _ = u := by rw [e', one_mul]
    have hsq : (⟨t * u, haY⟩ : ↥(layerY Ω (t * u))) * ⟨t * u, haY⟩ = 1 := by
      apply Subtype.ext
      show t * u * (t * u) = 1
      calc t * u * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [← hzt]
        _ = (t * t) * (u * u) := by group
        _ = 1 := by rw [hs.hz.sq, hs.ht.sq, mul_one]
    exact hne1 (eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card _) hmem
      (Balance.isPGroup_zpowers_of_mul_self_eq_one hsq))
  have hne : x ≠ x' := by
    intro e
    apply hab1
    rw [← hxx', ← e, hx.sq]
    rfl
  have hnO2 : ¬ ∃ Q : Subgroup ↥X, Q.Normal ∧ IsPGroup 2 ↥Q ∧ x ∈ Q := by
    rintro ⟨Q, hQn, hQ2, hxQ⟩
    apply hO2
    refine ⟨Q, hQn, hQ2, fun c hcz => ?_⟩
    obtain ⟨w, hw, hwc⟩ := hcz
    have hw' : (w : Y) ∈ Subgroup.zpowers t := Subgroup.mem_subgroupOf.mp hw
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
    have hwm : w = (⟨t, hzY⟩ : ↥(layerY Ω (t * u))) ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hm]
    have hcm : c = x ^ m := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hwc, hwm, map_zpow]
    rw [hcm]
    exact Q.zpow_mem hxQ m
  obtain ⟨QK, hQK, hQKfix⟩ := hσ.fixK
  have hσK : (secImg Ω (t * u) K).map σ.toMonoidHom = secImg Ω (t * u) K :=
    eq_of_isSylow2In_le hΦ hKb (hσ.perm _ hKb) hQK fun y hy => ⟨y, hQK.1 hy, hQKfix y hy⟩
  have hσX : X.map σ.toMonoidHom = X := orbGrp_map_eq_of_top omegaGen_secFam σ hσK
  have hσσx : ∀ y, σ (σ y) = y := fun y =>
    congrArg (fun τ : MulAut (SecQuot Ω (t * u)) => τ y) hσ.sq
  have hσmem : ∀ y ∈ X, σ y ∈ X := fun y hy => by
    rw [← hσX]
    exact ⟨y, hy, rfl⟩
  let σ' : MulAut ↥X :=
    { toFun := fun y => ⟨σ y, hσmem y y.2⟩
      invFun := fun y => ⟨σ y, hσmem y y.2⟩
      left_inv := fun y => Subtype.ext (hσσx y)
      right_inv := fun y => Subtype.ext (hσσx y)
      map_mul' := fun y z => Subtype.ext (map_mul σ (y : SecQuot Ω (t * u)) z) }
  refine ⟨x, x', σ', ⟨⟨hΦX, hOX, hA, hAB, hx, hx', hne, hcen, hgenA, hnO2⟩, ?_, ?_, ?_, ?_⟩,
    fun c => ?_, fun c => rfl⟩
  ·
    rintro _ ⟨M, hM, hMX, rfl⟩
    have hMσX : M.map σ.toMonoidHom ≤ X := by
      rw [← hσX]
      exact Subgroup.map_mono hMX
    refine ⟨M.map σ.toMonoidHom, hσ.perm M hM, hMσX, ?_⟩
    ext c
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
    · intro hc
      obtain ⟨m', hm', hm'c⟩ := Subgroup.mem_subgroupOf.mp hc
      exact ⟨⟨m', hMX hm'⟩, Subgroup.mem_subgroupOf.mpr hm', Subtype.ext hm'c⟩
  · exact MulEquiv.ext fun y => Subtype.ext (hσσx y)
  · exact ⟨QK.subgroupOf X, hQK.subgroupOf hKX, fun y hy =>
      Subtype.ext (hQKfix _ (Subgroup.mem_subgroupOf.mp hy))⟩
  · obtain ⟨QJ, hQJ, hQJn, hQJf⟩ := hσ.onJ
    refine ⟨QJ.subgroupOf X, hQJ.subgroupOf hJX, fun y hy => ?_, fun y hy hfix => ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hQJn _ (Subgroup.mem_subgroupOf.mp hy))
    · exact Subtype.ext (hQJf _ (Subgroup.mem_subgroupOf.mp hy) (congrArg Subtype.val hfix))
  ·
    constructor
    · intro hc
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      refine ⟨(⟨t * u, haY⟩ : ↥(layerY Ω (t * u))) ^ m, ?_, ?_⟩
      · show (⟨t * u, haY⟩ : ↥(layerY Ω (t * u))) ^ m ∈
          (Subgroup.zpowers (t * u)).subgroupOf (layerY Ω (t * u))
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_zpow]
        exact Subgroup.zpow_mem_zpowers _ m
      · rw [map_zpow, Subgroup.coe_zpow, hxx']
    · rintro ⟨w, hw, hwc⟩
      have hw' : (w : Y) ∈ Subgroup.zpowers (t * u) := Subgroup.mem_subgroupOf.mp hw
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hw'
      have hwm : w = (⟨t * u, haY⟩ : ↥(layerY Ω (t * u))) ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, ← hm]
      have hcm : c = (x * x') ^ m := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow, hxx', ← hwc, hwm, map_zpow]
      rw [hcm]
      exact Subgroup.zpow_mem_zpowers _ m

theorem std8_false_of_three_secOrb (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    {P₂ L₁ L₂ L₃ : Subgroup ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))}
    (hP₂ : IsPGroup 2 ↥P₂)
    (h₁ : L₁ ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
    (h₂ : L₂ ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
    (h₃ : L₃ ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
      (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)))
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) (hc₁ : 2 < Nat.card ↥(L₁ ⊓ P₂))
    (hc₂ : 2 < Nat.card ↥(L₂ ⊓ P₂)) (hc₃ : 2 < Nat.card ↥(L₃ ⊓ P₂)) : False := by
  have key : ∀ {L : Subgroup
      ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))},
      L ∈ restrictFamily (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)) →
      ∃ M : Subgroup Y, XMem (CoreAssembly.conjClass (tightCore R)) (t * u) M ∧
        (secImg (CoreAssembly.conjClass (tightCore R)) (t * u) M).subgroupOf
          (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)) = L ∧
        Nat.card ↥(L ⊓ P₂) = Nat.card ↥(secImg (CoreAssembly.conjClass (tightCore R)) (t * u) M ⊓
          P₂.map (Subgroup.subtype _)) := by
    intro L hL
    obtain ⟨M, hM, hMX, rfl⟩ := exists_xMem_of_mem_restrictFamily hL
    refine ⟨M, hM, rfl, ?_⟩
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Subgroup.map_inf_eq _ _ _ (Subgroup.subtype_injective _),
      Subgroup.map_subgroupOf_eq_of_le hMX]
  obtain ⟨M₁, hM₁, e₁, hk₁⟩ := key h₁
  obtain ⟨M₂, hM₂, e₂, hk₂⟩ := key h₂
  obtain ⟨M₃, hM₃, e₃, hk₃⟩ := key h₃
  exact false_of_three_secImg_of hs.partIHypG hthree hM₁ hM₂ hM₃
    (fun e => h12 (by rw [← e₁, ← e₂, e])) (fun e => h13 (by rw [← e₁, ← e₃, e]))
    (fun e => h23 (by rw [← e₂, ← e₃, e])) (hP₂.map (Subgroup.subtype _))
    (lt_of_lt_of_eq hc₁ hk₁) (lt_of_lt_of_eq hc₂ hk₂) (lt_of_lt_of_eq hc₃ hk₃)

theorem std8_false_of_twinE4 (hg : Z2GapFacts) (h4 : Thm4RBelow 3 n) (hs : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R)))
    {σ : MulAut (SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u))}
    (hσ : SPropSec (CoreAssembly.conjClass (tightCore R)) (t * u) (tightCore R) J σ)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t)
    (hE4 : TwinE4 ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
    False := by
  obtain ⟨k, k', σ', hT, -, -⟩ := std8_twinSProp3 h4 hs hcj hO2 hσ
  obtain ⟨Q, _, f, hf, hker, hQ | hQ⟩ := hE4
  · exact hg.sp62 _ _ _ _ _ _ σ' hT Q f hf hker hQ
  · obtain ⟨P₂, L₁, L₂, L₃, hP₂, h₁, h₂, h₃, h12, h13, h23, hc₁, hc₂, hc₃⟩ :=
      hg.o8p2 _ _ _ _ _ _ hT.toTwinBase3 Q f hf hker hQ
    exact std8_false_of_three_secOrb hs hthree hP₂ h₁ h₂ h₃ h12 h13 h23 hc₁ hc₂ hc₃

theorem Z2Set.exists_lift_fixSyl (hs : Z2Set n R S t J u R₀ T₀ P) {s : Y}
    (hsa : s ∈ Subgroup.centralizer ({t * u} : Set Y)) (hs2 : s * s = 1)
    (hsR : R₀ ≤ Subgroup.centralizer ({s} : Set Y)) (hsT : s ∈ Subgroup.normalizer (T₀ : Set Y))
    (hsZ : ∀ x ∈ T₀, x * s = s * x → x * x = 1) {h : Y} (hh : h * u * h⁻¹ = s)
    {σ' : MulAut ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))}
    (hσ' : ∀ c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)),
      ((σ' c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
        SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) =
          secAct hs.large.datum.hypOmegaGen.conjInvariant hsa c)
    (hL : ∃ (B : Subgroup ↥(fixSylGen (restrictFamily
        (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) σ')) (_ : B.Normal),
      LieModel (↥(fixSylGen (restrictFamily
        (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) σ') ⧸ B)
          .PSL 3 3 1) :
    ∃ (L : Subgroup Y) (B : Subgroup ↥L) (_ : B.Normal),
      L ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s ⊔ conjSub h J ∧
        LieModel (↥L ⧸ B) .PSL 3 3 1 := by
  obtain ⟨B, hBn, hB⟩ := hL
  have hTR : TypeRFam 3 (CoreAssembly.conjClass (tightCore R)) := TightLargeHypR.typeRFam hs.large
  have hJh : IsUniqueInvolution (conjSub h J) s := by
    rw [← hh]
    exact hs.hu.conj h
  obtain ⟨L, ψ, hψ, hLK⟩ := exists_lift_fixSylGen hTR hs.large.datum.hypOmegaGen.conjInvariant
    hsa hs2 hσ' (hTR.hyp.conjInvariant h J hs.hJ.1) hJh
  have hψ' : Function.Surjective ((QuotientGroup.mk' B).comp ψ) :=
    (QuotientGroup.mk'_surjective B).comp hψ
  exact ⟨L, ((QuotientGroup.mk' B).comp ψ).ker, inferInstance, hLK,
    LieModel.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective _ hψ').symm hB⟩

theorem Z2Set.not_lieModel_L33_of_le (hs : Z2Set n R S t J u R₀ T₀ P) {s h : Y}
    (hh : h * u * h⁻¹ = s) (L : Subgroup Y)
    (hL : L ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s ⊔ conjSub h J)
    (B : Subgroup ↥L) (_ : B.Normal) : ¬ LieModel (↥L ⧸ B) .PSL 3 3 1 := by
  intro hLie
  classical
  have hTR : TypeRFam 3 (CoreAssembly.conjClass (tightCore R)) := TightLargeHypR.typeRFam hs.large
  have hcl := hTR.hyp.conjInvariant
  obtain ⟨g, hg⟩ := hs.hJ.1
  have hg' : conjSub g (tightCore R) = J := hg
  have hgu : u = g * t * g⁻¹ := by
    have h1 := hs.large.datum.isUniqueInvolution_core.conj g
    rw [hg'] at h1
    exact hs.hu.eq h1
  have hJh : conjSub h J = conjSub (h * g) (tightCore R) := by rw [← hg', conjSub_mul]
  have hsc : (h * g) * t * (h * g)⁻¹ = s := by rw [← hh, hgu]; group
  have hΛ : linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s =
      conjSub (h * g) (linkLayer R t) := by
    rw [conjSub_linkLayerAt hcl (h * g), ← hJh, hsc]
  haveI : IsSimpleGroup (↥L ⧸ B) :=
    (LieType.Simplicity.fam_PSL_simplicity _ 3 3 1 (hLie.statedClassicalModel (by decide))).2
  have hcard : Nat.card (↥L ⧸ B) = 5616 := modelCardL33_proved _ hLie
  have hJhs : IsUniqueInvolution (conjSub h J) s := by
    rw [← hh]
    exact hs.hu.conj h
  have hJhN : conjSub h J ≤ Subgroup.normalizer
      (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s : Set Y) := by
    intro x hx
    have hxs : x ∈ Subgroup.centralizer ({s} : Set Y) :=
      S1916.normalizer_le_centralizer_of_isUniqueInvolution hJhs (Subgroup.le_normalizer hx)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact conj_mem_linkLayerAt hcl hxs (conjSub_eq_self_of_mem hx) hy
    · intro hy
      have h1 := conj_mem_linkLayerAt hcl ((Subgroup.centralizer _).inv_mem hxs)
        (conjSub_eq_self_of_mem ((conjSub h J).inv_mem hx)) hy
      have e : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hLN : L ≤ Subgroup.normalizer
      (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s : Set Y) :=
    hL.trans (sup_le Subgroup.le_normalizer hJhN)
  have hNn : ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s).subgroupOf
      (Subgroup.normalizer
        (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s : Set Y))).Normal :=
    Subgroup.normal_in_normalizer
  set Λ := linkLayerAt (CoreAssembly.conjClass (tightCore R)) (conjSub h J) s with hΛdef
  set Nz := Subgroup.normalizer (Λ : Set Y) with hNzdef
  set f := QuotientGroup.mk' (Λ.subgroupOf Nz) with hfdef
  set φ : ↥L →* Nz ⧸ Λ.subgroupOf Nz := f.comp (Subgroup.inclusion hLN) with hφdef
  have hker : ∀ l : ↥L, l ∈ φ.ker ↔ (l : Y) ∈ Λ := by
    intro l
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' (Λ.subgroupOf Nz) (Subgroup.inclusion hLN l) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hKn : (φ.ker.map (QuotientGroup.mk' B)).Normal :=
    (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map (QuotientGroup.mk' B)) with hbot | htop
  ·
    have hle : φ.ker ≤ B := by
      intro l hl
      have h1 : QuotientGroup.mk' B l ∈ φ.ker.map (QuotientGroup.mk' B) :=
        Subgroup.mem_map_of_mem _ hl
      rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h1 : Nat.card (↥L ⧸ B) ∣ Nat.card φ.range := by
      rw [← Subgroup.index_ker]
      exact Subgroup.index_dvd_of_le hle
    have h2 : φ.range ≤ ((conjSub h J).subgroupOf Nz).map f := by
      have hT : Λ ⊔ conjSub h J ≤
          ((((conjSub h J).subgroupOf Nz).map f).comap f).map Nz.subtype := by
        refine sup_le (fun y hy => ⟨⟨y, Subgroup.le_normalizer hy⟩, ?_, rfl⟩)
          (fun y hy => ⟨⟨y, hJhN hy⟩, ?_, rfl⟩)
        · show f ⟨y, Subgroup.le_normalizer hy⟩ ∈ ((conjSub h J).subgroupOf Nz).map f
          have e : f ⟨y, Subgroup.le_normalizer hy⟩ = 1 :=
            (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hy)
          rw [e]
          exact Subgroup.one_mem _
        · exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hy)
      rintro _ ⟨l, rfl⟩
      obtain ⟨y, hy, hyl⟩ := hT (hL l.2)
      have e : y = Subgroup.inclusion hLN l := Subtype.ext hyl
      rw [e] at hy
      exact hy
    have h3 : Nat.card ↥(((conjSub h J).subgroupOf Nz).map f) ∣ Nat.card ↥(conjSub h J) := by
      have hd := Subgroup.card_map_dvd ((conjSub h J).subgroupOf Nz) f
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJhN).toEquiv] at hd
    have h16 : 16 ∣ Nat.card ↥(conjSub h J) := by
      have hd := (h1.trans (Subgroup.card_dvd_of_le h2)).trans h3
      rw [hcard] at hd
      exact (show (16 : ℕ) ∣ 5616 by norm_num).trans hd
    exact not_sixteen_dvd_natCard hTR (hcl h J hs.hJ.1) h16
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' B).comp φ.ker.subtype) := by
      intro q
      have hq : q ∈ φ.ker.map (QuotientGroup.mk' B) := by
        rw [htop]
        exact Subgroup.mem_top q
      obtain ⟨k, hk, rfl⟩ := hq
      exact ⟨⟨k, hk⟩, rfl⟩
    have hmemΛt : ∀ k : ↥φ.ker, (h * g)⁻¹ * ((k : ↥L) : Y) * (h * g) ∈ linkLayer R t := by
      intro k
      exact mem_conjSub_iff.mp (hΛ.le ((hker k).mp k.2))
    let j : ↥φ.ker →* ↥(linkLayer R t) :=
      { toFun := fun k => ⟨(h * g)⁻¹ * ((k : ↥L) : Y) * (h * g), hmemΛt k⟩
        map_one' := by
          apply Subtype.ext
          show (h * g)⁻¹ * 1 * (h * g) = 1
          group
        map_mul' := fun a b => by
          apply Subtype.ext
          show (h * g)⁻¹ * (((a : ↥L) : Y) * ((b : ↥L) : Y)) * (h * g) =
            (h * g)⁻¹ * ((a : ↥L) : Y) * (h * g) * ((h * g)⁻¹ * ((b : ↥L) : Y) * (h * g))
          group }
    have hj : Function.Injective j := by
      intro a b hab
      have e : (h * g)⁻¹ * ((a : ↥L) : Y) * (h * g) = (h * g)⁻¹ * ((b : ↥L) : Y) * (h * g) :=
        congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (by simpa using e))
    have hodd : Odd (Nat.card ((linkLayerHom' hs.large).comp j).ker) := by
      have hle : ((linkLayerHom' hs.large).comp j).ker.map j ≤ (linkLayerHom' hs.large).ker := by
        rintro _ ⟨k, hk, rfl⟩
        exact hk
      rw [ker_linkLayerHom] at hle
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective hj] at h1
      exact (CFSG.ComponentClassification.OddCore.odd_card _).of_dvd_nat h1
    have heven : Even (Nat.card (↥L ⧸ B)) := by
      rw [hcard]
      decide
    obtain ⟨ψ, hψ⟩ := C264Om.exists_surj_range_of_odd_ker ((linkLayerHom' hs.large).comp j) _ hsurj
      heven hodd
    have hL' : LieModel (↥((linkLayerHom' hs.large).comp j).range ⧸ ψ.ker) .PSL 3 3 1 :=
      LieModel.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm hLie
    obtain ⟨p, f', hp, hp2, hf, -, hk⟩ := hs.model
    exact modelL33NotSectionL2_proved _ hs.simple hs.index p f' hp hp2 hf hk _ ψ.ker
      inferInstance hL'

theorem Z2Set.false_of_fixSyl_L33 (hs : Z2Set n R S t J u R₀ T₀ P) {s : Y}
    (hsa : s ∈ Subgroup.centralizer ({t * u} : Set Y)) (hs2 : s * s = 1)
    (hsR : R₀ ≤ Subgroup.centralizer ({s} : Set Y)) (hsT : s ∈ Subgroup.normalizer (T₀ : Set Y))
    (hsZ : ∀ x ∈ T₀, x * s = s * x → x * x = 1) {h : Y} (hh : h * u * h⁻¹ = s)
    {σ' : MulAut ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))}
    (hσ' : ∀ c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)),
      ((σ' c : ↥(secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) :
        SecQuot (CoreAssembly.conjClass (tightCore R)) (t * u)) =
          secAct hs.large.datum.hypOmegaGen.conjInvariant hsa c)
    (hL : ∃ (B : Subgroup ↥(fixSylGen (restrictFamily
        (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) σ')) (_ : B.Normal),
      LieModel (↥(fixSylGen (restrictFamily
        (secFam (CoreAssembly.conjClass (tightCore R)) (t * u))
        (secOrb (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u))) σ') ⧸ B)
          .PSL 3 3 1) : False := by
  obtain ⟨L, B, hB, hLle, hLie⟩ := hs.exists_lift_fixSyl hsa hs2 hsR hsT hsZ hh hσ' hL
  exact hs.not_lieModel_L33_of_le hh L hLle B hB hLie

theorem std8_false_of_secTwinOmega (hg : Z2GapFacts) (hs : Z2Set n R S t J u R₀ T₀ P) (h4 : Thm4RBelow 3 n)
    (hs8 : TightStd8R 3 n R S t J P R₀ T₀ W u)
    (hthree : NoThreeMeetSylow (CoreAssembly.conjClass (tightCore R))) {s : Y}
    (hsa : s ∈ Subgroup.centralizer ({t * u} : Set Y)) (hs2 : s * s = 1)
    (hsR : R₀ ≤ Subgroup.centralizer ({s} : Set Y)) (hsT : s ∈ Subgroup.normalizer (T₀ : Set Y))
    (hsZ : ∀ x ∈ T₀, x * s = s * x → x * x = 1) {h : Y} (hh : h * u * h⁻¹ = s)
    (hcj : SecConj264 (CoreAssembly.conjClass (tightCore R)) (tightCore R) J (t * u))
    (hO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u) t)
    (hom : SecTwinOmegaF (CoreAssembly.conjClass (tightCore R)) (tightCore R) (t * u)) :
    False := by
  have hσ := hs.sPropSec_of_s hsa hs2 hsR hsT hsZ
  obtain ⟨k, k', σ', hT, hcyc, hσ'⟩ := std8_twinSProp3 h4 hs8 hcj hO2 hσ
  obtain ⟨N, hNn, -, -, hNiff, -, d, ε, hcov⟩ := hom
  have hN : N = Subgroup.zpowers (k * k') := by
    ext c
    rw [hNiff c, hcyc c]
  have hsmall := hg.small _ _ _ _ _ _ σ' hT N hNn hN
  by_cases hd : 9 ≤ d ∨ (d = 8 ∧ ε = true)
  ·
    obtain ⟨P₂, L₁, L₂, L₃, hP₂, h₁, h₂, h₃, h12, h13, h23, hc₁, hc₂, hc₃⟩ :=
      gapOmegaLargeF_of hg.orth _ _ _ _ _ _ hT.toTwinBase3 N hNn hN d ε hd hcov
    exact std8_false_of_three_secOrb hs8 hthree hP₂ h₁ h₂ h₃ h12 h13 h23 hc₁ hc₂ hc₃
  ·
    have hd9 : ¬ 9 ≤ d := fun h9 => hd (Or.inl h9)
    obtain ⟨M₀, hKM, hOT⟩ := hcov
    obtain ⟨t', k₀, hOrth, hM⟩ := TQ.lieModel_of_hasOrthTypeU
      (hT.toTwinBase3.omegaGen_conjClass_eq_top hKM) (hT.toTwinBase3.exists_ne_comm_quot hN) hOT
    rcases hOrth with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
        ⟨h7, -, rfl, hk⟩ | ⟨h8, -, rfl, rfl, hk⟩ | ⟨h8, -, rfl, rfl, hk⟩
    · exact hsmall (Or.inl hM)
    · exact hs.false_of_fixSyl_L33 hsa hs2 hsR hsT hsZ hh hσ'
        (hg.l43 _ _ _ _ _ _ σ' hT N hNn hN hM)
    · exact hsmall (Or.inr (Or.inl hM))
    · obtain rfl : k₀ = 3 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inl hM)))
    · exact hd (Or.inr ⟨by omega, rfl⟩)
    · obtain rfl : k₀ = 4 := by omega
      exact hsmall (Or.inr (Or.inr (Or.inr hM)))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W
