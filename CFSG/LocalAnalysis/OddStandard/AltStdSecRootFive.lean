module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootFivePerm
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootConj
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS2
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS3

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal CFSG.ComponentClassification.RestrictedStd.Spor Equiv

section Odd

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))

theorem corr_le_oddCoreOf_of_comm_odd {T : Subgroup (Perm (Fin n))}
    (hTA : T ≤ alternatingGroup (Fin n)) (hcomm : ∀ g ∈ T, ∀ h ∈ T, g * h = h * g)
    (hodd : Odd (Nat.card T)) :
    corr (X := G) e T ≤ oddCoreOf (centralizer (corr (X := G) e T : Set G)) := by
  set R : Subgroup G := corr (X := G) e T with hR
  have hRabel : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := corr_comm e hcomm
  have hRC : R ≤ centralizer (R : Set G) := fun r hr => by
    rw [mem_centralizer_iff]
    intro r' hr'
    exact hRabel r' hr' r hr
  let N₀ : Subgroup ↥(centralizer (R : Set G)) := R.subgroupOf (centralizer (R : Set G))
  have hN₀ : N₀.Normal := by
    refine ⟨fun m hm x => ?_⟩
    have hm' : (m : G) ∈ R := hm
    have hx : ((x : G)) ∈ centralizer (R : Set G) := x.2
    have hc : (m : G) * x = x * m := mem_centralizer_iff.1 hx _ hm'
    show (x : G) * m * (x : G)⁻¹ ∈ R
    rw [mul_inv_eq_iff_eq_mul.2 hc.symm]
    exact hm'
  have hcard : Nat.card N₀ = Nat.card T := by
    have h1 : Nat.card N₀ = Nat.card R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv
    have h2 : Nat.card R = Nat.card T := Nat.card_congr (corrEquiv (X := G) e hTA).toEquiv
    rw [h1, h2]
  have hodd' : Odd (Nat.card N₀) := by rw [hcard]; exact hodd
  have hle : N₀ ≤ CFSG.oddCore ↥(centralizer (R : Set G)) := le_sSup ⟨hN₀, hodd'⟩
  intro x hx
  exact ⟨⟨x, hRC hx⟩, hle (show (⟨x, hRC hx⟩ : ↥(centralizer (R : Set G))) ∈ N₀ from hx), rfl⟩

theorem corr_zpowers_eq {c : Perm (Fin n)} (hc : c ∈ alternatingGroup (Fin n)) :
    corr (X := G) e (zpowers c) = zpowers ((e.symm ⟨c, hc⟩ : L) : G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxL, hmem⟩ := mem_corr.1 hx
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have h1 : e ⟨x, hxL⟩ = ⟨c, hc⟩ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
    have h2 : (⟨x, hxL⟩ : L) = (e.symm ⟨c, hc⟩) ^ k := by
      rw [← map_zpow, ← h1]
      simp
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val h2.symm⟩
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    refine mem_corr_of_mem (a := (e.symm ⟨c, hc⟩) ^ k) ?_
    rw [map_zpow]
    simp

end Odd

section Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem exists_decomp_commute_five {c : Perm (Fin n)} (hc : c.IsCycle)
    (hcA : c ∈ alternatingGroup (Fin n)) {σ : Perm (Fin n)} (hσc : σ * c = c * σ)
    (hσA : σ ∈ alternatingGroup (Fin n)) :
    ∃ r ∈ zpowers c, ∃ s ∈ altSub (c.support)ᶜ, σ = s * r := by
  obtain ⟨hc', hr⟩ := (hc.commute_iff).1 hσc
  set r : Perm (Fin n) := Perm.ofSubtype (σ.subtypePerm hc') with hrdef
  have hrA : r ∈ alternatingGroup (Fin n) := (zpowers_le.2 hcA) hr
  have hrσ : ∀ i ∈ c.support, r i = σ i := fun i hi => by
    rw [hrdef, Perm.ofSubtype_apply_of_mem _ hi]
    rfl
  have hs : r⁻¹ * σ ∈ altSub (c.support)ᶜ := by
    refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
    · have h1 := Perm.mem_alternatingGroup.1 hrA
      have h2 := Perm.mem_alternatingGroup.1 hσA
      rw [Perm.sign_mul, Perm.sign_inv, h1, h2]
      decide
    · have hi' : i ∈ c.support := by simpa using hi
      simp only [Perm.mul_apply]
      rw [← hrσ i hi']
      simp
  have hσr : σ * r = r * σ := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hr
    rw [← hk]
    exact (Commute.zpow_right (show Commute σ c from hσc) k).eq
  refine ⟨r, hr, r⁻¹ * σ, hs, ?_⟩
  calc σ = r⁻¹ * (r * σ) := by group
    _ = r⁻¹ * (σ * r) := by rw [hσr]
    _ = (r⁻¹ * σ) * r := by group

theorem rootData_of_five (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (e : L ≃* alternatingGroup (Fin n)) {c : Perm (Fin n)} (hc : c.IsCycle)
    (h5 : c.support.card = 5) (hn : 14 ≤ n) :
    RootData L z (corr (X := G) e (zpowers c)) (corr (X := G) e (altSub (c.support)ᶜ)) (n - 5) := by
  have hcA : c ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 (rootFive_sign hc h5)
  have hzA : zpowers c ≤ alternatingGroup (Fin n) := zpowers_le.2 hcA
  have hSc : (c.support)ᶜ.card = n - 5 := by rw [Finset.card_compl, Fintype.card_fin, h5]
  have hz := z_mem_centralizer_corr h d e (zpowers c)
  have hcommB : ∀ g ∈ zpowers c, ∀ w ∈ altSub (c.support)ᶜ, g * w = w * g := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    have hwc : w * c = c * w := rootSupp_comm_of_mem_altSub_compl hw
    exact (Commute.zpow_left (show Commute c w from hwc.symm) k).eq
  have hcommZ : ∀ g ∈ zpowers c, ∀ w ∈ zpowers c, g * w = w * g := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
    obtain ⟨l, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow_self c k l).eq
  have hodd : Odd (Nat.card (zpowers c)) := by
    rw [Nat.card_zpowers, rootFive_orderOf hc h5]
    exact ⟨2, rfl⟩
  have hSc4 : 4 ≤ (c.support)ᶜ.card := by omega
  have hfixle : ∀ σ ∈ centralizer ((altSub (c.support)ᶜ : Subgroup (Perm (Fin n))) :
      Set (Perm (Fin n))), σ ∈ centralizer ((zpowers c : Subgroup (Perm (Fin n))) :
        Set (Perm (Fin n))) → σ ∈ zpowers c := by
    intro σ hσ1 hσ2
    have hfix := (mem_centralizer_altSub_iff hSc4).1 hσ1
    have hcomm : σ * c = c * σ := (mem_centralizer_iff.1 hσ2 c (mem_zpowers c)).symm
    exact rootFive_mem_zpowers_of_commute hc hcomm (fun i hi => hfix i (by simpa using hi))
  have hRO : corr (X := G) e (zpowers c) ≤
      oddCoreOf (centralizer (corr (X := G) e (zpowers c) : Set G)) :=
    corr_le_oddCoreOf_of_comm_odd e hzA hcommZ hodd
  refine ⟨hz, ?_, ?_⟩
  · have hn8 : 8 ≤ n := by omega
    have hex := exactShape_of_setting h d hQ2
    have hBA : corr (X := G) e (altSub (c.support)ᶜ) ≤
        L ⊓ centralizer (corr (X := G) e (zpowers c) : Set G) :=
      corr_le_centralizer_corr e hcommB
    obtain ⟨eB⟩ := exists_equiv_corr_altSub (X := G) e (c.support)ᶜ
    have hnorm := hnorm_of_perm e hn8 hex (R' := zpowers c) (T := altSub (c.support)ᶜ) hzA
      (fun σ hσ => mem_normalizer_altSub (T := (c.support)ᶜ) fun i => by
        have hσc : σ * c = c * σ := (mem_centralizer_iff.1 hσ c (mem_zpowers c)).symm
        simp only [Finset.mem_compl]
        exact (Perm.mem_support_iff_of_commute hσc i).not.symm)
    have hcc := (hcc_of_perm_le e hn8 hex hzA (altSub_le_alternatingGroup _) hfixle).trans
      (sup_le_sup_left hRO _)
    have := exactShape_section hex hBA ⟨eB⟩ (by omega) hnorm hcc hz
    rwa [hSc] at this
  · intro c' hcL
    have hcR : (c' : G) ∈ centralizer (corr (X := G) e (zpowers c) : Set G) := c'.2
    have h1 := perm_mem_centralizer_of_mem_centralizer_corr e hzA hcL hcR
    obtain ⟨r, hr, s, hs, hrs⟩ := exists_decomp_commute_five hc hcA
      (σ := ((e ⟨c', hcL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)))
      (mem_centralizer_iff.1 h1 c (mem_zpowers c)).symm (e ⟨c', hcL⟩).2
    have hrA : r ∈ alternatingGroup (Fin n) := hzA hr
    have hsA : s ∈ alternatingGroup (Fin n) := altSub_le_alternatingGroup _ hs
    set cr : L := e.symm ⟨r, hrA⟩ with hcr
    set cs : L := e.symm ⟨s, hsA⟩ with hcs
    have hecr : e cr = ⟨r, hrA⟩ := by simp [hcr]
    have hecs : e cs = ⟨s, hsA⟩ := by simp [hcs]
    have hcr_mem : (cr : G) ∈ corr (X := G) e (zpowers c) :=
      mem_corr_of_mem (by rw [hecr]; exact hr)
    have hcs_mem : (cs : G) ∈ corr (X := G) e (altSub (c.support)ᶜ) :=
      mem_corr_of_mem (by rw [hecs]; exact hs)
    have hceq : (⟨c', hcL⟩ : L) = cs * cr := by
      apply e.injective
      rw [map_mul, hecs, hecr]
      exact Subtype.ext hrs
    have hceqG : (c' : G) = cs * cr := congrArg Subtype.val hceq
    obtain ⟨hcrH, hcrO⟩ := mem_oddCoreOf_iff.1 (hRO hcr_mem)
    have hcsH : (cs : G) ∈ centralizer (corr (X := G) e (zpowers c) : Set G) := by
      have : (cs : G) = c' * (cr : G)⁻¹ := by rw [hceqG]; group
      rw [this]
      exact mul_mem c'.2 (inv_mem hcrH)
    have : c' = ⟨cs, hcsH⟩ * ⟨cr, hcrH⟩ := Subtype.ext hceqG
    rw [this]
    exact mul_mem_sup hcs_mem hcrO

end Data

section Transfer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem conjSub_conjSub_inv (g : G) (H : Subgroup G) : conjSub g (conjSub g⁻¹ H) = H := by
  ext x
  rw [mem_conjSub_iff, mem_conjSub_iff]
  simp [mul_assoc]

theorem isZStar_zpowers_of_five (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 12 ≤ n) {c c' : Perm (Fin n)} (hc : c.IsCycle)
    (h5 : c.support.card = 5) (hc' : c'.IsCycle) (h5' : c'.support.card = 5)
    (hz : IsZStar (corr (X := G) e (zpowers c)) z) :
    IsZStar (corr (X := G) e (zpowers c')) z := by
  obtain ⟨σ, hσ, hσc⟩ := rootFive_exists_even_conj hn hc h5 hc' h5'
  set l : L := e.symm ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩ with hl
  have hlz : (l : G) * z * (l : G)⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (le_centralizer_single h d l.2)
    rw [this]
    group
  have hel : ((e l : alternatingGroup (Fin n)) : Perm (Fin n)) = σ := by simp [hl]
  have h1 := hz.conj (l : G)
  rw [hlz, conjSub_corr e l, hel] at h1
  have h2 : (zpowers c).map (MulAut.conj σ).toMonoidHom = zpowers c' := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hσc]
  rw [h2] at h1
  exact h1

theorem false_of_zstar_five (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) (hn : 14 ≤ n)
    {y g : G} (hy : y ∈ L) (hy2 : orderOf y = 2) (hg : g * z * g⁻¹ = z * y)
    (hf6 : (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 6)
    {c : Perm (Fin n)} (hc : c.IsCycle) (h5 : c.support.card = 5)
    (hcF : c.support ⊆ fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)))
    (hz : IsZStar (corr (X := G) e (zpowers c)) z) : False := by
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hid : NormalAltIdent n F.card := by
    rw [hf6]
    exact normalAltIdent_of_five_le (by norm_num)
  obtain ⟨F', hcard, hconj⟩ := exists_corr_eq_conj h d hQ2 hE e hy hy2 hg hid
  have hcA : c ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 (rootFive_sign hc h5)
  set xc : G := ((e.symm ⟨c, hcA⟩ : L) : G) with hxc
  have hcF' : c ∈ altSub F := mem_altSub.2 ⟨rootFive_sign hc h5, fun i hi => by
    by_contra hne
    exact hi (hcF (Perm.mem_support.2 hne))⟩
  have hxcN : xc ∈ corr (X := G) e (altSub F) :=
    mem_corr_of_mem (a := e.symm ⟨c, hcA⟩) (by simpa using hcF')
  have hxbar : g⁻¹ * xc * g ∈ corr (X := G) e (altSub F') := by
    rw [← hconj]
    refine mem_conjSub_iff.2 ?_
    have : g * (g⁻¹ * xc * g) * g⁻¹ = xc := by group
    simpa [this] using hxcN
  obtain ⟨hxL', hρ⟩ := mem_corr.1 hxbar
  set ρ : Perm (Fin n) := ((e ⟨g⁻¹ * xc * g, hxL'⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
    with hρdef
  have hρA : ρ ∈ alternatingGroup (Fin n) := (e ⟨g⁻¹ * xc * g, hxL'⟩).2
  have hρ5 : orderOf ρ = 5 := by
    rw [hρdef, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have : g⁻¹ * xc * g = (MulAut.conj g⁻¹) xc := by simp
    rw [this, MulEquiv.orderOf_eq, hxc, Subgroup.orderOf_coe, MulEquiv.orderOf_eq,
      Subgroup.orderOf_mk, rootFive_orderOf hc h5]
  have hρs : ρ.support ⊆ F' := fun i hi => by
    by_contra hiF'
    exact (Perm.mem_support.1 hi) ((mem_altSub.1 hρ).2 i hiF')
  obtain ⟨hρc, hρ5s⟩ := rootFive_isCycle_of_orderOf (by rw [hcard, hf6]) hρ5 hρs
  have hcorr : conjSub g⁻¹ (corr (X := G) e (zpowers c)) = corr (X := G) e (zpowers ρ) := by
    rw [corr_zpowers_eq e hcA, corr_zpowers_eq e hρA]
    have h1 : e.symm ⟨ρ, hρA⟩ = ⟨g⁻¹ * xc * g, hxL'⟩ := by
      have : (⟨ρ, hρA⟩ : alternatingGroup (Fin n)) = e ⟨g⁻¹ * xc * g, hxL'⟩ := rfl
      rw [this, MulEquiv.symm_apply_apply]
    rw [h1]
    unfold conjSub
    rw [MonoidHom.map_zpowers]
    simp [hxc]
  have hRconj : corr (X := G) e (zpowers c) = conjSub g (corr (X := G) e (zpowers ρ)) := by
    rw [← hcorr, conjSub_conjSub_inv]
  have hz₁ : IsZStar (corr (X := G) e (zpowers ρ)) z :=
    isZStar_zpowers_of_five h d e (by omega) hc h5 hρc hρ5s hz
  have hyC : y ∈ centralizer (corr (X := G) e (zpowers c) : Set G) := by
    rw [mem_centralizer_iff]
    intro r hr
    have : r ∈ corr (X := G) e (altSub F) := corr_mono e (zpowers_le.2 hcF') hr
    exact comm_of_mem_corr_of_fix e hy (fun i hi => mem_fixFin.1 hi) this
  have hRD := rootData_of_five h d hQ2 e hc h5 hn
  have h2' : IsZStar (corr (X := G) e (zpowers c)) (z * y) := by
    have := hz₁.conj g
    rw [← hRconj, hg] at this
    exact this
  exact false_of_isZStar_pair d hRD (by omega) hy2 hy hyC hz h2'

end Transfer

section Near

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

omit [Finite G] in
theorem comm_of_perm_comm (e : L ≃* alternatingGroup (Fin n)) {x w : G} (hx : x ∈ L) (hw : w ∈ L)
    (hxw : ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
      ((e ⟨w, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) =
        ((e ⟨w, hw⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) *
          ((e ⟨x, hx⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) : x * w = w * x := by
  have h1 : e (⟨x, hx⟩ * ⟨w, hw⟩) = e (⟨w, hw⟩ * ⟨x, hx⟩) := by
    rw [map_mul, map_mul]
    exact Subtype.ext hxw
  exact congrArg Subtype.val (e.injective h1)

theorem exists_near_ne_six (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hFour : FourExactOuterInput) (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) (e : L ≃* alternatingGroup (Fin n)) (hn : 14 ≤ n)
    {y : G} (hy : y ∈ FusionSet L z)
    (hf6 : (fixFin ((e ⟨y, hy.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card = 6) :
    ∃ (y' : G) (hy' : y' ∈ FusionSet L z),
      4 ≤ (fixFin ((e ⟨y', hy'.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ∧
      (fixFin ((e ⟨y', hy'.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ≠ 6 := by
  obtain ⟨hyL, hy2, g, hg⟩ := hy
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hf6' : F.card = 6 := hf6
  obtain ⟨c, hc, h5, hcF⟩ := rootFive_exists_cycle_in (F := F) (by omega)
  have hRD := rootData_of_five h d hQ2 e hc h5 hn
  have hcA : c ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 (rootFive_sign hc h5)
  have hR1 : ∃ r ∈ corr (X := G) e (zpowers c), r ≠ 1 := by
    refine ⟨((e.symm ⟨c, hcA⟩ : L) : G), mem_corr_of_mem (a := e.symm ⟨c, hcA⟩)
      (by simp), ?_⟩
    intro h1
    have h2 : (e.symm ⟨c, hcA⟩ : L) = 1 := Subtype.ext h1
    have h3 : (⟨c, hcA⟩ : alternatingGroup (Fin n)) = 1 := by simpa using congrArg e h2
    exact hc.ne_one (congrArg Subtype.val h3)
  rcases zstar_or_wreath_of_rootData hlookup hHN hFour h d hQ2 hE hRD (by omega) hR1 with hz | hW
  · exact (false_of_zstar_five h d hQ2 hE e hn hyL hy2 hg hf6' hc h5 hcF hz).elim
  · obtain ⟨b', hb'2, hb'sign, hb'1, hb'S, hb'card⟩ := rootFive_exists_involution hn h5
    have hb'A : b' ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 hb'sign
    set b : G := ((e.symm ⟨b', hb'A⟩ : L) : G) with hb
    have hbL : b ∈ L := (e.symm ⟨b', hb'A⟩).2
    have heb : e ⟨b, hbL⟩ = ⟨b', hb'A⟩ := by
      have : (⟨b, hbL⟩ : L) = e.symm ⟨b', hb'A⟩ := rfl
      rw [this, MulEquiv.apply_symm_apply]
    have hb'ord : orderOf b' = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hb'2) hb'1
    have hb2 : orderOf b = 2 := by
      rw [hb, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hb'ord
    have hb'comm : b' * c = c * b' := by
      refine rootSupp_comm_of_mem_altSub_compl (t := c) (mem_altSub.2 ⟨hb'sign, fun i hi => ?_⟩)
      exact hb'S i (by simpa using hi)
    have hbC : b ∈ centralizer (corr (X := G) e (zpowers c) : Set G) := by
      rw [mem_centralizer_iff]
      intro r hr
      obtain ⟨hrL, hrT⟩ := mem_corr.1 hr
      refine comm_of_perm_comm e hrL hbL ?_
      rw [heb]
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hrT
      rw [← hk]
      exact (Commute.zpow_left (show Commute c b' from hb'comm.symm) k).eq
    obtain ⟨h', -, hh'⟩ := wreath_fusion_of_rootData h d hRD (by omega) hW hbL hbC hb2
    have hbY : b ∈ FusionSet L z := ⟨hbL, hb2, h', hh'⟩
    have hcard : (fixFin ((e ⟨b, hbY.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card =
        (Finset.univ.filter fun i => b' i = i).card := by
      have : (e ⟨b, hbY.1⟩ : alternatingGroup (Fin n)) = ⟨b', hb'A⟩ := heb
      rw [this]
      rfl
    refine ⟨b, hbY, ?_, ?_⟩ <;> rw [hcard] <;> omega

end Near

end CFSG.OddStandard.AltStdSec
