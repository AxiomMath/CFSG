module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Setup
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Basic
public import CFSG.LargeExtraspecial.S10Conj
public import CFSG.CGT.PushingUpLit.CGT6.Diag.S2Transfer
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5
  CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}
variable (D : S5.SwapData S g)

theorem SwapW4.chi_ker_le_center (W : SwapW4 D) : D.chi.ker ≤ Subgroup.center D.Z :=
  CFSG.ComponentClassification.SwappedQuasisimpleProduct.diagonal_kernel_central D.Z
    (MulAut.conj D.t) D.commutator_eq_bot

theorem SwapW4.chi_injective (W : SwapW4 D) : Function.Injective D.chi := by
  have hodd : Odd (Nat.card D.chi.ker) := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
    have hycenter : ((y : D.chi.ker) : D.Z) ∈ Subgroup.center D.Z :=
      SwapW4.chi_ker_le_center D W y.2
    have hy2 : (((y : D.chi.ker) : D.Z) : S.O) ^ (2 ^ 1) = 1 := by
      have h1 := pow_orderOf_eq_one (y : D.chi.ker)
      rw [hy] at h1
      have h2 : ((y : D.chi.ker) : D.Z) ^ 2 = 1 := by
        simpa using congrArg Subtype.val h1
      rw [pow_one]
      exact congrArg Subtype.val h2
    have hy1 : (((y : D.chi.ker) : D.Z) : S.O) = 1 :=
      S5.eq_one_of_mem_center_of_pow S D.isComponentOf.2.1 ((y : D.chi.ker) : D.Z).2
        (fun z hz => congrArg Subtype.val
          ((Subgroup.mem_center_iff.mp hycenter) ⟨z, hz⟩).symm) hy2
    have hy1' : ((y : D.chi.ker) : D.Z) = 1 := Subtype.ext hy1
    have hyone : (y : D.chi.ker) = 1 := Subtype.ext hy1'
    rw [hyone, orderOf_one] at hy
    omega
  have hkerEq : D.chiR.ker = D.chi.ker := by
    ext z
    constructor
    · intro hz
      rw [MonoidHom.mem_ker] at hz ⊢
      have := congrArg Subtype.val hz
      simpa [S5.SwapData.coe_chiR] using this
    · intro hz
      rw [MonoidHom.mem_ker] at hz ⊢
      exact Subtype.ext (by simpa [S5.SwapData.coe_chiR] using hz)
  have hoddR : Odd (Nat.card D.chiR.ker) := by rwa [hkerEq]
  have hcR : D.chiR.ker ≤ Subgroup.center D.Z := by
    rw [hkerEq]
    exact SwapW4.chi_ker_le_center D W
  have hkerR : D.chiR.ker = ⊥ := by
    refine CFSG.CGT.PushingUpLit.CGT6.Diag.S2.ker_eq_bot_of_odd_central
      D.isQuasisimple_Z.1 D.chiR hcR hoddR ?_
    intro p hp hpo hdvd
    rw [SwapW4.card_Xhat D W] at hdvd
    have hp2 : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
    have hp7 : p ≤ 7 := by nlinarith
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases Nat.lt_or_ge 2 p with h2 | h2
      · omega
      · have hp2' : p = 2 := by omega
        rw [hp2'] at hpo
        norm_num at hpo
    interval_cases p
    all_goals norm_num at *
  have hker : D.chi.ker = ⊥ := by rwa [← hkerEq]
  rwa [MonoidHom.ker_eq_bot_iff] at hker

theorem SwapW4.chiR_injective (W : SwapW4 D) : Function.Injective D.chiR := by
  have hχ := SwapW4.chi_injective D W
  intro a b hab
  have h : D.chi a = D.chi b := by
    have := congrArg Subtype.val hab
    simpa [S5.SwapData.coe_chiR] using this
  exact hχ h

noncomputable def SwapW4.chiEquiv (W : SwapW4 D) : D.Z ≃* D.Xhat :=
  MulEquiv.ofBijective D.chiR ⟨SwapW4.chiR_injective D W, D.chiR_surjective⟩

theorem SwapW4.card_Z (W : SwapW4 D) : Nat.card D.Z = 60 :=
  (Nat.card_congr (SwapW4.chiEquiv D W).toEquiv).trans (SwapW4.card_Xhat D W)

theorem SwapW4.isSimpleGroup_Z (W : SwapW4 D) : IsSimpleGroup D.Z := by
  obtain ⟨Q, hQ, hR, -, hmin⟩ := SwapW4.exists_form_minus D W
  have hRsimple : IsSimpleGroup (RmodN S g D.t) := by
    rw [hR]
    exact (S8.isSimpleGroup_omegaGroup_minus_four hQ W.h4 hmin).1
  haveI : IsSimpleGroup (RmodN S g D.t) := hRsimple
  haveI : IsSimpleGroup D.Xhat :=
    MulEquiv.isSimpleGroup (SwapW4.xhatEquivRmodN D W)
  exact MulEquiv.isSimpleGroup (SwapW4.chiEquiv D W)

theorem SwapW4.Z_inf_W (W : SwapW4 D) : D.Z ⊓ D.W = ⊥ := by
  have hcenter : Subgroup.center D.Z = ⊥ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.center_eq_bot_of_quasisimple_simple
      D.isQuasisimple_Z (SwapW4.isSimpleGroup_Z D W)
  rw [eq_bot_iff]
  intro x hx
  have hxcenter : (⟨x, hx.1⟩ : D.Z) ∈ Subgroup.center D.Z := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (D.mul_comm_of_mem_W hx.2 y.2).symm
  rw [hcenter] at hxcenter
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxcenter))


theorem SwapW4.card_W (W : SwapW4 D) : Nat.card D.W = 60 := by
  rw [S5.SwapData.W, Subgroup.card_map_of_injective (MulAut.conj D.t).injective]
  exact SwapW4.card_Z D W

theorem SwapW4.card_E2 (W : SwapW4 D) :
    Nat.card (D.Z ⊔ D.W : Subgroup S.O) = 3600 := by
  rw [GL83.CompFam.card_sup_of_commute_of_inf_eq_bot
    (fun x hx y hy => D.mul_comm_of_mem hx hy) (SwapW4.Z_inf_W D W),
    SwapW4.card_Z D W, SwapW4.card_W D W]

theorem SwapW4.mem_E2_iff (W : SwapW4 D) {e : S.O} :
    e ∈ D.Z ⊔ D.W ↔ ∃ z ∈ D.Z, ∃ w ∈ D.W, z * w = e :=
  GL83.CompFam.mem_sup_of_commute (fun x hx y hy => D.mul_comm_of_mem hx hy)

theorem SwapW4.decomp (W : SwapW4 D) {e : S.O} (he : e ∈ D.Z ⊔ D.W) :
    ∃! p : D.Z × D.Z, e = (p.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹) := by
  obtain ⟨z, hz, w, hw, hzw⟩ := (SwapW4.mem_E2_iff D W).mp he
  obtain ⟨z2, hz2, hw_eq⟩ := Subgroup.mem_map.mp hw
  subst hzw
  subst hw_eq
  refine ⟨(⟨z, hz⟩, ⟨z2, hz2⟩), rfl, ?_⟩
  rintro ⟨⟨z1, hz1⟩, ⟨z2', hz2'⟩⟩ h
  change z * (D.t * z2 * D.t⁻¹) = z1 * (D.t * z2' * D.t⁻¹) at h
  have hrel : z⁻¹ * z1 =
      (D.t * z2 * D.t⁻¹) * (D.t * z2' * D.t⁻¹)⁻¹ := by
    calc z⁻¹ * z1
        = z⁻¹ * (z1 * (D.t * z2' * D.t⁻¹)) * (D.t * z2' * D.t⁻¹)⁻¹ := by group
      _ = z⁻¹ * (z * (D.t * z2 * D.t⁻¹)) * (D.t * z2' * D.t⁻¹)⁻¹ := by rw [← h]
      _ = (D.t * z2 * D.t⁻¹) * (D.t * z2' * D.t⁻¹)⁻¹ := by group
  have hmem : z⁻¹ * z1 ∈ D.Z ⊓ D.W := by
    refine ⟨D.Z.mul_mem (D.Z.inv_mem hz) hz1, ?_⟩
    rw [hrel]
    exact D.W.mul_mem (D.conj_mem_W hz2) (D.W.inv_mem (D.conj_mem_W hz2'))
  have hz1eq : z1 = z := by
    have hb := Subgroup.mem_bot.mp (by rwa [SwapW4.Z_inf_W D W] at hmem)
    calc z1 = z * (z⁻¹ * z1) := by group
      _ = z := by rw [hb, mul_one]
  have hAB : D.t * z2 * D.t⁻¹ = D.t * z2' * D.t⁻¹ := by
    rw [hz1eq] at h
    exact mul_left_cancel h
  have hz2eq : z2 = z2' := by
    have h' : z2 * D.t⁻¹ = z2' * D.t⁻¹ := by
      apply mul_left_cancel (a := D.t)
      simpa [mul_assoc] using hAB
    exact mul_right_cancel h'
  exact Prod.ext (Subtype.ext hz1eq) (Subtype.ext hz2eq.symm)

theorem SwapW4.t_not_mem_E2 (W : SwapW4 D) : D.t ∉ D.Z ⊔ D.W := by
  intro ht
  obtain ⟨z, hz, w, hw, hzw⟩ := (SwapW4.mem_E2_iff D W).mp ht
  obtain ⟨z2, hz2, hw_eq⟩ := Subgroup.mem_map.mp hw
  have hle : D.Z.map (MulAut.conj D.t).toMonoidHom ≤ D.Z := by
    rw [← hzw]
    rintro _ ⟨y, hy, rfl⟩
    rw [← hw_eq]
    change (z * (D.t * z2 * D.t⁻¹)) * y * (z * (D.t * z2 * D.t⁻¹))⁻¹ ∈ D.Z
    have hwy : (D.t * z2 * D.t⁻¹) * y * (D.t * z2 * D.t⁻¹)⁻¹ = y := by
      rw [D.mul_comm_of_mem_W (D.conj_mem_W hz2) hy]
      group
    have hcalc : (z * (D.t * z2 * D.t⁻¹)) * y * (z * (D.t * z2 * D.t⁻¹))⁻¹ =
        z * y * z⁻¹ := by
      calc (z * (D.t * z2 * D.t⁻¹)) * y * (z * (D.t * z2 * D.t⁻¹))⁻¹
          = z * ((D.t * z2 * D.t⁻¹) * y * (D.t * z2 * D.t⁻¹)⁻¹) * z⁻¹ := by group
        _ = z * y * z⁻¹ := by rw [hwy]
    rw [hcalc]
    exact D.Z.mul_mem (D.Z.mul_mem hz hy) (D.Z.inv_mem hz)
  have hcard : Nat.card (D.Z.map (MulAut.conj D.t).toMonoidHom) = Nat.card D.Z :=
    Subgroup.card_map_of_injective (MulAut.conj D.t).injective
  exact D.ne (eq_of_le_of_card_ge hle (by rw [hcard]))

theorem SwapW4.E2_inf_centralizer (W : SwapW4 D) :
    (D.Z ⊔ D.W) ⊓ centralizer ({D.t} : Set S.O) = D.Xhat := by
  refine le_antisymm ?_ (D.Xhat_le_sup_inf W.H)
  intro e he
  obtain ⟨p, hp, huniq⟩ := SwapW4.decomp D W he.1
  obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := p
  have het : D.t * e * D.t⁻¹ = e := by
    have hcomm : e * D.t = D.t * e := mem_centralizer_singleton_iff.mp he.2
    calc D.t * e * D.t⁻¹ = e * D.t * D.t⁻¹ := by rw [← hcomm]
      _ = e := by rw [mul_assoc, mul_inv_cancel, mul_one]
  have he2 : e = z2 * (D.t * z1 * D.t⁻¹) := by
    have ht2 : D.t * D.t = 1 := D.t_mul_t W.H
    have hti : D.t⁻¹ = D.t := D.t_inv W.H
    calc e = D.t * e * D.t⁻¹ := het.symm
      _ = D.t * (z1 * (D.t * z2 * D.t⁻¹)) * D.t⁻¹ := by rw [hp]
      _ = (D.t * z1 * D.t⁻¹) * z2 := by
        rw [hti]
        calc D.t * (z1 * (D.t * z2 * D.t)) * D.t
            = D.t * z1 * (D.t * z2 * (D.t * D.t)) := by group
          _ = D.t * z1 * (D.t * z2) := by rw [ht2, mul_one]
          _ = (D.t * z1 * D.t) * z2 := by group
      _ = z2 * (D.t * z1 * D.t⁻¹) := (D.mul_comm_of_mem hz2 (D.conj_mem_W hz1)).symm
  have hpair := huniq (⟨z2, hz2⟩, ⟨z1, hz1⟩) he2
  have hz12 : z1 = z2 := by
    have := congrArg (fun q : D.Z × D.Z => ((q.1 : D.Z) : S.O)) hpair
    simpa using this.symm
  have hp' : e = z2 * (D.t * z2 * D.t⁻¹) := by
    change e = z1 * (D.t * z2 * D.t⁻¹) at hp
    rw [hz12] at hp
    exact hp
  refine ⟨⟨z2, hz2⟩, ?_⟩
  rw [S5.SwapData.chi_apply]
  exact hp'.symm


noncomputable def SwapW4.P (W : SwapW4 D) : Subgroup D.Z :=
  (S.Lbar g ⊓ D.Xhat).comap D.chi

theorem SwapW4.Lbar_eq_sup_Nbar (W : SwapW4 D) :
    S.Lbar g = Nbar S g D.t ⊔ (S.Lbar g ⊓ D.Xhat) := by
  have hcomm : ∀ n ∈ zpowers D.t, ∀ x ∈ D.Xhat, n * x = x * n := by
    intro n hn x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((show Commute x D.t from
      Subgroup.mem_centralizer_singleton_iff.mp
        (D.Xhat_le_centralizer W.H hx)).zpow_right k).eq.symm
  refine le_antisymm ?_ (sup_le (by rw [W.hNzp]; exact zpowers_le.mpr D.mem_Lbar) inf_le_left)
  intro l hl
  have hR : l ∈ Rbar S g D.t := (S4.Lbar_le_Rbar (t := D.t) D.mem_Lbar) hl
  rw [W.hRX] at hR
  obtain ⟨n, hn, x, hx, hnx⟩ := (GL83.CompFam.mem_sup_of_commute hcomm).mp hR
  have hnL : n ∈ S.Lbar g := zpowers_le.mpr D.mem_Lbar hn
  have hxL : x ∈ S.Lbar g := by
    have hx_eq : x = n⁻¹ * l := by rw [← hnx]; group
    rw [hx_eq]
    exact (S.Lbar g).mul_mem ((S.Lbar g).inv_mem hnL) hl
  rw [← hnx]
  exact Subgroup.mul_mem_sup (by rwa [W.hNzp]) ⟨hxL, hx⟩

theorem SwapW4.Lbar_inf_Xhat_card (W : SwapW4 D) :
    Nat.card (S.Lbar g ⊓ D.Xhat : Subgroup S.O) = 4 := by
  have hcomm : ∀ n ∈ zpowers D.t, ∀ x ∈ S.Lbar g ⊓ D.Xhat, n * x = x * n := by
    intro n hn x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ((show Commute x D.t from
      Subgroup.mem_centralizer_singleton_iff.mp
        (D.Xhat_le_centralizer W.H hx.2)).zpow_right k).eq.symm
  have hdisj : Nbar S g D.t ⊓ (S.Lbar g ⊓ D.Xhat) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ D.Xhat ⊓ Nbar S g D.t := ⟨hx.2.2, hx.1⟩
    rwa [W.hXbot] at hx'
  have hcard := GL83.CompFam.card_sup_of_commute_of_inf_eq_bot
    (H := Nbar S g D.t) (K := S.Lbar g ⊓ D.Xhat)
    (fun n hn x hx => hcomm n (by rwa [W.hNzp] at hn) x hx) hdisj
  rw [← SwapW4.Lbar_eq_sup_Nbar D W] at hcard
  have hL8 : Nat.card (S.Lbar g) = 8 := by
    rw [W.C.card_Lbar, W.hw]
    norm_num
  have hN2 : Nat.card (zpowers D.t) = 2 :=
    S7.card_zpowers_eq_two W.H D.mem_Lbar (S5.SwapData.t_ne_one D)
  rw [W.hNzp] at hcard
  rw [hL8, hN2] at hcard
  omega

theorem SwapW4.Lbar_eq (W : SwapW4 D) :
    S.Lbar g = zpowers D.t ⊔ (SwapW4.P D W).map D.chi := by
  rw [SwapW4.Lbar_eq_sup_Nbar D W, W.hNzp]
  congr 1
  exact (Subgroup.map_comap_eq_self (f := D.chi) (H := S.Lbar g ⊓ D.Xhat) inf_le_right).symm

theorem SwapW4.card_P (W : SwapW4 D) : Nat.card (SwapW4.P D W) = 4 := by
  have hmap : (SwapW4.P D W).map D.chi = S.Lbar g ⊓ D.Xhat := by
    rw [SwapW4.P]
    exact Subgroup.map_comap_eq_self (f := D.chi) (H := S.Lbar g ⊓ D.Xhat) inf_le_right
  calc Nat.card (SwapW4.P D W)
      = Nat.card ((SwapW4.P D W).map D.chi) :=
        (Subgroup.card_map_of_injective (SwapW4.chi_injective D W)).symm
    _ = Nat.card (S.Lbar g ⊓ D.Xhat : Subgroup S.O) := by rw [hmap]
    _ = 4 := SwapW4.Lbar_inf_Xhat_card D W



theorem SwapW4.P_map_chi (W : SwapW4 D) :
    (SwapW4.P D W).map D.chi = S.Lbar g ⊓ D.Xhat := by
  rw [SwapW4.P]
  exact Subgroup.map_comap_eq_self (f := D.chi) (H := S.Lbar g ⊓ D.Xhat) inf_le_right

theorem SwapW4.mem_P_iff (W : SwapW4 D) {p : D.Z} :
    p ∈ SwapW4.P D W ↔ D.chi p ∈ S.Lbar g ⊓ D.Xhat := Iff.rfl

theorem SwapW4.P_comm (W : SwapW4 D) {a b : D.Z} (ha : a ∈ SwapW4.P D W)
    (hb : b ∈ SwapW4.P D W) : a * b = b * a := by
  apply SwapW4.chi_injective D W
  rw [map_mul, map_mul]
  have haL : D.chi a ∈ S.Lbar g := by
    have h : D.chi a ∈ (SwapW4.P D W).map D.chi := ⟨a, ha, rfl⟩
    rw [SwapW4.P_map_chi D W] at h
    exact h.1
  have hbL : D.chi b ∈ S.Lbar g := by
    have h : D.chi b ∈ (SwapW4.P D W).map D.chi := ⟨b, hb, rfl⟩
    rw [SwapW4.P_map_chi D W] at h
    exact h.1
  exact S4.Lbar_comm S W.H.conj_mem haL hbL

theorem SwapW4.P_mem_normalizer (W : SwapW4 D) {q : D.Z} (hq : q ∈ SwapW4.P D W) :
    (q : S.O) ∈ normalizer (S.Lbar g : Set S.O) := by
  have hq2 : q * q = 1 := by
    apply SwapW4.chi_injective D W
    rw [map_mul, map_one]
    have hqL : D.chi q ∈ S.Lbar g := by
      have h : D.chi q ∈ (SwapW4.P D W).map D.chi := ⟨q, hq, rfl⟩
      rw [SwapW4.P_map_chi D W] at h
      exact h.1
    exact S4.mul_self_of_mem_Lbar S W.H.conj_mem hqL
  have hq2S : (q : S.O) * (q : S.O) = 1 := congrArg Subtype.val hq2
  have hqinv : (q : S.O)⁻¹ = q := inv_eq_of_mul_eq_one_right hq2S
  have hchiL : D.chi q ∈ S.Lbar g := by
    have h : D.chi q ∈ (SwapW4.P D W).map D.chi := ⟨q, hq, rfl⟩
    rw [SwapW4.P_map_chi D W] at h
    exact h.1
  have hqt : (q : S.O) * D.t * (q : S.O)⁻¹ = D.chi q * D.t := by
    rw [hqinv, S5.SwapData.chi_apply]
    group
  have hBfix : ∀ b ∈ (S.Lbar g ⊓ D.Xhat : Subgroup S.O),
      (q : S.O) * b * (q : S.O)⁻¹ = b := by
    intro b hb
    have hbmap : b ∈ (SwapW4.P D W).map D.chi := by
      rwa [SwapW4.P_map_chi D W]
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hbmap
    rw [S5.SwapData.chi_apply]
    have hqr : (q : S.O) * r = r * q := congrArg Subtype.val (SwapW4.P_comm D W hq hr)
    have hqrt : (q : S.O) * (D.t * r * D.t⁻¹) = (D.t * r * D.t⁻¹) * q :=
      (D.mul_comm_of_mem_W (D.conj_mem_W r.2) q.2).symm
    calc (q : S.O) * (r * (D.t * r * D.t⁻¹)) * (q : S.O)⁻¹
        = ((q : S.O) * r) * (D.t * r * D.t⁻¹) * (q : S.O)⁻¹ := by group
      _ = (r * q) * (D.t * r * D.t⁻¹) * q := by rw [hqr, hqinv]
      _ = r * ((q : S.O) * (D.t * r * D.t⁻¹)) * q := by group
      _ = r * ((D.t * r * D.t⁻¹) * q) * q := by rw [hqrt]
      _ = r * (D.t * r * D.t⁻¹) * (q * q) := by group
      _ = r * (D.t * r * D.t⁻¹) := by rw [hq2S, mul_one]
  have hcommTB : ∀ n ∈ zpowers D.t, ∀ b ∈ (S.Lbar g ⊓ D.Xhat : Subgroup S.O), n * b = b * n := by
    intro n hn b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact S4.Lbar_comm S W.H.conj_mem ((S.Lbar g).zpow_mem D.mem_Lbar k) hb.1
  have hconj : ∀ x ∈ S.Lbar g, (q : S.O) * x * (q : S.O)⁻¹ ∈ S.Lbar g := by
    intro x hx
    have hxsup : x ∈ zpowers D.t ⊔ (S.Lbar g ⊓ D.Xhat) := by
      have hx' : x ∈ Nbar S g D.t ⊔ (S.Lbar g ⊓ D.Xhat) := by
        rw [← SwapW4.Lbar_eq_sup_Nbar D W]
        exact hx
      rwa [W.hNzp] at hx'
    obtain ⟨n, hn, b, hb, hnb⟩ := (GL83.CompFam.mem_sup_of_commute hcommTB).mp hxsup
    have hnconj : (q : S.O) * n * (q : S.O)⁻¹ ∈ S.Lbar g := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← conj_zpow, hqt]
      exact (S.Lbar g).zpow_mem ((S.Lbar g).mul_mem hchiL D.mem_Lbar) k
    have hcalc : (q : S.O) * x * (q : S.O)⁻¹ =
        ((q : S.O) * n * (q : S.O)⁻¹) * ((q : S.O) * b * (q : S.O)⁻¹) := by
      rw [← hnb]; group
    rw [hcalc, hBfix b hb]
    exact (S.Lbar g).mul_mem hnconj hb.1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hconj x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj (q : S.O)).injective]




theorem SwapW4.fix_a_of_mem_P (W : SwapW4 D) {q : D.Z} (hq : q ∈ SwapW4.P D W) :
    ((q : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp
    (show (q : S.O) ∈ S.ρ.range from D.Z_le_Mbar q.2)
  have hkN : S.ρ k ∈ normalizer (S.Lbar g : Set S.O) := by
    rw [hk]
    exact SwapW4.P_mem_normalizer D W hq
  have hfix := S10.fix_cl_of_mem_normalizer W.H hkN
  rwa [hk] at hfix



theorem SwapW4.Lbar_inf_E2 (W : SwapW4 D) :
    S.Lbar g ⊓ (D.Z ⊔ D.W) = S.Lbar g ⊓ D.Xhat := by
  refine le_antisymm ?_ ?_
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hxsup : x ∈ zpowers D.t ⊔ (S.Lbar g ⊓ D.Xhat) := by
      have hx' : x ∈ Nbar S g D.t ⊔ (S.Lbar g ⊓ D.Xhat) := by
        rw [← SwapW4.Lbar_eq_sup_Nbar D W]
        exact hx.1
      rwa [W.hNzp] at hx'
    have hcommTB : ∀ n ∈ zpowers D.t, ∀ b ∈ (S.Lbar g ⊓ D.Xhat : Subgroup S.O),
        n * b = b * n := by
      intro n hn b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      exact S4.Lbar_comm S W.H.conj_mem ((S.Lbar g).zpow_mem D.mem_Lbar k) hb.1
    obtain ⟨n, hn, b, hb, hnb⟩ := (GL83.CompFam.mem_sup_of_commute hcommTB).mp hxsup
    rcases (Setting.mem_zpowers_iff_of_mul_self (D.t_mul_t W.H)).mp hn with rfl | rfl
    · rw [one_mul] at hnb
      rw [← hnb]
      exact hb.2
    · exfalso
      apply SwapW4.t_not_mem_E2 D W
      have hbE2 : b ∈ D.Z ⊔ D.W := (D.Xhat_le_sup_inf W.H).trans inf_le_left hb.2
      have ht : D.t = x * b⁻¹ := by rw [← hnb]; group
      rw [ht]
      exact (D.Z ⊔ D.W).mul_mem hx.2 ((D.Z ⊔ D.W).inv_mem hbE2)
  · exact le_inf inf_le_left (inf_le_right.trans ((D.Xhat_le_sup_inf W.H).trans inf_le_left))



theorem SwapW4.normalizer_E2_decomp (W : SwapW4 D) {e : S.O}
    (he : e ∈ D.Z ⊔ D.W) (hn : e ∈ normalizer (S.Lbar g : Set S.O)) :
    ∃ (p : D.Z) (n : D.Z), p ∈ SwapW4.P D W ∧ e = (p : S.O) * D.chi n ∧
      D.chi n ∈ normalizer ((SwapW4.P D W).map D.chi : Set S.O) := by
  obtain ⟨p0, hp0, _⟩ := SwapW4.decomp D W he
  obtain ⟨⟨z1, hz1⟩, ⟨z2, hz2⟩⟩ := p0
  change e = z1 * (D.t * z2 * D.t⁻¹) at hp0
  let z2Z : D.Z := ⟨z2, hz2⟩
  let u : D.Z := ⟨z1 * z2⁻¹, D.Z.mul_mem hz1 (D.Z.inv_mem hz2)⟩
  have hu_inv : (u⁻¹ : D.Z) = ⟨z2 * z1⁻¹, D.Z.mul_mem hz2 (D.Z.inv_mem hz1)⟩ := rfl
  have huS : (u : S.O) = z1 * z2⁻¹ := rfl
  have hyt : e * D.t * e⁻¹ =
      ((u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹)) * D.t := by
    have hcommW : (D.t * z2 * D.t⁻¹) * z2⁻¹ = z2⁻¹ * (D.t * z2 * D.t⁻¹) :=
      D.mul_comm_of_mem_W (D.conj_mem_W hz2) (D.Z.inv_mem hz2)
    have hcommW' : D.t * z2 * D.t * z2⁻¹ = z2⁻¹ * D.t * z2 * D.t := by
      simpa [D.t_inv W.H, mul_assoc] using hcommW
    simp [hp0, D.t_inv W.H, D.t_mul_t W.H, hcommW', huS, hu_inv, mul_assoc]
    calc D.t * (z2 * (D.t * (z2⁻¹ * (D.t * z1⁻¹))))
        = (D.t * z2 * D.t * z2⁻¹) * (D.t * z1⁻¹) := by group
      _ = (z2⁻¹ * D.t * z2 * D.t) * (D.t * z1⁻¹) := by rw [hcommW']
      _ = z2⁻¹ * D.t * z2 * (D.t * D.t) * z1⁻¹ := by group
      _ = z2⁻¹ * D.t * z2 * z1⁻¹ := by rw [D.t_mul_t W.H, mul_one]
      _ = z2⁻¹ * (D.t * (z2 * z1⁻¹)) := by group
  have hyE2 : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) ∈ D.Z ⊔ D.W :=
    Subgroup.mul_mem_sup u.2 (D.conj_mem_W (u⁻¹).2)
  have hconjL : e * D.t * e⁻¹ ∈ S.Lbar g :=
    (mem_normalizer_iff.mp hn D.t).mp D.mem_Lbar
  have hyL : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) ∈ S.Lbar g := by
    have h := (S.Lbar g).mul_mem hconjL ((S.Lbar g).inv_mem D.mem_Lbar)
    have heq : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) =
        (e * D.t * e⁻¹) * D.t⁻¹ := by rw [hyt]; group
    rw [heq]
    exact h
  have hyB : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) ∈ S.Lbar g ⊓ D.Xhat := by
    have hy' : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) ∈
        S.Lbar g ⊓ (D.Z ⊔ D.W) := ⟨hyL, hyE2⟩
    rwa [SwapW4.Lbar_inf_E2 D W] at hy'
  have hyMap : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) ∈
      (SwapW4.P D W).map D.chi := by
    rwa [SwapW4.P_map_chi D W]
  obtain ⟨p, hpP, hpchi⟩ := Subgroup.mem_map.mp hyMap
  have hu_decomp : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) =
      (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) := rfl
  have hp_decomp : (u : S.O) * (D.t * (u⁻¹ : D.Z) * D.t⁻¹) =
      (p : S.O) * (D.t * (p : S.O) * D.t⁻¹) := by
    rw [← hpchi, S5.SwapData.chi_apply]
  have hpair1 := (SwapW4.decomp D W hyE2).choose_spec.2 (u, u⁻¹) hu_decomp
  have hpair2 := (SwapW4.decomp D W hyE2).choose_spec.2 (p, p) hp_decomp
  have hup : u = p := by
    have h := hpair1.trans hpair2.symm
    exact Subtype.ext (congrArg (fun q : D.Z × D.Z => ((q.1 : D.Z) : S.O)) h)
  have hz1eq : z1 = (p : S.O) * z2 := by
    have h : (u : S.O) = (p : S.O) := congrArg Subtype.val hup
    rw [huS] at h
    calc z1 = (z1 * z2⁻¹) * z2 := by group
      _ = (p : S.O) * z2 := by rw [h]
  have he_eq : e = (p : S.O) * D.chi z2Z := by
    rw [hp0, S5.SwapData.chi_apply, hz1eq]
    simp only [z2Z]
    group
  have hpN : (p : S.O) ∈ normalizer (S.Lbar g : Set S.O) :=
    SwapW4.P_mem_normalizer D W hpP
  have hchiN_L : D.chi z2Z ∈ normalizer (S.Lbar g : Set S.O) := by
    have h : (p : S.O)⁻¹ * e ∈ normalizer (S.Lbar g : Set S.O) :=
      (normalizer (S.Lbar g : Set S.O)).mul_mem
        ((normalizer (S.Lbar g : Set S.O)).inv_mem hpN) hn
    rwa [he_eq, ← mul_assoc, inv_mul_cancel, one_mul] at h
  have hchiN : D.chi z2Z ∈ normalizer ((SwapW4.P D W).map D.chi : Set S.O) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      have hbB : b ∈ S.Lbar g ⊓ D.Xhat := by rwa [SwapW4.P_map_chi D W] at hb
      have hconjL : D.chi z2Z * b * (D.chi z2Z)⁻¹ ∈ S.Lbar g :=
        (mem_normalizer_iff.mp hchiN_L b).mp hbB.1
      have hconjX : D.chi z2Z * b * (D.chi z2Z)⁻¹ ∈ D.Xhat :=
        D.Xhat.mul_mem (D.Xhat.mul_mem (D.chi_mem_Xhat z2Z) hbB.2)
          (D.Xhat.inv_mem (D.chi_mem_Xhat z2Z))
      have hconjB : D.chi z2Z * b * (D.chi z2Z)⁻¹ ∈ S.Lbar g ⊓ D.Xhat :=
        ⟨hconjL, hconjX⟩
      rw [SwapW4.P_map_chi D W]
      exact hconjB
    · exact (Subgroup.card_map_of_injective
        (f := (↑(MulAut.conj (D.chi z2Z)) : S.O →* S.O))
        (MulAut.conj (D.chi z2Z)).injective).ge
  exact ⟨p, z2Z, hpP, he_eq, hchiN⟩

theorem SwapW4.mem_normalizer_P_of_chi (W : SwapW4 D) {z : D.Z}
    (hz : D.chi z ∈ normalizer ((SwapW4.P D W).map D.chi : Set S.O)) :
    z ∈ normalizer (SwapW4.P D W : Set D.Z) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq (H := SwapW4.P D W) (g := z)]
  refine eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨p', hp', rfl⟩
    have hpB : D.chi p' ∈ (SwapW4.P D W).map D.chi := ⟨p', hp', rfl⟩
    have hmap := (Subgroup.mem_normalizer_iff.mp hz (D.chi p')).mp hpB
    have hmapB : D.chi z * D.chi p' * (D.chi z)⁻¹ ∈ S.Lbar g ⊓ D.Xhat := by
      rwa [SwapW4.P_map_chi D W] at hmap
    refine (SwapW4.mem_P_iff D W).mpr ?_
    change D.chi (z * p' * z⁻¹) ∈ S.Lbar g ⊓ D.Xhat
    rw [map_mul, map_mul, map_inv]
    exact hmapB
  · exact (Subgroup.card_map_of_injective
      (f := (↑(MulAut.conj z) : D.Z →* D.Z)) (MulAut.conj z).injective).ge

theorem SwapW4.normalizer_E2_subset (W : SwapW4 D) {e : S.O}
    (he : e ∈ D.Z ⊔ D.W) (hn : e ∈ normalizer (S.Lbar g : Set S.O)) :
    ∃ p : D.Z, p ∈ SwapW4.P D W ∧ ∃ n : D.Z,
      n ∈ normalizer (SwapW4.P D W : Set D.Z) ∧ e = (p : S.O) * D.chi n := by
  obtain ⟨p, n, hpP, he_eq, hchiN⟩ := SwapW4.normalizer_E2_decomp D W he hn
  exact ⟨p, hpP, n, SwapW4.mem_normalizer_P_of_chi D W hchiN, he_eq⟩


end CFSG.GF2Type.Smith1979.W4Swap

