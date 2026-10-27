module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.L193T
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Cited

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4.L193

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open CFSG.GH74.Uniqueness.SU.SU1
open scoped commutatorElement

section ThreeB

variable {G : Type} [Group G] [Finite G] {z t g : G} {p : ℕ}

theorem Op_le_Op_Fm' (M : Subgroup G) (r : ℕ) [Fact r.Prime] : Op r M ≤ Op r (Fm M) := by
  have hWB : Op r M ≤ Fm M := Subgroup.map_mono (pCore_le_fitting _ r)
  refine le_Op_of_normalized r hWB (fun b hb w hw => ?_) (isPGroup_Op r M)
  have hbH : b ∈ M := (Subgroup.map_subtype_le _) hb
  exact Op_conj_mem (C := M) r (fun _ hc _ hb => M.mul_mem (M.mul_mem hc hb) (M.inv_mem hc)) hbH hw

theorem Op_le_Fof {r : ℕ} [hr : Fact r.Prime] (hr2 : r ≠ 2) (hrp : r ≠ p) (M U : Subgroup G) :
    Op r M ≤ Fof p M U :=
  (Op_le_Op_Fm' M r).trans
    ((le_iSup₂ (f := fun r' (_ : r' ∈ {r' : ℕ | r'.Prime ∧ r' ≠ 2 ∧ r' ≠ p}) => Op r' (Fm M)) r
      ⟨hr.out, hr2, hrp⟩).trans le_sup_right)

theorem cen_conj_le (h : Ab G z t g p) {U : Subgroup G} (hU : IsU z p U) {q : ℕ} (hq : q.Prime) {w v : G}
    (hw1 : w ≠ 1) (hwq : w ^ q = 1) (hwF : zpowers w ≤ Fof p (Cen z) U) (hv : g * v * g⁻¹ = w) :
    ∀ c : G, c * v = v * c → c ∈ conjugate (Cen z) g := by
  intro c hc
  have hNX := h.cons.nG U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2 (zpowers w) hwF
    (fun hb => hw1 (by
      have : w ∈ zpowers w := Subgroup.mem_zpowers _
      rw [hb] at this
      exact Subgroup.mem_bot.mp this)) ⟨q, hq, isElementaryAbelian_zpowers hwq⟩
  rw [mem_conjugate_iff']
  apply hNX
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hcomm : Commute (g * c * g⁻¹) w := by
    show (g * c * g⁻¹) * w = w * (g * c * g⁻¹)
    rw [← hv]
    calc (g * c * g⁻¹) * (g * v * g⁻¹) = g * (c * v) * g⁻¹ := by group
      _ = g * (v * c) * g⁻¹ := by rw [hc]
      _ = (g * v * g⁻¹) * (g * c * g⁻¹) := by group
  exact ((hcomm.symm.zpow_left k).eq)

theorem lemma19_3b (h : Ab G z t g p) {U : Subgroup G} (hU : IsU z p U) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrp : r ≠ p) (hrank : 2 ≤ pRank r ↥(Op r (Cen z))) : ∀ x ∈ Op r (Cen z), t * x * t⁻¹ = x⁻¹ := by
  have hrf : Fact r.Prime := ⟨hr⟩
  have hpf : Fact p.Prime := ⟨h.prime⟩
  have hRp : IsPGroup r ↥(Op r (Cen z)) := isPGroup_Op r _
  refine inverted_of_no_fixed hRp h.t2 (fun e he => Op_norm r _ h.t_mem_M he) ?_
  intro e he hte her
  by_contra he1
  have hXp : IsPGroup r ↥(zpowers e) := isPGroup_zpowers' her
  have hXF : zpowers e ≤ Fof p (Cen z) U :=
    (Subgroup.zpowers_le.mpr he).trans (Op_le_Fof hr2 hrp (Cen z) U)
  have hee : e ∈ Cen z := Subgroup.map_subtype_le _ he
  have hez : e * z = z * e := Subgroup.mem_centralizer_singleton_iff.mp hee
  have hNX : normalizer ((zpowers e : Subgroup G) : Set G) ≤ Cen z := by
    refine h.cons.nG U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2 _ hXF (fun hb => he1 (by
      have : e ∈ zpowers e := Subgroup.mem_zpowers _
      rw [hb] at this
      exact Subgroup.mem_bot.mp this)) ⟨r, hr, isElementaryAbelian_zpowers her⟩
  have hte' : t * e = e * t := by
    calc t * e = (t * e * t⁻¹) * t := by group
      _ = e * t := by rw [hte]
  have heN : e ∈ conjugate (Cen z) g := by
    rw [← h.cen_t_eq]; exact Subgroup.mem_centralizer_singleton_iff.mpr hte'.symm
  have hDp : IsPGroup r ↥(Op r (conjugate (Cen z) g)) := isPGroup_Op r _
  have hXN : zpowers e ≤ conjugate (Cen z) g := by rw [Subgroup.zpowers_le]; exact heN
  have hDM : Op r (conjugate (Cen z) g) ≤ Cen z := by
    intro d hd
    have hzd := axb_helper (p := r) hr2 h.z2 h.z_ne_one hDp hXp
      (fun d hd => Op_norm r _ h.z_mem_N hd) (fun x' hx' d hd => Op_norm r _ (hXN hx') hd)
      (fun x' hx' => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
        exact ((Commute.zpow_left (show Commute e z from hez) k).eq).symm)
      (fun d hd hdc => by
        have hdX : d ∈ normalizer ((zpowers e : Subgroup G) : Set G) :=
          Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x' hx' => (hdc x' hx').symm)
        have := Subgroup.mem_centralizer_singleton_iff.mp (hNX hdX)
        exact this.symm) d hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr hzd.symm
  have hR2 : 2 ≤ Open.pRank r (Op r (Cen z)) := by
    rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hr] at hrank
  obtain ⟨ER, hERle, hERel, hERc⟩ := exists_isElemAbelian_of_le_pRank hr hR2
  have hEel : Open.IsElemAbelian r (conjugate ER g) := CFSG.SectionRank.isElemAbelian_map hERel _
  have hEc : Nat.card ↥(conjugate ER g) = r ^ 2 := by rw [card_conjugate, hERc]
  have hED : conjugate ER g ≤ Op r (conjugate (Cen z) g) :=
    (conjugate_mono hERle g).trans (op_conjugate_le r (Cen z) g)
  have hEM : conjugate ER g ≤ Cen z := hED.trans hDM
  have hCv : ∀ v ∈ conjugate ER g, v ≠ 1 → ∀ c : G, c * v = v * c → c ∈ conjugate (Cen z) g := by
    intro v hv hv1 c hc
    rw [mem_conjugate_iff'] at hv
    have hw1 : g * v * g⁻¹ ≠ 1 := fun hw1 => hv1 (by
      have : v = g⁻¹ * (g * v * g⁻¹) * g := by group
      rw [this, hw1]; group)
    have hwr : (g * v * g⁻¹) ^ r = 1 := (isElemAbelian_iff.mp hERel).2 _ hv
    exact cen_conj_le h hU hr hw1 hwr
      ((Subgroup.zpowers_le.mpr (hERle hv)).trans (Op_le_Fof hr2 hrp (Cen z) U)) rfl c hc
  have hPN : Op p (Cen z) ≤ conjugate (Cen z) g := by
    have hcop : Nat.Coprime r (Nat.card ↥(Op p (Cen z))) := by
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (isPGroup_Op p (Cen z))
      rw [ha]
      exact Nat.Coprime.pow_right a ((Nat.coprime_primes hr h.prime).mpr hrp)
    have hEnorm : conjugate ER g ≤ normalizer ((Op p (Cen z) : Subgroup G) : Set G) := by
      intro v hv
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hvM : v ∈ Cen z := hEM hv
      refine ⟨fun hx => Op_norm p _ hvM hx, fun hx => ?_⟩
      have := Op_norm p _ ((Cen z).inv_mem hvM) hx
      have e : v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x := by group
      rwa [e] at this
    have h1123 := CFSG.GH74.GLS.Stage2.Bender.Thm1.ig_11_23_thm G r hr (conjugate ER g) (Op p (Cen z))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).mpr hEel) hEc hcop hEnorm
    refine h1123.trans (iSup₂_le fun v hv => ?_)
    intro c hc
    exact hCv v hv.1 hv.2 c (Subgroup.mem_centralizer_singleton_iff.mp hc.2)
  have hUN : U ≤ conjugate (Cen z) g := fun u hu => hPN (hU.1 hu)
  have hZU : zpowers z ⊔ U ≤ conjugate (Cen z) g :=
    sup_le (by rw [Subgroup.zpowers_le]; exact h.z_mem_N) hUN
  have hUQ : U ≤ Qof p (Cen z) U := fun u hu =>
    mem_Qof.mpr ⟨hU.1 hu, fun w hw => congrArg Subtype.val (hU.2.2.1.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)⟩
  exact h.N_ne (h.cons.b U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2 g U hUQ hU.2.2.1 (by rw [hU.2.2.2]) hZU)

end ThreeB

end CFSG.GH74.GLS.Stage2.Final.Thm4.L193
