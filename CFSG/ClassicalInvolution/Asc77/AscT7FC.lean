module

public import CFSG.ClassicalInvolution.Asc77.AscT7DMu
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.Thompson

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

namespace Ctx

variable (c : Ctx p f Ω W)
include c

theorem mem_inf_W_of_isUniqueInvolution (ρ : Rep Ω W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    z ∈ ρ.R ⊓ W := by
  obtain ⟨w, hwRW, hw4⟩ := exists_orderOf_four c.hp c.hq c.hΩ c.hW ρ.hR
  have hw4' : w ^ 4 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hw4] at this
  have hw2 : w * w ≠ 1 := fun h => by
    have h1 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [hw4] at h1
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hwwsq : (w * w) * (w * w) = 1 := by
    calc (w * w) * (w * w) = w ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hw4'
  have hwwR : w * w ∈ ρ.R := ρ.R.mul_mem hwRW.1 hwRW.1
  have hwwK : w * w ∈ ρ.K := ρ.hRK.1 hwwR
  have hwz : w * w = z := (hz.unique (w * w) hwwK hwwsq).resolve_left hw2
  rw [← hwz]
  exact ⟨hwwR, W.mul_mem hwRW.2 hwRW.2⟩

theorem mem_W_of_isUniqueInvolution (ρ : Rep Ω W) {z : G} (hz : IsUniqueInvolution ρ.K z) :
    z ∈ W :=
  (c.mem_inf_W_of_isUniqueInvolution ρ hz).2

theorem exists_rep_of_involution_mem {J : Subgroup G} (hJ : J ∈ Ω) {t : G}
    (ht : IsUniqueInvolution J t) (htW : t ∈ W) : ∃ ρ : Rep Ω W, ρ.K = J := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet c.hW
  have hWC : W ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw t htW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ J) J :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (T7A.isSubnormal_centralizer c.hΩ hJ ht)
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hRD : T ⊓ J ∈ DSet Ω W :=
    mem_DSet_of_le_sylow c.hp c.hq c.hΩ c.hW (hWT.trans hTS) (mem_RSet_of_isSylow2In hJ hR)
      (inf_le_left.trans hTS)
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep c.hp c.hq c.hΩ c.hW hJ hR hRD
  exact ⟨ρ, hρK⟩

theorem conj_involution_of_comm (σ ρ : Rep Ω W) (hcomm : σ.img * ρ.img = ρ.img * σ.img) {v : G}
    (hv : v ∈ ρ.K ⊓ W) (hv2 : v * v = 1) : σ.r * v * σ.r⁻¹ = v := by
  by_cases hK : σ.K = ρ.K
  · have hvσ : v ∈ σ.K ⊓ W := by rw [hK]; exact hv
    rw [c.conj_inv σ hvσ]
    exact inv_eq_of_mul_eq_one_left hv2
  · have hnbr := c.omega_of_comm σ ρ hK hcomm
    have := c.centralizes σ ρ hnbr hv
    rw [this]
    group

theorem conj_involution_of_noncomm (σ ρ : Rep Ω W) (hnc : σ.img * ρ.img ≠ ρ.img * σ.img)
    {zσ j : G} (hz : IsUniqueInvolution σ.K zσ) (hj : IsUniqueInvolution ρ.K j) :
    σ.r * j * σ.r⁻¹ = zσ * j := by
  have hne : σ.K ≠ ρ.K := fun h => hnc (by rw [c.img_eq_of_K_eq σ ρ h])
  have hnot : ρ.K ∉ omegaNbr Ω σ.K := fun h => hnc (c.comm_of_omega σ ρ h)
  exact c.conj_involution σ ρ hne hnot hz hj

theorem clique_dichotomy (hnc : ¬ DbarConnected Ω W) {x₀ : ↥(muGroup Ω W)}
    (hx₀ : x₀ ∈ muDelta Ω W) :
    (∀ u ∈ Star3T.cent (muDelta Ω W) x₀, ∀ v ∈ Star3T.cent (muDelta Ω W) x₀, u * v = v * u) ∧
      ∀ x ∈ muDelta Ω W, ∀ y ∈ Star3T.cent (muDelta Ω W) x₀, x * y = y * x →
        x ∈ Star3T.cent (muDelta Ω W) x₀ := by
  have hP : PartIHyp p f Ω := ⟨c.hp, c.hq, c.hΩ, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hp c.hq c.hΩ c.hW (thompsonCube G Ω hP W c.hW)
  have hS : Star3T.IsStar (muDelta Ω W) :=
    isStar_muDelta c.hp c.hq c.hΩ c.hW (thompsonStar G Ω hP W c.hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ :=
    exists_not_conn_of_not_connected c.hp c.hq c.hΩ c.hW hnc
  obtain ⟨q₀, hq₀, hpq₀⟩ : ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) x₀ a := by
    by_cases h : Star3T.Conn (muDelta Ω W) x₀ d₀
    · exact ⟨a₀, ha₀, fun h' => hn₀ (h.symm.trans h')⟩
    · exact ⟨d₀, hd₀, h⟩
  have hpl : Star3T.IsPlane (muDelta Ω W) x₀ q₀ (x₀ * q₀ * x₀) := ⟨hx₀, hq₀, hpq₀, rfl⟩
  refine ⟨fun u hu v hv => hTT.isClique_cent hS hx₀ hq₀ hpq₀ hu hv, ?_⟩
  intro x hx y hy hxy
  have hxU : x ∈ Star3T.cent (muDelta Ω W) x₀ ∪ Star3T.cent (muDelta Ω W) q₀ ∪
      Star3T.cent (muDelta Ω W) (x₀ * q₀ * x₀) := by
    rw [← Star3T.IsTT.cent_union_eq hS hpl]
    exact hx
  have hpx : Star3T.Conn (muDelta Ω W) x₀ x :=
    (Star3T.conn_of_mem_cent hx₀ hy).trans (Star3T.conn_of_commute hy.1 hx hxy.symm)
  rcases hxU with (h1 | h2) | h3
  · exact h1
  · exact absurd (hpx.trans (Star3T.conn_of_mem_cent hq₀ h2).symm) hpq₀
  · exact absurd (hpx.trans (Star3T.conn_of_mem_cent (hTT.mem_third hpl) h3).symm)
      (hTT.not_conn_third_left hpl)

theorem conj_mul_involutions_eq (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) (σ : Rep Ω W) :
    σ.r * (t * z) * σ.r⁻¹ = t * z := by
  obtain ⟨hcl, hAON⟩ := c.clique_dichotomy hnc (T7D.imgQ_mem ρ)
  have hzW : z ∈ W := c.mem_W_of_isUniqueInvolution ρ hz
  have htW : t ∈ W := c.mem_W_of_isUniqueInvolution ρ' ht
  have hρ' : T7D.imgQ ρ' ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ) :=
    ⟨T7D.imgQ_mem ρ', Subtype.ext (c.comm_of_omega ρ ρ' hnbr).symm⟩
  by_cases hx : T7D.imgQ σ ∈ Star3T.cent (muDelta Ω W) (T7D.imgQ ρ)
  · have hxρ : σ.img * ρ.img = ρ.img * σ.img := congrArg Subtype.val hx.2
    have hxρ' : σ.img * ρ'.img = ρ'.img * σ.img :=
      congrArg Subtype.val (hcl _ hx _ hρ')
    have e1 := c.conj_involution_of_comm σ ρ hxρ ⟨hz.mem, hzW⟩ hz.sq
    have e2 := c.conj_involution_of_comm σ ρ' hxρ' ⟨ht.mem, htW⟩ ht.sq
    calc σ.r * (t * z) * σ.r⁻¹ = (σ.r * t * σ.r⁻¹) * (σ.r * z * σ.r⁻¹) := by group
      _ = t * z := by rw [e1, e2]
  · have hxρ : σ.img * ρ.img ≠ ρ.img * σ.img := fun h =>
      hx ⟨T7D.imgQ_mem σ, Subtype.ext h⟩
    have hxρ' : σ.img * ρ'.img ≠ ρ'.img * σ.img := fun h =>
      hx (hAON _ (T7D.imgQ_mem σ) _ hρ' (Subtype.ext h))
    obtain ⟨zσ, hzσ⟩ := c.hΩ.exists_uniqueInvolution c.hp c.hq σ.hK
    have hzσW : zσ ∈ W := c.mem_W_of_isUniqueInvolution σ hzσ
    have e1 := c.conj_involution_of_noncomm σ ρ hxρ hzσ hz
    have e2 := c.conj_involution_of_noncomm σ ρ' hxρ' hzσ ht
    have hc : t * zσ = zσ * t := c.comm_W t htW zσ hzσW
    calc σ.r * (t * z) * σ.r⁻¹ = (σ.r * t * σ.r⁻¹) * (σ.r * z * σ.r⁻¹) := by group
      _ = (zσ * t) * (zσ * z) := by rw [e1, e2]
      _ = zσ * (t * zσ) * z := by group
      _ = zσ * (zσ * t) * z := by rw [hc]
      _ = (zσ * zσ) * (t * z) := by group
      _ = t * z := by rw [hzσ.sq, one_mul]

theorem le_centralizer_mul_involutions (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({t * z} : Set G) := by
  intro R hR x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hxW : x ∈ W
  · exact c.comm_W x hxW (t * z)
      (W.mul_mem (c.mem_W_of_isUniqueInvolution ρ' ht) (c.mem_W_of_isUniqueInvolution ρ hz))
  · obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
    have h := c.conj_mul_involutions_eq hnc ρ ρ' hnbr hz ht
      (⟨K, R, x, hK, hR, hRK, hx, hxW⟩ : Rep Ω W)
    calc x * (t * z) = (x * (t * z) * x⁻¹) * x := by group
      _ = (t * z) * x := by rw [show x * (t * z) * x⁻¹ = t * z from h]

theorem MGrp_le_centralizer_mul_involutions (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) :
    MGrp Ω W ≤ Subgroup.centralizer ({t * z} : Set G) :=
  iSup₂_le fun R hR => c.le_centralizer_mul_involutions hnc ρ ρ' hnbr hz ht R hR

theorem mul_involutions_mem_MGrp (ρ ρ' : Rep Ω W) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) : t * z ∈ MGrp Ω W :=
  (MGrp Ω W).mul_mem (le_MGrp_of_mem_D ρ'.hR (c.mem_inf_W_of_isUniqueInvolution ρ' ht).1)
    (le_MGrp_of_mem_D ρ.hR (c.mem_inf_W_of_isUniqueInvolution ρ hz).1)

theorem mul_involutions_mem_centerIn (hnc : ¬ DbarConnected Ω W) (ρ ρ' : Rep Ω W)
    (hnbr : ρ'.K ∈ omegaNbr Ω ρ.K) {z t : G} (hz : IsUniqueInvolution ρ.K z)
    (ht : IsUniqueInvolution ρ'.K t) : t * z ∈ centerIn (MGrp Ω W) := by
  have hle := c.MGrp_le_centralizer_mul_involutions hnc ρ ρ' hnbr hz ht
  refine ⟨⟨t * z, c.mul_involutions_mem_MGrp ρ ρ' hz ht⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle g.2)

end Ctx

end Thompson

section Frame

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.not_dbarConnected (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  thompsonGraphAll G Ω ⟨h.std.stand.odd, h.std.stand.five, h.std.stand.hyp, h.std.stand.aEmpty⟩
    h.std.stand.mem hne h.hW

theorem Hyp21.exists_reps (h : Hyp21 p f Ω K K' z u J t W) :
    ∃ ρ ρ' : Thompson.Rep Ω W, ρ.K = K ∧ ρ'.K = J ∧ ρ'.K ∈ omegaNbr Ω ρ.K := by
  have hst := h.std.stand
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst h.hW
  obtain ⟨ρ, hρ⟩ := c.exists_rep_of_involution_mem hst.mem h.std.hz h.hzW
  obtain ⟨ρ', hρ'⟩ := c.exists_rep_of_involution_mem h.hJ.1 h.ht h.htW
  refine ⟨ρ, ρ', hρ, hρ', ?_⟩
  rw [hρ, hρ']
  exact h.hJ.2 K (mem_twinSet_self hst.mem h.std.hz)

theorem Hyp21.dSet_le_centralizer_tz (h : Hyp21 p f Ω K K' z u J t W)
    (hnc : ¬ DbarConnected Ω W) :
    ∀ R ∈ DSet Ω W, R ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand h.std.stand h.hW
  obtain ⟨ρ, ρ', hρ, hρ', hnbr⟩ := h.exists_reps
  exact c.le_centralizer_mul_involutions hnc ρ ρ' hnbr (hρ ▸ h.std.hz) (hρ' ▸ h.ht)

theorem Hyp21.mGrp_le_rLayer_tz (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : MGrp Ω W ≤ rLayer Ω (t * z) := by
  have hle := h.dSet_le_centralizer_tz (h.not_dbarConnected hne)
  exact iSup₂_le fun R hR =>
    le_iSup₂_of_le R hR.1 (le_iSup_of_le (hle R hR) le_rfl)

theorem Hyp21.tz_mem_centerIn_mGrp (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K) : t * z ∈ centerIn (MGrp Ω W) := by
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand h.std.stand h.hW
  obtain ⟨ρ, ρ', hρ, hρ', hnbr⟩ := h.exists_reps
  exact c.mul_involutions_mem_centerIn (h.not_dbarConnected hne) ρ ρ' hnbr (hρ ▸ h.std.hz)
    (hρ' ▸ h.ht)

end Frame

end CFSG.ClassicalInvolution.Asc77
