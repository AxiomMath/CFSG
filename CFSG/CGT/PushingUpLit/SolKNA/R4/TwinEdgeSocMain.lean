module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocQuot
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocCore
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinEdgeSocSec

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4Twin
open scoped commutatorElement

@[expose] def SocTwinFreeSection {G : Type} [Group G] [Finite G] (K W : Subgroup G) : Prop :=
  K ≤ W ∧ IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W ∧
    ¬ PhilipHall.Frame.HasTwin (K.subgroupOf W)

theorem EdgelessSection.soc_twinFree {G : Type} [Group G] [Finite G] {K W : Subgroup G}
    (h : EdgelessSection K W) : SocTwinFreeSection K W :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

section Helpers

variable {G : Type} [Group G]

theorem soc_mem_normalizer_core {K D : Subgroup G} [D.Normal] {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) :
    y ∈ Subgroup.normalizer ((⁅K, K⁆ ⊓ D : Subgroup G) : Set G) := by
  have hc : conjSub y ⁅K, K⁆ = ⁅K, K⁆ := by
    have := Subgroup.map_commutator K K (MulAut.conj y).toMonoidHom
    have hK : conjSub y K = K := mem_normalizer_iff_conjSub_eq.mp hy
    unfold conjSub at hK
    rw [hK] at this
    exact this
  have hyc : y ∈ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hc
  rw [Subgroup.mem_normalizer_iff] at hyc ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hyc h]
  haveI hDn : D.Normal := inferInstance
  exact and_congr_right fun _ => ⟨fun hh => hDn.conj_mem h hh y, fun hh => by
    have := hDn.conj_mem _ hh y⁻¹
    simpa [mul_assoc] using this⟩

theorem soc_mem_normalizer_map {A : Type} [Group A] (φ : G →* A) {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) :
    φ y ∈ Subgroup.normalizer ((H.map φ : Subgroup A) : Set A) := by
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro h
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨y * n * y⁻¹, (hy n).mp hn, by simp⟩
  · rintro ⟨m, hm, hmh⟩
    refine ⟨y⁻¹ * m * y, ?_, ?_⟩
    · exact (hy (y⁻¹ * m * y)).mpr (by simpa [mul_assoc] using hm)
    · rw [map_mul, map_mul, map_inv, hmh]
      group

theorem soc_orderOf_mk {z : G} (hz : z * z = 1) (hZ : z ∉ Subgroup.center G) :
    orderOf (QuotientGroup.mk' (Subgroup.center G) z) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, pow_two, hz, map_one]
  · intro h
    exact hZ ((QuotientGroup.eq_one_iff _).mp h)

end Helpers

section TheoremA

variable {r : ℕ} {G : Type} [Group G] [Finite G] {J L L₀ : Subgroup G}

theorem F2ConfigR.false_of_socleFacts (hr : 4 ≤ r) (hc : F2ConfigR r J L L₀)
    (hF : SocleFactsR ↥(socleOf L₀)) {WJ WL : Subgroup G} (hJ : EdgelessSection J WJ)
    (hL : SocTwinFreeSection L WL) : False := by
  haveI := hc.normal
  obtain ⟨hJW, hJs, hJg, hJtw, hJedge⟩ := hJ
  obtain ⟨hLW, hLs, hLg, hLtw⟩ := hL
  set Δ := CoreAssembly.conjClass J ∪ CoreAssembly.conjClass L with hΔ
  have hΔh : TwinT4Hyp r G Δ := hc.min.hyp
  have hΩ : HypOmegaGen Δ := hΔh.hyp
  have hJΔ : J ∈ Δ := Or.inl (CoreAssembly.mem_conjClass_self J)
  have hLΔ : L ∈ Δ := Or.inr (CoreAssembly.mem_conjClass_self L)
  obtain ⟨zJ, hzJ⟩ := (hΩ.omega1 J hJΔ).1
  obtain ⟨zL, hzL⟩ := (hΩ.omega1 L hLΔ).1
  have hn2 : (2 : ℕ) ^ 2 ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hNZ : ∀ n : ℕ, n = 2 ^ (r - 2) → NeZero n := fun n hn => ⟨by rw [hn]; positivity⟩
  have hcard : ∀ {K : Subgroup G}, K ∈ Δ → ∀ {P : Subgroup G}, IsSylow2In P K →
      ∃ e : ↥P ≃* QuaternionGroup (2 ^ (r - 2)), Nat.card ↥P = 2 ^ r := by
    intro K hK P hP
    obtain ⟨e⟩ := hΔh.quat K hK P hP
    refine ⟨e, ?_⟩
    haveI : NeZero (2 ^ (r - 2)) := hNZ _ rfl
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    have : r = (r - 2) + 2 := by omega
    conv_rhs => rw [this, pow_add]
    ring
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  set R : Subgroup G := Subgroup.map J.subtype (R₀ : Subgroup ↥J) with hRdef
  have hR : IsSylow2In R J := isSylow2In_map_sylow J R₀
  obtain ⟨S, hRS⟩ := hR.2.1.exists_le_sylow
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  set T₀' : Subgroup G := Subgroup.map L.subtype (T₀ : Subgroup ↥L) with hT₀def
  have hT₀ : IsSylow2In T₀' L := isSylow2In_map_sylow L T₀
  obtain ⟨S₁, hS₁⟩ := hT₀.2.1.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S S₁
  set M : Subgroup G := conjSub g⁻¹ L with hMdef
  set T : Subgroup G := conjSub g⁻¹ T₀' with hTdef
  have hTS : T ≤ (S : Subgroup G) := by
    have h1 : T₀' ≤ conjSub g (S : Subgroup G) := hg ▸ hS₁
    have := conjSub_mono (n := g⁻¹) h1
    rwa [conjSub_inv_conjSub] at this
  have hMΔ : M ∈ Δ := hΩ.conjInvariant g⁻¹ L hLΔ
  have hTM : IsSylow2In T M := hT₀.conj g⁻¹
  set t : G := g⁻¹ * zL * g with htdef
  have hzM : IsUniqueInvolution M t := by
    have := hzL.conj g⁻¹
    rwa [inv_inv] at this
  have h2r : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hMJ : M ≠ J := by
    intro h
    exact hc.min.notConj ⟨g, by rw [← h, hMdef, conjSub_conjSub_inv]⟩
  obtain ⟨eR, hRcard⟩ := hcard hJΔ hR
  obtain ⟨eT, hTcard⟩ := hcard hMΔ hTM
  have hRne : R ≠ T := by
    intro hRT
    have hdvd : 2 ^ r ∣ Nat.card ↥(J ⊓ M) := by
      have h2 : R ≤ J ⊓ M := le_inf hR.1 (hRT ▸ hTM.1)
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le h2
    have h3 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
    have h4 := (hΩ.omega4 J hJΔ M hMΔ hMJ.symm).1
    omega
  have hcomm : Commutes R T :=
    Q3CP.l67Gen G Δ hΩ S R (mem_RSet_of_isSylow2In hJΔ hR) T (mem_RSet_of_isSylow2In hMΔ hTM)
      hRS hTS hRne
  have htT : t ∈ T :=
    mem_of_isUniqueInvolution_of_isPGroup hzM hTM.1 hTM.2.1 (by rw [hTcard]; exact h2r)
  set mk := QuotientGroup.mk' (Subgroup.center G) with hmk
  have hzJL : zJ ∈ L₀ := hc.invMem J hJΔ zJ hzJ
  have htL : t ∈ L₀ := hc.invMem M hMΔ t hzM
  have hzJZ := hc.soc_not_mem_center hJΔ hzJ
  have htZ := hc.soc_not_mem_center hMΔ hzM
  have hxW : ∀ {x : G}, x ∈ L₀ → x ∈ WJ := fun hx => hc.soc_le_section hJΔ hJW hJs hx
  have hxWL : ∀ {x : G}, x ∈ L₀ → x ∈ WL := fun hx => hc.soc_le_section hLΔ hLW hLs hx
  have hmkt : mk t = mk zJ := by
    have h1 : orderOf (⟨mk zJ, Subgroup.mem_map_of_mem _ hzJL⟩ : ↥(socleOf L₀)) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact soc_orderOf_mk hzJ.sq hzJZ
    have h2 : orderOf (⟨mk t, Subgroup.mem_map_of_mem _ htL⟩ : ↥(socleOf L₀)) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact soc_orderOf_mk hzM.sq htZ
    obtain ⟨xb, hxb⟩ := hF.inv_conj _ _ h1 h2
    obtain ⟨x, hxL, hx⟩ := xb.2
    have h3 : mk (x * zJ * x⁻¹) = mk t := by
      have := congrArg Subtype.val hxb
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at this
      rw [map_mul, map_mul, map_inv, hx]
      exact this
    have hcZ : (x * zJ * x⁻¹)⁻¹ * t ∈ Subgroup.center G := by
      have := h3
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hs : x * zJ * x⁻¹ = t * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹ := by group
    have hxz : x * zJ * x⁻¹ = zJ := by
      refine hc.soc_eq_of_edgeless hr hJΔ hzJ hJW hJs hJg hJtw hJedge hR (hxW hxL) fun ρ hρ => ?_
      rw [hs]
      have h1 : ρ * t = t * ρ := hcomm ρ hρ t htT
      have h2 : ρ * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹ = ((x * zJ * x⁻¹)⁻¹ * t)⁻¹ * ρ :=
        Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcZ) ρ
      calc ρ * (t * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹) = (ρ * t) * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹ := by group
        _ = t * (ρ * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹) := by rw [h1]; group
        _ = t * (((x * zJ * x⁻¹)⁻¹ * t)⁻¹ * ρ) := by rw [h2]
        _ = (t * ((x * zJ * x⁻¹)⁻¹ * t)⁻¹) * ρ := by group
    rw [← h3, hxz]
  have hmkinj : ∀ {K : Subgroup G}, K ∈ Δ → ∀ x ∈ K, mk x = 1 → x = 1 := by
    intro K hK x hx h1
    have hxZ : x ∈ Subgroup.center G := (QuotientGroup.eq_one_iff _).mp h1
    have : x ∈ K ⊓ Subgroup.center G := Subgroup.mem_inf.mpr ⟨hx, hxZ⟩
    rw [hc.soc_inf_center_eq_bot hK] at this
    exact Subgroup.mem_bot.mp this
  set D : Subgroup G := L₀ ⊔ Subgroup.center G with hD
  haveI hDn : D.Normal := inferInstance
  have hDmk : ∀ {x : G}, x ∈ D → mk x ∈ socleOf L₀ := by
    intro x hx
    obtain ⟨l, hl, c, hcZ, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨l, hl, ?_⟩
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff c).mpr hcZ, mul_one]
  have hS₁ : IsSylow2In ⁅R, R⁆ (⁅J, J⁆ ⊓ D) :=
    soc_isSylow2In_commutator (hΔh.twoGroup J hJΔ) hR
      (le_inf (Subgroup.commutator_mono hR.1 hR.1) (hc.soc_commutator_le_of_comm2 hF.comm2 hR.2.1))
      inf_le_left
  have hS₂ : IsSylow2In ⁅T, T⁆ (⁅M, M⁆ ⊓ D) :=
    soc_isSylow2In_commutator (hΔh.twoGroup M hMΔ) hTM
      (le_inf (Subgroup.commutator_mono hTM.1 hTM.1) (hc.soc_commutator_le_of_comm2 hF.comm2 hTM.2.1))
      inf_le_left
  have hN₁J : ⁅J, J⁆ ⊓ D ≤ J := inf_le_left.trans (soc_commutator_le_self J)
  have hN₂M : ⁅M, M⁆ ⊓ D ≤ M := inf_le_left.trans (soc_commutator_le_self M)
  have hS₁' := soc_isSylow2In_map mk (fun x hx => hmkinj hJΔ x (hN₁J hx)) hS₁
  have hS₂' := soc_isSylow2In_map mk (fun x hx => hmkinj hMΔ x (hN₂M hx)) hS₂
  have hN₁T : (⁅J, J⁆ ⊓ D).map mk ≤ socleOf L₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hDmk hy.2
  have hN₂T : (⁅M, M⁆ ⊓ D).map mk ≤ socleOf L₀ := by
    rintro _ ⟨y, hy, rfl⟩
    exact hDmk hy.2
  have hc₁ : (⁅J, J⁆ ⊓ D).map mk ≤ Subgroup.centralizer {mk zJ} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact (hzJ.commute_of_mem (hN₁J hy)).symm
  have hc₂ : (⁅M, M⁆ ⊓ D).map mk ≤ Subgroup.centralizer {mk zJ} := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hmkt, ← map_mul, ← map_mul]
    congr 1
    exact (hzM.commute_of_mem (hN₂M hy)).symm
  have hyz : ∀ {y : G}, y ∈ L₀ → mk y * mk zJ = mk zJ * mk y → y * zJ * y⁻¹ = zJ := by
    intro y hyL hycent
    have hcZ : zJ⁻¹ * (y * zJ * y⁻¹) ∈ Subgroup.center G := by
      have h1 : mk zJ = mk (y * zJ * y⁻¹) := by
        rw [map_mul, map_mul, map_inv, hycent]
        group
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      exact h1
    exact hc.soc_eq_of_mk_eq hr hJΔ hzJ hJW hJs hJg hJtw hJedge hR hyL hcZ (by group)
  have hn₁ : ∀ y' ∈ socleOf L₀, y' ∈ Subgroup.centralizer {mk zJ} →
      y' ∈ Subgroup.normalizer (((⁅J, J⁆ ⊓ D).map mk : Subgroup _) : Set _) := by
    intro y' hy' hycent
    obtain ⟨y, hyL, rfl⟩ := hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at hycent
    have hyN : y ∈ Subgroup.normalizer (J : Set G) :=
      hc.soc_mem_normalizer_of_section hr hJΔ hzJ hJW hJs hJg hJtw (hxW hyL) (hyz hyL hycent)
    exact soc_mem_normalizer_map mk (soc_mem_normalizer_core hyN)
  have hn₂ : ∀ y' ∈ socleOf L₀, y' ∈ Subgroup.centralizer {mk zJ} →
      y' ∈ Subgroup.normalizer (((⁅M, M⁆ ⊓ D).map mk : Subgroup _) : Set _) := by
    intro y' hy' hycent
    obtain ⟨y, hyL, rfl⟩ := hy'
    rw [Subgroup.mem_centralizer_singleton_iff] at hycent
    have hyz' := hyz hyL hycent
    have he : zJ⁻¹ * t ∈ Subgroup.center G := by
      have := hmkt.symm
      rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hyt : y * t * y⁻¹ = t := by
      have h1 : t = zJ * (zJ⁻¹ * t) := by group
      have h2 : y * (zJ⁻¹ * t) * y⁻¹ = zJ⁻¹ * t := by
        have := Subgroup.mem_center_iff.mp he y
        rw [this]; group
      calc y * t * y⁻¹ = (y * zJ * y⁻¹) * (y * (zJ⁻¹ * t) * y⁻¹) := by
            conv_lhs => rw [h1]
            group
        _ = t := by rw [hyz', h2]; group
    have hgy : g * y * g⁻¹ ∈ L₀ := hc.normal.conj_mem y hyL g
    have hgyz : (g * y * g⁻¹) * zL * (g * y * g⁻¹)⁻¹ = zL := by
      have h1 : zL = g * t * g⁻¹ := by rw [htdef]; group
      calc (g * y * g⁻¹) * zL * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * zL * g) * y⁻¹) * g⁻¹ := by group
        _ = g * (y * t * y⁻¹) * g⁻¹ := by rw [htdef]
        _ = zL := by rw [hyt, h1]
    have hgyN : g * y * g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      hc.soc_mem_normalizer_of_section hr hLΔ hzL hLW hLs hLg hLtw (hxWL hgy) hgyz
    have hyM : y ∈ Subgroup.normalizer (M : Set G) := by
      rw [mem_normalizer_iff_conjSub_eq] at hgyN ⊢
      rw [hMdef, ← conjSub_mul]
      have h1 : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
      rw [h1, conjSub_mul, hgyN]
    exact soc_mem_normalizer_map mk (soc_mem_normalizer_core hyM)
  haveI hNZ' : NeZero (2 ^ (r - 2)) := hNZ _ rfl
  have h4n : 4 ≤ 2 ^ (r - 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (r - 2) := hn2
  have hRinj : ∀ x ∈ ⁅R, R⁆, mk x = 1 → x = 1 := fun x hx =>
    hmkinj hJΔ x (hR.1 (soc_commutator_le_self R hx))
  have hTinj : ∀ x ∈ ⁅T, T⁆, mk x = 1 → x = 1 := fun x hx =>
    hmkinj hMΔ x (hTM.1 (soc_commutator_le_self T hx))
  obtain ⟨u, hu, hou⟩ := soc_cyc4_apply (socleOf L₀) hF.cyc4 (Subgroup.mem_map_of_mem _ hzJL)
    (soc_orderOf_mk hzJ.sq hzJZ) hN₁T hN₂T hc₁ hc₂ hn₁ hn₂ hS₁' hS₂'
    ((soc_isCyclic_map mk hRinj).mpr (soc_isCyclic_commutator_of_quat eR))
    ((soc_isCyclic_map mk hTinj).mpr (soc_isCyclic_commutator_of_quat eT))
    (by rw [soc_natCard_map mk hRinj]; exact soc_four_le_card_commutator_of_quat eR h4n)
    (by rw [soc_natCard_map mk hTinj]; exact soc_four_le_card_commutator_of_quat eT h4n)
  obtain ⟨j, hj, hju⟩ := (Subgroup.mem_inf.mp hu).1
  obtain ⟨m, hm, hmu⟩ := (Subgroup.mem_inf.mp hu).2
  have hjR : j ∈ R := soc_commutator_le_self R hj
  have hmT : m ∈ T := soc_commutator_le_self T hm
  have hj2 : j * j ≠ 1 := by
    intro h
    have : u ^ 2 = 1 := by rw [← hju, ← map_pow, pow_two, h, map_one]
    exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hou]; norm_num) this
  have hem : j⁻¹ * m ∈ Subgroup.center G := by
    have : mk j = mk m := hju.trans hmu.symm
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    exact this
  have hjc : ∀ y ∈ R, j * y = y * j := by
    intro y hy
    have h1 : y * m = m * y := hcomm y hy m hmT
    have h2 : y * (j⁻¹ * m)⁻¹ = (j⁻¹ * m)⁻¹ * y :=
      Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hem) y
    have hj' : j = m * (j⁻¹ * m)⁻¹ := by group
    calc j * y = (m * (j⁻¹ * m)⁻¹) * y := by rw [← hj']
      _ = m * ((j⁻¹ * m)⁻¹ * y) := by group
      _ = m * (y * (j⁻¹ * m)⁻¹) := by rw [← h2]
      _ = (m * y) * (j⁻¹ * m)⁻¹ := by group
      _ = (y * m) * (j⁻¹ * m)⁻¹ := by rw [h1]
      _ = y * (m * (j⁻¹ * m)⁻¹) := by group
      _ = y * j := by rw [← hj']
  exact hj2 (soc_sq_eq_one_of_central eR (by omega) hjR hjc)

end TheoremA

end CFSG.CGT.PushingUpLit.SolKNA.R4
