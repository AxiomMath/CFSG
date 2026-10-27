module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusMainX

public section

namespace CFSG.OddStandard.AltStdSmall4.Fus.Main

open Subgroup Equiv AltStdCycTwo

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {θ : L ≃* alternatingGroup (Fin 9)}
  {z : G}

theorem mem_bSub_iff {g : G} : g ∈ bSub θ ↔
    ∃ hg : g ∈ L, ((θ ⟨g, hg⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ bBar := by
  unfold bSub
  constructor
  · rintro ⟨l, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨(θ.symm a).2, ?_⟩
    show ((θ (θ.symm a) : alternatingGroup (Fin 9)) : Perm (Fin 9)) ∈ bBar
    rw [MulEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨hg, hb⟩
    exact ⟨⟨g, hg⟩, ⟨θ ⟨g, hg⟩, hb, θ.symm_apply_apply _⟩, rfl⟩

theorem bSub_le_L : bSub θ ≤ L := fun _ hg => (mem_bSub_iff.1 hg).1

theorem coe_theta_eps {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} (hn : 8 ≤ n) (i : Fin 8)
    (h : N0.eps θ hn i ∈ L) :
    ((θ ⟨N0.eps θ hn i, h⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) = tr hn i := by
  have e : (⟨N0.eps θ hn i, h⟩ : L) = θ.symm ⟨tr hn i, tr_mem_alternatingGroup hn i⟩ := rfl
  rw [e, MulEquiv.apply_symm_apply]

section Nine

variable (c : Config G L Q 9 θ z)
include c

theorem mem_vSub_iff {g : G} : g ∈ vSub θ z ↔ g ∈ bSub θ ∨ g * z ∈ bSub θ :=
  mem_sup_zpowers_iff_of_mul_self (z_mul_self c) fun p hp => by
    have hpz : p * z = z * p := mem_centralizer_singleton_iff.1 (L_le_cent c (bSub_le_L hp))
    rw [← hpz, mul_inv_cancel_right]
    exact hp

theorem vSub_le_sSyl (hJ : FusJ) : vSub θ z ≤ sSyl c L rBar9 := by
  refine sup_le (fun g hg => ?_) (zpowers_le.2 z_mem_sSyl)
  obtain ⟨hgL, hb⟩ := mem_bSub_iff.1 hg
  exact rStar_le_sSyl ((isHStar_inner c).mem_rStar_of_mem_L hgL (hJ.bBar_le hb))

theorem mem_vSub_iff_rhoC {s : centralizer ({z} : Set G)} (hs : (s : G) ∈ sSyl c L rBar9) :
    (s : G) ∈ vSub θ z ↔ rhoC c s ∈ bBar := by
  have hzC := self_mem_centralizer_singleton z
  constructor
  · intro hv
    rcases (mem_vSub_iff c).1 hv with h | h
    · obtain ⟨hgL, hb⟩ := mem_bSub_iff.1 h
      have h1 : rhoC c s = ((θ ⟨s, hgL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
        rhoC_of_mem_L c hgL s.2
      rw [h1]
      exact hb
    · obtain ⟨hgL, hb⟩ := mem_bSub_iff.1 h
      have h1 : rhoC c (s * ⟨z, hzC⟩) =
          ((θ ⟨s * z, hgL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
        rhoC_of_mem_L c hgL (mul_mem s.2 hzC)
      rw [map_mul, rhoC_z, mul_one] at h1
      rw [h1]
      exact hb
  · intro hb
    rcases mem_sSyl_iff.1 hs with h | h
    · have hL : (s : G) ∈ L := rStar_le_H h
      have h1 : rhoC c s = ((θ ⟨s, hL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
        rhoC_of_mem_L c hL s.2
      refine mem_sup_left (mem_bSub_iff.2 ⟨hL, ?_⟩)
      rw [← h1]
      exact hb
    · have hL : (s : G) * z ∈ L := rStar_le_H h
      have h1 : rhoC c (s * ⟨z, hzC⟩) =
          ((θ ⟨s * z, hL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
        rhoC_of_mem_L c hL (mul_mem s.2 hzC)
      rw [map_mul, rhoC_z, mul_one] at h1
      have hB : (s : G) * z ∈ bSub θ := mem_bSub_iff.2 ⟨hL, by rw [← h1]; exact hb⟩
      have : (s : G) = s * z * z := by rw [mul_assoc, z_mul_self c, mul_one]
      rw [this]
      exact mul_mem (mem_sup_left hB) (mem_sup_right (mem_zpowers z))

theorem comm_commutators_iff (hJ : FusJ) (hle : rBar9 ≤ alternatingGroup (Fin 9))
    {s : centralizer ({z} : Set G)} (hs : (s : G) ∈ sSyl c L rBar9) :
    (∀ a ∈ sSyl c L rBar9, ∀ b ∈ sSyl c L rBar9,
      (s : G) * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * s) ↔ rhoC c s ∈ bBar := by
  have hH := isHStar_inner c
  rw [← hJ.cent_iff _ (rhoC_mem_of_mem_sSyl hs)]
  constructor
  · intro h a ha b hb
    obtain ⟨a', ha'H, rfl⟩ := hH.surj a (hle ha)
    obtain ⟨b', hb'H, rfl⟩ := hH.surj b (hle hb)
    have ha'S : (a' : G) ∈ sSyl c L rBar9 := rStar_le_sSyl (mem_rStar_iff'.2 ⟨ha'H, ha⟩)
    have hb'S : (b' : G) ∈ sSyl c L rBar9 := rStar_le_sSyl (mem_rStar_iff'.2 ⟨hb'H, hb⟩)
    have h1 : s * (a' * b' * a'⁻¹ * b'⁻¹) = a' * b' * a'⁻¹ * b'⁻¹ * s :=
      Subtype.ext (h _ ha'S _ hb'S)
    have h2 := congrArg (rhoC c) h1
    simpa only [map_mul, map_inv] using h2
  · intro h a ha b hb
    have haC := sSyl_le_cent ha
    have hbC := sSyl_le_cent hb
    have hcS : (((⟨a, haC⟩ : centralizer ({z} : Set G)) * ⟨b, hbC⟩ * (⟨a, haC⟩)⁻¹ *
        (⟨b, hbC⟩)⁻¹ : centralizer ({z} : Set G)) : G) ∈ sSyl c L rBar9 :=
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have := hH.comm_of_rhoC_comm hs hcS (by
      simp only [map_mul, map_inv]
      exact h _ (rhoC_mem_of_mem_sSyl (s := ⟨a, haC⟩) ha) _
        (rhoC_mem_of_mem_sSyl (s := ⟨b, hbC⟩) hb))
    exact this

theorem mem_normalizer_vSub (hJ : FusJ) (hle : rBar9 ≤ alternatingGroup (Fin 9)) {x : G}
    (hxN : x ∈ normalizer (sSyl c L rBar9 : Set G)) : x ∈ normalizer (vSub θ z : Set G) := by
  apply mem_normalizer_fintype
  intro v hv
  have hvS : v ∈ sSyl c L rBar9 := vSub_le_sSyl c hJ hv
  have hxvS : x * v * x⁻¹ ∈ sSyl c L rBar9 := (mem_normalizer_iff.1 hxN v).1 hvS
  have hv' := (comm_commutators_iff c hJ hle (s := ⟨v, sSyl_le_cent hvS⟩) hvS).2
    ((mem_vSub_iff_rhoC c (s := ⟨v, sSyl_le_cent hvS⟩) hvS).1 hv)
  refine (mem_vSub_iff_rhoC c (s := ⟨x * v * x⁻¹, sSyl_le_cent hxvS⟩) hxvS).2
    ((comm_commutators_iff c hJ hle (s := ⟨x * v * x⁻¹, sSyl_le_cent hxvS⟩) hxvS).1 ?_)
  intro a ha b hb
  have hxi : x⁻¹ ∈ normalizer (sSyl c L rBar9 : Set G) := inv_mem hxN
  have ha' : x⁻¹ * a * x ∈ sSyl c L rBar9 := by
    have := (mem_normalizer_iff.1 hxi a).1 ha
    simpa using this
  have hb' : x⁻¹ * b * x ∈ sSyl c L rBar9 := by
    have := (mem_normalizer_iff.1 hxi b).1 hb
    simpa using this
  have h1 : v * ((x⁻¹ * a * x) * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)⁻¹) =
      (x⁻¹ * a * x) * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)⁻¹ * v :=
    hv' _ ha' _ hb'
  show x * v * x⁻¹ * (a * b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ * (x * v * x⁻¹)
  calc x * v * x⁻¹ * (a * b * a⁻¹ * b⁻¹)
      = x * (v * ((x⁻¹ * a * x) * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)⁻¹)) *
          x⁻¹ := by group
    _ = x * ((x⁻¹ * a * x) * (x⁻¹ * b * x) * (x⁻¹ * a * x)⁻¹ * (x⁻¹ * b * x)⁻¹ * v) * x⁻¹ := by
        rw [h1]
    _ = a * b * a⁻¹ * b⁻¹ * (x * v * x⁻¹) := by group

theorem not_cc9 (hin : centralizer ({z} : Set G) ≤ L ⊔ centralizer (L : Set G)) (hJ : FusJ)
    (hP : FusP42) (h9 : FusR 9 c.hn8 (alternatingGroup (Fin 9)) rBar9 6 cc9) {x : G}
    (hxN : x ∈ normalizer (sSyl c L rBar9 : Set G)) (hxz : x⁻¹ * z * x = z * w θ c.hn8)
    (hxw : x⁻¹ * w θ c.hn8 * x = w θ c.hn8) : ¬ cc9 (xBar c L x) := by
  intro hcc
  have hH := isHStar_inner c
  have hzC := self_mem_centralizer_singleton z
  have hxV := mem_normalizer_vSub c hJ h9.le hxN
  have hfL : N0.eps θ c.hn8 2 ∈ L := N0.eps_mem_L θ c.hn8 2
  have hfE : N0.eps θ c.hn8 2 ∈ E θ c.hn8 := N0.eps_mem_E θ c.hn8 2
  have hfB : N0.eps θ c.hn8 2 ∈ bSub θ :=
    mem_bSub_iff.2 ⟨hfL, by rw [coe_theta_eps]; exact hJ.tr_two_mem⟩
  have hmL : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) ∈ L := (θ.symm ⟨mBar, hJ.mBar_mem⟩).2
  have hmz : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * z = z * θ.symm ⟨mBar, hJ.mBar_mem⟩ :=
    mem_centralizer_singleton_iff.1 (L_le_cent c hmL)
  have hconj : (⟨mBar, hJ.mBar_mem⟩ : alternatingGroup (Fin 9)) * wBar c.hn8 *
      (⟨mBar, hJ.mBar_mem⟩ : alternatingGroup (Fin 9))⁻¹ =
        ⟨tr c.hn8 2, tr_mem_alternatingGroup c.hn8 2⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_wBar]
    exact hJ.mBar_conj
  have hmw : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * w θ c.hn8 *
      ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ = N0.eps θ c.hn8 2 := by
    have h1 := congrArg (fun a => ((θ.symm a : L) : G)) hconj
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1
  have hmB : ∀ b ∈ bSub θ, ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * b *
      ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ ∈ bSub θ := by
    intro b hb
    obtain ⟨hbL, hbB⟩ := mem_bSub_iff.1 hb
    have hL : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * b *
        ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ ∈ L := mul_mem (mul_mem hmL hbL) (inv_mem hmL)
    refine mem_bSub_iff.2 ⟨hL, ?_⟩
    have e : (⟨_, hL⟩ : L) = θ.symm ⟨mBar, hJ.mBar_mem⟩ * ⟨b, hbL⟩ *
        (θ.symm ⟨mBar, hJ.mBar_mem⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hJ.mBar_norm _ hbB
  have hmV : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) ∈ normalizer (vSub θ z : Set G) := by
    apply mem_normalizer_fintype
    intro v hv
    rcases (mem_vSub_iff c).1 hv with h | h
    · exact mem_sup_left (hmB v h)
    · have hmiz : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ * z =
          z * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ := (Commute.inv_left hmz).eq
      have e : ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * v *
          ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ =
            ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * (v * z) *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ * z := by
        calc ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * v *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹
            = ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * v * (z * z) *
                ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ := by rw [z_mul_self c, mul_one]
          _ = ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * (v * z) *
                (z * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) := by group
          _ = ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * (v * z) *
                ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹ * z := by rw [← hmiz]; group
      rw [e]
      exact mul_mem (mem_sup_left (hmB _ h)) (mem_sup_right (mem_zpowers z))
  obtain ⟨y, hy⟩ : ∃ y, y = x⁻¹ * N0.eps θ c.hn8 2 * x := ⟨_, rfl⟩
  have hxy : x * y * x⁻¹ = N0.eps θ c.hn8 2 := by rw [hy]; group
  have hyV1 : y ∈ vOne θ c.hn8 z x := by
    rw [mem_vOne_iff, hxy]
    exact mem_sup_left hfE
  have hyS : y ∈ sSyl c L rBar9 := hH.vOne_le_sSyl h9.tr_mem hxN hyV1
  have hyC : y ∈ centralizer ({z} : Set G) := sSyl_le_cent hyS
  have hyL : y ∈ L := by
    have hqS : x⁻¹ * (z * N0.eps θ c.hn8 2) * x ∈ sSyl c L rBar9 := by
      refine hH.vOne_le_sSyl h9.tr_mem hxN ?_
      rw [mem_vOne_iff]
      have : x * (x⁻¹ * (z * N0.eps θ c.hn8 2) * x) * x⁻¹ = z * N0.eps θ c.hn8 2 := by group
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers z)) (mem_sup_left hfE)
    have hq : x⁻¹ * (z * N0.eps θ c.hn8 2) * x =
        (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * x) * z *
          (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * x)⁻¹ := by
      calc x⁻¹ * (z * N0.eps θ c.hn8 2) * x
          = x⁻¹ * (z * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * w θ c.hn8 *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) * x := by rw [← hmw]; group
        _ = x⁻¹ * (((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * z * w θ c.hn8 *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) * x := by rw [hmz]
        _ = x⁻¹ * (((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * (z * w θ c.hn8) *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) * x := by group
        _ = x⁻¹ * (((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * (x * z * x⁻¹) *
              ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) * x := by
            rw [conj_z_eq_mul c hxz hxw]
        _ = (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * x) * z *
              (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * x)⁻¹ := by group
    rcases mem_sSyl_iff.1 hqS with h | h
    · exact absurd (rStar_le_H h) (by rw [hq]; exact N0.conj_z_not_mem_L c _)
    · have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 hyC
      have hwy : x⁻¹ * (z * N0.eps θ c.hn8 2) * x * z = w θ c.hn8 * y := by
        calc x⁻¹ * (z * N0.eps θ c.hn8 2) * x * z
            = (x⁻¹ * z * x) * (x⁻¹ * N0.eps θ c.hn8 2 * x) * z := by group
          _ = z * w θ c.hn8 * y * z := by rw [hxz, ← hy]
          _ = z * w θ c.hn8 * (z * y) := by rw [mul_assoc _ y z, hyz]
          _ = z * (w θ c.hn8 * z) * y := by group
          _ = w θ c.hn8 * y := by rw [w_comm_z c, ← mul_assoc, z_mul_self c, one_mul]
      have h1 : w θ c.hn8 * y ∈ L := hwy ▸ rStar_le_H h
      have : y = (w θ c.hn8)⁻¹ * (w θ c.hn8 * y) := by group
      rw [this]
      exact mul_mem (inv_mem (w_mem_L c)) h1
  have hyV : y ∈ vSub θ z := by
    have := (mem_normalizer_iff.1 (inv_mem hxV) _).1 (mem_sup_left hfB)
    rw [inv_inv, ← hy] at this
    exact this
  have hyB : y ∈ bSub θ := by
    rcases (mem_vSub_iff c).1 hyV with h | h
    · exact h
    · exfalso
      apply N0.z_not_mem_L c
      have : z = y⁻¹ * (y * z) := by group
      rw [this]
      exact mul_mem (inv_mem hyL) (bSub_le_L h)
  have hy1 : y ≠ 1 := by
    intro h
    have : N0.eps θ c.hn8 2 = 1 := by rw [← hxy, h]; group
    exact absurd ((N0.eps_eq_one_iff θ c.hn8 2).1 this) (by decide)
  have hyw : y ≠ w θ c.hn8 := by
    intro h
    have : N0.eps θ c.hn8 2 = N0.eps θ c.hn8 1 := by
      rw [← hxy, h, conj_w_eq hxw, N0.w_eq_eps]
    exact absurd (N0.eps_injective θ c.hn8 this) (by decide)
  have hcard : ((θ ⟨y, hyL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)).support.card ≠ 4 := by
    intro h4
    have hg : x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) ∈ normalizer (vSub θ z : Set G) :=
      mul_mem (inv_mem hxV) hmV
    have hxz' : x⁻¹ * z * x⁻¹⁻¹ = z * w θ c.hn8 := by rw [inv_inv]; exact hxz
    apply hP G L Q θ z c hin x⁻¹ (inv_mem hxV) hxz' _ hg ⟨y, hyL⟩ (mem_bSub_iff.1 hyB).2 h4
    show x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * w θ c.hn8 *
      (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G))⁻¹ = y
    calc x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * w θ c.hn8 *
          (x⁻¹ * ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G))⁻¹
        = x⁻¹ * (((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G) * w θ c.hn8 *
            ((θ.symm ⟨mBar, hJ.mBar_mem⟩ : L) : G)⁻¹) * x := by group
      _ = y := by rw [hmw, hy]
  apply hcard
  have hρy : rhoC c ⟨y, hyC⟩ = ((θ ⟨y, hyL⟩ : alternatingGroup (Fin 9)) : Perm (Fin 9)) :=
    rhoC_of_mem_L c hyL hyC
  rw [← hρy]
  refine hcc _ (mem_xBar_iff.2 ⟨⟨y, hyC⟩, ⟨hyV1, hyL⟩, rfl⟩) ?_ ?_ ?_
  · rw [hρy]
    exact (mem_bSub_iff.1 hyB).2
  · intro h
    apply hy1
    have := hH.eq_of_rhoC_eq (a := ⟨y, hyC⟩) (b := 1) hyL (one_mem L) (by rw [h, map_one])
    exact congrArg Subtype.val this
  · intro h
    apply hyw
    have := hH.eq_of_rhoC_eq (a := ⟨y, hyC⟩) (b := ⟨w θ c.hn8, L_le_cent c (w_mem_L c)⟩) hyL
      hH.w_mem (by rw [h, rhoC_w])
    exact congrArg Subtype.val this

end Nine

end CFSG.OddStandard.AltStdSmall4.Fus.Main
