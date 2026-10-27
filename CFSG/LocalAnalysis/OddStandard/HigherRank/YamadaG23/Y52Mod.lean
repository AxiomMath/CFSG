module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Cover
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y52Abs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3C2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y52_comm_le_C₂ {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ⁅s.C₂, normIn L s.fr.B⁆ ≤ s.C₂ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hbX : b ∈ s.X := (f3_N_le_X s) ⟨s3_L_le_H s hH.hS hb.1, hb.2⟩
  have hba : b * a * b⁻¹ ∈ s.C₂ := f3_C₂_normal hH b hbX a ha
  have hcomm : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by rw [commutatorElement_def]; group
  rw [hcomm]
  exact s.C₂.mul_mem ha (s.C₂.inv_mem hba)

private lemma subgroupOf_commutator_eq {G : Type} [Group G] {H K M : Subgroup G}
    (hH : H ≤ M) (hK : K ≤ M) :
    (⁅H, K⁆).subgroupOf M = ⁅H.subgroupOf M, K.subgroupOf M⁆ := by
  refine (Subgroup.map_subtype_inj (H := M)).mp ?_
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hH,
    Subgroup.map_subgroupOf_eq_of_le hK,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hH hK)]

theorem y52_gen {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.C₂ = M2 s ⊔ zpowers s.t := by
  obtain ⟨k, hk⟩ := y52_exists_K hH
  obtain ⟨f, hfval, hfsurj, hfker⟩ := f3_phiHom hH
  have hkX : k ∈ s.X := f3_N_le_X s ⟨s3_L_le_H s hH.hS hk.mem.1, hk.mem.2⟩
  have hkt : k * s.t = s.t * k := (Subgroup.mem_centralizer_iff.mp s.t_mem) k hk.mem.1
  have htC₂ : s.t ∈ s.C₂ :=
    f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hM2le : M2 s ≤ s.C₂ :=
    sup_le (y52_comm_le_C₂ hH)
      ((le_sup_left : s.fr.B ≤ f3P s).trans (f3_P_le_C₂ hH))
  refine le_antisymm ?_ (sup_le hM2le (Subgroup.zpowers_le.mpr htC₂))
  have hVab : ∀ a ∈ cen s.fr.B, ∀ b ∈ cen s.fr.B, a * b = b * a := by
    intro a ha b hb
    rw [cen, Subgroup.mem_inf] at ha hb
    exact ((Subgroup.mem_centralizer_iff.mp ha.2) b hb.1).symm
  have hkV : ∀ v ∈ cen s.fr.B, k * v * k⁻¹ ∈ cen s.fr.B := by
    intro v hv
    rw [cen, Subgroup.mem_inf] at hv ⊢
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp hk.mem.2 v).mp hv.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hv ⊢
    intro b hb
    have hb' : k⁻¹ * b * k ∈ s.fr.B :=
      (Subgroup.mem_set_normalizer_iff''.mp hk.mem.2 b).mp hb
    calc b * (k * v * k⁻¹) = k * ((k⁻¹ * b * k) * v) * k⁻¹ := by group
      _ = k * (v * (k⁻¹ * b * k)) * k⁻¹ := by rw [hv.2 (k⁻¹ * b * k) hb']
      _ = (k * v * k⁻¹) * b := by group
  have hsurj := fpf_surj hVab hkV hk.fix
  intro x hx
  have hxY : x ∈ f3Y s := f3_C₂_le_Y hH hx
  have hφx : f3phi s x ∈ cen s.fr.B := f3_phi_mem hH x hxY
  obtain ⟨u, huV, hu⟩ := hsurj (f3phi s x) hφx
  obtain ⟨c, hc⟩ := hfsurj ⟨u, huV⟩
  have hcu : f3phi s (c : G) = u := by
    have h := hfval c
    rw [hc] at h
    exact h.symm
  have hcY : (c : G) ∈ f3Y s := f3_C₂_le_Y hH c.2
  have hkcinv : k * (c : G)⁻¹ * k⁻¹ ∈ f3Y s :=
    f3_Y_normal hH k hkX (c : G)⁻¹ ((f3Y s).inv_mem hcY)
  have hphi_inv : f3phi s (c : G)⁻¹ = (f3phi s (c : G))⁻¹ := by
    have h1 := f3_phi_mul hH (c : G)⁻¹ ((f3Y s).inv_mem hcY) (c : G) hcY
    have h0 : f3phi s ((c : G)⁻¹ * (c : G)) = 1 := by rw [inv_mul_cancel]; simp [f3phi]
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hdC : ⁅(c : G), k⁆ ∈ s.C₂ := by
    have hmem : k * (c : G)⁻¹ * k⁻¹ ∈ s.C₂ :=
      f3_C₂_normal hH k hkX (c : G)⁻¹ (s.C₂.inv_mem c.2)
    have heq : ⁅(c : G), k⁆ = (c : G) * (k * (c : G)⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact s.C₂.mul_mem c.2 hmem
  have hphi_d : f3phi s ⁅(c : G), k⁆ = f3phi s x := by
    have hmul := f3_phi_mul hH (c : G) hcY (k * (c : G)⁻¹ * k⁻¹) hkcinv
    have hconj := f3_phi_conj s hkt (c : G)⁻¹
    have heq : ⁅(c : G), k⁆ = (c : G) * (k * (c : G)⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]; group
    rw [heq, hmul, hconj, hphi_inv, hcu, hu]
    group
  have hfx : f ⟨⁅(c : G), k⁆, hdC⟩ = f ⟨x, hx⟩ := by
    apply Subtype.ext
    simp only [hfval, hphi_d]
  have hker1 : f (⟨⁅(c : G), k⁆, hdC⟩⁻¹ * ⟨x, hx⟩) = 1 := by
    rw [map_mul, map_inv, hfx, inv_mul_cancel]
  have hpP : ((⟨⁅(c : G), k⁆, hdC⟩⁻¹ * ⟨x, hx⟩ : ↥s.C₂) : G) ∈ f3P s :=
    (hfker _).mp hker1
  have hdM2 : ⁅(c : G), k⁆ ∈ M2 s :=
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator c.2 hk.mem)
  have hx_eq : x = ⁅(c : G), k⁆ * ((⟨⁅(c : G), k⁆, hdC⟩⁻¹ * ⟨x, hx⟩ : ↥s.C₂) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rcases f3_mem_P ((⟨⁅(c : G), k⁆, hdC⟩⁻¹ * ⟨x, hx⟩ : ↥s.C₂) : G) hpP with hpB | ⟨b, hb, hpb⟩
  · have hpM2 : ((⟨⁅(c : G), k⁆, hdC⟩⁻¹ * ⟨x, hx⟩ : ↥s.C₂) : G) ∈ M2 s :=
      Subgroup.mem_sup_right hpB
    exact Subgroup.mem_sup_left (hx_eq ▸ (M2 s).mul_mem hdM2 hpM2)
  · have hbM2 : b ∈ M2 s := Subgroup.mem_sup_right hb
    have hdbM2 : ⁅(c : G), k⁆ * b ∈ M2 s := (M2 s).mul_mem hdM2 hbM2
    have hx2 : x = (⁅(c : G), k⁆ * b) * s.t := by rw [hx_eq, hpb]; group
    rw [hx2]
    exact Subgroup.mul_mem_sup hdbM2 (Subgroup.mem_zpowers s.t)

theorem y52_t_not_mem_M2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (hc : ∀ x ∈ s.C₂, ∀ y ∈ s.C₂, ⁅x, y⁆ ∈ s.fr.B) : s.t ∉ M2 s := by
  obtain ⟨k, hk⟩ := y52_exists_K hH
  have hNLN : normIn L s.fr.B ≤ f3N s := fun x hx => ⟨s3_L_le_H s hH.hS hx.1, hx.2⟩
  have hkX : k ∈ s.X := (hNLN.trans (f3_N_le_X s)) hk.mem
  have hkcomm : k * s.t = s.t * k := (Subgroup.mem_centralizer_iff.mp s.t_mem) k hk.mem.1
  have hC₂X : s.C₂ ≤ s.X := f3_C₂_le_X hH
  have hNX : normIn L s.fr.B ≤ s.X := hNLN.trans (f3_N_le_X s)
  have hcommC₂ : ⁅s.C₂, normIn L s.fr.B⁆ ≤ s.C₂ := y52_comm_le_C₂ hH
  have hCNX : ⁅s.C₂, normIn L s.fr.B⁆ ≤ s.X := hcommC₂.trans hC₂X
  have hPX : f3P s ≤ s.X := Subgroup.le_normalizer (H := f3P s)
  have hBX : s.fr.B ≤ s.X := (le_sup_left : s.fr.B ≤ f3P s).trans hPX
  have htX : s.t ∈ s.X := hPX (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have htC₂ : s.t ∈ s.C₂ := f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  haveI hnorm : ((s.fr.B).subgroupOf s.X).Normal :=
    (Subgroup.normal_subgroupOf_iff hBX).mpr fun h k' hh hk' =>
      (Subgroup.mem_set_normalizer_iff.mp (f3_X_le_normB hH hk') h).mp hh
  let π : ↥s.X →* (↥s.X ⧸ (s.fr.B).subgroupOf s.X) :=
    QuotientGroup.mk' ((s.fr.B).subgroupOf s.X)
  let C : Subgroup (↥s.X ⧸ (s.fr.B).subgroupOf s.X) := (s.C₂.subgroupOf s.X).map π
  let N : Subgroup (↥s.X ⧸ (s.fr.B).subgroupOf s.X) :=
    ((normIn L s.fr.B).subgroupOf s.X).map π
  let tbar : ↥s.X ⧸ (s.fr.B).subgroupOf s.X := π ⟨s.t, htX⟩
  let kbar : ↥s.X ⧸ (s.fr.B).subgroupOf s.X := π ⟨k, hkX⟩
  have htbar : tbar = π ⟨s.t, htX⟩ := rfl
  have hkbar : kbar = π ⟨k, hkX⟩ := rfl
  have hCdef : C = (s.C₂.subgroupOf s.X).map π := rfl
  have hNdef : N = ((normIn L s.fr.B).subgroupOf s.X).map π := rfl
  have hpiB : ∀ {b : G} (hb : b ∈ s.fr.B), π ⟨b, hBX hb⟩ = 1 := fun hb =>
    (QuotientGroup.eq_one_iff (⟨_, hBX hb⟩ : ↥s.X)).mpr (Subgroup.mem_subgroupOf.mpr hb)
  have hpiBker : (s.fr.B).subgroupOf s.X ≤ MonoidHom.ker π := by
    intro b hb
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff b).mpr hb
  have hC : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
    intro x hx y hy
    rw [hCdef] at hx hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    have ha₂ : (a : G) ∈ s.C₂ := Subgroup.mem_subgroupOf.mp ha
    have hb₂ : (b : G) ∈ s.C₂ := Subgroup.mem_subgroupOf.mp hb
    have hmem : (a * b)⁻¹ * (b * a) ∈ (s.fr.B).subgroupOf s.X := by
      rw [Subgroup.mem_subgroupOf]
      have hkey : (b : G)⁻¹ * ⁅(a : G)⁻¹, (b : G)⁆ * (b : G) ∈ s.fr.B :=
        (Subgroup.mem_set_normalizer_iff''.mp
          (f3_X_le_normB hH (f3_C₂_le_X hH hb₂)) _).mp
          (hc (a : G)⁻¹ (s.C₂.inv_mem ha₂) (b : G) hb₂)
      have heq : (((a * b)⁻¹ * (b * a) : ↥s.X) : G) =
          (b : G)⁻¹ * ⁅(a : G)⁻¹, (b : G)⁆ * (b : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [heq]
      exact hkey
    calc π a * π b = π (a * b) := (map_mul π a b).symm
      _ = π (b * a) := QuotientGroup.eq.mpr hmem
      _ = π b * π a := map_mul π b a
  have htC : tbar ∈ C := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr htC₂)
  have ht1 : tbar ≠ 1 := by
    intro h
    have htB : (⟨s.t, htX⟩ : ↥s.X) ∈ (s.fr.B).subgroupOf s.X :=
      (QuotientGroup.eq_one_iff _).mp h
    exact s3_t_not_mem_L s hH.h31 (f3_B_le_L s (Subgroup.mem_subgroupOf.mp htB))
  have ht2 : tbar * tbar = 1 := by
    have htt : s.t * s.t = 1 := by
      have h := pow_orderOf_eq_one s.t
      rw [s.t_order, pow_two] at h
      exact h
    have h1 : (⟨s.t, htX⟩ : ↥s.X) * ⟨s.t, htX⟩ = 1 := by ext; simpa using htt
    calc tbar * tbar = π (⟨s.t, htX⟩ * ⟨s.t, htX⟩) := by simp only [htbar, map_mul]
      _ = 1 := by rw [h1, map_one]
  have hk3 : kbar ^ 3 = 1 := by
    have h1 : (⟨k, hkX⟩ : ↥s.X) ^ 3 = 1 := by ext; simpa using hk.cube
    calc kbar ^ 3 = π ((⟨k, hkX⟩ : ↥s.X) ^ 3) := by simp only [hkbar, map_pow]
      _ = 1 := by rw [h1, map_one]
  have hkC : ∀ x ∈ C, kbar * x * kbar⁻¹ ∈ C := by
    intro x hx
    rw [hCdef] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have hmem : (⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹ ∈ s.C₂.subgroupOf s.X :=
      Subgroup.mem_subgroupOf.mpr
        (f3_C₂_normal hH k hkX (a : G) (Subgroup.mem_subgroupOf.mp ha))
    have heq : kbar * π a * kbar⁻¹ = π ((⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹) := by
      simp only [hkbar, ← map_mul, ← map_inv]
    rw [heq, hCdef]
    exact Subgroup.mem_map_of_mem π hmem
  have hkbt : kbar * tbar * kbar⁻¹ = tbar := by
    have hcomm : k * s.t = s.t * k := (Subgroup.mem_centralizer_iff.mp s.t_mem) k hk.mem.1
    have h1 : (⟨k, hkX⟩ : ↥s.X) * ⟨s.t, htX⟩ * ⟨k, hkX⟩⁻¹ = ⟨s.t, htX⟩ := by
      ext
      show k * s.t * k⁻¹ = s.t
      rw [hcomm]; group
    calc kbar * tbar * kbar⁻¹ = π ((⟨k, hkX⟩ : ↥s.X) * ⟨s.t, htX⟩ * ⟨k, hkX⟩⁻¹) := by
          simp only [hkbar, htbar, ← map_mul, ← map_inv]
      _ = π ⟨s.t, htX⟩ := by rw [h1]
      _ = tbar := htbar.symm
  have hfix : ∀ x ∈ C, kbar * x * kbar⁻¹ = x → x = 1 ∨ x = tbar := by
    intro x hx hkx
    rw [hCdef] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    have haC₂ : (a : G) ∈ s.C₂ := Subgroup.mem_subgroupOf.mp ha
    have haY : (a : G) ∈ f3Y s := f3_C₂_le_Y hH haC₂
    have huB : k * (a : G) * k⁻¹ * (a : G)⁻¹ ∈ s.fr.B := by
      have h1 : π ((⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹) = π a := by
        have h := hkx
        simp only [hkbar, ← map_mul, ← map_inv] at h
        exact h
      have h2 : π (((⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹) * a⁻¹) = 1 := by
        rw [map_mul, h1, map_inv, mul_inv_cancel]
      have h3 : ((⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹) * a⁻¹ ∈
          (s.fr.B).subgroupOf s.X := (QuotientGroup.eq_one_iff _).mp h2
      have h4 : ((((⟨k, hkX⟩ : ↥s.X) * a * ⟨k, hkX⟩⁻¹) * a⁻¹ : ↥s.X) : G) ∈ s.fr.B :=
        Subgroup.mem_subgroupOf.mp h3
      convert h4 using 1
    have hφu : f3phi s (k * (a : G) * k⁻¹ * (a : G)⁻¹) = 1 := by
      have hY : k * (a : G) * k⁻¹ * (a : G)⁻¹ ∈ f3Y s :=
        (f3Y s).mul_mem (f3_Y_normal hH k hkX (a : G) haY) ((f3Y s).inv_mem haY)
      exact (f3_phi_eq_one hH _ hY).mpr (f3_P_le_X0 s (Subgroup.mem_sup_left huB))
    have hphi_fix : k * f3phi s (a : G) * k⁻¹ = f3phi s (a : G) := by
      have hmul := f3_phi_mul hH (k * (a : G) * k⁻¹)
        (f3_Y_normal hH k hkX (a : G) haY) (a : G)⁻¹ ((f3Y s).inv_mem haY)
      have hconj := f3_phi_conj s hkcomm (a : G)
      have hphi_inv : f3phi s (a : G)⁻¹ = (f3phi s (a : G))⁻¹ := by
        have h1 := f3_phi_mul hH (a : G)⁻¹ ((f3Y s).inv_mem haY) (a : G) haY
        have h0 : f3phi s ((a : G)⁻¹ * (a : G)) = 1 := by rw [inv_mul_cancel]; simp [f3phi]
        rw [h0] at h1
        exact eq_inv_of_mul_eq_one_left h1.symm
      have hprod : f3phi s (k * (a : G) * k⁻¹) * f3phi s (a : G)⁻¹ = 1 := by
        rw [← hmul]; exact hφu
      rw [hconj, hphi_inv] at hprod
      exact mul_inv_eq_one.mp hprod
    have hphi1 : f3phi s (a : G) = 1 := hk.fix _ (f3_phi_mem hH (a : G) haY) hphi_fix
    have haX0 : (a : G) ∈ f3X0 s := (f3_phi_eq_one hH (a : G) haY).mp hphi1
    have haP : (a : G) ∈ f3P s := by
      rw [← f3_C₂_inf_X0 hH]
      exact Subgroup.mem_inf.mpr ⟨haC₂, haX0⟩
    rcases f3_mem_P (a : G) haP with haB | ⟨b, hb, hab⟩
    · left
      exact (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_subgroupOf.mpr haB)
    · right
      have haeq : a = (⟨b, hBX hb⟩ : ↥s.X) * ⟨s.t, htX⟩ := by
        ext
        show (a : G) = b * s.t
        exact hab
      calc π a = π ((⟨b, hBX hb⟩ : ↥s.X) * ⟨s.t, htX⟩) := by rw [haeq]
        _ = π ⟨b, hBX hb⟩ * π ⟨s.t, htX⟩ := map_mul π _ _
        _ = 1 * tbar := by rw [hpiB hb, htbar]
        _ = tbar := one_mul _
  have hNC : ∀ n ∈ N, ∀ x ∈ C, n * x * n⁻¹ ∈ C := by
    intro n hn x hx
    rw [hNdef] at hn
    rw [hCdef] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
    have haX : (a : G) ∈ s.X := hNX (Subgroup.mem_subgroupOf.mp ha)
    have hmem : a * b * a⁻¹ ∈ s.C₂.subgroupOf s.X :=
      Subgroup.mem_subgroupOf.mpr
        (f3_C₂_normal hH (a : G) haX (b : G) (Subgroup.mem_subgroupOf.mp hb))
    have heq : π a * π b * (π a)⁻¹ = π (a * b * a⁻¹) := by
      simp only [← map_mul, ← map_inv]
    rw [heq, hCdef]
    exact Subgroup.mem_map_of_mem π hmem
  have hNt : ∀ n ∈ N, n * tbar * n⁻¹ = tbar := by
    intro n hn
    rw [hNdef] at hn
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    have haL : (a : G) ∈ L := (Subgroup.mem_subgroupOf.mp ha).1
    have hcomm : (a : G) * s.t = s.t * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp s.t_mem) (a : G) haL
    have h1 : a * (⟨s.t, htX⟩ : ↥s.X) * a⁻¹ = ⟨s.t, htX⟩ := by
      ext
      show (a : G) * s.t * (a : G)⁻¹ = s.t
      rw [hcomm]; group
    calc π a * tbar * (π a)⁻¹ = π (a * ⟨s.t, htX⟩ * a⁻¹) := by
          simp only [htbar, ← map_mul, ← map_inv]
      _ = π ⟨s.t, htX⟩ := by rw [h1]
      _ = tbar := htbar.symm
  have hNk : ∀ n ∈ N, n * kbar * n⁻¹ = kbar ∨ n * kbar * n⁻¹ = kbar⁻¹ := by
    intro n hn
    rw [hNdef] at hn
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨b, hb, hab⟩ := hk.conj (a : G) (Subgroup.mem_subgroupOf.mp ha)
    have haeq : a * (⟨k, hkX⟩ : ↥s.X) * a⁻¹ = ⟨k, hkX⟩ * ⟨b, hBX hb⟩ ∨
        a * (⟨k, hkX⟩ : ↥s.X) * a⁻¹ = (⟨k, hkX⟩ : ↥s.X)⁻¹ * ⟨b, hBX hb⟩ := by
      rcases hab with h | h
      · left; ext; show (a : G) * k * (a : G)⁻¹ = k * b; rw [h]
      · right; ext; show (a : G) * k * (a : G)⁻¹ = k⁻¹ * b; rw [h]
    rcases haeq with h | h
    · left
      calc π a * kbar * (π a)⁻¹ = π (a * ⟨k, hkX⟩ * a⁻¹) := by
            simp only [hkbar, ← map_mul, ← map_inv]
        _ = π (⟨k, hkX⟩ * ⟨b, hBX hb⟩) := by rw [h]
        _ = π ⟨k, hkX⟩ * π ⟨b, hBX hb⟩ := map_mul π _ _
        _ = kbar * 1 := by rw [hkbar, hpiB hb]
        _ = kbar := mul_one _
    · right
      calc π a * kbar * (π a)⁻¹ = π (a * ⟨k, hkX⟩ * a⁻¹) := by
            simp only [hkbar, ← map_mul, ← map_inv]
        _ = π ((⟨k, hkX⟩ : ↥s.X)⁻¹ * ⟨b, hBX hb⟩) := by rw [h]
        _ = (π ⟨k, hkX⟩)⁻¹ * π ⟨b, hBX hb⟩ := by rw [map_mul, map_inv]
        _ = kbar⁻¹ * 1 := by rw [hkbar, hpiB hb]
        _ = kbar⁻¹ := mul_one _
  have hnot := y52_mod_abs C N tbar kbar hC htC ht1 ht2 hk3 hkC hkbt hfix hNC hNt hNk
  have hM2map : ((M2 s).subgroupOf s.X).map π = ⁅C, N⁆ := by
    have hBbot : ((s.fr.B).subgroupOf s.X).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff ((s.fr.B).subgroupOf s.X)).mpr hpiBker
    rw [M2, Subgroup.subgroupOf_sup hCNX hBX, Subgroup.map_sup,
      subgroupOf_commutator_eq hC₂X hNX, Subgroup.map_commutator, hBbot, sup_bot_eq,
      ← hCdef, ← hNdef]
  intro htM2
  apply hnot
  rw [htbar, ← hM2map]
  exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr htM2)

theorem y52_mod {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (hc : ∀ x ∈ s.C₂, ∀ y ∈ s.C₂, ⁅x, y⁆ ∈ cen s.fr.B) :
    s.C₂ = M2 s ⊔ zpowers s.t ∧ M2 s ≠ s.C₂ := by
  refine ⟨y52_gen hH, ?_⟩
  intro hM2
  apply y52_t_not_mem_M2 hH fun x hx y hy => (Subgroup.mem_inf.mp (hc x hx y hy)).1
  rw [hM2]
  exact f3_P_le_C₂ hH (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))

end CFSG.OddStandard.HigherRank.YamadaG23
