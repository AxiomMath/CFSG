module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.TwL44Seven

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup

private theorem tw_map_centralizer_subtype {G : Type*} [Group G] (C : Subgroup G) (d : G)
    (hd : d ∈ C) :
    (Subgroup.centralizer ({⟨d, hd⟩} : Set C)).map C.subtype =
      Subgroup.centralizer ({d} : Set G) ⊓ C := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    rw [Subgroup.mem_inf]
    refine ⟨?_, h.2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
    simpa using congrArg Subtype.val hh
  · intro hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hg1, hg2⟩ := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg1
    refine Subgroup.mem_map.mpr ⟨⟨g, hg2⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hg1

private theorem tw_map_inf_centralizer_subtype {G : Type*} [Group G] (C : Subgroup G)
    (N : Subgroup G) (hNC : N ≤ C) (d : G) (hd : d ∈ C) :
    ((Subgroup.centralizer ((N.subgroupOf C : Subgroup C) : Set C) ⊓
        Subgroup.centralizer ({⟨d, hd⟩} : Set C)).map C.subtype) =
      Subgroup.centralizer ({d} : Set G) ⊓ C ⊓ Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    rw [Subgroup.mem_inf] at hh
    obtain ⟨hhD, hhd⟩ := hh
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine ⟨⟨?_, h.2⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff] at hhd ⊢
      simpa using congrArg Subtype.val hhd
    · rw [Subgroup.mem_centralizer_iff] at hhD ⊢
      intro n hn
      have hnC : n ∈ C := hNC hn
      exact congrArg Subtype.val (hhD ⟨n, hnC⟩ hn)
  · intro hg
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hg
    obtain ⟨⟨hg1, hg2⟩, hgN⟩ := hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg1
    rw [Subgroup.mem_centralizer_iff] at hgN
    refine Subgroup.mem_map.mpr ⟨⟨g, hg2⟩, ?_, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro n hn
      exact Subtype.ext (hgN n.val hn)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hg1

private theorem tw_center_eq_bot_of_mulEquiv_alternating {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 8)) : Subgroup.center X = ⊥ := by
  have hZ : (Subgroup.center X).map (e : X →* alternatingGroup (Fin 8)) = ⊥ := by
    rw [Subgroup.map_center_eq e]
    exact alternatingGroup.center_eq_bot (by simp)
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) e.injective).mp hZ

private theorem tw_inf_subgroupOf_centralizer_eq_bot {G : Type*} [Group G]
    (C N A : Subgroup G) (hAN : A ≤ N) (hNC : N ≤ C)
    (eA : ↥A ≃* alternatingGroup (Fin 8)) :
    A.subgroupOf C ⊓ Subgroup.centralizer ((N.subgroupOf C : Subgroup C) : Set C) = ⊥ := by
  rw [eq_bot_iff]
  intro h hh
  rw [Subgroup.mem_inf] at hh
  obtain ⟨hhA, hhD⟩ := hh
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  have hcentN : (h : G) ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnC : n ∈ C := hNC hn
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hhD) ⟨n, hnC⟩ hn)
  have hcentA : (h : G) ∈ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le hAN hcentN
  have hcenter : (⟨h, hhA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hcentA a.val a.2
  have hZ : Subgroup.center ↥A = ⊥ := tw_center_eq_bot_of_mulEquiv_alternating eA
  rw [hZ] at hcenter
  rw [Subgroup.mem_bot] at hcenter
  exact congrArg (fun x : ↥A => (x : G)) hcenter

theorem seven_dvd_card_inf_of_lieModel_l44 {G : Type} [Group G] [Finite G] {x : G}
    {N A : Subgroup G} (hNx : N ≤ centralizer ({x} : Set G))
    (hNn : (N.subgroupOf (centralizer ({x} : Set G))).Normal) (hN : ⁅N, N⁆ = N)
    (hS : LieModel (↥N ⧸ center ↥N) .PSL 4 2 2) (hAN : A ≤ N)
    (eA : ↥A ≃* alternatingGroup (Fin 8)) {t d : G}
    (ht : t ∈ centralizer ({x} : Set G)) (hd : d ∈ centralizer ({x} : Set G))
    (ht1 : ¬ ∀ n ∈ N, t * n = n * t) (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a = a * t)
    (hd2 : d * d = 1) (hdt : d * t = t * d) (hdA : ∀ a ∈ A, d * a * d⁻¹ ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ y ∈ A, d * y * d⁻¹ = a * y * a⁻¹) :
    7 ∣ Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({x} : Set G)) →
      7 ∣ Nat.card ↥(centralizer ({d} : Set G) ⊓ centralizer ({x} : Set G) ⊓
        centralizer (N : Set G)) := by
  classical
  intro h7
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have htC : t ∈ C := ht
  have hdC : d ∈ C := hd
  have hAC : A ≤ C := le_trans hAN hNx
  let N' : Subgroup C := N.subgroupOf C
  haveI hN'norm : N'.Normal := hNn
  let D₀ : Subgroup C := Subgroup.centralizer (N' : Set C)
  haveI hD₀norm : D₀.Normal := Subgroup.normal_centralizer
  have hN' : ⁅N', N'⁆ = N' := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hNx, hN]
  have hS' : LieModel (↥N' ⧸ Subgroup.center ↥N') .PSL 4 2 2 := by
    let eNC : ↥N' ≃* ↥N := Subgroup.subgroupOfEquivOfLe hNx
    exact LieModel.of_mulEquiv
      (QuotientGroup.congr (Subgroup.center ↥N') (Subgroup.center ↥N) eNC
        (Subgroup.map_center_eq eNC)).symm hS
  have hD : ∀ h : C, h ∈ D₀ ↔ ∀ n ∈ N', h * n = n * h := by
    intro h
    rw [Subgroup.mem_centralizer_iff]
    exact ⟨fun hh n hn => (hh n hn).symm, fun hh n hn => (hh n hn).symm⟩
  let A' : Subgroup (C ⧸ D₀) := (A.subgroupOf C).map (QuotientGroup.mk' D₀)
  have hAS : A' ≤ N'.map (QuotientGroup.mk' D₀) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono C hAN)
  have hdisj : A.subgroupOf C ⊓ D₀ = ⊥ :=
    tw_inf_subgroupOf_centralizer_eq_bot C N A hAN hNx eA
  let q : ↥(A.subgroupOf C) →* (C ⧸ D₀) :=
    (QuotientGroup.mk' D₀).comp (A.subgroupOf C).subtype
  have hqker : q.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyD : (y : C) ∈ D₀ := (QuotientGroup.eq_one_iff (N := D₀) (y : C)).mp hy
    have hyinf : (y : C) ∈ A.subgroupOf C ⊓ D₀ := ⟨y.2, hyD⟩
    rw [hdisj] at hyinf
    rw [Subgroup.mem_bot] at hyinf
    rw [Subgroup.mem_bot]
    exact Subtype.ext hyinf
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hqker
  have hmemA' : ∀ y : ↥(A.subgroupOf C), q y ∈ A' := fun y =>
    Subgroup.mem_map.mpr ⟨(y : C), y.2, rfl⟩
  let q' : ↥(A.subgroupOf C) →* A' := q.codRestrict A' hmemA'
  have hq'inj : Function.Injective q' := by
    intro y z hyz
    apply hq
    simpa [q', MonoidHom.codRestrict_apply] using
      congrArg (fun w : A' => (w : C ⧸ D₀)) hyz
  have hq'surj : Function.Surjective q' := by
    intro w
    have hw : (w : C ⧸ D₀) ∈ A' := w.2
    rw [Subgroup.mem_map] at hw
    obtain ⟨z, hz, hzw⟩ := hw
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    simpa [q, q', MonoidHom.codRestrict_apply] using hzw
  let e1 : ↥(A.subgroupOf C) ≃* A' := MulEquiv.ofBijective q' ⟨hq'inj, hq'surj⟩
  let eA' : A' ≃* alternatingGroup (Fin 8) :=
    e1.symm.trans ((Subgroup.subgroupOfEquivOfLe hAC).trans eA)
  let t' : C ⧸ D₀ := QuotientGroup.mk' D₀ ⟨t, htC⟩
  let d' : C := ⟨d, hdC⟩
  have ht1' : t' ≠ 1 := by
    intro h1
    apply ht1
    intro n hnN
    have hnC : n ∈ C := hNx hnN
    have hnN' : (⟨n, hnC⟩ : C) ∈ N' := hnN
    have htD : (⟨t, htC⟩ : C) ∈ D₀ :=
      (QuotientGroup.eq_one_iff (N := D₀) (⟨t, htC⟩ : C)).mp h1
    exact congrArg Subtype.val ((hD ⟨t, htC⟩).mp htD ⟨n, hnC⟩ hnN')
  have ht2' : t' * t' = 1 := by
    have h : (⟨t, htC⟩ : C) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
    simpa only [t', map_mul, map_one] using congrArg (QuotientGroup.mk' D₀) h
  have htA' : ∀ a ∈ A', t' * a = a * t' := by
    intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have hcomm : (⟨t, htC⟩ : C) * a₀ = a₀ * ⟨t, htC⟩ := Subtype.ext (htA (a₀ : G) ha₀)
    simpa only [t', map_mul] using congrArg (QuotientGroup.mk' D₀) hcomm
  have hd2' : d' * d' = 1 := Subtype.ext hd2
  have hdt' : (d' : C ⧸ D₀) * t' = t' * (d' : C ⧸ D₀) := by
    calc (d' : C ⧸ D₀) * t'
        = QuotientGroup.mk' D₀ (d' * ⟨t, htC⟩) := by rw [map_mul]; rfl
      _ = QuotientGroup.mk' D₀ (⟨t, htC⟩ * d') := by
        rw [show d' * ⟨t, htC⟩ = ⟨t, htC⟩ * d' from Subtype.ext hdt]
      _ = t' * (d' : C ⧸ D₀) := by rw [map_mul]; rfl
  have hdA' : ∀ a ∈ A', (d' : C ⧸ D₀) * a * (d' : C ⧸ D₀)⁻¹ ∈ A' := by
    intro a ha
    rw [Subgroup.mem_map] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    have hmem : d' * a₀ * d'⁻¹ ∈ A.subgroupOf C := by
      show ((d' * a₀ * d'⁻¹ : C) : G) ∈ A
      exact hdA (a₀ : G) ha₀
    have hEq : (d' : C ⧸ D₀) * (QuotientGroup.mk' D₀ a₀) * (d' : C ⧸ D₀)⁻¹
        = QuotientGroup.mk' D₀ (d' * a₀ * d'⁻¹) := by
      rw [map_mul, map_mul, map_inv]; rfl
    rw [hEq]
    exact Subgroup.mem_map.mpr ⟨d' * a₀ * d'⁻¹, hmem, rfl⟩
  have hdout' : ¬ ∃ a ∈ A', ∀ y ∈ A',
      (d' : C ⧸ D₀) * y * (d' : C ⧸ D₀)⁻¹ = a * y * a⁻¹ := by
    rintro ⟨a, haA', hconj⟩
    rw [Subgroup.mem_map] at haA'
    obtain ⟨a₀, ha₀, haeq⟩ := haA'
    apply hdout
    refine ⟨(a₀ : G), ha₀, ?_⟩
    intro y hyA
    have hyC : y ∈ C := hNx (hAN hyA)
    let y₀ : C := ⟨y, hyC⟩
    have hy₀ : y₀ ∈ A.subgroupOf C := hyA
    have hy'A' : QuotientGroup.mk' D₀ y₀ ∈ A' := Subgroup.mem_map.mpr ⟨y₀, hy₀, rfl⟩
    have hc := hconj (QuotientGroup.mk' D₀ y₀) hy'A'
    have hc' : (d' * y₀ * d'⁻¹ : C) = a₀ * y₀ * a₀⁻¹ := by
      have hEq1 : (d' : C ⧸ D₀) * QuotientGroup.mk' D₀ y₀ * (d' : C ⧸ D₀)⁻¹
          = QuotientGroup.mk' D₀ (d' * y₀ * d'⁻¹) := by
        rw [map_mul, map_mul, map_inv]; rfl
      have hEq2 : a * QuotientGroup.mk' D₀ y₀ * a⁻¹
          = QuotientGroup.mk' D₀ (a₀ * y₀ * a₀⁻¹) := by
        rw [← haeq, map_mul, map_mul, map_inv]
      have heq : QuotientGroup.mk' D₀ (d' * y₀ * d'⁻¹)
          = QuotientGroup.mk' D₀ (a₀ * y₀ * a₀⁻¹) := by
        rw [← hEq1, ← hEq2, hc]
      have hmemD : (d' * y₀ * d'⁻¹) / (a₀ * y₀ * a₀⁻¹) ∈ D₀ :=
        QuotientGroup.eq_iff_div_mem.mp heq
      have hmemA : (d' * y₀ * d'⁻¹) / (a₀ * y₀ * a₀⁻¹) ∈ A.subgroupOf C := by
        have h1 : d' * y₀ * d'⁻¹ ∈ A.subgroupOf C := by
          show ((d' * y₀ * d'⁻¹ : C) : G) ∈ A
          exact hdA y hyA
        have h2 : a₀ * y₀ * a₀⁻¹ ∈ A.subgroupOf C :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₀ hy₀) (Subgroup.inv_mem _ ha₀)
        exact Subgroup.div_mem (A.subgroupOf C) h1 h2
      have hbot : (d' * y₀ * d'⁻¹) / (a₀ * y₀ * a₀⁻¹) ∈ (⊥ : Subgroup C) := by
        rw [← hdisj]
        exact ⟨hmemA, hmemD⟩
      exact div_eq_one.mp (Subgroup.mem_bot.mp hbot)
    exact congrArg Subtype.val hc'
  have h7' : 7 ∣ Nat.card (Subgroup.centralizer ({d'} : Set C)) := by
    rw [← Subgroup.card_subtype C (Subgroup.centralizer ({d'} : Set C)),
      tw_map_centralizer_subtype C d hdC]
    simpa [C] using h7
  have hH := seven_dvd_card_inf_of_perfect N' D₀ hN' hD hS' A' hAS eA' t' d'
    ht1' ht2' htA' hd2' hdt' hdA' hdout' h7'
  have hcard : Nat.card ↥(D₀ ⊓ Subgroup.centralizer ({d'} : Set C)) =
      Nat.card ↥(Subgroup.centralizer ({d} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (N : Set G)) := by
    rw [← Subgroup.card_subtype C (D₀ ⊓ Subgroup.centralizer ({d'} : Set C)),
      tw_map_inf_centralizer_subtype C N hNx d hdC]
  rw [hcard] at hH
  exact hH

end CFSG.OddStandard.AltStdSec.SwapPartner
