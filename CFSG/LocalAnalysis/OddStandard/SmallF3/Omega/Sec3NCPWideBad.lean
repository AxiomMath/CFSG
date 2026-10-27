module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3NCPWideSwap
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.SwapPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.ThmU.Rank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard

public section

namespace CFSG.OddStandard.SmallF3.Omega.NCPWide

open Subgroup CFSG.Blueprint CFSG.OddStandard.SmallF3.Omega CFSG.LocalAnalysis.ComponentInitial
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.ThmU

variable {G : Type} [Group G]

theorem bad_and_comp_of_swapCfg [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B M : Subgroup G} (hB : Unp B) {x y : G} (hx : GoodI B x) (hc : SwapCfg B x y M) (hM : Unp M)
    {r : G} (hr : orderOf r = 2) (hrx : r * x = x * r) (hry : r * y = y * r)
    (hrB : r ∈ centralizer (B : Set G))
    (hrM : r ∈ centralizer ((M ⊔ CFSG.conjugate M x : Subgroup G) : Set G)) :
    BadI B r ∧ IsComponentIn M (centralizer ({r} : Set G)) := by
  have hyy : y * y = 1 := hc.y_sq
  have hMr : M ≤ centralizer ({r} : Set G) := fun m hm =>
    Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 hrM m (Subgroup.mem_sup_left hm))
  have hxX : x ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hrx.symm
  have hyX : y ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hry.symm
  have hBcent : B ≤ centralizer ({r} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hrB b hb)
  have hMry : M ≤ centralizer ({y, r} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rcases hw with rfl | hw
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hc.comp.1 hz)).symm
    · rw [Set.mem_singleton_iff.mp hw]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hMr hz)).symm
  have hpair : centralizer ({y, r} : Set G) ≤ centralizer ({y} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Set.mem_insert y {r}))
  have hpair' : centralizer ({y, r} : Set G) ≤ centralizer ({r} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
      (Set.mem_insert_of_mem y (Set.mem_singleton r)))
  have hMpair : IsComponentIn M (centralizer ({y, r} : Set G)) := hc.comp.mono hMry hpair
  obtain ⟨L, hL, hMLle⟩ := hS.lBalance y r hc.y_ord hr hry.symm M hMpair
  rw [← cj_eq_conjugate_of_sq hyy] at hMLle
  have hBnotComp : ¬ IsComponentIn B (centralizer ({r} : Set G)) := by
    intro hBcomp
    have hLyc : IsComponentIn (cj y L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hyX
    have hle : M ≤ normalizer (B : Set G) :=
      hMLle.trans (sup_le ((IsCompIn.le_layerIn hL).trans (layerIn_le_normalizer hBcomp))
        ((IsCompIn.le_layerIn hLyc).trans (layerIn_le_normalizer hBcomp)))
    exact not_le_normalizer_diag hc.x_sq hc.diagComm (IsCompIn.perfect hc.comp)
      hc.ne' hc.mem_iff' hle
  have hbad : BadI B r := ⟨hr, hrB, hBnotComp⟩
  refine ⟨hbad, ?_⟩
  obtain ⟨N, hSr, -⟩ := exists_swapCfg hS hB hx hbad hrx.symm
  by_cases hLy : cj y L = L
  · have hMLle' : M ≤ L := by
      rw [hLy, sup_idem] at hMLle
      exact hMLle
    have hLy' : CFSG.conjugate L y = L := by rwa [← cj_eq_conjugate_of_sq hyy]
    rcases commutator_zpowers_eq_self_or_le_centralizer hL.isQuasisimple hLy' with hcM | hLc
    · exact (aor_not_walterArrow_of_inCStar hM.1 L
        ⟨y, r, hc.y_ord, hr, hry.symm, hc.comp, hL, hMLle', hcM⟩).elim
    · have hLpair : IsComponentIn L (centralizer ({y, r} : Set G)) := by
        refine hL.mono ?_ hpair'
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        rcases hw with rfl | hw
        · exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hz)).symm
        · rw [Set.mem_singleton_iff.mp hw]
          exact (Subgroup.mem_centralizer_singleton_iff.mp (hL.1 hz)).symm
      rw [hMpair.eq_of_le hLpair hMLle']
      exact hL
  · exfalso
    have hLyX : IsComponentIn (cj y L) (centralizer ({r} : Set G)) := isCompIn_cj_of_mem hL hyX
    have hcL : DiagComm y L := hL.commute_of_ne hLyX (Ne.symm hLy)
    have hfix : ∀ k ∈ M, y * k * y⁻¹ = k := by
      intro k hk
      have hk' : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 (hc.comp.1 hk)
      rw [← hk']
      group
    have hD : (diagHom hcL).range ≤ centralizer ({y, r} : Set G) := by
      rintro _ ⟨m, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hfx := diag_fixed hyy hcL m.2
      have hmr : m.1 ∈ centralizer ({r} : Set G) := hL.1 m.2
      have hymr : y * m.1 * y⁻¹ ∈ centralizer ({r} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hyX hmr) (Subgroup.inv_mem _ hyX)
      rcases hw with rfl | hw
      · change w * diag w m.1 = diag w m.1 * w
        calc w * diag w m.1 = (w * diag w m.1 * w⁻¹) * w := by group
          _ = _ := by rw [hfx]
      · rw [Set.mem_singleton_iff.mp hw]
        have := Subgroup.mem_centralizer_singleton_iff.1
          (Subgroup.mul_mem _ hmr hymr)
        exact this.symm
    have hMd := diag_eq_of_component hyy hcL hL.isQuasisimple hMpair hMLle hfix hD
    have hML : ¬ ∀ m ∈ M, ∀ l ∈ L, m * l = l * m := by
      intro h
      apply diag_not_centralize_left hyy hcL (IsCompIn.not_commute hL)
      intro m hm n hn
      exact h (diag y m) ((hMd _).2 ⟨m, hm, rfl⟩) n hn
    exact ncpw_not_alt3 hc.comm hrx.symm hry.symm hc hSr hL hML hLy hMd

theorem ncpw_cj_ne_of_not_centralizes [Finite G] {B : Subgroup G} {u b : G}
    {M' : Subgroup G} (h : SwapCfg B u b M') {L : Subgroup G}
    (hL : IsComponentIn L (centralizer ({b} : Set G)))
    (hBL : ¬ ∀ c ∈ B, ∀ l ∈ L, c * l = l * c) : cj u L ≠ L := by
  intro hLu
  rcases (h.support hL).1 hBL with hLM | hLcj
  · apply h.ne'
    rw [← hLM]
    exact hLu
  · have h1 : cj u L = M' := by rw [hLcj, cj_cj_of_mul_self h.x_sq M']
    apply h.ne'
    rw [← hLcj]
    exact hLu.symm.trans h1

theorem SwapCfg.mem_centralizer_sup [Finite G] {B M : Subgroup G} {x y : G}
    (h : SwapCfg B x y M) {g : G} (hgN : g ∈ normalizer (M : Set G))
    (hgB : ∀ b ∈ B, g * b = b * g) :
    g ∈ centralizer ((M ⊔ CFSG.conjugate M x : Subgroup G) : Set G) := by
  obtain ⟨h1, h2⟩ := h.centralizes_of_mem_normalizer hgN hgB
  have hle : M ⊔ CFSG.conjugate M x ≤ centralizer ({g} : Set G) := by
    refine sup_le (fun m hm => Subgroup.mem_centralizer_singleton_iff.2 (h1 m hm).symm)
      (fun m hm => ?_)
    have hm' : m ∈ cj x M := by
      rwa [cj_eq_conjugate_of_sq h.x_sq]
    have hm'' : x⁻¹ * m * x ∈ M := mem_cj.1 hm'
    have := h2 _ hm''
    have e : x * (x⁻¹ * m * x) * x⁻¹ = m := by group
    rw [e] at this
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  exact Subgroup.mem_centralizer_iff.2 fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hw)

theorem goodI_of_fourGroup [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B : Subgroup G} (hB : Unp B) {u₁ u₂ : G} (h₁ : GoodI B u₁) (h₂ : GoodI B u₂)
    (h₃ : GoodI B (u₁ * u₂)) (h12 : u₁ * u₂ = u₂ * u₁) {b : G} (hb : orderOf b = 2)
    (hbB : b ∈ centralizer (B : Set G)) (hb₁ : u₁ * b = b * u₁) (hb₂ : u₂ * b = b * u₂) :
    GoodI B b := by
  refine goodI_of_not_badI hb hbB ?_
  intro hbad
  obtain ⟨M, hS₁, -⟩ := exists_swapCfg hS hB h₁ hbad hb₁
  have hsupp : cj u₂ M = M ∨ cj u₂ M = cj u₁ M :=
    hS₁.cj_mem_support hb₂ fun c hc =>
      (Subgroup.mem_centralizer_singleton_iff.1 (h₂.2.le hc)).symm
  rcases hsupp with hcase | hcase
  · obtain ⟨M₂, hS₂, -⟩ := exists_swapCfg hS hB h₂ hbad hb₂
    exact ncpw_cj_ne_of_not_centralizes (h := hS₂) hS₁.comp hS₁.not_centralizes_left hcase
  · have hxy3 : (u₁ * u₂) * b = b * (u₁ * u₂) := by
      calc (u₁ * u₂) * b = u₁ * (u₂ * b) := by group
        _ = u₁ * (b * u₂) := by rw [hb₂]
        _ = (u₁ * b) * u₂ := by group
        _ = (b * u₁) * u₂ := by rw [hb₁]
        _ = b * (u₁ * u₂) := by group
    obtain ⟨M₃, hS₃, -⟩ := exists_swapCfg hS hB h₃ hbad hxy3
    have hcjcj : cj (u₁ * u₂) M = M := by
      have h1sq : u₁ * u₁ = 1 := mul_self_eq_one_of_orderOf h₁.1
      calc cj (u₁ * u₂) M = cj u₁ (cj u₂ M) := (Subgroup.map_conj_map_conj M u₂ u₁).symm
        _ = cj u₁ (cj u₁ M) := by rw [hcase]
        _ = M := cj_cj_of_mul_self h1sq M
    exact ncpw_cj_ne_of_not_centralizes (h := hS₃) hS₁.comp hS₁.not_centralizes_left hcjcj

theorem ncpw_swap_package [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B : Subgroup G} (hB : Unp B) {z y : G} {M : Subgroup G} (hz : GoodI B z)
    (hc : SwapCfg B z y M) (hM : Unp M) {P : Subgroup G}
    (hPy : P ≤ centralizer ({y} : Set G)) (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p)
    (hPz : ∀ p ∈ P, p * z = z * p) (hzP : z ∈ P) :
    (P ⊓ normalizer (M : Set G)).relIndex P = 2 ∧
      ∀ r ∈ P ⊓ normalizer (M : Set G), orderOf r = 2 →
        BadI B r ∧ IsComponentIn M (centralizer ({r} : Set G)) ∧
          IsComponentIn (cj z M) (centralizer ({r} : Set G)) := by
  refine ⟨hc.relIndex_normalizer_eq_two hPy hPB hzP, ?_⟩
  intro r hr hr2
  have hrP : r ∈ P := hr.1
  have hrN : r ∈ normalizer (M : Set G) := hr.2
  have hrB : ∀ b ∈ B, r * b = b * r := hPB r hrP
  have hrz : r * z = z * r := hPz r hrP
  have hry : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.1 (hPy hrP)
  have hrB' : r ∈ centralizer (B : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun b hb => (hrB b hb).symm
  obtain ⟨hbad, hMX⟩ := bad_and_comp_of_swapCfg hS hB hz hc hM hr2 hrz hry hrB'
    (hc.mem_centralizer_sup hrN hrB)
  exact ⟨hbad, hMX, isCompIn_cj_of_mem hMX (Subgroup.mem_centralizer_singleton_iff.2 hrz.symm)⟩

theorem ncpw_false_of_commuting_bad_pair [Finite G] {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {B : Subgroup G} (hB : Unp B) {z y y' : G}
    (hz : GoodI B z) (hy : BadI B y) (hy' : BadI B y') (hw : GoodI B (y * y'))
    {P : Subgroup G} (hP : IsPGroup 2 P) (h8 : 8 ≤ Nat.card P)
    (hPB : ∀ p ∈ P, ∀ b ∈ B, p * b = b * p) (hzP : z ∈ P) (hPz : ∀ p ∈ P, p * z = z * p)
    (hyP : y ∈ P) (hy'P : y' ∈ P) (hPy : ∀ p ∈ P, p * y = y * p)
    (hPy' : ∀ p ∈ P, p * y' = y' * p) : False := by
  have hzy : z * y = y * z := (hPz y hyP).symm
  have hzy' : z * y' = y' * z := (hPz y' hy'P).symm
  obtain ⟨M, hS₁, hM⟩ := exists_swapCfg hS hB hz hy hzy
  obtain ⟨M', hS', hM'u⟩ := exists_swapCfg hS hB hz hy' hzy'
  have hPyc : P ≤ centralizer ({y} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPy p hp)
  have hPy'c : P ≤ centralizer ({y'} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.2 (hPy' p hp)
  obtain ⟨hRi, hRinv⟩ := ncpw_swap_package hS hB hz hS₁ hM hPyc hPB hPz hzP
  obtain ⟨hR'i, hR'inv⟩ := ncpw_swap_package hS hB hz hS' hM'u hPy'c hPB hPz hzP
  have hyN : y ∈ normalizer (M : Set G) :=
    mem_normalizer_of_centralizes fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hS₁.comp.1 hm)).symm
  have hyR : y ∈ P ⊓ normalizer (M : Set G) := ⟨hyP, hyN⟩
  have hy'notR : y' ∉ P ⊓ normalizer (M : Set G) := by
    intro hy'R
    have hyy'R : y * y' ∈ P ⊓ normalizer (M : Set G) :=
      (P ⊓ normalizer (M : Set G)).mul_mem hyR hy'R
    exact (hRinv (y * y') hyy'R hw.1).1.not_goodI hw
  have hM'neM : M' ≠ M := by
    intro hEq
    apply hy'notR
    refine ⟨hy'P, ?_⟩
    rw [← hEq]
    exact mem_normalizer_of_centralizes (M := M') fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hS'.comp.1 hm)).symm
  have hM'neCj : M' ≠ cj z M := by
    intro hEq
    apply hy'notR
    refine ⟨hy'P, ?_⟩
    have hzy'conj : z * y' * z⁻¹ = y' := by rw [hzy']; group
    have h1 : cj z (centralizer ({y'} : Set G)) = centralizer ({y'} : Set G) := by
      rw [cj_centralizer_singleton z y', hzy'conj]
    have h2 : cj z M' ≤ centralizer ({y'} : Set G) := h1 ▸ cj_mono z hS'.comp.1
    rw [hEq, cj_cj_of_mul_self hS₁.x_sq M] at h2
    exact mem_normalizer_of_centralizes (M := M) fun m hm =>
      (Subgroup.mem_centralizer_singleton_iff.1 (h2 hm)).symm
  have hCjM'neM : cj z M' ≠ M := by
    intro hEq
    apply hM'neCj
    have h := congrArg (cj z) hEq
    rw [cj_cj_of_mul_self hS'.x_sq M'] at h
    exact h
  have hCjM'neCj : cj z M' ≠ cj z M := by
    intro hEq
    apply hM'neM
    have h := congrArg (cj z) hEq
    rw [cj_cj_of_mul_self hS'.x_sq M', cj_cj_of_mul_self hS₁.x_sq M] at h
    exact h
  obtain ⟨w, hwRR', hw2⟩ :=
    exists_involution_inf (R := P ⊓ normalizer (M : Set G))
      (R' := P ⊓ normalizer (M' : Set G)) hP h8 inf_le_left inf_le_left hRi hR'i
  have hMw : IsComponentIn M (centralizer ({w} : Set G)) := (hRinv w hwRR'.1 hw2).2.1
  have hCjw : IsComponentIn (cj z M) (centralizer ({w} : Set G)) := (hRinv w hwRR'.1 hw2).2.2
  have hM'w : IsComponentIn M' (centralizer ({w} : Set G)) := (hR'inv w hwRR'.2 hw2).2.1
  have hCj'w : IsComponentIn (cj z M') (centralizer ({w} : Set G)) :=
    (hR'inv w hwRR'.2 hw2).2.2
  exact false_of_four_components (X := centralizer ({w} : Set G)) (IsCompIn.not_commute hz.2)
    hMw hCjw hM'w hCj'w hM'neM hM'neCj hCjM'neM hCjM'neCj hS₁.le_sup hS'.le_sup

theorem ncpw_no_bad_in_sylow [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B : Subgroup G} (hB : Unp B) {u₁ u₂ : G} (h₁ : GoodI B u₁) (h₂ : GoodI B u₂)
    (h₃ : GoodI B (u₁ * u₂)) (h12 : u₁ * u₂ = u₂ * u₁) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTB : T ≤ centralizer (B : Set G)) (hu₁ : u₁ ∈ T) (hu₂ : u₂ ∈ T)
    (hrank : 3 ≤ CFSG.Open.pRank 2 T) : ¬ ∃ y ∈ T, BadI B y := by
  rintro ⟨y, hyT, hy⟩
  obtain ⟨y, hyT, hy', hmax⟩ := exists_max_bad ⟨y, hyT, badI_iff.1 hy⟩
  have hy : BadI B y := badI_iff.2 hy'
  let P : Subgroup G := T ⊓ centralizer ({y} : Set G)
  have hBc : ∀ t ∈ T, ∀ b ∈ B, t * b = b * t := by
    intro t ht b hb
    exact (Subgroup.mem_centralizer_iff.1 (hTB ht) b hb).symm
  obtain ⟨z, hzT, hz2, hzc⟩ := exists_central_involution hT hu₁ h₁.1
  have hzgood : GoodI B z :=
    goodI_of_fourGroup hS hB h₁ h₂ h₃ h12 hz2 (hTB hzT) (hzc u₁ hu₁).symm (hzc u₂ hu₂).symm
  have hne : ∃ t ∈ T, y * t ≠ t * y := by
    by_contra hcon
    push Not at hcon
    exact hy.not_goodI
      (goodI_of_fourGroup hS hB h₁ h₂ h₃ h12 hy.1 hy.2.1
        (hcon u₁ hu₁).symm (hcon u₂ hu₂).symm)
  have hyz : y ≠ z := by
    rintro rfl
    exact hy.not_goodI hzgood
  have hyz_comm : y * z = z * y := (hzc y hyT).symm
  have hyP : y ∈ P :=
    ⟨hyT, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hzP : z ∈ P :=
    ⟨hzT, Subgroup.mem_centralizer_singleton_iff.2 (hzc y hyT)⟩
  have h4 : 4 ≤ Nat.card P :=
    four_le_card_of_involutions hy.1 hz2 hyz hyz_comm hyP hzP
  have hne4 : Nat.card P ≠ 4 := by
    intro h4eq
    have hle : CFSG.Open.pRank 2 T ≤ 2 :=
      pRank_le_two_of_centralizer_card_four' hT hyT hy.1 h4eq
    omega
  have hP2 : IsPGroup 2 P := hT.to_le inf_le_left
  have h8 : 8 ≤ Nat.card P := eight_le_card hP2 h4 hne4
  obtain ⟨g, hgT, -, hy'P, hy'cent, hw2, hlt⟩ := exists_conj_in_center hT hyT hy.1 hne
  have hy'bad : BadI B (g * y * g⁻¹) :=
    hy.conj fun b hb => hBc g hgT b hb
  have hy'T : g * y * g⁻¹ ∈ T := hy'P.1
  have hwT : y * (g * y * g⁻¹) ∈ T := T.mul_mem hyT hy'T
  have hwgood : GoodI B (y * (g * y * g⁻¹)) :=
    goodI_of_not_badI hw2 (hTB hwT) fun hbadw =>
      (not_lt_of_ge (hmax (y * (g * y * g⁻¹)) hwT (badI_iff.1 hbadw))) hlt
  exact ncpw_false_of_commuting_bad_pair hS hB hzgood hy hy'bad hwgood hP2 h8
    (fun p hp b hb => hBc p hp.1 b hb)
    hzP (fun p hp => (hzc p hp.1).symm)
    hyP hy'P (fun p hp => Subgroup.mem_centralizer_singleton_iff.1 hp.2)
    (fun p hp => hy'cent p hp)

theorem componentAt_of_fourGroup [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {B : Subgroup G} (hB : Unp B) {u₁ u₂ : G} (h₁ : GoodI B u₁) (h₂ : GoodI B u₂)
    (h₃ : GoodI B (u₁ * u₂)) (h12 : u₁ * u₂ = u₂ * u₁)
    (h3 : 3 ≤ CFSG.Open.pRank 2 (centralizer (B : Set G))) : ComponentAtCentralInvolutions B := by
  classical
  by_contra hnu
  unfold ComponentAtCentralInvolutions at hnu
  push Not at hnu
  obtain ⟨y₀, hy₀ord, hy₀C, hy₀nc⟩ := hnu
  have hy₀ : BadI B y₀ := ⟨hy₀ord, hy₀C, hy₀nc⟩
  let C : Subgroup G := centralizer (B : Set G)
  have hu₁C : u₁ ∈ C := Subgroup.mem_centralizer_iff.2 fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 (h₁.2.le hb)
  have hu₂C : u₂ ∈ C := Subgroup.mem_centralizer_iff.2 fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.1 (h₂.2.le hb)
  have hUC : zpowers u₁ ⊔ zpowers u₂ ≤ C :=
    sup_le (Subgroup.zpowers_le.2 hu₁C) (Subgroup.zpowers_le.2 hu₂C)
  have hU : IsPGroup 2 ↥(zpowers u₁ ⊔ zpowers u₂) :=
    isPGroup_two_sup_zpowers h₁.1 h₂.1 h12
  obtain ⟨T, hTC, hT, hUT, hconj⟩ := exists_sylow_forall_conj hU hUC
  have hy₀U : IsPGroup 2 ↥(zpowers y₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy₀ord]; norm_num)
  obtain ⟨c, hcC, hcj⟩ := hconj (zpowers y₀) hy₀U (Subgroup.zpowers_le.2 hy₀C)
  have hyT : c * y₀ * c⁻¹ ∈ T := hcj (conj_mem_cj (Subgroup.mem_zpowers y₀))
  have hybad : BadI B (c * y₀ * c⁻¹) :=
    hy₀.conj fun b hb => (Subgroup.mem_centralizer_iff.1 hcC b hb).symm
  have hrank : 3 ≤ CFSG.Open.pRank 2 T := three_le_pRank_of_conj hconj h3
  exact ncpw_no_bad_in_sylow hS hB h₁ h₂ h₃ h12 hT hTC
    (hUT (Subgroup.mem_sup_left (Subgroup.mem_zpowers u₁)))
    (hUT (Subgroup.mem_sup_right (Subgroup.mem_zpowers u₂)))
    hrank ⟨c * y₀ * c⁻¹, hyT, hybad⟩

end CFSG.OddStandard.SmallF3.Omega.NCPWide
