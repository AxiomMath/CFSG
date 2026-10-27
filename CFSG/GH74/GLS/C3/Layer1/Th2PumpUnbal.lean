module

public import CFSG.GH74.GLS.C3.Layer1.BkIv10
public import CFSG.GH74.GLS.C3.Layer1.Th2PumpTerm
public import CFSG.GH74.GLS.C3.Layer1.Th2L84
public import CFSG.GH74.GLS.C3.Layer1.Th2Main
public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Der10C2
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i
public import CFSG.GH74.GLS.C3.Layer1.Th2L83GenCore
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic6
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic7
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic9
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt69
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Closed2
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Stmt
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt10
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt12
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Stmt9
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Kinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop41
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop43
public import CFSG.GH74.GLS.Stage2.Signalizer.Prop47
public import CFSG.GH74.GLS.Stage2.Signalizer.SDWr
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt5

public section

namespace CFSG.GH74.GLS.Th2.PumpUnbal

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Bk
open scoped commutatorElement

section KSide

variable {G : Type} [Group G] [Finite G]

theorem exists_oddNormal_fixed
    {x y : G} {K : Subgroup G} (hlu : IsLocallyUnbalancing x y K)
    {q : ℕ} (hq : IsFM9 q) (hL2 : HasL2Model (kBar K) (fun r => r = q)) :
    ∃ W' : Subgroup (kBar K), W' ≠ ⊥ ∧
      W' ≤ fixedSubgroup (kBar K) (Back.actHom (hLn_normalizer K) ⟨y, hlu.2.2.2.1⟩) ∧
      Odd (Nat.card ↥W') ∧
      ∀ c ∈ fixedSubgroup (kBar K) (Back.actHom (hLn_normalizer K) ⟨y, hlu.2.2.2.1⟩),
        ∀ k ∈ W', c * k * c⁻¹ ∈ W' := by
  obtain ⟨⟨hx2, hKc⟩, hy2, hyC, hyN, hWnot⟩ := hlu
  have hKx : K ≤ centralizer ({x} : Set G) := hKc.1
  have hsimple : IsSimpleGroup (kBar K) := Back.isSimpleGroup_of_hasL2Model hL2
  obtain ⟨hcen, hZ⟩ := no_central_involution hKc hsimple
  have hWN := pPrimeCoreOf_centralizer_le_normalizer hKc hy2 hyN hZ
  set M₀ : Subgroup G := normalizer (K : Set G) with hM₀
  have hLn := hLn_normalizer K
  set Zxy : Subgroup G := centralizer ({x, y} : Set G) with hZxy
  have hZmem : ∀ z, z ∈ Zxy ↔ z * x = x * z ∧ z * y = y * z := by
    intro z
    simp only [hZxy, Subgroup.mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  set W : Subgroup G := pPrimeCoreOf 2 Zxy with hWdef
  set N₁ : Subgroup G := Zxy ⊓ normalizer (K : Set G) with hN₁
  have hWZ : W ≤ Zxy := TwoThin.pPrimeCoreOf_le Zxy
  have hWM : W ≤ M₀ := hWN
  have hWN₁ : W ≤ N₁ := fun w hw => ⟨hWZ hw, hWN hw⟩
  have hlift : ∀ kb : kBar K, Back.actHom hLn ⟨y, hyN⟩ kb = kb →
      (MulAut.conj kb : MulAut (kBar K)) ∈ actImg hLn N₁ := by
    intro kb hfix
    obtain ⟨c, hcy, rfl⟩ := exists_lift_fixed hy2 hyN hLn kb hfix
    have hcM : (c : G) ∈ M₀ := le_normalizer c.2
    refine mem_actImg_iff hLn |>.2 ⟨⟨c, hcM⟩, ⟨(hZmem c).2 ⟨?_, hcy⟩, le_normalizer c.2⟩, ?_⟩
    · exact mem_centralizer_singleton_iff.1 (hKx c.2)
    · exact Back.actHom_of_mem hLn c.2 hcM
  have hCc : ∀ φ ∈ actImg hLn N₁,
      φ * Back.actHom hLn ⟨y, hyN⟩ = Back.actHom hLn ⟨y, hyN⟩ * φ := by
    intro φ hφ
    obtain ⟨m, hmN, rfl⟩ := (mem_actImg_iff hLn).1 hφ
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext ((hZmem m).1 hmN.1).2
  have hWCc : actImg hLn W ≤ actImg hLn N₁ := by
    intro φ hφ
    obtain ⟨m, hmW, rfl⟩ := (mem_actImg_iff hLn).1 hφ
    exact (mem_actImg_iff hLn).2 ⟨m, hWN₁ hmW, rfl⟩
  have hWn : ∀ c ∈ actImg hLn N₁, ∀ w ∈ actImg hLn W, c * w * c⁻¹ ∈ actImg hLn W := by
    intro c hc w hw
    obtain ⟨n, hnN, rfl⟩ := (mem_actImg_iff hLn).1 hc
    obtain ⟨m, hmW, rfl⟩ := (mem_actImg_iff hLn).1 hw
    refine (mem_actImg_iff hLn).2 ⟨n * m * n⁻¹, ?_, by simp⟩
    exact TwoThin.pPrimeCoreOf_normalized Zxy hnN.1 hmW
  have hodd : Odd (Nat.card ↥(actImg hLn W)) := by
    have h1 : Nat.card ↥(actImg hLn W) ∣ Nat.card ↥(W.subgroupOf M₀) :=
      Subgroup.card_map_dvd (W.subgroupOf M₀) (Back.actHom hLn)
    have h2 : Nat.card ↥(W.subgroupOf M₀) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv
    exact Odd.of_dvd_nat (by rw [h2]; exact TwoThin.card_pPrimeCoreOf_odd Zxy) h1
  have hWbot : actImg hLn W ≠ ⊥ := by
    intro hbot
    apply hWnot
    intro w hw
    have h1 : Back.actHom hLn ⟨w, hWM hw⟩ = 1 := by
      have : Back.actHom hLn ⟨w, hWM hw⟩ ∈ actImg hLn W :=
        (mem_actImg_iff hLn).2 ⟨⟨w, hWM hw⟩, hw, rfl⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.1 this
    exact ⟨hWN hw, TwoThin.mem_normalizer_pPrimeCoreOf (hWN hw),
      fun k hk => (Back.actHom_eq_one_iff_commutator_mem hLn ⟨w, hWM hw⟩).1 h1 k hk⟩
  have hne := pPrimeCoreOf_ne_bot_of_lift hcen hCc hlift hWCc hWn hodd hWbot
  obtain ⟨F, _, _, e0, hF, hFq⟩ := IVK.Proofs2.exists_l2Field_of_hasL2Model hq hL2
  have hfm : IsFM9 (Nat.card F) := hFq ▸ hq
  have hinj : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)) := by
    intro a b hab
    have h1 : MulAut.conj (a * b⁻¹) = (1 : MulAut (kBar K)) := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : a * b⁻¹ = 1 := conj_injective_of_center_bot hcen (h1.trans (map_one _).symm)
    exact mul_inv_eq_one.1 h2
  exact IVK.Proofs2.exists_normal_odd_fixed hinj
    (fun w hw => IVK.Proofs2.mem_innAut_of_odd_orderOf hF hfm e0 hw)
    (le_sup_left : IVK.innAut (kBar K) ≤ (MulAut.conj : kBar K →* MulAut (kBar K)).range ⊔ actImg hLn N₁)
    hne

end KSide

section MSide

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid

variable {G : Type} [Group G] [Finite G]

theorem locUnbal_of_oddNormal {u y : G} {M : Subgroup G} (hu2 : orderOf u = 2) (hy2 : orderOf y = 2)
    (hyP : y ∈ centralizer ({u} : Set G)) (hM : IsPCompIn 2 (centralizer ({u} : Set G)) M)
    (hMN : ∀ c ∈ centralizer ({u} : Set G), ∀ m ∈ M, c * m * c⁻¹ ∈ M) (hMcen : CenterlessBar M)
    (Z : Subgroup (TwoThin.barQ ↥(centralizer ({u} : Set G))))
    (hZS : Z ≤ bar u M) (hZodd : Odd (Nat.card ↥Z)) (hZne : Z ≠ ⊥)
    (hZfix : ∀ z ∈ Z, sbar y hyP * z = z * sbar y hyP)
    (hZn : ∀ (c : G) (hc : c ∈ centralizer ({u} : Set G)), c * y = y * c →
      ∀ z ∈ Z, sbar c hc * z * (sbar c hc)⁻¹ ∈ Z) :
    IsLocallyUnbalancing u y M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyN : y ∈ normalizer (M : Set G) := mem_normalizer_K_of_KN hMN hyP
  refine ⟨⟨hu2, hM⟩, hy2, hyP, hyN, ?_⟩
  intro hle
  obtain ⟨z, hzZ, hz1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left hZne
  obtain ⟨mP, hmP, hmz⟩ := hZS hzZ
  have hLn : ∀ m ∈ (centralizer ({u} : Set G)), ∀ l ∈ (centralizer ({u} : Set G)), m * l * m⁻¹ ∈ (centralizer ({u} : Set G)) := fun m hm l hl =>
    (centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).mul_mem hm hl) ((centralizer ({u} : Set G)).inv_mem hm)
  have hfix : Back.actHom hLn ⟨y, hyP⟩ z = z := by
    have hc := hZfix z hzZ
    rw [← hmz] at hc ⊢
    change Back.actHom hLn ⟨y, hyP⟩ (QuotientGroup.mk mP) = QuotientGroup.mk mP
    rw [Back.actHom_mk]
    have h1 : (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyP⟩) * TwoThin.barMk ↥(centralizer ({u} : Set G)) mP * (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y, hyP⟩)⁻¹ =
        TwoThin.barMk ↥(centralizer ({u} : Set G)) mP := by
      have := hc
      simp only [sbar] at this
      rw [this]
      group
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  obtain ⟨c, hcy, hcz⟩ := exists_lift_fixed hy2 hyP hLn z hfix
  have hcπ : TwoThin.barMk ↥(centralizer ({u} : Set G)) c = z := hcz
  obtain ⟨Zh, hZh⟩ : ∃ Zh : Subgroup G, Zh = ((Z.comap (TwoThin.barMk ↥(centralizer ({u} : Set G)))).map (centralizer ({u} : Set G)).subtype) ⊓
      centralizer ({y} : Set G) := ⟨_, rfl⟩
  have hmem : ∀ g : G, g ∈ Zh ↔ ∃ hgP : g ∈ (centralizer ({u} : Set G)),
      TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨g, hgP⟩ ∈ Z ∧ g ∈ centralizer ({y} : Set G) := by
    intro g
    rw [hZh, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hgy⟩
      exact ⟨x.2, hx, hgy⟩
    · rintro ⟨hgP, hgZ, hgy⟩
      exact ⟨⟨⟨g, hgP⟩, hgZ, rfl⟩, hgy⟩
  have hZhX : Zh ≤ centralizer ({u, y} : Set G) := by
    intro g hg
    obtain ⟨hgP, -, hgy⟩ := (hmem g).1 hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | hh
    · exact (mem_centralizer_singleton_iff.1 hgP).symm
    · rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (mem_centralizer_singleton_iff.1 hgy).symm
  have hnorm : ∀ g ∈ centralizer ({u, y} : Set G), ∀ n ∈ Zh, g * n * g⁻¹ ∈ Zh := by
    intro g hg n hn
    have hgu : g ∈ (centralizer ({u} : Set G)) :=
      mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hg u (by simp)).symm)
    have hgy : g ∈ centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hg y (by simp)).symm)
    obtain ⟨hnP, hnZ, hny⟩ := (hmem n).1 hn
    have hmul : g * n * g⁻¹ ∈ (centralizer ({u} : Set G)) :=
      (centralizer ({u} : Set G)).mul_mem ((centralizer ({u} : Set G)).mul_mem hgu hnP) ((centralizer ({u} : Set G)).inv_mem hgu)
    refine (hmem _).2 ⟨hmul, ?_, ?_⟩
    · have h1 : (⟨g * n * g⁻¹, hmul⟩ : ↥(centralizer ({u} : Set G))) = ⟨g, hgu⟩ * ⟨n, hnP⟩ * ⟨g, hgu⟩⁻¹ :=
        Subtype.ext (by simp)
      rw [h1, map_mul, map_mul, map_inv]
      exact hZn g hgu (mem_centralizer_singleton_iff.1 hgy) _ hnZ
    · exact (centralizer ({y} : Set G)).mul_mem
        ((centralizer ({y} : Set G)).mul_mem hgy hny) ((centralizer ({y} : Set G)).inv_mem hgy)
  have hZhodd : Odd (Nat.card ↥Zh) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card ↥Zh := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥Zh) 2 h2
    obtain ⟨hgP, hgZ, -⟩ := (hmem (a : G)).1 a.2
    have hao : orderOf (a : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ha
    have hsq : (⟨(a : G), hgP⟩ : ↥(centralizer ({u} : Set G))) ^ 2 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hao]
      exact pow_orderOf_eq_one _
    have hzz2 : (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨(a : G), hgP⟩) ^ 2 = 1 := by
      rw [← map_pow, hsq, map_one]
    have hcop : Nat.Coprime 2 (Nat.card ↥Z) := Nat.coprime_two_left.2 hZodd
    have hzz1 : TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨(a : G), hgP⟩ = 1 := by
      have h1 : orderOf (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨(a : G), hgP⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hzz2
      have h2' : orderOf (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨(a : G), hgP⟩) ∣ Nat.card ↥Z :=
        Subgroup.orderOf_dvd_natCard Z hgZ
      have h3 : orderOf (TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨(a : G), hgP⟩) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2'
      exact orderOf_eq_one_iff.1 h3
    have hO : (a : G) ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G)) :=
      Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hgP, (QuotientGroup.eq_one_iff _).1 hzz1⟩
    have hodd2 : Odd (orderOf (a : G)) :=
      Odd.of_dvd_nat (TwoThin.card_pPrimeCoreOf_odd (centralizer ({u} : Set G))) (Subgroup.orderOf_dvd_natCard _ hO)
    rw [hao] at hodd2
    exact absurd hodd2 (by decide)
  have hZhle : Zh ≤ pPrimeCoreOf 2 (centralizer ({u, y} : Set G)) :=
    Stage2.Bender.Thm2.le_pPrimeCoreOf_of_normal_odd hZhX hnorm hZhodd
  have hwZh : (c : G) ∈ Zh := (hmem _).2 ⟨c.2, by simpa [hcπ] using hzZ, mem_centralizer_singleton_iff.2 hcy⟩
  have hwc : (c : G) ∈ centralizerSection M (pPrimeCoreOf 2 M) := hle (hZhle hwZh)
  have hmP' : (mP : G) ∈ M := Subgroup.mem_subgroupOf.mp hmP
  have hoO : ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G) ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
    have h1 : (QuotientGroup.mk mP : kBar (centralizer ({u} : Set G))) = QuotientGroup.mk c := by
      change TwoThin.barMk ↥(centralizer ({u} : Set G)) mP = TwoThin.barMk ↥(centralizer ({u} : Set G)) c
      rw [hmz, hcπ]
    rw [QuotientGroup.eq] at h1
    exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨(mP⁻¹ * c).2, h1⟩
  have hoP : ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G) ∈ (centralizer ({u} : Set G)) := (mP⁻¹ * c).2
  have hoN : ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G) ∈ normalizer (M : Set G) := mem_normalizer_K_of_KN hMN hoP
  have hocs : ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G) ∈ centralizerSection M (pPrimeCoreOf 2 M) := by
    refine ⟨hoN, TwoThin.mem_normalizer_pPrimeCoreOf hoN, fun k hk => ?_⟩
    have hkP : k ∈ (centralizer ({u} : Set G)) := hM.1 hk
    have h1 : ⁅k, ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G)⁆ ∈ pPrimeCoreOf 2 (centralizer ({u} : Set G)) := by
      rw [commutatorElement_def]
      exact (pPrimeCoreOf 2 (centralizer ({u} : Set G))).mul_mem (TwoThin.pPrimeCoreOf_normalized (centralizer ({u} : Set G)) hkP hoO)
        ((pPrimeCoreOf 2 (centralizer ({u} : Set G))).inv_mem hoO)
    have h2 : ⁅k, ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G)⁆ ∈ M := by
      have : ⁅k, ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G)⁆ =
          k * (((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G) * k⁻¹ * ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact M.mul_mem hk ((Subgroup.mem_normalizer_iff.1 hoN _).1 (M.inv_mem hk))
    exact Th2.inf_le_pPrimeCoreOf hM.1 ⟨h1, h2⟩
  have hmcs : (mP : G) ∈ centralizerSection M (pPrimeCoreOf 2 M) := by
    have := (centralizerSection M (pPrimeCoreOf 2 M)).mul_mem hwc
      ((centralizerSection M (pPrimeCoreOf 2 M)).inv_mem hocs)
    have e : (c : G) * ((mP⁻¹ * c : ↥(centralizer ({u} : Set G))) : G)⁻¹ = (mP : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e] at this
  have hmO : (mP : G) ∈ pPrimeCoreOf 2 M :=
    mem_pPrimeCoreOf_of_commutators hMcen hmP' hmcs.2.2
  have hOMP : pPrimeCoreOf 2 M ≤ pPrimeCoreOf 2 (centralizer ({u} : Set G)) :=
    Stage2.Bender.Thm2.le_pPrimeCoreOf_of_normal_odd
      ((TwoThin.pPrimeCoreOf_le M).trans hM.1)
      (fun g hg n hn => (Subgroup.mem_normalizer_iff.1
        (TwoThin.mem_normalizer_pPrimeCoreOf (mem_normalizer_K_of_KN hMN hg)) n).1 hn)
      (TwoThin.card_pPrimeCoreOf_odd M)
  obtain ⟨hxM, hmπ⟩ := Back.Setup91.mem_pPrimeCoreOf_iff.1 (hOMP hmO)
  apply hz1
  rw [← hmz]
  exact (QuotientGroup.eq_one_iff _).2 hmπ

end MSide

section Transport

open CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.PumpRigid

variable {G : Type} [Group G] [Finite G]

theorem exists_oddNormal_bar {x u y : G} {K M : Subgroup G}
    (hltM : PumpUpLT 2 x K u M) (e : kBar M ≃* kBar K) (hxM : x ∈ normalizer (M : Set G))
    (hMN : ∀ c ∈ (centralizer ({u} : Set G)), ∀ m ∈ M, c * m * c⁻¹ ∈ M)
    (hyP : y ∈ (centralizer ({u} : Set G))) (hyK : y ∈ normalizer (K : Set G))
    (W' : Subgroup (kBar K)) (hW'ne : W' ≠ ⊥)
    (hW'fix : W' ≤ fixedSubgroup (kBar K) (Back.actHom (hLn_normalizer K) ⟨y, hyK⟩))
    (hW'odd : Odd (Nat.card ↥W'))
    (hW'n : ∀ c ∈ fixedSubgroup (kBar K) (Back.actHom (hLn_normalizer K) ⟨y, hyK⟩),
      ∀ k ∈ W', c * k * c⁻¹ ∈ W') :
    ∃ Z : Subgroup (TwoThin.barQ ↥(centralizer ({u} : Set G))), Z ≤ bar u M ∧ Odd (Nat.card ↥Z) ∧ Z ≠ ⊥ ∧
      (∀ z ∈ Z, sbar y hyP * z = z * sbar y hyP) ∧
      ∀ (c : G) (hc : c ∈ (centralizer ({u} : Set G))), c * y = y * c → ∀ z ∈ Z, sbar c hc * z * (sbar c hc)⁻¹ ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxY : x ∈ (centralizer ({u} : Set G)) := TwoThin.mem_centralizer_symm hltM.2.2.1
  have hle : TwoThin.hatCard M ≤ TwoThin.hatCard K := (Nat.card_congr e.toEquiv).le
  obtain ⟨Λ, hΛ, -, ⟨eΛ⟩, -, -, hcases⟩ := rigid_step hltM hxY hle
  have hvert : bar u Λ = bar u M := (hcases.resolve_right (fun h => h.1 hxM)).2
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ (centralizer ({u} : Set G)) := hΛ.le.trans inf_le_right
  obtain ⟨φ, hφs, -, hφρ⟩ := TwoThin.exists_phi hΛK hΛY hΛ.cover
  have hφb : Function.Bijective φ :=
    hφs.bijective_of_nat_card_le (Nat.card_congr eΛ.toEquiv).ge
  have hyX : y ∈ normalizer ((K ⊓ (centralizer ({u} : Set G)) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_inf hyK (Subgroup.le_normalizer hyP)
  have hyΛ : ∀ a ∈ Λ, y * a * y⁻¹ ∈ Λ := fun a ha =>
    TwoThin.conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq hyX ha
  have hyΛN : y ∈ normalizer (Λ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact hyΛ a ha
    · intro ha
      have := TwoThin.conj_mem_of_unique_isPCompIn hΛ.pc hΛ.uniq (inv_mem hyX) ha
      simpa [mul_assoc] using this
  have hconjS : ∀ s ∈ bar u Λ, sbar y hyP * s * (sbar y hyP)⁻¹ ∈ bar u Λ := by
    intro s hs
    have h := map_conj_bar_of_normalizes (u := u) (X := Λ) hyP hyΛN
    rw [← h]
    exact ⟨s, hs, by simp [MulAut.conj_apply]⟩
  have hφequi : ∀ (s : ↥(bar u Λ)),
      φ ⟨sbar y hyP * (s : TwoThin.barQ ↥(centralizer ({u} : Set G))) * (sbar y hyP)⁻¹, hconjS _ s.2⟩ =
        Back.actHom (hLn_normalizer K) ⟨y, hyK⟩ (φ s) := by
    rintro ⟨s, hs⟩
    obtain ⟨⟨a, haP⟩, haΛ, rfl⟩ := hs
    have haΛ' : a ∈ Λ := Subgroup.mem_subgroupOf.mp haΛ
    have hyaΛ := hyΛ a haΛ'
    have e1 := hφρ a haΛ'
    have e2 := hφρ (y * a * y⁻¹) hyaΛ
    have hPe : (⟨y * a * y⁻¹, hΛY hyaΛ⟩ : ↥(centralizer ({u} : Set G))) =
        ⟨y, hyP⟩ * ⟨a, haP⟩ * ⟨y, hyP⟩⁻¹ := Subtype.ext rfl
    have e3 : (⟨sbar y hyP * TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, haP⟩ * (sbar y hyP)⁻¹, hconjS _ ⟨⟨a, haP⟩, haΛ, rfl⟩⟩ :
        ↥(bar u Λ)) = ⟨TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨y * a * y⁻¹, hΛY hyaΛ⟩,
          ⟨⟨y * a * y⁻¹, hΛY hyaΛ⟩, Subgroup.mem_subgroupOf.mpr hyaΛ, rfl⟩⟩ :=
      Subtype.ext (by simp only [hPe, map_mul, map_inv, sbar])
    rw [e3, e2]
    show QuotientGroup.mk ⟨y * a * y⁻¹, hΛK hyaΛ⟩ = Back.actHom (hLn_normalizer K) ⟨y, hyK⟩ _
    have e4 : (⟨TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, haP⟩, ⟨⟨a, haP⟩, haΛ, rfl⟩⟩ : ↥(bar u Λ)) =
        ⟨TwoThin.barMk ↥(centralizer ({u} : Set G)) ⟨a, hΛY haΛ'⟩, ⟨⟨a, hΛY haΛ'⟩, Subgroup.mem_subgroupOf.mpr haΛ', rfl⟩⟩ := rfl
    rw [e4, e1]
    show QuotientGroup.mk ⟨y * a * y⁻¹, hΛK hyaΛ⟩ =
      Back.actHom (hLn_normalizer K) ⟨y, hyK⟩ (QuotientGroup.mk ⟨a, hΛK haΛ'⟩)
    rw [Back.actHom_mk]
  obtain ⟨F, hF⟩ : ∃ F : Subgroup (TwoThin.barQ ↥(centralizer ({u} : Set G))),
      F = bar u M ⊓ centralizer ({sbar y hyP} : Set (TwoThin.barQ ↥(centralizer ({u} : Set G)))) :=
    ⟨_, rfl⟩
  obtain ⟨Z₁, hZ₁⟩ : ∃ Z₁ : Subgroup (TwoThin.barQ ↥(centralizer ({u} : Set G))),
      Z₁ = (W'.comap φ).map (bar u Λ).subtype := ⟨_, rfl⟩
  have hmemZ₁ : ∀ x' : TwoThin.barQ ↥(centralizer ({u} : Set G)),
      x' ∈ Z₁ ↔ ∃ hx : x' ∈ bar u Λ, φ ⟨x', hx⟩ ∈ W' := by
    intro x'
    rw [hZ₁, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s.2, hs⟩
    · rintro ⟨hx, hφx⟩
      exact ⟨⟨x', hx⟩, hφx, rfl⟩
  have hZ₁F : Z₁ ≤ F := by
    intro x' hx'
    obtain ⟨hxS, hφx⟩ := (hmemZ₁ x').1 hx'
    rw [hF]
    refine Subgroup.mem_inf.2 ⟨by rw [← hvert]; exact hxS, ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hfix : Back.actHom (hLn_normalizer K) ⟨y, hyK⟩ (φ ⟨x', hxS⟩) = φ ⟨x', hxS⟩ := hW'fix hφx
    have h2 := (hφequi ⟨x', hxS⟩).trans hfix
    have h3 := hφb.1 h2
    have h4 : sbar y hyP * x' * (sbar y hyP)⁻¹ = x' := congrArg Subtype.val h3
    calc x' * sbar y hyP = (sbar y hyP * x' * (sbar y hyP)⁻¹) * sbar y hyP := by rw [h4]
      _ = sbar y hyP * x' := by group
  have hZ₁odd : Odd (Nat.card ↥Z₁) := by
    rw [hZ₁, Subgroup.card_map_of_injective (bar u Λ).subtype_injective]
    have h1 : Nat.card ↥((W'.comap φ).map φ) = Nat.card ↥(W'.comap φ) :=
      Subgroup.card_map_of_injective hφb.1
    rw [Subgroup.map_comap_eq_self_of_surjective hφs] at h1
    rw [← h1]
    exact hW'odd
  have hZ₁ne : Z₁ ≠ ⊥ := by
    obtain ⟨k, hkW, hk1⟩ := (Subgroup.bot_or_exists_ne_one W').resolve_left hW'ne
    obtain ⟨s, hs⟩ := hφs k
    have hs1 : (s : TwoThin.barQ ↥(centralizer ({u} : Set G))) ≠ 1 := fun h =>
      hk1 (by rw [← hs, show s = 1 from Subtype.ext h, map_one])
    intro hbot
    apply hs1
    have : (s : TwoThin.barQ ↥(centralizer ({u} : Set G))) ∈ Z₁ :=
      (hmemZ₁ _).2 ⟨s.2, by simpa [hs] using hkW⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hZ₁n : ∀ f ∈ F, ∀ n ∈ Z₁, f * n * f⁻¹ ∈ Z₁ := by
    intro f hf n hn
    rw [hF] at hf
    obtain ⟨hfS', hfc⟩ := Subgroup.mem_inf.1 hf
    have hfS : f ∈ bar u Λ := by rw [hvert]; exact hfS'
    obtain ⟨hnS, hφn⟩ := (hmemZ₁ n).1 hn
    have hfnS : f * n * f⁻¹ ∈ bar u Λ :=
      (bar u Λ).mul_mem ((bar u Λ).mul_mem hfS hnS) ((bar u Λ).inv_mem hfS)
    refine (hmemZ₁ _).2 ⟨hfnS, ?_⟩
    have hφf : φ ⟨f, hfS⟩ ∈ fixedSubgroup (kBar K) (Back.actHom (hLn_normalizer K) ⟨y, hyK⟩) := by
      have hc : f * sbar y hyP = sbar y hyP * f := mem_centralizer_singleton_iff.1 hfc
      have h1 := hφequi ⟨f, hfS⟩
      have h4 : sbar y hyP * f * (sbar y hyP)⁻¹ = f := by
        calc sbar y hyP * f * (sbar y hyP)⁻¹ = (f * sbar y hyP) * (sbar y hyP)⁻¹ := by rw [hc]
          _ = f := by group
      have h2 : (⟨sbar y hyP * f * (sbar y hyP)⁻¹, hconjS _ hfS⟩ : ↥(bar u Λ)) = ⟨f, hfS⟩ :=
        Subtype.ext h4
      rw [h2] at h1
      exact h1.symm
    have : φ ⟨f * n * f⁻¹, hfnS⟩ = φ ⟨f, hfS⟩ * φ ⟨n, hnS⟩ * (φ ⟨f, hfS⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hW'n _ hφf _ hφn
  have hZ₁le : Z₁ ≤ pPrimeCoreOf 2 F :=
    Stage2.Bender.Thm2.le_pPrimeCoreOf_of_normal_odd hZ₁F hZ₁n hZ₁odd
  refine ⟨pPrimeCoreOf 2 F, ?_, TwoThin.card_pPrimeCoreOf_odd F, ?_, ?_, ?_⟩
  · intro z hz
    have := TwoThin.pPrimeCoreOf_le F hz
    rw [hF] at this
    exact (Subgroup.mem_inf.1 this).1
  · intro hbot
    apply hZ₁ne
    rw [eq_bot_iff]
    intro x' hx'
    have := hZ₁le hx'
    rw [hbot] at this
    exact this
  · intro z hz
    have := TwoThin.pPrimeCoreOf_le F hz
    rw [hF] at this
    exact (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2).symm
  · intro c hc hcy z hz
    have hgy : sbar c hc ∈ centralizer ({sbar y hyP} : Set (TwoThin.barQ ↥(centralizer ({u} : Set G)))) :=
      mem_centralizer_singleton_iff.2 (sbar_commute hc hyP hcy)
    have hcN : c ∈ normalizer (M : Set G) := mem_normalizer_K_of_KN hMN hc
    have hgS : sbar c hc ∈ normalizer ((bar u M : Subgroup _) : Set _) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_bar_of_normalizes hc hcN)
    have hgF : sbar c hc ∈ normalizer ((F : Subgroup _) : Set _) := by
      rw [hF]
      exact Th2.mem_normalizer_inf' hgS (Subgroup.le_normalizer hgy)
    have hgZ := TwoThin.mem_normalizer_pPrimeCoreOf hgF
    exact (Subgroup.mem_normalizer_iff.1 hgZ z).1 hz

end Transport

end CFSG.GH74.GLS.Th2.PumpUnbal

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.PumpUnbal
  CFSG.GH74.GLS.C3.Layer1
open CFSG.GH74.GLS.C3.Layer1.PumpCalc

theorem b_thm2_pump_unbal_of
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2)
    (hfm : ∀ (L : Type) [Group L] [Finite L], TwoThin.Gen4Comp L → InC2 L → InU2 L →
      ¬ IsL34Quotient L → HasL2Model L IsFM9) :
    B_thm2_pump_unbal := by
  intro G _ _ hG x y K T S h hrk2 hC2 u hu huc hu2 M hltM hMN
  have hv : IsV2Triple x y K := h.v2ss.isV2Triple
  have hlu : IsLocallyUnbalancing x y K := hv.1
  obtain ⟨hcenK, -⟩ := h.centerless_and_shape hG hL34 h102
  obtain ⟨hxM, ⟨e⟩, -⟩ := h.pumpup_data hu huc hltM
  have hU2 : InU2 (kBar K) := h102 G hG x y K hlu
  have hno : ¬ IsL34Quotient (kBar K) := fun hl34 =>
    hL34 G hG.gen4 x K hlu.1.1 hlu.1.2 ⟨hl34, (inU2_center hU2).1, (inU2_center hU2).2⟩
  have hKc : IsPCompIn 2 (centralizer ({x} : Set G)) K := hlu.1.2
  obtain ⟨eb⟩ := PumpCalc.kBar_equiv_bar hKc
  have hP : TwoThin.Gen4Comp ↥(bar x K) :=
    TwoThin.gen4Comp_of_gen4Cen (TwoThin.gen4Cen_barQ hG.gen4 hlu.1.1) _
  have hL2b : HasL2Model ↥(bar x K) IsFM9 :=
    hfm _ hP (CFSG.GH74.E2.inC2_of_mulEquiv eb hC2) (inU2_of_mulEquiv eb hU2)
      (fun hl => hno (TwoThin.isL34Quotient_of_mulEquiv eb.symm hl))
  have hL2 : HasL2Model (kBar K) IsFM9 := TwoThin.hasL2Model_of_mulEquiv eb.symm hL2b
  obtain ⟨p, f, hp, hf, hq, hLie⟩ := hL2
  have hL2' : HasL2Model (kBar K) (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hLie⟩
  obtain ⟨W', hW'ne, hW'fix, hW'odd, hW'n⟩ := exists_oddNormal_fixed hlu hq hL2'
  have hyT : y ∈ T := h.y_mem
  have hyP : y ∈ centralizer ({u} : Set G) := mem_centralizer_singleton_iff.2 (huc y hyT).symm
  have hyK : y ∈ normalizer (K : Set G) := hlu.2.2.2.1
  obtain ⟨Z, hZS, hZodd, hZne, hZfix, hZn⟩ :=
    exists_oddNormal_bar hltM e hxM hMN hyP hyK W' hW'ne hW'fix hW'odd hW'n
  exact ⟨y, locUnbal_of_oddNormal hu2 hlu.2.1 hyP hltM.2.1.2.2 hMN
    (centerlessBar_of_equiv hcenK e) Z hZS hZodd hZne hZfix hZn⟩

end CFSG.GH74.GLS
