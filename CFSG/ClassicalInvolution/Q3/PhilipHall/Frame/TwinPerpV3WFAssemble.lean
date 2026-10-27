module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFF4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFPerm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf46WO2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22EW92

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section Assemble




variable {n : ℕ}

theorem exists_odd_pow_mem {Y : Type*} [Group Y] [Finite Y] {N P : Subgroup Y}
    (hn : (P.subgroupOf N).Normal) (hodd : Odd (P.subgroupOf N).index) :
    ∀ g ∈ N, ∃ m : ℕ, Odd m ∧ g ^ m ∈ P := by
  intro g hg
  haveI := hn
  let g' : ↥N := ⟨g, hg⟩
  refine ⟨orderOf (QuotientGroup.mk g' : ↥N ⧸ P.subgroupOf N), ?_, ?_⟩
  · exact Odd.of_dvd_nat hodd (by
      have := orderOf_dvd_natCard (QuotientGroup.mk g' : ↥N ⧸ P.subgroupOf N)
      rwa [← Subgroup.index] at this)
  · have h1 : (QuotientGroup.mk g' : ↥N ⧸ P.subgroupOf N) ^
        orderOf (QuotientGroup.mk g' : ↥N ⧸ P.subgroupOf N) = 1 := pow_orderOf_eq_one _
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1

private theorem prod4_sq {Z : Type*} [Group Z] {p q r u : Z} (hpq : Commute p q) (hpr : Commute p r)
    (hpu : Commute p u) (hqr : Commute q r) (hqu : Commute q u) (hru : Commute r u) :
    (p * q * r * u) * (p * q * r * u) = (p * p) * (q * q) * (r * r) * (u * u) := by
  have h1 : Commute (p * q * r) u := (hpu.mul_left hqu).mul_left hru
  have h2 : Commute (p * q) r := hpr.mul_left hqr
  have := h1.mul_pow 2
  rw [h2.mul_pow, hpq.mul_pow] at this
  simpa [sq] using this

section WFInAssemble

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem WFIn.conj_mem_twinSet (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {c : Y} (hc : c * t = t * c)
    {J : Subgroup Y} (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) :
    conjSub c J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K := by
  refine ⟨h.hyp.conjInvariant c J hJ.1, t, h.hStd.datum.hz, ?_⟩
  have := (h.uniqInv hJ).conj c
  have e : c * t * c⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hc
  rwa [e] at this

theorem WFIn.exists_conj (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J J' : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) :
    ∃ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c J = J' := by
  have hd := h.hStd.datum
  have htr : ∀ J ∈ CoreAssembly.conjClass (tightCore R), ∃ g : Y, conjSub g K = J := by
    obtain ⟨a, ha⟩ := hd.mem
    rintro _ ⟨b, rfl⟩
    refine ⟨b * a⁻¹, ?_⟩
    rw [← ha, conjSub_mul, conjSub_inv_conjSub]
  have e := twinSet_eq htr hd.hz
  rw [e] at hJ hJ'
  obtain ⟨-, g, hg, rfl⟩ := hJ
  obtain ⟨-, g', hg', rfl⟩ := hJ'
  refine ⟨g' * g⁻¹, Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hg), ?_⟩
  rw [conjSub_mul, conjSub_inv_conjSub]

theorem WFIn.P_normalizes (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {J : Subgroup Y}
    (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) :
    ∀ p ∈ (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y),
      conjSub p J = J := by
  intro p hp
  have hle : (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y) ≤
      Subgroup.normalizer (J : Set Y) := by
    refine iSup₂_le fun M hM => ?_
    by_cases hMJ : M = J
    · subst hMJ
      exact Subgroup.le_normalizer
    · intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have e : m * g * m⁻¹ = g := by rw [h.comm hM hJ hMJ m hm g hg]; group
        rw [e]; exact hg
      · intro hg
        have h1 := h.comm hM hJ hMJ m hm _ hg
        have h3 : m * (m * g * m⁻¹) = m * g := by
          calc m * (m * g * m⁻¹) = (m * g * m⁻¹) * m := h1
            _ = m * g := by group
        have h2 : m * g * m⁻¹ = g := mul_left_cancel h3
        rw [h2] at hg
        exact hg
  exact conjSub_eq_of_mem_normalizer (hle hp)


theorem WFIn.N_normalizes (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {N : Subgroup Y}
    (hN : WFOddNormal (Subgroup.centralizer ({t} : Set Y))
      (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M) N) :
    ∀ g ∈ N, ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub g J = J := by
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  obtain ⟨hNC, hNn, hPN, hodd⟩ := hN
  have hPn := v3_P_normalTwo h.hStd h.exit.2.2.2.1
  have hnorm : ((⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y).subgroupOf N).Normal := by
    refine ⟨fun a' ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hPn.2.2 (g : Y) (by
      have := hNC g.2
      exact this) (a' : Y) ha
  have hmain := normalizes_of_odd_normal M hfr.inj (Subgroup.centralizer ({t} : Set Y))
    (fun c hc i => by
      have hc' : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      obtain ⟨j, hj⟩ := hfr.surj _ (h.conj_mem_twinSet hc' (hfr.mem i))
      exact ⟨j, hj.symm⟩)
    (fun i j => h.exists_conj (hfr.mem i) (hfr.mem j)) N _ hNC hNn hPN
    (fun p hp i => h.P_normalizes (hfr.mem i) p hp) (exists_odd_pow_mem hnorm hodd)
  intro g hg J hJ
  obtain ⟨i, rfl⟩ := hfr.surj J hJ
  exact hmain g hg i

private theorem fin4_exists_two : ∀ i j : Fin 4, i ≠ j → ∃ k l : Fin 4, k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j ∧ k ≠ l := by
  decide

private theorem fin4_cover : ∀ i j k l r : Fin 4, i ≠ j → k ≠ i → k ≠ j → l ≠ i → l ≠ j → k ≠ l →
    r = i ∨ r = j ∨ r = k ∨ r = l := by
  decide

theorem WFIn.cent_all_of_two (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    {J J' : Subgroup Y} (hJ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K)
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) (hne : J ≠ J')
    (hc : ∀ m ∈ J, x * m = m * x) (hc' : ∀ m ∈ J', x * m = m * x) :
    ∀ J'' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, ∀ m ∈ J'', x * m = m * x := by
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  obtain ⟨i, rfl⟩ := hfr.surj J hJ
  obtain ⟨j, rfl⟩ := hfr.surj J' hJ'
  have hij : i ≠ j := fun e => hne (by rw [e])
  obtain ⟨k, l, hki, hkj, hli, hlj, hkl⟩ := fin4_exists_two i j hij
  have hMne : ∀ p q : Fin 4, p ≠ q → M p ≠ M q := fun p q hpq e => hpq (hfr.inj e)
  have hcom : ∀ p q : Fin 4, p ≠ q → Commutes (M p) (M q) :=
    fun p q hpq => h.comm (hfr.mem p) (hfr.mem q) (hMne p q hpq)
  have hsq : ∀ p, a p * a p = t := fun p =>
    T7A.sq_eq_of_orderOf_four (h.uniqInv (hfr.mem p)) (hfr.haM p) (hfr.ha4 p)
  have hq8 : ∀ p, Q8Facts (M p) t := fun p => h.q8 (hfr.mem p)
  have hxa : ∀ p, x * a p * x⁻¹ ∈ M p := fun p => by
    have := conj_mem_conjSub (n := x) (hfr.haM p)
    rwa [hxM _ (hfr.mem p)] at this
  have hxM' : ∀ p, ∀ m ∈ M p, x * m * x⁻¹ ∈ M p := fun p m hm => by
    have := conj_mem_conjSub (n := x) hm
    rwa [hxM _ (hfr.mem p)] at this
  obtain ⟨s, hs⟩ : ∃ s, s = a i * a j * a k * a l := ⟨_, rfl⟩
  have hinj4 : Function.Injective ![i, j, k, l] := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all
  have hsF : s ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W := by
    refine ⟨fun r => M (![i, j, k, l] r), fun r => a (![i, j, k, l] r), hfr.inj.comp hinj4,
      fun r => hfr.mem _, fun r => ⟨Subgroup.mem_inf.mpr ⟨hfr.haM _, hfr.haW _⟩, hfr.ha4 _⟩, ?_⟩
    simpa using hs
  have hxC : x ∈ Subgroup.centralizer ({a i * a j} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hc (a i) (hfr.haM i)
    have h2 := hc' (a j) (hfr.haM j)
    calc x * (a i * a j) = (x * a i) * a j := (mul_assoc _ _ _).symm
      _ = (a i * x) * a j := by rw [h1]
      _ = a i * (x * a j) := mul_assoc _ _ _
      _ = a i * (a j * x) := by rw [h2]
      _ = a i * a j * x := (mul_assoc _ _ _).symm
  have hnormK := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W h.hW h.t_mem (M i) (hfr.mem i) (M j) (hfr.mem j)
    (hMne i j hij) (a i) (Subgroup.mem_inf.mpr ⟨hfr.haM i, hfr.haW i⟩) (a j)
    (Subgroup.mem_inf.mpr ⟨hfr.haM j, hfr.haW j⟩) (hfr.ha4 i) (hfr.ha4 j) s hsF hxC
  have hxs0 : x * s * x⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) :=
    (Subgroup.mem_normalizer_iff.mp hnormK s).mp (Subgroup.subset_closure (by simp))
  have ht := (hq8 i).z_sq
  have ht1 := (hq8 i).z_ne
  have hcomW : ∀ p q : Fin 4, a p * a q = a q * a p := fun p q => h.abelian _ (hfr.haW p) _ (hfr.haW q)
  have hcW : ∀ p q : Fin 4, Commute (a p) (a q) := hcomW
  have hs2 : s * s = 1 := by
    rw [hs, prod4_sq (hcW i j) (hcW i k) (hcW i l) (hcW j k) (hcW j l) (hcW k l), hsq, hsq, hsq, hsq,
      ht, one_mul, ht]
  have hts : t * s = s * t := by
    have hti : ∀ p, Commute t (a p) := fun p => (hq8 p).z_central (a p) (hfr.haM p)
    rw [hs]
    exact (((hti i).mul_right (hti j)).mul_right (hti k)).mul_right (hti l)
  have hsne := frame_prod_ne (hq8 i) (hfr.haM i) (hfr.haM j) (hfr.haM k) (hfr.haM l) (hsq i)
    (hcom i j hij) (hcom i k (Ne.symm hki)) (hcom i l (Ne.symm hli))
  rw [← hs] at hsne
  have hxs : x * s * x⁻¹ = s := by
    refine fix_of_odd_klein hxo hxt ht ht1 ?_
    have hxt' : x * t * x⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr hxt
    rcases klein_closure ht hs2 hts _ hxs0 with e | e | e | e
    · exfalso
      apply hsne.1
      have : s = x⁻¹ * (x * s * x⁻¹) * x := by group
      rw [this, e]; group
    · exfalso
      apply hsne.2
      have : s = x⁻¹ * (x * s * x⁻¹) * x := by group
      rw [this, e]
      calc x⁻¹ * t * x = x⁻¹ * (t * x) := mul_assoc _ _ _
        _ = x⁻¹ * (x * t) := by rw [hxt]
        _ = t := by group
    · exact Or.inl e
    · exact Or.inr e
  have hx1 : x * a i = a i * x := hc _ (hfr.haM i)
  have hx2 : x * a j = a j * x := hc' _ (hfr.haM j)
  obtain ⟨hk3, hl4⟩ := f4_core (J₁ := M i) (J₂ := M j) (J₃ := M k) (J₄ := M l) (hq8 k) (hq8 l)
    (hfr.haM i) (hfr.haM j) (hfr.haM k) (hfr.haM l) (hsq k) (hsq l)
    (hcom i k (Ne.symm hki)) (hcom i l (Ne.symm hli)) (hcom j k (Ne.symm hkj)) (hcom j l (Ne.symm hlj))
    (hcom k l hkl) hxo hxt (hxM' k) (hxM' l) hx1 hx2 (by rw [← hs]; exact hxs)
  intro J'' hJ'' m hm
  obtain ⟨r, rfl⟩ := hfr.surj J'' hJ''
  rcases fin4_cover i j k l r hij hki hkj hli hlj hkl with rfl | rfl | rfl | rfl
  · exact hc m hm
  · exact hc' m hm
  · exact hk3 m hm
  · exact hl4 m hm

end WFInAssemble


theorem v3WFinalWg_of_subleaves (hW0 : WFW0 n) (hB0 : WFB0 n) (hC : WFStepC n) (hD : WFStepD n) :
    V3WFinalWg n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ hin W hW hKD hK'D hK₃D hu₁ hu₂ hUniq hO U hU hUC x hxo hxL hxP
  have hWF : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W := ⟨hin, hW, hKD, hK'D, hK₃D, hu₁, hu₂, hUniq, hO⟩
  have hd := hin.1.datum
  have hW1 : ∃ V : Subgroup (LSec (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)),
      WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) = {V} :=
    hUniq W hW K (mem_twinSet_self hd.mem hd.hz) K' hd.hK' (Ne.symm hd.hne) u₁
      ⟨hd.hu₁.1, hu₁⟩ u₂ ⟨hd.hu₂.1, hu₂⟩ hd.hu₁.2 hd.hu₂.2
  obtain ⟨N, hN, hxN⟩ := hW0 Y R S t K K' K₃ u₁ u₂ u₃ K₄ hin hW1 hO U hU hUC x hxo hxL hxP
  have hxC : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hN.1 hxN)
  have hxM := hWF.N_normalizes hN x hxN
  by_cases hcent : ∃ J₀ ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, ∀ m ∈ J₀, x * m = m * x
  · obtain ⟨J₀, hJ₀, hc₀⟩ := hcent
    refine hC Y R S t K K' K₃ u₁ u₂ u₃ K₄ W hWF x hxo hxC hxM ⟨N, hN, hxN⟩
      ⟨J₀, hJ₀, hc₀, fun J hJ hne hcJ => ?_⟩
    apply hxP
    have hall := hWF.cent_all_of_two hB0 hxo hxC hxM hJ₀ hJ (Ne.symm hne) hc₀ hcJ
    have hle : (⨆ M ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, M : Subgroup Y) ≤
        Subgroup.centralizer ({x} : Set Y) := by
      refine iSup₂_le fun J' hJ' m hm => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hall J' hJ' m hm).symm
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  · exact hD Y R S t K K' K₃ u₁ u₂ u₃ K₄ W hWF x hxo hxC hxM fun J hJ hcJ => hcent ⟨J, hJ, hcJ⟩

end Assemble

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
