module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Bal3Lemma2_1Sylow
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalPairGeometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G]

@[expose] def pPowerSubgroup (p : ℕ) (S : Subgroup G) : Subgroup G :=
  closure {x | ∃ s ∈ S, x = s ^ p}

theorem pow_mem_pPowerSubgroup {p : ℕ} {S : Subgroup G} {s : G} (hs : s ∈ S) :
    s ^ p ∈ pPowerSubgroup p S :=
  subset_closure ⟨s, hs, rfl⟩

theorem conj_mem_pPowerSubgroup {p : ℕ} {S : Subgroup G} {x h : G}
    (hx : x ∈ normalizer (S : Set G)) (hh : h ∈ pPowerSubgroup p S) :
    x * h * x⁻¹ ∈ pPowerSubgroup p S := by
  induction hh using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, hs, rfl⟩ := hy
    rw [← conj_pow]
    exact pow_mem_pPowerSubgroup ((mem_normalizer_iff.mp hx s).mp hs)
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
    exact mul_mem ha hb
  | inv a _ ha =>
    rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
    exact inv_mem ha

theorem normalizer_le_normalizer_pPowerSubgroup {p : ℕ} (S : Subgroup G) :
    normalizer (S : Set G) ≤ normalizer (pPowerSubgroup p S : Set G) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_pPowerSubgroup hx hh, fun hh => ?_⟩
  have := conj_mem_pPowerSubgroup (inv_mem hx) hh
  rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at this

theorem exists_ne_one_mem_inf_pPowerSubgroup {p : ℕ} [Fact p.Prime] {S D : Subgroup G}
    (hS : IsPGroup p S) (hD : ∀ y ∈ S, y ^ p = 1 → y ∈ D) {s : G} (hs : s ∈ S) (hsD : s ∉ D) :
    ∃ y ∈ D, y ≠ 1 ∧ y ∈ pPowerSubgroup p S := by
  classical
  obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
  have hex : ∃ k : ℕ, s ^ (p ^ k) ∈ D := by
    refine ⟨m, ?_⟩
    have : s ^ (p ^ m) = 1 := by simpa using congrArg Subtype.val hm
    rw [this]
    exact one_mem D
  have hk0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact hsD (by simpa using this)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmin : s ^ (p ^ k) ∉ D := Nat.find_min hex (by omega)
  have hsk : s ^ (p ^ k) ∈ S := pow_mem hs _
  have hskp : (s ^ (p ^ k)) ^ p ∈ D := by
    have := Nat.find_spec hex
    rwa [hk, pow_succ, pow_mul] at this
  exact ⟨(s ^ (p ^ k)) ^ p, hskp, fun h1 => hmin (hD _ hsk h1), pow_mem_pPowerSubgroup hsk⟩

theorem le_of_normalizer_le_of_exists_conj {D W : Subgroup G} {z : G} (hWD : W ≤ D)
    (hW1 : ∃ y ∈ W, y ≠ 1) (hN : normalizer (D : Set G) ≤ normalizer (W : Set G))
    (htr : ∀ d ∈ D, d ≠ 1 → ∃ g ∈ normalizer (D : Set G),
      zpowers d = (zpowers z).map (MulAut.conj g).toMonoidHom) : D ≤ W := by
  have hconj : ∀ g ∈ normalizer (D : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := fun g hg w hw =>
    (mem_normalizer_iff.mp (hN hg) w).mp hw
  have hzW : z ∈ W := by
    obtain ⟨y, hyW, hy1⟩ := hW1
    obtain ⟨g, hgN, hg⟩ := htr y (hWD hyW) hy1
    have hgz : g * z * g⁻¹ ∈ zpowers y := by
      rw [hg]
      exact ⟨z, mem_zpowers z, rfl⟩
    obtain ⟨a, ha⟩ := mem_zpowers_iff.mp hgz
    have hzy : z = g⁻¹ * y ^ a * g := by
      rw [ha]
      group
    have hc : (g⁻¹ * y * g) ^ a = g⁻¹ * y ^ a * g := by
      have := conj_zpow (a := g⁻¹) (b := y) (i := a)
      simpa using this
    rw [hzy, ← hc]
    refine zpow_mem ?_ a
    have := hconj g⁻¹ (inv_mem hgN) y hyW
    simpa using this
  intro d hd
  by_cases hd1 : d = 1
  · rw [hd1]
    exact one_mem W
  obtain ⟨g, hgN, hg⟩ := htr d hd hd1
  have hdz : d ∈ (zpowers z).map (MulAut.conj g).toMonoidHom := hg ▸ mem_zpowers d
  obtain ⟨c, hc, hcd⟩ := hdz
  have hcW : c ∈ W := (zpowers_le.mpr hzW) hc
  rw [← hcd]
  exact hconj g hgN c hcW

variable [Finite G]

theorem normalizer_le_normalizer_inf_pPowerSubgroup {p : ℕ} [Fact p.Prime] {S D : Subgroup G}
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer (D : Set G))) (hDS : D ≤ S)
    (hDe : ∀ y ∈ D, y ^ p = 1) (hS : ∀ y ∈ S, y ^ p = 1 → y ∈ D) :
    normalizer (D : Set G) ≤ normalizer ((D ⊓ pPowerSubgroup p S : Subgroup G) : Set G) := by
  have hfrat := le_sup_normalizer_of_isSylowOf
    (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D) hsyl
  refine hfrat.trans (sup_le ?_ ?_)
  · exact (centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)).trans
      (centralizer_le_normalizer _)
  · intro x hx
    have key : ∀ x ∈ normalizer (S : Set G), ∀ y ∈ D, x * y * x⁻¹ ∈ D := fun x hx y hy =>
      hS _ ((mem_normalizer_iff.mp hx y).mp (hDS hy))
        (by rw [conj_pow, hDe y hy, mul_one, mul_inv_cancel])
    have hxD : x ∈ normalizer (D : Set G) := by
      rw [mem_normalizer_iff]
      intro h
      refine ⟨key x hx h, fun hh => ?_⟩
      have := key x⁻¹ (inv_mem hx) _ hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h by group] at this
    exact inf_normalizer_le_normalizer_inf ⟨hxD, normalizer_le_normalizer_pPowerSubgroup S hx⟩

theorem exists_conj_normalizer_inf {p : ℕ} (hprime : p.Prime) (P : Sylow p G) {D : Subgroup G}
    (hDP : D ≤ (P : Subgroup G)) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G)) :
    ∃ g : G, g ∈ (P : Subgroup G) ∧ g ∉ normalizer (D : Set G) ∧
      D.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) ⊓ normalizer (D : Set G) ∧
      (P : Subgroup G) ⊓ normalizer (D : Set G) ≤
        normalizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  set T : Subgroup G := (P : Subgroup G) ⊓ normalizer (D : Set G) with hT
  have hTP : T < (P : Subgroup G) :=
    lt_of_le_of_ne inf_le_left fun heq => hPD (by rw [← heq]; exact inf_le_right)
  obtain ⟨g, hgN, hgT⟩ := IsConcreteLE.exists_of_lt
    (pGroup_proper_subgroup_lt_internal_normalizer p hprime P T P.isPGroup' hTP)
  have hgP : g ∈ (P : Subgroup G) := hgN.1
  have hgnT : ∀ x, x ∈ T ↔ g * x * g⁻¹ ∈ T := fun x => mem_normalizer_iff.mp hgN.2 x
  have hmem : ∀ w, w ∈ D.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * w * g ∈ D := by
    intro w
    constructor
    · rintro ⟨d, hd, rfl⟩
      show g⁻¹ * (g * d * g⁻¹) * g ∈ D
      rwa [show g⁻¹ * (g * d * g⁻¹) * g = d by group]
    · intro h
      exact ⟨g⁻¹ * w * g, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  refine ⟨g, hgP, fun h => hgT ⟨hgP, h⟩, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact (hgnT d).mp ⟨hDP hd, le_normalizer hd⟩
  · intro t ht
    rw [mem_normalizer_iff]
    intro w
    have ht' : g⁻¹ * t * g ∈ T := by
      rw [hgnT]
      rwa [show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
    rw [hmem, hmem]
    have := mem_normalizer_iff.mp ht'.2 (g⁻¹ * w * g)
    rw [show g⁻¹ * (t * w * t⁻¹) * g = (g⁻¹ * t * g) * (g⁻¹ * w * g) * (g⁻¹ * t * g)⁻¹ by group]
    exact this

theorem ExtremalObstruction.inf_centralizer_le_self (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : ¬ (P : Subgroup G) ≤ normalizer (D : Set G))
    (hDab : IsMulCommutative D) {z : G} (hzD : z ∈ D) (hz1 : z ≠ 1)
    (hzc : z ∈ centralizer ((P : Subgroup G) : Set G))
    (hN₀M : normalizer ((zpowers z : Subgroup G) : Set G) ≤ M) :
    (P : Subgroup G) ⊓ centralizer (D : Set G) ≤ D := by
  classical
  have hprime := sigmaA_prime p hp
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hDe, hDc⟩ := hext.isElemAbelian_of_isMulCommutative hprime hDab
  have hDP : D ≤ (P : Subgroup G) := hext.obstruction.2.1
  have hCM : centralizer (D : Set G) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzD)).trans
      ((centralizer_singleton_le_normalizer_zpowers z).trans hN₀M)
  have hCp : ∀ y ∈ centralizer (D : Set G), y ^ p = 1 → y ∈ D := fun y hyC hyp =>
    hext.mem_of_mem_centralizer_of_isMulCommutative hS hD1 hp hDab hCM hyC hyp
  have hDC : D ≤ centralizer (D : Set G) := le_centralizer_iff_isMulCommutative.mpr hDab
  have hCN : centralizer (D : Set G) ≤ normalizer (D : Set G) := centralizer_le_normalizer _
  set S : Subgroup G := (P : Subgroup G) ⊓ centralizer (D : Set G) with hSdef
  set T : Subgroup G := (P : Subgroup G) ⊓ normalizer (D : Set G) with hTdef
  have hDS : D ≤ S := le_inf hDP hDC
  have hST : S ≤ T := inf_le_inf_left _ hCN
  have hSp : IsPGroup p S := P.isPGroup'.to_inf_left
  have hSD : ∀ y ∈ S, y ^ p = 1 → y ∈ D := fun y hy hyp => hCp y hy.2 hyp
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p S (centralizer (D : Set G)) := by
    have hN := hext.isSylowOf_normalizer_inf hS hD1 hp hPD hDab hCM hzD hz1 hzc hN₀M
    have hC := hN.inf_of_le_normalizer hCN
      (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D)
    rwa [inf_assoc, inf_eq_right.mpr hCN] at hC
  by_contra hSnD
  obtain ⟨s, hsS, hsD⟩ := IsConcreteLE.not_le_iff_exists.mp hSnD
  obtain ⟨y, hyD, hy1, hyW⟩ := exists_ne_one_mem_inf_pPowerSubgroup hSp hSD hsS hsD
  have hDW : D ≤ pPowerSubgroup p S := by
    have hN := normalizer_le_normalizer_inf_pPowerSubgroup hsyl hDS hDe.2 hSD
    exact (le_of_normalizer_le_of_exists_conj inf_le_left ⟨y, ⟨hyD, hyW⟩, hy1⟩ hN
      fun d hd hd1 =>
        hext.exists_mem_normalizer_zpowers_eq hS hD1 hp hPD hDab hCM hzD hz1 hzc hN₀M hd hd1).trans
      inf_le_right
  obtain ⟨g, hgP, hgD, hD'T, hTD'⟩ := exists_conj_normalizer_inf hprime P hDP hPD
  set D' : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hD'def
  have hmem : ∀ w, w ∈ D' ↔ g⁻¹ * w * g ∈ D := by
    intro w
    constructor
    · rintro ⟨d, hd, rfl⟩
      show g⁻¹ * (g * d * g⁻¹) * g ∈ D
      rwa [show g⁻¹ * (g * d * g⁻¹) * g = d by group]
    · intro h
      exact ⟨g⁻¹ * w * g, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hD'ne : D' ≠ D := fun h => hgD (mem_normalizer_iff_map_conj_eq.mpr h)
  have hD'card : Nat.card D' = Nat.card D := card_map_of_injective (MulAut.conj g).injective
  have hD'e : ∀ w ∈ D', w ^ p = 1 := by
    rintro _ ⟨d, hd, rfl⟩
    change (g * d * g⁻¹) ^ p = 1
    rw [conj_pow, hDe.2 d hd, mul_one, mul_inv_cancel]
  obtain ⟨u, huD', huC⟩ : ∃ u ∈ D', u ∉ centralizer (D : Set G) := by
    by_contra hall
    push Not at hall
    exact hD'ne (Subgroup.eq_of_le_of_card_ge
      (fun w hw => hCp w (hall w hw) (hD'e w hw)) hD'card.ge)
  have huT : u ∈ T := hD'T huD'
  have huN : u ∈ normalizer (D : Set G) := huT.2
  have hupow : ∀ s ∈ S, u * s ^ p = s ^ p * u := by
    intro s hs
    have hsC : s ∈ centralizer (D : Set G) := hs.2
    have hsT : s ∈ T := hST hs
    have haS : u⁻¹ * s * u ∈ S := by
      have hsP : s ∈ (P : Subgroup G) := hs.1
      have huP : u ∈ (P : Subgroup G) := huT.1
      have haP : u⁻¹ * s * u ∈ (P : Subgroup G) := mul_mem (mul_mem (inv_mem huP) hsP) huP
      refine ⟨haP, ?_⟩
      · show u⁻¹ * s * u ∈ centralizer (D : Set G)
        rw [mem_centralizer_iff]
        intro h hh
        have hh' : u * h * u⁻¹ ∈ D := (mem_normalizer_iff.mp huN h).mp hh
        have := mem_centralizer_iff.mp hsC _ hh'
        calc h * (u⁻¹ * s * u) = u⁻¹ * ((u * h * u⁻¹) * s) * u := by group
          _ = u⁻¹ * (s * (u * h * u⁻¹)) * u := by rw [this]
          _ = (u⁻¹ * s * u) * h := by group
    have hcS : s⁻¹ * (u⁻¹ * s * u) ∈ S := mul_mem (inv_mem hs) haS
    have hcD' : s⁻¹ * (u⁻¹ * s * u) ∈ D' := by
      have h1 : s⁻¹ * u * s⁻¹⁻¹ ∈ D' := (mem_normalizer_iff.mp (hTD' (inv_mem hsT)) u).mp huD'
      have h2 := inv_mem h1
      have h3 := mul_mem h2 huD'
      rwa [show (s⁻¹ * u * s⁻¹⁻¹)⁻¹ * u = s⁻¹ * (u⁻¹ * s * u) by group] at h3
    have hcD : s⁻¹ * (u⁻¹ * s * u) ∈ D := hCp _ hcS.2 (hD'e _ hcD')
    have hcomm : s * (s⁻¹ * (u⁻¹ * s * u)) = (s⁻¹ * (u⁻¹ * s * u)) * s :=
      (mem_centralizer_iff.mp hsC _ hcD).symm
    have hcp : (s⁻¹ * (u⁻¹ * s * u)) ^ p = 1 := hD'e _ hcD'
    have hpow : (u⁻¹ * s * u) ^ p = s ^ p := by
      have e : u⁻¹ * s * u = s * (s⁻¹ * (u⁻¹ * s * u)) := by group
      rw [e, Commute.mul_pow hcomm, hcp, mul_one]
    have hconjp : (u⁻¹ * s * u) ^ p = u⁻¹ * s ^ p * u := by
      have := conj_pow (a := u⁻¹) (b := s) (i := p)
      simpa using this
    have hfix : u⁻¹ * s ^ p * u = s ^ p := hconjp.symm.trans hpow
    have h1 : u * (u⁻¹ * s ^ p * u) = s ^ p * u := by group
    rw [hfix] at h1
    exact h1
  have hcentr : pPowerSubgroup p S ≤ centralizer ({u} : Set G) := by
    refine (closure_le _).mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hupow s hs
  apply huC
  rw [mem_centralizer_iff]
  intro d hd
  exact (mem_centralizer_iff.mp (hcentr (hDW hd)) u (Set.mem_singleton u)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
