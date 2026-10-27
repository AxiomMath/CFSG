module

import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConstrainedSolv3Action
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

section Local

variable {Y : Type} [Group Y] [Finite Y]

theorem kl5_eq_sup_zpowers {p : ℕ} (hp : p.Prime) {B T : Subgroup Y} {s : Y} (hBT : B ≤ T)
    (hsT : s ∈ T) (hsB : s ∉ B) (hB : Nat.card B = p ^ 3) (hT : Nat.card T = p ^ 4) :
    T = B ⊔ Subgroup.zpowers s := by
  have hST : B ⊔ Subgroup.zpowers s ≤ T := sup_le hBT (Subgroup.zpowers_le.mpr hsT)
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le (le_sup_left : B ≤ B ⊔ Subgroup.zpowers s)
  have hdvd := Subgroup.card_dvd_of_le hST
  rw [hm, hB, hT, show p ^ 4 = p ^ 3 * p by ring] at hdvd
  have hm' : m ∣ p := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos 3) hdvd
  rcases (Nat.dvd_prime hp).mp hm' with h1 | h1
  · refine absurd ?_ hsB
    rw [h1, mul_one] at hm
    rw [Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ Subgroup.zpowers s)
      (by rw [hm, hB])]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  · rw [h1] at hm
    exact (Subgroup.eq_of_le_of_card_ge hST (by rw [hm, hB, hT]; ring_nf; rfl)).symm

theorem exists_sigma_z_five {p : ℕ} [Fact p.Prime] {T : Sylow p Y} {B Y₀ : Subgroup Y}
    (hBT : B ≤ (T : Subgroup Y)) (hBel : IsElemAbelian p B) (hBc : Nat.card B = p ^ 3)
    (hweak : GLBWeakCore p (T : Subgroup Y) ≤ Y₀) (hT : Nat.card (T : Subgroup Y) = p ^ 4)
    (hZ : Nat.card (centerOf (T : Subgroup Y)) = p) (hKD : HasKlingenData p T Y₀) :
    ∃ σ z : Y, σ ∈ (T : Subgroup Y) ∧ σ ∉ B ∧ σ ^ p = 1 ∧ z ∈ B ∧ z ≠ 1 ∧
      z ∈ Subgroup.centralizer ((T : Subgroup Y) : Set Y) ∧
      ∀ y ∈ (T : Subgroup Y), y ∈ Subgroup.centralizer ((T : Subgroup Y) : Set Y) →
        y ∈ Subgroup.zpowers z := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, D, L, hET, -, -, -, hDE, hDel, hDc, -, hND, -⟩ := hKD
  have hDB : ¬ D ≤ B := by
    intro hDB
    refine hND ((normalizer_le_weakCore_of_commutative_overgroup p hp hBT hDB hBel.1 ?_ ?_).trans
      hweak)
    · exact le_csSup (pRank_bddAbove p hp D) ⟨D, le_rfl, hDel, hDc⟩
    · exact le_csSup (pRank_bddAbove p hp B) ⟨B, le_rfl, hBel, hBc⟩
  obtain ⟨σ, hσD, hσB⟩ := IsConcreteLE.not_le_iff_exists.mp hDB
  have hσT : σ ∈ (T : Subgroup Y) := hET (hDE hσD)
  have hDT : D ≤ (T : Subgroup Y) := hDE.trans hET
  have hTeq : (T : Subgroup Y) = B ⊔ Subgroup.zpowers σ :=
    kl5_eq_sup_zpowers hp hBT hσT hσB hBc hT
  have hDBne : D ⊓ B ≠ ⊥ := by
    intro h0
    have h1 : B.relIndex (T : Subgroup Y) * p ^ 3 = p ^ 4 := by
      have := Subgroup.relIndex_mul_card (H := B) (K := (T : Subgroup Y))
      rwa [inf_eq_left.mpr hBT, hBc, hT] at this
    have h2 : D.relIndex (T : Subgroup Y) * p ^ 2 = p ^ 4 := by
      have := Subgroup.relIndex_mul_card (H := D) (K := (T : Subgroup Y))
      rwa [inf_eq_left.mpr hDT, hDc, hT] at this
    have h3 := Subgroup.relIndex_inf_le (H := D) (K := B) (L := (T : Subgroup Y))
    rw [h0, Subgroup.relIndex_bot_left, hT] at h3
    have hBp : B.relIndex (T : Subgroup Y) = p := by
      have : B.relIndex (T : Subgroup Y) * p ^ 3 = p * p ^ 3 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this
    have hDp : D.relIndex (T : Subgroup Y) = p ^ 2 := by
      have : D.relIndex (T : Subgroup Y) * p ^ 2 = p ^ 2 * p ^ 2 := by rw [h2]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) this
    rw [hBp, hDp] at h3
    have h4 : p ^ 2 * p < p ^ 4 := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨⟨z, hzD, hzB⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hDBne
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzT : z ∈ (T : Subgroup Y) := hBT hzB
  have hTc : (T : Subgroup Y) ≤ Subgroup.centralizer ({z} : Set Y) := by
    rw [hTeq]
    refine sup_le (fun b hb => ?_) ((Subgroup.zpowers_le).mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hBel.1) ⟨b, hb⟩ ⟨z, hzB⟩)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val ((isMulCommutative_iff.mp hDel.1) ⟨σ, hσD⟩ ⟨z, hzD⟩)
  have hzc : z ∈ Subgroup.centralizer ((T : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTc hq)
  have hzo : orderOf z = p := orderOf_eq_prime (hDel.2 z hzD) hz1'
  have hzp : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzo]
  have hZeq : Subgroup.zpowers z = centerOf (T : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzT, hzc⟩) (by rw [hzp, hZ])
  refine ⟨σ, z, hσT, hσB, hDel.2 σ hσD, hzB, hz1', hzc, fun y hy hyc => ?_⟩
  rw [hZeq]
  exact ⟨hy, hyc⟩

end Local

section Package

variable {G : Type} [Group G] [Finite G]

structure D1KlingenFivePkg (p : ℕ) (R X : Subgroup G) (σ z : G) : Prop where
  card_R : Nat.card R = p ^ 4
  le_R : X ≤ R
  elem : IsElemAbelian p X
  card_X : Nat.card X = p ^ 3
  z_mem : z ∈ X
  z_ne : z ≠ 1
  center_le : ∀ y ∈ R, y ∈ Subgroup.centralizer (R : Set G) → y ∈ Subgroup.zpowers z
  σ_mem : σ ∈ R
  σ_not_mem : σ ∉ X
  σ_pow : σ ^ p = 1
  le_normalizer : R ≤ Subgroup.normalizer (X : Set G)
  heis : ∃ E : Subgroup G, E ≤ R ∧ Nat.card E = p ^ 3 ∧ (∀ x ∈ E, x ^ p = 1) ∧
    ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a

namespace D1KlingenFivePkg

variable {p : ℕ} {R X : Subgroup G} {σ z : G}

theorem eq_sup [Fact p.Prime] (h : D1KlingenFivePkg p R X σ z) : R = X ⊔ Subgroup.zpowers σ :=
  kl5_eq_sup_zpowers Fact.out h.le_R h.σ_mem h.σ_not_mem h.card_X h.card_R

theorem mem_of_normal [Fact p.Prime] (h : D1KlingenFivePkg p R X σ z) (hR : IsPGroup p R)
    {W : Subgroup G} (hWR : W ≤ R) (hWn : R ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    z ∈ W := by
  have hzR : z ∈ R := h.le_R h.z_mem
  have hz : orderOf z = p := orderOf_eq_prime (h.elem.2 z h.z_mem) h.z_ne
  have : (W.subgroupOf R).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hWR).mpr hWn
  have hK : W.subgroupOf R ≠ ⊥ := by
    intro hK
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hw' : (⟨w, hWR hw⟩ : R) ∈ W.subgroupOf R := hw
    rw [hK, Subgroup.mem_bot] at hw'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hw')
  exact Subgroup.mem_subgroupOf.mp (mem_of_normal_ne_bot hR hzR hz
    (fun y hyC hyR _ => h.center_le y hyR hyC) hK)

theorem mem_of_hyperplane [Fact p.Prime] (h : D1KlingenFivePkg p R X σ z) (hR : IsPGroup p R)
    {F : Subgroup G} (hFX : F ≤ X) (hF : F.relIndex X = p)
    (hσF : σ ∈ Subgroup.normalizer (F : Set G)) : z ∈ F := by
  have hp : p.Prime := Fact.out
  have hFne : F ≠ ⊥ := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (H := F) (K := X)
    rw [inf_eq_left.mpr hFX, hF, h.card_X, h0, Subgroup.card_bot] at h1
    have h2 : p ^ 2 = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1]; ring)
    have h3 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hRn : R ≤ Subgroup.normalizer (F : Set G) := by
    rw [h.eq_sup]
    refine sup_le (fun x hx => ?_) ((Subgroup.zpowers_le).mpr hσF)
    have hcomm : ∀ f ∈ X, x * f * x⁻¹ = f := fun f hf => by
      have h2 := congrArg Subtype.val ((isMulCommutative_iff.mp h.elem.1) ⟨x, hx⟩ ⟨f, hf⟩)
      have h3 : x * f = f * x := h2
      rw [h3, mul_inv_cancel_right]
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      rw [hcomm f (hFX hf)]
      exact hf
    · intro hf
      have hfX : f ∈ X := by
        have h1 : x⁻¹ * (x * f * x⁻¹) * x ∈ X :=
          X.mul_mem (X.mul_mem (X.inv_mem hx) (hFX hf)) hx
        simpa [mul_assoc] using h1
      rw [hcomm f hfX] at hf
      exact hf
  exact h.mem_of_normal hR (hFX.trans h.le_R) hRn hFne

end D1KlingenFivePkg

theorem kl5_map_mem_of_mem_sup {p : ℕ} {H R : Subgroup G} (hRH : R ≤ H) {a : H}
    (ha : (a : G) ∈ R ⊔ GLBPrimeCore p H) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) a ∈
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hN : (primeComplementCore (G := H) p).map H.subtype = GLBPrimeCore p H := by
    rw [← glbPrimeCore_subgroupOf p H]
    exact Subgroup.map_subgroupOf_eq_of_le (glbPrimeCore_le p H)
  have hsup : ((R.subgroupOf H) ⊔ primeComplementCore (G := H) p).map H.subtype =
      R ⊔ GLBPrimeCore p H := by
    rw [Subgroup.map_sup, hN, Subgroup.map_subgroupOf_eq_of_le hRH]
  rw [← hsup] at ha
  obtain ⟨b, hb, hba⟩ := ha
  have hba' : b = a := Subtype.ext hba
  subst hba'
  have h1 := Subgroup.mem_map_of_mem (QuotientGroup.mk' (primeComplementCore (G := H) p)) hb
  have h2 : (primeComplementCore (G := H) p).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  rwa [Subgroup.map_sup, h2, sup_bot_eq] at h1

theorem kl5_centralizer_inf_le {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}
    (hS : D1SurvivorData p P M H R X) :
    ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓
      Subgroup.centralizer (((X.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup
          (H ⧸ primeComplementCore (G := H) p)) : Set (H ⧸ primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hXH : X ≤ H := hS.le_R.trans hS.ph3.le_H
  rintro _ ⟨⟨a, ha, rfl⟩, hyC⟩
  have hd : (a : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp ha
  refine kl5_map_mem_of_mem_sup hS.ph3.le_H (hS.centralizer_le (a : G) hd fun x hx => ?_)
  have hxB : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hXH hx⟩ ∈
      (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
  have hc := Subgroup.mem_centralizer_iff.mp hyC _ hxB
  have h1 : QuotientGroup.mk' (primeComplementCore (G := H) p)
      (a * ⟨x, hXH hx⟩ * a⁻¹ * (⟨x, hXH hx⟩ : H)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  simpa using (mk'_primeComplementCore_eq_one_iff p _).mp h1

theorem exists_d1KlingenFivePkg {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M H R X : Subgroup G}
    {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
    (hcfg : D1ComponentConfig3 p P M H R Rbar) (hS : D1SurvivorData p P M H R X)
    (hXel : IsElemAbelian p X) (hXc : Nat.card X = p ^ 3)
    (hT : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) = p ^ 4)
    (hZ : Nat.card (centerOf (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p))) = p)
    (hKD : HasKlingenData p Rbar
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))) :
    ∃ σ z : G, D1KlingenFivePkg p R X σ z := by
  have hp : p.Prime := Fact.out
  have hred := hcfg.red
  have hRH : R ≤ H := hcfg.ext.le_H
  have hRp : IsPGroup p (R.subgroupOf H) := hcfg.ext.isPGroup.comap_subtype
  have hO : p.Coprime (Nat.card (primeComplementCore (G := H) p)) := primeComplementCore_coprime p
  have hXR : X ≤ R := hS.le_R
  have hXH : X ≤ H := hXR.trans hRH
  have hRbar := hcfg.rbar
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set B := (X.subgroupOf H).map π with hB
  have hXp : IsPGroup p X := hcfg.ext.isPGroup.to_le hXR
  have hXp' : IsPGroup p (X.subgroupOf H) := hXp.comap_subtype
  have hcard : Nat.card B = p ^ 3 := by
    rw [hB, card_map_mk_of_isPGroup hp _ hO hXp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
  have hBT : B ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) := by
    rw [hRbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXR)
  have hBe : IsElemAbelian p B := by
    refine elementary_abelian_map p ?_ _
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
    · have := (isMulCommutative_iff.mp hXel.1) ⟨_, Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨_, Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val this
    · exact Subtype.ext (hXel.2 _ (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨σ', z', hσT, hσB, hσp, hzB, hz1, hzc, hZle⟩ :=
    exists_sigma_z_five hBT hBe hcard hred.weakCore_le hT hZ hKD
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRp ha hb hab
  obtain ⟨s, hsR, hsπ⟩ : σ' ∈ (R.subgroupOf H).map π := hRbar ▸ hσT
  obtain ⟨t, htR, htπ⟩ : z' ∈ (R.subgroupOf H).map π := hRbar ▸ hBT hzB
  have hmemE : ∀ a ∈ R.subgroupOf H, π a ∈ B → a ∈ X.subgroupOf H := by
    intro a ha h
    obtain ⟨b, hb, hba⟩ := h
    have hbR : b ∈ R.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (hXR (Subgroup.mem_subgroupOf.mp hb))
    rwa [← hinj b hbR a ha hba]
  have htX : t ∈ X.subgroupOf H := hmemE t htR (by rw [htπ]; exact hzB)
  have hsX : s ∉ X.subgroupOf H := fun h => hσB (hsπ ▸ Subgroup.mem_map_of_mem π h)
  have hRc : Nat.card R = p ^ 4 := by
    rw [← hT, hRbar, card_map_mk_of_isPGroup hp _ hO hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  have hσpow : (s : G) ^ p = 1 := by
    have h := hinj _ (Subgroup.pow_mem _ hsR p) _ (Subgroup.one_mem _) (by
      rw [map_pow, hsπ, hσp, map_one])
    simpa using congrArg Subtype.val h
  have hcenter : ∀ y ∈ R, y ∈ Subgroup.centralizer (R : Set G) →
      y ∈ Subgroup.zpowers (t : G) := by
    intro y hyR hyC
    have hyR' : (⟨y, hRH hyR⟩ : H) ∈ R.subgroupOf H := hyR
    have hyT : π ⟨y, hRH hyR⟩ ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :=
      hRbar ▸ Subgroup.mem_map_of_mem π hyR'
    have hyZ : π ⟨y, hRH hyR⟩ ∈ Subgroup.centralizer
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      rw [hRbar] at hq
      obtain ⟨r, hr, rfl⟩ := hq
      have hc := Subgroup.mem_centralizer_iff.mp hyC (r : G) (Subgroup.mem_subgroupOf.mp hr)
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hc)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hZle _ hyT hyZ)
    have han : (⟨y, hRH hyR⟩ : H) = t ^ n :=
      hinj _ hyR' _ (Subgroup.zpow_mem _ htR n) (by rw [map_zpow, htπ, hn])
    exact ⟨n, by simpa using (congrArg Subtype.val han).symm⟩
  have hnorm : R ≤ Subgroup.normalizer (X : Set G) := by
    have h1 : X.relIndex R * p ^ 3 = p ^ 4 := by
      have := Subgroup.relIndex_mul_card (H := X) (K := R)
      rwa [inf_eq_left.mpr hXR, hXc, hRc] at this
    have hidx : X.relIndex R = p := by
      have : X.relIndex R * p ^ 3 = p * p ^ 3 := by rw [h1]; ring
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 3) this
    have hN : (X.subgroupOf R).Normal := by
      refine Subgroup.normal_of_index_eq_minFac_card ?_
      have h2 : (X.subgroupOf R).index = p := hidx
      rw [h2, hRc, Nat.Prime.pow_minFac hp (by norm_num)]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXR).mp hN
  obtain ⟨Eb, Db, L, hEbR, hEbc, hEbexp, hEbZ, -⟩ := hKD
  obtain ⟨S, hSH, hSR, hSmap, -, ψ, hψ⟩ := exists_lift_of_le_map hp hRH hcfg.ext.isPGroup
    (primeComplementCore (G := H) p) hO (hEbR.trans hRbar.le)
  have hScard : Nat.card S = p ^ 3 := (Nat.card_congr ψ.toEquiv).trans hEbc
  have hSexp : ∀ x ∈ S, x ^ p = 1 := pow_eq_one_of_mulEquiv ψ hEbexp
  have hEnc : ∃ a b : Eb, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have htop : Subgroup.center ↥Eb = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcon g x
    rw [htop, Subgroup.card_top, hEbc] at hEbZ
    have h3 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h3
    omega
  obtain ⟨a, b, hab⟩ := hEnc
  refine ⟨(s : G), (t : G), ?_⟩
  refine
    { card_R := hRc
      le_R := hXR
      elem := hXel
      card_X := hXc
      z_mem := Subgroup.mem_subgroupOf.mp htX
      z_ne := ?_
      center_le := hcenter
      σ_mem := Subgroup.mem_subgroupOf.mp hsR
      σ_not_mem := fun h => hsX (Subgroup.mem_subgroupOf.mpr h)
      σ_pow := hσpow
      le_normalizer := hnorm
      heis := ⟨S, hSR, hScard, hSexp, ((ψ.symm a : S) : G), (ψ.symm a).2, ((ψ.symm b : S) : G),
        (ψ.symm b).2, fun h => hab ?_⟩ }
  · intro h1
    have ht1 : t = 1 := Subtype.ext h1
    exact hz1 (by rw [← htπ, ht1, map_one])
  · have h1 : ψ.symm a * ψ.symm b = ψ.symm b * ψ.symm a := Subtype.ext h
    simpa using congrArg ψ h1

end Package

end CFSG.LocalAnalysis.RankThreeTheoremC
