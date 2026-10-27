module

import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Data
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Component3
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoDataAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

section Local

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_sigma_z_of_klingenData [Fact (Nat.Prime 3)] {T : Sylow 3 Y} {B Y₀ : Subgroup Y}
    (hBT : B ≤ (T : Subgroup Y)) (hBel : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 3)
    (hweak : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) (hT : Nat.card (T : Subgroup Y) = 3 ^ 4)
    (hZ : Nat.card (centerOf (T : Subgroup Y)) = 3) (hKD : HasKlingenData 3 T Y₀) :
    ∃ σ z : Y, σ ∈ (T : Subgroup Y) ∧ σ ∉ B ∧ σ ^ 3 = 1 ∧ z ∈ B ∧ z ≠ 1 ∧
      z ∈ Subgroup.centralizer ((T : Subgroup Y) : Set Y) ∧
      (∀ b ∈ B, σ * b * σ⁻¹ = b → b ∈ Subgroup.zpowers z) ∧
      ¬ Subgroup.normalizer ((Subgroup.closure {σ, z} : Subgroup Y) : Set Y) ≤ Y₀ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨E, D, L, hET, -, -, -, hDE, hDel, hDc, -, hND, -⟩ := hKD
  have hDB : ¬ D ≤ B := by
    intro hDB
    refine hND ((normalizer_le_weakCore_of_commutative_overgroup 3 hp hBT hDB hBel.1 ?_ ?_).trans
      hweak)
    · exact le_csSup (pRank_bddAbove 3 hp D) ⟨D, le_rfl, hDel, hDc⟩
    · exact le_csSup (pRank_bddAbove 3 hp B) ⟨B, le_rfl, hBel, hBc⟩
  obtain ⟨σ, hσD, hσB⟩ := IsConcreteLE.not_le_iff_exists.mp hDB
  have hσT : σ ∈ (T : Subgroup Y) := hET (hDE hσD)
  have hDT : D ≤ (T : Subgroup Y) := hDE.trans hET
  have hTeq : (T : Subgroup Y) = B ⊔ Subgroup.zpowers σ :=
    eq_sup_zpowers_of_card hBT hσT hσB hBc hT
  have hDBne : D ⊓ B ≠ ⊥ := by
    intro h0
    have h1 : B.relIndex (T : Subgroup Y) * 3 ^ 3 = 3 ^ 4 := by
      have := Subgroup.relIndex_mul_card (H := B) (K := (T : Subgroup Y))
      rwa [inf_eq_left.mpr hBT, hBc, hT] at this
    have h2 : D.relIndex (T : Subgroup Y) * 3 ^ 2 = 3 ^ 4 := by
      have := Subgroup.relIndex_mul_card (H := D) (K := (T : Subgroup Y))
      rwa [inf_eq_left.mpr hDT, hDc, hT] at this
    have h3 := Subgroup.relIndex_inf_le (H := D) (K := B) (L := (T : Subgroup Y))
    rw [h0, Subgroup.relIndex_bot_left, hT] at h3
    have hB3 : B.relIndex (T : Subgroup Y) = 3 := by omega
    have hD9 : D.relIndex (T : Subgroup Y) = 9 := by omega
    rw [hB3, hD9] at h3
    norm_num at h3
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
  have hzo : orderOf z = 3 := orderOf_eq_prime (hDel.2 z hzD) hz1'
  have hzp : Nat.card (Subgroup.zpowers z) = 3 := by rw [Nat.card_zpowers, hzo]
  have hZeq : Subgroup.zpowers z = centerOf (T : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ⟨hzT, hzc⟩) (by rw [hzp, hZ])
  have hfix : ∀ b ∈ B, σ * b * σ⁻¹ = b → b ∈ Subgroup.zpowers z := by
    intro b hb hσb
    rw [hZeq]
    refine ⟨hBT hb, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hbσ : b * σ = σ * b := by
      calc b * σ = (σ * b * σ⁻¹) * σ := by rw [hσb]
        _ = σ * b := by group
    have hTb : (T : Subgroup Y) ≤ Subgroup.centralizer ({b} : Set Y) := by
      rw [hTeq]
      refine sup_le (fun c hc => ?_) ((Subgroup.zpowers_le).mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val ((isMulCommutative_iff.mp hBel.1) ⟨c, hc⟩ ⟨b, hb⟩)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbσ.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTb hq)
  have hzσ : Subgroup.zpowers z ≤ Subgroup.closure ({σ, z} : Set Y) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hclos : Subgroup.closure ({σ, z} : Set Y) = D := by
    have hle : Subgroup.closure ({σ, z} : Set Y) ≤ D := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      exacts [hσD, hzD]
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hdvd1 : 3 ∣ Nat.card (Subgroup.closure ({σ, z} : Set Y)) := by
      rw [← hzp]
      exact Subgroup.card_dvd_of_le hzσ
    have hdvd2 : Nat.card (Subgroup.closure ({σ, z} : Set Y)) ∣ 3 ^ 2 := by
      rw [← hDc]
      exact Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
    have hk1 : k ≠ 1 := by
      rintro rfl
      have heq : Subgroup.zpowers z = Subgroup.closure ({σ, z} : Set Y) :=
        Subgroup.eq_of_le_of_card_ge hzσ (by rw [hzp, hk]; norm_num)
      refine hσB ((Subgroup.zpowers_le.mpr hzB) ?_)
      rw [heq]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      rw [hk] at hdvd1
      norm_num at hdvd1
    have hk2' : k = 2 := by omega
    rw [hDc, hk, hk2']
  refine ⟨σ, z, hσT, hσB, hDel.2 σ hσD, hzB, hz1', hzc, hfix, ?_⟩
  rw [hclos]
  exact hND

end Local

section Package

variable {G : Type} [Group G] [Finite G]

theorem exists_d1A9DataCore_of_local [Fact (Nat.Prime 3)] {P : Sylow 3 G} {M H R X : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    (hcfg : D1ComponentConfig3 3 P M H R Rbar) (hS : D1SurvivorData 3 P M H R X)
    (hXel : IsElemAbelian 3 X) (hXc : Nat.card X = 3 ^ 3)
    (hIS : A9InSitu (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3))
      ((X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))))
    (hT : Nat.card (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) = 3 ^ 4)
    {σ' z' : H ⧸ primeComplementCore (G := H) 3}
    (hσT : σ' ∈ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)))
    (hσB : σ' ∉ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hσ3 : σ' ^ 3 = 1)
    (hzB : z' ∈ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hz1 : z' ≠ 1)
    (hzc : z' ∈ Subgroup.centralizer
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) : Set _))
    (hfix : ∀ b ∈ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)),
      σ' * b * σ'⁻¹ = b → b ∈ Subgroup.zpowers z')
    (hesc : ¬ Subgroup.normalizer ((Subgroup.closure {σ', z'} : Subgroup _) : Set _) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))) :
    ∃ σ z : G, D1A9DataCore P M H R X σ z := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hred := hcfg.red
  have hRH : R ≤ H := hcfg.ext.le_H
  have hRp : IsPGroup 3 (R.subgroupOf H) := hcfg.ext.isPGroup.comap_subtype
  have hO : (3 : ℕ).Coprime (Nat.card (primeComplementCore (G := H) 3)) :=
    primeComplementCore_coprime 3
  have hXR : X ≤ R := hS.le_R
  have hRbar := hcfg.rbar
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set X₀ := ((H ⊓ M).subgroupOf H).map π with hX₀
  set B := (X.subgroupOf H).map π with hB
  have hinj : ∀ a ∈ R.subgroupOf H, ∀ b ∈ R.subgroupOf H, π a = π b → a = b :=
    fun a ha b hb hab => eq_of_mk_eq_of_isPGroup hp _ hO hRp ha hb hab
  have hQX₀ : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ≤ X₀ :=
    (subgroup_le_weakCore_of_rank 3 hp _ hred.three_le_pRank).trans hred.weakCore_le
  have hBR : B ≤ (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [hRbar]
    exact Subgroup.map_mono (Subgroup.comap_mono hXR)
  obtain ⟨s, hsR, hsπ⟩ : σ' ∈ (R.subgroupOf H).map π := hRbar ▸ hσT
  obtain ⟨t, htR, htπ⟩ : z' ∈ (R.subgroupOf H).map π := hRbar ▸ hBR hzB
  have hmemE : ∀ a ∈ R.subgroupOf H, π a ∈ B → a ∈ X.subgroupOf H := by
    intro a ha h
    obtain ⟨b, hb, hba⟩ := h
    have hbR : b ∈ R.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (hXR (Subgroup.mem_subgroupOf.mp hb))
    rwa [← hinj b hbR a ha hba]
  have htX : t ∈ X.subgroupOf H := hmemE t htR (by rw [htπ]; exact hzB)
  have hsX : s ∉ X.subgroupOf H := fun h => hσB (hsπ ▸ Subgroup.mem_map_of_mem π h)
  have hfixG : ∀ x ∈ X, (s : G) * x * (s : G)⁻¹ = x → x ∈ Subgroup.zpowers (t : G) := by
    intro x hx hsx
    have hxR : x ∈ R := hXR hx
    have haX : (⟨x, hRH hxR⟩ : H) ∈ X.subgroupOf H := hx
    have haR : (⟨x, hRH hxR⟩ : H) ∈ R.subgroupOf H := hxR
    have hsa : s * ⟨x, hRH hxR⟩ * s⁻¹ = ⟨x, hRH hxR⟩ := Subtype.ext (by simpa using hsx)
    have hb' : σ' * π ⟨x, hRH hxR⟩ * σ'⁻¹ = π ⟨x, hRH hxR⟩ := by
      rw [← hsπ, ← map_inv, ← map_mul, ← map_mul, hsa]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hfix _ (Subgroup.mem_map_of_mem π haX) hb')
    have han : (⟨x, hRH hxR⟩ : H) = t ^ n :=
      hinj _ haR _ (Subgroup.zpow_mem _ htR n) (by rw [map_zpow, htπ, hn])
    exact ⟨n, by simpa using (congrArg Subtype.val han).symm⟩
  refine ⟨s, t, ?_⟩
  refine
    { surv := hS
      elem := hXel
      card_X := hXc
      card_R := ?_
      normalizer_le := ?_
      pRank_le := pRank_inf_le_of_pRank_top_le hp hIS.pRank_le
      perfect_le := fun Y hY hYY => le_glbPrimeCore_of_perfect hIS.solvable hY hYY
      pcore_le := fun Y hY hYN hYp => le_sup_glbPrimeCore_of_forall
        (fun W hW hWn hWp => hIS.pcore_le W hW hWn hWp) hY hYN hYp
      z_mem := Subgroup.mem_subgroupOf.mp htX
      z_ne := ?_
      z_center := ?_
      center_le := ?_
      σ_mem := Subgroup.mem_subgroupOf.mp hsR
      σ_not_mem := fun h => hsX (Subgroup.mem_subgroupOf.mpr h)
      σ_pow := ?_
      fix := hfixG
      escape := ?_ }
  ·
    rw [← hT, hRbar, card_map_mk_of_isPGroup hp _ hO hRp,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRH).toEquiv]
  ·
    refine le_normalizer_of_forall_mul_mul_inv_mem fun k hk x hx => ?_
    obtain ⟨⟨hkH, hkM⟩, hkN⟩ := hk
    have hxR : x ∈ R := hXR hx
    have hkx : k * x * k⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hkN _).mp hxR
    have hkX₀ : π ⟨k, hkH⟩ ∈ X₀ :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hkH, hkM⟩)
    have haX : (⟨x, hRH hxR⟩ : H) ∈ X.subgroupOf H := hx
    have h1 : π (⟨k, hkH⟩ * ⟨x, hRH hxR⟩ * (⟨k, hkH⟩ : H)⁻¹) ∈ B := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hIS.le_normalizer hkX₀) (π ⟨x, hRH hxR⟩)).mp
        (Subgroup.mem_map_of_mem π haX)
    have h2 : (⟨k, hkH⟩ * ⟨x, hRH hxR⟩ * (⟨k, hkH⟩ : H)⁻¹ : H) ∈ R.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (by simpa using hkx)
    simpa using Subgroup.mem_subgroupOf.mp (hmemE _ h2 h1)
  ·
    intro h1
    have ht1 : t = 1 := Subtype.ext h1
    exact hz1 (by rw [← htπ, ht1, map_one])
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : (⟨r, hRH hr⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hr
    have h := hinj _ (Subgroup.mul_mem _ hr' htR) _ (Subgroup.mul_mem _ htR hr') (by
      rw [map_mul, map_mul, htπ]
      refine Subgroup.mem_centralizer_iff.mp hzc _ ?_
      rw [hRbar]
      exact Subgroup.mem_map_of_mem π hr')
    simpa using congrArg Subtype.val h
  ·
    intro r hr
    obtain ⟨hrR, hrC⟩ := hr
    have hr' : (⟨r, hRH hrR⟩ : H) ∈ R.subgroupOf H := Subgroup.mem_subgroupOf.mpr hrR
    have hrQ : π ⟨r, hRH hrR⟩ ∈ X₀ := hQX₀ (by
      rw [hRbar]
      exact Subgroup.mem_map_of_mem π hr')
    have hrc : π ⟨r, hRH hrR⟩ ∈ Subgroup.centralizer
        (B : Set (H ⧸ primeComplementCore (G := H) 3)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨a, haX, rfl⟩
      rw [← map_mul, ← map_mul]
      refine congrArg π (Subtype.ext ?_)
      simpa using Subgroup.mem_centralizer_iff.mp hrC _ (hXR (Subgroup.mem_subgroupOf.mp haX))
    have hrX : r ∈ X := Subgroup.mem_subgroupOf.mp (hmemE _ hr' (hIS.centralizer_le ⟨hrQ, hrc⟩))
    refine hfixG r hrX ?_
    have hsr := Subgroup.mem_centralizer_iff.mp hrC _ (Subgroup.mem_subgroupOf.mp hsR)
    rw [hsr, mul_inv_cancel_right]
  ·
    have h := hinj _ (Subgroup.pow_mem _ hsR 3) _ (Subgroup.one_mem _) (by
      rw [map_pow, hsπ, hσ3, map_one])
    simpa using congrArg Subtype.val h
  ·
    intro hN
    have hOM : primeComplementCore (G := H) 3 ≤ (H ⊓ M).subgroupOf H := by
      rw [← glbPrimeCore_subgroupOf]
      exact glbPrimeCore_subgroupOf_le_inf hcfg.ext.primeCore_le
    have hDp : IsPGroup 3 (Subgroup.closure {s, t} : Subgroup H) := hRp.to_le
      ((Subgroup.closure_le _).mpr (by rintro _ (rfl | rfl); exacts [hsR, htR]))
    have hNH : Subgroup.normalizer ((Subgroup.closure {s, t} : Subgroup H) : Set H) ≤
        (H ⊓ M).subgroupOf H := fun n hn => by
      refine Subgroup.mem_subgroupOf.mpr ⟨n.2, hN ?_⟩
      have h := Subgroup.le_normalizer_map H.subtype ⟨n, hn, rfl⟩
      rwa [MonoidHom.map_closure, Set.image_pair] at h
    have h1 := le_map_of_comap_le (QuotientGroup.mk'_surjective _)
      ((comap_normalizer_map_le_sup hp _ hO hDp).trans (sup_le hOM hNH))
    rw [MonoidHom.map_closure, Set.image_pair, hsπ, htπ] at h1
    exact hesc h1

end Package

end CFSG.LocalAnalysis.RankThreeTheoremC
