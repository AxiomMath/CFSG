module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_conj_mem_sylow_of_pow_eq_one {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] (Rb : Sylow p Y) {x : Y} {k : ℕ} (hx : x ^ p ^ k = 1) :
    ∃ g : Y, g⁻¹ * x * g ∈ (Rb : Subgroup Y) := by
  have hxp : IsPGroup p (Subgroup.zpowers x) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).mp (orderOf_dvd_of_pow_eq_one hx)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y Rb S
  have hxS := hS (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    ← map_inv, MulAut.conj_apply, inv_inv] at hxS
  exact ⟨g, hxS⟩

theorem mem_sup_centralizer_of_pow_eq_one {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {Rb : Sylow p Y} {K : Subgroup Y} (hKn : K.Normal)
    (hRK : (Rb : Subgroup Y) ≤ K ⊔ Subgroup.centralizer (K : Set Y)) {x : Y} {k : ℕ}
    (hx : x ^ p ^ k = 1) : x ∈ K ⊔ Subgroup.centralizer (K : Set Y) := by
  have := hKn
  have hn : (K ⊔ Subgroup.centralizer (K : Set Y)).Normal := Subgroup.sup_normal _ _
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_of_pow_eq_one Rb hx
  have h1 := hn.conj_mem _ (hRK hg) g
  have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [e]
  exact h1

theorem D1OneSmallData.exists_lift_centralizer_of_mem (hd : D1OneSmallData p P M H R Rbar K)
    (hz : D1SmallCZElt p H R K z) (hzM : z ∈ M)
    {γ : H ⧸ primeComplementCore (G := H) p} (hγX : γ ∈ d1X0 p M H)
    (hγz : γ * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hz.2.2.1⟩ =
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hz.2.2.1⟩ * γ) :
    ∃ g : G, g ∈ H ⊓ M ∧ g * z = z * g ∧ ∃ hgH : g ∈ H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨g, hgH⟩ = γ := by
  have hp := hd.cfg.red.prime
  obtain ⟨h₀, hh₀, rfl⟩ := hγX
  set A := H ⊓ M
  set O : Subgroup ↥A := (GLBPrimeCore p H).subgroupOf A
  have hOn : O.Normal := ⟨fun n hn a => Subgroup.mem_subgroupOf.mpr (by
    simpa using (Subgroup.mem_normalizer_iff.mp (le_normalizer_glbPrimeCore p H a.2.1) n).mp
      (Subgroup.mem_subgroupOf.mp hn))⟩
  have hOc : p.Coprime (Nat.card O) := by
    have h1 : O.map A.subtype ≤ GLBPrimeCore p H := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mp hn
    rw [← Subgroup.card_map_of_injective A.subtype_injective]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h1) (glbPrimeCore_coprime p H)
  set e : ↥A := ⟨z, hz.2.2.1, hzM⟩
  have he : IsPGroup p (Subgroup.zpowers e) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hz.2.1
  set a₀ : ↥A := ⟨h₀, Subgroup.mem_subgroupOf.mp hh₀⟩
  have hx : QuotientGroup.mk' O a₀ ∈
      Subgroup.centralizer ({QuotientGroup.mk' O e} : Set (↥A ⧸ O)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have h1 := QuotientGroup.eq.mp (by rw [map_mul, map_mul]; exact hγz :
      QuotientGroup.mk' (primeComplementCore (G := H) p) (h₀ * ⟨z, hz.2.2.1⟩) =
        QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨z, hz.2.2.1⟩ * h₀))
    simpa using (mem_primeComplementCore_iff_mem_glbPrimeCore p _).mp h1
  obtain ⟨g, hg, hgx⟩ := exists_mem_centralizer_mk_eq hp O hOc he hx
  refine ⟨g, g.2, ?_, g.2.1, ?_⟩
  · exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  · refine QuotientGroup.eq.mpr ((mem_primeComplementCore_iff_mem_glbPrimeCore p _).mpr ?_)
    simpa using Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hgx)

theorem D1OneSmallData.le_zpowers_zbar_of (hd : D1OneSmallData p P M H R Rbar K)
    (hz : D1SmallCZElt p H R K z) (hph : D1PhaseThree p P M H R)
    (hcz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hle : ∀ {N : Subgroup (H ⧸ primeComplementCore (G := H) p)},
      (∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k = 1) → N ≤ d1X0 p M H →
      K ⊓ d1X0 p M H ≤ Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p)) →
      (∀ n ∈ N, n * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hz.2.2.1⟩ =
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hz.2.2.1⟩ * n) →
      N ≤ Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hz.2.2.1⟩))
    {Λ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hΛp : ∀ x ∈ Λ, ∃ k : ℕ, x ^ p ^ k = 1)
    (hΛC : Λ ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩} : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hΛn : ∀ g : ↥M, (g : G) * z = z * g → QuotientGroup.mk' (CFSG.pCore 2 ↥M) g ∈
      Subgroup.normalizer (Λ : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    Λ ≤ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hph.le_M hz.1⟩) := by
  have hp := hd.cfg.red.prime
  have hzM : z ∈ M := hph.le_M hz.1
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set zM : ↥M := ⟨z, hzM⟩
  set zH : ↥H := ⟨z, hz.2.2.1⟩
  have htwo : pCoreOf 2 M ≤ GLBPrimeCore p H :=
    (hph.twoCore_M_le hph.twoCore_inf).trans (pCoreOf_le_glbPrimeCore Nat.prime_two
      ((Nat.coprime_primes hp Nat.prime_two).mpr hd.cfg.red.ne_two) H)
  have hzbarp : mkM zM ^ p = 1 := by
    have : zM ^ p = 1 := Subtype.ext (by simp [zM, ← hz.2.1, pow_orderOf_eq_one])
    rw [← map_pow, this, map_one]
  set W : Subgroup ↥H :=
    (((Λ.comap mkM) ⊓ Subgroup.centralizer ({zM} : Set ↥M)).map M.subtype).subgroupOf H
  have hmemW : ∀ m : ↥M, mkM m ∈ Λ → (m : G) * z = z * m → ∀ hmH : (m : G) ∈ H,
      (⟨m, hmH⟩ : ↥H) ∈ W := fun m hmΛ hmz hmH => Subgroup.mem_subgroupOf.mpr
    ⟨m, ⟨hmΛ, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext hmz)⟩, rfl⟩
  have hWmem : ∀ w ∈ W, ∃ m : ↥M, mkM m ∈ Λ ∧ (m : G) * z = z * m ∧ (m : G) = w := by
    intro w hw
    obtain ⟨m, ⟨hmΛ, hmz⟩, hmw⟩ := Subgroup.mem_subgroupOf.mp hw
    exact ⟨m, hmΛ, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hmz), hmw⟩
  set N := W.map π
  have hNp : ∀ x ∈ N, ∃ k : ℕ, x ^ p ^ k = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨m, hmΛ, -, hmw⟩ := hWmem w hw
    obtain ⟨k, hk⟩ := hΛp _ hmΛ
    refine ⟨k, ?_⟩
    rw [← map_pow, mk'_primeComplementCore_eq_one_iff]
    have h1 : mkM (m ^ p ^ k) = 1 := by rw [map_pow, hk]
    have h2 := htwo (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
    simpa [← hmw] using h2
  have hNX : N ≤ d1X0 p M H := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨m, -, -, hmw⟩ := hWmem w hw
    exact ⟨w, Subgroup.mem_subgroupOf.mpr ⟨w.2, hmw ▸ m.2⟩, rfl⟩
  have hNn : K ⊓ d1X0 p M H ≤
      Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p)) := by
    rintro γ ⟨hγK, hγX⟩
    have hγz : γ * π zH = π zH * γ := Subgroup.mem_centralizer_iff.mp hz.2.2.2 γ hγK
    obtain ⟨g, hgA, hgz, hgH, hgγ⟩ := hd.exists_lift_centralizer_of_mem hz hzM hγX hγz
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨w, hw, rfl⟩ := hn
    obtain ⟨m, hmΛ, hmz, hmw⟩ := hWmem w hw
    set gM : ↥M := ⟨g, hgA.2⟩
    have h1 : mkM (gM * m * gM⁻¹) ∈ Λ := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hΛn gM hgz) _).mp hmΛ
    have h2 : ((gM * m * gM⁻¹ : ↥M) : G) * z = z * (gM * m * gM⁻¹ : ↥M) := by
      have hgz' : g⁻¹ * z = z * g⁻¹ := by
        calc g⁻¹ * z = g⁻¹ * (z * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * z) * g⁻¹ := by rw [hgz]
          _ = z * g⁻¹ := by group
      simp only [gM, Subgroup.coe_mul, Subgroup.coe_inv]
      calc g * m * g⁻¹ * z = g * m * (g⁻¹ * z) := by group
        _ = g * (m * z) * g⁻¹ := by rw [hgz']; group
        _ = g * (z * m) * g⁻¹ := by rw [hmz]
        _ = (g * z) * m * g⁻¹ := by group
        _ = z * (g * m * g⁻¹) := by rw [hgz]; group
    have h3 : ((gM * m * gM⁻¹ : ↥M) : G) ∈ H := by
      simp only [gM, Subgroup.coe_mul, Subgroup.coe_inv]
      exact H.mul_mem (H.mul_mem hgH (hmw ▸ w.2)) (H.inv_mem hgH)
    refine ⟨⟨_, h3⟩, hmemW _ h1 h2 h3, ?_⟩
    have h4 : (⟨_, h3⟩ : ↥H) = ⟨g, hgH⟩ * w * ⟨g, hgH⟩⁻¹ :=
      Subtype.ext (by simp [gM, ← hmw])
    rw [h4, map_mul, map_mul, map_inv, hgγ]
  have hNz : ∀ n ∈ N, n * π zH = π zH * n := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨m, -, hmz, hmw⟩ := hWmem w hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa [← hmw, zH] using hmz)
  intro x hx
  have hcop2 : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr hd.cfg.red.ne_two).pow_right k
  have hzMp : IsPGroup p (Subgroup.zpowers zM) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hz.2.1
  have hxC := hΛC hx
  obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M) hcop2 hzMp hxC
  have hgz : (g : G) * z = z * g :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hgH : (g : G) ∈ H := hcz (Subgroup.mem_centralizer_singleton_iff.mpr hgz)
  have hπg : π ⟨g, hgH⟩ ∈ Subgroup.zpowers (π zH) :=
    hle hNp hNX hNn hNz ⟨_, hmemW g hx hgz hgH, rfl⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hπg
  set u : ↥M := g * zM ^ (-j)
  have huH : (u : G) ∈ H := H.mul_mem hgH (H.zpow_mem hz.2.2.1 _)
  have hu : (u : G) ∈ GLBPrimeCore p H := by
    refine (mk'_primeComplementCore_eq_one_iff p (⟨u, huH⟩ : ↥H)).mp ?_
    have : (⟨u, huH⟩ : ↥H) = ⟨g, hgH⟩ * zH ^ (-j) := Subtype.ext (by simp [u, zM, zH])
    rw [this, map_mul, map_zpow, ← hj, ← zpow_add, add_neg_cancel, zpow_zero]
  obtain ⟨k, hk⟩ := hΛp _ hx
  have hzb : mkM zM ^ p = 1 := hzbarp
  have hcomm : Commute (mkM g) (mkM zM) := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hzb' : mkM zM ^ p ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, hzb, one_pow]
  have hgk : mkM g ^ p ^ (k + 1) = 1 := by rw [pow_succ, pow_mul, hk, one_pow]
  have hpow : mkM u ^ p ^ (k + 1) = 1 := by
    rw [map_mul, map_zpow, (hcomm.zpow_right _).mul_pow, hgk, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzb', one_zpow]
  have hord : orderOf (mkM u) ∣ Nat.card (GLBPrimeCore p H) :=
    (orderOf_map_dvd mkM u).trans (by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hu)
  have hu1 : mkM u = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((glbPrimeCore_coprime p H).pow_left (k + 1)) (orderOf_dvd_of_pow_eq_one hpow) hord)
  have hgu : g = u * zM ^ j := by simp [u]
  rw [hgu, map_mul, hu1, one_mul, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ j

end CFSG.AGLEmbedding
