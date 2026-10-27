module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVOuterSup

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace D1SmallAltConfig

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_pow_lift (hc : D1SmallAltConfig p P M H R Rbar K z)
    {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    ∃ g : ↥M, (g : G) * z = z * g ∧ (∃ j : ℕ, g ^ p ^ j = 1) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) g = y :=
  exists_pow_lift_of_coprime hc.prime hc.mem_M hc.elt.2.1
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact ((Nat.coprime_primes hc.prime Nat.prime_two).mpr hc.data.cfg.red.ne_two).pow_right k)
    hyz hy
theorem mem_zpowers_of_mem_block (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hB : D1AltBlockInputs) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    y ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hc.mem_M⟩) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hRM := hc.phase.le_M
  obtain ⟨g, hgz, hgp, rfl⟩ := hc.exists_pow_lift hyz hy
  set A := Subgroup.centralizer ({z} : Set G) ⊓ M
  have hRA : R ≤ A := le_inf hc.le_centralizer hRM
  have hmax : ∀ Q : Subgroup G, Q ≤ A → IsPGroup p Q → Nat.card Q ≤ Nat.card R := by
    intro Q hQA hQ
    obtain ⟨Q₀, hQ₀⟩ := hc.b0
    rw [← hQ₀]
    exact card_le_card_map_sylow Q₀ hQ (hQA.trans inf_le_left)
  have hgA : (g : G) ∈ A := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgz, g.2⟩
  obtain ⟨j, hj⟩ := hgp
  obtain ⟨a, haA, haR⟩ := exists_conj_mem_of_card_le hRA hc.phase.isPGroup hmax hgA
    ⟨j, by simpa using congrArg Subtype.val hj⟩
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haA.1
  have haN : mkM ⟨a, haA.2⟩ ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine hc.mem_normalizer_of_commute hB hL ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext haz)
  have h1 : a⁻¹ * g * a ∈ rPart M R (barM M L) := by
    refine (mem_rPart hRM haR).mpr ?_
    have he : (⟨a⁻¹ * g * a, hRM haR⟩ : ↥M) = (⟨a, haA.2⟩ : ↥M)⁻¹ * g * ⟨a, haA.2⟩ := rfl
    rw [he, map_mul, map_mul, map_inv]
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) (mkM g)).mp hyL
    rw [inv_inv] at this
    exact this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hBL h1)
  have hg : (g : G) = z ^ i := by
    have haz' : Commute a (z ^ i) := (Commute.zpow_right haz i)
    calc (g : G) = a * (a⁻¹ * g * a) * a⁻¹ := by group
      _ = a * z ^ i * a⁻¹ := by rw [← hi]
      _ = z ^ i := by rw [haz'.eq, mul_inv_cancel_right]
  have hgM : g = (⟨z, hc.mem_M⟩ : ↥M) ^ i := Subtype.ext (by simp [hg])
  rw [hgM, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ i

theorem eq_one_of_mem_sup (hc : D1SmallAltConfig p P M H R Rbar K z) (hB : D1AltBlockInputs)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥)
    {t : G} (ht : t ∈ d1LiftX p H R K) (hRt : t ∈ M)
    (htL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, hRt⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : t = 1 :=
  eq_one_of_mem_sup_of_block hc.prime hc.phase.le_M hc.elt.1 hc.elt.2.1 hc.mem_M hc.le_centralizer
    hc.exp hc.card_d1LiftX.2 (fun hyL hyz _ hy => hc.mem_zpowers_of_mem_block hB hL hBL hyL hyz hy)
    (hc.zbar_mem_block hB hL) hBC ht hRt htL
theorem false_of_rPart_eq_bot (hc : D1SmallAltConfig p P M H R Rbar K z)
    (hB : D1AltBlockInputs) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥) :
    False := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  obtain ⟨hTcard, -⟩ := hc.card_d1LiftX
  set T := d1LiftX p H R K
  have hRM := hc.phase.le_M
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hcomm : ∀ t (ht : t ∈ T), mkM ⟨t, hRM (hTR ht)⟩ ∈
      Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro t ht
    refine hc.mem_normalizer_of_commute hB hL ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hc.le_centralizer (hTR ht))))
  have hpow : ∀ t (ht : t ∈ T), mkM ⟨t, hRM (hTR ht)⟩ ^ p = 1 := by
    intro t ht
    have : (⟨t, hRM (hTR ht)⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hc.exp t (hTR ht))
    rw [← map_pow, this, map_one]
  obtain ⟨t₀, ht₀T, ht₀1⟩ : ∃ t ∈ T, t ≠ 1 := by
    by_contra h
    push Not at h
    have : T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [this, Subgroup.card_bot] at hTcard
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hp.one_lt
    omega
  rcases hc.phase.blockType_alt hB hL with htype | ⟨hcl, hpar, hne, hnB⟩
  · exact ht₀1 (hc.eq_one_of_mem_sup hB hL hBL hBC ht₀T (hRM (hTR ht₀T))
      (hB.hOP _ (barM M L) hL.component p hp hc.five_le htype _ (hcomm t₀ ht₀T)
        (hpow t₀ ht₀T)))
  set E := barM M T
  have hTp : IsPGroup p (T.subgroupOf M) := (hc.phase.isPGroup.to_le hTR).comap_subtype
  have hinj := pGroup_quotient_subgroupMap_injective_of_coprime_kernel p hp (CFSG.pCore 2 ↥M)
    (by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
      rw [hk]
      exact fun h => hc.data.cfg.red.ne_two
        ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)))
    _ hTp
  have hEcard : Nat.card E = p ^ 2 := by
    rw [← hTcard, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTR.trans hRM)).toEquiv]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj,
      MonoidHom.subgroupMap_surjective _ _⟩)).symm
  have hEel : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨s, hs, rfl⟩⟩ := a
      obtain ⟨_, ⟨t, ht, rfl⟩⟩ := b
      change mkM s * mkM t = mkM t * mkM s
      rw [← map_mul, ← map_mul]
      exact congrArg mkM (Subtype.ext (hc.commute_of_mem_R
        (hTR (Subgroup.mem_subgroupOf.mp hs)) (hTR (Subgroup.mem_subgroupOf.mp ht))))
    · rintro _ ⟨t, ht, rfl⟩
      exact hpow _ (Subgroup.mem_subgroupOf.mp ht)
  have hEN : E ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcomm _ (Subgroup.mem_subgroupOf.mp ht)
  have hE1 : E ⊓ (barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) =
      ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨⟨t, ht, rfl⟩, hxL⟩ := hx
    have h1 := hc.eq_one_of_mem_sup hB hL hBL hBC (Subgroup.mem_subgroupOf.mp ht) t.2 hxL
    have : t = 1 := Subtype.ext h1
    rw [this, map_one]
  exact hB.hOR _ (barM M L) _ hL.component hcl hpar hne hnB p hc.prime57
    (hc.perfectSectionsAltSq_block hB.hΓ hL) E hEN hEel hEcard hE1

end D1SmallAltConfig

end CFSG.AGLEmbedding
