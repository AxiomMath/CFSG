module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalAltSplit
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_lift_of_coprime {p : ℕ} (hp : p.Prime) {M : Subgroup G} {z : G} (hzM : z ∈ M)
    (hzp : orderOf z = p) (hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)))
    {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    ∃ g : ↥M, (g : G) * z = z * g ∧ (∃ j : ℕ, g ^ p ^ j = 1) ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) g = y := by
  have hp := hp
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hzMp : IsPGroup p (Subgroup.zpowers (⟨z, hzM⟩ : ↥M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hzp
  obtain ⟨g₀, hg₀, hg₀y⟩ := exists_mem_centralizer_mk_eq hp (CFSG.pCore 2 ↥M)
    hcop hzMp (Subgroup.mem_centralizer_singleton_iff.mpr hyz)
  set g := Group.pSingular p g₀
  set r := Group.pRegular p g₀
  have hgg : g ∈ Subgroup.zpowers g₀ := ⟨_, rfl⟩
  have hrg : r ∈ Subgroup.zpowers g₀ := ⟨_, rfl⟩
  have hfin : IsOfFinOrder g₀ := isOfFinOrder_of_finite g₀
  have hdec : r * g = g₀ := Group.pDecomp' p hfin
  have hgC : g ∈ Subgroup.centralizer ({(⟨z, hzM⟩ : ↥M)} : Set ↥M) :=
    (Subgroup.zpowers_le.mpr hg₀) hgg
  have hr1 : mkM r = 1 := by
    have h1 : mkM r ∈ Subgroup.zpowers y := by
      obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hrg
      rw [← ha, map_zpow, hg₀y]
      exact Subgroup.zpow_mem_zpowers y a
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 : mkM r ^ p ^ k = 1 := by
      rw [← ha, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
    have h3 : (orderOf (mkM r)).Coprime p :=
      Nat.Coprime.coprime_dvd_left (orderOf_map_dvd mkM r) (Group.isPRegular_pRegular p hfin)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (h3.symm.pow_left k)
      (orderOf_dvd_of_pow_eq_one h2) dvd_rfl)
  refine ⟨g, congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hgC), ?_, ?_⟩
  · obtain ⟨n, hn⟩ := Group.isPSingular_pSingular p g₀
    exact ⟨n, by rw [← hn, pow_orderOf_eq_one]⟩
  · rw [← hg₀y, ← hdec, map_mul, hr1, one_mul]

theorem exists_conj_rPart_of {p : ℕ} (hp : p.Prime) {M R : Subgroup G} {z : G} (hRM : R ≤ M)
    (hzM : z ∈ M) (hzp : orderOf z = p) (hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M)))
    (hRC : R ≤ Subgroup.centralizer ({z} : Set G)) (hb0 : D1CzB0 p R z) (hRp : IsPGroup p R)
    {L : Subgroup G}
    (hN : ∀ {y : ↥M ⧸ CFSG.pCore 2 ↥M}, y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y →
      y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {y : ↥M ⧸ CFSG.pCore 2 ↥M} (hyL : y ∈ barM M L)
    (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y) {k : ℕ}
    (hy : y ^ p ^ k = 1) :
    ∃ g : ↥M, QuotientGroup.mk' (CFSG.pCore 2 ↥M) g = y ∧ ∃ a : G, a ∈ M ∧
      a * z = z * a ∧ a⁻¹ * (g : G) * a ∈ rPart M R (barM M L) := by
  have hp := hp
  have : Fact p.Prime := ⟨hp⟩
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hRM := hRM
  obtain ⟨g, hgz, hgp, rfl⟩ := exists_pow_lift_of_coprime hp hzM hzp hcop hyz hy
  set A := Subgroup.centralizer ({z} : Set G) ⊓ M
  have hRA : R ≤ A := le_inf hRC hRM
  have hmax : ∀ Q : Subgroup G, Q ≤ A → IsPGroup p Q → Nat.card Q ≤ Nat.card R := by
    intro Q hQA hQ
    obtain ⟨Q₀, hQ₀⟩ := hb0
    rw [← hQ₀]
    exact card_le_card_map_sylow Q₀ hQ (hQA.trans inf_le_left)
  have hgA : (g : G) ∈ A := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hgz, g.2⟩
  obtain ⟨j, hj⟩ := hgp
  obtain ⟨a, haA, haR⟩ := exists_conj_mem_of_card_le hRA hRp hmax hgA
    ⟨j, by simpa using congrArg Subtype.val hj⟩
  have haz : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp haA.1
  have haN : mkM ⟨a, haA.2⟩ ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine hN ?_
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext haz)
  refine ⟨g, rfl, a, haA.2, haz, (mem_rPart hRM haR).mpr ?_⟩
  have he : (⟨a⁻¹ * g * a, hRM haR⟩ : ↥M) = (⟨a, haA.2⟩ : ↥M)⁻¹ * g * ⟨a, haA.2⟩ := rfl
  rw [he, map_mul, map_mul, map_inv]
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) (mkM g)).mp hyL
  rw [inv_inv] at this
  exact this

theorem mem_zpowers_of_mem_block_of {p : ℕ} (hp : p.Prime) {M R : Subgroup G} {z : G}
    (hRM : R ≤ M) (hzM : z ∈ M) (hzp : orderOf z = p)
    (hcop : p.Coprime (Nat.card (CFSG.pCore 2 ↥M))) (hRC : R ≤ Subgroup.centralizer ({z} : Set G))
    (hb0 : D1CzB0 p R z) (hRp : IsPGroup p R) {L : Subgroup G}
    (hN : ∀ {y : ↥M ⧸ CFSG.pCore 2 ↥M}, y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y →
      y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hBL : rPart M R (barM M L) ≤ Subgroup.zpowers z) {y : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hyL : y ∈ barM M L) (hyz : y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y) {k : ℕ} (hy : y ^ p ^ k = 1) :
    y ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩) := by
  obtain ⟨g, rfl, a, -, haz, hga⟩ :=
    exists_conj_rPart_of hp hRM hzM hzp hcop hRC hb0 hRp hN hyL hyz hy
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hBL hga)
  have hg : (g : G) = z ^ i := by
    have haz' : Commute a (z ^ i) := Commute.zpow_right haz i
    calc (g : G) = a * (a⁻¹ * g * a) * a⁻¹ := by group
      _ = a * z ^ i * a⁻¹ := by rw [← hi]
      _ = z ^ i := by rw [haz'.eq, mul_inv_cancel_right]
  have hgM : g = (⟨z, hzM⟩ : ↥M) ^ i := Subtype.ext (by simp [hg])
  rw [hgM, map_zpow]
  exact Subgroup.zpow_mem_zpowers _ i

omit [Finite G] in
theorem rPart_inv_of {p : ℕ} {M H R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    {z : G} (hRM : R ≤ M) (hNM : Subgroup.normalizer (R : Set G) ≤ M) (hzM : z ∈ M)
    {L : Subgroup G}
    (hN : ∀ {y : ↥M ⧸ CFSG.pCore 2 ↥M}, y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y →
      y ∈ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    {X : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hX : Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ≤
      Subgroup.normalizer (X : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) →
        ∀ b ∈ rPart M R X, n * b * n⁻¹ ∈ rPart M R X := by
  intro n hn hnz _ b hb
  have hRM := hRM
  have hnM : n ∈ M := hNM hn
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  have hnz' : mkM ⟨n, hnM⟩ * mkM ⟨z, hzM⟩ = mkM ⟨z, hzM⟩ * mkM ⟨n, hnM⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using (mul_inv_eq_iff_eq_mul.mp hnz))
  have hnN := hX (hN hnz')
  have hbR : b ∈ R := hb.1
  have hnbR : n * b * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn b).mp hbR
  rw [mem_rPart hRM hbR] at hb
  rw [mem_rPart hRM hnbR]
  have h1 : (⟨n * b * n⁻¹, hRM hnbR⟩ : ↥M) = ⟨n, hnM⟩ * ⟨b, hRM hbR⟩ * ⟨n, hnM⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.mp hnN _).mp hb

theorem inv_subgroup_of {p : ℕ} (hp : p.Prime) {H R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G} (hzp : orderOf z = p)
    (hTcard : Nat.card (d1LiftX p H R K) = p ^ 2)
    (hdec : ∀ r ∈ R, ∃ t ∈ d1LiftX p H R K, ∃ i : ℕ, r = t * z ^ i)
    (hne : ∀ {S : Set G}, D1InvSubset p H R K z S → S.ncard ≠ 1 ∧ S.ncard ≠ p - 1)
    {B : Subgroup G} (hBR : B ≤ R)
    (hBinv : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
      (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ b ∈ B, n * b * n⁻¹ ∈ B) :
    (d1LiftX p H R K ≤ B ∨ B ⊓ d1LiftX p H R K = ⊥) ∧
      (B ⊓ d1LiftX p H R K = ⊥ → B ≤ Subgroup.zpowers z ∧ (z ∉ B → B = ⊥)) := by
  have hp := hp
  set T := d1LiftX p H R K
  refine ⟨?_, fun hD => ?_⟩
  · set D := B ⊓ T
    have hS : D1InvSubset p H R K z ((D : Set G) \ {1}) := by
      refine ⟨fun t ht => ⟨ht.1.2, ht.2⟩, fun n hn hnz hnT t ht => ⟨⟨hBinv n hn hnz hnT t ht.1.1,
        hnT t ht.1.2⟩, fun h1 => ht.2 ?_⟩⟩
      rw [Set.mem_singleton_iff] at h1 ⊢
      calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    have hcard := (hne hS).2
    rw [Set.ncard_sdiff_singleton_of_mem D.one_mem, ← Nat.card_coe_set_eq] at hcard
    change Nat.card D - 1 ≠ p - 1 at hcard
    have hDdvd : Nat.card D ∣ p ^ 2 := hTcard ▸ Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hDdvd
    interval_cases j
    · right
      exact Subgroup.eq_bot_of_card_eq D (by rw [hjeq, pow_zero])
    · exact absurd (by rw [hjeq, pow_one]) hcard
    · left
      have : D = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hjeq, hTcard])
      exact this ▸ inf_le_left
  · have hBz : B ≤ Subgroup.zpowers z := by
      intro b hb
      obtain ⟨t, ht, i, rfl⟩ := hdec b (hBR hb)
      by_cases ht1 : t = 1
      · rw [ht1, one_mul]
        exact Subgroup.npow_mem_zpowers z i
      exfalso
      have hfix : ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
          (∀ s ∈ T, n * s * n⁻¹ ∈ T) → n * t * n⁻¹ = t := by
        intro n hn hnz hnT
        have h1 := hBinv n hn hnz hnT _ hb
        have h2 : n * (t * z ^ i) * n⁻¹ * (t * z ^ i)⁻¹ = n * t * n⁻¹ * t⁻¹ := by
          have : n * z ^ i * n⁻¹ = z ^ i := by rw [← conj_pow, hnz]
          calc n * (t * z ^ i) * n⁻¹ * (t * z ^ i)⁻¹
              = n * t * n⁻¹ * (n * z ^ i * n⁻¹) * (z ^ i)⁻¹ * t⁻¹ := by group
            _ = n * t * n⁻¹ * t⁻¹ := by rw [this]; group
        have h3 : n * t * n⁻¹ * t⁻¹ ∈ B ⊓ T := by
          rw [← h2]
          exact ⟨B.mul_mem h1 (B.inv_mem hb), by
            rw [h2]; exact T.mul_mem (hnT t ht) (T.inv_mem ht)⟩
        rw [hD, Subgroup.mem_bot] at h3
        exact mul_inv_eq_one.mp h3
      have hS : D1InvSubset p H R K z {t} := by
        refine ⟨fun s hs => ?_, fun n hn hnz hnT s hs => ?_⟩
        · rw [Set.mem_singleton_iff] at hs
          exact hs ▸ ⟨ht, ht1⟩
        · rw [Set.mem_singleton_iff] at hs ⊢
          rw [hs]
          exact hfix n hn hnz hnT
      exact (hne hS).1 (Set.ncard_singleton t)
    refine ⟨hBz, fun hzB => (Subgroup.eq_bot_iff_forall _).mpr fun b hb => ?_⟩
    by_contra hb1
    exact hzB ((Subgroup.zpowers_le.mpr hb) (mem_zpowers_of_mem_zpowers_of_prime hp hzp
      (hBz hb) hb1))

theorem eq_one_of_mem_sup_of_block {p : ℕ} (hp : p.Prime) {M H R : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G} (hRM : R ≤ M) (hzR : z ∈ R)
    (hzp : orderOf z = p) (hzM : z ∈ M) (hRC : R ≤ Subgroup.centralizer ({z} : Set G))
    (hexp : ∀ r ∈ R, r ^ p = 1) (hzT : z ∉ d1LiftX p H R K) {L : Subgroup G}
    (hblock : ∀ {y : ↥M ⧸ CFSG.pCore 2 ↥M}, y ∈ barM M L →
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ * y → ∀ {k : ℕ}, y ^ p ^ k = 1 →
      y ∈ Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩))
    (hzbL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M L)
    (hBC : rPart M R (Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) = ⊥)
    {t : G} (ht : t ∈ d1LiftX p H R K) (hRt : t ∈ M)
    (htL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨t, hRt⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) : t = 1 := by
  have hRM := hRM
  have htR : t ∈ R := d1LiftX_le p H R K ht
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M)
  set x := mkM ⟨t, hRt⟩
  set zb := mkM ⟨z, hzM⟩
  have hxz : x * zb = zb * x := by
    rw [← map_mul, ← map_mul]
    exact congrArg mkM (Subtype.ext
      (Subgroup.mem_centralizer_singleton_iff.mp (hRC htR)))
  have hxp : x ^ p = 1 := by
    have : (⟨t, hRt⟩ : ↥M) ^ p = 1 := Subtype.ext (by simpa using hexp t htR)
    rw [← map_pow, this, map_one]
  set Lb := barM M L
  set C := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  have hLC : Lb ≤ Subgroup.normalizer (C : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb C hLC] at htL
  obtain ⟨l, hl, c, hcC, hlc⟩ := htL
  have hlx : l⁻¹ * x ∈ C := by
    have : x = l * c := hlc.symm
    rw [this]
    simpa using hcC
  obtain ⟨l', hl'L, hl'l, hl'p, hl'c⟩ :=
    exists_pow_mem_of_inv_mul_mem_centralizer hp hxp hl hlx
  have hcz : zb * c = c * zb := Subgroup.mem_centralizer_iff.mp hcC zb hzbL
  have hlz : l * zb = zb * l := by
    have : l = x * c⁻¹ := by rw [← hlc]; group
    have hcz' : c⁻¹ * zb = zb * c⁻¹ := by
      calc c⁻¹ * zb = c⁻¹ * (zb * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * zb) * c⁻¹ := by rw [hcz]
        _ = zb * c⁻¹ := by group
    rw [this]
    calc x * c⁻¹ * zb = x * (c⁻¹ * zb) := by group
      _ = x * zb * c⁻¹ := by rw [hcz']; group
      _ = zb * (x * c⁻¹) := by rw [hxz]; group
  have hl'z : l' * zb = zb * l' := by
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hl'l
    rw [← ha]
    exact (Commute.zpow_left hlz a).eq
  obtain ⟨k, hk⟩ := hl'p
  obtain ⟨i, hi⟩ :=
    Subgroup.mem_zpowers_iff.mp (hblock hl'L hl'z hk)
  have hzR : z ^ (-i) * t ∈ R := R.mul_mem (R.zpow_mem hzR _) htR
  have h1 : z ^ (-i) * t ∈ rPart M R C := by
    refine (mem_rPart hRM hzR).mpr ?_
    have he : (⟨z ^ (-i) * t, hRM hzR⟩ : ↥M) = (⟨z, hzM⟩ : ↥M) ^ (-i) * ⟨t, hRt⟩ :=
      Subtype.ext (by simp)
    rw [he, map_mul, map_zpow]
    change zb ^ (-i) * x ∈ C
    rw [zpow_neg, hi]
    exact hl'c
  rw [hBC, Subgroup.mem_bot] at h1
  have hti : t = z ^ i := by
    calc t = z ^ i * (z ^ (-i) * t) := by group
      _ = z ^ i := by rw [h1, mul_one]
  by_contra ht1
  have hzt : z ∈ Subgroup.zpowers t := mem_zpowers_of_mem_zpowers_of_prime hp hzp
    (hti ▸ Subgroup.zpow_mem_zpowers z i) ht1
  exact hzT ((Subgroup.zpowers_le.mpr ht) hzt)

end CFSG.AGLEmbedding
