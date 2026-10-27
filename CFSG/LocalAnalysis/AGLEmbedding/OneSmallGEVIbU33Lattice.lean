module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbU33Data
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbCubeDefs
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroLift
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoverAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def IsInvR (p : ℕ) (H R : Subgroup G) (K : Subgroup (H ⧸ primeComplementCore (G := H) p))
    (z : G) (B : Subgroup G) : Prop :=
  ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
    (∀ t ∈ d1LiftX p H R K, n * t * n⁻¹ ∈ d1LiftX p H R K) → ∀ b ∈ B, n * b * n⁻¹ ∈ B

namespace D1IbCubeThreeData

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {z : G}

theorem exists_lift (hc : D1IbCubeThreeData p P M H R Rbar K z) {T₁ : Sylow p K}
    (hT₁ : (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K)
    {nb : K} (hnb : nb ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K)) :
    ∃ n : H, (n : G) ∈ Subgroup.normalizer (R : Set G) ∧ (n : G) * z * (n : G)⁻¹ = z ∧
      (∀ t ∈ d1LiftX p H R K, (n : G) * t * (n : G)⁻¹ ∈ d1LiftX p H R K) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) n =
        (nb : H ⧸ primeComplementCore (G := H) p) := by
  obtain ⟨n, hnR, hnz, hnπ⟩ := hc.data.exists_lift_of_mem_normalizer hc.elt hc.dec hT₁ hnb
  refine ⟨n, hnR, hnz, ?_, hnπ⟩
  rintro _ ⟨t', ⟨ht'R, ht'K⟩, rfl⟩
  refine ⟨n * t' * n⁻¹, ⟨?_, ?_⟩, rfl⟩
  · exact (Subgroup.mem_normalizer_iff.mp hnR (t' : G)).mp ht'R
  · show QuotientGroup.mk' (primeComplementCore (G := H) p) (n * t' * n⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv, hnπ]
    exact K.mul_mem (K.mul_mem nb.2 ht'K) (K.inv_mem nb.2)

theorem mk_eq_iff (hc : D1IbCubeThreeData p P M H R Rbar K z) {a b : H} (ha : (a : G) ∈ R)
    (hb : (b : G) ∈ R)
    (hab : QuotientGroup.mk' (primeComplementCore (G := H) p) a =
      QuotientGroup.mk' (primeComplementCore (G := H) p) b) : a = b :=
  eq_of_mk_eq_of_isPGroup hc.prime _ (primeComplementCore_coprime (G := H) p)
    hc.data.cfg.ext.isPGroup.comap_subtype ha hb hab

theorem exists_moves (hc : D1IbCubeThreeData p P M H R Rbar K z) (hOrb3 : KFactSmallOrbitsCube)
    {t : G} (ht : t ∈ d1LiftX p H R K) (ht1 : t ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z ∧
      (∀ s ∈ d1LiftX p H R K, n * s * n⁻¹ ∈ d1LiftX p H R K) ∧ n * t * n⁻¹ ≠ t := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, hs, hnab, hcat, hT₁nc, hΓ, -⟩ := hc.data.exists_sylow
  have hT₁card : Nat.card T₁ = p ^ 3 := by
    rw [← hc.card_T, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  obtain ⟨t', ⟨ht'R, ht'K⟩, rfl⟩ := ht
  set kt : K := ⟨π t', ht'K⟩
  have hkt : kt ∈ (T₁ : Subgroup K) := by
    have h1 : (kt : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :=
      ⟨by rw [hc.data.cfg.rbar]; exact ⟨t', ht'R, rfl⟩, ht'K⟩
    rw [← hT₁] at h1
    obtain ⟨k, hk, hkeq⟩ := h1
    rwa [show k = kt from Subtype.ext hkeq] at hk
  have hkt1 : kt ≠ 1 := by
    intro h1
    apply ht1
    have h2 : π t' = π 1 := by
      rw [map_one]
      exact congrArg Subtype.val h1
    have := hc.mk_eq_iff (b := 1) ht'R R.one_mem h2
    rw [this]
    rfl
  obtain ⟨nb, hnb, hne⟩ := (hOrb3 K hs hnab hcat p hp hc.data.cfg.red.ne_two T₁ hT₁nc hΓ
    hc.data.small hT₁card).2 kt hkt hkt1
  obtain ⟨n, hnR, hnz, hnT, hnπ⟩ := hc.exists_lift hT₁ hnb
  refine ⟨n, hnR, hnz, hnT, fun heq => hne ?_⟩
  have h1 : n * t' * n⁻¹ = t' := Subtype.ext heq
  apply Subtype.ext
  change (nb : H ⧸ primeComplementCore (G := H) p) * π t' * (nb : H ⧸ _)⁻¹ = π t'
  rw [← hnπ, ← map_inv, ← map_mul, ← map_mul, h1]

theorem card_ne_of_inv (hc : D1IbCubeThreeData p P M H R Rbar K z) (hOrb3 : KFactSmallOrbitsCube)
    {X : Subgroup G} (hXT : X ≤ d1LiftX p H R K) (hX : IsInvR p H R K z X) :
    Nat.card X ≠ p ^ 2 := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T₁, hT₁, hs, hnab, hcat, hT₁nc, hΓ, -⟩ := hc.data.exists_sylow
  have hT₁card : Nat.card T₁ = p ^ 3 := by
    rw [← hc.card_T, ← hT₁, Subgroup.card_map_of_injective K.subtype_injective]
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  have hXH : X ≤ H := hXT.trans (d1LiftX_le_H p H R K)
  set X₂ : Subgroup (H ⧸ primeComplementCore (G := H) p) := (X.subgroupOf H).map π
  have hX₂K : X₂ ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t', ⟨-, ht'K⟩, ht'x⟩ : (x : G) ∈ d1LiftX p H R K := hXT hx
    rwa [show t' = x from Subtype.ext ht'x] at ht'K
  set X₁ : Subgroup K := X₂.comap K.subtype
  have hX₁T : X₁ ≤ (T₁ : Subgroup K) := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := hk
    have hxR : (x : G) ∈ R := d1LiftX_le p H R K (hXT hx)
    have h1 : (k : H ⧸ primeComplementCore (G := H) p) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :=
      ⟨by rw [hc.data.cfg.rbar]; exact ⟨x, hxR, hxk⟩, k.2⟩
    rw [← hT₁] at h1
    obtain ⟨k', hk', hk'eq⟩ := h1
    rwa [show k' = k from Subtype.ext hk'eq] at hk'
  have hX₁inv : ∀ n ∈ Subgroup.normalizer ((T₁ : Subgroup K) : Set K), ∀ x ∈ X₁,
      n * x * n⁻¹ ∈ X₁ := by
    intro nb hnb k hk
    obtain ⟨n, hnR, hnz, hnT, hnπ⟩ := hc.exists_lift hT₁ hnb
    obtain ⟨x, hx, hxk⟩ := hk
    have hx' : (n : G) * x * (n : G)⁻¹ ∈ X := hX n hnR hnz hnT x hx
    refine ⟨n * x * n⁻¹, hx', ?_⟩
    show π (n * x * n⁻¹) = ((nb * k * nb⁻¹ : K) : H ⧸ primeComplementCore (G := H) p)
    rw [map_mul, map_mul, map_inv, hnπ]
    change _ = (nb : H ⧸ primeComplementCore (G := H) p) * (k : H ⧸ _) * (nb : H ⧸ _)⁻¹
    rw [show π x = (k : H ⧸ primeComplementCore (G := H) p) from hxk]
  have hcard : Nat.card X₁ = Nat.card X := by
    have h1 : X₁.map K.subtype = X₂ := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr hX₂K
    have h2 : Nat.card X₂ = Nat.card (X.subgroupOf H) := by
      refine card_map_of_coprime (p := p) π (fun y hy => ?_) ?_
      · have h3 := (mk'_primeComplementCore_eq_one_iff p y).mp hy
        have h4 := Subgroup.orderOf_dvd_natCard _ h3
        rw [Subgroup.orderOf_coe] at h4
        exact Nat.Coprime.coprime_dvd_right h4 (glbPrimeCore_coprime p H)
      · exact (hc.data.cfg.ext.isPGroup.to_le
          (hXT.trans (d1LiftX_le p H R K))).comap_subtype
    rw [← Subgroup.card_map_of_injective K.subtype_injective, h1, h2,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv]
  rw [← hcard]
  exact (hOrb3 K hs hnab hcat p hp hc.data.cfg.red.ne_two T₁ hT₁nc hΓ hc.data.small
    hT₁card).1 X₁ hX₁T hX₁inv

theorem conj_props_of_mem (hc : D1IbCubeThreeData p P M H R Rbar K z) {r : G} (hr : r ∈ R) :
    r ∈ Subgroup.normalizer (R : Set G) ∧ r * z * r⁻¹ = z ∧
      ∀ t ∈ d1LiftX p H R K, r * t * r⁻¹ ∈ d1LiftX p H R K := by
  refine ⟨Subgroup.le_normalizer hr, ?_, ?_⟩
  · rw [hc.commute_z hr, mul_inv_cancel_right]
  · have hKn : K.Normal := hc.data.cfg.red.normal_of_rankOne hc.data.comp hc.data.noncyclic
    have hrH : r ∈ H := hc.data.cfg.ext.le_H hr
    rintro _ ⟨t', ⟨ht'R, ht'K⟩, rfl⟩
    refine ⟨⟨r, hrH⟩ * t' * ⟨r, hrH⟩⁻¹, ⟨?_, ?_⟩, rfl⟩
    · exact R.mul_mem (R.mul_mem hr ht'R) (R.inv_mem hr)
    · show QuotientGroup.mk' (primeComplementCore (G := H) p) (⟨r, hrH⟩ * t' * ⟨r, hrH⟩⁻¹) ∈ K
      rw [map_mul, map_mul, map_inv]
      exact hKn.conj_mem _ ht'K _

theorem isInvR_centerOf (_hc : D1IbCubeThreeData p P M H R Rbar K z) :
    IsInvR p H R K z (centerOf (d1LiftX p H R K)) := by
  intro n _ _ hnT c hc'
  refine ⟨hnT c hc'.1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
  have ht' : n⁻¹ * t * n ∈ d1LiftX p H R K := by
    obtain ⟨u, hu, hut⟩ : ∃ u ∈ d1LiftX p H R K, n * u * n⁻¹ = t := by
      have hinj : Function.Injective (fun u : d1LiftX p H R K =>
          (⟨n * u * n⁻¹, hnT u u.2⟩ : d1LiftX p H R K)) := by
        intro a b hab
        have := congrArg Subtype.val hab
        simp only at this
        exact Subtype.ext (by simpa using this)
      obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨t, ht⟩
      exact ⟨u, u.2, congrArg Subtype.val hu⟩
    rw [← hut]
    simpa [mul_assoc] using hu
  have h1 := Subgroup.mem_centralizer_iff.mp hc'.2 _ ht'
  calc t * (n * c * n⁻¹) = n * ((n⁻¹ * t * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * t := by group

theorem le_centerOf_of_card (hc : D1IbCubeThreeData p P M H R Rbar K z) {D : Subgroup G}
    (hDT : D ≤ d1LiftX p H R K) (hDinv : ∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D)
    (hD : Nat.card D = p) : D ≤ centerOf (d1LiftX p H R K) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  have hDR : D ≤ R := hDT.trans (d1LiftX_le p H R K)
  have hRp : IsPGroup p ↥R := hc.data.cfg.ext.isPGroup
  have : Group.IsNilpotent ↥R := hRp.isNilpotent
  set D' : Subgroup ↥R := D.subgroupOf R
  have hD'n : D'.Normal := ⟨fun d hd r => Subgroup.mem_subgroupOf.mpr
    (hDinv r r.2 d (Subgroup.mem_subgroupOf.mp hd))⟩
  have hD'ne : D' ≠ ⊥ := by
    intro h
    have h1 : Nat.card D' = 1 := by rw [h, Subgroup.card_bot]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv, hD] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨⟨d, hdD, hdZ⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hD'ne)
  have hd1' : (d : G) ≠ 1 := fun h => hd1 (Subtype.ext (Subtype.ext h))
  have hdDG : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hdD
  have hzd : Subgroup.zpowers (d : G) = D := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdDG) ?_
    rw [hD, Nat.card_zpowers]
    have h1 : orderOf (d : G) ∣ p := hD ▸ Subgroup.orderOf_dvd_natCard D hdDG
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hd1'
    · exact h.ge
  intro x hx
  rw [← hzd] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  refine hc.mem_centerOf_of_comm (hDT (hzd ▸ Subgroup.zpow_mem_zpowers _ k)) fun r hr => ?_
  have h1 : (d : G) * r = r * d :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hdZ ⟨r, hr⟩).symm
  exact (Commute.zpow_left h1 k).eq

theorem lattice (hc : D1IbCubeThreeData p P M H R Rbar K z) (hShape : KFactSmallSylowShape)
    (hOrb3 : KFactSmallOrbitsCube) {B : Subgroup G} (hBR : B ≤ R) (hB : IsInvR p H R K z B) :
    d1LiftX p H R K ≤ B ∨
      ((∀ b ∈ B, ∃ c ∈ centerOf (d1LiftX p H R K), ∃ i : ℕ, b = c * z ^ i) ∧
        (B ⊓ d1LiftX p H R K = ⊥ → B ≤ Subgroup.zpowers z) ∧
        (B ⊓ d1LiftX p H R K ≠ ⊥ → centerOf (d1LiftX p H R K) ≤ B)) := by
  have hp := hc.prime
  have : Fact p.Prime := ⟨hp⟩
  set T := d1LiftX p H R K
  set Z₀ := centerOf T
  set D := B ⊓ T
  have hTcard : Nat.card T = p ^ 3 := hc.card_d1LiftX.1
  have hTR : T ≤ R := d1LiftX_le p H R K
  have hDinv : IsInvR p H R K z D := fun n hn hnz hnT b hb =>
    ⟨hB n hn hnz hnT b hb.1, hnT b hb.2⟩
  have hDR : ∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D := fun r hr => by
    obtain ⟨h1, h2, h3⟩ := hc.conj_props_of_mem hr
    exact hDinv r h1 h2 h3
  have hkey : ∀ b ∈ B, ∀ t ∈ T, ∀ i : ℕ, b = t * z ^ i →
      ∀ n ∈ Subgroup.normalizer (R : Set G), n * z * n⁻¹ = z →
        (∀ s ∈ T, n * s * n⁻¹ ∈ T) → n * t * n⁻¹ * t⁻¹ ∈ D := by
    intro b hb t ht i hbt n hn hnz hnT
    have h1 := hB n hn hnz hnT b hb
    have hzi : n * z ^ i * n⁻¹ = z ^ i := by rw [← conj_pow, hnz]
    have h2 : n * b * n⁻¹ * b⁻¹ = n * t * n⁻¹ * t⁻¹ := by
      rw [hbt]
      calc n * (t * z ^ i) * n⁻¹ * (t * z ^ i)⁻¹
          = n * t * n⁻¹ * (n * z ^ i * n⁻¹) * (z ^ i)⁻¹ * t⁻¹ := by group
        _ = n * t * n⁻¹ * t⁻¹ := by rw [hzi]; group
    exact ⟨h2 ▸ B.mul_mem h1 (B.inv_mem hb), T.mul_mem (hnT t ht) (T.inv_mem ht)⟩
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow hp).mp
    (hTcard ▸ Subgroup.card_dvd_of_le (inf_le_right : D ≤ T))
  interval_cases k
  · have hD : D = ⊥ := Subgroup.eq_bot_of_card_eq D (by rw [hk, pow_zero])
    have hb1 : ∀ b ∈ B, ∀ t ∈ T, ∀ i : ℕ, b = t * z ^ i → t = 1 := by
      intro b hb t ht i hbt
      by_contra ht1
      obtain ⟨n, hn, hnz, hnT, hne⟩ := hc.exists_moves hOrb3 ht ht1
      have h1 := hkey b hb t ht i hbt n hn hnz hnT
      rw [hD, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact hne h1
    right
    refine ⟨fun b hb => ?_, fun _ b hb => ?_, fun h => absurd hD h⟩
    · obtain ⟨t, ht, i, hbt⟩ := hc.dec b (hBR hb)
      exact ⟨1, Z₀.one_mem, i, by rw [hbt, hb1 b hb t ht i hbt]⟩
    · obtain ⟨t, ht, i, hbt⟩ := hc.dec b (hBR hb)
      rw [hbt, hb1 b hb t ht i hbt, one_mul]
      exact Subgroup.npow_mem_zpowers z i
  · rw [pow_one] at hk
    have hDZ : D = Z₀ := Subgroup.eq_of_le_of_card_ge
      (hc.le_centerOf_of_card inf_le_right hDR hk) (by rw [hk, hc.card_Z hShape])
    have hD1 : D ≠ ⊥ := fun h => by
      have h2 : Nat.card D = 1 := by rw [h, Subgroup.card_bot]
      rw [show Nat.card D = p from hk] at h2
      exact hp.one_lt.ne' h2
    right
    refine ⟨fun b hb => ?_, fun h => absurd h hD1, fun _ => hDZ ▸ inf_le_left⟩
    obtain ⟨t, ht, i, hbt⟩ := hc.dec b (hBR hb)
    refine ⟨t, ?_, i, hbt⟩
    by_contra htZ
    set X := Z₀ ⊔ Subgroup.zpowers t
    have hXT : X ≤ T := sup_le inf_le_left (Subgroup.zpowers_le.mpr ht)
    have hXinv : IsInvR p H R K z X := by
      intro n hn hnz hnT x hx
      have hle : X.map (MulAut.conj n).toMonoidHom ≤ X := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ?_
        · rintro _ ⟨c, hcZ, rfl⟩
          exact Subgroup.mem_sup_left (hc.isInvR_centerOf n hn hnz hnT c hcZ)
        · rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
          have h1 : n * t * n⁻¹ * t⁻¹ ∈ Z₀ := hDZ ▸ hkey b hb t ht i hbt n hn hnz hnT
          have h2 : (MulAut.conj n).toMonoidHom t = (n * t * n⁻¹ * t⁻¹) * t := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
          rw [h2]
          exact X.mul_mem (Subgroup.mem_sup_left h1)
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      exact hle ⟨x, hx, rfl⟩
    exact hc.card_ne_of_inv hOrb3 hXT hXinv (hc.elem_sup_zpowers hShape ht htZ).2.2
  · exact absurd hk (hc.card_ne_of_inv hOrb3 inf_le_right hDinv)
  · left
    have : D = T := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk, hTcard])
    exact this ▸ inf_le_left

end D1IbCubeThreeData

end CFSG.AGLEmbedding
