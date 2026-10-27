module

public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UPrimeExcL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

namespace L34FF

omit [Finite G] in
theorem le_normalizer_centralizer_of_normalizes {A B : Subgroup G}
    (h : A ≤ Subgroup.normalizer (B : Set G)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (B : Set G), ∀ c ∈ Subgroup.centralizer (B : Set G),
      x * c * x⁻¹ ∈ Subgroup.centralizer (B : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : x⁻¹ * b * x⁻¹⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (B : Set G)).inv_mem hx) b).mp hb
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hb'
    simp only [inv_inv] at h1
    calc b * (x * c * x⁻¹) = x * ((x⁻¹ * b * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * b * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * b := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key x (h hx) c, fun hc => ?_⟩
  have := key x⁻¹ ((Subgroup.normalizer (B : Set G)).inv_mem (h hx)) _ hc
  simpa [mul_assoc] using this

omit [Finite G] in
theorem nclIn_le_of_le_normalizer {X Z Ω : Subgroup G} (hZ : Z ≤ Ω)
    (hX : X ≤ Subgroup.normalizer (Ω : Set G)) : nclIn X Z ≤ Ω := by
  have : (Ω.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hX
  have hle : Subgroup.normalClosure ((Z.subgroupOf X : Subgroup X) : Set X) ≤ Ω.subgroupOf X :=
    Subgroup.normalClosure_le_normal fun y hy => hZ hy
  rintro _ ⟨x, hx, rfl⟩
  exact hle hx

omit [Finite G] in
theorem le_centralizer_nclIn {X Z D : Subgroup G} (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hDZ : D ≤ Subgroup.centralizer (Z : Set G)) :
    D ≤ Subgroup.centralizer (nclIn X Z : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  have : ((Subgroup.centralizer (D : Set G)).subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_centralizer_of_normalizes hXD)
  have hle : Subgroup.normalClosure ((Z.subgroupOf X : Subgroup X) : Set X) ≤
      (Subgroup.centralizer (D : Set G)).subgroupOf X :=
    Subgroup.normalClosure_le_normal fun y hy =>
      Subgroup.le_centralizer_iff.mp hDZ (Subgroup.mem_subgroupOf.mp hy)
  rintro _ ⟨x, hx, rfl⟩
  exact hle hx

omit [Finite G] in
theorem le_normalizer_inf_of_normalizes_both {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G))
    (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro h hh
  have h1 := hA hh
  have h2 := hB hh
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro x
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩, fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

omit [Finite G] in
theorem eq_one_of_pow_three_pow_of_pow_two_pow {M' : Type*} [Monoid M'] {x : M'} {a b : ℕ}
    (h3 : x ^ 3 ^ a = 1) (h2 : x ^ 2 ^ b = 1) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left
    (orderOf_dvd_of_pow_eq_one h3) (Nat.Coprime.pow _ _ (by norm_num)))
    (orderOf_dvd_of_pow_eq_one h2))

end L34FF

variable {P : Sylow 3 G} {M H R : Subgroup G} {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.twoCore_le_of_isSylowTwoOf (hd : D1OneSmallData 3 P M H R Rbar K)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) : pCoreOf 2 H ≤ V := by
  have hS2 := RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hHS := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hcop : Nat.Coprime 3 (Nat.card (pCoreOf 2 H)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hSD : pCoreOf 2 H ≤ GLBPrimeCore 3 (H ⊓ M) :=
    le_glbPrimeCore (_root_.le_inf (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H)
      hd.cfg.ext.toD1Escape.twoCore_le) (inf_le_left.trans hHS) hcop
  exact hV.le_of_normalizes hSD ((glbPrimeCore_le 3 _).trans (inf_le_left.trans hHS)) hS2

theorem D1OneSmallData.omegaOneCenterOf_le_twoCore (hd : D1OneSmallData 3 P M H R Rbar K)
    {V : Subgroup G} (hV : IsSylowTwoOf V (GLBPrimeCore 3 (H ⊓ M))) :
    omegaOneCenterOf V ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  have hSV := hd.twoCore_le_of_isSylowTwoOf hV
  have hVH : V ≤ H := hV.1.trans ((glbPrimeCore_le 3 _).trans inf_le_left)
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨⟨hxV, hxC⟩, hx2⟩
  have hxCS : x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := Subgroup.centralizer_le hSV hxC
  have hxS : x ∈ pCoreOf 2 H :=
    hd.cfg.glob.charTwo H hd.cfg.ext.maxTwoLocal_H.1 ⟨hVH hxV, hxCS⟩
  exact Subgroup.subset_closure ⟨⟨hxS, hxCS⟩, hx2⟩

omit [Finite G] in
theorem L34FF.le_normalizer_omegaOneCenterOf_pCoreOf_two (H : Subgroup G) :
    H ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) := by
  have : ((omegaOneCenterOf (pCoreOf 2 H)).subgroupOf (pCoreOf 2 H)).Characteristic :=
    Setup.characteristic_omegaOneCenterOf _
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((omegaOneCenterOf (pCoreOf 2 H)).subgroupOf (pCoreOf 2 H))
  rw [Subgroup.map_subgroupOf_eq_of_le (Setup.omegaOneCenterOf_le _)] at h
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans h

theorem L34FF.eq_one_of_mk_eq_mul (hcenter : Subgroup.center K = ⊥) (hle : R ≤ H ⊓ M)
    (hrbar : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) =
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)))
    (hsyl : ∃ T₁ : Sylow 3 K, (T₁ : Subgroup K).map K.subtype =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) ⊓ K)
    (hL : IsLinThreeFour K) {v : G} (hv : v ∈ GLBPrimeCore 3 (H ⊓ M)) {a : ℕ}
    (hva : v ^ 2 ^ a = 1) (hvH : v ∈ H) {k c : H ⧸ primeComplementCore (G := H) 3}
    (hk : k ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)))
    (he : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨v, hvH⟩ = k * c) : k = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  have hD₀H : GLBPrimeCore 3 (H ⊓ M) ≤ H := (glbPrimeCore_le 3 _).trans inf_le_left
  obtain ⟨T₁, hT₁⟩ := hsyl
  have hloc := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T₁
  set Dbar := ((GLBPrimeCore 3 (H ⊓ M)).subgroupOf H).map π with hDbar
  have hRD : R ≤ Subgroup.normalizer (GLBPrimeCore 3 (H ⊓ M) : Set G) :=
    hle.trans (le_normalizer_glbPrimeCore 3 (H ⊓ M))
  have hTD : ∀ t ∈ (T₁ : Subgroup K), ∀ x ∈ Dbar,
      (t : H ⧸ primeComplementCore (G := H) 3) * x * (t : H ⧸ primeComplementCore 3)⁻¹ ∈ Dbar := by
    intro t ht x hx
    have htR : (t : H ⧸ primeComplementCore (G := H) 3) ∈
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 3)) := by
      have : (t : H ⧸ primeComplementCore (G := H) 3) ∈ (T₁ : Subgroup K).map K.subtype :=
        ⟨t, ht, rfl⟩
      rw [hT₁] at this
      exact this.1
    rw [hrbar] at htR
    obtain ⟨⟨r, hrH⟩, hrR, hrt⟩ := htR
    obtain ⟨⟨d, hdH⟩, hdD, rfl⟩ := hx
    have hrd : r * d * r⁻¹ ∈ GLBPrimeCore 3 (H ⊓ M) :=
      (Subgroup.mem_normalizer_iff.mp (hRD (Subgroup.mem_subgroupOf.mp hrR)) d).mp hdD
    refine ⟨⟨r * d * r⁻¹, hD₀H hrd⟩, hrd, ?_⟩
    have e : (⟨r * d * r⁻¹, hD₀H hrd⟩ : H) = ⟨r, hrH⟩ * ⟨d, hdH⟩ * (⟨r, hrH⟩ : H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hrt]
  have hY : Dbar.subgroupOf K = ⊥ := by
    refine KFactProofs.UPrimeExcL34.eq_bot_of_le_normalizer_of_isLinThreeFour hL
      (KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hL T₁) ?_ ?_
    · intro h3
      have h1 : Nat.card (Dbar.subgroupOf K) ∣ Nat.card Dbar := by
        rw [← Subgroup.card_map_of_injective K.subtype_injective]
        exact Subgroup.card_dvd_of_le (by rintro _ ⟨y, hy, rfl⟩; exact hy)
      have h2 : Nat.card Dbar ∣ Nat.card (GLBPrimeCore 3 (H ⊓ M)) := by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD₀H).toEquiv]
        exact Subgroup.card_map_dvd _ _
      exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime 3 (H ⊓ M))
        (h3.trans (h1.trans h2))
    · intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hTD t ht _ hy
      · intro hy
        have := hTD t⁻¹ (inv_mem ht) _ hy
        rw [Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using this
  have hkc : k * c = c * k := (Subgroup.mem_centralizer_iff.mp hc k hk)
  have hkT : ∀ t ∈ (T₁ : Subgroup K), (t : H ⧸ primeComplementCore (G := H) 3) * k = k * t := by
    intro t ht
    have hvD : π ⟨v, hvH⟩ ∈ Dbar := ⟨⟨v, hvH⟩, hv, rfl⟩
    have hmem := Dbar.mul_mem (hTD t ht _ hvD) (Dbar.inv_mem hvD)
    have htc : (t : H ⧸ primeComplementCore (G := H) 3) * c = c * t :=
      Subgroup.mem_centralizer_iff.mp hc _ t.2
    have hcomm : (t : H ⧸ primeComplementCore (G := H) 3) * π ⟨v, hvH⟩ *
        (t : H ⧸ primeComplementCore 3)⁻¹ * (π ⟨v, hvH⟩)⁻¹ =
        t * k * (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹ := by
      have htc' : c * (t : H ⧸ primeComplementCore (G := H) 3)⁻¹ =
          (t : H ⧸ primeComplementCore (G := H) 3)⁻¹ * c := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [he]
      calc (t : H ⧸ primeComplementCore (G := H) 3) * (k * c) *
            (t : H ⧸ primeComplementCore 3)⁻¹ * (k * c)⁻¹
          = t * k * (c * (t : H ⧸ primeComplementCore 3)⁻¹) * c⁻¹ * k⁻¹ := by group
        _ = t * k * (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹ := by rw [htc']; group
    have hmemK : (t : H ⧸ primeComplementCore (G := H) 3) * k *
        (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem t.2 hk) (K.inv_mem t.2)) (K.inv_mem hk)
    have h1 : (⟨_, hmemK⟩ : K) ∈ Dbar.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      change (t : H ⧸ primeComplementCore (G := H) 3) * k *
        (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹ ∈ Dbar
      rw [← hcomm]
      exact hmem
    rw [hY, Subgroup.mem_bot] at h1
    have h2 : (t : H ⧸ primeComplementCore (G := H) 3) * k *
        (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h1
    calc (t : H ⧸ primeComplementCore (G := H) 3) * k =
          ((t : H ⧸ primeComplementCore 3) * k * (t : H ⧸ primeComplementCore 3)⁻¹ * k⁻¹) *
            (k * t) := by group
      _ = k * t := by rw [h2, one_mul]
  have hT₁ne : (T₁ : Subgroup K) ≠ ⊥ := by
    intro h
    have := KFactProofs.UPrimeExcL34.card_sylow_three_of_isLinThreeFour hL T₁
    rw [h, Subgroup.card_bot] at this
    norm_num at this
  obtain ⟨⟨t₀, ht₀⟩, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT₁ne
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have hkT₁ : (⟨k, hk⟩ : K) ∈ (T₁ : Subgroup K) :=
    hloc.centralizer_le t₀ ht₀ ht₀1' ⟨k, hk⟩ (Subtype.ext (hkT t₀ ht₀).symm)
  obtain ⟨b, hb⟩ := T₁.isPGroup' ⟨⟨k, hk⟩, hkT₁⟩
  have hk3 : k ^ 3 ^ b = 1 := by
    have := congrArg (fun x : (T₁ : Subgroup K) => ((x : K) : H ⧸ primeComplementCore 3)) hb
    simpa using this
  have hk2 : k ^ 2 ^ a = 1 := by
    have h1 : (k * c) ^ 2 ^ a = 1 := by
      rw [← he, ← map_pow]
      have : (⟨v, hvH⟩ : H) ^ 2 ^ a = 1 := Subtype.ext (by simpa using hva)
      rw [this, map_one]
    rw [(Commute.mul_pow hkc (2 ^ a))] at h1
    have h2 : k ^ 2 ^ a = (c ^ 2 ^ a)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hcen : (⟨k ^ 2 ^ a, K.pow_mem hk _⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      change (y : H ⧸ primeComplementCore (G := H) 3) * k ^ 2 ^ a = k ^ 2 ^ a * y
      rw [h2]
      have hcy := Subgroup.mem_centralizer_iff.mp
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ hc (2 ^ a))) _ y.2
      exact hcy
    rw [hcenter, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hcop : Nat.Coprime (orderOf k) (2 ^ a) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk3)
      (Nat.Coprime.pow _ _ (by norm_num))
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk2))

theorem D1OneSmallData.eq_one_of_mk_eq_mul (hd : D1OneSmallData 3 P M H R Rbar K)
    (hL : IsLinThreeFour K) {v : G} (hv : v ∈ GLBPrimeCore 3 (H ⊓ M)) {a : ℕ}
    (hva : v ^ 2 ^ a = 1) (hvH : v ∈ H) {k c : H ⧸ primeComplementCore (G := H) 3}
    (hk : k ∈ K) (hc : c ∈ Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3)))
    (he : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨v, hvH⟩ = k * c) : k = 1 :=
  L34FF.eq_one_of_mk_eq_mul hd.center hd.cfg.ext.le_inf hd.cfg.rbar
    (let ⟨T₁, h, _⟩ := hd.exists_sylow; ⟨T₁, h⟩) hL hv hva hvH hk hc he

end CFSG.AGLEmbedding
