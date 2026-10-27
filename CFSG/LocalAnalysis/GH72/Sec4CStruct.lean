module

public import CFSG.LocalAnalysis.GH72.Sec4C

public section

namespace CFSG.GH72

open Subgroup

namespace G4c

section Helpers

variable {X : Type*} [Group X]

theorem normal_of_top_le_normalizer {K : Subgroup X} (h : ⊤ ≤ normalizer (K : Set X)) :
    K.Normal :=
  normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem commutator_le_left_of_le_normalizer {K L : Subgroup X} (h : L ≤ normalizer (K : Set X)) :
    ⁅K, L⁆ ≤ K := by
  rw [commutator_comm]
  exact le_normalizer_iff_commutator_le_right.mp h

theorem commutator_le_right_of_le_normalizer {K L : Subgroup X} (h : K ≤ normalizer (L : Set X)) :
    ⁅K, L⁆ ≤ L :=
  le_normalizer_iff_commutator_le_right.mp h

theorem le_normalizer_commutator_right (K L : Subgroup X) :
    L ≤ normalizer ((⁅K, L⁆ : Subgroup X) : Set X) := by
  rw [commutator_comm]
  exact normalizer_commutator_ge_left L K

theorem commutator_eq_bot_of_isCyclic {K : Subgroup X} (hK : IsCyclic K) : ⁅K, K⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have := hK.commGroup.mul_comm ⟨y, hy⟩ ⟨x, hx⟩
  exact congrArg Subtype.val this

end Helpers

section Klein

variable {G : Type*} [Group G] [Finite G]

theorem isKleinFour_bar {H V : Subgroup G} (hVH : V ≤ H) (hV : IsKleinFour V) :
    IsKleinFour (bar H V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)
  set V' : Subgroup H := V.subgroupOf H with hV'
  have hV'2 : IsPGroup 2 V' := hV2.comap_subtype
  set φ : V' →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp V'.subtype with hφ
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : H) ∈ CFSG.oddCore H := by
      rw [← QuotientGroup.ker_mk' (CFSG.oddCore H), MonoidHom.mem_ker]
      exact hx
    have hbot := inf_eq_bot_of_odd_of_isPGroup (CFSG.ABGLocalTools.odd_card_oddCore (H := H))
      hV'2
    have : (x : H) ∈ CFSG.oddCore H ⊓ V' := ⟨hx', x.2⟩
    rw [hbot, mem_bot] at this
    rw [mem_bot]
    exact Subtype.ext this
  have hrange : φ.range = bar H V := by
    rw [hφ, MonoidHom.range_comp, range_subtype]
    rfl
  let e : V ≃* bar H V :=
    ((subgroupOfEquivOfLe hVH).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hrange)
  exact ⟨by rw [← Nat.card_congr e.toEquiv]; exact IsKleinFour.card_four,
    by rw [← Monoid.exponent_eq_of_mulEquiv e]; exact IsKleinFour.exponent_two⟩

end Klein

section Structure

variable {G : Type*} [Group G] [Finite G] {H R T : Subgroup G} {F : Subgroup (Bar H)}

omit [Finite G] in
theorem bar_normal_of_sup (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) : (bar H R).Normal := by
  refine normal_of_top_le_normalizer ?_
  rw [← hRF']
  exact sup_le le_normalizer (hFR.trans (centralizer_le_normalizer _))

omit [Finite G] in
theorem normal_of_sup (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) : F.Normal := by
  refine normal_of_top_le_normalizer ?_
  rw [← hRF']
  exact sup_le ((le_centralizer_iff.mp hFR).trans (centralizer_le_normalizer _)) le_normalizer

omit [Finite G] in
theorem commutator_normal_of_sup (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) : (⁅F, F⁆ : Subgroup (Bar H)).Normal := by
  refine normal_of_top_le_normalizer ?_
  rw [← hRF']
  refine sup_le ?_ (normalizer_commutator_ge_left F F)
  refine le_trans ?_ (centralizer_le_normalizer _)
  exact (le_centralizer_iff.mp hFR).trans (centralizer_le (commutator_le_of_le le_rfl le_rfl))

theorem index_eq_card_bar (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) : F.index = Nat.card (bar H R) := by
  have := bar_normal_of_sup hRF' hFR
  have h1 : Nat.card (Bar H) = Nat.card (bar H R) * Nat.card F := by
    rw [← card_top (G := Bar H), ← hRF']
    exact CFSG.CGT.Foote81L6.card_sup_of_le_normalizer (le_normalizer_of_normal) hRF
  have h2 := card_mul_index F
  have hpos : 0 < Nat.card F := Nat.card_pos
  rw [h1, mul_comm (Nat.card (bar H R))] at h2
  exact Nat.eq_of_mul_eq_mul_left hpos h2

omit [Finite G] in
theorem bar_sup_inf_le (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTF : bar H T ≤ F) :
    (bar H R ⊔ bar H T) ⊓ F ≤ bar H T := by
  have := bar_normal_of_sup hRF' hFR
  rintro u ⟨hu, huF⟩
  obtain ⟨r, hr, t, ht, rfl⟩ := mem_sup_of_normal_left.mp hu
  have hrF : r ∈ F := by
    have : r * t * t⁻¹ ∈ F := F.mul_mem huF (F.inv_mem (hTF ht))
    simpa using this
  have hr1 : r ∈ bar H R ⊓ F := ⟨hr, hrF⟩
  rw [hRF, mem_bot] at hr1
  rw [hr1, one_mul]
  exact ht

variable (S : Sylow 2 G) (hSRT : (S : Subgroup G) = R ⊔ T) (hSH : (S : Subgroup G) ≤ H)

include hSRT hSH in
theorem odd_relIndex_bar (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTF : bar H T ≤ F) :
    Odd ((bar H T).relIndex F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := bar_normal_of_sup hRF' hFR
  have hRH : R ≤ H := hSRT ▸ hSH |> fun h => le_sup_left.trans h
  have hTH : T ≤ H := hSRT ▸ hSH |> fun h => le_sup_right.trans h
  let S' : Sylow 2 H := S.subtype hSH
  let Sb : Sylow 2 (Bar H) := Sylow.mapSurjective (QuotientGroup.mk'_surjective _) S'
  have hSb : (Sb : Subgroup (Bar H)) = bar H R ⊔ bar H T := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, hSRT, ← bar_sup hRH hTH]
    rfl
  have hRT : bar H R ⊓ bar H T = ⊥ := by
    rw [eq_bot_iff]
    exact le_trans (inf_le_inf_left _ hTF) hRF.le
  have hcS : Nat.card (Sb : Subgroup (Bar H)) = Nat.card (bar H R) * Nat.card (bar H T) := by
    rw [hSb]
    exact CFSG.CGT.Foote81L6.card_sup_of_le_normalizer le_normalizer_of_normal hRT
  have hcX : Nat.card (Bar H) = Nat.card (bar H R) * Nat.card F := by
    rw [← card_top (G := Bar H), ← hRF']
    exact CFSG.CGT.Foote81L6.card_sup_of_le_normalizer le_normalizer_of_normal hRF
  have hidx : ¬ 2 ∣ (Sb : Subgroup (Bar H)).index := Sb.not_dvd_index
  have h1 := card_mul_index (Sb : Subgroup (Bar H))
  rw [hcS, hcX] at h1
  have hR0 : 0 < Nat.card (bar H R) := Nat.card_pos
  have h2 : Nat.card (bar H T) * (Sb : Subgroup (Bar H)).index = Nat.card F := by
    have := h1
    rw [mul_assoc] at this
    exact Nat.eq_of_mul_eq_mul_left hR0 this
  have h3 : Nat.card (bar H T) * (bar H T).relIndex F = Nat.card F := by
    have h := card_mul_index ((bar H T).subgroupOf F)
    rwa [Nat.card_congr (subgroupOfEquivOfLe hTF).toEquiv] at h
  have hT0 : 0 < Nat.card (bar H T) := Nat.card_pos
  have h4 : (bar H T).relIndex F = (Sb : Subgroup (Bar H)).index := by
    rw [← h2] at h3
    exact Nat.eq_of_mul_eq_mul_left hT0 h3
  rw [h4, Nat.odd_iff]
  omega

include hSRT hSH in
theorem bar_O2_eq (hR : IsPGroup 2 R) (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTL : bar H T ≤ ⁅F, F⁆) :
    bar H (O2 H) = F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn := normal_of_sup hRF' hFR
  have hLF : ⁅F, F⁆ ≤ F := commutator_le_of_le le_rfl le_rfl
  have hTF : bar H T ≤ F := hTL.trans hLF
  apply le_antisymm
  ·
    set Fp : Subgroup G := (F.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype with hFp
    have hFpH : Fp ≤ H := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hsub : Fp.subgroupOf H = F.comap (QuotientGroup.mk' (CFSG.oddCore H)) := by
      rw [hFp, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
    have hnorm : H ≤ normalizer (Fp : Set G) := by
      have : (F.comap (QuotientGroup.mk' (CFSG.oddCore H))).Normal := hFn.comap _
      exact CFSG.ABGLocalTools.le_normalizer_map_subtype H _
    have hidx : Fp.relIndex H = Nat.card (bar H R) := by
      rw [relIndex, hsub, index_comap_of_surjective _ (QuotientGroup.mk'_surjective _),
        index_eq_card_bar hRF hRF' hFR]
    obtain ⟨n, hn⟩ := (isPGroup_bar (H := H) hR).exists_card_eq
    have hle := O2_le_of_relIndex hFpH hnorm (n := n) (hidx.trans hn)
    calc bar H (O2 H) ≤ bar H Fp := bar_mono hle
      _ = F := by
        rw [bar, hsub, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  ·
    have hodd : Odd ((⁅F, F⁆ : Subgroup (Bar H)).relIndex F) := by
      have h := odd_relIndex_bar S hSRT hSH hRF hRF' hFR hTF
      rw [← relIndex_mul_relIndex _ _ _ hTL hLF] at h
      exact (Nat.odd_mul.mp h).2
    have hF2 : O2 F = F := O2_eq_self_of_odd_relIndex hodd
    have hb : O2 (⊤ : Subgroup (Bar H)) ≤ bar H (O2 H) := by
      obtain ⟨n, hn⟩ := exists_relIndex_O2 H
      have hdvd : (bar H (O2 H)).index ∣ 2 ^ n := by
        rw [← hn, relIndex]
        exact index_map_dvd _ (QuotientGroup.mk'_surjective _)
      obtain ⟨k, hk⟩ := exists_eq_two_pow_of_dvd hdvd
      refine O2_le_of_relIndex le_top ?_ (n := k) (by rw [relIndex_top_right]; exact hk)
      intro x _
      have h := bar_le_normalizer (H := H) (le_normalizer_O2 H)
      rw [bar_self] at h
      exact h (mem_top x)
    calc F = O2 F := hF2.symm
      _ ≤ O2 (⊤ : Subgroup (Bar H)) := O2_mono le_top
      _ ≤ bar H (O2 H) := hb

include hSRT hSH in
theorem bar_commutator_O2_eq (hR : IsPGroup 2 R) (hRF : bar H R ⊓ F = ⊥)
    (hRF' : bar H R ⊔ F = ⊤) (hFR : F ≤ centralizer (bar H R : Set (Bar H)))
    (hTL : bar H T ≤ ⁅F, F⁆) :
    bar H ⁅O2 H, O2 H⁆ = ⁅F, F⁆ := by
  rw [bar_commutator (O2_le H) (O2_le H), bar_O2_eq S hSRT hSH hR hRF hRF' hFR hTL]

include hSRT hSH in
theorem isPGroup_inf_centralizer (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTL : bar H T ≤ ⁅F, F⁆) :
    IsPGroup 2 (F ⊓ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) : Subgroup (Bar H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn := normal_of_sup hRF' hFR
  have hLn := commutator_normal_of_sup hRF' hFR
  have hLF : ⁅F, F⁆ ≤ F := commutator_le_of_le le_rfl le_rfl
  have hTF : bar H T ≤ F := hTL.trans hLF
  have hRH : R ≤ H := hSRT ▸ hSH |> fun h => le_sup_left.trans h
  have hTH : T ≤ H := hSRT ▸ hSH |> fun h => le_sup_right.trans h
  set T₀ := F ⊓ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) with hT₀
  have hT₀n : T₀.Normal := by
    rw [hT₀]
    infer_instance
  refine isPGroup_of_forall_le_centralizer (oddCore_bar_eq_bot H) hT₀n ?_
  intro Q hQ hQ2
  let S' : Sylow 2 H := S.subtype hSH
  let Sb : Sylow 2 (Bar H) := Sylow.mapSurjective (QuotientGroup.mk'_surjective _) S'
  have hSb : (Sb : Subgroup (Bar H)) = bar H R ⊔ bar H T := by
    rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, hSRT, ← bar_sup hRH hTH]
    rfl
  obtain ⟨c, -, hc⟩ := exists_mem_map_cj_le Sb (le_top : (Sb : Subgroup (Bar H)) ≤ ⊤) le_top hQ2
  have hcT₀ : Q.map (cj c) ≤ T₀ := by
    have hT₀c : T₀.map (cj c) = T₀ :=
      map_cj_eq_of_mem_normalizer (by rw [normalizer_eq_top]; exact mem_top c)
    exact (map_mono hQ).trans hT₀c.le
  have hcL : Q.map (cj c) ≤ ⁅F, F⁆ := by
    have h1 : Q.map (cj c) ≤ (bar H R ⊔ bar H T) ⊓ F :=
      le_inf (hSb ▸ hc) (hcT₀.trans inf_le_left)
    exact (h1.trans (bar_sup_inf_le hRF hRF' hFR hTF)).trans hTL
  have hQL : Q ≤ ⁅F, F⁆ := by
    have hLc : (⁅F, F⁆ : Subgroup (Bar H)).map (cj c⁻¹) = ⁅F, F⁆ :=
      map_cj_eq_of_mem_normalizer (by rw [normalizer_eq_top]; exact mem_top c⁻¹)
    exact (map_cj_le_iff.mp hcL).trans hLc.le
  exact inf_le_right.trans (centralizer_le hQL)

include hSRT hSH in
theorem eq_bot_of_odd_le_centralizer (hR : IsPGroup 2 R) (hRF : bar H R ⊓ F = ⊥)
    (hRF' : bar H R ⊔ F = ⊤) (hFR : F ≤ centralizer (bar H R : Set (Bar H)))
    (hTL : bar H T ≤ ⁅F, F⁆) {E : Subgroup (Bar H)} (hE : Odd (Nat.card E))
    (hEL : E ≤ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H))) : E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRn := bar_normal_of_sup hRF' hFR
  have hLF : ⁅F, F⁆ ≤ F := commutator_le_of_le le_rfl le_rfl
  set T₀ := F ⊓ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) with hT₀
  have hT₀2 : IsPGroup 2 T₀ := isPGroup_inf_centralizer S hSRT hSH hRF hRF' hFR hTL
  have hRL : bar H R ≤ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) :=
    (le_centralizer_iff.mp hFR).trans (centralizer_le hLF)
  have hle : E ≤ bar H R ⊔ T₀ := by
    intro e he
    have he' : e ∈ bar H R ⊔ F := by rw [hRF']; exact mem_top e
    obtain ⟨r, hr, f, hf, rfl⟩ := mem_sup_of_normal_left.mp he'
    have hfc : f ∈ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) := by
      have : r⁻¹ * (r * f) ∈ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) :=
        mul_mem (inv_mem (hRL hr)) (hEL he)
      simpa using this
    exact mul_mem_sup hr ⟨hf, hfc⟩
  have h2 : IsPGroup 2 (bar H R ⊔ T₀ : Subgroup (Bar H)) :=
    (isPGroup_bar hR).to_sup_of_normal_left hT₀2
  have hbot := inf_eq_bot_of_odd_of_isPGroup hE h2
  rwa [inf_eq_left.mpr hle] at hbot

include hSRT hSH in
theorem le_O_of_covers (hR : IsPGroup 2 R) (hRF : bar H R ⊓ F = ⊥) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTL : bar H T ≤ ⁅F, F⁆)
    (hLs : ∀ N : Subgroup (Bar H), N ≤ ⁅F, F⁆ → ⁅F, F⁆ ≤ normalizer (N : Set (Bar H)) →
      Odd (Nat.card N) → N = ⊥)
    {K D : Subgroup G} (hKH : K ≤ H) (hcov : ⁅O2 H, O2 H⁆ ≤ K ⊔ O H) (hDH : D ≤ H)
    (hD : Odd (Nat.card D)) (hKD : K ≤ normalizer (D : Set G)) : D ≤ O H := by
  have hLn := commutator_normal_of_sup hRF' hFR
  have hLK : ⁅F, F⁆ ≤ bar H K := by
    rw [← bar_commutator_O2_eq S hSRT hSH hR hRF hRF' hFR hTL, ← bar_sup_O hKH]
    exact bar_mono hcov
  have hLD : ⁅F, F⁆ ≤ normalizer (bar H D : Set (Bar H)) :=
    hLK.trans (bar_le_normalizer hKD)
  have hDL : bar H D ≤ normalizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) := by
    rw [normalizer_eq_top]
    exact le_top
  set N := ⁅bar H D, ⁅F, F⁆⁆ with hN
  have hNL : N ≤ ⁅F, F⁆ := commutator_le_right_of_le_normalizer hDL
  have hND : N ≤ bar H D := commutator_le_left_of_le_normalizer hLD
  have hNodd : Odd (Nat.card N) := odd_card_of_le hND (odd_card_bar hD)
  have hNbot : N = ⊥ := hLs N hNL (le_normalizer_commutator_right _ _) hNodd
  have hDc : bar H D ≤ centralizer ((⁅F, F⁆ : Subgroup (Bar H)) : Set (Bar H)) :=
    commutator_eq_bot_iff_le_centralizer.mp hNbot
  have hDbot := eq_bot_of_odd_le_centralizer S hSRT hSH hR hRF hRF' hFR hTL (odd_card_bar hD) hDc
  exact (bar_eq_bot_iff hDH).mp hDbot

theorem commutator_le_O_of_le_R (hR : IsPGroup 2 R) (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) {X' D : Subgroup G} (hXR : X' ≤ R)
    (hRH : R ≤ H) (hDH : D ≤ H) (hD : Odd (Nat.card D)) (hXD : X' ≤ normalizer (D : Set G)) :
    ⁅D, X'⁆ ≤ O H := by
  have hRn := bar_normal_of_sup hRF' hFR
  have hXH : X' ≤ H := hXR.trans hRH
  rw [← bar_eq_bot_iff (commutator_le_of_le hDH hXH), bar_commutator hDH hXH]
  have h1 : ⁅bar H D, bar H X'⁆ ≤ bar H D :=
    commutator_le_left_of_le_normalizer (bar_le_normalizer hXD)
  have h2 : ⁅bar H D, bar H X'⁆ ≤ bar H R :=
    (commutator_mono le_rfl (bar_mono hXR)).trans (commutator_le_right _ _)
  have h3 := inf_eq_bot_of_odd_of_isPGroup (odd_card_bar hD) (isPGroup_bar (H := H) hR)
  rw [eq_bot_iff, ← h3]
  exact le_inf h1 h2

theorem commutator_commutator_le_O (hRF' : bar H R ⊔ F = ⊤)
    (hFR : F ≤ centralizer (bar H R : Set (Bar H))) (hTL : bar H T ≤ ⁅F, F⁆)
    {Y' D : Subgroup G} (hYT : Y' ≤ T) (hTH : T ≤ H) (hDH : D ≤ H) (hD : Odd (Nat.card D))
    (hYD : Y' ≤ normalizer (D : Set G))
    (hcyc : ∀ K : Subgroup (Bar H), K ≤ ⁅F, F⁆ → Odd (Nat.card K) →
      bar H Y' ≤ normalizer (K : Set (Bar H)) → IsCyclic K) :
    ⁅⁅D, Y'⁆, ⁅D, Y'⁆⁆ ≤ O H := by
  have hLn := commutator_normal_of_sup hRF' hFR
  have hYH : Y' ≤ H := hYT.trans hTH
  have hDY : ⁅D, Y'⁆ ≤ H := commutator_le_of_le hDH hYH
  rw [← bar_eq_bot_iff (commutator_le_of_le hDY hDY), bar_commutator hDY hDY,
    bar_commutator hDH hYH]
  set K := ⁅bar H D, bar H Y'⁆ with hK
  have h1 : K ≤ bar H D := commutator_le_left_of_le_normalizer (bar_le_normalizer hYD)
  have h2 : K ≤ ⁅F, F⁆ :=
    (commutator_mono le_rfl ((bar_mono hYT).trans hTL)).trans (commutator_le_right _ _)
  have h3 : bar H Y' ≤ normalizer (K : Set (Bar H)) := le_normalizer_commutator_right _ _
  exact commutator_eq_bot_of_isCyclic (hcyc K h2 (odd_card_of_le h1 (odd_card_bar hD)) h3)

end Structure

end G4c

end CFSG.GH72
