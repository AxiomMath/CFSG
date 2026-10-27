module

public import CFSG.ClassicalInvolution.Asc77.AscSix66Norm

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem commutes_of_commutator_le_oddCoreOf {A B J : Subgroup G} (hBJ : B ≤ J)
    (h : ⁅A, J⁆ ≤ oddCoreOf J) (hAB : IsPGroup 2 ↥(A ⊔ B)) : Commutes A B := by
  intro a ha b hb
  have h1 : ⁅a, b⁆ ∈ oddCoreOf J := h (Subgroup.commutator_mem_commutator ha (hBJ hb))
  have ha' : a ∈ A ⊔ B := Subgroup.mem_sup_left ha
  have hb' : b ∈ A ⊔ B := Subgroup.mem_sup_right hb
  have h2 : ⁅a, b⁆ ∈ A ⊔ B := by
    rw [commutatorElement_def]
    exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem ha' hb') ((A ⊔ B).inv_mem ha'))
      ((A ⊔ B).inv_mem hb')
  have h3 : IsPGroup 2 (Subgroup.zpowers ⁅a, b⁆) := hAB.to_le (Subgroup.zpowers_le.mpr h2)
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard J) h1 h3)

theorem claim_not_normalizes (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {K J A B : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (hAK : IsSylow2In A K) (hBJ : IsSylow2In B J) (hA : A ∈ RSet Ω) (hB : B ∈ RSet Ω)
    (hKJ : K ≠ J) (hAB : IsPGroup 2 ↥(A ⊔ B)) (hnc : ¬ Commutes A B) {a b : G}
    (ha : IsUniqueInvolution K a) (hb : IsUniqueInvolution J b)
    (hbY : ∀ α ∈ A, ∀ y ∈ B, (b⁻¹ * α⁻¹ * b * α) * y = y * (b⁻¹ * α⁻¹ * b * α)) :
    conjSub b A ≠ A := by
  intro hbA
  have hAq := hΩ.isQuatSub_of_mem_RSet hp hA
  have hBq := hΩ.isQuatSub_of_mem_RSet hp hB
  have hA2 : IsPGroup 2 ↥A := hAK.2.1
  have hB2 : IsPGroup 2 ↥B := hBJ.2.1
  have ha2 : orderOf a = 2 := ConnectedA2.orderOf_eq_two_of_isUniqueInvolution ha
  have hb2 : orderOf b = 2 := ConnectedA2.orderOf_eq_two_of_isUniqueInvolution hb
  have haA : a ∈ A :=
    mem_of_isUniqueInvolution_of_isPGroup ha hAK.1 hA2 (by have := hAq.eight_le; omega)
  have hbB : b ∈ B :=
    mem_of_isUniqueInvolution_of_isPGroup hb hBJ.1 hB2 (by have := hBq.eight_le; omega)
  have hab : a ≠ b := by
    intro hab
    apply hnc
    exact hΩ.commutes_of_twin_of_isPGroup hK hJ hKJ ha (hab ▸ hb) hAK.1 hBJ.1 hAB
  have hKJt : K ∉ twinSet Ω J := by
    rintro ⟨-, z, hzJ, hzK⟩
    exact hab ((ha.eq hzK).trans (hb.eq hzJ).symm)
  have hJKt : J ∉ twinSet Ω K := by
    rintro ⟨-, z, hzK, hzJ⟩
    exact hab ((ha.eq hzK).trans (hb.eq hzJ).symm)
  have hnormA : ∀ α ∈ A, b⁻¹ * α⁻¹ * b ∈ A := by
    intro α hα
    have h1 : conjSub b⁻¹ A = A := by
      calc conjSub b⁻¹ A = conjSub b⁻¹ (conjSub b A) := by rw [hbA]
        _ = A := conjSub_inv_conjSub b A
    have h2 : b⁻¹ * α⁻¹ * b⁻¹⁻¹ ∈ conjSub b⁻¹ A := conj_mem_conjSub (A.inv_mem hα)
    rw [h1, inv_inv] at h2
    exact h2
  have hcA : ∀ α ∈ A, b⁻¹ * α⁻¹ * b * α ∈ A := fun α hα => A.mul_mem (hnormA α hα) hα
  by_cases hall : ∀ α ∈ A, b⁻¹ * α⁻¹ * b * α = 1
  ·
    have hAc : A ≤ Subgroup.centralizer ({b} : Set G) := by
      intro α hα
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : α⁻¹ * b * α = b := by
        calc α⁻¹ * b * α = b * (b⁻¹ * α⁻¹ * b * α) := by group
          _ = b := by rw [hall α hα, mul_one]
      have h2 : b * α = α * b := by
        calc b * α = α * (α⁻¹ * b * α) := by group
          _ = α * b := by rw [h1]
      exact h2.symm
    have hSyl : IsSylow2In A (K ⊓ Subgroup.centralizer ({b} : Set G)) :=
      ⟨le_inf hAK.1 hAc, hA2, fun V hV hV2 hAV => hAK.2.2 V (hV.trans inf_le_left) hV2 hAV⟩
    rcases h62 hp hq G Ω hΩ J hJ b hb K hK hKJt a ha A hSyl haA with h | h | h | h
    · have h8 := hAq.eight_le
      rw [h.1, Nat.card_zpowers, ha2] at h8
      omega
    · have h8 := hAq.eight_le
      rw [h.1, Nat.card_zpowers, ha2] at h8
      omega
    · obtain ⟨R, -, J', -, -, -, hcyc, -, -⟩ := hΩ.exists_data_of_mem_USet hp h.1
      obtain ⟨x, hx, y, hy, hxy⟩ := hAq.exists_not_commute
      exact hxy (commute_of_isCyclic hcyc hx hy)
    · exact hnc (commutes_of_commutator_le_oddCoreOf hBJ.1 h.2 hAB)
  ·
    push Not at hall
    obtain ⟨α, hα, hne⟩ := hall
    set c : G := b⁻¹ * α⁻¹ * b * α with hc
    have hcA : c ∈ A := hcA α hα
    have hzcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
    have hzc2 : IsPGroup 2 ↥(Subgroup.zpowers c) := hA2.to_le hzcA
    have hcard : 2 ≤ Nat.card (Subgroup.zpowers c) := by
      rw [Nat.card_zpowers]
      have h1 : orderOf c ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf c := orderOf_pos c
      omega
    have haz : a ∈ Subgroup.zpowers c :=
      mem_of_isUniqueInvolution_of_isPGroup ha (hzcA.trans hAK.1) hzc2 hcard
    have hBc : B ≤ Subgroup.centralizer ({a} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haz
      have hcy : Commute c y := hbY α hα y hy
      have : Commute a y := hk ▸ Commute.zpow_left hcy k
      exact this.symm.eq
    have hSyl : IsSylow2In B (J ⊓ Subgroup.centralizer ({a} : Set G)) :=
      ⟨le_inf hBJ.1 hBc, hB2, fun V hV hV2 hBV => hBJ.2.2 V (hV.trans inf_le_left) hV2 hBV⟩
    rcases h62 hp hq G Ω hΩ K hK a ha J hJ hJKt b hb B hSyl hbB with h | h | h | h
    · have h8 := hBq.eight_le
      rw [h.1, Nat.card_zpowers, hb2] at h8
      omega
    · have h8 := hBq.eight_le
      rw [h.1, Nat.card_zpowers, hb2] at h8
      omega
    · obtain ⟨R, -, J', -, -, -, hcyc, -, -⟩ := hΩ.exists_data_of_mem_USet hp h.1
      obtain ⟨x, hx, y, hy, hxy⟩ := hBq.exists_not_commute
      exact hxy (commute_of_isCyclic hcyc hx hy)
    · exact hnc (commutes_of_commutator_le_oddCoreOf hAK.1 h.2 (sup_comm B A ▸ hAB)).symm

theorem card_biSup_conj_lt {S C : Subgroup G} (hS : IsPGroup 2 S) (hC : C < S) :
    (⨆ s ∈ S, conjSub s C) ≤ S ∧ Nat.card ↥(⨆ s ∈ S, conjSub s C) < Nat.card S := by
  obtain ⟨M, hCM, hMS, hMinv⟩ := exists_normal_lt_of_lt hS hC
  have hXM : (⨆ s ∈ S, conjSub s C) ≤ M := by
    refine iSup₂_le fun s hs x hx => ?_
    rw [mem_conjSub_iff] at hx
    have h1 : s⁻¹ * x * s ∈ M := hCM hx
    have h2 := hMinv s hs _ h1
    simpa [mul_assoc] using h2
  refine ⟨hXM.trans hMS.le, ?_⟩
  have h1 := Subgroup.card_le_of_le hXM
  have h2 : Nat.card M < Nat.card S := by
    by_contra hge
    exact hMS.ne (Subgroup.eq_of_le_of_card_ge hMS.le (not_lt.mp hge))
  omega

theorem orbit_commutes (hΩ : HypOmegaMod p f Ω) {n : ℕ}
    (ih : ∀ m < n, ∀ S' : Subgroup G, Nat.card S' = m → IsPGroup 2 S' →
      ∀ Δ : Set (Subgroup G), (∀ A ∈ Δ, A ≤ S') → (∀ A ∈ Δ, ∀ s ∈ S', conjSub s A ∈ Δ) →
        Δ ⊆ RSet Ω → ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B)
    {S C : Subgroup G} (hSn : Nat.card S = n) (hS : IsPGroup 2 S) (hC : C < S)
    (hCR : C ∈ RSet Ω) :
    ∀ C₁ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C},
      ∀ C₂ ∈ {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C}, C₁ ≠ C₂ → Commutes C₁ C₂ := by
  obtain ⟨hXS, hXlt⟩ := card_biSup_conj_lt hS hC
  refine ih _ (hSn ▸ hXlt) (⨆ s ∈ S, conjSub s C) rfl (hS.to_le hXS)
    {C' : Subgroup G | ∃ s ∈ S, C' = conjSub s C} ?_ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact le_iSup₂_of_le s hs le_rfl
  · rintro _ ⟨s, hs, rfl⟩ x hx
    exact ⟨x * s, S.mul_mem (hXS hx) hs, conjSub_mul x s C ▸ rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact RSet.conj hΩ.conjInvariant hCR s

theorem l6_6i_main (h62 : L6_2 p f) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) :
    ∀ n : ℕ, ∀ S : Subgroup G, Nat.card S = n → IsPGroup 2 S → ∀ Δ : Set (Subgroup G),
      (∀ A ∈ Δ, A ≤ S) → (∀ A ∈ Δ, ∀ s ∈ S, conjSub s A ∈ Δ) → Δ ⊆ RSet Ω →
        ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commutes A B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hSn hS Δ hΔS hΔinv hΔR A hA B hB hne
  by_contra hnc
  have hAR := hΔR hA
  have hBR := hΔR hB
  obtain ⟨K, hK, hAK⟩ := exists_isSylow2In_of_mem_RSet hAR
  obtain ⟨J, hJ, hBJ⟩ := exists_isSylow2In_of_mem_RSet hBR
  have hAq := hΩ.isQuatSub_of_mem_RSet hp hAR
  have hBq := hΩ.isQuatSub_of_mem_RSet hp hBR
  have hAS : A ≤ S := hΔS A hA
  have hBS : B ≤ S := hΔS B hB
  have hS' : ∀ P : Subgroup G, IsPGroup 2 ↥(P ⊓ S) := fun P => hS.to_inf_right
  have hKJ : K ≠ J := by
    rintro rfl
    have h1 : K ⊓ S = A := hAK.eq_of_le (hS' K) inf_le_left (le_inf hAK.1 hAS)
    have h2 : K ⊓ S = B := hBJ.eq_of_le (hS' K) inf_le_left (le_inf hBJ.1 hBS)
    exact hne (h1.symm.trans h2)
  obtain ⟨a, ha⟩ := hΩ.exists_uniqueInvolution hp hq hK
  obtain ⟨b, hb⟩ := hΩ.exists_uniqueInvolution hp hq hJ
  have hbB : b ∈ B :=
    mem_of_isUniqueInvolution_of_isPGroup hb hBJ.1 hBJ.2.1 (by have := hBq.eight_le; omega)
  have hAltS : A < S := by
    refine lt_of_le_of_ne hAS ?_
    intro hAeq
    have hBA : B ≤ A := hAeq ▸ hBS
    exact hKJ (hΩ.eq_of_le_of_le hK hJ hBJ.2.1 (by have := hBq.eight_le; omega)
      (hBA.trans hAK.1) hBJ.1)
  have hBltS : B < S := by
    refine lt_of_le_of_ne hBS ?_
    intro hBeq
    have hAB : A ≤ B := hBeq ▸ hAS
    exact hKJ (hΩ.eq_of_le_of_le hK hJ hAK.2.1 (by have := hAq.eight_le; omega)
      hAK.1 (hAB.trans hBJ.1))
  have hXcomm := orbit_commutes hΩ ih hSn hS hAltS hAR
  have hYcomm := orbit_commutes hΩ ih hSn hS hBltS hBR
  set Y : Subgroup G := ⨆ s ∈ S, conjSub s B with hY
  have hBY : B ≤ Y := le_iSup₂_of_le (1 : G) S.one_mem (conjSub_one B).ge
  have hYinv : ∀ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := fun s hs y hy =>
    conjSub_biSup_conj_le hs (conj_mem_conjSub hy)
  have hbcY : ∀ y ∈ Y, b * y = y * b := by
    have hle : Y ≤ Subgroup.centralizer ({b} : Set G) := by
      refine iSup₂_le fun s hs y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hsB : conjSub s B = B
      · have hyB : y ∈ B := hsB ▸ hy
        exact (hb.commute_of_mem (hBJ.1 hyB)).symm
      · exact (hYcomm B ⟨1, S.one_mem, (conjSub_one B).symm⟩ (conjSub s B) ⟨s, hs, rfl⟩
          (Ne.symm hsB) b hbB y hy).symm
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  have hbY : ∀ α ∈ A, ∀ y ∈ B, (b⁻¹ * α⁻¹ * b * α) * y = y * (b⁻¹ * α⁻¹ * b * α) := by
    intro α hα y hy
    have hyY : y ∈ Y := hBY hy
    have ht : α * y * α⁻¹ ∈ Y := hYinv α (hAS hα) y hyY
    have hbt : b * (α * y * α⁻¹) = (α * y * α⁻¹) * b := hbcY _ ht
    have hby : b⁻¹ * y = y * b⁻¹ := by
      have := hbcY y hyY
      calc b⁻¹ * y = b⁻¹ * (y * b) * b⁻¹ := by group
        _ = b⁻¹ * (b * y) * b⁻¹ := by rw [this]
        _ = y * b⁻¹ := by group
    calc (b⁻¹ * α⁻¹ * b * α) * y = b⁻¹ * α⁻¹ * (b * (α * y * α⁻¹)) * α := by group
      _ = b⁻¹ * α⁻¹ * ((α * y * α⁻¹) * b) * α := by rw [hbt]
      _ = (b⁻¹ * y) * (α⁻¹ * b * α) := by group
      _ = (y * b⁻¹) * (α⁻¹ * b * α) := by rw [hby]
      _ = y * (b⁻¹ * α⁻¹ * b * α) := by group
  have hbn : conjSub b A ≠ A :=
    claim_not_normalizes h62 hp hq hΩ hK hJ hAK hBJ hAR hBR hKJ
      (hS.to_le (sup_le hAS hBS)) hnc ha hb hbY
  have hreg : ∀ g ∈ B, conjSub g A = A → g = 1 := by
    intro g hg hgA
    by_contra hg1
    have hzgB : Subgroup.zpowers g ≤ B := Subgroup.zpowers_le.mpr hg
    have hz2 : IsPGroup 2 ↥(Subgroup.zpowers g) := hBJ.2.1.to_le hzgB
    have hcard : 2 ≤ Nat.card (Subgroup.zpowers g) := by
      rw [Nat.card_zpowers]
      have h1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
      have h0 : 0 < orderOf g := orderOf_pos g
      omega
    have hbg : b ∈ Subgroup.zpowers g :=
      mem_of_isUniqueInvolution_of_isPGroup hb (hzgB.trans hBJ.1) hz2 hcard
    have hgN : g ∈ Subgroup.normalizer (A : Set G) := mem_normalizer_iff_conjSub_eq.mpr hgA
    have hbN : b ∈ Subgroup.normalizer (A : Set G) := (Subgroup.zpowers_le.mpr hgN) hbg
    exact hbn (mem_normalizer_iff_conjSub_eq.mp hbN)
  have hinj : ∀ g ∈ B, ∀ h ∈ B, conjSub g A = conjSub h A → g = h := by
    intro g hg h hh hgh
    have h1 : conjSub (h⁻¹ * g) A = A := by
      rw [conjSub_mul, hgh, conjSub_inv_conjSub]
    have := hreg (h⁻¹ * g) (B.mul_mem (B.inv_mem hh) hg) h1
    exact (inv_mul_eq_one.mp this).symm
  set X : Subgroup G := ⨆ s ∈ S, conjSub s A with hX
  have hXS : X ≤ S := (card_biSup_conj_lt hS hAltS).1
  have hXinv : ∀ s ∈ S, ∀ g ∈ X, s⁻¹ * g * s ∈ X := by
    intro s hs g hg
    have h2 := conjSub_biSup_conj_le (S := S) (A := A) (S.inv_mem hs) (conj_mem_conjSub hg)
    simpa using h2
  have hXN : ∀ g ∈ X, conjSub g A = A := by
    have hle : X ≤ Subgroup.normalizer (A : Set G) := by
      refine iSup₂_le fun s hs g hg => ?_
      by_cases hsA : conjSub s A = A
      · exact Subgroup.le_normalizer (hsA ▸ hg)
      · have hc : Commutes (conjSub s A) A :=
          hXcomm _ ⟨s, hs, rfl⟩ A ⟨1, S.one_mem, (conjSub_one A).symm⟩ hsA
        exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hg hc)
    intro g hg
    exact mem_normalizer_iff_conjSub_eq.mp (hle hg)
  have hAX : ∀ g ∈ B, conjSub g A ≤ X := fun g hg => le_iSup₂_of_le g (hBS hg) le_rfl
  have hcommorbit : ∀ g ∈ B, ∀ h ∈ B, g ≠ h → Commutes (conjSub g A) (conjSub h A) := by
    intro g hg h hh hgh
    exact hXcomm _ ⟨g, hBS hg, rfl⟩ _ ⟨h, hBS hh, rfl⟩ (fun e => hgh (hinj g hg h hh e))
  obtain ⟨x, hxB, hxord⟩ := hBq.exists_orderOf_four
  obtain ⟨u, huA, huord⟩ := hAq.exists_orderOf_four
  exact norm_contradiction hΩ hJ hBJ hS hBS hXS hAq hBq hXinv hXN hAX hinj hcommorbit hxB hxord
    huA huord

variable (p f)

theorem l6_6i (h62 : L6_2 p f) : L6_6i p f := by
  intro hp hq G _ _ Ω hΩ S hS Δ hΔS hΔinv hR A hA B hB hne
  exact l6_6i_main h62 hp hq hΩ _ S rfl hS Δ hΔS hΔinv hR A hA B hB hne

end CFSG.ClassicalInvolution.Asc77
