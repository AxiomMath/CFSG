module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Derived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin

@[expose] def Lemma2_4_24_core : Prop :=
  Lin2Statement fun G _ _ T M H S L D n (_ : Lin2Cfg G T M H S L n D) => centerOf L = ⊥

section Aux

variable {G : Type*} [Group G]

theorem inf_centralizer_conj_eq {R Z : Subgroup G} {t s y : G} (hs : s ∈ R)
    (hy : s⁻¹ * t * s = y) (hZ : Z = R ⊓ Subgroup.centralizer ({t} : Set G))
    (hZc : Z ≤ centerOf R) : R ⊓ Subgroup.centralizer ({y} : Set G) = Z := by
  apply le_antisymm
  · rintro k ⟨hkR, hky⟩
    have hky' : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 hky
    have ht : t = s * y * s⁻¹ := by rw [← hy]; group
    have hk' : s * k * s⁻¹ ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine ⟨R.mul_mem (R.mul_mem hs hkR) (R.inv_mem hs),
        Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [ht]
      calc s * k * s⁻¹ * (s * y * s⁻¹) = s * (k * y) * s⁻¹ := by group
        _ = s * (y * k) * s⁻¹ := by rw [hky']
        _ = s * y * s⁻¹ * (s * k * s⁻¹) := by group
    have hk'Z : s * k * s⁻¹ ∈ Z := hZ ▸ hk'
    have hc := Subgroup.mem_centralizer_iff.1 (hZc hk'Z).2 s hs
    have h1 : s * (s * k * s⁻¹) = s * k := by rw [hc]; group
    have : s * k * s⁻¹ = k := mul_left_cancel h1
    rwa [this] at hk'Z
  · intro z hz
    have hzR : z ∈ R := (hZc hz).1
    have hzt : z * t = t * z :=
      Subgroup.mem_centralizer_singleton_iff.1 ((hZ ▸ hz : z ∈ R ⊓ _).2)
    have hzs : s * z = z * s := Subgroup.mem_centralizer_iff.1 (hZc hz).2 s hs
    have hz' : s⁻¹ * z * s = z := by
      rw [mul_assoc, ← hzs, ← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨hzR, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hy]
    calc z * (s⁻¹ * t * s) = (s⁻¹ * z * s) * (s⁻¹ * t * s) := by rw [hz']
      _ = s⁻¹ * (z * t) * s := by group
      _ = s⁻¹ * (t * z) * s := by rw [hzt]
      _ = (s⁻¹ * t * s) * (s⁻¹ * z * s) := by group
      _ = (s⁻¹ * t * s) * z := by rw [hz']

theorem le_normalizer_inf_centralizer {T Z : Subgroup G} (hTZ : T ≤ Subgroup.normalizer (Z : Set G)) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [← conjR_eq_self_iff, conjR_inf, conjR_eq_of_mem hg, ← conjR_centralizer,
    conjR_eq_of_mem_normalizer (hTZ hg)]

end Aux

section Parts

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem lemma2_4_24 (h8 : Lemma2_4_8) (h12 : Lemma2_4_12) (h14 : Lemma2_4_14)
    (h17 : Lemma2_4_17) (h22 : Lemma2_4_22) (hcore : Lemma2_4_24_core) : Lemma2_4_24 := by
  intro G _ _ T M H S L D n hcfg B hB Z hZ
  have hc : centerOf L = ⊥ := hcore G T M H S L D n hcfg
  obtain ⟨⟨hTS, -, hTnR⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨⟨hFcyc, -, -, -, -⟩, -⟩ := h12 G T M H S L D n hcfg B hB
  have hST : S ≤ T := hcfg.S_le_T
  have hRS : thompsonJ S ≤ S := thompsonJ_le_self S
  have hRNT : thompsonJ S ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) = T := hB.2.2.2.2.2.2.2.2.1
  have hRNT' : thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) = ⊥ :=
    hB.2.2.2.2.2.2.2.2.2.1
  have hZc : Z = centerOf (thompsonJ S) :=
    ((lin2Z_cases hZ).resolve_right fun h => h.1 hc).2
  have hTBR : T ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer (thompsonJ S : Set G) :=
    fun k hk => hTnR hk.1
  have hTBgen : ∀ y ∈ T ⊓ Subgroup.normalizer (B : Set G), y ∉ S →
      T ⊓ Subgroup.normalizer (B : Set G) =
        Subgroup.zpowers y ⊔ (S ⊓ Subgroup.normalizer (B : Set G)) := by
    intro y hy hyS
    apply le_antisymm
    · intro k hk
      by_cases hkS : k ∈ S
      · exact Subgroup.mem_sup_right ⟨hkS, hk.2⟩
      · have h1 : y⁻¹ * k ∈ S := inv_mul_mem_of_relIndex_two hTS hy.1 hk.1 hyS hkS
        have h2 : y⁻¹ * k ∈ T ⊓ Subgroup.normalizer (B : Set G) :=
          (T ⊓ Subgroup.normalizer (B : Set G)).mul_mem
            ((T ⊓ Subgroup.normalizer (B : Set G)).inv_mem hy) hk
        have e : k = y * (y⁻¹ * k) := by group
        rw [e]
        exact (Subgroup.zpowers y ⊔ (S ⊓ Subgroup.normalizer (B : Set G))).mul_mem
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers y))
          (Subgroup.mem_sup_right ⟨h1, h2.2⟩)
    · exact sup_le (Subgroup.zpowers_le.2 hy) fun k hk => ⟨hST hk.1, hk.2⟩
  obtain ⟨h17a, h17b⟩ := h17 G T M H S L D n hcfg Z hZ
  have hnc := (h22 G T M H S L D n hcfg).1
  rcases h17a with hCT | ⟨-, t₁, ht₁T, ht₁S, ht₁2, hCT, hZeq, hZC⟩
  · exfalso
    obtain ⟨t, htT, hTt⟩ := h17b hc
    rw [hCT] at hTt
    exact hnc ⟨t, htT, hTt⟩
  have hZRc : Z ≤ centerOf (thompsonJ S) := hZeq.le
  obtain ⟨r, hr, y, hy, ht₁y⟩ : ∃ r ∈ thompsonJ S, ∃ y ∈ T ⊓ Subgroup.normalizer (B : Set G),
      t₁ = r * y := by
    have h1 : t₁ ∈ thompsonJ S ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) := by
      rw [hRNT]; exact ht₁T
    exact (mem_sup_iff_of_le_normalizer hTBR).1 h1
  have hyeq : y = r⁻¹ * t₁ := by rw [ht₁y]; group
  have hyS : y ∉ S := fun hyS => ht₁S (by
    rw [ht₁y]; exact S.mul_mem (hRS hr) hyS)
  have hy2 : y ^ 2 = 1 := by
    have h1 : y ^ 2 = r⁻¹ * (t₁ * r⁻¹ * t₁⁻¹) * t₁ ^ 2 := by
      rw [hyeq]; simp only [pow_two]; group
    have h2 : y ^ 2 ∈ thompsonJ S := by
      rw [h1, ht₁2, mul_one]
      exact (thompsonJ S).mul_mem ((thompsonJ S).inv_mem hr)
        ((Subgroup.mem_normalizer_iff.1 (hTnR ht₁T) r⁻¹).1 ((thompsonJ S).inv_mem hr))
    have h3 : y ^ 2 ∈ T ⊓ Subgroup.normalizer (B : Set G) := pow_mem hy 2
    have : y ^ 2 ∈ thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) := ⟨h2, h3⟩
    rw [hRNT', Subgroup.mem_bot] at this
    exact this
  have hyn : y ∈ Subgroup.normalizer (thompsonJ S : Set G) := hTnR hy.1
  have hCTy : T ⊓ Subgroup.centralizer (Z : Set G) = thompsonJ S ⊔ Subgroup.zpowers y := by
    rw [hCT]
    apply le_antisymm
    · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
      rw [ht₁y]
      exact (thompsonJ S ⊔ Subgroup.zpowers y).mul_mem (Subgroup.mem_sup_left hr)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    · refine sup_le le_sup_left (Subgroup.zpowers_le.2 ?_)
      rw [hyeq]
      exact (thompsonJ S ⊔ Subgroup.zpowers t₁).mul_mem
        (Subgroup.mem_sup_left ((thompsonJ S).inv_mem hr))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₁))
  have hsq : t₁ ^ 2 ∈ thompsonJ S := by rw [ht₁2]; exact one_mem _
  obtain ⟨-, htrans, -⟩ := h14 G T M H S L D n hcfg t₁ ht₁T ht₁S hsq
  have ht₁y' : t₁⁻¹ * y ∈ thompsonJ S := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (inv_mem (hTnR ht₁T) : t₁⁻¹ ∈ _) r⁻¹).1
      ((thompsonJ S).inv_mem hr)
    have e : t₁⁻¹ * y = t₁⁻¹ * r⁻¹ * t₁⁻¹⁻¹ := by rw [hyeq]; group
    rw [e]; exact h1
  obtain ⟨s, hs, hsy⟩ := htrans t₁ y (by simp) ht₁y' ht₁2 hy2
  have hZy : thompsonJ S ⊓ Subgroup.centralizer ({y} : Set G) = Z :=
    inf_centralizer_conj_eq hs hsy hZC hZRc
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) := fun g hg => by
    rw [← conjR_eq_self_iff, hZc]
    exact centerOf_normalized (hTnR hg)
  have hTN := le_normalizer_inf_centralizer hTZ
  have hFC : S ⊓ Subgroup.normalizer (B : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfT : f ∈ T ⊓ Subgroup.normalizer (B : Set G) := ⟨hST hf.1, hf.2⟩
    have hfy : f * y * f⁻¹ ∈ T ⊓ Subgroup.centralizer (Z : Set G) := by
      refine (Subgroup.mem_normalizer_iff.1 (hTN hfT.1) y).1 ?_
      rw [hCTy]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    have hfyB : f * y * f⁻¹ ∈ T ⊓ Subgroup.normalizer (B : Set G) :=
      (T ⊓ Subgroup.normalizer (B : Set G)).mul_mem
        ((T ⊓ Subgroup.normalizer (B : Set G)).mul_mem hfT hy)
        ((T ⊓ Subgroup.normalizer (B : Set G)).inv_mem hfT)
    have hy1 : y ≠ 1 := fun h => hyS (by rw [h]; exact S.one_mem)
    rw [hCTy] at hfy
    rcases mem_sup_zpowers_of_sq_eq_one hyn hy2 hfy with h | ⟨r', hr', hr'e⟩
    · exfalso
      have : f * y * f⁻¹ ∈ thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) := ⟨h, hfyB⟩
      rw [hRNT', Subgroup.mem_bot] at this
      exact hy1 (conj_eq_one_iff.1 this)
    · have hr'B : r' ∈ T ⊓ Subgroup.normalizer (B : Set G) := by
        have e : r' = (f * y * f⁻¹) * y⁻¹ := by rw [hr'e]; group
        rw [e]
        exact (T ⊓ Subgroup.normalizer (B : Set G)).mul_mem hfyB
          ((T ⊓ Subgroup.normalizer (B : Set G)).inv_mem hy)
      have : r' ∈ thompsonJ S ⊓ (T ⊓ Subgroup.normalizer (B : Set G)) := ⟨hr', hr'B⟩
      rw [hRNT', Subgroup.mem_bot] at this
      rw [this, one_mul] at hr'e
      calc f * y = (f * y * f⁻¹) * f := by group
        _ = y * f := by rw [hr'e]
  refine ⟨⟨hRNT', hRNT⟩, hc, y, hy, hyS, hy2, hZy, hCTy.symm, hFcyc, hTBgen y hy hyS, ?_, hFC⟩
  rw [eq_bot_iff]
  rintro k ⟨hk1, hk2⟩
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk1
  rcases zpow_of_sq_eq_one hy2 j with h | h
  · rw [h]; exact one_mem _
  · exact absurd (h ▸ hk2.1) hyS

end Parts

end CFSG.QuasithinUnique.Lin2
