module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step110Base
public import CFSG.LocalAnalysis.ComponentClassification.AS81Inputs

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

section Quot

variable {K : Type} [Group K] {z : K}

omit [Group K] in
theorem zpowers_normal_of_mem_center [Group K] (hz : z ∈ center K) : (zpowers z).Normal := by
  refine ⟨fun c hc g => ?_⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
  have h1 : g * z * g⁻¹ = z := by
    rw [mem_center_iff.mp hz g]
    group
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h1]
  exact zpow_mem (mem_zpowers z) k

variable [(zpowers z).Normal]

noncomputable abbrev barMap (z : K) [(zpowers z).Normal] : K →* K ⧸ zpowers z :=
  QuotientGroup.mk' (zpowers z)

omit [Group K] in
theorem barMap_surjective [Group K] (z : K) [(zpowers z).Normal] :
    Function.Surjective (barMap z) :=
  QuotientGroup.mk'_surjective _

theorem ker_barMap : (barMap z).ker = zpowers z := QuotientGroup.ker_mk' _

theorem comap_map_barMap {H : Subgroup K} (hzH : z ∈ H) :
    (H.map (barMap z)).comap (barMap z) = H := by
  rw [comap_map_eq, ker_barMap, sup_eq_left.mpr (zpowers_le.mpr hzH)]

theorem map_comap_barMap (H : Subgroup (K ⧸ zpowers z)) :
    (H.comap (barMap z)).map (barMap z) = H :=
  map_comap_eq_self_of_surjective (barMap_surjective z) H

theorem card_comap_barMap [Finite K] (H : Subgroup (K ⧸ zpowers z)) :
    Nat.card (H.comap (barMap z)) = Nat.card (zpowers z) * Nat.card H := by
  have h1 := card_mul_index (H.comap (barMap z))
  have h2 := card_mul_index H
  rw [index_comap_of_surjective H (barMap_surjective z)] at h1
  have h3 := card_eq_card_quotient_mul_card_subgroup (zpowers z)
  have hpos : 0 < H.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have : Nat.card (H.comap (barMap z)) * H.index =
      Nat.card (zpowers z) * Nat.card H * H.index := by
    rw [h1, h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem map_rightConjugate_barMap (H : Subgroup K) (g : K) :
    (rightConjugate H g).map (barMap z) = rightConjugate (H.map (barMap z)) (barMap z g) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : g * y * g⁻¹ ∈ H := (mem_rightConjugate_iff H g y).mp hy
    rw [mem_rightConjugate_iff]
    exact ⟨_, hy', by simp [map_mul, map_inv]⟩
  · intro hx
    rw [mem_rightConjugate_iff] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    refine ⟨g⁻¹ * y * g, (mem_rightConjugate_iff H g _).mpr (by simpa [mul_assoc] using hy), ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group

theorem comap_rightConjugate_barMap (H : Subgroup (K ⧸ zpowers z)) (g : K) :
    (rightConjugate H (barMap z g)).comap (barMap z) = rightConjugate (H.comap (barMap z)) g := by
  ext x
  rw [mem_comap, mem_rightConjugate_iff, mem_rightConjugate_iff, mem_comap, map_mul, map_mul,
    map_inv]

theorem comap_normalizer_barMap (H : Subgroup (K ⧸ zpowers z)) :
    (normalizer (H : Set (K ⧸ zpowers z))).comap (barMap z) =
      normalizer ((H.comap (barMap z) : Subgroup K) : Set K) :=
  comap_normalizer_eq_of_surjective H (barMap_surjective z)

end Quot

section Hyp

variable {K : Type} [Group K] [Finite K] {z : K} {X T : Subgroup K}

structure Hyp19K (K : Type) [Group K] [Finite K] (z : K) (X T : Subgroup K) : Prop where
  center : z ∈ center K
  extra : ExtraIn X z
  sylowT : IsSylowOf 2 T ⊤
  le_T : X ≤ T
  weak : ∀ h : K, rightConjugate X h ≤ T → rightConjugate X h = X
  rank : ∀ h : K, 1 < Open.pRank 2 (X ⊓ rightConjugate X h) → rightConjugate X h = X

variable (hH : Hyp19K K z X T) [(zpowers z).Normal]
include hH

theorem Hyp19K.isElemAbelian_map : IsElemAbelian 2 (X.map (barMap z)) := by
  have hker : ∀ c ∈ zpowers z, barMap z c = 1 := fun c hc =>
    (MonoidHom.mem_ker).mp (by rw [ker_barMap]; exact hc)
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun q hq => ?_⟩
  · obtain ⟨x₁, hx₁, ha⟩ := a.2
    obtain ⟨x₂, hx₂, hb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← ha, ← hb, ← map_mul]
    have h1 := hker _ (hH.extra.commutator_mem hx₁ hx₂)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc barMap z x₁ * barMap z x₂ =
        barMap z x₁ * barMap z x₂ * (barMap z x₁)⁻¹ * (barMap z x₂)⁻¹ *
          (barMap z x₂ * barMap z x₁) := by group
      _ = barMap z x₂ * barMap z x₁ := by rw [h1, one_mul]
  · obtain ⟨x, hx, rfl⟩ := hq
    rw [← map_pow]
    exact hker _ (hH.extra.sq_mem hx)

theorem Hyp19K.isSylowOf_map : IsSylowOf 2 (T.map (barMap z)) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hH.sylowT
  rw [isSylowOf_iff] at h ⊢
  refine ⟨le_top, h.2.1.map _, fun h2 => h.2.2 ?_⟩
  rw [relIndex_top_right] at h2 ⊢
  exact h2.trans (index_map_dvd T (barMap_surjective z))

theorem Hyp19K.weak_map (h : K ⧸ zpowers z)
    (hle : rightConjugate (X.map (barMap z)) h ≤ T.map (barMap z)) :
    rightConjugate (X.map (barMap z)) h = X.map (barMap z) := by
  obtain ⟨h, rfl⟩ := barMap_surjective z h
  rw [← map_rightConjugate_barMap] at hle ⊢
  have hzT : z ∈ T := hH.le_T hH.extra.mem
  have h1 : rightConjugate X h ≤ T := by
    rw [← comap_map_barMap hzT]
    exact map_le_iff_le_comap.mp hle
  rw [hH.weak h h1]

theorem Hyp19K.not_strongly_map {x h : K} (hx : x ∈ X) (hT : h⁻¹ * x * h ∈ T)
    (hX : h⁻¹ * x * h ∉ X) :
    ∃ x' ∈ X.map (barMap z), ∃ h' : K ⧸ zpowers z, h'⁻¹ * x' * h' ∈ T.map (barMap z) ∧
      h'⁻¹ * x' * h' ∉ X.map (barMap z) := by
  refine ⟨barMap z x, ⟨x, hx, rfl⟩, barMap z h, ⟨_, hT, by simp [map_mul, map_inv]⟩, ?_⟩
  intro hmem
  apply hX
  rw [← comap_map_barMap hH.extra.mem, mem_comap]
  simpa [map_mul, map_inv] using hmem

theorem Hyp19K.exists_tim77 (hT : Tim77Lemma24) {x h : K} (hx : x ∈ X)
    (hxT : h⁻¹ * x * h ∈ T) (hxX : h⁻¹ * x * h ∉ X) :
    ∃ g : K, Tim77Facts (X.map (barMap z)) (barMap z g) := by
  obtain ⟨h', hh'⟩ := hT (K ⧸ zpowers z) (T.map (barMap z)) (X.map (barMap z))
    hH.isSylowOf_map (map_mono hH.le_T) hH.isElemAbelian_map hH.weak_map
    (hH.not_strongly_map hx hxT hxX)
  obtain ⟨g, rfl⟩ := barMap_surjective z h'
  exact ⟨g, hh'⟩

end Hyp

section Config

variable {K : Type} [Group K] [Finite K] {z : K} [(zpowers z).Normal] {X : Subgroup K} {g : K}

omit [Finite K] in
theorem comap_map_barMap_rightConjugate (hzX : z ∈ X) :
    (rightConjugate (X.map (barMap z)) (barMap z g)).comap (barMap z) = rightConjugate X g := by
  rw [comap_rightConjugate_barMap, comap_map_barMap hzX]

omit [Finite K] [(zpowers z).Normal] in
theorem mem_rightConjugate_of_center (hz : z ∈ center K) (hzX : z ∈ X) :
    z ∈ rightConjugate X g := by
  rw [mem_rightConjugate_iff, show g * z * g⁻¹ = z by rw [mem_center_iff.mp hz g]; group]
  exact hzX

omit [Finite K] in
theorem comap_tim77I (hzX : z ∈ X) :
    (tim77I (X.map (barMap z)) (barMap z g)).comap (barMap z) = tim77I X g := by
  rw [tim77I, comap_inf, comap_map_barMap hzX, comap_map_barMap_rightConjugate hzX]

omit [Finite K] in
theorem comap_tim77B (hzX : z ∈ X) :
    (tim77B (X.map (barMap z)) (barMap z g)).comap (barMap z) = tim77B X g := by
  rw [tim77B, comap_inf, comap_map_barMap hzX, comap_normalizer_barMap,
    comap_map_barMap_rightConjugate hzX]

omit [Finite K] in
theorem comap_tim77D (hzX : z ∈ X) :
    (tim77D (X.map (barMap z)) (barMap z g)).comap (barMap z) = tim77D X g := by
  rw [tim77D, comap_inf, comap_normalizer_barMap, comap_map_barMap hzX,
    comap_map_barMap_rightConjugate hzX]

omit [Finite K] in
theorem comap_tim77M (hzX : z ∈ X) :
    (tim77M (X.map (barMap z)) (barMap z g)).comap (barMap z) = tim77M X g := by
  rw [tim77M, ← comap_sup_eq _ _ _ (barMap_surjective z), comap_tim77B hzX,
    comap_tim77D hzX]

omit [Finite K] in
theorem comap_tim77L (hzX : z ∈ X) :
    (tim77L (X.map (barMap z)) (barMap z g)).comap (barMap z) = tim77L X g := by
  rw [tim77L, ← comap_sup_eq _ _ _ (barMap_surjective z), comap_map_barMap hzX,
    comap_map_barMap_rightConjugate hzX]

structure Config111 (z : K) (X : Subgroup K) (g : K) : Prop where
  elem : ∀ a ∈ tim77M X g, ∀ b ∈ tim77M X g, a * b * a⁻¹ * b⁻¹ ∈ tim77I X g ∧ a * a ∈ tim77I X g
  normal : tim77L X g ≤ normalizer (tim77M X g : Set K)
  lt_D : tim77I X g < tim77D X g
  center : ∀ i ∈ tim77I X g, ∀ l ∈ tim77L X g, i * l * i⁻¹ * l⁻¹ ∈ zpowers z

omit [Finite K] in
theorem Tim77Facts.config111 (hzX : z ∈ X)
    (hC : Tim77Facts (X.map (barMap z)) (barMap z g)) : Config111 z X g where
  elem a ha b hb := by
    rw [← comap_tim77M hzX] at ha hb
    rw [← comap_tim77I hzX, mem_comap, mem_comap]
    obtain ⟨h1, h2⟩ := hC.elem _ ha _ hb
    refine ⟨?_, ?_⟩
    · simpa [map_mul, map_inv] using h1
    · simpa [map_mul] using h2
  normal := by
    rw [← comap_tim77L hzX, ← comap_tim77M hzX, ← comap_normalizer_barMap]
    exact comap_mono hC.normal
  lt_D := by
    rw [← comap_tim77I hzX, ← comap_tim77D hzX]
    refine lt_of_le_of_ne (comap_mono hC.lt_D.le) fun h => hC.lt_D.ne ?_
    rw [← map_comap_barMap (tim77I _ _), h, map_comap_barMap]
  center i hi l hl := by
    rw [← comap_tim77I hzX] at hi
    rw [← comap_tim77L hzX] at hl
    have h := mem_centralizer_iff.mp (hC.le_center hi) _ hl
    rw [← ker_barMap, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    rw [← h]
    group

end Config

section Tim77Gen

variable {H : Type} [Group H] {Q : Subgroup H} {h : H}

omit [Group H] in
theorem tim77D_le_normalizer_B [Group H] (Q : Subgroup H) (h : H) :
    tim77D Q h ≤ normalizer (tim77B Q h : Set H) := by
  intro d hd
  have h1 : d ∈ normalizer (Q : Set H) := hd.2
  have h2 : d ∈ normalizer (normalizer (rightConjugate Q h : Set H) : Set H) :=
    le_normalizer (le_normalizer hd.1)
  rw [mem_normalizer_iff] at h1 h2 ⊢
  intro x
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩, fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

omit [Group H] in
theorem inf_tim77M [Group H] (Q : Subgroup H) (h : H) : Q ⊓ tim77M Q h = tim77B Q h := by
  refine le_antisymm (fun m hm => ?_) (le_inf inf_le_left le_sup_left)
  obtain ⟨hmQ, hmM⟩ := hm
  have hcoe := coe_mul_of_right_le_normalizer_left (tim77B Q h) (tim77D Q h)
    (tim77D_le_normalizer_B Q h)
  have : m ∈ ((tim77B Q h ⊔ tim77D Q h : Subgroup H) : Set H) := hmM
  rw [hcoe] at this
  obtain ⟨b, hb, d, hd, rfl⟩ := this
  have hdQ : d ∈ Q := by
    have := Q.mul_mem (Q.inv_mem hb.1) hmQ
    simpa using this
  have hdB : d ∈ tim77B Q h := ⟨hdQ, le_normalizer hd.1⟩
  exact (tim77B Q h).mul_mem hb hdB

end Tim77Gen

end CFSG.ComponentClassification.AS81
