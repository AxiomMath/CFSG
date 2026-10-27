module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTr

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

theorem transvection_mul_self {V : Type} [CommGroup V] (hV : ∀ v : V, v * v = 1)
    {τ : MulAut V} (hτ : IsTransvection τ) : τ * τ = 1 := by
  obtain ⟨-, hcard⟩ := hτ
  set C := Subgroup.closure (Set.range fun v : V => τ v * v⁻¹) with hC
  have hmem : ∀ v, τ v * v⁻¹ ∈ C := fun v => Subgroup.subset_closure ⟨v, rfl⟩
  obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : C)).1 hcard
  have hfix : ∀ v, τ (τ v * v⁻¹) = τ v * v⁻¹ := by
    intro v
    set w := τ v * v⁻¹ with hw
    by_contra hne
    have hw1 : w ≠ 1 := by
      intro h
      apply hne
      rw [h, map_one]
    have hfw : τ w * w⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.mp h)
    have h1 : (⟨w, hmem v⟩ : C) = z := hz _ fun h => hw1 (congrArg Subtype.val h)
    have h2 : (⟨τ w * w⁻¹, hmem w⟩ : C) = z := hz _ fun h => hfw (congrArg Subtype.val h)
    have hww : τ w * w⁻¹ = w := congrArg Subtype.val (h2.trans h1.symm)
    have hτw : τ w = 1 := by
      have e : τ w = w * w := by
        calc τ w = τ w * w⁻¹ * w := by group
          _ = w * w := by rw [hww]
      rw [e, hV]
    exact hw1 (τ.injective (hτw.trans (map_one τ).symm))
  refine MulEquiv.ext fun v => ?_
  rw [MulAut.mul_apply, MulAut.one_apply]
  have h1 : τ v = τ v * v⁻¹ * v := by group
  have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV v)
  calc τ (τ v) = τ (τ v * v⁻¹ * v) := by rw [← h1]
    _ = τ v * v⁻¹ * τ v := by rw [map_mul, hfix v]
    _ = τ v * τ v * v⁻¹ := mul_right_comm _ _ _
    _ = v := by rw [hV, one_mul, hvv]

section Index

variable {G : Type*} [Group G] {K X : Subgroup G}

theorem conj_mem (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) {k g : G} (hk : k ∈ K)
    (hg : g ∈ X) : g * k * g⁻¹ ∈ K := by
  have h := hKn.conj_mem ⟨k, hKX hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  exact h

variable {τ : G}

theorem mem_or_mul_mem (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) (hτX : τ ∈ X)
    (hττ : τ * τ = 1) (hX : X = K ⊔ zpowers τ) {g : G} (hg : g ∈ X) : g ∈ K ∨ g * τ ∈ K := by
  have hc : ∀ {k : G}, k ∈ K → τ⁻¹ * k * τ⁻¹⁻¹ ∈ K := fun hk =>
    conj_mem hKX hKn hk (X.inv_mem hτX)
  let L : Subgroup G :=
    { carrier := {g | g ∈ K ∨ g * τ ∈ K}
      one_mem' := Or.inl K.one_mem
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (K.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact K.mul_mem ha hb)
        · refine Or.inr ?_
          have h := K.mul_mem ha (hc hb)
          rwa [show a * τ * (τ⁻¹ * b * τ⁻¹⁻¹) = a * b * τ by group] at h
        · refine Or.inl ?_
          have h := K.mul_mem ha (hc hb)
          rwa [show a * τ * (τ⁻¹ * (b * τ) * τ⁻¹⁻¹) = a * b * (τ * τ) by group, hττ,
            mul_one] at h
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (K.inv_mem ha)
        · refine Or.inr ?_
          have h := K.inv_mem (hc ha)
          rwa [show (τ⁻¹ * (a * τ) * τ⁻¹⁻¹)⁻¹ = (τ * τ)⁻¹ * (a⁻¹ * τ) by group, hττ, inv_one,
            one_mul] at h }
  have hle : X ≤ L := by
    rw [hX]
    refine sup_le (fun k hk => Or.inl hk) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by rw [hττ]; exact K.one_mem)
  exact hle hg

theorem index_eq_two (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) (hτX : τ ∈ X) (hτK : τ ∉ K)
    (hττ : τ * τ = 1) (hX : X = K ⊔ zpowers τ) : (K.subgroupOf X).index = 2 := by
  rw [Subgroup.index_eq_two_iff_exists_notMem_and]
  refine ⟨⟨τ, hτX⟩, fun h => hτK (Subgroup.mem_subgroupOf.mp h), fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact (mem_or_mul_mem hKX hKn hτX hττ hX b.2).symm

theorem sq_mem (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) (hτX : τ ∈ X) (hττ : τ * τ = 1)
    (hX : X = K ⊔ zpowers τ) {g : G} (hg : g ∈ X) : g * g ∈ K := by
  rcases mem_or_mul_mem hKX hKn hτX hττ hX hg with h | h
  · exact K.mul_mem h h
  · have h' := K.mul_mem h (conj_mem hKX hKn h (X.inv_mem hτX))
    rwa [show g * τ * (τ⁻¹ * (g * τ) * τ⁻¹⁻¹) = g * g * (τ * τ) by group, hττ, mul_one] at h'

theorem mem_of_pow_three (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal) (hτX : τ ∈ X)
    (hττ : τ * τ = 1) (hX : X = K ⊔ zpowers τ) {g : G} (hg : g ∈ X) (h3 : g ^ 3 = 1) :
    g ∈ K := by
  have h := K.inv_mem (sq_mem hKX hKn hτX hττ hX hg)
  rwa [inv_eq_of_mul_eq_one_right (by rw [← pow_three']; exact h3)] at h

end Index

section Centralizer

variable {G : Type*} [Group G]

theorem eq_one_of_mem_of_commute {K : Subgroup G} (hKs : IsSimpleGroup K)
    (hKna : ∃ a b : K, a * b ≠ b * a) {z : G} (hz : z ∈ K) (hc : ∀ k ∈ K, z * k = k * z) :
    z = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · have hzc : (⟨z, hz⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (hc k k.2).symm
    rw [h, Subgroup.mem_bot] at hzc
    exact congrArg Subtype.val hzc
  · obtain ⟨a, b, hab⟩ := hKna
    have ha : a ∈ Subgroup.center K := h ▸ Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

variable {K X : Subgroup G} {τ : G}

theorem eq_one_of_commute (hO2 : pCoreOf 2 X = ⊥) (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal)
    (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a) (hτX : τ ∈ X) (hττ : τ * τ = 1)
    (hX : X = K ⊔ zpowers τ) {g : G} (hg : g ∈ X) (hc : ∀ k ∈ K, g * k = k * g) : g = 1 := by
  let C : Subgroup G := X ⊓ Subgroup.centralizer (K : Set G)
  have hCn : (C.subgroupOf X).Normal := by
    constructor
    intro c hc' x
    rw [Subgroup.mem_subgroupOf] at hc' ⊢
    obtain ⟨hcX, hcK⟩ := Subgroup.mem_inf.mp hc'
    have hyX : (x : G) ∈ X := x.2
    have key : ∀ y ∈ X, y * c * y⁻¹ ∈ C := by
      intro y hyX
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hyX hcX) (X.inv_mem hyX), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : y⁻¹ * k * y⁻¹⁻¹ ∈ K := conj_mem hKX hKn hk (X.inv_mem hyX)
      have e := Subgroup.mem_centralizer_iff.mp hcK _ hk'
      calc k * (y * c * y⁻¹) = y * ((y⁻¹ * k * y⁻¹⁻¹) * c) * y⁻¹ := by group
        _ = y * (c * (y⁻¹ * k * y⁻¹⁻¹)) * y⁻¹ := by rw [e]
        _ = y * c * y⁻¹ * k := by group
    exact key _ hyX
  have hCp : IsPGroup 2 C := by
    intro c
    refine ⟨1, Subtype.ext ?_⟩
    have hcK : ∀ k ∈ K, k * (c : G) = c * k := Subgroup.mem_centralizer_iff.mp c.2.2
    have hsq := sq_mem hKX hKn hτX hττ hX c.2.1
    have hcc : (c : G) * c = 1 := eq_one_of_mem_of_commute hKs hKna hsq fun k hk => by
      rw [mul_assoc, ← hcK k hk, ← mul_assoc, ← hcK k hk, mul_assoc]
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hcc
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 C X inf_le_left hCn
    hCp
  rw [hO2] at hle
  have hgC : g ∈ C := ⟨hg, Subgroup.mem_centralizer_iff.mpr fun k hk => (hc k hk).symm⟩
  exact Subgroup.mem_bot.mp (hle hgC)

theorem closure_conj_eq (hO2 : pCoreOf 2 X = ⊥) (hKX : K ≤ X) (hKn : (K.subgroupOf X).Normal)
    (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a) (hτX : τ ∈ X) (hττ : τ * τ = 1)
    (hX : X = K ⊔ zpowers τ) (hτ1 : τ ≠ 1) :
    Subgroup.closure {τ' | ∃ g ∈ X, τ' = g⁻¹ * τ * g} = X := by
  set N := Subgroup.closure {τ' | ∃ g ∈ X, τ' = g⁻¹ * τ * g} with hN
  have hNX : N ≤ X := by
    rw [hN, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    exact X.mul_mem (X.mul_mem (X.inv_mem hg) hτX) hg
  have hτN : τ ∈ N := Subgroup.subset_closure ⟨1, X.one_mem, by group⟩
  have hNc : ∀ h ∈ X, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
    intro h hh n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * h⁻¹, X.mul_mem hg (X.inv_mem hh), by group⟩
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact N.one_mem
    | mul x y _ _ hx hy =>
      have hxy := N.mul_mem hx hy
      rwa [show h * x * h⁻¹ * (h * y * h⁻¹) = h * (x * y) * h⁻¹ by group] at hxy
    | inv x _ hx =>
      have hx' := N.inv_mem hx
      rwa [show (h * x * h⁻¹)⁻¹ = h * x⁻¹ * h⁻¹ by group] at hx'
  haveI := hKs
  haveI hNKn : ((N ⊓ K).subgroupOf K).Normal := by
    constructor
    intro u hu k
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    exact ⟨hNc k (hKX k.2) u hu.1, K.mul_mem (K.mul_mem k.2 hu.2) (K.inv_mem k.2)⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ K).subgroupOf K) with h | h
  · refine absurd (eq_one_of_commute hO2 hKX hKn hKs hKna hτX hττ hX hτX fun k hk => ?_) hτ1
    have hmemN : τ * k * τ⁻¹ * k⁻¹ ∈ N := by
      have h1 : k * τ⁻¹ * k⁻¹ ∈ N := hNc k (hKX hk) _ (N.inv_mem hτN)
      have h2 := N.mul_mem hτN h1
      rwa [show τ * (k * τ⁻¹ * k⁻¹) = τ * k * τ⁻¹ * k⁻¹ by group] at h2
    have hmemK : τ * k * τ⁻¹ * k⁻¹ ∈ K := K.mul_mem (conj_mem hKX hKn hk hτX) (K.inv_mem hk)
    have hbot : (⟨_, hmemK⟩ : K) ∈ (N ⊓ K).subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr ⟨hmemN, hmemK⟩
    rw [h, Subgroup.mem_bot] at hbot
    have h1 : τ * k * τ⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hbot
    calc τ * k = τ * k * τ⁻¹ * k⁻¹ * (k * τ) := by group
      _ = k * τ := by rw [h1, one_mul]
  · have hKN : K ≤ N := fun k hk => by
      have hk' : (⟨k, hk⟩ : K) ∈ (N ⊓ K).subgroupOf K := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp hk').1
    refine le_antisymm hNX ?_
    rw [hX]
    exact sup_le hKN (Subgroup.zpowers_le.mpr hτN)

end Centralizer

section Decomposition

variable {V : Type} [CommGroup V] {K X : Subgroup (MulAut V)} {τ : MulAut V}

theorem exists_eq_of_decomposition (hO2 : pCoreOf 2 X = ⊥) (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a)
    (hτX : τ ∈ X) (hττ : τ * τ = 1) (hX : X = K ⊔ zpowers τ) (hτ1 : τ ≠ 1) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (MulAut V)} (hW : IsMcLaughlinDecomposition X τ r W) :
    ∃ i, X = W i := by
  obtain ⟨hsup, hWX, hcomm, -, -, -, -, -⟩ := hW
  have hsupX : (⨆ i, W i) = X :=
    hsup.trans (closure_conj_eq hO2 hKX hKn hKs hKna hτX hττ hX hτ1)
  have hWn : ∀ i, ∀ x ∈ X, ∀ w ∈ W i, x * w * x⁻¹ ∈ W i := by
    intro i
    have hle : X ≤ Subgroup.normalizer (W i : Set (MulAut V)) := by
      rw [← hsupX]
      refine iSup_le fun j => ?_
      by_cases hij : j = i
      · rw [hij]
        exact Subgroup.le_normalizer
      · intro y hy
        have hyc := Subgroup.mem_centralizer_iff.mp (hcomm j i hij hy)
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          rwa [show y * w * y⁻¹ = w by rw [← hyc w hw]; group]
        · intro hw
          have e := hyc _ hw
          have e2 : y * w = y * (y * w * y⁻¹) := by
            calc y * w = y * w * y⁻¹ * y := by group
              _ = y * (y * w * y⁻¹) := e
          rw [mul_left_cancel e2]
          exact hw
    intro x hx w hw
    exact (Subgroup.mem_normalizer_iff.mp (hle hx) w).mp hw
  by_cases hex : ∃ i, K ≤ W i
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, le_antisymm ?_ (hWX i)⟩
    rw [← hsupX]
    refine iSup_le fun j => ?_
    by_cases hij : j = i
    · rw [hij]
    · intro w hw
      have hw1 : w = 1 := eq_one_of_commute hO2 hKX hKn hKs hKna hτX hττ hX (hWX j hw)
        fun k hk => (Subgroup.mem_centralizer_iff.mp (hcomm j i hij hw) k (hi hk)).symm
      rw [hw1]
      exact (W i).one_mem
  · exfalso
    push Not at hex
    obtain ⟨a, b, hab⟩ := hKna
    apply hab
    haveI := hKs
    have hcen : X ≤ Subgroup.centralizer (K : Set (MulAut V)) := by
      rw [← hsupX]
      refine iSup_le fun j => ?_
      haveI hn : ((W j ⊓ K).subgroupOf K).Normal := by
        constructor
        intro u hu k
        rw [Subgroup.mem_subgroupOf] at hu ⊢
        exact ⟨hWn j _ (hKX k.2) _ hu.1, K.mul_mem (K.mul_mem k.2 hu.2) (K.inv_mem k.2)⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((W j ⊓ K).subgroupOf K) with h | h
      · intro w hw
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hmemW : w * k * w⁻¹ * k⁻¹ ∈ W j := by
          have h1 := (W j).mul_mem hw (hWn j k (hKX hk) _ ((W j).inv_mem hw))
          rwa [show w * (k * w⁻¹ * k⁻¹) = w * k * w⁻¹ * k⁻¹ by group] at h1
        have hmemK : w * k * w⁻¹ * k⁻¹ ∈ K :=
          K.mul_mem (conj_mem hKX hKn hk (hWX j hw)) (K.inv_mem hk)
        have hbot : (⟨_, hmemK⟩ : K) ∈ (W j ⊓ K).subgroupOf K :=
          Subgroup.mem_subgroupOf.mpr ⟨hmemW, hmemK⟩
        rw [h, Subgroup.mem_bot] at hbot
        have h1 : w * k * w⁻¹ * k⁻¹ = 1 := congrArg Subtype.val hbot
        calc k * w = (w * k * w⁻¹ * k⁻¹)⁻¹ * (w * k) := by group
          _ = w * k := by rw [h1, inv_one, one_mul]
      · refine absurd (fun k hk => ?_) (hex j)
        have hk' : (⟨k, hk⟩ : K) ∈ (W j ⊓ K).subgroupOf K := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hk').1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcen (hKX a.2)) b b.2).symm

theorem isMcLaughlinGroup_of_decomposition (hO2 : pCoreOf 2 X = ⊥) (hKX : K ≤ X)
    (hKn : (K.subgroupOf X).Normal) (hKs : IsSimpleGroup K) (hKna : ∃ a b : K, a * b ≠ b * a)
    (hτX : τ ∈ X) (hττ : τ * τ = 1) (hX : X = K ⊔ zpowers τ) (hτ1 : τ ≠ 1) {r : ℕ}
    {W : Fin (r + 1) → Subgroup (MulAut V)} (hW : IsMcLaughlinDecomposition X τ r W) :
    IsMcLaughlinGroup ↥X := by
  obtain ⟨i, hi⟩ := exists_eq_of_decomposition hO2 hKX hKn hKs hKna hτX hττ hX hτ1 hW
  rw [hi]
  exact hW.2.2.2.2.2.2.2 i

end Decomposition

theorem isElemAbelian_map {G H : Type*} [Group G] [Group H] (f : G →* H) {p : ℕ}
    {E : Subgroup G} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, ha, rfl⟩ := x
    obtain ⟨_, b, hb, rfl⟩ := y
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hp a ha, map_one]

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614KTr
