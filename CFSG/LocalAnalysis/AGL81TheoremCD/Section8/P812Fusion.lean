module

public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.A1cTransfer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section8

open Subgroup

private theorem exists_mem_conj_le_of_isPGroup_of_isSylowOf {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {M K V : Subgroup G} (hV : CFSG.ABGLocalTools.IsSylowOf p V M)
    (hKM : K ≤ M) (hK : IsPGroup p ↥K) :
    ∃ m ∈ M, K.map (MulAut.conj m) ≤ V := by
  have hK' : IsPGroup p ↥(K.subgroupOf M) :=
    hK.comap_of_injective M.subtype M.subtype_injective
  obtain ⟨R, hKR⟩ := hK'.exists_le_sylow
  have hR : CFSG.ABGLocalTools.IsSylowOf p ((R : Subgroup ↥M).map M.subtype) M := ⟨R, rfl⟩
  obtain ⟨k, hkM, hk⟩ := hV.exists_mem_conj hR
  refine ⟨k⁻¹, M.inv_mem hkM, ?_⟩
  rintro z ⟨y, hyK, rfl⟩
  have hyR : y ∈ (R : Subgroup ↥M).map M.subtype :=
    Subgroup.mem_map.mpr ⟨⟨y, hKM hyK⟩, hKR hyK, rfl⟩
  have hconj := (hk y).mp hyR
  simpa [MulAut.conj_apply] using hconj

theorem isSylowOf_top_of_isSylowOf_of_omega {G : Type} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] {M S A : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf q S M)
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian q A)
    (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A) (hNA : Subgroup.normalizer (A : Set G) ≤ M) :
    CFSG.ABGLocalTools.IsSylowOf q S ⊤ := by
  obtain ⟨T, hST⟩ := hS.isPGroup.exists_le_sylow
  have hNTM : ((T : Subgroup G) ⊓ Subgroup.normalizer (S : Set G)) ≤ M := by
    intro x hx
    apply hNA
    refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
    · have haS : a ∈ S := hAS ha
      have h1 : x * a * x⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hx.2 a).mp haS
      have h2 : (x * a * x⁻¹) ^ q = 1 := by
        rw [conj_pow, hA.2 a ha]
        simp
      exact hΩ _ h1 h2
    · have haS : a ∈ S := (Subgroup.mem_normalizer_iff.mp hx.2 a).mpr (hAS ha)
      have h2 : (x * a * x⁻¹) ^ q = 1 := hA.2 _ ha
      have haq : a ^ q = 1 := by
        rw [conj_pow] at h2
        calc a ^ q = x⁻¹ * (x * a ^ q * x⁻¹) * x := by group
          _ = x⁻¹ * 1 * x := by rw [h2]
          _ = 1 := by group
      exact hΩ _ haS haq
  have hQS : ((T : Subgroup G) ⊓ Subgroup.normalizer (S : Set G)) = S :=
    hS.eq_of_le (le_inf hST Subgroup.le_normalizer) hNTM
      (T.isPGroup'.to_le inf_le_left)
  have hTeq : (T : Subgroup G) = S := by
    by_contra hne
    have hsub_ne_top : S.subgroupOf (T : Subgroup G) ≠ ⊤ := fun htop =>
      hne (le_antisymm hST (Subgroup.subgroupOf_eq_top.mp htop)).symm
    have hlt : S.subgroupOf (T : Subgroup G) < ⊤ := lt_top_iff_ne_top.mpr hsub_ne_top
    haveI : Group.IsNilpotent ↥(T : Subgroup G) := T.isPGroup'.isNilpotent
    obtain ⟨y, hyNorm, hyNot⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (S.subgroupOf (T : Subgroup G)) hlt)
    have hyN : (y : G) ∈ Subgroup.normalizer (S : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro z ⟨a, ha, rfl⟩
        have haU : (⟨a, hST ha⟩ : ↥(T : Subgroup G)) ∈ S.subgroupOf (T : Subgroup G) := ha
        have hconj := (Subgroup.mem_normalizer_iff.mp hyNorm ⟨a, hST ha⟩).mp haU
        simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp hconj
      · rw [Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective]
    have hyS : (y : G) ∈ S := by
      have hmem : (y : G) ∈ (T : Subgroup G) ⊓ Subgroup.normalizer (S : Set G) :=
        ⟨y.2, hyN⟩
      rw [hQS] at hmem
      exact hmem
    exact hyNot hyS
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨le_top, hTeq ▸ T.isPGroup', ?_⟩
  rw [← hTeq, Subgroup.relIndex_top_right]
  exact T.not_dvd_index

theorem isWeaklyClosedIn_of_omega {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {S A : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A)
    (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A) :
    CFSG.Quasithin.IsWeaklyClosedIn A S := by
  intro g hg
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) ?_
  · obtain ⟨a, ha, hxeq⟩ := Subgroup.mem_map.mp hx
    refine hΩ x (hg hx) ?_
    rw [← hxeq, ← map_pow, hA.2 a ha, map_one]
  · rw [show (CFSG.Quasithin.conjSubgroup A g : Subgroup G) =
        A.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]

private theorem conjSet_eq_self_of_le_elemAbelian {G : Type} [Group G] {q : ℕ}
    {A X : Subgroup G} (hA : CFSG.Open.IsElemAbelian q A) (hXA : X ≤ A) :
    ∀ w ∈ A, CFSG.Quasithin.conjSet (X : Set G) w = (X : Set G) := by
  intro w hw
  ext z
  rw [CFSG.Quasithin.mem_conjSet_iff]
  constructor
  · intro hz
    have hzA : w * z * w⁻¹ ∈ A := hXA hz
    have hcomm : w⁻¹ * (w * z * w⁻¹) = (w * z * w⁻¹) * w⁻¹ :=
      hA.comm (A.inv_mem hw) hzA
    rwa [show z = w * z * w⁻¹ by
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = (w * z * w⁻¹) * w⁻¹ * w := by rw [hcomm]
        _ = w * z * w⁻¹ := by group]
  · intro hz
    have hcomm : w * z = z * w := hA.comm hw (hXA hz)
    rwa [show w * z * w⁻¹ = z by
      calc w * z * w⁻¹ = (z * w) * w⁻¹ := by rw [hcomm]
        _ = z := by group]

private theorem mem_elemAbelian_of_mem_conjSet {G : Type} [Group G] {q : ℕ}
    {S A X : Subgroup G} (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian q A)
    (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A) (hXA : X ≤ A) {h : G}
    (hhX : X.map (MulAut.conj h).toMonoidHom ≤ S) :
    ∀ z ∈ CFSG.Quasithin.conjSet (X : Set G) h⁻¹, z ∈ A := by
  intro z hz
  have hzX : h⁻¹ * z * h ∈ X := by
    simpa using (CFSG.Quasithin.mem_conjSet_iff.mp hz)
  have hzS : z ∈ S := hhX (Subgroup.mem_map.mpr ⟨h⁻¹ * z * h, hzX, by
    simp [MulAut.conj_apply]
    group⟩)
  have hzq : z ^ q = 1 := by
    have hxp : (h⁻¹ * z * h) ^ q = 1 := hA.2 _ (hXA hzX)
    rw [show z = h * (h⁻¹ * z * h) * h⁻¹ by group, conj_pow, hxp]
    group
  exact hΩ z hzS hzq

private theorem conjSet_conjSet_eq_self_of_le {G : Type} [Group G] {q : ℕ}
    {S A X : Subgroup G} (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian q A)
    (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A) (hXA : X ≤ A) {h : G}
    (hhX : X.map (MulAut.conj h).toMonoidHom ≤ S) :
    ∀ w ∈ A,
      CFSG.Quasithin.conjSet (CFSG.Quasithin.conjSet (X : Set G) h⁻¹) w =
        CFSG.Quasithin.conjSet (X : Set G) h⁻¹ := by
  intro w hw
  ext z
  rw [CFSG.Quasithin.mem_conjSet_iff]
  constructor
  · intro hz
    have hzA : w * z * w⁻¹ ∈ A :=
      mem_elemAbelian_of_mem_conjSet hAS hA hΩ hXA hhX _ hz
    have hcomm : w⁻¹ * (w * z * w⁻¹) = (w * z * w⁻¹) * w⁻¹ :=
      hA.comm (A.inv_mem hw) hzA
    have hfix : z = w * z * w⁻¹ := by
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = (w * z * w⁻¹) * w⁻¹ * w := by rw [hcomm]
        _ = w * z * w⁻¹ := by group
    rw [hfix]
    exact hz
  · intro hz
    have hzA : z ∈ A := mem_elemAbelian_of_mem_conjSet hAS hA hΩ hXA hhX _ hz
    have hcomm : w * z = z * w := hA.comm hw hzA
    have hfix : w * z * w⁻¹ = z := by
      calc w * z * w⁻¹ = (z * w) * w⁻¹ := by rw [hcomm]
        _ = z := by group
    rwa [hfix]

private theorem exists_mem_normalizer_mul_normalizer {G : Type} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] {S A X : Subgroup G} (hTop : CFSG.ABGLocalTools.IsSylowOf q S ⊤)
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian q A)
    (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A) (hXA : X ≤ A) {h : G}
    (hhX : X.map (MulAut.conj h).toMonoidHom ≤ S) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n * h ∈ Subgroup.normalizer (X : Set G) := by
  have hdvd : ¬ q ∣ S.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff.mp hTop).2.2
    simpa [Subgroup.relIndex_top_right] using h
  let T : Sylow q G := hTop.isPGroup.toSylow hdvd
  have hT : (T : Subgroup G) = S := IsPGroup.toSylow_coe hTop.isPGroup hdvd
  have hWT : A ≤ (T : Subgroup G) := by rw [hT]; exact hAS
  have hWc : CFSG.Quasithin.IsWeaklyClosedIn A (T : Subgroup G) := by
    rw [hT]
    exact isWeaklyClosedIn_of_omega hA hΩ
  obtain ⟨n, hnN, hn⟩ := CFSG.Quasithin.burnside_fusion_lemma T hWT hWc
    (conjSet_eq_self_of_le_elemAbelian hA hXA)
    (conjSet_conjSet_eq_self_of_le hAS hA hΩ hXA hhX)
    (B := CFSG.Quasithin.conjSet (X : Set G) h⁻¹) rfl
  refine ⟨n, hnN, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have h1 : h * z * h⁻¹ ∈ CFSG.Quasithin.conjSet (X : Set G) h⁻¹ :=
      (CFSG.Quasithin.mem_conjSet_iff).mpr (by
        rw [show h⁻¹ * (h * z * h⁻¹) * (h⁻¹)⁻¹ = z by group]
        exact hz)
    rw [← hn] at h1
    have h2 := (CFSG.Quasithin.mem_conjSet_iff.mp h1)
    have h3 : n * (h * z * h⁻¹) * n⁻¹ = n * h * z * (n * h)⁻¹ := by group
    rwa [h3] at h2
  · intro hz
    have h1 : n * (h * z * h⁻¹) * n⁻¹ ∈ X := by
      have h3 : n * (h * z * h⁻¹) * n⁻¹ = n * h * z * (n * h)⁻¹ := by group
      rwa [h3]
    have h2 : h * z * h⁻¹ ∈ CFSG.Quasithin.conjSet (X : Set G) n :=
      (CFSG.Quasithin.mem_conjSet_iff).mpr h1
    rw [hn] at h2
    have h3 := (CFSG.Quasithin.mem_conjSet_iff.mp h2)
    rwa [show h⁻¹ * (h * z * h⁻¹) * (h⁻¹)⁻¹ = z by group] at h3

private theorem exists_conj_le_of_le_map_conj {G : Type} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] {M S A X : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf q S M)
    (hXA : X ≤ A) (hA : CFSG.Open.IsElemAbelian q A) {g : G}
    (hXg : X ≤ M.map (MulAut.conj g).toMonoidHom) :
    ∃ m ∈ M, ∃ h : G, h = m * g⁻¹ ∧ X.map (MulAut.conj h).toMonoidHom ≤ S := by
  have hXq : IsPGroup q ↥X := hA.isPGroup.to_le hXA
  have hXconjM : X.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    rintro z ⟨x, hxX, hxeq⟩
    obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.mp (hXg hxX)
    have hm' : g * m * g⁻¹ = x := by
      simpa [MulAut.conj_apply] using hm
    have hz : (MulAut.conj g⁻¹).toMonoidHom x = m := by
      change (MulAut.conj g⁻¹) x = m
      rw [MulAut.conj_apply, ← hm', inv_inv]
      group
    rw [← hxeq, hz]
    exact hmM
  obtain ⟨m, hmM, hmX⟩ := exists_mem_conj_le_of_isPGroup_of_isSylowOf hS hXconjM
    (hXq.map (MulAut.conj g⁻¹).toMonoidHom)
  refine ⟨m, hmM, m * g⁻¹, rfl, ?_⟩
  have heq : X.map (MulAut.conj (m * g⁻¹)).toMonoidHom =
      (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj m).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    change (MulAut.conj (m * g⁻¹)) x = (MulAut.conj m) ((MulAut.conj g⁻¹) x)
    rw [map_mul, MulAut.mul_apply]
  rw [heq]
  exact hmX

theorem mem_uniqueSet_of_normalizer_le_of_omega {G : Type} [Group G] [Finite G] {q : ℕ}
    [Fact q.Prime] {M S A X : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf q S M)
    (hAS : A ≤ S) (hA : CFSG.Open.IsElemAbelian q A) (hΩ : ∀ x ∈ S, x ^ q = 1 → x ∈ A)
    (hNA : Subgroup.normalizer (A : Set G) ≤ M) (hXA : X ≤ A)
    (hNX : Subgroup.normalizer (X : Set G) ≤ M) :
    X ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet M := by
  have hTop : CFSG.ABGLocalTools.IsSylowOf q S ⊤ :=
    isSylowOf_top_of_isSylowOf_of_omega hS hAS hA hΩ hNA
  refine ⟨hXA.trans (hAS.trans hS.le), fun g hXg => ?_⟩
  obtain ⟨m, hmM, h, hh, hhX⟩ := exists_conj_le_of_le_map_conj hS hXA hA hXg
  obtain ⟨n, hnN, hnhX⟩ := exists_mem_normalizer_mul_normalizer hTop hAS hA hΩ hXA hhX
  have hnM : n ∈ M := hNA hnN
  have hnhM : n * h ∈ M := hNX hnhX
  have hhM : h ∈ M := by
    have hsplit : h = n⁻¹ * (n * h) := by group
    rw [hsplit]
    exact M.mul_mem (M.inv_mem hnM) hnhM
  have hgM : g ∈ M := by
    have hg' : g = h⁻¹ * m := by rw [hh]; group
    rw [hg']
    exact M.mul_mem (M.inv_mem hhM) hmM
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section8
