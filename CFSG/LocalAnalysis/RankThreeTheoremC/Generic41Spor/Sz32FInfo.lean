module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Fcases
import CFSG.LocalAnalysis.RankFourTheoremC.PPointPlane
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

structure Sz32FInfo (x : G) (U F : Subgroup G) : Prop where
  le_cent : F ≤ Subgroup.centralizer ({x} : Set G)
  wc : ∀ g : G, (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom ≤ F →
    (Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers x
  cases : IsMulCommutative F ∨
    (Nat.card F = 5 ^ 3 ∧ ¬ IsMulCommutative F ∧ (∀ f ∈ F, f ^ 25 = 1) ∧
      (∀ z ∈ F, (∀ f ∈ F, f * z = z * f) ↔ z ∈ Subgroup.zpowers x) ∧
      (∀ f ∈ F, f ^ 5 = 1 → f ∈ U))


section Helpers

private theorem sfi_mem_map_conj {A : Subgroup G} {g y : G} :
    y ∈ A.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ A := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hz
  · intro h
    exact ⟨g⁻¹ * y * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem sfi_conj_mem_map_iff (w f : G) (A : Subgroup G) :
    w * f * w⁻¹ ∈ A.map (MulAut.conj w).toMonoidHom ↔ f ∈ A := by
  rw [sfi_mem_map_conj]
  simp [mul_assoc]

private theorem sfi_map_conj_map_conj (g h : G) (A : Subgroup G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

private theorem sfi_map_conj_cancel (g : G) (A : Subgroup G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [sfi_map_conj_map_conj]
  ext y
  simp [Subgroup.mem_map, MulAut.conj_apply]

private theorem sfi_conj_pow_eq_one_iff (w f : G) (n : ℕ) : (w * f * w⁻¹) ^ n = 1 ↔ f ^ n = 1 := by
  rw [conj_pow]
  constructor
  · intro h
    have : f ^ n = w⁻¹ * (w * f ^ n * w⁻¹) * w := by group
    rw [this, h]
    group
  · intro h
    rw [h]
    group

private theorem sfi_map_zpowers_conj {w x : G} (hwx : w * x = x * w) :
    (Subgroup.zpowers x).map (MulAut.conj w).toMonoidHom = Subgroup.zpowers x := by
  rw [MonoidHom.map_zpowers]
  congr 1
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hwx]
  group

end Helpers

section Helpers2

private theorem sfi_pelt_centralizes {n x : G} {m : ℕ} (hn : n ^ (5 ^ m) = 1)
    (hxo : orderOf x = 5) (hnx : n * x * n⁻¹ ∈ Subgroup.zpowers x) : n * x = x * n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x ^ k = n * x * n⁻¹ := Subgroup.mem_zpowers_iff.mp hnx
  have hpow : ∀ i : ℕ, n ^ i * x * (n ^ i)⁻¹ = x ^ (k ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc n ^ (i + 1) * x * (n ^ (i + 1))⁻¹
          = n * (n ^ i * x * (n ^ i)⁻¹) * n⁻¹ := by
            rw [pow_succ', mul_inv_rev]
            simp only [mul_assoc]
        _ = n * x ^ (k ^ i) * n⁻¹ := by rw [ih]
        _ = (n * x * n⁻¹) ^ (k ^ i) := conj_zpow.symm
        _ = (x ^ k) ^ (k ^ i) := by rw [hk]
        _ = x ^ (k ^ (i + 1)) := by rw [← zpow_mul, pow_succ']
  have hxpow : x ^ (k ^ (5 ^ m)) = x := by
    have := hpow (5 ^ m)
    rwa [hn, one_mul, inv_one, mul_one, eq_comm] at this
  have hdvd : ((5 : ℕ) : ℤ) ∣ k ^ (5 ^ m) - 1 := by
    have h1 : x ^ (k ^ (5 ^ m) - 1) = 1 := by
      rw [zpow_sub_one, hxpow, mul_inv_cancel]
    have h2 := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hxo] at h2
  have hk1 : (k : ZMod 5) = 1 := by
    have h3 : ((k ^ (5 ^ m) - 1 : ℤ) : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hdvd
    push_cast at h3
    rw [ZMod.pow_card_pow] at h3
    exact sub_eq_zero.mp h3
  have hdvd' : ((5 : ℕ) : ℤ) ∣ k - 1 := by
    have h4 : ((k - 1 : ℤ) : ZMod 5) = 0 := by
      push_cast
      rw [hk1]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h4
  have hxk : x ^ k = x := by
    have h5 : x ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.mp (by rwa [hxo])
    rw [zpow_sub_one] at h5
    exact mul_inv_eq_one.mp h5
  rw [hxk] at hk
  exact mul_inv_eq_iff_eq_mul.mp hk.symm

private theorem sfi_card_le_of_pRank {F E : Subgroup G} (hrank : CFSG.Open.pRank 5 F ≤ 2)
    (hEF : E ≤ F) (hE : IsElemAbelian 5 E) : Nat.card E ≤ 5 ^ 2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := hE.isPGroup.exists_card_eq
  have hkle : k ≤ CFSG.Open.pRank 5 F := by
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hEF, hE, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 5 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (hkle.trans hrank)

private theorem sfi_eq_of_normalizer {F N : Subgroup G} (hF5 : IsPGroup 5 F) (hNF : N ≤ F)
    (hN : ∀ n ∈ F, n ∈ Subgroup.normalizer (N : Set G) → n ∈ N) : N = F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Group.IsNilpotent F := hF5.isNilpotent
  have hnc : NormalizerCondition F := Group.normalizerCondition_of_isNilpotent (G := F)
  by_contra hne
  have hIPne : N.subgroupOf F ≠ ⊤ := by
    intro htop
    exact hne (le_antisymm hNF (Subgroup.subgroupOf_eq_top.1 htop))
  have hlt : N.subgroupOf F < Subgroup.normalizer ((N.subgroupOf F : Subgroup F) : Set F) :=
    hnc _ (lt_top_iff_ne_top.2 hIPne)
  obtain ⟨y, hyN, hyIP⟩ := SetLike.exists_of_lt hlt
  have hyNorm : (y : G) ∈ Subgroup.normalizer (N : Set G) := by
    have hysub : y ∈ (Subgroup.normalizer (N : Set G)).subgroupOf F := by
      rw [Subgroup.subgroupOf_normalizer_eq hNF]
      exact hyN
    exact Subgroup.mem_subgroupOf.mp hysub
  exact hyIP (Subgroup.mem_subgroupOf.mpr (hN y y.2 hyNorm))

end Helpers2

section PlaneConj

variable {P : Sylow 5 G} {M : Subgroup G} {a c y : G}

private theorem sfi_plane_conj (hQ : Sz32QFacts (P : Subgroup G) a c y x)
    (hZ : Sz32ZFacts P M x (a ^ 5)) {U : Subgroup G} (hU : Sz32Plane P x a c y U) {w : G}
    (hwx : w * x = x * w) (hwP : U.map (MulAut.conj w).toMonoidHom ≤ (P : Subgroup G)) :
    Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x (U.map (MulAut.conj w).toMonoidHom) := by
  have hel : IsElemAbelian 5 (U.map (MulAut.conj w).toMonoidHom) := hU.abs.elem.map _
  have hcard : Nat.card (U.map (MulAut.conj w).toMonoidHom) = 5 ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
    exact hU.abs.card
  have hxmem : x ∈ U.map (MulAut.conj w).toMonoidHom := by
    refine ⟨x, hU.abs.mem, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hwx]
    group
  refine ⟨hel, hcard, ?_, hxmem, ?_⟩
  · intro v hv
    exact hQ.Om_all v (hwP hv) (hel.2 v hv)
  · set U' : Subgroup G := U.map (MulAut.conj w).toMonoidHom with hU'
    have hxZ : x ∈ sz32Z a c := szk_x_mem_Z hQ
    have hle : Subgroup.zpowers x ≤ U' ⊓ sz32Z a c :=
      le_inf (Subgroup.zpowers_le.2 hxmem) (Subgroup.zpowers_le.2 hxZ)
    by_contra hne
    have h5 : 5 ∣ Nat.card (U' ⊓ sz32Z a c : Subgroup G) := by
      have := Subgroup.card_dvd_of_le hle
      rwa [szk_card_zpowers_x hQ] at this
    have h25 : Nat.card (U' ⊓ sz32Z a c : Subgroup G) ∣ 5 ^ 2 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : U' ⊓ sz32Z a c ≤ U')
      rwa [hcard] at this
    have hn5 : Nat.card (U' ⊓ sz32Z a c : Subgroup G) ≠ 5 := by
      intro h
      exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw [h, szk_card_zpowers_x hQ])).symm
    have h25' : Nat.card (U' ⊓ sz32Z a c : Subgroup G) = 5 ^ 2 := by
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 h25
      interval_cases i
      · rw [hi'] at h5
        norm_num at h5
      · exact absurd (by simpa using hi') hn5
      · exact hi'
    have hUZ : U' ⊓ sz32Z a c = U' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h25', hcard])
    have hU'Z : U' ≤ sz32Z a c := inf_eq_left.1 hUZ
    have hU'eq : U' = sz32Z a c :=
      Subgroup.eq_of_le_of_card_ge hU'Z (by rw [hQ.Z_card, hcard])
    have hZmap : (sz32Z a c).map (MulAut.conj w⁻¹).toMonoidHom = U := by
      rw [← hU'eq, hU']
      exact sfi_map_conj_cancel w U
    have hZe : Subgroup.zpowers (a ^ 5) ⊔ Subgroup.zpowers x = sz32Z a c := by
      rw [hQ.x_eq]
      rfl
    have hZwc := hZ.Z_wc w⁻¹ (by rw [hZe, hZmap]; exact hU.le_P)
    rw [hZe, hZmap] at hZwc
    have hUx : U = Subgroup.zpowers x :=
      calc U = U ⊓ sz32Z a c := (inf_eq_left.2 hZwc.le).symm
        _ = Subgroup.zpowers x := hU.abs.inf_Z
    have h2 := hU.abs.card
    rw [hUx, szk_card_zpowers_x hQ] at h2
    norm_num at h2

end PlaneConj

section Core

variable {P : Sylow 5 G} {M : Subgroup G} {J : Subgroup G} {a c y : G}

private theorem sfi_core (hc : PointConfig IsSz32Type G 5 P M x J)
    (hP : Sz32Struct P x J a c y) (hZ : Sz32ZFacts P M x (a ^ 5))
    {U : Subgroup G} (hU : Sz32Plane P x a c y U) {F₁ : Subgroup G} (hF₁5 : IsPGroup 5 F₁)
    (hUF₁ : U ≤ F₁) (hF₁C : F₁ ≤ Subgroup.centralizer ({x} : Set G))
    (hrank : ∀ E : Subgroup G, E ≤ F₁ → IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 2) :
    ∃ w ∈ Subgroup.centralizer ({x} : Set G),
      F₁.map (MulAut.conj w).toMonoidHom ≤ (P : Subgroup G) ∧
      ¬ Subgroup.zpowers (a ^ 5) ≤ F₁.map (MulAut.conj w).toMonoidHom ∧
      (F₁ = U ∨ (Nat.card F₁ = 5 ^ 3 ∧ ¬ IsMulCommutative F₁ ∧ (∀ f ∈ F₁, f ^ 25 = 1) ∧
        (∀ z ∈ F₁, (∀ f ∈ F₁, f * z = z * f) ↔ z ∈ Subgroup.zpowers x) ∧
        (∀ f ∈ F₁, f ^ 5 = 1 → f ∈ U))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hQ : Sz32QFacts (P : Subgroup G) a c y x := hP.facts
  have hPS : IsSylowOf 5 (P : Subgroup G) (Subgroup.centralizer ({x} : Set G)) := by
    have h := hc.generic.2.2.1
    rwa [inf_eq_left.2 hP.le_cent] at h
  obtain ⟨w, hwC, hw⟩ :=
    CFSG.LocalAnalysis.RankFourTheoremC.exists_conj_le_of_isSylowOf hPS hF₁C hF₁5
  have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
  have hUP : U.map (MulAut.conj w).toMonoidHom ≤ (P : Subgroup G) :=
    (Subgroup.map_mono hUF₁).trans hw
  have hU' := sfi_plane_conj hQ hZ hU hwx hUP
  have hrank' : ∀ E : Subgroup G, E ≤ F₁.map (MulAut.conj w).toMonoidHom → IsElemAbelian 5 E →
      Nat.card E ≤ 5 ^ 2 := by
    intro E hE hEel
    have hE1 : E.map (MulAut.conj w⁻¹).toMonoidHom ≤ F₁ := by
      have := Subgroup.map_mono (f := (MulAut.conj w⁻¹).toMonoidHom) hE
      rwa [sfi_map_conj_cancel] at this
    have := hrank _ hE1 (hEel.map _)
    rwa [Subgroup.card_map_of_injective (MulAut.conj w⁻¹).injective] at this
  obtain ⟨hnot, hcases⟩ := sz32_Fcases hQ hU' (Subgroup.map_mono hUF₁) hw hrank'
  refine ⟨w, hwC, hw, hnot, ?_⟩
  have hxw := sfi_map_zpowers_conj hwx
  have hxc : ∀ t : G, w * t * w⁻¹ ∈ Subgroup.zpowers x ↔ t ∈ Subgroup.zpowers x := by
    intro t
    have := sfi_conj_mem_map_iff w t (Subgroup.zpowers x)
    rwa [hxw] at this
  rcases hcases with h | ⟨hcard, hnc, hexp, hcen, hom⟩
  · left
    exact Subgroup.map_injective (MulAut.conj w).injective h
  · right
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hcard
    · intro hF
      apply hnc
      haveI := hF
      infer_instance
    · intro f hf
      exact (sfi_conj_pow_eq_one_iff w f 25).1 (hexp _ ((sfi_conj_mem_map_iff w f F₁).2 hf))
    · intro z hz
      have hz' := (sfi_conj_mem_map_iff w z F₁).2 hz
      rw [← hxc z, ← hcen _ hz']
      constructor
      · intro h f' hf'
        obtain ⟨f, hf, rfl⟩ := hf'
        have := congrArg (MulAut.conj w) (h f hf)
        show w * f * w⁻¹ * (w * z * w⁻¹) = w * z * w⁻¹ * (w * f * w⁻¹)
        simpa only [map_mul, MulAut.conj_apply] using this
      · intro h f hf
        have := h (w * f * w⁻¹) ((sfi_conj_mem_map_iff w f F₁).2 hf)
        apply (MulAut.conj w).injective
        simpa only [map_mul, MulAut.conj_apply] using this
    · intro f hf hf5
      exact (sfi_conj_mem_map_iff w f U).1
        (hom _ ((sfi_conj_mem_map_iff w f F₁).2 hf) ((sfi_conj_pow_eq_one_iff w f 5).2 hf5))

end Core

theorem sz32_F_info (hc : PointConfig IsSz32Type G 5 P M x J) {a c y : G}
    (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) (hZ : Sz32ZFacts P M x (a ^ 5))
    {U : Subgroup G} (hU : Sz32Plane P x a c y U) {F : Subgroup G} (hF5 : IsPGroup 5 F)
    (hUF : U ≤ F) (hrank : CFSG.Open.pRank 5 F ≤ 2) : Sz32FInfo x U F := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hxo : orderOf x = 5 := hP.decomp.pres.x_ord
  have hxU : x ∈ U := hU.abs.mem
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : Subgroup G, F₁ = F ⊓ Subgroup.normalizer (U : Set G) := ⟨_, rfl⟩
  have hF₁F : F₁ ≤ F := hF₁def ▸ inf_le_left
  have hUF₁ : U ≤ F₁ := hF₁def ▸ le_inf hUF Subgroup.le_normalizer
  have hF₁N : ∀ n ∈ F₁, n ∈ Subgroup.normalizer (U : Set G) := fun n hn => by
    rw [hF₁def] at hn
    exact hn.2
  have hF₁C : ∀ n ∈ F₁, n * x = x * n := by
    intro n hn
    have hnU := hF₁N n hn
    have hnxU : n * x * n⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 hnU x).1 hxU
    have hmap : (Subgroup.zpowers x).map (MulAut.conj n).toMonoidHom ≤ U := by
      rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.2 ?_
      simpa [MulAut.conj_apply] using hnxU
    have hwc := hU.wc n hmap
    have hmem : n * x * n⁻¹ ∈ Subgroup.zpowers x := by
      rw [← hwc]
      exact ⟨x, Subgroup.mem_zpowers x, by simp [MulAut.conj_apply]⟩
    obtain ⟨m, hm⟩ := hF5 ⟨n, hF₁F hn⟩
    have hnm : n ^ (5 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    exact sfi_pelt_centralizes hnm hxo hmem
  have hF₁C' : F₁ ≤ Subgroup.centralizer ({x} : Set G) := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.2 (hF₁C n hn)
  have hrank₁ : ∀ E : Subgroup G, E ≤ F₁ → IsElemAbelian 5 E → Nat.card E ≤ 5 ^ 2 :=
    fun E hE hEel => sfi_card_le_of_pRank hrank (hE.trans hF₁F) hEel
  obtain ⟨w, hwC, hwP, hnot, hcases⟩ :=
    sfi_core hc hP hZ hU (hF5.to_le hF₁F) hUF₁ hF₁C' hrank₁
  have hwx : w * x = x * w := Subgroup.mem_centralizer_singleton_iff.1 hwC
  have hxw := sfi_map_zpowers_conj hwx
  have hΩ : ∀ f ∈ F₁, f ^ 5 = 1 → f ∈ U := by
    rcases hcases with h | ⟨-, -, -, -, h⟩
    · intro f hf _
      rwa [h] at hf
    · exact h
  have hF₁eq : F₁ = F := by
    refine sfi_eq_of_normalizer hF5 hF₁F ?_
    intro n hnF hnN
    have hN' := Subgroup.mem_normalizer_iff.1 hnN
    have hnU : n ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        have h1 : n * u * n⁻¹ ∈ F₁ := (hN' u).1 (hUF₁ hu)
        have h5 : (n * u * n⁻¹) ^ 5 = 1 :=
          (sfi_conj_pow_eq_one_iff n u 5).2 (hU.abs.elem.2 u hu)
        exact hΩ _ h1 h5
      · intro hu
        have h1 : u ∈ F₁ := (hN' u).2 (hUF₁ hu)
        have h5 : u ^ 5 = 1 := (sfi_conj_pow_eq_one_iff n u 5).1 (hU.abs.elem.2 _ hu)
        exact hΩ u h1 h5
    rw [hF₁def]
    exact ⟨hnF, hnU⟩
  rw [hF₁eq] at hwP hnot hcases
  have hFC : F ≤ Subgroup.centralizer ({x} : Set G) := hF₁eq ▸ hF₁C'
  refine ⟨hFC, ?_, ?_⟩
  ·
    intro g hg
    have h1 : ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom).map (MulAut.conj w).toMonoidHom ≤
        F.map (MulAut.conj w).toMonoidHom := Subgroup.map_mono hg
    rw [sfi_map_conj_map_conj] at h1
    rcases hL.lines (w * g) (h1.trans hwP) with h | h
    · have h2 : ((Subgroup.zpowers x).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj w).toMonoidHom = Subgroup.zpowers x := by
        rw [sfi_map_conj_map_conj]
        exact h
      have h3 := congrArg (fun A : Subgroup G => A.map (MulAut.conj w⁻¹).toMonoidHom) h2
      simp only [sfi_map_conj_cancel] at h3
      rw [h3]
      have h4 := sfi_map_conj_cancel w (Subgroup.zpowers x)
      rwa [hxw] at h4
    · exfalso
      apply hnot
      rw [← h]
      exact h1
  · rcases hcases with h | h
    · left
      rw [h]
      exact hU.abs.elem.1
    · right
      exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
