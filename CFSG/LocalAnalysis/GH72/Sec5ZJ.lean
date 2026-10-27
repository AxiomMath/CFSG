module

public import CFSG.LocalAnalysis.GH72.Sec5A
import CFSG.Foundations.MaxOrderThompson
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
import CFSG.GroupTheory.ABGLocalTools.OddInvolution
public import CFSG.LocalAnalysis.GH72.RelativeZJAmbient

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

namespace G5a

section General

variable {G : Type*} [Group G]

theorem ambientMaxCardZJ_ne_bot [Finite G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p P) (hP1 : P ≠ ⊥) : ambientMaxCardZJ P ≠ ⊥ := by
  have : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hP1
  rw [ambientMaxCardZJ_eq_map, maxCardZJ_eq_orderZJ, Ne,
    map_eq_bot_iff_of_injective _ P.subtype_injective]
  exact orderZJ_ne_bot_of_isPGroup hp hP

theorem isPLocal_normalizer_ambientMaxCardZJ [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) (hP1 : P ≠ ⊥) :
    CFSG.IsPLocal p (normalizer (ambientMaxCardZJ P : Set G)) :=
  ⟨ambientMaxCardZJ P, ambientMaxCardZJ_ne_bot hp hP hP1, hP.to_le (ambientMaxCardZJ_le P), rfl⟩

end General

section Choice

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxInvIn_top (p : ℕ) (A : Subgroup G) : ∃ P : Subgroup G, IsMaxInvIn p A ⊤ P := by
  obtain ⟨P, hP, -⟩ := G5d.exists_isMaxInvIn_ge (p := p) (A := A) (H := ⊤) le_top
    IsPGroup.of_bot le_normalizer_of_normal
  exact ⟨P, hP⟩

theorem exists_max_pair {p : ℕ} {A : Subgroup G} (𝒞 : Subgroup G → Prop) (h : ∃ H, 𝒞 H) :
    ∃ H P : Subgroup G, 𝒞 H ∧ P ≤ H ∧ IsPGroup p P ∧ A ≤ normalizer (P : Set G) ∧
      ∀ H' P' : Subgroup G, 𝒞 H' → P' ≤ H' → IsPGroup p P' → A ≤ normalizer (P' : Set G) →
        Nat.card P' ≤ Nat.card P := by
  obtain ⟨H₀, hH₀⟩ := h
  set Pairs : Set (Subgroup G × Subgroup G) :=
    {x | 𝒞 x.1 ∧ x.2 ≤ x.1 ∧ IsPGroup p x.2 ∧ A ≤ normalizer (x.2 : Set G)}
  have hne : Pairs.Nonempty := ⟨(H₀, ⊥), hH₀, bot_le, IsPGroup.of_bot, le_normalizer_of_normal⟩
  obtain ⟨⟨H, P⟩, ⟨hH, hPH, hPp, hAP⟩, hmax⟩ :=
    Set.exists_max_image Pairs (fun x => Nat.card x.2) (Set.toFinite Pairs) hne
  exact ⟨H, P, hH, hPH, hPp, hAP, fun H' P' h₁ h₂ h₃ h₄ => hmax (H', P') ⟨h₁, h₂, h₃, h₄⟩⟩

theorem not_le_centralizer_of_pConstrainedWrt {p : ℕ} (hp : p.Prime) {A H Z P : Subgroup G}
    (hA : IsPGroup 2 A) (hAH : A ≤ H) (hZA : Z ≤ A) (hc : Sec4Setting.PConstrainedWrt p A H Z)
    (hP : IsSylowOf p P (O H)) (hAP : A ≤ normalizer (P : Set G)) :
    ¬ Z ≤ centralizer (P : Set G) := by
  obtain ⟨P₀, hP₀, hAP₀, hZP₀⟩ := hc
  have hAO : A ≤ normalizer (O H : Set G) := hAH.trans (le_normalizer_O H)
  have hO2 : ¬ 2 ∣ Nat.card (O H) := fun h =>
    Nat.not_even_iff_odd.mpr (card_O_odd H) (even_iff_two_dvd.mpr h)
  obtain ⟨c, ⟨-, hcA⟩, hc⟩ := ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime
    Nat.prime_two hp hA hAO hO2 hP₀ hP hAP₀ hAP
  intro hZP
  apply hZP₀
  intro z hz
  rw [mem_centralizer_iff]
  intro x hx
  have hcx : c * x * c⁻¹ ∈ P := hc ▸ G4b.conj_mem_map_conj hx
  have h1 : c * x * c⁻¹ * z = z * (c * x * c⁻¹) := mem_centralizer_iff.mp (hZP hz) _ hcx
  have hcz : c * z = z * c := (mem_centralizer_iff.mp hcA z (hZA hz)).symm
  have hzc : c⁻¹ * z = z * c⁻¹ := by
    calc c⁻¹ * z = c⁻¹ * (z * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * z) * c⁻¹ := by rw [← hcz]
      _ = z * c⁻¹ := by group
  calc x * z = c⁻¹ * (c * x * c⁻¹) * (c * z) := by group
    _ = c⁻¹ * (c * x * c⁻¹) * (z * c) := by rw [hcz]
    _ = c⁻¹ * (c * x * c⁻¹ * z) * c := by group
    _ = c⁻¹ * (z * (c * x * c⁻¹)) * c := by rw [h1]
    _ = c⁻¹ * z * (c * x * c⁻¹) * c := by group
    _ = z * c⁻¹ * (c * x * c⁻¹) * c := by rw [hzc]
    _ = z * x := by group

theorem pConstrainedWrt_map_conj {p : ℕ} [Fact p.Prime] {A H Z : Subgroup G} {u : G}
    (hc : Sec4Setting.PConstrainedWrt p A H Z) (hu : u ∈ normalizer (A : Set G))
    (hZ : Z.map (MulAut.conj u).toMonoidHom = Z) :
    Sec4Setting.PConstrainedWrt p A (H.map (MulAut.conj u).toMonoidHom) Z := by
  obtain ⟨R, hR, hAR, hZR⟩ := hc
  have hA : A.map (MulAut.conj u).toMonoidHom = A := G4b.mem_normalizer_iff_map_conj_eq'.mp hu
  refine ⟨R.map (MulAut.conj u).toMonoidHom, ?_, ?_, ?_⟩
  · rw [← G4b.map_O]
    exact isSylowOf_map_hom hR _
  · rw [← hA, ← map_equiv_normalizer_eq]
    exact map_mono hAR
  · intro hZR'
    apply hZR
    rw [← G4b.map_centralizer, ← hZ] at hZR'
    exact (map_le_map_iff_of_injective (MulAut.conj u).injective).mp hZR'

end Choice

section EqTwo

variable {G : Type} [Group G] [Finite G]

theorem hasDihedralSylowTwo_of_odd_relIndex {J K K₀ S : Subgroup G} (hS : IsSylowOf 2 S K₀)
    (hSd : IsDih S) (hJK₀ : J ≤ K₀) (hJK : J ≤ K) (h₀ : Odd (J.relIndex K₀))
    (h₁ : Odd (J.relIndex K)) : GorensteinWalter.HasDihedralSylowTwo K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnd : ∀ {n : ℕ}, Odd n → ¬ 2 ∣ n := fun hn h =>
    Nat.not_even_iff_odd.mpr hn (even_iff_two_dvd.mpr h)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  have hT₀ := isSylowOf_of_not_dvd_relIndex hT hJK₀ (hnd h₀)
  have hTK := isSylowOf_of_not_dvd_relIndex hT hJK (hnd h₁)
  refine hasDihedralSylowTwo_of_isSylowOf hTK ?_
  obtain ⟨a, ha, ⟨e⟩⟩ := hSd
  obtain ⟨Q₁, hQ₁⟩ := hS.exists_sylow_eq_subgroupOf
  obtain ⟨Q₂, hQ₂⟩ := hT₀.exists_sylow_eq_subgroupOf
  exact ⟨a, ha, ⟨(subgroupOfEquivOfLe hT₀.le).symm.trans ((MulEquiv.subgroupCongr hQ₂).symm.trans
    ((Sylow.equiv Q₂ Q₁).trans ((MulEquiv.subgroupCongr hQ₁).trans
      ((subgroupOfEquivOfLe hS.le).trans e))))⟩⟩

omit [Finite G] in
theorem le_sup_O_of_sup_eq {H K₀ OK Z W : Subgroup G} (hZOK : Z ⊔ OK = K₀)
    (hZOKn : Z ≤ normalizer (OK : Set G)) (hZW : Z ≤ W) (hWK : W ≤ K₀) (hWO : W ⊓ OK ≤ O H) :
    W ≤ Z ⊔ O H := by
  intro w hw
  have hw' : w ∈ ((Z ⊔ OK : Subgroup G) : Set G) := by
    rw [SetLike.mem_coe, hZOK]
    exact hWK hw
  rw [coe_mul_of_left_le_normalizer_right Z OK hZOKn] at hw'
  obtain ⟨z, hz, o, ho, rfl⟩ := hw'
  have hoW : o ∈ W := by
    have : o = z⁻¹ * (z * o) := by group
    rw [this]
    exact W.mul_mem (W.inv_mem (hZW hz)) hw
  exact mul_mem_sup hz (hWO ⟨hoW, ho⟩)

theorem eq_O_sup_inf_normalizer_zj_of_covers {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A H K₀ OK Z W P K₁ : Subgroup G} {L : Type} [Group L] (f : K₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀)
    (hLs : IsSimpleGroup L ∨ Nat.card L ≤ Nat.card Z) (hS : ∃ S, IsSylowOf 2 S K₀ ∧ IsDih S)
    (hOKK₀ : OK ≤ K₀) (hOK : Odd (Nat.card OK)) (hZA : Z ≤ A) (hA2 : IsPGroup 2 A)
    (hAH : A ≤ H) (hWH : W ≤ H) (hWK : W ≤ K₀) (hZW : Z ≤ W) (hWcov : K₀ ≤ W ⊔ OK)
    (hWn : ((W ⊔ O H).subgroupOf H).Normal) (hWint : O H ⊓ W = W ⊓ OK)
    (hmax : IsMaxInvIn p A H P) (hK₁ : K₁ = W ⊔ O H ⊔ P)
    (hZQ : ¬ Z ≤ centralizer ((P ⊓ O K₁ : Subgroup G) : Set G)) :
    K₁ = O K₁ ⊔ (K₁ ⊓ normalizer (ambientMaxCardZJ P : Set G)) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPH := hmax.1
  have hPp := hmax.2.1
  have hAP := hmax.2.2.1
  have hL₀H : W ⊔ O H ≤ H := sup_le hWH (map_subtype_le _)
  have hHL₀ : H ≤ normalizer ((W ⊔ O H : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL₀H).mp hWn
  have hK₁H : K₁ ≤ H := hK₁.le.trans (sup_le hL₀H hPH)
  have hPK₁ : P ≤ K₁ := le_sup_right.trans hK₁.ge
  have hWK₁ : W ≤ K₁ := (le_sup_left.trans le_sup_left).trans hK₁.ge
  have hOHK₁' : O H ≤ K₁ := (le_sup_right.trans le_sup_left).trans hK₁.ge
  have hAK₁ : A ≤ normalizer (K₁ : Set G) := by
    rw [hK₁]
    exact fun a ha => inf_normalizer_le_normalizer_sup _ P ⟨hHL₀ (hAH ha), hAP ha⟩
  have hQ : IsSylowOf p (P ⊓ O K₁) (O K₁) :=
    isSylowOf_inf_O_of_isMaxInvIn hp hA2 hAK₁ (hmax.of_le hPK₁ hK₁H)
  have hOHK₁ : O H ≤ O K₁ :=
    G5d.le_O_of_le_normalizer hOHK₁' (hK₁H.trans (le_normalizer_O H)) (card_O_odd H)
  have hK₀OK : K₀ ≤ normalizer (OK : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hOKK₀).mp (hker ▸ f.normal_ker)
  have hWO : W ⊓ OK ≤ O H := by
    rw [← hWint]
    exact inf_le_left
  have hZ2 : IsPGroup 2 Z := hA2.to_le hZA
  rcases hLs with hsimple | hcard
  ·
    obtain ⟨S, hSs, hSd⟩ := hS
    have hLzK₁ : W ⊔ O K₁ ≤ K₁ := sup_le hWK₁ (map_subtype_le _)
    have hLz' : W ⊔ O K₁ = (W ⊔ O H) ⊔ O K₁ := by
      rw [sup_assoc, sup_eq_right.mpr hOHK₁]
    have hK₁Lz : K₁ ≤ normalizer ((W ⊔ O K₁ : Subgroup G) : Set G) := by
      rw [hLz']
      exact fun k hk => inf_normalizer_le_normalizer_sup _ (O K₁)
        ⟨hHL₀ (hK₁H hk), le_normalizer_O K₁ hk⟩
    have hLzn : ((W ⊔ O K₁).subgroupOf K₁).Normal :=
      (normal_subgroupOf_iff_le_normalizer hLzK₁).mpr hK₁Lz
    have hLzP : W ⊔ O K₁ ⊔ P = K₁ :=
      le_antisymm (sup_le hLzK₁ hPK₁) (hK₁.le.trans (sup_le (sup_le
        (le_sup_left.trans le_sup_left) (hOHK₁.trans (le_sup_right.trans le_sup_left)))
        le_sup_right))
    have hLmin : ∀ N : Subgroup G, (N.subgroupOf K₁).Normal → O K₁ ≤ N →
        N ≤ W ⊔ O K₁ → N = O K₁ ∨ N = W ⊔ O K₁ := by
      intro N hN hON hNL
      have hK₁N : K₁ ≤ normalizer (N : Set G) :=
        (normal_subgroupOf_iff_le_normalizer (hNL.trans hLzK₁)).mp hN
      exact eq_or_eq_of_isSimpleGroup_of_le_sup f hf hker hOKK₀ hWK hWcov hWK₁
        (hWO.trans hOHK₁) (hWK₁.trans hK₁N) hON hNL
    have hD : GorensteinWalter.HasDihedralSylowTwo K₁ := by
      refine hasDihedralSylowTwo_of_odd_relIndex hSs hSd hWK hWK₁ ?_ ?_
      · have h := relIndex_sup_left_of_le_normalizer (hWK.trans hK₀OK)
        rw [← le_antisymm hWcov (sup_le hWK hOKK₀)] at h
        rw [h]
        exact hOK.of_dvd_nat (relIndex_dvd_card _ _)
      · have h₁ : Odd (W.relIndex (W ⊔ O H)) := by
          rw [relIndex_sup_left_of_le_normalizer (hWH.trans (le_normalizer_O H))]
          exact (card_O_odd H).of_dvd_nat (relIndex_dvd_card _ _)
        have h₂ : Odd ((W ⊔ O H).relIndex K₁) := by
          have h := relIndex_sup_of_le_normalizer (hPH.trans hHL₀)
          rw [sup_comm P, ← hK₁] at h
          rw [h]
          exact (odd_card_of_isPGroup hp hp2 hPp).of_dvd_nat (relIndex_dvd_card _ _)
        rw [← relIndex_mul_relIndex W (W ⊔ O H) K₁ le_sup_left (le_sup_left.trans hK₁.ge)]
        exact h₁.mul h₂
    exact eq_O_sup_inf_normalizer_zj hp2 hPp hPK₁ hQ hZ2 (hZA.trans hAP) hZQ hLzn le_sup_right
      (hZW.trans le_sup_left) hLzP hLmin hD
  ·
    have hZOK := sup_eq_of_card_le f hf hker hOKK₀ hOK (hZW.trans hWK) hZ2 hcard
    have hWZ : W ≤ Z ⊔ O H :=
      le_sup_O_of_sup_eq hZOK ((hZW.trans hWK).trans hK₀OK) hZW hWK hWO
    have hK₁le : K₁ ≤ Z ⊔ (P ⊔ O H) :=
      hK₁.le.trans (sup_le (sup_le (hWZ.trans (sup_le le_sup_left
        (le_sup_right.trans le_sup_right))) (le_sup_right.trans le_sup_right))
        (le_sup_left.trans le_sup_right))
    have hPOH : P ⊔ O H ≤ O K₁ := by
      refine G5d.le_O_of_le_normalizer (sup_le hPK₁ hOHK₁') ?_
        (odd_card_sup_of_le_normalizer (hPH.trans (le_normalizer_O H))
          (odd_card_of_isPGroup hp hp2 hPp) (card_O_odd H))
      refine hK₁le.trans (sup_le (fun z hz => ?_) le_normalizer)
      exact inf_normalizer_le_normalizer_sup P (O H)
        ⟨hAP (hZA hz), le_normalizer_O H (hAH (hZA hz))⟩
    exact eq_O_sup_inf_normalizer_zj_of_le_O hQ (le_sup_left.trans hPOH)

end EqTwo

section Core

variable {G : Type} [Group G] [Finite G]

private theorem exists_pair_ne_of_isKleinFour' {V : Type*} [Group V] [IsKleinFour V] :
    ∃ x y : V, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [IsKleinFour.card_four]; norm_num)
  have : Nontrivial V :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [IsKleinFour.card_four]; norm_num)
  obtain ⟨x, hx⟩ := exists_ne (1 : V)
  obtain ⟨y, hy⟩ : ∃ y : V, y ∉ Subgroup.zpowers x := by
    by_contra h
    exact IsKleinFour.not_isCyclic
      ⟨⟨x, fun y => Subgroup.mem_zpowers_iff.mp (not_not.mp (not_exists.mp h y))⟩⟩
  exact ⟨x, y, hx, fun h => hy (h ▸ Subgroup.one_mem _), fun h => hy (h ▸ Subgroup.mem_zpowers x)⟩

theorem le_centralizer_of_forall_inf_centralizer {Q V Z : Subgroup G} (hV : IsKleinFour V)
    (hQ : Odd (Nat.card Q)) (hVQ : V ≤ normalizer (Q : Set G))
    (h : ∀ v ∈ V, v ≠ 1 → Z ≤ centralizer ((Q ⊓ C v : Subgroup G) : Set G)) :
    Z ≤ centralizer (Q : Set G) := by
  have := hV
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_pair_ne_of_isKleinFour' (V := V)
  have hx1 : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
  have hxy' : (x : G) ≠ y := fun h => hxy (Subtype.ext h)
  have hxy1 : (x : G) * y ≠ 1 := by
    intro h
    apply hxy
    have h2 : x * y = 1 := Subtype.ext h
    rw [← mul_left_cancel_iff (a := x), h2, IsKleinFour.mul_self]
  have hxyx : (x : G) * y ≠ x := fun h => hy1 (by simpa using h)
  have hxyy : (x : G) * y ≠ y := fun h => hx1 (by simpa using h)
  have hgen := ABGLocalTools.four_group_odd_eq_mul_centralizers hQ hVQ x.2 y.2
    (V.mul_mem x.2 y.2) hx1 hy1 hxy1 hxy' (Ne.symm hxyx) (Ne.symm hxyy)
  intro z hz
  rw [mem_centralizer_iff]
  intro q hq
  have hq' : q ∈ ((Q ⊓ C (x : G) : Subgroup G) : Set G) * ((Q ⊓ C (y : G) : Subgroup G) : Set G) *
      ((Q ⊓ C ((x : G) * y) : Subgroup G) : Set G) := by
    rw [← hgen]
    exact hq
  obtain ⟨_, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, c₃, hc₃, rfl⟩ := hq'
  have h₁ : Commute c₁ z := mem_centralizer_iff.mp (h x x.2 hx1 hz) c₁ hc₁
  have h₂ : Commute c₂ z := mem_centralizer_iff.mp (h y y.2 hy1 hz) c₂ hc₂
  have h₃ : Commute c₃ z :=
    mem_centralizer_iff.mp (h _ (V.mul_mem x.2 y.2) hxy1 hz) c₃ hc₃
  exact ((h₁.mul_left h₂).mul_left h₃).eq

theorem prop_5_2_cover_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A K₀ OK V Z H P : Subgroup G}
    {L : Type} [Group L] (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hLs : IsSimpleGroup L ∨ Nat.card L ≤ Nat.card Z)
    (hS : ∃ S, IsSylowOf 2 S K₀ ∧ IsDih S) (hA2 : IsPGroup 2 A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hVA : V ≤ A) (hZA : Z ≤ A) (hV : IsKleinFour V)
    (hK₀V : K₀ ≤ centralizer (V : Set G)) (hOK : OK = O (centralizer (V : Set G)))
    (hOKK₀ : OK ≤ K₀)
    (h1 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H K₀ OK →
      ∃ W : Subgroup G, W ≤ H ⊓ K₀ ∧ Z ≤ W ∧ K₀ ≤ W ⊔ OK ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ OK)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H K₀ OK → ∀ v ∈ V, v ≠ 1 → v ∈ H →
      O H ⊓ C v ≤ O (C v))
    (hHtop : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H K₀ OK)
    (hpc : Sec4Setting.PConstrainedWrt p A H Z) (hmaxH : IsMaxInvIn p A H P) :
    Covers (normalizer (ambientMaxCardZJ P : Set G)) K₀ OK ∧
      ∃ v ∈ V, v ≠ 1 ∧ ∃ Q ≤ P, IsPGroup p Q ∧ A ≤ normalizer (Q : Set G) ∧ Q ≤ O (C v) ∧
        ¬ Z ≤ centralizer (Q : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hOKodd : Odd (Nat.card OK) := hOK ▸ card_O_odd _
  have hPH : P ≤ H := hmaxH.1
  have hPp : IsPGroup p P := hmaxH.2.1
  have hAP : A ≤ normalizer (P : Set G) := hmaxH.2.2.1
  obtain ⟨W, hWHK, hZW, hWcov, hWn, hWint⟩ := h1 H hHtop hAH hcov
  have hWH : W ≤ H := hWHK.trans inf_le_left
  have hWK : W ≤ K₀ := hWHK.trans inf_le_right
  set K₁ : Subgroup G := W ⊔ O H ⊔ P with hK₁
  have hL₀H : W ⊔ O H ≤ H := sup_le hWH (map_subtype_le _)
  have hK₁H : K₁ ≤ H := sup_le hL₀H hPH
  have hWK₁ : W ≤ K₁ := le_sup_left.trans le_sup_left
  have hHL₀ : H ≤ normalizer ((W ⊔ O H : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hL₀H).mp hWn
  have hAK₁ : A ≤ normalizer (K₁ : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_sup _ P ⟨hHL₀ (hAH ha), hAP ha⟩
  have hOHK₁ : O H ≤ O K₁ :=
    G5d.le_O_of_le_normalizer ((le_sup_right.trans le_sup_left : O H ≤ K₁))
      (hK₁H.trans (le_normalizer_O H)) (card_O_odd H)
  have hZQ : ¬ Z ≤ centralizer ((P ⊓ O K₁ : Subgroup G) : Set G) := by
    have hPOH : IsSylowOf p (P ⊓ O H) (O H) :=
      isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAH.trans le_normalizer) hmaxH
    have hAPOH : A ≤ normalizer ((P ⊓ O H : Subgroup G) : Set G) := fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨hAP ha, le_normalizer_O H (hAH ha)⟩
    have h0 := not_le_centralizer_of_pConstrainedWrt hp hA2 hAH hZA hpc hPOH hAPOH
    exact fun hZ => h0 (hZ.trans (centralizer_le (inf_le_inf_left P hOHK₁)))
  have heq2 : K₁ = O K₁ ⊔ (K₁ ⊓ normalizer (ambientMaxCardZJ P : Set G)) :=
    eq_O_sup_inf_normalizer_zj_of_covers hp hp2 f hf hker hLs hS hOKK₀ hOKodd hZA hA2 hAH hWH
      hWK hZW hWcov hWn hWint hmaxH hK₁ hZQ
  set Hs : Subgroup G := normalizer (ambientMaxCardZJ P : Set G) with hHs
  have hAHs : A ≤ Hs := hAP.trans (normalizer_le_normalizer_ambientMaxCardZJ P)
  set Kw : Subgroup G := K₁ ⊔ V with hKw
  have hVK : V ≤ Kw := le_sup_right
  have hKwH : Kw ≤ H := sup_le hK₁H (hVA.trans hAH)
  have hKwtop : Kw ≠ ⊤ := fun h => hHtop (eq_top_iff.mpr (h ▸ hKwH))
  have hOK₁Kw : O K₁ ≤ O Kw := by
    refine G5d.le_O_of_le_normalizer ((map_subtype_le _).trans le_sup_left) (sup_le
      (le_normalizer_O K₁) ?_) (card_O_odd K₁)
    exact fun v hv =>
      ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image
        K₁ (hAK₁ (hVA hv))
  have hKweq : Kw = O Kw ⊔ (Kw ⊓ Hs) := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le (map_subtype_le _) inf_le_left)
    · calc K₁ = O K₁ ⊔ (K₁ ⊓ Hs) := heq2
        _ ≤ O Kw ⊔ (Kw ⊓ Hs) := sup_le_sup hOK₁Kw (inf_le_inf_right _ le_sup_left)
    · exact (le_inf hVK (hVA.trans hAHs)).trans le_sup_right
  have hcovKw : Covers Kw K₀ OK :=
    hWcov.trans (sup_le_sup_right (le_inf (hWK₁.trans le_sup_left) hWK) _)
  have hV1 : ∃ v ∈ V, v ≠ 1 := by
    have := hV
    obtain ⟨x, -, hx, -, -⟩ := exists_pair_ne_of_isKleinFour' (V := V)
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hOKM : O Kw ⊓ centralizer (V : Set G) ≤ O (centralizer (V : Set G)) := by
    obtain ⟨v, hv, hv1⟩ := hV1
    exact O_inf_centralizer_le_of_mem hv (h413 Kw hKwtop hcovKw v hv hv1 (hVK hv))
  have hcovKH : Covers (Kw ⊓ Hs) K₀ OK := by
    have h := G5d.covers_of_eq_O_sup (hA2.to_le hVA) hVK (fun v hv =>
      inf_normalizer_le_normalizer_inf ⟨le_normalizer (hVK hv), le_normalizer (hAHs (hVA hv))⟩)
      inf_le_left hKweq rfl hK₀V (hOK ▸ hOKK₀) hOKM (hOK ▸ hcovKw)
    rwa [← hOK] at h
  refine ⟨covers_mono hcovKH inf_le_right, ?_⟩
  have hQKw : P ⊓ O K₁ ≤ O Kw := inf_le_right.trans hOK₁Kw
  have hQp : IsPGroup p (P ⊓ O K₁ : Subgroup G) := hPp.to_le inf_le_left
  have hAQ : A ≤ normalizer ((P ⊓ O K₁ : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hAP ha,
      ProperTwoGeneratedCore.LocalCriterionDenominator.normalizer_normalizes_oddCore_image
        K₁ (hAK₁ ha)⟩
  have hexv : ∃ v ∈ V, v ≠ 1 ∧
      ¬ Z ≤ centralizer ((P ⊓ O K₁ ⊓ C v : Subgroup G) : Set G) := by
    by_contra hall
    push Not at hall
    exact hZQ (le_centralizer_of_forall_inf_centralizer hV (odd_card_of_isPGroup hp hp2 hQp)
      (hVA.trans hAQ) hall)
  obtain ⟨v, hvV, hv1, hvZ⟩ := hexv
  refine ⟨v, hvV, hv1, P ⊓ O K₁ ⊓ C v, inf_le_left.trans inf_le_left, hQp.to_le inf_le_left,
    fun a ha => inf_normalizer_le_normalizer_inf ⟨hAQ ha,
      le_normalizer (mem_centralizer_singleton_iff.mpr (hAc a ha v (hVA hvV)))⟩,
    fun q hq => h413 Kw hKwtop hcovKw v hvV hv1 (hVK hvV) ⟨hQKw hq.1, hq.2⟩, hvZ⟩

theorem prop_5_2_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A K₀ OK V Z : Subgroup G}
    {L : Type} [Group L] (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hLo : CFSG.oddCore L = ⊥)
    (hLs : IsSimpleGroup L ∨ Nat.card L ≤ Nat.card Z) (hS : ∃ S, IsSylowOf 2 S K₀ ∧ IsDih S)
    (hA2 : IsPGroup 2 A) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hVA : V ≤ A) (hZA : Z ≤ A)
    (hV : IsKleinFour V) (hK₀V : K₀ ≤ centralizer (V : Set G))
    (hOK : OK = O (centralizer (V : Set G))) (hOKK₀ : OK ≤ K₀)
    (hnt : ∀ H : Subgroup G, CFSG.IsPLocal p H → H ≠ ⊤)
    (hinv : normalizer (A : Set G) ≤ normalizer (K₀ : Set G) ⊓ normalizer (OK : Set G) ⊓
      normalizer (Z : Set G))
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h1 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H K₀ OK →
      ∃ W : Subgroup G, W ≤ H ⊓ K₀ ∧ Z ≤ W ∧ K₀ ≤ W ⊔ OK ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ OK)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H K₀ OK → ∀ v ∈ V, v ≠ 1 → v ∈ H →
      O H ⊓ C v ≤ O (C v))
    (hex : ∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H K₀ OK ∧
      Sec4Setting.PConstrainedWrt p A H Z) :
    ∀ P₁ : Subgroup G, IsMaxInvIn p A ⊤ P₁ →
      Sec4Setting.IsPLocalA p A (normalizer (ambientMaxCardZJ P₁ : Set G)) ∧
        Covers (normalizer (ambientMaxCardZJ P₁ : Set G)) K₀ OK ∧
        Sec4Setting.PConstrainedWrt p A (normalizer (ambientMaxCardZJ P₁ : Set G)) Z := by
  have : Fact p.Prime := ⟨hp⟩
  have hAZ : A ≤ normalizer (Z : Set G) := fun a ha => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun z hz => hAc z (hZA hz) a ha)
  obtain ⟨H, P, ⟨hHloc, hAH, hcov, hpc⟩, hPH, hPp, hAP, hmaxpair⟩ :=
    exists_max_pair (p := p) (A := A) (fun H => CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H K₀ OK ∧
      Sec4Setting.PConstrainedWrt p A H Z) hex
  have hHtop := hnt H hHloc
  have hmaxH : IsMaxInvIn p A H P := ⟨hPH, hPp, hAP, fun Q hQH hQp hAQ hPQ =>
    (eq_of_le_of_card_ge hPQ (hmaxpair H Q ⟨hHloc, hAH, hcov, hpc⟩ hQH hQp hAQ)).symm⟩
  obtain ⟨hcovHs, v, hvV, hv1, Q₀, hQ₀P, hQ₀p, hAQ₀, hQ₀v, hvZ⟩ :=
    prop_5_2_cover_core hp hp2 f hf hker hLs hS hA2 hAc hVA hZA hV hK₀V hOK hOKK₀ h1 h413 hHtop
      hAH hcov hpc hmaxH
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    refine hvZ fun z _ => mem_centralizer_iff.mpr fun x hx => ?_
    rw [mem_bot.mp (hQ₀P hx), one_mul, mul_one]
  set Hs : Subgroup G := normalizer (ambientMaxCardZJ P : Set G) with hHs
  have hPHs : P ≤ Hs := le_normalizer.trans (normalizer_le_normalizer_ambientMaxCardZJ P)
  have hAHs : A ≤ Hs := hAP.trans (normalizer_le_normalizer_ambientMaxCardZJ P)
  have hHsloc : CFSG.IsPLocal p Hs := isPLocal_normalizer_ambientMaxCardZJ hp hPp hP1
  have hHstop := hnt Hs hHsloc
  obtain ⟨W', hW'HK, hZW', hW'cov, hW'n, hW'int⟩ := h1 Hs hHstop hAHs hcovHs
  have hpcHs : Sec4Setting.PConstrainedWrt p A Hs Z :=
    pConstrainedWrt_of_le_O_C hp hp2 hA2 f hf hker hLo hOKK₀ hAHs (hW'HK.trans inf_le_left)
      (hW'HK.trans inf_le_right) hW'cov hW'n hW'int hZA hAZ hZW'
      (hK₀V.trans (centralizer_le (Set.singleton_subset_iff.mpr hvV))) (hQ₀P.trans hPHs) hQ₀p
      hAQ₀ hQ₀v hvZ
  have hmaxG : IsMaxInvIn p A ⊤ P := by
    refine ⟨le_top, hPp, hAP, fun Q _ hQp hAQ' hPQ => ?_⟩
    have hRHs : Q ⊓ normalizer (P : Set G) ≤ Hs :=
      inf_le_right.trans (normalizer_le_normalizer_ambientMaxCardZJ P)
    have hAR : A ≤ normalizer ((Q ⊓ normalizer (P : Set G) : Subgroup G) : Set G) := fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨hAQ' ha, le_normalizer (hAP ha)⟩
    have hcard := hmaxpair Hs _ ⟨hHsloc, hAHs, hcovHs, hpcHs⟩ hRHs (hQp.to_le inf_le_left) hAR
    have hPR : P ≤ Q ⊓ normalizer (P : Set G) := le_inf hPQ le_normalizer
    have hRP := eq_of_le_of_card_ge hPR hcard
    exact (eq_of_inf_normalizer_le hQp hPQ hRP.ge).symm
  intro P₁ hP₁
  obtain ⟨u, hu, hPu⟩ := h46 P P₁ hmaxG hP₁
  have hZJu : ambientMaxCardZJ P₁ = (ambientMaxCardZJ P).map (MulAut.conj u).toMonoidHom := by
    rw [← hPu, map_ambientMaxCardZJ_of_injective _ _
      ((MulAut.conj u).injective.comp P.subtype_injective)]
  have hHs₁ : normalizer (ambientMaxCardZJ P₁ : Set G) = Hs.map (MulAut.conj u).toMonoidHom := by
    rw [hZJu, hHs, map_equiv_normalizer_eq]
  have hP₁1 : P₁ ≠ ⊥ := by
    rw [← hPu, Ne, map_eq_bot_iff_of_injective _ (MulAut.conj u).injective]
    exact hP1
  have huK₀ : K₀.map (MulAut.conj u).toMonoidHom = K₀ :=
    G4b.mem_normalizer_iff_map_conj_eq'.mp (hinv hu).1.1
  have huOK : OK.map (MulAut.conj u).toMonoidHom = OK :=
    G4b.mem_normalizer_iff_map_conj_eq'.mp (hinv hu).1.2
  have huZ : Z.map (MulAut.conj u).toMonoidHom = Z :=
    G4b.mem_normalizer_iff_map_conj_eq'.mp (hinv hu).2
  refine ⟨⟨isPLocal_normalizer_ambientMaxCardZJ hp hP₁.2.1 hP₁1,
    hP₁.2.2.1.trans (normalizer_le_normalizer_ambientMaxCardZJ P₁), P₁, hP₁,
    le_normalizer.trans (normalizer_le_normalizer_ambientMaxCardZJ P₁)⟩, ?_, ?_⟩
  · rw [hHs₁]
    have h := G5d.covers_map_conj hcovHs u
    rwa [huK₀, huOK] at h
  · rw [hHs₁]
    exact pConstrainedWrt_map_conj hpcHs hu huZ

end Core

end G5a

namespace Sec5Roles

open G5a

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A)

omit [Finite G] in
private theorem isSimpleGroup_or_card_le {L : Type} [Group L] {Z : Subgroup G}
    (hZ : IsKleinFour Z) (hL : IsL2OrA7 L 5 ∨ IsKleinFour L) :
    IsSimpleGroup L ∨ Nat.card L ≤ Nat.card Z := by
  rcases hL with h | h
  · exact Or.inl (isSimpleGroup_of_isL2OrA7 le_rfl h)
  · right
    have := h
    have := hZ
    rw [IsKleinFour.card_four (G := L), IsKleinFour.card_four (G := ↥Z)]

theorem prop_5_2_cover_first_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    ∀ H F : Subgroup G, CFSG.IsPLocal p H → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      Sec4Setting.PConstrainedWrt p A H ρ.Y → IsMaxInvIn p A H F →
      Covers (normalizer (CFSG.ambientMaxCardZJ F : Set G)) ρ.M₀ (O ρ.M) := by
  intro H F hHloc hAH hcov hpc hF
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  exact (prop_5_2_cover_core hp hp2 f hf hker (isSimpleGroup_or_card_le ρ.isKleinFour_Y hL)
    ⟨ρ.S₂, h47.2.1, ρ.dih₂⟩ ρ.isPGroup_A (fun a ha b hb => ρ.comm ha hb) ρ.X_le_A ρ.Y_le_A
    ρ.isKleinFour_X ρ.M₀_le rfl ρ.O_M_le_M₀
    (fun H hH hAH hc => by
      obtain ⟨W, h₁, h₂, h₃, -, h₅, h₆, -⟩ := h1M H hH hAH hc
      exact ⟨W, h₁, h₂, h₃.trans (sup_le_sup_right inf_le_left _), h₅, h₆⟩)
    (fun H hH hc => (h413 H hH).1 hc) (ρ.ne_top_of_isPLocal hp hp2 hHloc) hAH hcov hpc hF).1

theorem prop_5_2_first_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.M₀ (O ρ.M) ∧
        Sec4Setting.PConstrainedWrt p A H ρ.Y) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y := by
  intro hex P hP
  obtain ⟨L, _, f, hf, hker, hL⟩ := h47.1
  have : Finite L := Finite.of_surjective f hf
  have h := prop_5_2_core hp hp2 f hf hker (oddCore_eq_bot_of_isL2OrA7_or_isKleinFour le_rfl hL)
    (isSimpleGroup_or_card_le ρ.isKleinFour_Y hL) ⟨ρ.S₂, h47.2.1, ρ.dih₂⟩ ρ.isPGroup_A
    (fun a ha b hb => ρ.comm ha hb) ρ.X_le_A ρ.Y_le_A ρ.isKleinFour_X ρ.M₀_le rfl ρ.O_M_le_M₀
    (fun H hH => ρ.ne_top_of_isPLocal hp hp2 hH)
    (fun u hu => ⟨⟨ρ.normalizer_le_normalizer_M₀ hu, ρ.normalizer_le_normalizer_O_M hu⟩,
      ρ.normalizer_le_normalizer_Y hu⟩)
    h46 (fun H hH hAH hc => by
      obtain ⟨W, h₁, h₂, h₃, -, h₅, h₆, -⟩ := h1M H hH hAH hc
      exact ⟨W, h₁, h₂, h₃.trans (sup_le_sup_right inf_le_left _), h₅, h₆⟩)
    (fun H hH hc => (h413 H hH).1 hc) hex P hP
  exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

theorem prop_5_2_second_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.N₀ (O ρ.N) ∧
        Sec4Setting.PConstrainedWrt p A H ρ.X) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        ρ.IsCoveringSecond p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.X :=
  ρ.swap.prop_5_2_first_of hp hp2 h46 h1N h48 fun H hH => (h413 H hH).symm

theorem prop_5_2_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₂ ρ.M₀ ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (A : Set G)) ∧
      ρ.M = ρ.M₀ ⊔ (ρ.M ⊓ normalizer (ρ.S₂ : Set G)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → O2 (C x) = (O2 ρ.M ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ ρ.X, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (ρ.M₀ ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs ρ.N₀ (O ρ.N) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 ρ.S₁ ρ.N₀ ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (A : Set G)) ∧
      ρ.N = ρ.N₀ ⊔ (ρ.N ⊓ normalizer (ρ.S₁ : Set G)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → O2 (C y) = (O2 ρ.N ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ ρ.Y, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (ρ.N₀ ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.M₀ (O ρ.M) ∧
         Sec4Setting.PConstrainedWrt p A H ρ.Y) →
       ∀ P, IsMaxInvIn p A ⊤ P →
         ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
           Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y) ∧
    ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.N₀ (O ρ.N) ∧
         Sec4Setting.PConstrainedWrt p A H ρ.X) →
       ∀ P, IsMaxInvIn p A ⊤ P →
         ρ.IsCoveringSecond p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
           Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.X) :=
  ⟨ρ.prop_5_2_first_of hp hp2 h46 h1M h47 h413, ρ.prop_5_2_second_of hp hp2 h46 h1N h48 h413⟩

theorem lemma_5_5_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h52 : (∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.M₀ (O ρ.M) ∧
          Sec4Setting.PConstrainedWrt p A H ρ.Y) →
        ∀ P, IsMaxInvIn p A ⊤ P →
          ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
            Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y)
    (x : G) (hx : x ∈ ρ.X) (_hx1 : x ≠ 1)
    (hCx : Sec4Setting.PConstrainedWrt p A (C x) ρ.Y) (P : Subgroup G)
    (hP : IsMaxInvIn p A ⊤ P) :
    ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
      Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y := by
  obtain ⟨H, hHloc, hAH, hcov, hpc⟩ := G5d.exists_pLocal_covers_of_pConstrainedWrt hp hp2
    ρ.isPGroup_A (fun a ha b hb => ρ.comm ha hb) ρ.X_le_A hx ρ.M₀_le ρ.O_M_le_M₀ hCx
  exact h52 ⟨H, hHloc, hAH, hcov, hpc⟩ P hP

theorem lemma_5_6_of {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h52 : ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.M₀ (O ρ.M) ∧
           Sec4Setting.PConstrainedWrt p A H ρ.Y) →
         ∀ P, IsMaxInvIn p A ⊤ P →
           ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
             Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y) ∧
      ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H ρ.N₀ (O ρ.N) ∧
           Sec4Setting.PConstrainedWrt p A H ρ.X) →
         ∀ P, IsMaxInvIn p A ⊤ P →
           ρ.IsCoveringSecond p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
             Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.X))
    (x : G) (hx : x ∈ ρ.X) (hx1 : x ≠ 1)
    (hCx : Sec4Setting.PConstrainedWrt p A (C x) ρ.Y) (hno : ¬ ∃ H, ρ.IsCovering p H) :
    ∀ K, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
      ¬ Sec4Setting.PConstrainedWrt p A K ρ.X := by
  intro K hK hAK hcovK hpcK
  obtain ⟨P, hP⟩ := exists_isMaxInvIn_top (G := G) p A
  obtain ⟨⟨hloc, hcovM⟩, -⟩ := ρ.lemma_5_5_of hp hp2 h52.1 x hx hx1 hCx P hP
  obtain ⟨⟨-, hcovN⟩, -⟩ := h52.2 ⟨K, hK, hAK, hcovK, hpcK⟩ P hP
  exact hno ⟨_, hloc, hcovM, hcovN⟩

end Sec5Roles

namespace Sec4Setting

open G5a

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

section Prop52

variable (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
include hAS hA hp hp2

theorem prop_5_2_of
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h1M : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.M₀ A) (O (𝔖.M A)) →
      ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.M₀ A ∧ 𝔖.Y A ≤ W ∧ Covers W (𝔖.M₀ A) (O (𝔖.M A)) ∧
        H ⊓ 𝔖.M₀ A ≤ W ⊔ (H ⊓ O (𝔖.M A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O (𝔖.M A) ∧ IsL2OrA7 (bar H W) 7 ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O (𝔖.M A)) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H (𝔖.N₀ A) (O (𝔖.N A)) →
      ∃ W : Subgroup G, W ≤ H ⊓ 𝔖.N₀ A ∧ 𝔖.X A ≤ W ∧ Covers W (𝔖.N₀ A) (O (𝔖.N A)) ∧
        H ⊓ 𝔖.N₀ A ≤ W ⊔ (H ⊓ O (𝔖.N A)) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O (𝔖.N A) ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H (𝔖.X A) ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O (𝔖.N A)) ≤ centralizer (bar H A : Set (Bar H)))
    (h47 : QuotIs (𝔖.M₀ A) (O (𝔖.M A)) (fun L _ => IsL2OrA7 L 7) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₂ (𝔖.M₀ A) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (A : Set G)) ∧
      𝔖.M A = 𝔖.M₀ A ⊔ (𝔖.M A ⊓ normalizer (𝔖.S₂ : Set G)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → O2 (C x) = (O2 (𝔖.M A) ⊓ O2 (C x)) ⊔ O (C x)) ∧
      (∀ x ∈ 𝔖.X A, x ≠ 1 → ⁅O2 (C x), O2 (C x)⁆ ⊔ O (C x) =
        (𝔖.M₀ A ⊓ ⁅O2 (C x), O2 (C x)⁆) ⊔ O (C x)))
    (h48 : QuotIs (𝔖.N₀ A) (O (𝔖.N A)) (fun L _ => IsL2OrA7 L 5 ∨ IsKleinFour L) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 𝔖.S₁ (𝔖.N₀ A) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (A : Set G)) ∧
      𝔖.N A = 𝔖.N₀ A ⊔ (𝔖.N A ⊓ normalizer (𝔖.S₁ : Set G)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → O2 (C y) = (O2 (𝔖.N A) ⊓ O2 (C y)) ⊔ O (C y)) ∧
      (∀ y ∈ 𝔖.Y A, y ≠ 1 → ⁅O2 (C y), O2 (C y)⁆ ⊔ O (C y) =
        (𝔖.N₀ A ⊓ ⁅O2 (C y), O2 (C y)⁆) ⊔ O (C y)))
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H (𝔖.M₀ A) (O (𝔖.M A)) → ∀ x ∈ 𝔖.X A, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H (𝔖.N₀ A) (O (𝔖.N A)) → ∀ y ∈ 𝔖.Y A, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y))) :
    ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H (𝔖.M₀ A) (O (𝔖.M A)) ∧
        PConstrainedWrt p A H (𝔖.Y A)) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        𝔖.IsCoveringFirst p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) (𝔖.Y A)) ∧
    ((∃ H, CFSG.IsPLocal p H ∧ A ≤ H ∧ Covers H (𝔖.N₀ A) (O (𝔖.N A)) ∧
        PConstrainedWrt p A H (𝔖.X A)) →
      ∀ P, IsMaxInvIn p A ⊤ P →
        𝔖.IsCoveringSecond p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) (𝔖.X A)) :=
  (𝔖.sec5Roles hAS hA).prop_5_2_of hp hp2 h46 (sec5_one_M_weaken 𝔖 h1M) h1N
    (lemma_4_7_weaken 𝔖 h47) h48 h413
end Prop52

end Sec4Setting

end CFSG.GH72
