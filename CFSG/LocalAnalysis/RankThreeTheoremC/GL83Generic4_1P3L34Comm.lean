module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartOne.K1327.Trick

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem l34c_mem_normalizer_iSup {ι : Type} {H : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ normalizer (H i : Set G)) :
    g ∈ normalizer ((⨆ i, H i : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  exact iSup_congr fun i => mem_normalizer_iff_map_conj_eq.mp (h i)

private theorem l34c_mem_normalizer_sup {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ normalizer (H₁ : Set G)) (h₂ : g ∈ normalizer (H₂ : Set G)) :
    g ∈ normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp h₁,
    mem_normalizer_iff_map_conj_eq.mp h₂]

private theorem l34c_mem_normalizer_inf {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ normalizer (H₁ : Set G)) (h₂ : g ∈ normalizer (H₂ : Set G)) :
    g ∈ normalizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at h₁ h₂ ⊢
  intro h
  simpa only [SetLike.mem_coe, mem_inf] using and_congr (h₁ h) (h₂ h)

private theorem l34c_le_of_le_sup_commutator [Finite G] {p : ℕ} [Fact p.Prime]
    {K H : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) (hle : K ≤ H ⊔ ⁅K, K⁆) : K ≤ H := by
  have : Fact (IsPGroup p K) := ⟨hK⟩
  have hKK : ⁅K, K⁆ ≤ K :=
    CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized K K le_normalizer
  have hcomm : (⁅K, K⁆ : Subgroup G).subgroupOf K = _root_.commutator K := by
    have hmap : ⁅K, K⁆ = (_root_.commutator K).map K.subtype := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rw [hmap]
    exact comap_map_eq_self_of_injective K.subtype_injective _
  have htop : H.subgroupOf K ⊔ frattini K = ⊤ := by
    refine top_le_iff.mp ?_
    calc (⊤ : Subgroup K) = (H ⊔ ⁅K, K⁆).subgroupOf K := (subgroupOf_eq_top.mpr hle).symm
      _ = H.subgroupOf K ⊔ _root_.commutator K := by rw [subgroupOf_sup hHK hKK, hcomm]
      _ ≤ H.subgroupOf K ⊔ frattini K :=
        sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := p)) _
  exact subgroupOf_eq_top.mp (CFSG.lemma_1_7_a (p := p) _ htop)

private theorem l34c_le_of_commutator_eq [Finite G] {p : ℕ} [Fact p.Prime] {K A H : Subgroup G}
    (hK : IsPGroup p K) (hAK : A ≤ normalizer (K : Set G)) (hKA : ⁅K, A⁆ = K) (hHK : H ≤ K)
    (hAH : A ≤ normalizer (H : Set G)) (hgen : K ≤ K ⊓ centralizer (A : Set G) ⊔ H) :
    K ≤ H := by
  set D : Subgroup G := H ⊔ ⁅K, K⁆
  have hKK : ⁅K, K⁆ ≤ K :=
    CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized K K le_normalizer
  have hDK : D ≤ K := sup_le hHK hKK
  have hAD : ∀ a ∈ A, ∀ d ∈ D, a * d * a⁻¹ ∈ D := fun a ha d hd =>
    (mem_normalizer_iff.mp (l34c_mem_normalizer_sup (hAH ha)
      (CFSG.LargeEvenClassification.Helpers.normalizes_commutator_pair A K K hAK hAK ha)) d).mp hd
  have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ ∈ D := by
    intro k hk d hd
    have he : k * d * k⁻¹ = ⁅k, d⁆ * d := by rw [commutatorElement_def]; group
    rw [he]
    exact D.mul_mem (le_sup_right (a := H) (commutator_mem_commutator hk (hDK hd))) hd
  let T : Subgroup G :=
    { carrier := {k | k ∈ K ∧ ∀ a ∈ A, ⁅k, a⁆ ∈ D}
      mul_mem' := by
        rintro k₁ k₂ ⟨hk₁, h₁⟩ ⟨hk₂, h₂⟩
        refine ⟨K.mul_mem hk₁ hk₂, fun a ha => ?_⟩
        have he : ⁅k₁ * k₂, a⁆ = k₁ * ⁅k₂, a⁆ * k₁⁻¹ * ⁅k₁, a⁆ := by
          simp only [commutatorElement_def]; group
        rw [he]
        exact D.mul_mem (hKD k₁ hk₁ _ (h₂ a ha)) (h₁ a ha)
      one_mem' := ⟨K.one_mem, fun a _ => by rw [commutatorElement_one_left]; exact D.one_mem⟩
      inv_mem' := by
        rintro k ⟨hk, h⟩
        refine ⟨K.inv_mem hk, fun a ha => ?_⟩
        have he : ⁅k⁻¹, a⁆ = k⁻¹ * ⁅k, a⁆⁻¹ * k⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [he]
        exact hKD _ (K.inv_mem hk) _ (D.inv_mem (h a ha)) }
  have hT : K ≤ T := by
    refine hgen.trans (sup_le ?_ ?_)
    · rintro k ⟨hk, hkc⟩
      refine ⟨hk, fun a ha => ?_⟩
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hkc a ha).symm]
      exact D.one_mem
    · intro h hh
      refine ⟨hHK hh, fun a ha => ?_⟩
      have he : ⁅h, a⁆ = h * (a * h⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      rw [he]
      have hhD : h ∈ D := le_sup_left (b := ⁅K, K⁆) hh
      exact D.mul_mem hhD (hAD a ha _ (D.inv_mem hhD))
  have hKD' : K ≤ D := hKA.ge.trans (commutator_le.mpr fun k hk a ha => (hT hk).2 a ha)
  exact l34c_le_of_le_sup_commutator hK hHK hKD'

theorem l34_stepF [Finite G] {S₁ U M : Subgroup G} {x : G} (hS₁ : IsPGroup 2 S₁)
    (hU : ∀ g ∈ U, g ^ 3 = 1) (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hUc : Nat.card U = 3 ^ 2) (hxU : x ∈ U) (hUS : U ≤ normalizer (S₁ : Set G))
    (hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M) :
    ⁅S₁, zpowers x⁆ ≤ M ∧ ⁅S₁ ⊓ M, zpowers x⁆ = ⁅S₁, zpowers x⁆ ∧
      S₁ ≤ normalizer ((⁅S₁ ⊓ M, zpowers x⁆ : Subgroup G) : Set G) := by
  have hxS : zpowers x ≤ normalizer (S₁ : Set G) := zpowers_le.mpr (hUS hxU)
  have hS3 : ¬ 3 ∣ Nat.card S₁ := by
    obtain ⟨n, hn⟩ := hS₁.exists_card_eq
    rw [hn]
    intro h
    have := Nat.le_of_dvd (by norm_num) (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hx3 : IsPGroup 3 (zpowers x) := fun g =>
    ⟨1, Subtype.ext (by simpa using hU g (zpowers_le.mpr hxU g.2))⟩
  have hKK := CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
    Nat.prime_three (zpowers x) S₁ hx3 hS3 hxS
  set K : Subgroup G := ⁅S₁, zpowers x⁆
  have hKS : K ≤ S₁ := CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized S₁ _ hxS
  have hUx : U ≤ normalizer (zpowers x : Set G) := by
    intro u hu
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (hUab x hxU u hu) k).eq
  have hUK : U ≤ normalizer (K : Set G) :=
    CFSG.LargeEvenClassification.Helpers.normalizes_commutator_pair U S₁ (zpowers x) hUS hUx
  have hK3 : ¬ 3 ∣ Nat.card K := fun h => hS3 (h.trans (card_dvd_of_le hKS))
  have hUe : CFSG.Open.IsElemAbelian 3 U :=
    ⟨⟨⟨fun a b => Subtype.ext (hUab a a.2 b b.2)⟩⟩, hU⟩
  have hgen0 := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers Nat.prime_three hUe hUc hUK hK3
  set H : Subgroup G :=
    ⨆ u : {u : G // u ∈ U ∧ u ∉ zpowers x}, K ⊓ centralizer ({u.1} : Set G)
  have hHK : H ≤ K := iSup_le fun u => inf_le_left
  have hHM : H ≤ M := iSup_le fun u => inf_le_right.trans (hC u.1 u.2.1 u.2.2)
  have hxH : zpowers x ≤ normalizer (H : Set G) := by
    refine zpowers_le.mpr (l34c_mem_normalizer_iSup fun u =>
      l34c_mem_normalizer_inf (hUK hxU) (le_normalizer ?_))
    exact mem_centralizer_singleton_iff.mpr (hUab x hxU u.1 u.2.1)
  have hgen : K ≤ K ⊓ centralizer (zpowers x : Set G) ⊔ H := by
    refine hgen0.trans (iSup_le fun b => ?_)
    by_cases hb : ((b.1 : U) : G) ∈ zpowers x
    · refine le_sup_of_le_left (inf_le_inf_left K ?_)
      have hb1 : ((b.1 : U) : G) ≠ 1 := fun h => b.2 (Subtype.ext h)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, zpowers_one_eq_bot, mem_bot] at hb
        exact hb1 hb
      have hzb : zpowers ((b.1 : U) : G) = zpowers x := by
        refine eq_of_le_of_card_ge (zpowers_le.mpr hb) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime (hU x hxU) hx1,
          orderOf_eq_prime (hU _ b.1.2) hb1]
      rw [← hzb, zpowers_eq_closure, centralizer_closure]
    · exact le_sup_of_le_right (le_iSup_of_le ⟨b.1, b.1.2, hb⟩ le_rfl)
  have hKH : K ≤ H :=
    l34c_le_of_commutator_eq (p := 2) (hS₁.to_le hKS) ((zpowers_le.mpr hxU).trans hUK) hKK
      hHK hxH hgen
  have ha : K ≤ M := hKH.trans hHM
  have hb : ⁅S₁ ⊓ M, zpowers x⁆ = K :=
    le_antisymm (commutator_mono inf_le_left le_rfl)
      (hKK.ge.trans (commutator_mono (le_inf hKS ha) le_rfl))
  refine ⟨ha, hb, ?_⟩
  rw [hb]
  exact normalizer_commutator_ge_left S₁ (zpowers x)

end CFSG.LocalAnalysis.RankThreeTheoremC
