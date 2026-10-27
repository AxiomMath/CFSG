module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3GlueC
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma64Glue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

variable {G : Type} [Group G] {L : Subgroup G} {z t : G} {T : Subgroup G}

theorem mem_zpowers_sup_iff_outer {L : Subgroup G} {z β : G} (hzL : z ∈ centralizer (L : Set G))
    (hz : z ∈ centralizer ({β} : Set G)) (k : ↥(centralizer ({β} : Set G))) :
    k ∈ zpowers (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) ⊔
      (L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) ↔
      (k : G) ∈ L ⊔ zpowers z := by
  have hzβ : z * β = β * z := mem_centralizer_singleton_iff.1 hz
  constructor
  · intro hk
    have hle : zpowers (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) ⊔
        (L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) ≤
        (L ⊔ zpowers z).comap (centralizer ({β} : Set G)).subtype :=
      sup_le (zpowers_le.2 (mem_comap.2 (mem_sup_right (mem_zpowers z))))
        (fun d hd => mem_comap.2 (mem_sup_left (mem_subgroupOf.1 hd).1))
    exact mem_comap.1 (hle hk)
  · intro hx
    obtain ⟨a, ha, c, hc, hkac⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le.2 hzL) hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hc
    have hcK : z ^ j ∈ centralizer ({β} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact (Commute.zpow_left (show Commute z β from hzβ) j).eq
    have haK : a ∈ centralizer ({β} : Set G) := by
      have : a = (k : G) * (z ^ j)⁻¹ := by rw [hkac]; group
      rw [this]
      exact mul_mem k.2 (inv_mem hcK)
    have hke : k = (⟨a, haK⟩ : ↥(centralizer ({β} : Set G))) *
        (⟨z, hz⟩ : ↥(centralizer ({β} : Set G))) ^ j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
      exact hkac
    rw [hke]
    exact mul_mem (mem_sup_right (mem_subgroupOf.2 ⟨ha, haK⟩))
      (mem_sup_left (zpow_mem (mem_zpowers _) j))

variable [Finite G]

theorem m10Config_of_outerConfig (cfg : OuterConfig G L z t T) {β : G}
    (hD : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)))
    (hO : fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β)
    (hM1 : ∃ c ∈ centralizer ({z} : Set G), c * β = β * c ∧ c ∉ L ⊔ zpowers z)
    (hM2 : ∀ c ∈ centralizer ({z} : Set G), c * β = β * c → c * c ∈ zpowers z ⊔ zpowers β →
      c ∈ L ⊔ zpowers z)
    (hS : ∃ s : G, s * β = β * s ∧ z * s * z⁻¹ * s⁻¹ ≠ 1 ∧
      ∃ n : ℕ, (z * s * z⁻¹ * s⁻¹) ^ (2 ^ n) = 1)
    (hz : z ∈ centralizer ({β} : Set G)) :
    M10Config (⟨z, hz⟩ : ↥(centralizer ({β} : Set G)))
      ((L ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) := by
  set K : Subgroup G := centralizer ({β} : Set G) with hKdef
  set zK : ↥K := ⟨z, hz⟩ with hzK
  set DK : Subgroup ↥K := (L ⊓ K).subgroupOf K with hDK
  have hcommβ : ∀ x : ↥K, (x : G) * β = β * x := fun x => mem_centralizer_singleton_iff.1 x.2
  have hzβ : z * β = β * z := mem_centralizer_singleton_iff.1 hz
  have T1 : ∀ k : ↥K, k ∈ zpowers zK ⊔ DK ↔ (k : G) ∈ L ⊔ zpowers z :=
    mem_zpowers_sup_iff_outer cfg.z_cent hz
  have hmemC : ∀ k : ↥K, k ∈ centralizer ({zK} : Set ↥K) ↔ (k : G) ∈ centralizer ({z} : Set G) := by
    intro k
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h1
      exact congrArg Subtype.val h1
    · intro h1
      exact Subtype.ext h1
  let e : DK ≃* ↥(L ⊓ K) := Subgroup.subgroupOfEquivOfLe (inf_le_right : L ⊓ K ≤ K)
  have hmap : (fusionOddCore DK).map e.toMonoidHom = fusionOddCore ↥(L ⊓ K) :=
    map_fusionOddCore_mulEquiv e
  have hOK : ∀ y ∈ fusionOddCore DK, ((y : ↥K) : G) ∈ zpowers β := by
    intro y hy
    have h1 : e y ∈ fusionOddCore ↥(L ⊓ K) := hmap ▸ ⟨y, hy, rfl⟩
    exact hO ⟨e y, h1, rfl⟩
  refine
  { z_order := ?_
    disjoint := ?_
    z_comm := ?_
    odd_central := ?_
    quot := ?_
    index_two := ?_
    no_outer := ?_
    noncentral := ?_ }
  · rw [← Subgroup.orderOf_coe]
    exact cfg.z_order
  · rw [Subgroup.disjoint_def]
    intro x hxz hxD
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hxz
    have h1 : z ^ k ∈ L := by
      have := (mem_subgroupOf.1 hxD).1
      simpa [hzK] using this
    have h2 : z ^ k ∈ L ⊓ zpowers z := ⟨h1, mem_zpowers_iff.2 ⟨k, rfl⟩⟩
    rw [cfg.disjoint.eq_bot, mem_bot] at h2
    apply Subtype.ext
    simpa [hzK] using h2
  · intro d hd
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hzK]
    exact cfg.z_comm_of_mem_A (mem_subgroupOf.1 hd).1
  ·
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_center_iff]
    intro g
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hOK y hy)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    show (g : G) * ((y : ↥K) : G) = ((y : ↥K) : G) * g
    rw [← hj]
    exact (Commute.zpow_right (show Commute (g : G) β from hcommβ g) j).eq
  · obtain ⟨eD⟩ := hD
    exact ⟨(QuotientGroup.congr (fusionOddCore DK) (fusionOddCore ↥(L ⊓ K)) e hmap).trans eD⟩
  ·
    obtain ⟨c, hcz, hcβ, hcL⟩ := hM1
    have hN₀ : ((L ⊔ zpowers z).subgroupOf (centralizer ({z} : Set G))).index = 2 :=
      cfg.index_two
    rw [Subgroup.index_eq_two_iff]
    have hcK : c ∈ K := by rw [hKdef, mem_centralizer_singleton_iff]; exact hcβ
    refine ⟨⟨⟨c, hcK⟩, (hmemC ⟨c, hcK⟩).2 hcz⟩, fun b => ?_⟩
    have hb := (hmemC b.1).1 b.2
    have key : ((b : G) * c ∈ L ⊔ zpowers z) ↔
        ((b : G) ∈ L ⊔ zpowers z ↔ c ∈ L ⊔ zpowers z) :=
      Subgroup.mul_mem_iff_of_index_two hN₀ (a := ⟨(b : G), hb⟩) (b := ⟨c, hcz⟩)
    show Xor ((b * (⟨⟨c, hcK⟩, (hmemC ⟨c, hcK⟩).2 hcz⟩ : ↥(centralizer ({zK} : Set ↥K)))).1 ∈
      zpowers zK ⊔ DK) (b.1 ∈ zpowers zK ⊔ DK)
    rw [T1, T1]
    have e1 : (((b * (⟨⟨c, hcK⟩, (hmemC ⟨c, hcK⟩).2 hcz⟩ : ↥(centralizer ({zK} : Set ↥K)))).1 :
        ↥K) : G) = (b : G) * c := rfl
    rw [e1]
    by_cases hbL : ((b.1 : ↥K) : G) ∈ L ⊔ zpowers z
    · refine Or.inr ⟨hbL, ?_⟩
      intro hbc
      exact hcL ((key.1 hbc).1 hbL)
    · refine Or.inl ⟨key.2 ⟨fun h1 => absurd h1 hbL, fun h2 => absurd h2 hcL⟩, hbL⟩
  · intro c hc hcc
    have hcG : (c : G) ∈ centralizer ({z} : Set G) := (hmemC c).1 hc
    have hP : zpowers zK ⊔ fusionOddCoreOf DK ≤ (zpowers z ⊔ zpowers β).comap K.subtype := by
      refine sup_le (zpowers_le.2 (mem_comap.2 (mem_sup_left (mem_zpowers z)))) ?_
      rintro _ ⟨y, hy, rfl⟩
      exact mem_comap.2 (mem_sup_right (hOK y hy))
    have h1 : (c : G) * c ∈ zpowers z ⊔ zpowers β := mem_comap.1 (hP hcc)
    exact (T1 c).2 (hM2 c hcG (hcommβ c) h1)
  · obtain ⟨s, hsβ, hs1, n, hsn⟩ := hS
    have hsK : s ∈ K := by rw [hKdef, mem_centralizer_singleton_iff]; exact hsβ
    refine ⟨⟨s, hsK⟩, fun h1 => hs1 (congrArg Subtype.val h1), n, ?_⟩
    apply Subtype.ext
    simpa [hzK] using hsn

theorem lemma96_of_outerConfig (hSol : SolomonM10) (cfg : OuterConfig G L z t T) {β : G}
    (hKG : CFSG.SectionRank.IsKGroupCat ↥(centralizer ({β} : Set G))) (hβL : β ∈ L)
    (hD : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)))
    (hO : fusionOddCoreOf (L ⊓ centralizer ({β} : Set G)) ≤ zpowers β)
    (hM1 : ∃ c ∈ centralizer ({z} : Set G), c * β = β * c ∧ c ∉ L ⊔ zpowers z)
    (hM2 : ∀ c ∈ centralizer ({z} : Set G), c * β = β * c → c * c ∈ zpowers z ⊔ zpowers β →
      c ∈ L ⊔ zpowers z)
    (hS : ∃ s : G, s * β = β * s ∧ z * s * z⁻¹ * s⁻¹ ≠ 1 ∧
      ∃ n : ℕ, (z * s * z⁻¹ * s⁻¹) ^ (2 ^ n) = 1) :
    ∃ hz : z ∈ centralizer ({β} : Set G),
      Lemma96Conclusion ↥(centralizer ({β} : Set G))
        (QuotientGroup.mk (⟨z, hz⟩ : ↥(centralizer ({β} : Set G)))) ∧
      ∃ c ∈ centralizer ({z} : Set G), c * β = β * c ∧ c ∉ L ⊔ zpowers z ∧ c * c ∈ L := by
  have hz : z ∈ centralizer ({β} : Set G) :=
    mem_centralizer_singleton_iff.2 (cfg.z_comm_of_mem_A hβL).symm
  obtain ⟨hconc, c, hc, hcC, hcc⟩ :=
    lemma96_of_solomon (m10Config_of_outerConfig cfg hD hO hM1 hM2 hS hz) hSol hKG
  refine ⟨hz, hconc, (c : G), ?_, ?_, ?_, (mem_subgroupOf.1 hcc).1⟩
  · exact mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hc))
  · exact mem_centralizer_singleton_iff.1 c.2
  · exact fun hh => hcC ((mem_zpowers_sup_iff_outer cfg.z_cent hz c).2 hh)

end CFSG.EvenSporadicStandard.Fin76b
