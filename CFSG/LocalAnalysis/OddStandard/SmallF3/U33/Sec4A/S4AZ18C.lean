module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem z18_grow {V K D : Subgroup G} (hV : IsPGroup 2 V) (hKD : K < D) (hDV : D ≤ V) {t : G}
    (htV : t ∈ V) (htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K) :
    ∃ z ∈ D, z ∉ K ∧ (∀ k ∈ K, z * k * z⁻¹ ∈ K) ∧ ∃ k ∈ K, t * z * t⁻¹ = z * k := by
  have hD2 : IsPGroup 2 D := hV.to_le hDV
  obtain ⟨n₀, hn₀D, hn₀N, hn₀K⟩ := exists_mem_normalizer_not_mem hD2 hKD
  have htN : t ∈ normalizer (K : Set G) := mem_normalizer_of_conj_mem htK
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = D ⊓ normalizer (K : Set G) := ⟨_, rfl⟩
  have hn₀N' : n₀ ∈ N := by
    rw [hNdef]
    exact Subgroup.mem_inf.mpr ⟨hn₀D, hn₀N⟩
  have htNN : ∀ n ∈ N, t * n * t⁻¹ ∈ N := by
    intro n hn
    rw [hNdef] at hn ⊢
    obtain ⟨hnD, hnK⟩ := Subgroup.mem_inf.mp hn
    exact Subgroup.mem_inf.mpr ⟨htD n hnD, ((normalizer (K : Set G)).mul_mem
      ((normalizer (K : Set G)).mul_mem htN hnK) ((normalizer (K : Set G)).inv_mem htN))⟩
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = N ⊔ zpowers t := ⟨_, rfl⟩
  have hNH : N ≤ H := hHdef ▸ le_sup_left
  have htH : t ∈ H := hHdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hND : N ≤ D := by
    rw [hNdef]
    exact inf_le_left
  have hHV : H ≤ V := by
    rw [hHdef]
    exact sup_le (hND.trans hDV) (Subgroup.zpowers_le.mpr htV)
  have hHK : H ≤ normalizer (K : Set G) := by
    rw [hHdef]
    refine sup_le ?_ (Subgroup.zpowers_le.mpr htN)
    rw [hNdef]
    exact inf_le_right
  have hHN : H ≤ normalizer (N : Set G) := by
    rw [hHdef]
    exact sup_le Subgroup.le_normalizer
      (Subgroup.zpowers_le.mpr (mem_normalizer_of_conj_mem htNN))
  have hKN : K ≤ N := by
    rw [hNdef]
    exact le_inf hKD.le Subgroup.le_normalizer
  have hKH : K ≤ H := hKN.trans hNH
  haveI hK'n : (K.subgroupOf H).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHK g.2) k).mp hk⟩
  haveI hN'n : (N.subgroupOf H).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHN g.2) n).mp hn⟩
  haveI : Fact (IsPGroup 2 (↥H ⧸ K.subgroupOf H)) :=
    ⟨(hV.to_le hHV).to_quotient (K.subgroupOf H)⟩
  set Nb : Subgroup (↥H ⧸ K.subgroupOf H) :=
    (N.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H)) with hNb
  haveI hNbn : Nb.Normal := by
    rw [hNb]
    exact Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective _)
  have hmk0 : (QuotientGroup.mk (⟨n₀, hNH hn₀N'⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ∈ Nb := by
    rw [hNb]
    exact ⟨⟨n₀, hNH hn₀N'⟩, Subgroup.mem_subgroupOf.mpr hn₀N', rfl⟩
  have hmk0ne : (QuotientGroup.mk (⟨n₀, hNH hn₀N'⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) ≠ 1 := by
    intro h1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact hn₀K h1
  haveI : Nontrivial Nb := ⟨⟨⟨_, hmk0⟩, 1, fun h => hmk0ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal Nb (p := 2)
  obtain ⟨y, hyN, hyx⟩ : ∃ y : ↥H, y ∈ N.subgroupOf H ∧
      QuotientGroup.mk' (K.subgroupOf H) y = (x : ↥H ⧸ K.subgroupOf H) :=
    Subgroup.mem_map.mp x.2
  have hyN' : (y : G) ∈ N := Subgroup.mem_subgroupOf.mp hyN
  refine ⟨y, hND hyN', ?_, ?_, ?_⟩
  · intro hyK
    apply hx1
    apply Subtype.ext
    rw [← hyx]
    exact (QuotientGroup.eq_one_iff y).mpr (Subgroup.mem_subgroupOf.mpr hyK)
  · intro k hk
    rw [hNdef] at hyN'
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hyN').2 k).mp hk
  · have hc := Subgroup.mem_center_iff.mp hxc (QuotientGroup.mk (⟨t, htH⟩ : ↥H))
    have h2 : (QuotientGroup.mk (⟨t, htH⟩ : ↥H) : ↥H ⧸ K.subgroupOf H) *
        (QuotientGroup.mk y) * (QuotientGroup.mk (⟨t, htH⟩ : ↥H))⁻¹ = QuotientGroup.mk y := by
      rw [mul_inv_eq_iff_eq_mul]
      have hyx' : (QuotientGroup.mk y : ↥H ⧸ K.subgroupOf H) = x := hyx
      rw [hyx']
      exact hc
    have h3 : (QuotientGroup.mk (⟨t, htH⟩ * y * (⟨t, htH⟩ : ↥H)⁻¹) :
        ↥H ⧸ K.subgroupOf H) = QuotientGroup.mk y := by
      rw [← h2]
      rfl
    have h4 := (QuotientGroup.eq.mp h3.symm)
    rw [Subgroup.mem_subgroupOf] at h4
    refine ⟨(y : G)⁻¹ * (t * y * t⁻¹), h4, ?_⟩
    group

theorem z18_cent_eq {V D K : Subgroup G} (hV : IsPGroup 2 V) (hDV : D ≤ V) (hKD : K ≤ D) {t : G}
    (htV : t ∈ V) (htD : ∀ d ∈ D, t * d * t⁻¹ ∈ D) (htK : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hcl : ∀ z ∈ D, (∀ k ∈ K, z * k * z⁻¹ ∈ K) → (∃ k ∈ K, t * z * t⁻¹ = z * k) → z ∈ K) :
    D = K := by
  by_contra hne
  obtain ⟨z, hzD, hzK, hzn, hzt⟩ :=
    z18_grow hV (lt_of_le_of_ne hKD fun h => hne h.symm) hDV htV htD htK
  exact hzK (hcl z hzD hzn hzt)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
