module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CoverUniq

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Equiv

variable {Y : Type*} [Group Y] [Finite Y] {w : Y} {π : Y →* Perm (Fin 5)}

private lemma tableVII_cover_hyp_zpowers_normal (hC : TableVIICover Y w π) :
    (Subgroup.zpowers w).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr
    (Subgroup.mem_center_iff.mpr (fun g => (tableVII_cover_central hC g).symm)))

private lemma tableVII_cover_hyp_zpowers_card (hC : TableVIICover Y w π) :
    Nat.card (Subgroup.zpowers w) = 2 := by
  rw [Nat.card_zpowers w, orderOf_eq_prime hC.sq hC.ne_one]

private lemma tableVII_cover_hyp_card_perm : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  norm_num

private lemma tableVII_cover_hyp_factorization : (240 : ℕ).factorization 2 = 4 := by
  have h240 : (240 : ℕ) = 2 ^ 4 * 15 := by norm_num
  rw [h240, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_two]
  simp [Nat.factorization_eq_zero_of_not_dvd]

theorem tableVII_cover_sylow (hC : TableVIICover Y w π) (S : Sylow 2 Y) :
    (∀ x : Y, (x ∈ centerOf (S : Subgroup Y) ∧ x ^ 2 = 1) ↔ x ∈ Subgroup.zpowers w) ∧
      2 < Nat.card S := by
  have hcardS : Nat.card S = 16 := by
    rw [Sylow.card_eq_multiplicity S, tableVII_cover_card hC,
      tableVII_cover_hyp_factorization]
    norm_num
  have hleS : Subgroup.zpowers w ≤ (S : Subgroup Y) := by
    letI : (Subgroup.zpowers w).Normal := tableVII_cover_hyp_zpowers_normal hC
    exact IsPGroup.le_sylow_of_normal
      (IsPGroup.of_card (p := 2) (n := 1) (by
        rw [tableVII_cover_hyp_zpowers_card hC]; norm_num)) S
  refine ⟨fun x => ⟨?_, ?_⟩, by omega⟩
  · intro hx
    obtain ⟨hxZ, hx2⟩ := hx
    rw [centerOf, Subgroup.mem_inf] at hxZ
    by_contra hxw
    have hx1 : x ≠ 1 := fun h => hxw ((tableVII_cover_mem_zpowers hC).mpr (Or.inl h))
    have hxw' : x ≠ w := fun h => hxw ((tableVII_cover_mem_zpowers hC).mpr (Or.inr h))
    have hsign : Perm.sign (π x) = -1 := tableVII_cover_sign_of_inv hC hx2 hx1 hxw'
    have hx2π : π x * π x = 1 := by rw [← map_mul, ← pow_two, hx2, map_one]
    have hcardC : Nat.card (Subgroup.centralizer ({π x} : Set (Perm (Fin 5)))) = 12 :=
      tableVII_perm_card_centralizer (π x) hx2π hsign
    have hmap_le : (S : Subgroup Y).map π ≤
        Subgroup.centralizer ({π x} : Set (Perm (Fin 5))) := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨s, hs, rfl⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxZ.2 s hs]
    have hdvd12 : Nat.card ((S : Subgroup Y).map π) ∣ 12 := by
      have h := Subgroup.card_dvd_of_le hmap_le
      rwa [hcardC] at h
    let f : (S : Subgroup Y) →* Perm (Fin 5) := π.domRestrict (S : Subgroup Y)
    have hfker : f.ker = π.ker.subgroupOf (S : Subgroup Y) := rfl
    have hfrange : f.range = (S : Subgroup Y).map π := by
      ext z
      constructor
      · intro hz
        rw [MonoidHom.mem_range] at hz
        obtain ⟨s, rfl⟩ := hz
        exact Subgroup.mem_map.mpr ⟨(s : Y), s.2, rfl⟩
      · intro hz
        rw [Subgroup.mem_map] at hz
        obtain ⟨s, hs, rfl⟩ := hz
        exact MonoidHom.mem_range.mpr ⟨⟨s, hs⟩, rfl⟩
    have hkerle : π.ker ≤ (S : Subgroup Y) := by
      rw [hC.ker_eq]
      exact hleS
    have hcardker : Nat.card f.ker = 2 := by
      rw [hfker]
      calc Nat.card (π.ker.subgroupOf (S : Subgroup Y))
          = Nat.card π.ker := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
        _ = Nat.card (Subgroup.zpowers w) := by rw [hC.ker_eq]
        _ = 2 := tableVII_cover_hyp_zpowers_card hC
    have hquot : Nat.card ((S : Subgroup Y) ⧸ f.ker) = Nat.card ((S : Subgroup Y).map π) := by
      calc Nat.card ((S : Subgroup Y) ⧸ f.ker)
          = Nat.card f.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
        _ = Nat.card ((S : Subgroup Y).map π) := by rw [hfrange]
    have hcard8 : Nat.card ((S : Subgroup Y).map π) = 8 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
      rw [hquot, hcardker, hcardS] at h
      omega
    rw [hcard8] at hdvd12
    obtain ⟨k, hk⟩ := hdvd12
    omega
  · intro hx
    rcases (tableVII_cover_mem_zpowers hC).mp hx with h1 | hw'
    · subst h1
      exact ⟨by simp [centerOf], by simp⟩
    · subst hw'
      refine ⟨?_, hC.sq⟩
      rw [centerOf, Subgroup.mem_inf]
      exact ⟨hleS (by simpa using Subgroup.npow_mem_zpowers w 1),
        Subgroup.mem_centralizer_iff.mpr (fun h _ => (tableVII_cover_central hC h).symm)⟩

theorem tableVII_cover_normal (hC : TableVIICover Y w π) (N : Subgroup Y) (hN : N.Normal)
    (hne : N ≠ ⊥) : w ∈ N := by
  by_contra hwN
  have hker_bot : (π.domRestrict N).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hyw : (y : Y) ∈ Subgroup.zpowers w := by
      rw [← hC.ker_eq]
      exact MonoidHom.mem_ker.mpr (by simpa using hy)
    rcases (tableVII_cover_mem_zpowers hC).mp hyw with h1 | hw'
    · exact Subtype.ext h1
    · exact absurd (hw' ▸ y.2) hwN
  have hinj : Function.Injective (π.domRestrict N) :=
    (MonoidHom.ker_eq_bot_iff (π.domRestrict N)).mp hker_bot
  have hcardN : Nat.card (N.map π) = Nat.card N := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup N))
      (f := π.domRestrict N) hinj
    rw [Subgroup.map_top, MonoidHom.domRestrict_range, Subgroup.card_top] at h
    exact h
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  obtain ⟨n, hnN, hn1⟩ := Subgroup.exists_ne_one_of_nontrivial N
  have hπn_mem : π n ∈ N.map π := Subgroup.mem_map.mpr ⟨n, hnN, rfl⟩
  have hπn_ne : π n ≠ 1 := by
    intro h
    have hker : n ∈ Subgroup.zpowers w := by
      rw [← hC.ker_eq]
      exact MonoidHom.mem_ker.mpr h
    rcases (tableVII_cover_mem_zpowers hC).mp hker with h1 | hw'
    · exact hn1 h1
    · exact hwN (hw' ▸ hnN)
  have hNmap_ne : N.map π ≠ ⊥ := by
    intro hbot
    have hmem : π n ∈ (⊥ : Subgroup (Perm (Fin 5))) := hbot ▸ hπn_mem
    rw [Subgroup.mem_bot] at hmem
    exact hπn_ne hmem
  have hNmap_normal : (N.map π).Normal := hN.map π hC.surj
  have hAlt_le : alternatingGroup (Fin 5) ≤ N.map π :=
    tableVII_perm_alternating_le hNmap_normal hNmap_ne
  have hcases : Nat.card (N.map π) = 60 ∨ Nat.card (N.map π) = 120 := by
    have h60dvd : 60 ∣ Nat.card (N.map π) := by
      have h := Subgroup.card_dvd_of_le hAlt_le
      rwa [tableVII_perm_card_alternating] at h
    have hdvd : Nat.card (N.map π) ∣ 120 := by
      have h := Subgroup.card_subgroup_dvd_card (N.map π)
      rwa [tableVII_cover_hyp_card_perm] at h
    obtain ⟨k, hk⟩ := h60dvd
    have hk_pos : 0 < k := by
      have : 0 < 60 * k := by rw [← hk]; exact Nat.card_pos
      omega
    have hk_le : k ≤ 2 := by
      have hle : 60 * k ≤ 120 := by
        rw [← hk]
        exact Nat.le_of_dvd (by norm_num) hdvd
      omega
    interval_cases k
    · left; omega
    · right; omega
  have hq_card : Nat.card (Y ⧸ N) = 2 ∨ Nat.card (Y ⧸ N) = 4 := by
    have hNcases : Nat.card N = 60 ∨ Nat.card N = 120 := by
      rwa [hcardN] at hcases
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [tableVII_cover_card hC] at h
    rcases hNcases with hN60 | hN120
    · right; rw [hN60] at h; omega
    · left; rw [hN120] at h; omega
  have hcomm : IsMulCommutative (Y ⧸ N) := by
    letI : N.Normal := hN
    rcases hq_card with h2 | h4
    · exact (isCyclic_of_prime_card (p := 2) h2).isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [h4]; norm_num)
  have hcomm_le : commutator Y ≤ N := by
    letI : N.Normal := hN
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  exact hwN (hcomm_le (hC.le_comm (by simpa only [zpow_one] using Subgroup.zpow_mem_zpowers w 1)))

theorem tableVII_cover_closure (hC : TableVIICover Y w π) (C : Set Y)
    (hCconj : ∀ g y : Y, y ∈ C → g * y * g⁻¹ ∈ C) {x : Y} (hxC : x ∈ C) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxw : x ≠ w) : Subgroup.closure C = ⊤ := by
  have hnorm : (Subgroup.closure C).Normal := by
    have hle : Subgroup.normalClosure C ≤ Subgroup.closure C := by
      rw [Subgroup.normalClosure]
      rw [Subgroup.closure_le]
      intro z hz
      rw [Group.mem_conjugatesOfSet_iff] at hz
      obtain ⟨c, hc, hconj⟩ := hz
      rw [isConj_iff] at hconj
      obtain ⟨g, rfl⟩ := hconj
      exact Subgroup.subset_closure (hCconj g c hc)
    have heq : Subgroup.closure C = Subgroup.normalClosure C :=
      le_antisymm Subgroup.closure_le_normalClosure hle
    rw [heq]
    exact Subgroup.normalClosure_normal
  have hMne : Subgroup.closure C ≠ ⊥ := by
    intro hbot
    have : x ∈ (⊥ : Subgroup Y) := hbot ▸ Subgroup.subset_closure hxC
    rw [Subgroup.mem_bot] at this
    exact hx1 this
  have hwM : w ∈ Subgroup.closure C :=
    tableVII_cover_normal hC (Subgroup.closure C) hnorm hMne
  have hsign : Perm.sign (π x) = -1 := tableVII_cover_sign_of_inv hC hx2 hx1 hxw
  have hπx : π x ∈ (Subgroup.closure C).map π :=
    Subgroup.mem_map.mpr ⟨x, Subgroup.subset_closure hxC, rfl⟩
  have hmap_top : (Subgroup.closure C).map π = ⊤ :=
    tableVII_perm_eq_top_of_normal (hnorm.map π hC.surj) hπx hsign
  rw [Subgroup.eq_top_iff']
  intro y
  have hy : π y ∈ (Subgroup.closure C).map π := by
    rw [hmap_top]
    exact Subgroup.mem_top _
  obtain ⟨m, hm, hπm⟩ := Subgroup.mem_map.mp hy
  have hker : m⁻¹ * y ∈ Subgroup.zpowers w := by
    rw [← hC.ker_eq]
    exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hπm, inv_mul_cancel])
  rcases (tableVII_cover_mem_zpowers hC).mp hker with h1 | hw'
  · rw [← mul_inv_cancel_left m y, h1, mul_one]
    exact hm
  · rw [← mul_inv_cancel_left m y, hw']
    exact mul_mem hm hwM

end CFSG.EvenSporadicStandard.HNRecog.Section3
