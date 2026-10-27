module

public import CFSG.CGT.T75Q.KerZ

public section

namespace CFSG.CGT.T75Q

open CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G]

theorem odd_index_normalizer_subgroupOf [Finite G] {T U : Subgroup G} (hWC : IsWC T)
    (hTU : T ≤ U) : Odd ((Subgroup.normalizer (T : Set G)).subgroupOf U).index := by
  classical
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hWC.1
  have hT'2 : IsPGroup 2 (T.subgroupOf U) := by
    intro x
    obtain ⟨n, hn⟩ := hT2 ⟨(x : G), Subgroup.mem_subgroupOf.1 x.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg (fun z : ↥T => (z : G)) hn
    simpa using this
  obtain ⟨P, hTP⟩ := hT'2.exists_le_sylow
  have hP'2 : IsPGroup 2 ((P : Subgroup ↥U).map U.subtype) := P.isPGroup'.map U.subtype
  have hTP' : T ≤ (P : Subgroup ↥U).map U.subtype := fun t ht =>
    ⟨⟨t, hTU ht⟩, hTP (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hPN : (P : Subgroup ↥U) ≤ (Subgroup.normalizer (T : Set G)).subgroupOf U := by
    intro p hp
    have hpP' : (p : G) ∈ (P : Subgroup ↥U).map U.subtype := ⟨p, hp, rfl⟩
    have h1 : conjSubgroup (p : G) T ≤ (P : Subgroup ↥U).map U.subtype := by
      intro x hx
      have hx' : (p : G)⁻¹ * x * p ∈ T := mem_conjSubgroup.1 hx
      have := ((P : Subgroup ↥U).map U.subtype).mul_mem
        (((P : Subgroup ↥U).map U.subtype).mul_mem hpP' (hTP' hx'))
        (((P : Subgroup ↥U).map U.subtype).inv_mem hpP')
      simpa [mul_assoc] using this
    exact Subgroup.mem_subgroupOf.2
      (mem_normalizer_of_conjSubgroup_eq (eq_of_conj_le_pGroup hWC hP'2 hTP' h1))
  have hdvd := Subgroup.index_dvd_of_le hPN
  have hodd : Odd (P : Subgroup ↥U).index := by
    rcases Nat.even_or_odd (P : Subgroup ↥U).index with he | ho
    · exact absurd (even_iff_two_dvd.1 he) P.not_dvd_index
    · exact ho
  exact hodd.of_dvd_nat hdvd

theorem commutator_eq_top_of_good {T H U : Subgroup G} (hWC : IsWC T) (hTH : T ≤ H)
    (hHU : H ≤ U) (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T)
    (htrans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y)
    (hH2 : ¬ IsPGroup 2 H)
    (hcl : Subgroup.normalClosure ((T.subgroupOf U : Subgroup ↥U) : Set ↥U) = ⊤) :
    commutator ↥U = ⊤ := by
  classical
  have hTU : T ≤ U := hTH.trans hHU
  by_cases hex : ∃ t : G, ∃ ht : t ∈ T, t ≠ 1 ∧ (⟨t, hTU ht⟩ : ↥U) ∈ commutator ↥U
  · obtain ⟨t, ht, ht1, htU⟩ := hex
    have hle : T.subgroupOf U ≤ commutator ↥U := by
      intro s hs
      have hsT : (s : G) ∈ T := Subgroup.mem_subgroupOf.1 hs
      by_cases hs1 : (s : G) = 1
      · have : s = 1 := Subtype.ext hs1
        rw [this]
        exact Subgroup.one_mem _
      · obtain ⟨h, hh, hht⟩ := htrans t ht ht1 (s : G) hsT hs1
        have hmem := (inferInstance : (commutator ↥U).Normal).conj_mem _ htU ⟨h, hHU hh⟩
        have e : (⟨h, hHU hh⟩ * ⟨t, hTU ht⟩ * ⟨h, hHU hh⟩⁻¹ : ↥U) = s :=
          Subtype.ext (by simpa using hht)
        rwa [e] at hmem
    rw [eq_top_iff, ← hcl]
    exact Subgroup.normalClosure_le_normal hle
  · push Not at hex
    exfalso
    have hcomm : ∀ h ∈ H, ∀ t ∈ T, h * t = t * h := by
      intro h hh t ht
      by_contra hne
      have hw : h * t * h⁻¹ * t⁻¹ ∈ T := T.mul_mem (conj_mem_of_mem_normalizer (hHN hh) ht)
        (T.inv_mem ht)
      have hw1 : h * t * h⁻¹ * t⁻¹ ≠ 1 := by
        intro h1
        apply hne
        have : h * t * h⁻¹ = t := by simpa using mul_inv_eq_one.1 h1
        calc h * t = (h * t * h⁻¹) * h := by group
          _ = t * h := by rw [this]
      apply hex _ hw hw1
      have e : (⟨h * t * h⁻¹ * t⁻¹, hTU hw⟩ : ↥U) =
          ⁅(⟨h, hHU hh⟩ : ↥U), (⟨t, hTU ht⟩ : ↥U)⁆ := by
        apply Subtype.ext
        simp [commutatorElement_def]
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hHCT : H ≤ Subgroup.centralizer (T : Set G) := fun h hh =>
      Subgroup.mem_centralizer_iff.2 fun t ht => (hcomm h hh t ht).symm
    have hHT : H = T := by
      rw [← hHC]
      exact (inf_eq_left.2 hHCT).symm
    apply hH2
    rw [hHT]
    exact isPGroup_two_of_isElemAbelian hWC.1

theorem odd_card_center_of_good [Finite G] {T H U : Subgroup G} (hWC : IsWC T) (hTH : T ≤ H)
    (hHU : H ≤ U) (hHN : H ≤ Subgroup.normalizer (T : Set G))
    (hHC : H ⊓ Subgroup.centralizer (T : Set G) = T)
    (htrans : ∀ x ∈ T, x ≠ 1 → ∀ y ∈ T, y ≠ 1 → ∃ h ∈ H, h * x * h⁻¹ = y)
    (hH2 : ¬ IsPGroup 2 H)
    (hprod : ∀ g ∈ Subgroup.normalizer (T : Set G),
      ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set G), g = h * c)
    (hinf : H ⊓ Subgroup.centralizer (H : Set G) = ⊥)
    (hCU : ∀ c ∈ Subgroup.centralizer (H : Set G), c ∈ U → ∀ u ∈ U, c * u = u * c)
    (hcl : Subgroup.normalClosure ((T.subgroupOf U : Subgroup ↥U) : Set ↥U) = ⊤) :
    Odd (Nat.card (Subgroup.center ↥U)) := by
  classical
  have hTU : T ≤ U := hTH.trans hHU
  have hperf := commutator_eq_top_of_good hWC hTH hHU hHN hHC htrans hH2 hcl
  have hodd := odd_index_normalizer_subgroupOf hWC hTU
  set N : Subgroup ↥U := (Subgroup.normalizer (T : Set G)).subgroupOf U with hNdef
  refine odd_card_center_of_transfer N hperf hodd ?_
  intro y hy hyz
  have hcommH : ∀ g₁ g₂ : ↥N, ((⁅g₁, g₂⁆ : ↥N) : ↥U).1 ∈ H := by
    intro g₁ g₂
    have hg₁ : (g₁ : ↥U).1 ∈ Subgroup.normalizer (T : Set G) := Subgroup.mem_subgroupOf.1 g₁.2
    have hg₂ : (g₂ : ↥U).1 ∈ Subgroup.normalizer (T : Set G) := Subgroup.mem_subgroupOf.1 g₂.2
    obtain ⟨h₁, hh₁, c₁, hc₁, e₁⟩ := hprod _ hg₁
    obtain ⟨h₂, hh₂, c₂, hc₂, e₂⟩ := hprod _ hg₂
    have hc₁U : c₁ ∈ U := by
      have : c₁ = h₁⁻¹ * (g₁ : ↥U).1 := by rw [e₁]; group
      rw [this]
      exact U.mul_mem (U.inv_mem (hHU hh₁)) (g₁ : ↥U).2
    have hc₂U : c₂ ∈ U := by
      have : c₂ = h₂⁻¹ * (g₂ : ↥U).1 := by rw [e₂]; group
      rw [this]
      exact U.mul_mem (U.inv_mem (hHU hh₂)) (g₂ : ↥U).2
    have k₁₂ : c₁ * h₂ = h₂ * c₁ := hCU c₁ hc₁ hc₁U h₂ (hHU hh₂)
    have k₁₂' : c₁ * c₂ = c₂ * c₁ := hCU c₁ hc₁ hc₁U c₂ hc₂U
    have k₂₁ : c₂ * h₁ = h₁ * c₂ := hCU c₂ hc₂ hc₂U h₁ (hHU hh₁)
    have hval : ((⁅g₁, g₂⁆ : ↥N) : ↥U).1 =
        (g₁ : ↥U).1 * (g₂ : ↥U).1 * (g₁ : ↥U).1⁻¹ * (g₂ : ↥U).1⁻¹ := by
      simp [commutatorElement_def]
    rw [hval, e₁, e₂]
    have e : h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by
      calc h₁ * c₁ * (h₂ * c₂) * (h₁ * c₁)⁻¹ * (h₂ * c₂)⁻¹
          = h₁ * (c₁ * h₂) * c₂ * c₁⁻¹ * h₁⁻¹ * c₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * (h₂ * c₁) * c₂ * c₁⁻¹ * h₁⁻¹ * c₂⁻¹ * h₂⁻¹ := by rw [k₁₂]
        _ = h₁ * h₂ * (c₁ * c₂) * c₁⁻¹ * h₁⁻¹ * c₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * (c₂ * c₁) * c₁⁻¹ * h₁⁻¹ * c₂⁻¹ * h₂⁻¹ := by rw [k₁₂']
        _ = h₁ * h₂ * c₂ * h₁⁻¹ * c₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * (c₂ * h₁⁻¹) * c₂⁻¹ * h₂⁻¹ := by group
        _ = h₁ * h₂ * (h₁⁻¹ * c₂) * c₂⁻¹ * h₂⁻¹ := by
            rw [show c₂ * h₁⁻¹ = h₁⁻¹ * c₂ by
              calc c₂ * h₁⁻¹ = h₁⁻¹ * (h₁ * c₂) * h₁⁻¹ := by group
                _ = h₁⁻¹ * (c₂ * h₁) * h₁⁻¹ := by rw [k₂₁]
                _ = h₁⁻¹ * c₂ := by group]
        _ = h₁ * h₂ * h₁⁻¹ * h₂⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.mul_mem hh₁ hh₂) (H.inv_mem hh₁)) (H.inv_mem hh₂)
  have hle : commutator ↥N ≤ (H.subgroupOf U).subgroupOf N := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 (hcommH g₁ g₂))
  have hyH : ((y : ↥U) : G) ∈ H :=
    Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 (hle hy))
  have hyC : ((y : ↥U) : G) ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := Subgroup.mem_center_iff.1 hyz ⟨h, hHU hh⟩
    exact congrArg Subtype.val this
  have h1 : ((y : ↥U) : G) ∈ H ⊓ Subgroup.centralizer (H : Set G) := ⟨hyH, hyC⟩
  rw [hinf, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

end CFSG.CGT.T75Q
