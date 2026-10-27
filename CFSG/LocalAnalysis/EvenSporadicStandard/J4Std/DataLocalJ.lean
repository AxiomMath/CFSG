module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Local
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Sporadic.J4.QT2LocUniqCheck
public import Certificates.Certificate4117
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.EvenSporadicStandard.J4Std.DataLocal

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

theorem Hloc_top_eq_Hj (hF : J4Facts) :
    Hloc (⊤ : Subgroup J) (Eg uJ 11) = Hj := by
  rw [Hloc, inf_top_eq]
  exact normalizer_Eg_eq_Hj hF

theorem card_H_J (hF : J4Facts) :
    Nat.card (Hloc (⊤ : Subgroup J) (Eg uJ 11)) = 501397585920 := by
  rw [Hloc_top_eq_Hj hF]
  exact card_Hj hF

theorem selfCentralizing_J (hF : J4Facts) :
    ∀ l ∈ (⊤ : Subgroup J), (∀ u ∈ Eg uJ 11, l * u = u * l) → l ∈ Eg uJ 11 := by
  intro l _ hc
  have hlc : l ∈ Subgroup.centralizer (Eg uJ 11 : Set J) :=
    Subgroup.mem_centralizer_iff.2 fun u hu => (hc u hu).symm
  have hl : l ∈ Hj := by
    rw [← normalizer_Eg_eq_Hj hF]
    exact Subgroup.centralizer_le_normalizer _ hlc
  exact centralizer_Hj hF.mat hF l hl hc

theorem irred_J (hF : J4Facts) :
    ∀ D : Subgroup J, D ≤ Eg uJ 11 →
      (∀ h ∈ Hloc (⊤ : Subgroup J) (Eg uJ 11), ∀ d ∈ D, h * d * h⁻¹ ∈ D) →
      D = ⊥ ∨ D = Eg uJ 11 := by
  intro D hD hinv
  rw [Hloc_top_eq_Hj hF] at hinv
  exact minimal_of_orbits (elem_uJ hF.mat) Hj XJ act letters (fun _ hℓ => XJ_mem hℓ)
    (fun _ hℓ c => hX_all hF.mat hℓ c) orbits orbit_words orbit_cover orbit_span D hD hinv

theorem T0_pGroup_J
    (hF : J4Facts) : IsPGroup 2 P0 :=
  IsPGroup.of_card (card_P0 hF.mat hF)

theorem T0_index_odd_J
    (hF : J4Facts) : ¬ 2 ∣ P0.relIndex (⊤ : Subgroup J) := by
  have h := Subgroup.card_mul_index P0
  rw [card_P0 hF.mat hF, card_J hF] at h
  have hidx : P0.index = 41377816699065 := by omega
  rw [Subgroup.relIndex_top_right, hidx]
  decide

noncomputable def Tl : Finset J := (tMasks.map (eta uJ 11)).toFinset

theorem mem_Tl {x : J} : x ∈ Tl ↔ ∃ c ∈ tMasks, eta uJ 11 c = x := by
  simp [Tl]

theorem card_Tl (hM : MatFacts) :
    Tl.card = 276 := by
  obtain ⟨h1, h2, h3⟩ := Certificates.certificate4117.1
  rw [Tl, List.toFinset_card_of_nodup, List.length_map, h1]
  rw [List.nodup_map_iff_inj_on h2]
  intro c hc d hd e
  exact eta_inj hM c (h3 c hc) d (h3 d hd) e

theorem Tl_conj (hM : MatFacts) :
    ∀ h ∈ Hj, ∀ x ∈ Tl, h * x * h⁻¹ ∈ Tl := by
  intro h hh x hx
  obtain ⟨c, hc, rfl⟩ := mem_Tl.1 hx
  obtain ⟨c', hc', e⟩ := (tSet_conj hM h hh).1 (eta uJ 11 c) ⟨c, hc, rfl⟩
  exact mem_Tl.2 ⟨c', hc', e.symm⟩

theorem exists_conj_eta_one
    (hM : MatFacts) {c : ℕ} (hc : c ∈ tMasks) :
    ∃ g ∈ Hj, g * eta uJ 11 1 * g⁻¹ = eta uJ 11 c := by
  have hroot : (orbits.getD 0 (1, [], [])).1 = 1 := Certificates.certificate4117.2
  have hoo : orbits.getD 0 (1, [], []) ∈ orbits := by
    by_contra hnot
    have hdef : orbits.getD 0 (1, [], []) = (1, [], []) := by
      rw [List.getD_eq_getElem?_getD]
      cases h : orbits[0]? with
      | none => rfl
      | some y =>
        exact absurd (List.mem_of_getElem? h) (by simpa [List.getD_eq_getElem?_getD, h] using hnot)
    have hz : tMasks = [] := by
      simp only [tMasks, hdef]
      rfl
    rw [hz] at hc
    simp at hc
  obtain ⟨p, hp, rfl⟩ : ∃ p ∈ (orbits.getD 0 (1, [], [])).2.1, p.1 = c := by
    simpa [tMasks] using hc
  obtain ⟨hlet, hfold⟩ := orbit_words _ hoo p hp
  rw [hroot] at hfold
  refine ⟨(p.2.map XJ).prod, ?_, ?_⟩
  · refine Subgroup.list_prod_mem Hj ?_
    intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.1 hx
    exact XJ_mem (hlet ℓ hℓ)
  · rw [word_conj XJ act p.2 (fun ℓ hℓ => hX_all hM (hlet ℓ hℓ)), hfold]

theorem mem_hOrbit_top (hF : J4Facts) {x u : J} :
    u ∈ hOrbit (⊤ : Subgroup J) (Eg uJ 11) x ↔ ∃ h ∈ Hj, h * x * h⁻¹ = u := by
  show (∃ h ∈ Hloc (⊤ : Subgroup J) (Eg uJ 11), h * x * h⁻¹ = u) ↔ _
  rw [Hloc_top_eq_Hj hF]

theorem hOrbit_eta_three
    (hF : J4Facts) : hOrbit (⊤ : Subgroup J) (Eg uJ 11) (eta uJ 11 3) = (Zl : Set J) := by
  ext u
  rw [mem_hOrbit_top hF, Finset.mem_coe]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (Zl_conj hF.mat h hh).1 _ (mem_Zl.2 ⟨3, three_mem_zMasks, rfl⟩)
  · intro hu
    obtain ⟨c, hc, rfl⟩ := mem_Zl.1 hu
    exact exists_conj_eta_three hF.mat hc

theorem hOrbit_eta_one
    (hF : J4Facts) :
    hOrbit (⊤ : Subgroup J) (Eg uJ 11) (eta uJ 11 1) = (Tl : Set J) := by
  ext u
  rw [mem_hOrbit_top hF, Finset.mem_coe]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact Tl_conj hF.mat h hh _ (mem_Tl.2 ⟨1, one_mem_tMasks, rfl⟩)
  · intro hu
    obtain ⟨c, hc, rfl⟩ := mem_Tl.1 hu
    exact exists_conj_eta_one hF.mat hc

theorem orbits_J
    (hF : J4Facts) :
    ∃ a b : J, a ∈ Eg uJ 11 ∧ b ∈ Eg uJ 11 ∧ a ≠ 1 ∧ b ≠ 1 ∧
      b ∉ hOrbit (⊤ : Subgroup J) (Eg uJ 11) a ∧
      (∀ u ∈ Eg uJ 11, u ≠ 1 →
        u ∈ hOrbit (⊤ : Subgroup J) (Eg uJ 11) a ∨ u ∈ hOrbit (⊤ : Subgroup J) (Eg uJ 11) b) ∧
      (hOrbit (⊤ : Subgroup J) (Eg uJ 11) a).ncard = 1771 ∧
      (hOrbit (⊤ : Subgroup J) (Eg uJ 11) b).ncard = 276 := by
  have hM := hF.mat
  refine ⟨eta uJ 11 3, eta uJ 11 1, eta_mem_Eg 11 le_rfl 3, eta_mem_Eg 11 le_rfl 1,
    eta_ne_one hM (by norm_num) (by norm_num), eta_ne_one hM (by norm_num) (by norm_num),
    ?_, ?_, ?_, ?_⟩
  · rw [hOrbit_eta_three hF, Finset.mem_coe]
    intro h1
    have hsub : Zl ⊆ Tl := by
      intro y hy
      obtain ⟨h, hh, rfl⟩ := Zl_trans hM _ h1 y hy
      exact Tl_conj hM h hh _ (mem_Tl.2 ⟨1, one_mem_tMasks, rfl⟩)
    have := Finset.card_le_card hsub
    rw [card_Zl hM, card_Tl hM] at this
    omega
  · intro u hu hu1
    obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 hu
    rw [hOrbit_eta_three hF, hOrbit_eta_one hF, Finset.mem_coe, Finset.mem_coe]
    rcases mask_cover c (by omega) with h0 | h0 | h0
    · exact absurd (by rw [h0, eta_zero]) hu1
    · exact Or.inr (mem_Tl.2 ⟨c, h0, rfl⟩)
    · exact Or.inl (mem_Zl.2 ⟨c, h0, rfl⟩)
  · rw [hOrbit_eta_three hF, Set.ncard_coe_finset, card_Zl hM]
  · rw [hOrbit_eta_one hF, Set.ncard_coe_finset, card_Tl hM]

theorem localData_J_of_unique
    (huniq : ∀ A : Subgroup J, A ≤ P0 → (∀ a ∈ A, a * a = 1) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → 2 ^ 11 ≤ Nat.card A → A = Eg uJ 11) :
    LocalData (⊤ : Subgroup J) (Eg uJ 11) P0 where
  U_le_T0 := Eg_le_P0
  T0_le_L := le_top
  T0_pGroup := T0_pGroup_J j4Facts
  T0_index_odd := T0_index_odd_J j4Facts
  U_sq := fun _ hu => Eg_sq (elem_uJ j4Facts.mat) hu
  U_comm := fun _ hu _ hv => Eg_comm (elem_uJ j4Facts.mat) hu hv
  card_U := card_Eg_uJ j4Facts.mat
  unique := huniq
  selfCentralizing := selfCentralizing_J j4Facts
  card_H := card_H_J j4Facts
  orbits := orbits_J j4Facts
  irred := irred_J j4Facts

end CFSG.EvenSporadicStandard.J4Std.DataLocal
