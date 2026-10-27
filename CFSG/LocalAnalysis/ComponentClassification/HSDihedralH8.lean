module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralAutPair
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralDihedral
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2ActModel
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Inv
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.HSDihedral.H8

open CFSG Subgroup Equiv CFSG.ComponentClassification.HSFLit
open CFSG.ComponentClassification.HSFLit.L2Act

abbrev kap : Multiplicative (ZMod 2 × ZMod 2) := Multiplicative.ofAdd (0, 1)

theorem typeP_k8 : typeP k8 = kap := by decide

theorem kap_mul_kap : kap * kap = 1 := by decide

theorem typeP_aff8_eq_one_iff : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8,
    typeP (aff8 u b) = 1 ↔ aff8 u b ∈ R8 := by decide

theorem typeP_cases : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 0 →
    typeP (aff8 u b) = 1 ∨ typeP (aff8 u b) = kap := by decide

theorem fbit8_of_typeP_eq_kap : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, typeP (aff8 u b) = kap →
    fbit8 u = 1 := by decide

theorem typeP_of_D16 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, (u = 1 ∨ u = -1) → aff8 u b ∉ R8 →
    typeP (aff8 u b) = Multiplicative.ofAdd (1, 0) := by decide

theorem class_cases : ∀ a : Multiplicative (ZMod 2 × ZMod 2), a ≠ 1 → a ≠ kap →
    a = Multiplicative.ofAdd (1, 0) ∨ a = Multiplicative.ofAdd (1, 1) := by decide

theorem index_aux (a b : Multiplicative (ZMod 2 × ZMod 2)) (ha : a ≠ 1) (hb : b ≠ 1)
    (hak : a ≠ kap) (hbk : b ≠ kap) (habk : a * b ≠ kap) : a * b⁻¹ = 1 := by
  rcases class_cases a ha hak with rfl | rfl <;> rcases class_cases b hb hbk with rfl | rfl <;>
    first | decide | exact absurd (by decide) habk

theorem dbit8_of_comm_x8_y8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, aff8 u b * x8 = x8 * aff8 u b →
    aff8 u b * y8 = y8 * aff8 u b → dbit8 b = 0 := by decide

theorem dbit8_of_comm_refl : ∀ u : (ZMod 8)ˣ, ∀ b c : ZMod 8,
    aff8 u b * aff8 (-1) (2 * c) = aff8 (-1) (2 * c) * aff8 u b → dbit8 b = 0 := by decide

theorem rot_inv_cases : ∀ c : ZMod 8, aff8 1 (2 * c) * aff8 1 (2 * c) = 1 →
    aff8 1 (2 * c) = 1 ∨ aff8 1 (2 * c) = z8 := by decide

theorem x8_memR : x8 ∈ R8 := by decide

theorem y8_memR : y8 ∈ R8 := by decide

theorem z8_memR : z8 ∈ R8 := by decide

theorem typeP_mul {g h : Perm (ZMod 8)} (hg : g ∈ H8) (hh : h ∈ H8) :
    typeP (g * h) = typeP g * typeP h :=
  map_mul type8 ⟨g, hg⟩ ⟨h, hh⟩

theorem typeP_inv {g : Perm (ZMod 8)} (hg : g ∈ H8) : typeP g⁻¹ = (typeP g)⁻¹ :=
  map_inv type8 ⟨g, hg⟩

theorem typeP_eq_one_iff {g : Perm (ZMod 8)} (hg : g ∈ H8) : typeP g = 1 ↔ g ∈ R8 := by
  obtain ⟨u, b, rfl⟩ := hg
  exact typeP_aff8_eq_one_iff u b

theorem R8_le_D16 : R8 ≤ D16 := by
  rintro _ ⟨u, c, hu, rfl⟩
  exact ⟨u, 2 * c, hu, rfl⟩

theorem D16_le_H8 : D16 ≤ H8 := by
  rintro _ ⟨u, b, -, rfl⟩
  exact aff8_mem_H8 u b

theorem aff8_mem_D16 {u : (ZMod 8)ˣ} (b : ZMod 8) (hu : fbit8 u = 0) : aff8 u b ∈ D16 :=
  ⟨u, b, (fbit8_eq_zero_iff u).mp hu, rfl⟩

theorem range_dih8 : dih8.range = D16 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨g, rfl⟩
    exact dih8_mem_D16 g
  · rintro _ ⟨u, b, hu, rfl⟩
    rcases hu with rfl | rfl
    · exact ⟨DihedralGroup.r b, dih8_r b⟩
    · exact ⟨DihedralGroup.sr (-b), by rw [dih8_sr, neg_neg]⟩

theorem gen3_H8 {U : Subgroup (Perm (ZMod 8))} (hU : U ≤ H8) :
    ∃ s : Finset (Perm (ZMod 8)), s.card ≤ 3 ∧ closure (s : Set (Perm (ZMod 8))) = U := by
  classical
  set U' : Subgroup H8 := U.subgroupOf H8
  obtain ⟨s, hs, hsU⟩ := exists_finset_closure_eq_of_card_le (U'.map lin8) (k := 2) (by
    calc Nat.card (U'.map lin8) ≤ Nat.card (ZMod 8)ˣ := Subgroup.card_le_card_group _
      _ = 2 ^ 2 := by rw [card_units_zmod_eight]; norm_num)
  set V : Subgroup H8 := U' ⊓ lin8.ker
  have hVC : V.map H8.subtype ≤ C8 := by
    rintro _ ⟨g, hg, rfl⟩
    exact (lin8_eq_one_iff g).mp (mem_inf.mp hg).2
  have : IsCyclic (V.map H8.subtype) := Subgroup.isCyclic_of_le hVC
  obtain ⟨s₁, hs₁, hs₁V⟩ := exists_finset_closure_eq_of_isCyclic (V.map H8.subtype)
  obtain ⟨v, hv, hvV⟩ := exists_finset_closure_eq_of_map H8.subtype V hs₁ hs₁V
    (r := ∅) (b := 0) (by simp) (by rw [ker_subtype, inf_bot_eq, Finset.coe_empty,
      Subgroup.closure_empty])
  obtain ⟨u, hu, huU⟩ := exists_finset_closure_eq_of_map lin8 U' hs hsU hv hvV
  refine ⟨u.image H8.subtype, Finset.card_image_le.trans (by omega), ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, huU, subgroupOf_map_subtype, inf_of_le_left hU]

variable {P : Subgroup (Perm (ZMod 8))}

theorem typeP_ne_kap (hP1 : R8 ≤ P) (hP2 : P ≤ H8) (hk : k8 ∉ P) {g : Perm (ZMod 8)}
    (hg : g ∈ P) : typeP g ≠ kap := by
  intro h
  have hk8H : k8 ∈ H8 := aff8_mem_H8 _ _
  have h1 : g * k8⁻¹ ∈ R8 := by
    rw [← typeP_eq_one_iff (mul_mem (hP2 hg) (inv_mem hk8H)), typeP_mul (hP2 hg) (inv_mem hk8H),
      typeP_inv hk8H, h, typeP_k8]
    exact mul_inv_cancel _
  apply hk
  have := mul_mem (inv_mem (hP1 h1)) hg
  rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] at this

theorem centralizer_cases (hP2 : P ≤ H8) {c : Perm (ZMod 8)} (hc : c ∈ P)
    (hcD : ∀ d ∈ R8, c * d = d * c) : c ∈ R8 ∨ c * k8 ∈ R8 := by
  obtain ⟨u, b, rfl⟩ := hP2 hc
  rcases typeP_cases u b (dbit8_of_comm_x8_y8 u b (hcD x8 x8_memR) (hcD y8 y8_memR)) with h | h
  · exact Or.inl ((typeP_eq_one_iff (aff8_mem_H8 u b)).mp h)
  · right
    rw [← typeP_eq_one_iff (mul_mem (aff8_mem_H8 u b) (aff8_mem_H8 _ _)),
      typeP_mul (aff8_mem_H8 u b) (aff8_mem_H8 _ _), h, typeP_k8, kap_mul_kap]

theorem two_H8 (hP1 : R8 ≤ P) (hP2 : P ≤ H8) {k : Perm (ZMod 8)} (hk : PairCaseTwo P R8 k) :
    ∃ Tbar : Subgroup (Perm (ZMod 8)), Tbar ≤ P ∧ R8 ≤ Tbar ∧
      (∀ r ∈ P, r ^ 2 = 1 → r ∈ Tbar ∨ r * k ∈ R8) ∧
      (∀ δ ∈ Tbar, δ ∉ R8 → δ * k ≠ k * δ) ∧
      (Nat.card R8 = 8 → ∀ r ∈ P, r ∈ Tbar ∨ r * k ∈ Tbar) ∧
      (Tbar ≠ R8 → ∃ m : ℕ, Nonempty (↥Tbar ≃* DihedralGroup m)) := by
  obtain ⟨hkP, hkC, hkD, -, -, -⟩ := hk
  obtain ⟨u', b', rfl⟩ := hP2 hkP
  have hkty : typeP (aff8 u' b') = kap := by
    rcases typeP_cases u' b' (dbit8_of_comm_x8_y8 u' b' (hkC x8 x8_memR) (hkC y8 y8_memR))
      with h | h
    · exact absurd ((typeP_eq_one_iff (aff8_mem_H8 _ _)).mp h) hkD
    · exact h
  have hfk := fbit8_of_typeP_eq_kap u' b' hkty
  have hRT : R8 ≤ P ⊓ D16 := le_inf hP1 R8_le_D16
  refine ⟨P ⊓ D16, inf_le_left, hRT, fun r hr hr2 => ?_, fun δ hδ hδD hc => ?_,
    fun _ r hr => ?_, fun hne => ?_⟩
  · obtain ⟨u, b, rfl⟩ := hP2 hr
    rcases zmod2_cases (fbit8 u) with h | h
    · exact Or.inl ⟨hr, aff8_mem_D16 b h⟩
    · right
      have hb : dbit8 b = 0 := by
        rcases zmod2_cases (dbit8 b) with h' | h'
        · exact h'
        · exact absurd (by rw [← pow_two]; exact hr2) (not_inv_FD u b h h')
      have hrt : typeP (aff8 u b) = kap := by
        rcases typeP_cases u b hb with h' | h'
        · rw [typeP_aff8, hb, h] at h'
          exact absurd h' (by decide)
        · exact h'
      rw [← typeP_eq_one_iff (mul_mem (aff8_mem_H8 u b) (aff8_mem_H8 u' b')),
        typeP_mul (aff8_mem_H8 _ _) (aff8_mem_H8 _ _), hrt, hkty, kap_mul_kap]
  · obtain ⟨u, b, hu, rfl⟩ := (mem_inf.mp hδ).2
    have hb := dbit8_eq_one_of_not_mem_R8 hu hδD
    rcases cent_R8_odd u' b' u b hb (hkC x8 x8_memR) (hkC y8 y8_memR) hc.symm with h | h
    · exact hkD (h ▸ one_mem _)
    · exact hkD (h ▸ z8_memR)
  · obtain ⟨u, b, rfl⟩ := hP2 hr
    rcases zmod2_cases (fbit8 u) with h | h
    · exact Or.inl ⟨hr, aff8_mem_D16 b h⟩
    · right
      refine ⟨mul_mem hr hkP, ?_⟩
      rw [aff8_mul]
      refine aff8_mem_D16 _ ?_
      rw [fbit8_mul, h, hfk]
      decide
  · obtain ⟨δ, hδ, hδD⟩ : ∃ δ ∈ P ⊓ D16, δ ∉ R8 := by
      by_contra h
      push Not at h
      exact hne (le_antisymm h hRT)
    have hδ16 := (mem_inf.mp hδ).2
    have hδH := D16_le_H8 hδ16
    have hTb : P ⊓ D16 = D16 := by
      refine le_antisymm inf_le_right fun g hg => ?_
      by_cases hgR : g ∈ R8
      · exact hRT hgR
      · have hgH := D16_le_H8 hg
        have hty : typeP g = typeP δ := by
          obtain ⟨u, b, hu, rfl⟩ := hg
          obtain ⟨u₂, b₂, hu₂, rfl⟩ := hδ16
          rw [typeP_of_D16 u b hu hgR, typeP_of_D16 u₂ b₂ hu₂ hδD]
        have h1 : g * δ⁻¹ ∈ R8 := by
          rw [← typeP_eq_one_iff (mul_mem hgH (inv_mem hδH)), typeP_mul hgH (inv_mem hδH),
            typeP_inv hδH, hty]
          exact mul_inv_cancel _
        have := mul_mem (hRT h1) hδ
        rwa [mul_assoc, inv_mul_cancel, mul_one] at this
    exact ⟨8, ⟨(MulEquiv.subgroupCongr hTb).trans
      ((MonoidHom.ofInjective dih8_injective).trans (MulEquiv.subgroupCongr range_dih8)).symm⟩⟩

theorem autPair_H8 (hP1 : R8 ≤ P) (hP2 : P ≤ H8) : AutPair P R8 := by
  have hk8C : ∀ d ∈ R8, k8 * d = d * k8 := by
    rintro _ ⟨u, c, hu, rfl⟩
    exact k8_comm_R8 u c hu
  have hnot : PairCaseOne P R8 → k8 ∉ P := fun h1 hk => k8_not_mem_R8 (h1 k8 hk hk8C)
  refine ⟨fun R' hR' => gen3_H8 (hR'.trans hP2), ?_, fun h1 r₁ hr₁ r₂ hr₂ hn₁ hn₂ => ?_,
    fun h1 E hED hE4 hEsq c hc hcE => ?_, fun h1 σ hσ hσD hσ2 => ?_,
    fun k hk => two_H8 hP1 hP2 hk⟩
  · by_cases hk : k8 ∈ P
    · exact Or.inr ⟨k8, hk, hk8C, k8_not_mem_R8, by rw [pow_two]; exact k8_mul_k8,
        by rw [card_R8], fun c hc hcD => centralizer_cases hP2 hc hcD⟩
    · left
      intro c hc hcD
      refine (centralizer_cases hP2 hc hcD).resolve_right fun h => hk ?_
      have := mul_mem (inv_mem hc) (hP1 h)
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · have hk := hnot h1
    have H1 := hP2 hr₁
    have H2 := hP2 hr₂
    rw [← typeP_eq_one_iff (mul_mem H1 (inv_mem H2)), typeP_mul H1 (inv_mem H2), typeP_inv H2]
    refine index_aux _ _ (fun h => hn₁ ((typeP_eq_one_iff H1).mp h))
      (fun h => hn₂ ((typeP_eq_one_iff H2).mp h)) (typeP_ne_kap hP1 hP2 hk hr₁)
      (typeP_ne_kap hP1 hP2 hk hr₂) ?_
    rw [← typeP_mul H1 H2]
    exact typeP_ne_kap hP1 hP2 hk (mul_mem hr₁ hr₂)
  · have hk := hnot h1
    obtain ⟨e, heE, he1, hez⟩ : ∃ e ∈ E, e ≠ 1 ∧ e ≠ z8 := by
      by_contra hne
      push Not at hne
      have h2 := card_le_of_forall_mem_finset E {1, z8} fun x hx => by
        by_cases hx1 : x = 1
        · simp [hx1]
        · simp [hne x hx hx1]
      have := h2.trans Finset.card_le_two
      omega
    obtain ⟨u₁, c₁, hu₁, he⟩ := hED heE
    rcases hu₁ with rfl | rfl
    · exfalso
      have he2 := hEsq e heE
      rw [← he, pow_two] at he2
      rcases rot_inv_cases c₁ he2 with h | h
      · exact he1 (he ▸ h)
      · exact hez (he ▸ h)
    · obtain ⟨u, b, rfl⟩ := hP2 hc
      have hcomm := hcE e heE
      rw [← he] at hcomm
      rcases typeP_cases u b (dbit8_of_comm_refl u b c₁ hcomm) with h | h
      · exact (typeP_eq_one_iff (aff8_mem_H8 u b)).mp h
      · exact absurd h (typeP_ne_kap hP1 hP2 hk hc)
  · have hk := hnot h1
    obtain ⟨u₁, b₁, rfl⟩ := hP2 hσ
    have hb₁ : dbit8 b₁ = 1 := by
      rcases zmod2_cases (dbit8 b₁) with h | h
      · rcases typeP_cases u₁ b₁ h with h' | h'
        · exact absurd ((typeP_eq_one_iff (aff8_mem_H8 _ _)).mp h') hσD
        · exact absurd h' (typeP_ne_kap hP1 hP2 hk hσ)
      · exact h
    have hσσ : aff8 u₁ b₁ * aff8 u₁ b₁ = 1 := by rw [← pow_two]; exact hσ2
    have hf₁ : fbit8 u₁ = 0 := by
      rcases zmod2_cases (fbit8 u₁) with h | h
      · exact h
      · exact absurd hσσ (not_inv_FD u₁ b₁ h hb₁)
    refine (card_le_of_forall_mem_finset _ {1, z8} fun x hx => ?_).trans Finset.card_le_two
    obtain ⟨hxR, hxC⟩ := mem_inf.mp hx
    obtain ⟨u, c, hu, rfl⟩ := hxR
    rw [mem_centralizer_singleton_iff] at hxC
    rcases reflCent_D16 u₁ b₁ u (2 * c) hf₁ hb₁ ((fbit8_eq_zero_iff u).mpr hu) hσσ hxC with
      h | h | h | h
    · simp [h]
    · simp [h]
    · exact absurd (h ▸ ⟨u, c, hu, rfl⟩ : aff8 u₁ b₁ ∈ R8) hσD
    · exfalso
      apply hσD
      have hσ' : aff8 u₁ b₁ = z8⁻¹ * aff8 u (2 * c) := by rw [h, inv_mul_cancel_left]
      rw [hσ']
      exact mul_mem (inv_mem z8_memR) ⟨u, c, hu, rfl⟩

end CFSG.ComponentClassification.HSDihedral.H8
