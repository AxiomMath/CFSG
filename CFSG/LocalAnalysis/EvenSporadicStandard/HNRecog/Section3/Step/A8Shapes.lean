module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.Perm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.MemQz

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem isConj_coe_of_isConj {G : Type} [Group G] {K : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥K) {s t : alternatingGroup (Fin 8)}
    (h : IsConj s t) : IsConj (φ s : G) (φ t : G) :=
  (K.subtype.comp φ.toMonoidHom).map_isConj h

private theorem isConj_left_iff_of_isConj {G : Type} [Group G] {c x y : G}
    (h : IsConj x y) : IsConj c x ↔ IsConj c y :=
  ⟨fun hx => hx.trans h, fun hy => hy.trans h.symm⟩

private theorem coe_mul_phi {G : Type} [Group G] {K : Subgroup G}
    (φ : alternatingGroup (Fin 8) ≃* ↥K) (s t : alternatingGroup (Fin 8)) :
    (φ s : G) * (φ t : G) = (φ (s * t) : G) := by
  have h : K.subtype (φ (s * t)) = K.subtype (φ s) * K.subtype (φ t) := by
    rw [map_mul φ s t, map_mul]
  exact h.symm

private theorem inv_cases_of_A8 (hI : TwoHSInterface) {G : Type} [Group G] [Finite G]
    {a z : G} (h : IsF5Type a z) (hF1 : Fusion1Facts a z) {K : Subgroup G}
    (hK : K ≤ Gx a) (hKder : K ≤ derivedOf (Gx a)) (φ : alternatingGroup (Fin 8) ≃* ↥K)
    {s : alternatingGroup (Fin 8)} (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) :
    IsConj a (φ s : G) ∨
      (IsConj z (φ s : G) ∧ IsConj a (a * (φ s : G)) ∧ a ∈ Qz (φ s : G)) := by
  have htmem : (φ s : G) ∈ derivedOf (Gx a) := hKder (φ s).2
  have ht2 : orderOf (φ s : G) = 2 := by
    rw [Subgroup.orderOf_coe, φ.orderOf_eq]
    exact orderOf_eq_prime hs2 hs1
  rcases inv_mem_derivedOf_cases hI h hF1 htmem ht2 with haeq | hcase | hcase
  · exfalso
    have hcentral : ∀ u : alternatingGroup (Fin 8), u * s = s * u := by
      intro u
      apply φ.injective
      apply Subtype.ext
      show ((φ (u * s) : ↥K) : G) = ((φ (s * u) : ↥K) : G)
      rw [← coe_mul_phi φ u s, ← coe_mul_phi φ s u]
      rw [haeq]
      exact (mem_Gx.mp (hK (φ u).2)).symm
    exact hs1 (eq_one_of_forall_commute hcentral)
  · exact Or.inr hcase
  · exact Or.inl hcase.1

theorem a8Shapes_of_cube (hI : TwoHSInterface) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z) (hCube : Vert CubeFacts a z) :
    A8Shapes a z := by
  have perfect : ∀ {K : Subgroup G} (hK : K ≤ Gx a)
      (φ : alternatingGroup (Fin 8) ≃* ↥K), K ≤ derivedOf (Gx a) := by
    intro K hK φ
    refine le_derivedOf_of_commutator_eq_top hK ?_
    exact commutator_eq_top_of_mulEquiv φ (commutator_alternatingGroup_eq_top (by simp))
  have h2211 : ∀ K : Subgroup G, K ≤ Gx a → ∀ φ : alternatingGroup (Fin 8) ≃* ↥K,
      ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2} →
        IsConj a (φ t : G) := by
    intro K hK φ t ht
    by_contra hna
    have hKder : K ≤ derivedOf (Gx a) := perfect hK φ
    have hAll : ∀ s : alternatingGroup (Fin 8),
        (s : Equiv.Perm (Fin 8)).cycleType = {2, 2} →
        IsConj z (φ s : G) ∧ IsConj a (a * (φ s : G)) ∧ a ∈ Qz (φ s : G) := by
      intro s hs
      obtain ⟨hs2, hs1⟩ := sq_eq_one_of_cycleType_two_two hs
      have hconjG : IsConj (φ s : G) (φ t : G) :=
        isConj_coe_of_isConj φ (isConj_of_cycleType_two_two hs ht)
      have hna' : ¬ IsConj a (φ s : G) :=
        fun h' => hna ((isConj_left_iff_of_isConj hconjG).mp h')
      rcases inv_cases_of_A8 hI h hF1.self hK hKder φ hs2 hs1 with h' | h'
      · exact absurd h' hna'
      · exact h'
    obtain ⟨t₀, t₁, t₂, ht₀, ht₁, ht₂, ht₀₁, ht₀₂, hcomm₁, hcomm₂, hord⟩ :=
      exists_triple_cycleType_two_two
    have haa : a * a = 1 := by rw [← pow_two, ← h.orderOf_a]; exact pow_orderOf_eq_one a
    have hcomm₁' : (φ t₁ : G) * (φ t₀ : G) = (φ t₀ : G) * (φ t₁ : G) := by
      rw [coe_mul_phi φ t₁ t₀, coe_mul_phi φ t₀ t₁, hcomm₁]
    have hcomm₂' : (φ t₂ : G) * (φ t₀ : G) = (φ t₀ : G) * (φ t₂ : G) := by
      rw [coe_mul_phi φ t₂ t₀, coe_mul_phi φ t₀ t₂, hcomm₂]
    have hc₁ : ((t₁ * t₀ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
      rw [← hcomm₁]
      exact ht₀₁
    have hc₂ : ((t₂ * t₀ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)).cycleType = {2, 2} := by
      rw [← hcomm₂]
      exact ht₀₂
    have hEq₁ : (a * (φ t₁ : G)) * (φ t₀ : G) = a * (φ (t₁ * t₀) : G) := by
      rw [mul_assoc, coe_mul_phi φ t₁ t₀]
    have hEq₂ : (a * (φ t₂ : G)) * (φ t₀ : G) = a * (φ (t₂ * t₀) : G) := by
      rw [mul_assoc, coe_mul_phi φ t₂ t₀]
    have haQz : a ∈ Qz (φ t₀ : G) := (hAll t₀ ht₀).2.2
    have hxt₁ : (a * (φ t₁ : G)) * (φ t₀ : G) = (φ t₀ : G) * (a * (φ t₁ : G)) :=
      (Commute.mul_left (mem_Gx.mp (hK (φ t₀).2)) hcomm₁').eq
    have hxt₁' : IsConj a ((a * (φ t₁ : G)) * (φ t₀ : G)) := by
      rw [hEq₁]
      exact (hAll (t₁ * t₀) hc₁).2.1
    have ha_r₁ : a * (φ t₁ : G) ∈ Qz (φ t₀ : G) :=
      mem_Qz_of_isConj_mul hI h hF1 (x := a * (φ t₁ : G)) (t := (φ t₀ : G))
        (hAll t₁ ht₁).2.1 (hAll t₀ ht₀).1 hxt₁ hxt₁'
    have hr₁ : (φ t₁ : G) ∈ Qz (φ t₀ : G) := by
      have h := (Qz (φ t₀ : G)).mul_mem haQz ha_r₁
      simpa [← mul_assoc, haa] using h
    have hxt₂ : (a * (φ t₂ : G)) * (φ t₀ : G) = (φ t₀ : G) * (a * (φ t₂ : G)) :=
      (Commute.mul_left (mem_Gx.mp (hK (φ t₀).2)) hcomm₂').eq
    have hxt₂' : IsConj a ((a * (φ t₂ : G)) * (φ t₀ : G)) := by
      rw [hEq₂]
      exact (hAll (t₂ * t₀) hc₂).2.1
    have ha_r₂ : a * (φ t₂ : G) ∈ Qz (φ t₀ : G) :=
      mem_Qz_of_isConj_mul hI h hF1 (x := a * (φ t₂ : G)) (t := (φ t₀ : G))
        (hAll t₂ ht₂).2.1 (hAll t₀ ht₀).1 hxt₂ hxt₂'
    have hr₂ : (φ t₂ : G) ∈ Qz (φ t₀ : G) := by
      have h := (Qz (φ t₀ : G)).mul_mem haQz ha_r₂
      simpa [← mul_assoc, haa] using h
    have hr₁₂ : (φ t₁ : G) * (φ t₂ : G) ∈ Qz (φ t₀ : G) :=
      (Qz (φ t₀ : G)).mul_mem hr₁ hr₂
    have hord₁₂ : orderOf ((φ t₁ : G) * (φ t₂ : G)) = 3 := by
      rw [coe_mul_phi φ t₁ t₂, Subgroup.orderOf_coe, MulEquiv.orderOf_eq φ (t₁ * t₂), hord]
    have hQz_pg : IsPGroup 2 ↥(Qz (φ t₀ : G)) := by
      show IsPGroup 2 ↥((CFSG.pCore 2 ↥(Gx (φ t₀ : G))).map (Gx (φ t₀ : G)).subtype)
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(Gx (φ t₀ : G)))).map (Gx (φ t₀ : G)).subtype
    have hordQ : orderOf (⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G))) = 3 :=
      (Subgroup.orderOf_coe (⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G)))).symm.trans
        (show orderOf ((⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G))) : G) = 3 from hord₁₂)
    have hne₁₂ : (⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G))) ≠ 1 := by
      intro h1
      have h3 : orderOf (⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G))) = 1 := by
        rw [h1, orderOf_one]
      rw [hordQ] at h3
      exact (by norm_num : (3 : ℕ) ≠ 1) h3
    have h2dvd : 2 ∣ orderOf (⟨(φ t₁ : G) * (φ t₂ : G), hr₁₂⟩ : ↥(Qz (φ t₀ : G))) :=
      IsPGroup.dvd_orderOf hQz_pg hne₁₂
    rw [hordQ] at h2dvd
    obtain ⟨c, hc⟩ := h2dvd
    omega
  have h2222 : ∀ K : Subgroup G, K ≤ Gx a → ∀ φ : alternatingGroup (Fin 8) ≃* ↥K,
      ∀ t : alternatingGroup (Fin 8), (t : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} →
        IsConj z (φ t : G) := by
    intro K hK φ t ht
    by_contra hnz
    have hKder : K ≤ derivedOf (Gx a) := perfect hK φ
    have hAll : ∀ s : alternatingGroup (Fin 8),
        (s : Equiv.Perm (Fin 8)).cycleType = {2, 2, 2, 2} → IsConj a (φ s : G) := by
      intro s hs
      obtain ⟨hs2, hs1⟩ := sq_eq_one_of_cycleType_two_two_two_two hs
      have hconjG : IsConj (φ s : G) (φ t : G) :=
        isConj_coe_of_isConj φ (isConj_of_cycleType_two_two_two_two hs ht)
      have hnz' : ¬ IsConj z (φ s : G) :=
        fun h' => hnz ((isConj_left_iff_of_isConj hconjG).mp h')
      rcases inv_cases_of_A8 hI h hF1.self hK hKder φ hs2 hs1 with h' | h'
      · exact h'
      · exact absurd h'.1 hnz'
    obtain ⟨E₀, hE₀⟩ := exists_isElemTwo_three
    refine hCube.self.no_cube ⟨(E₀.map φ.toMonoidHom).map K.subtype, ?_, ?_⟩
    · exact isElemTwo_map K.subtype K.subtype_injective
        (isElemTwo_map φ.toMonoidHom φ.injective hE₀)
    · intro x hx hx2 hx1
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨s, _hsE₀, hsk⟩ := Subgroup.mem_map.mp hk
      have hfs : (K.subtype.comp φ.toMonoidHom) s = K.subtype k :=
        congrArg (fun u : ↥K => K.subtype u) hsk
      have hf_inj : Function.Injective (K.subtype.comp φ.toMonoidHom) :=
        K.subtype_injective.comp φ.injective
      have hs2 : s ^ 2 = 1 := by
        refine hf_inj ?_
        rw [map_pow, hfs, map_one]
        exact hx2
      have hs1 : s ≠ 1 := by
        intro h1
        apply hx1
        have hthis : (K.subtype.comp φ.toMonoidHom) s = 1 := by rw [h1, map_one]
        rw [hfs] at hthis
        exact hthis
      rcases cycleType_eq_of_sq_eq_one hs2 hs1 with hc | hc
      · rw [← hfs]
        exact h2211 K hK φ s hc
      · rw [← hfs]
        exact hAll s hc
  exact ⟨h2211, h2222⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
