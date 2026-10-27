module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511K
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511M
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.GH74.GLS.IVK.Lifted

theorem commute_of_mul_sq_L512 {X : Type*} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have h1 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
  rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_left ha, inv_eq_of_mul_eq_one_left hb]

section DSDFour

variable {M : Type} [Group M] [Finite M]

theorem dsd_mem_of_commute_L512 (hM : IsPGroup 2 M) {A : Subgroup M} (hA : IsCyclic ↥A) {u : M}
    (hu : u ∈ A) (hu4 : orderOf u = 4) (hinv : ∀ x : M, x ∉ A → x * u * x⁻¹ = u⁻¹) {v : M}
    (hvA : v ∉ A) {c : M} (hc : c * v = v * c) :
    c = 1 ∨ c = u * u ∨ c = v ∨ c = v * (u * u) := by
  have hu4' := CFSG.GH74.GLS.IVK.Lifted.pow_four_aux hu4
  have hww : (u * u) * (u * u) = 1 := by
    calc (u * u) * (u * u) = u * (u * (u * u)) := by group
      _ = 1 := hu4'
  have hw1 : u * u ≠ 1 := fun h1 => by
    have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h1)
    rw [hu4] at h2
    omega
  have hA' : ∀ c ∈ A, c * v = v * c → c = 1 ∨ c = u * u := by
    intro c hcA hcv
    by_cases hcc : c * c = 1
    · by_cases hc1 : c = 1
      · exact Or.inl hc1
      · exact Or.inr (CFSG.GH74.GLS.Stage1.Thm3.Sec6.B.cyclic_invol_unique hA hcA (mul_mem hu hu)
          hcc hww hc1 hw1)
    · exfalso
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hM) c
      have hk2 : 2 ≤ k := by
        by_contra hlt
        apply hcc
        have h2 : orderOf c ∣ 2 := by
          rw [hk]
          exact (Nat.pow_dvd_pow 2 (show k ≤ 1 by omega)).trans (by norm_num)
        have h1 := orderOf_dvd_iff_pow_eq_one.mp h2
        rwa [sq] at h1
      set c' := c ^ 2 ^ (k - 2) with hc'
      have hdvd : 2 ^ (k - 2) ∣ orderOf c := by
        rw [hk]
        exact Nat.pow_dvd_pow 2 (by omega)
      have hc'4 : orderOf c' = 4 := by
        rw [hc', orderOf_pow_of_dvd (by positivity) hdvd, hk, Nat.pow_div (by omega) (by norm_num),
          show k - (k - 2) = 2 by omega]
      have hc'A : c' ∈ A := pow_mem hcA _
      have hc'v : c' * v = v * c' := (Commute.pow_left hcv _).eq
      have hvu : v * u * v⁻¹ = u := by
        rcases eq_or_inv_of_orderOf_four hA hu hc'A hu4 hc'4 with h1 | h1
        · rw [← h1, ← hc'v, mul_inv_cancel_right]
        · have h2 : v * u⁻¹ * v⁻¹ = u⁻¹ := by rw [← h1, ← hc'v, mul_inv_cancel_right]
          have h3 := congrArg (·⁻¹) h2
          simpa [mul_assoc] using h3
      have h4 := hinv v hvA
      rw [hvu] at h4
      apply hw1
      calc u * u = u * u⁻¹ := by rw [← h4]
        _ = 1 := mul_inv_cancel u
  by_cases hcA : c ∈ A
  · rcases hA' c hcA hc with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · have h1 := dsd_inv_mul_mem hu4 hinv hvA hcA
    have h2 : v⁻¹ * c * v = v * (v⁻¹ * c) := by
      calc v⁻¹ * c * v = v⁻¹ * (c * v) := by group
        _ = v⁻¹ * (v * c) := by rw [hc]
        _ = v * (v⁻¹ * c) := by group
    rcases hA' _ h1 (by rw [← h2]) with h3 | h3
    · right; right; left
      calc c = v * (v⁻¹ * c) := by group
        _ = v := by rw [h3, mul_one]
    · right; right; right
      calc c = v * (v⁻¹ * c) := by group
        _ = v * (u * u) := by rw [h3]

theorem dsd_mem_of_commute_four_L512 (hM : IsPGroup 2 M) (hD : DSDData M) {a b : M}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : a * b = b * a) {d : M} (hda : d * a = a * d) (hdb : d * b = b * d) :
    d = a * b ∨ d = a ∨ d = b ∨ d = 1 := by
  obtain ⟨A, u, hA, hu, hu4, -, hinv⟩ := hD
  have hout : a ∉ A ∨ b ∉ A := by
    by_contra h
    push Not at h
    exact hab (CFSG.GH74.GLS.Stage1.Thm3.Sec6.B.cyclic_invol_unique hA h.1 h.2 ha2 hb2 ha1 hb1)
  rcases hout with haA | hbA
  · have hb := dsd_mem_of_commute_L512 hM hA hu hu4 hinv haA hc.symm
    have hd := dsd_mem_of_commute_L512 hM hA hu hu4 hinv haA hda
    rcases hb with hb | hb | hb | hb
    · exact absurd hb hb1
    · rw [← hb] at hd
      rcases hd with hd | hd | hd | hd
      · exact Or.inr (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hd)
      · exact Or.inl hd
    · exact absurd hb.symm hab
    · have hw : u * u = a * b := by
        rw [hb, ← mul_assoc, ha2, one_mul]
      rw [← hb, hw] at hd
      rcases hd with hd | hd | hd | hd
      · exact Or.inr (Or.inr (Or.inr hd))
      · exact Or.inl hd
      · exact Or.inr (Or.inl hd)
      · exact Or.inr (Or.inr (Or.inl hd))
  · have ha := dsd_mem_of_commute_L512 hM hA hu hu4 hinv hbA hc
    have hd := dsd_mem_of_commute_L512 hM hA hu hu4 hinv hbA hdb
    rcases ha with ha | ha | ha | ha
    · exact absurd ha ha1
    · rw [← ha, ← hc] at hd
      rcases hd with hd | hd | hd | hd
      · exact Or.inr (Or.inr (Or.inr hd))
      · exact Or.inr (Or.inl hd)
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inl hd
    · exact absurd ha hab
    · have hw : u * u = a * b := by
        rw [hc, ha, ← mul_assoc, hb2, one_mul]
      rw [← ha, hw] at hd
      rcases hd with hd | hd | hd | hd
      · exact Or.inr (Or.inr (Or.inr hd))
      · exact Or.inl hd
      · exact Or.inr (Or.inr (Or.inl hd))
      · exact Or.inr (Or.inl hd)

end DSDFour

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem dsdData_of_dihedral_or_semidihedral_L512 {Q : Subgroup G}
    (hQ : AschbacherTheorem3.IsDihedralTwoGroup Q ∨ AschbacherTheorem3.IsSemidihedralTwoGroup Q)
    (h4 : 4 < Nat.card Q) : DSDData ↥Q := by
  rcases hQ with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hcard : Nat.card Q = 2 * 2 ^ (n - 1) := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hn3 : 3 ≤ n := by
      by_contra hlt
      have hn2 : n = 2 := by omega
      rw [hn2] at hcard
      norm_num at hcard
      omega
    have h4d : 4 ∣ 2 ^ (n - 1) := by
      rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
      exact dvd_mul_of_dvd_right (by norm_num) _
    have : NeZero (2 ^ (n - 1)) := ⟨by positivity⟩
    exact (dsdData_dihedral (2 ^ (n - 1)) h4d).congr e.symm
  · exact (dsdData_semidihedral n hn).congr e.symm

theorem mem_of_commute_four_of_dsd_L512 {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hD : DSDData ↥Q)
    {a b : G} (haQ : a ∈ Q) (hbQ : b ∈ Q) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) {d : G} (hdQ : d ∈ Q) (hda : d * a = a * d)
    (hdb : d * b = b * d) : d = a * b ∨ d = a ∨ d = b ∨ d = 1 := by
  have h := dsd_mem_of_commute_four_L512 (a := ⟨a, haQ⟩) (b := ⟨b, hbQ⟩) (d := ⟨d, hdQ⟩) hQ2 hD
    (Subtype.ext ha2) (Subtype.ext hb2) (fun h1 => ha1 (congrArg Subtype.val h1))
    (fun h1 => hb1 (congrArg Subtype.val h1)) (fun h1 => hab (congrArg Subtype.val h1))
    (Subtype.ext hc) (Subtype.ext hda) (Subtype.ext hdb)
  rcases h with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem conj_cube_of_fpf_L512 {V : Subgroup G} (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    {g : G} (hgV : ∀ v ∈ V, g * v * g⁻¹ ∈ V) (hfix : ∀ v ∈ V, g * v * g⁻¹ = v → v = 1) {v : G}
    (hv : v ∈ V) :
    g ^ 3 * v * (g ^ 3)⁻¹ = v ∧ v * (g * v * g⁻¹) * (g ^ 2 * v * (g ^ 2)⁻¹) = 1 := by
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    commute_of_mul_sq_L512 (hVsq a ha) (hVsq b hb) (hVsq _ (mul_mem ha hb))
  obtain ⟨v₁, hv₁⟩ : ∃ w, g * v * g⁻¹ = w := ⟨_, rfl⟩
  obtain ⟨v₂, hv₂⟩ : ∃ w, g * v₁ * g⁻¹ = w := ⟨_, rfl⟩
  obtain ⟨v₃, hv₃⟩ : ∃ w, g * v₂ * g⁻¹ = w := ⟨_, rfl⟩
  have hv₁V : v₁ ∈ V := hv₁ ▸ hgV v hv
  have hv₂V : v₂ ∈ V := hv₂ ▸ hgV v₁ hv₁V
  have hv₃V : v₃ ∈ V := hv₃ ▸ hgV v₂ hv₂V
  have h2 : g ^ 2 * v * (g ^ 2)⁻¹ = v₂ := by
    rw [sq, ← hv₂, ← hv₁]
    group
  have h3 : g ^ 3 * v * (g ^ 3)⁻¹ = v₃ := by
    rw [pow_succ, sq, ← hv₃, ← hv₂, ← hv₁]
    group
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b hab => by
    rwa [mul_left_inj, mul_right_inj] at hab
  have hne1 : ∀ a : G, a ≠ 1 → g * a * g⁻¹ ≠ 1 := fun a ha h1 => ha (by
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  rw [h2, h3, hv₁]
  by_cases hv1 : v = 1
  · subst hv1
    have hv₁1 : v₁ = 1 := by rw [← hv₁]; group
    have hv₂1 : v₂ = 1 := by rw [← hv₂, hv₁1]; group
    have hv₃1 : v₃ = 1 := by rw [← hv₃, hv₂1]; group
    rw [hv₁1, hv₂1, hv₃1]
    exact ⟨rfl, by group⟩
  have hv₁1 : v₁ ≠ 1 := hv₁ ▸ hne1 v hv1
  have hv₂1 : v₂ ≠ 1 := hv₂ ▸ hne1 v₁ hv₁1
  have hvv₁ : v ≠ v₁ := fun h1 => hv1 (hfix v hv (hv₁.trans h1.symm))
  have hv₁v₂ : v₁ ≠ v₂ := fun h1 => hv₁1 (hfix v₁ hv₁V (hv₂.trans h1.symm))
  have hvv₂ : v ≠ v₂ := by
    intro h1
    have h4 : g * (v * v₁) * g⁻¹ = v * v₁ := by
      calc g * (v * v₁) * g⁻¹ = (g * v * g⁻¹) * (g * v₁ * g⁻¹) := by group
        _ = v₁ * v := by rw [hv₁, hv₂, ← h1]
        _ = v * v₁ := hcomm v₁ hv₁V v hv
    have h5 := hfix _ (mul_mem hv hv₁V) h4
    apply hvv₁
    rw [eq_inv_of_mul_eq_one_right h5, inv_eq_of_mul_eq_one_left (hVsq v hv)]
  have hv₃v : v₃ = v := by
    rcases mem_of_card_le_four hV4.le (one_mem V) hv hv₁V hv₂V (Ne.symm hv1) (Ne.symm hv₁1)
      (Ne.symm hv₂1) hvv₁ hvv₂ hv₁v₂ hv₃V with h1 | h1 | h1 | h1
    · exact absurd (hv₃.trans h1) (hne1 v₂ hv₂1)
    · exact h1
    · exact absurd (hinj _ _ ((hv₃.trans h1).trans hv₁.symm)) (Ne.symm hvv₂)
    · exact absurd (hfix v₂ hv₂V (hv₃.trans h1)) hv₂1
  refine ⟨hv₃v, ?_⟩
  have hP : g * (v * v₁ * v₂) * g⁻¹ = v * v₁ * v₂ := by
    calc g * (v * v₁ * v₂) * g⁻¹ = (g * v * g⁻¹) * (g * v₁ * g⁻¹) * (g * v₂ * g⁻¹) := by group
      _ = v₁ * v₂ * v := by rw [hv₁, hv₂, hv₃, hv₃v]
      _ = v * (v₁ * v₂) := hcomm _ (mul_mem hv₁V hv₂V) v hv
      _ = v * v₁ * v₂ := by group
  exact hfix _ (mul_mem (mul_mem hv hv₁V) hv₂V) hP

end CFSG.ComponentClassification.Foote5
