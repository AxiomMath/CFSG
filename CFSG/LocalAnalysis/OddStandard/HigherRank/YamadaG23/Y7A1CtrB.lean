module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6Q8b
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6SGen

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] {A V P3 D : Subgroup G} {a₁ b₁ a₂ b₂ z : G}

private lemma sq_eq_one_of_mem_zpowers {z g : G} (hz2 : z ^ 2 = 1)
    (hg : g ∈ Subgroup.zpowers z) : g ^ 2 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_mem_zpowers hg).trans (orderOf_dvd_iff_pow_eq_one.mpr hz2))

private lemma notMem_zpowers_of_sq {z g : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hg2 : g ^ 2 = z) : g ∉ Subgroup.zpowers z := by
  intro hg
  have h1 : g ^ 2 = 1 := sq_eq_one_of_mem_zpowers hz2 hg
  rw [hg2] at h1
  exact hz h1

private lemma mem_normalizer_zpowers {z k : G} (hk : k * z * k⁻¹ = z) :
    k ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  show Subgroup.zpowers (k * z * k⁻¹) = Subgroup.zpowers z
  rw [hk]

private def supComm (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : Subgroup G where
  carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
  mul_mem' := by
    rintro a b ⟨h₁, hh₁, k₁, hk₁, rfl⟩ ⟨h₂, hh₂, k₂, hk₂, rfl⟩
    refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, k₁ * k₂, K.mul_mem hk₁ hk₂, ?_⟩
    calc (h₁ * k₁) * (h₂ * k₂) = h₁ * (k₁ * h₂) * k₂ := by group
      _ = h₁ * (h₂ * k₁) * k₂ := by rw [← hcomm h₂ hh₂ k₁ hk₁]
      _ = (h₁ * h₂) * (k₁ * k₂) := by group
  one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨h, hh, k, hk, rfl⟩
    refine ⟨h⁻¹, H.inv_mem hh, k⁻¹, K.inv_mem hk, ?_⟩
    rw [mul_inv_rev]
    exact (hcomm h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)).symm

private lemma le_supComm (H K : Subgroup G)
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) : H ⊔ K ≤ supComm H K hcomm := by
  apply sup_le
  · intro h hh
    exact ⟨h, hh, 1, K.one_mem, by simp⟩
  · intro k hk
    exact ⟨1, H.one_mem, k, hk, by simp⟩

private lemma mem_sup_of_comm {H K : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, x = h * k :=
  le_supComm H K hcomm hx

private lemma mul_notMem_left {U W Z : Subgroup G} (hUW : U ⊓ W = Z) {u w : G}
    (hu : u ∈ U) (hw : w ∈ W) (hwZ : w ∉ Z) : u * w ∉ U := by
  intro h
  have hwU : w ∈ U := by
    have h' : u⁻¹ * (u * w) ∈ U := U.mul_mem (U.inv_mem hu) h
    simpa using h'
  exact hwZ (by rw [← hUW]; exact ⟨hwU, hw⟩)

private lemma mul_notMem_right {U W Z : Subgroup G} (hUW : U ⊓ W = Z) {u w : G}
    (hu : u ∈ U) (hw : w ∈ W) (huZ : u ∉ Z) : u * w ∉ W := by
  intro h
  have huW : u ∈ W := by
    have h' : (u * w) * w⁻¹ ∈ W := W.mul_mem h (W.inv_mem hw)
    simpa using h'
  exact huZ (by rw [← hUW]; exact ⟨hu, huW⟩)

private lemma inf_eq_zpowers {z : G} {A V U : Subgroup G} (hUA : U ≤ A)
    (hVA : A ⊓ V = zpowers z) (hzU : z ∈ U) : U ⊓ V = zpowers z := by
  apply le_antisymm
  · intro x hx
    rw [← hVA]
    exact ⟨hUA hx.1, hx.2⟩
  · intro x hx
    exact ⟨(Subgroup.zpowers_le.mpr hzU) hx, (le_of_eq hVA.symm).trans inf_le_right hx⟩

theorem y7a_orbit_sub {S : Set G} (hzD : z ∈ D) (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hS : IsOrbitMod P3 (zpowers z) S) (hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hex : ∃ x ∈ S, x ∈ D) : ∀ y ∈ S, y ∈ D := by
  intro y hy
  obtain ⟨x, hxS, hxD⟩ := hex
  obtain ⟨k, hk, hkz⟩ := y6_orbitMod_trans (T := P3) (Z := Subgroup.zpowers z)
    (fun k hk => mem_normalizer_zpowers (hP3z k hk)) hS hxS hy
  have hzD' : (k * x * k⁻¹)⁻¹ * y ∈ D := (Subgroup.zpowers_le.mpr hzD) hkz
  have hy_eq : y = (k * x * k⁻¹) * ((k * x * k⁻¹)⁻¹ * y) := by group
  rw [hy_eq]
  exact D.mul_mem (hDinv k hk x hxD) hzD'

theorem y7a_inv_W (hrel : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1) (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hW : IsOrbitMod P3 (zpowers z) ((closure {a₂, b₂} : Set G) \ (zpowers z : Set G)))
    (hzV : z ∈ V) (hVD : V ≤ D) (hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hVc : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), ∀ v ∈ V, w * v = v * w)
    (hWV : (closure {a₂, b₂} : Subgroup G) ⊓ V = zpowers z)
    (hne : ∃ x ∈ D, x ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V ∧ x ∉ V) :
    (closure {a₂, b₂} : Subgroup G) ≤ D := by
  obtain ⟨x, hxD, hxWV, hxV⟩ := hne
  obtain ⟨w, hwW, v, hvV, hxwv⟩ := mem_sup_of_comm hVc hxWV
  have hwD : w ∈ D := by
    have h : x * v⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem (hVD hvV))
    rw [hxwv] at h
    simpa using h
  have hwZ : w ∉ Subgroup.zpowers z := by
    intro hwz
    have hwV : w ∈ V := by
      have h : w ∈ (closure {a₂, b₂} : Subgroup G) ⊓ V := by rw [hWV]; exact hwz
      exact h.2
    exact hxV (by rw [hxwv]; exact V.mul_mem hwV hvV)
  have horb : ∀ y ∈ ((closure {a₂, b₂} : Set G) \
      (Subgroup.zpowers z : Set G)), y ∈ D :=
    y7a_orbit_sub (D := D) (P3 := P3) (z := z) (hVD hzV) hP3z hW hDinv
      ⟨w, ⟨hwW, hwZ⟩, hwD⟩
  intro y hyW
  by_cases hyZ : y ∈ Subgroup.zpowers z
  · exact (Subgroup.zpowers_le.mpr (hVD hzV)) hyZ
  · exact horb y ⟨hyW, hyZ⟩

theorem y7a_inv_U (hrel : Y6ARel a₁ b₁ a₂ b₂ z) (hz : z ≠ 1) (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hU : IsOrbitMod P3 (zpowers z) ((closure {a₁, b₁} : Set G) \ (zpowers z : Set G)))
    (hzV : z ∈ V) (hVD : V ≤ D) (hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hVc : ∀ w ∈ (closure {a₁, b₁} : Subgroup G), ∀ v ∈ V, w * v = v * w)
    (hUV : (closure {a₁, b₁} : Subgroup G) ⊓ V = zpowers z)
    (hne : ∃ x ∈ D, x ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V ∧ x ∉ V) :
    (closure {a₁, b₁} : Subgroup G) ≤ D := by
  obtain ⟨x, hxD, hxUV, hxV⟩ := hne
  obtain ⟨w, hwW, v, hvV, hxwv⟩ := mem_sup_of_comm hVc hxUV
  have hwD : w ∈ D := by
    have h : x * v⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem (hVD hvV))
    rw [hxwv] at h
    simpa using h
  have hwZ : w ∉ Subgroup.zpowers z := by
    intro hwz
    have hwV : w ∈ V := by
      have h : w ∈ (closure {a₁, b₁} : Subgroup G) ⊓ V := by rw [hUV]; exact hwz
      exact h.2
    exact hxV (by rw [hxwv]; exact V.mul_mem hwV hvV)
  have horb : ∀ y ∈ ((closure {a₁, b₁} : Set G) \
      (Subgroup.zpowers z : Set G)), y ∈ D :=
    y7a_orbit_sub (D := D) (P3 := P3) (z := z) (hVD hzV) hP3z hU hDinv
      ⟨w, ⟨hwW, hwZ⟩, hwD⟩
  intro y hyW
  by_cases hyZ : y ∈ Subgroup.zpowers z
  · exact (Subgroup.zpowers_le.mpr (hVD hzV)) hyZ
  · exact horb y ⟨hyW, hyZ⟩

theorem y7a_inv_UW (hA : A = closure {a₁, b₁, a₂, b₂}) (hrel : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : z ≠ 1) (hA32 : Nat.card ↥A = 32) (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hU : IsOrbitMod P3 (zpowers z) ((closure {a₁, b₁} : Set G) \ (zpowers z : Set G)))
    (hW : IsOrbitMod P3 (zpowers z) ((closure {a₂, b₂} : Set G) \ (zpowers z : Set G)))
    (h9 : IsOrbitMod P3 (zpowers z) ((A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G))))
    (hVA : A ⊓ V = zpowers z) (hVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a)
    (hVD : V ≤ D) (hDA : D ≤ A ⊔ V) (hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D)
    (hne : ∃ x ∈ D, x ∉ V) :
    (closure {a₁, b₁} : Subgroup G) ≤ D ∨ (closure {a₂, b₂} : Subgroup G) ≤ D := by
  obtain ⟨x, hxD, hxV⟩ := hne
  obtain ⟨a, haA, v, hvV, hxav⟩ := mem_sup_of_comm hVc (hDA hxD)
  have hzV : z ∈ V := by
    have h : z ∈ A ⊓ V := by rw [hVA]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    exact h.2
  have haZ : a ∉ Subgroup.zpowers z := by
    intro haz
    have haV : a ∈ V := by
      have h : a ∈ A ⊓ V := by rw [hVA]; exact haz
      exact h.2
    exact hxV (by rw [hxav]; exact V.mul_mem haV hvV)
  have hA32' : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← hA]; exact hA32
  have hcard := y6q8_card_UW hrel hz hA32'
  have hUW : (closure {a₁, b₁} : Subgroup G) ⊓ (closure {a₂, b₂} : Subgroup G) = zpowers z := by
    apply le_antisymm
    · intro y hy
      have hpair : y = 1 ∨ y = z := (hcard.2.2 y).mp ⟨hy.1, hy.2⟩
      rcases hpair with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    · exact Subgroup.zpowers_le.mpr
        ⟨by rw [← hrel.a1_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2,
          by rw [← hrel.a2_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2⟩
  by_cases haU : a ∈ (closure {a₁, b₁} : Subgroup G)
  · left
    have hzU : z ∈ (closure {a₁, b₁} : Subgroup G) := by
      rw [← hrel.a1_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
    have hUV : (closure {a₁, b₁} : Subgroup G) ⊓ V = zpowers z :=
      inf_eq_zpowers (by rw [hA]; exact y6q8_U_le_A) hVA hzU
    exact y7a_inv_U hrel hz hP3z hU hzV hVD hDinv
      (fun w hw v' hv' => hVc w (by rw [hA]; exact y6q8_U_le_A hw) v' hv') hUV
      ⟨x, hxD, by rw [hxav]; exact Subgroup.mul_mem_sup haU hvV, hxV⟩
  · by_cases haW : a ∈ (closure {a₂, b₂} : Subgroup G)
    · right
      have hzW : z ∈ (closure {a₂, b₂} : Subgroup G) := by
        rw [← hrel.a2_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
      have hWV : (closure {a₂, b₂} : Subgroup G) ⊓ V = zpowers z :=
        inf_eq_zpowers (by rw [hA]; exact y6q8_W_le_A) hVA hzW
      exact y7a_inv_W hrel hz hP3z hW hzV hVD hDinv
        (fun w hw v' hv' => hVc w (by rw [hA]; exact y6q8_W_le_A hw) v' hv') hWV
        ⟨x, hxD, by rw [hxav]; exact Subgroup.mul_mem_sup haW hvV, hxV⟩
    · right
      have haO : a ∈ (A : Set G) \
          ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) := by
        refine ⟨haA, ?_⟩
        simp only [Set.mem_union, not_or]
        exact ⟨haU, haW⟩
      have haD : a ∈ D := by
        have h : x * v⁻¹ ∈ D := D.mul_mem hxD (D.inv_mem (hVD hvV))
        rw [hxav] at h
        simpa using h
      have horb : ∀ y ∈ (A : Set G) \
          ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)), y ∈ D :=
        y7a_orbit_sub (D := D) (P3 := P3) (z := z) (hVD hzV) hP3z h9 hDinv
          ⟨a, haO, haD⟩
      have hb1U : b₁ ∈ (closure {a₁, b₁} : Subgroup G) := Subgroup.subset_closure (by simp)
      have hb2W : b₂ ∈ (closure {a₂, b₂} : Subgroup G) := Subgroup.subset_closure (by simp)
      have ha2W : a₂ ∈ (closure {a₂, b₂} : Subgroup G) := Subgroup.subset_closure (by simp)
      have hb1A : b₁ ∈ A := by rw [hA]; exact y6q8_U_le_A hb1U
      have hb2A : b₂ ∈ A := by rw [hA]; exact y6q8_W_le_A hb2W
      have ha2A : a₂ ∈ A := by rw [hA]; exact y6q8_W_le_A ha2W
      have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hrel.z_sq
      have hb1Z : b₁ ∉ Subgroup.zpowers z := notMem_zpowers_of_sq hz hz2 hrel.b1_sq
      have hb2Z : b₂ ∉ Subgroup.zpowers z := notMem_zpowers_of_sq hz hz2 hrel.b2_sq
      have ha2Z : a₂ ∉ Subgroup.zpowers z := notMem_zpowers_of_sq hz hz2 hrel.a2_sq
      have hb1a2O : b₁ * a₂ ∈ (A : Set G) \
          ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) := by
        refine ⟨A.mul_mem hb1A ha2A, ?_⟩
        simp only [Set.mem_union, not_or]
        exact ⟨mul_notMem_left hUW hb1U ha2W ha2Z, mul_notMem_right hUW hb1U ha2W hb1Z⟩
      have hb1b2O : b₁ * b₂ ∈ (A : Set G) \
          ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G)) := by
        refine ⟨A.mul_mem hb1A hb2A, ?_⟩
        simp only [Set.mem_union, not_or]
        exact ⟨mul_notMem_left hUW hb1U hb2W hb2Z, mul_notMem_right hUW hb1U hb2W hb1Z⟩
      have hw0D : (b₁ * a₂)⁻¹ * (b₁ * b₂) ∈ D :=
        D.mul_mem (D.inv_mem (horb (b₁ * a₂) hb1a2O)) (horb (b₁ * b₂) hb1b2O)
      have hw0eq : (b₁ * a₂)⁻¹ * (b₁ * b₂) = a₂⁻¹ * b₂ := by group
      have hw0W : (b₁ * a₂)⁻¹ * (b₁ * b₂) ∈ (closure {a₂, b₂} : Subgroup G) := by
        rw [hw0eq]
        exact mul_mem (inv_mem ha2W) hb2W
      have hw0Z : (b₁ * a₂)⁻¹ * (b₁ * b₂) ∉ Subgroup.zpowers z := by
        refine notMem_zpowers_of_sq hz hz2 ?_
        rw [hw0eq]
        have ha2A' : a₂ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := y6q8_W_le_A ha2W
        have hb2A' : b₂ ∈ (closure {a₁, b₁, a₂, b₂} : Subgroup G) := y6q8_W_le_A hb2W
        have hsq := y6q8_sq_mul hrel a₂⁻¹ ((closure {a₁, b₁, a₂, b₂}).inv_mem ha2A')
          b₂ hb2A'
        have h1 : (a₂⁻¹) ^ 2 = z := by
          rw [inv_pow, hrel.a2_sq]
          exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hrel.z_sq)
        have h2 : ⁅b₂, a₂⁻¹⁆ = z := by
          rw [commutatorElement_inv_right, hrel.comm2,
            y6q8_z_central hrel a₂⁻¹ ((closure {a₁, b₁, a₂, b₂}).inv_mem ha2A')]
          group
        rw [hsq, h1, hrel.b2_sq, h2]
        rw [show z * z = 1 from by simpa [pow_two] using hrel.z_sq]
        simp
      have hO : ∀ y ∈ ((closure {a₂, b₂} : Set G) \
          (Subgroup.zpowers z : Set G)), y ∈ D :=
        y7a_orbit_sub (D := D) (P3 := P3) (z := z) (hVD hzV) hP3z hW hDinv
          ⟨_, ⟨hw0W, hw0Z⟩, hw0D⟩
      intro y hyW
      by_cases hyZ : y ∈ Subgroup.zpowers z
      · exact (Subgroup.zpowers_le.mpr (hVD hzV)) hyZ
      · exact hO y ⟨hyW, hyZ⟩

end CFSG.OddStandard.HigherRank.YamadaG23
