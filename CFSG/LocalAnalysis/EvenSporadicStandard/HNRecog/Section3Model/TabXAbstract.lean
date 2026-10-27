module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXSix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXGroup

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

private theorem isConj_conj_right (g b x : G) : IsConj b (g * x * g⁻¹) ↔ IsConj b x :=
  ⟨fun h => h.trans (isConj_iff.2 ⟨g, rfl⟩).symm, fun h => h.trans (isConj_iff.2 ⟨g, rfl⟩)⟩

private theorem HIsA_conj_arg (a z b x g : G) : HIsA a z b (g * x * g⁻¹) ↔ HIsA a z b x := by
  unfold HIsA
  rw [isConj_conj_right g a x, isConj_conj_right g (a * z) x, isConj_conj_right g b x]

private theorem HIsB_conj_arg (z z₁ x g : G) : HIsB z z₁ (g * x * g⁻¹) ↔ HIsB z z₁ x := by
  unfold HIsB
  rw [isConj_conj_right g z x, isConj_conj_right g z₁ x]

private theorem conj_mul_az {a z k : G} (ha : a ∈ Subgroup.center G) (hk : k ∈ Gx z) (c : G) :
    k * (a * z * c) * k⁻¹ = a * z * (k * c * k⁻¹) := by
  have ha' : k * a = a * k := Subgroup.mem_center_iff.mp ha k
  have hz' : k * z = z * k := (mem_Gx.mp hk).symm
  have h : k * (a * z) = a * z * k := by
    calc k * (a * z) = (k * a) * z := by rw [mul_assoc]
      _ = (a * k) * z := by rw [ha']
      _ = a * (k * z) := by rw [mul_assoc]
      _ = a * (z * k) := by rw [hz']
      _ = a * z * k := by rw [mul_assoc]
  calc k * (a * z * c) * k⁻¹ = (k * (a * z)) * c * k⁻¹ := by group
    _ = a * z * (k * c * k⁻¹) := by rw [h]; group

theorem tabXSet_conj_mem {a z b z₁ k c : G} (ha : a ∈ Subgroup.center G) (hk : k ∈ Gx z)
    (i : Fin 2) (hc : c ∈ tabXSet a z b z₁ i) : k * c * k⁻¹ ∈ tabXSet a z b z₁ i := by
  fin_cases i
  · obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨(isConj_conj_right k b c).2 h1,
      (Gx z).mul_mem ((Gx z).mul_mem hk h2) ((Gx z).inv_mem hk), ?_⟩
    rw [← conj_mul_az ha hk c]
    exact (HIsA_conj_arg a z b _ k).2 h3
  · obtain ⟨h1, h2, h3⟩ := hc
    refine ⟨(isConj_conj_right k b c).2 h1,
      (Gx z).mul_mem ((Gx z).mul_mem hk h2) ((Gx z).inv_mem hk), ?_⟩
    rw [← conj_mul_az ha hk c]
    exact (HIsB_conj_arg z z₁ _ k).2 h3

private theorem not_HIsA_HIsB {a z b z₁ x : G}
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hA : HIsA a z b x) (hB : HIsB z z₁ x) : False := by
  unfold HIsA at hA
  unfold HIsB at hB
  rcases hA with h | h | h <;> rcases hB with h' | h'
  · exact (hnc 0 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 0 4 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 2 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 2 4 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 3 1 (by decide)) (by simpa using h.trans h'.symm)
  · exact (hnc 3 4 (by decide)) (by simpa using h.trans h'.symm)

theorem tabXSet_disjoint {a z b z₁ : G}
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j)) :
    ∀ i j, i ≠ j → Disjoint (tabXSet a z b z₁ i) (tabXSet a z b z₁ j) := by
  have h01 : Disjoint (tabXSet a z b z₁ 0) (tabXSet a z b z₁ 1) :=
    Set.disjoint_left.mpr fun c h0 h1 => not_HIsA_HIsB hnc h0.2.2 h1.2.2
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact (hij rfl).elim
      | exact h01
      | exact h01.symm

theorem tableX_orbits [Finite G] {a z b z₁ : G} (ha : a ∈ Subgroup.center G)
    (hnc : ∀ i j : Fin 5, i ≠ j →
      ¬ IsConj (![a, z, a * z, b, z₁] i) (![a, z, a * z, b, z₁] j))
    (hX : Nat.card ↥(Gx z) = 30720) (hB : {c | IsConj b c ∧ c ∈ Gx z}.ncard = 120)
    (c : Fin 2 → G) (hc : ∀ i, c i ∈ tabXSet a z b z₁ i)
    (hstab : ∀ i, Nat.card ↥(Gx z ⊓ Gx (c i)) = ![768, 384] i) :
    IsOrbitPartition (Gx z) {c | IsConj b c ∧ c ∈ Gx z} (tabXSet a z b z₁) ∧
      StabCard (Gx z) (tabXSet a z b z₁) ![768, 384] := by
  refine orbitPartition_of_rows (Gx z) {c | IsConj b c ∧ c ∈ Gx z} (tabXSet a z b z₁) c
    ![768, 384] ?_ (fun i j hij => tabXSet_disjoint hnc i j hij)
    (fun i k hk x hx => tabXSet_conj_mem ha hk i hx) hc hstab ?_
  · intro i x hx
    fin_cases i <;> exact ⟨hx.1, hx.2.1⟩
  · rw [hX, hB]
    decide

theorem map_conj_inf_normalized {X V : Subgroup G} {k : G} (hk : k ∈ X)
    (hV : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) (M : Subgroup G) :
    (M ⊓ V).map (MulAut.conj k).toMonoidHom = M.map (MulAut.conj k).toMonoidHom ⊓ V := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj k).injective, map_conj_eq_of_normalized hk hV]

theorem map_conj_stab_inf {X V : Subgroup G} {k : G} (hk : k ∈ X)
    (hV : ∀ x ∈ X, ∀ v ∈ V, x * v * x⁻¹ ∈ V) (c : G) :
    (X ⊓ Gx c ⊓ V).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c * k⁻¹) ⊓ V := by
  rw [map_conj_inf_normalized hk hV, map_conj_stab hk]

private theorem stab_norm {X R D : Subgroup G} (hR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (c : G) {m n : G} (hm : m ∈ X ⊓ Gx c ⊓ D)
    (hn : n ∈ X ⊓ Gx c ⊓ R ⊓ D) : m * n * m⁻¹ ∈ X ⊓ Gx c ⊓ R ⊓ D := by
  obtain ⟨⟨hmX, hmc⟩, hmD⟩ := hm
  obtain ⟨⟨⟨hnX, hnc⟩, hnR⟩, hnD⟩ := hn
  exact ⟨⟨⟨X.mul_mem (X.mul_mem hmX hnX) (X.inv_mem hmX),
    (Gx c).mul_mem ((Gx c).mul_mem hmc hnc) ((Gx c).inv_mem hmc)⟩, hR m hmX n hnR⟩,
    hD m hmX n hnD⟩

private theorem stab_le {X R D : Subgroup G} (c : G) : X ⊓ Gx c ⊓ R ⊓ D ≤ X ⊓ Gx c ⊓ D :=
  fun _ hx => ⟨hx.1.1, hx.2⟩

theorem tableX_row0 [Finite G] {X R D : Subgroup G} (hR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) {T : Set G} (hT : IsConjOrbit X T) {c₀ : G}
    (hc₀ : c₀ ∈ T) (hmem : c₀ ∈ R) (h1 : Nat.card ↥(X ⊓ Gx c₀ ⊓ R) = 2 ^ 7)
    (h2 : Nat.card ↥(X ⊓ Gx c₀ ⊓ R ⊓ D) = 2 ^ 6) (h3 : Nat.card ↥(X ⊓ Gx c₀ ⊓ D) = 2 ^ 6 * 3) :
    ∀ c ∈ T, c ∈ R ∧ Nat.card ↥(X ⊓ Gx c ⊓ R) = 2 ^ 7 ∧ Nat.card ↥(X ⊓ Gx c ⊓ R ⊓ D) = 2 ^ 6 ∧
      Nat.card ↥(X ⊓ Gx c ⊓ D) = 2 ^ 6 * 3 ∧
      QuotShape (X ⊓ Gx c ⊓ D) (X ⊓ Gx c ⊓ R ⊓ D) (Z 3) := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := hT.transitive c₀ hc₀ c hc
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  have hA : (X ⊓ Gx c₀ ⊓ R).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c₀ * k⁻¹) ⊓ R :=
    map_conj_stab_inf hk hR c₀
  have hB : (X ⊓ Gx c₀ ⊓ R ⊓ D).map (MulAut.conj k).toMonoidHom =
      X ⊓ Gx (k * c₀ * k⁻¹) ⊓ R ⊓ D := by
    rw [map_conj_inf_normalized hk hD, hA]
  have hC : (X ⊓ Gx c₀ ⊓ D).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c₀ * k⁻¹) ⊓ D :=
    map_conj_stab_inf hk hD c₀
  have h1' : Nat.card ↥(X ⊓ Gx (k * c₀ * k⁻¹) ⊓ R) = 2 ^ 7 := by
    rw [← hA, Subgroup.card_map_of_injective hinj, h1]
  have h2' : Nat.card ↥(X ⊓ Gx (k * c₀ * k⁻¹) ⊓ R ⊓ D) = 2 ^ 6 := by
    rw [← hB, Subgroup.card_map_of_injective hinj, h2]
  have h3' : Nat.card ↥(X ⊓ Gx (k * c₀ * k⁻¹) ⊓ D) = 2 ^ 6 * 3 := by
    rw [← hC, Subgroup.card_map_of_injective hinj, h3]
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨hR k hk c₀ hmem, h1', h2', h3', ?_⟩
  refine quotShape_prime (stab_le _) (fun m hm n hn => stab_norm hR hD _ hm hn) ?_
  rw [h3', h2']
  norm_num

theorem tableX_row1 [Finite G] {X R D : Subgroup G} (hR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R)
    (hD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) {T : Set G} (hT : IsConjOrbit X T) {c₁ : G}
    (hc₁ : c₁ ∈ T) (hmem : c₁ ∉ R) (h1 : IsElemTwo 5 (X ⊓ Gx c₁ ⊓ R))
    (h2 : IsElemTwo 4 (X ⊓ Gx c₁ ⊓ R ⊓ D)) (h3 : Nat.card ↥(X ⊓ Gx c₁ ⊓ D) = 2 ^ 5 * 3)
    {m₁ m₂ : G} (hm₁ : m₁ ∈ X ⊓ Gx c₁ ⊓ D) (hm₂ : m₂ ∈ X ⊓ Gx c₁ ⊓ D)
    (hcomm : m₁ * m₂ * m₁⁻¹ * m₂⁻¹ ∉ R) :
    ∀ c ∈ T, c ∉ R ∧ IsElemTwo 5 (X ⊓ Gx c ⊓ R) ∧ IsElemTwo 4 (X ⊓ Gx c ⊓ R ⊓ D) ∧
      Nat.card ↥(X ⊓ Gx c ⊓ D) = 2 ^ 5 * 3 ∧
      QuotShape (X ⊓ Gx c ⊓ D) (X ⊓ Gx c ⊓ R ⊓ D) (Sym 3) := by
  have hq : QuotShape (X ⊓ Gx c₁ ⊓ D) (X ⊓ Gx c₁ ⊓ R ⊓ D) (Sym 3) := by
    refine quotShape_sym3 (stab_le _) (fun m hm n hn => stab_norm hR hD _ hm hn) ?_ hm₁ hm₂
      (fun h => hcomm h.1.2)
    rw [h3, h2.2]
    norm_num
  intro c hc
  obtain ⟨k, hk, rfl⟩ := hT.transitive c₁ hc₁ c hc
  have hinj : Function.Injective (MulAut.conj k).toMonoidHom := (MulAut.conj k).injective
  have hA : (X ⊓ Gx c₁ ⊓ R).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c₁ * k⁻¹) ⊓ R :=
    map_conj_stab_inf hk hR c₁
  have hB : (X ⊓ Gx c₁ ⊓ R ⊓ D).map (MulAut.conj k).toMonoidHom =
      X ⊓ Gx (k * c₁ * k⁻¹) ⊓ R ⊓ D := by
    rw [map_conj_inf_normalized hk hD, hA]
  have hC : (X ⊓ Gx c₁ ⊓ D).map (MulAut.conj k).toMonoidHom = X ⊓ Gx (k * c₁ * k⁻¹) ⊓ D :=
    map_conj_stab_inf hk hD c₁
  refine ⟨fun hcR => hmem ?_, ?_, ?_, ?_, ?_⟩
  · have := hR k⁻¹ (X.inv_mem hk) _ hcR
    simpa [mul_assoc] using this
  · rw [← hA]
    exact isElemTwo_map_of_injective hinj h1
  · rw [← hB]
    exact isElemTwo_map_of_injective hinj h2
  · rw [← hC, Subgroup.card_map_of_injective hinj, h3]
  · rw [← hB, ← hC]
    exact QuotShape.map hinj hq

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
