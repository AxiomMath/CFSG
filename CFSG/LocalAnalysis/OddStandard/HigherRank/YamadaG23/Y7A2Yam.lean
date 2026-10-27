module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private lemma elemAbelian_comm {E : Subgroup G} (hE : IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  haveI := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)

private lemma mul_self_eq_one_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E) {a : G}
    (ha : a ∈ E) : a * a = 1 := by
  have h := hE.2 a ha
  rwa [pow_two] at h

private lemma mul_comm_of_sq_eq_one {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b * (a * b) = 1) : a * b = b * a := by
  have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right hab
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * b = (a * b)⁻¹ := hinv.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

private lemma card_setMul_mul_card_inf (A B : Subgroup G) :
    Nat.card ↥((A : Set G) * (B : Set G)) * Nat.card ↥(A ⊓ B) =
      Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have himg : Nat.card ↥((A : Set G).image ((↑) : G → G ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : G) : G ⧸ B) =
        (A : Set G).image ((↑) : G → G ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : G), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : G) : G ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : G) : G ⧸ B)) = ((a : G) : G ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        simpa using B.inv_mem h
      · intro h
        simpa using B.inv_mem h
    have := MulAction.index_stabilizer ↥A ((1 : G) : G ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

private lemma centEl_eq_of_mem {S A B : Subgroup G} (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hB : IsElemAbelian 2 B)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S, s * a = a * s ↔ s ∈ A) :
    ∀ b ∈ B, b ∉ A → ∀ s ∈ S, s * b = b * s ↔ s ∈ B := by
  intro b hbB hbA s hsS
  constructor
  · intro h
    obtain ⟨a, haA, b', hb'B, rfl⟩ := hSAB s hsS
    have hcomm : a * b = b * a := by
      have h1 : a * b' * b = b * (a * b') := h
      have hb'b : b' * b = b * b' := elemAbelian_comm hB hb'B hbB
      have h2 : (a * b) * b' = (b * a) * b' := by
        calc (a * b) * b' = a * (b * b') := by rw [mul_assoc]
          _ = a * (b' * b) := by rw [hb'b]
          _ = (a * b') * b := by rw [← mul_assoc]
          _ = b * (a * b') := h1
          _ = (b * a) * b' := by rw [mul_assoc]
      exact mul_right_cancel h2
    by_cases haB : a ∈ B
    · exact B.mul_mem haB hb'B
    · exact absurd ((hcent a haA haB b (hBS hbB)).mp hcomm.symm) hbA
  · intro hsB
    exact elemAbelian_comm hB hsB hbB

private lemma prod_rev {S A B : Subgroup G}
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    ∀ s ∈ S, ∃ b ∈ B, ∃ a ∈ A, s = b * a := by
  intro s hs
  obtain ⟨a, ha, b, hb, heq⟩ := hSAB s⁻¹ (S.inv_mem hs)
  exact ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, by rw [← inv_inv s, heq, mul_inv_rev]⟩

private lemma not_le_of_nonabelian {S P Q : Subgroup G} (hPS : P ≤ S) (hQS : Q ≤ S)
    (hS_PQ : ∀ s ∈ S, ∃ p ∈ P, ∃ q ∈ Q, s = p * q)
    (hQ : IsElemAbelian 2 Q) (hnab : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x) :
    ¬ P ≤ Q := by
  intro hPQ
  obtain ⟨x, hxS, y, hyS, hxy⟩ := hnab
  have hSle : S ≤ Q := by
    intro s hs
    obtain ⟨p, hp, q, hq, rfl⟩ := hS_PQ s hs
    exact Q.mul_mem (hPQ hp) hq
  exact hxy (elemAbelian_comm hQ (hSle hxS) (hSle hyS))

private lemma inf_le_cen {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B) : A ⊓ B ≤ cen S := by
  intro g hg
  obtain ⟨hgA, hgB⟩ := Subgroup.mem_inf.mp hg
  refine Subgroup.mem_inf.mpr ⟨hAS hgA, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  obtain ⟨a, haA, b, hbB, rfl⟩ := hSAB s hs
  have hga : g * a = a * g := elemAbelian_comm hA hgA haA
  have hgb : g * b = b * g := elemAbelian_comm hB hgB hbB
  calc (a * b) * g = a * (b * g) := by rw [mul_assoc]
    _ = a * (g * b) := by rw [hgb]
    _ = (a * g) * b := by rw [← mul_assoc]
    _ = (g * a) * b := by rw [hga]
    _ = g * (a * b) := by rw [mul_assoc]

private lemma cen_eq {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hAle : ¬ A ≤ B) (hBle : ¬ B ≤ A)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S, s * a = a * s ↔ s ∈ A)
    (hcentB : ∀ b ∈ B, b ∉ A → ∀ s ∈ S, s * b = b * s ↔ s ∈ B) :
    cen S = A ⊓ B := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgS, hgcent⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨a, haA, haB⟩ := Set.not_subset.mp hAle
    obtain ⟨b, hbB, hbA⟩ := Set.not_subset.mp hBle
    have hgA : g ∈ A :=
      (hcent a haA haB g hgS).mp (Subgroup.mem_centralizer_iff.mp hgcent a (hAS haA)).symm
    have hgB : g ∈ B :=
      (hcentB b hbB hbA g hgS).mp (Subgroup.mem_centralizer_iff.mp hgcent b (hBS hbB)).symm
    exact Subgroup.mem_inf.mpr ⟨hgA, hgB⟩
  · exact inf_le_cen hAS hBS hSAB hA hB

private lemma le_or_le_of_elemAbelian {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S, s * a = a * s ↔ s ∈ A)
    {E : Subgroup G} (hES : E ≤ S) (hE : IsElemAbelian 2 E) : E ≤ A ∨ E ≤ B := by
  have hcover : ∀ e ∈ E, e ∈ A ∨ e ∈ B := by
    intro e heE
    have heS : e ∈ S := hES heE
    obtain ⟨a, haA, b, hbB, rfl⟩ := hSAB e heS
    have he2 : (a * b) * (a * b) = 1 := mul_self_eq_one_of_mem hE heE
    have ha2 : a * a = 1 := mul_self_eq_one_of_mem hA haA
    have hb2 : b * b = 1 := mul_self_eq_one_of_mem hB hbB
    have hcomm : a * b = b * a := mul_comm_of_sq_eq_one ha2 hb2 he2
    by_cases haB : a ∈ B
    · exact Or.inr (B.mul_mem haB hbB)
    · exact Or.inl (A.mul_mem haA ((hcent a haA haB b (hBS hbB)).mp hcomm.symm))
  by_contra h
  have hAnle : ¬ E ≤ A := fun hle => h (Or.inl hle)
  have hBnle : ¬ E ≤ B := fun hle => h (Or.inr hle)
  obtain ⟨x, hxE, hxA⟩ := Set.not_subset.mp hAnle
  obtain ⟨y, hyE, hyB⟩ := Set.not_subset.mp hBnle
  have hxB : x ∈ B := (hcover x hxE).resolve_left hxA
  have hyA : y ∈ A := (hcover y hyE).resolve_right hyB
  rcases hcover (x * y) (E.mul_mem hxE hyE) with hxyA | hxyB
  · refine hxA ?_
    have hx : x = x * y * y⁻¹ := by group
    rw [hx]
    exact A.mul_mem hxyA (A.inv_mem hyA)
  · refine hyB ?_
    have hy : y = x⁻¹ * (x * y) := by group
    rw [hy]
    exact B.mul_mem (B.inv_mem hxB) hxyB

private lemma maxElemAbelian_eq {S A B : Subgroup G} (hAS : A ≤ S) (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b)
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hAle : ¬ A ≤ B) (hBle : ¬ B ≤ A)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S, s * a = a * s ↔ s ∈ A) :
    maxElemAbelian S = {A, B} := by
  ext Y
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hY
    obtain ⟨hYS, hYel, hYmax⟩ := hY
    rcases le_or_le_of_elemAbelian hAS hBS hSAB hA hB hcent hYS hYel with hYA | hYB
    · exact Or.inl (hYmax A hYA hAS hA).symm
    · exact Or.inr (hYmax B hYB hBS hB).symm
  · intro hY
    rcases hY with rfl | rfl
    · refine ⟨hAS, hA, ?_⟩
      intro Y' hAY' hY'S hY'el
      rcases le_or_le_of_elemAbelian hAS hBS hSAB hA hB hcent hY'S hY'el with hY'A | hY'B
      · exact le_antisymm hY'A hAY'
      · exact absurd (hAY'.trans hY'B) hAle
    · refine ⟨hBS, hB, ?_⟩
      intro Y' hBY' hY'S hY'el
      rcases le_or_le_of_elemAbelian hAS hBS hSAB hA hB hcent hY'S hY'el with hY'A | hY'B
      · exact absurd (hBY'.trans hY'A) hBle
      · exact le_antisymm hY'B hBY'

private lemma centEl_card_le_of {S P Q : Subgroup G} (hPS : P ≤ S) (hQS : Q ≤ S)
    (hS_PQ : (S : Set G) = (P : Set G) * (Q : Set G))
    (hcentP : ∀ p ∈ P, p ∉ Q → ∀ s ∈ S, s * p = p * s ↔ s ∈ P)
    (hP : IsElemAbelian 2 P) (hQ : IsElemAbelian 2 Q)
    {x : G} (hxS : x ∈ S) (hxP : x ∉ P) (hxQ : x ∉ Q) :
    Nat.card ↥(centEl S x) ≤ Nat.card ↥Q := by
  let C : Subgroup G := centEl S x
  have hCS : C ≤ S := inf_le_left
  have hPC : P ⊓ C = P ⊓ Q := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨-, hgcent⟩ := Subgroup.mem_inf.mp hgC
      by_cases hgQ : g ∈ Q
      · exact Subgroup.mem_inf.mpr ⟨hgP, hgQ⟩
      · exfalso
        have hcomm : x * g = g * x :=
          (Subgroup.mem_centralizer_singleton_iff.mp hgcent).symm
        exact hxP ((hcentP g hgP hgQ x hxS).mp hcomm)
    · intro g hg
      obtain ⟨hgP, hgQ⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_inf.mpr ⟨hgP, ?_⟩
      refine Subgroup.mem_inf.mpr ⟨hPS hgP, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxPQ : x ∈ (P : Set G) * (Q : Set G) := by
        rw [← hS_PQ]
        exact hxS
      obtain ⟨p, hpP, q, hqQ, hxeq⟩ := Set.mem_mul.mp hxPQ
      rw [← hxeq]
      have hgp : g * p = p * g := elemAbelian_comm hP hgP hpP
      have hgq : g * q = q * g := elemAbelian_comm hQ hgQ hqQ
      calc g * (p * q) = (g * p) * q := by rw [mul_assoc]
        _ = (p * g) * q := by rw [hgp]
        _ = p * (g * q) := by rw [← mul_assoc]
        _ = p * (q * g) := by rw [hgq]
        _ = (p * q) * g := by rw [mul_assoc]
  have hprodC := card_setMul_mul_card_inf P C
  have hprodQ := card_setMul_mul_card_inf P Q
  have hsub : (P : Set G) * (C : Set G) ⊆ (S : Set G) := by
    rintro z ⟨p, hp, c, hc, rfl⟩
    exact S.mul_mem (hPS hp) (hCS hc)
  have hcardle : Nat.card ↥((P : Set G) * (C : Set G)) ≤ Nat.card ↥S := by
    refine Nat.card_le_card_of_injective
      (fun z : ↥((P : Set G) * (C : Set G)) => (⟨z.1, hsub z.2⟩ : ↥S)) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : ↥S => (z : G)) hab)
  have hSQ : Nat.card ↥((P : Set G) * (Q : Set G)) = Nat.card ↥S :=
    congrArg (fun t : Set G => Nat.card t) hS_PQ.symm
  have h1 : Nat.card ↥P * Nat.card ↥C =
      Nat.card ↥((P : Set G) * (C : Set G)) * Nat.card ↥(P ⊓ Q) := by
    have h := hprodC
    rw [hPC] at h
    exact h.symm
  have h2 : Nat.card ↥((P : Set G) * (C : Set G)) * Nat.card ↥(P ⊓ Q) ≤
      Nat.card ↥S * Nat.card ↥(P ⊓ Q) := Nat.mul_le_mul_right _ hcardle
  have h3 : Nat.card ↥S * Nat.card ↥(P ⊓ Q) = Nat.card ↥P * Nat.card ↥Q := by
    rw [← hSQ]
    exact hprodQ
  exact Nat.le_of_mul_le_mul_left (h1.le.trans (h2.trans_eq h3)) Nat.card_pos

theorem y7a_yam79_21 {S A B : Subgroup G} (hS : IsPGroup 2 S) (hAS : A ≤ S) (hBS : B ≤ S)
    (hSAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hnab : ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x)
    (hcent : ∀ a ∈ A, a ∉ B → ∀ s ∈ S, s * a = a * s ↔ s ∈ A) :
    (∀ b ∈ B, b ∉ A → ∀ s ∈ S, s * b = b * s ↔ s ∈ B) ∧
      maxElemAbelian S = {A, B} ∧ cen S = A ⊓ B ∧
      ∀ x ∈ S, x ∉ A → x ∉ B → Nat.card ↥(centEl S x) ≤ min (Nat.card ↥A) (Nat.card ↥B) := by
  have hSAB_rev := prod_rev hSAB
  have hcentB := centEl_eq_of_mem hBS hSAB hB hcent
  have hAle : ¬ A ≤ B := not_le_of_nonabelian hAS hBS hSAB hB hnab
  have hBle : ¬ B ≤ A := not_le_of_nonabelian hBS hAS hSAB_rev hA hnab
  refine ⟨hcentB, maxElemAbelian_eq hAS hBS hSAB hA hB hAle hBle hcent,
    cen_eq hAS hBS hSAB hA hB hAle hBle hcent hcentB, ?_⟩
  have hsetAB : (S : Set G) = (A : Set G) * (B : Set G) := by
    apply Set.Subset.antisymm
    · intro s hs
      obtain ⟨a, ha, b, hb, rfl⟩ := hSAB s hs
      exact Set.mem_mul.mpr ⟨a, ha, b, hb, rfl⟩
    · rintro z ⟨a, ha, b, hb, rfl⟩
      exact S.mul_mem (hAS ha) (hBS hb)
  have hsetBA : (S : Set G) = (B : Set G) * (A : Set G) := by
    apply Set.Subset.antisymm
    · intro s hs
      obtain ⟨b, hb, a, ha, rfl⟩ := hSAB_rev s hs
      exact Set.mem_mul.mpr ⟨b, hb, a, ha, rfl⟩
    · rintro z ⟨b, hb, a, ha, rfl⟩
      exact S.mul_mem (hBS hb) (hAS ha)
  intro x hxS hxA hxB
  refine le_min ?_ ?_
  · exact centEl_card_le_of hBS hAS hsetBA hcentB hB hA hxS hxB hxA
  · exact centEl_card_le_of hAS hBS hsetAB hcent hA hB hxS hxA hxB

end CFSG.OddStandard.HigherRank.YamadaG23
