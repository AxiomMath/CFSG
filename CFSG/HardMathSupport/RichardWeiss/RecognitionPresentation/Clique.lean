module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StarLemma

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

section Algebra

variable {J : Type*} [Group J]

theorem mem_closure_of_pow_five {p q : J} (hq : q ^ 3 = 1) (h5 : (p * q) ^ 5 = 1) :
    q ∈ Subgroup.closure ({p, q⁻¹ * p * q, q * p * q⁻¹} : Set J) := by
  set H := Subgroup.closure ({p, q⁻¹ * p * q, q * p * q⁻¹} : Set J) with hH
  have hp : p ∈ H := Subgroup.subset_closure (by simp)
  have ha : q⁻¹ * p * q ∈ H := Subgroup.subset_closure (by simp)
  have hb : q * p * q⁻¹ ∈ H := Subgroup.subset_closure (by simp)
  have e1 : q * q = q⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    calc q * q * q = q * (q * q) := mul_assoc _ _ _
      _ = q ^ 3 := (pow_three q).symm
      _ = 1 := hq
  have e2 : q⁻¹ * q⁻¹ = q := by
    rw [← mul_inv_rev, e1, inv_inv]
  have conj_sq : ∀ x : J, q * (q * x * q⁻¹) * q⁻¹ = q⁻¹ * x * q := by
    intro x
    calc q * (q * x * q⁻¹) * q⁻¹ = (q * q) * x * (q⁻¹ * q⁻¹) := by group
      _ = q⁻¹ * x * q := by rw [e1, e2]
  have hnorm : ∀ h ∈ H, q * h * q⁻¹ ∈ H := by
    intro h hh
    have : H.map (MulAut.conj q).toMonoidHom ≤ H := by
      rw [hH, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hb
      · have : (MulAut.conj q).toMonoidHom (q⁻¹ * p * q) = p := by
          simp [MulAut.conj_apply]; group
        rw [this]; exact hp
      · have : (MulAut.conj q).toMonoidHom (q * p * q⁻¹) = q⁻¹ * p * q := by
          simp [MulAut.conj_apply]; exact conj_sq p
        rw [this]; exact ha
    exact this ⟨h, hh, by simp [MulAut.conj_apply]⟩
  have ht1 : q * p * q⁻¹ ∈ H := hb
  have ht2 : q * (q * p * q⁻¹) * q⁻¹ ∈ H := hnorm _ ht1
  have ht3 : q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹ ∈ H := hnorm _ ht2
  have ht4 : q * (q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹) * q⁻¹ ∈ H := hnorm _ ht3
  have key : (p * q) ^ 5 = p * (q * p * q⁻¹) * (q * (q * p * q⁻¹) * q⁻¹) *
      (q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹) * (q * (q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹) * q⁻¹) *
      q ^ 5 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hprod : p * (q * p * q⁻¹) * (q * (q * p * q⁻¹) * q⁻¹) *
      (q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹) * (q * (q * (q * (q * p * q⁻¹) * q⁻¹) * q⁻¹) * q⁻¹)
      ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem hp ht1) ht2) ht3) ht4
  have hq5 : q ^ 5 ∈ H := by
    have h' := key
    rw [h5] at h'
    rw [eq_inv_of_mul_eq_one_right h'.symm]
    exact H.inv_mem hprod
  have hq10 : q = q ^ 5 * q ^ 5 := by
    rw [← pow_add]
    have : q ^ (5 + 5) = (q ^ 3) ^ 3 * q := by rw [← pow_mul, ← pow_succ]
    rw [this, hq]; simp
  rw [hq10]
  exact H.mul_mem hq5 hq5

theorem sq_comm_eq_one {p q : J} (h : (p * q) ^ 2 = 1) : (q * p) ^ 2 = 1 := by
  have : (q * p) ^ 2 = q * (p * q) ^ 2 * q⁻¹ := by
    simp only [pow_two]; group
  rw [this, h]; group

end Algebra

variable {J : Type*} [Group J] [DecidableEq J] {D : J → Prop}

structure IsClique (D : J → Prop) (F : Finset J) : Prop where
  mem : ∀ p ∈ F, D p
  adj : ∀ p ∈ F, ∀ q ∈ F, p ≠ q → (p * q) ^ 2 = 1

structure IsMaxClique (D : J → Prop) (F : Finset J) : Prop extends IsClique D F where
  max : ∀ F' : Finset J, IsClique D F' → F'.card ≤ F.card

theorem IsClique.image_conj (hD : OrderThreeClass D) {F : Finset J} (hF : IsClique D F)
    (g : J) : IsClique D (F.image fun z => g⁻¹ * z * g) := by
  constructor
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    exact hD.conj g z (hF.mem z hz)
  · intro p hp q hq hpq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hq
    have hzw : z ≠ w := fun h => hpq (by rw [h])
    have := hF.adj z hz w hw hzw
    calc (g⁻¹ * z * g * (g⁻¹ * w * g)) ^ 2 = g⁻¹ * (z * w) ^ 2 * g := by
          simp only [pow_two]; group
      _ = 1 := by rw [this]; group

theorem IsMaxClique.image_conj (hD : OrderThreeClass D) {F : Finset J} (hF : IsMaxClique D F)
    (g : J) : IsMaxClique D (F.image fun z => g⁻¹ * z * g) := by
  refine ⟨hF.toIsClique.image_conj hD g, fun F' hF' => ?_⟩
  rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  exact hF.max F' hF'

theorem IsMaxClique.mem_closure_of_related_two
    (hD : OrderThreeClass D) {F : Finset J}
    (hF : IsMaxClique D F) {p q y : J} (hp : p ∈ F) (hq : q ∈ F) (hpq : p ≠ q) (hy : D y)
    (hpy : (p * y) ^ 2 = 1) (hqy : (q * y) ^ 2 = 1) :
    y ∈ Subgroup.closure (F : Set J) := by
  by_contra hyF
  have hyF' : y ∉ F := fun h => hyF (Subgroup.subset_closure h)
  have hcl : IsClique D (insert y F) := by
    have hpq' : (p * q) ^ 2 = 1 := hF.adj p hp q hq hpq
    have rel : ∀ s ∈ F, (s * y) ^ 2 = 1 := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]; exact hpy
      by_cases hsq : s = q
      · rw [hsq]; exact hqy
      have hps : (p * s) ^ 2 = 1 := hF.adj p hp s hs (Ne.symm hsp)
      have hqs : (q * s) ^ 2 = 1 := hF.adj q hq s hs (Ne.symm hsq)
      rcases hD.star_lemma (hF.mem p hp) (hF.mem q hq) (hF.mem s hs) hy hpq' hps hqs hpy hqy
        with h | h
      · exfalso
        apply hyF
        have hsub : ({p, q, s} : Set J) ⊆ (F : Set J) := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl <;> assumption
        exact Subgroup.closure_mono hsub h
      · exact h
    constructor
    · intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact hy
      · exact hF.mem z hz
    · intro a ha b hb hab
      rcases Finset.mem_insert.1 ha with rfl | ha'
      · rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact absurd rfl hab
        · exact sq_comm_eq_one (rel b hb')
      · rcases Finset.mem_insert.1 hb with rfl | hb'
        · exact rel a ha'
        · exact hF.adj a ha' b hb' hab
  have := hF.max _ hcl
  rw [Finset.card_insert_of_notMem hyF'] at this
  omega

theorem IsMaxClique.mem_closure_of_related_two_conj
    (hD : OrderThreeClass D) {F : Finset J}
    (hF : IsMaxClique D F) {g p q y : J} (hg : g ∈ Subgroup.closure (F : Set J)) (hp : p ∈ F)
    (hq : q ∈ F) (hpq : p ≠ q) (hy : D y) (hpy : (g⁻¹ * p * g * y) ^ 2 = 1)
    (hqy : (g⁻¹ * q * g * y) ^ 2 = 1) : y ∈ Subgroup.closure (F : Set J) := by
  have hFg := hF.image_conj hD g
  have key := hFg.mem_closure_of_related_two hD (Finset.mem_image_of_mem _ hp)
    (Finset.mem_image_of_mem _ hq) (fun h => hpq (by simpa using h)) hy hpy hqy
  refine (Subgroup.closure_le _).2 ?_ key
  intro z hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (by simpa using hz)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg)
    (Subgroup.subset_closure hw)) hg

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
