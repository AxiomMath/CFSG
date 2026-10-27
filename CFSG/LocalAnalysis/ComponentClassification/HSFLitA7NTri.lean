module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7NQ0

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

theorem ElemAbelianTwo.sup' {G : Type*} [Group G] {A B : Subgroup G} (hA : ElemAbelianTwo A)
    (hB : ElemAbelianTwo B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : ElemAbelianTwo (A ⊔ B) := by
  have hs : ∀ a ∈ (A : Set G) ∪ B, ∀ b ∈ (A : Set G) ∪ B, a * b = b * a := by
    rintro a (ha | ha) b (hb | hb)
    · exact hA.comm a ha b hb
    · exact hAB a ha b hb
    · exact (hAB b hb a ha).symm
    · exact hB.comm a ha b hb
  have hcl : A ⊔ B = closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcomm : ∀ a ∈ A ⊔ B, ∀ b ∈ A ⊔ B, a * b = b * a := by
    intro a ha b hb
    rw [hcl] at ha hb
    exact comm_of_mem_closure hs ha hb
  refine ⟨hcomm, fun a ha => ?_⟩
  have ha' := ha
  rw [hcl] at ha'
  induction ha' using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hA.sq_eq_one x hx
    · exact hB.sq_eq_one x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [← hcl] at hx hy
    rw [(Commute.mul_pow (hcomm x hx y hy) 2), ihx hx, ihy hy, one_mul]
  | inv x hx ihx =>
    rw [← hcl] at hx
    rw [inv_pow, ihx hx, inv_one]

theorem elem_closure {G : Type*} [Group G] {s : Set G} (hc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a)
    (h2 : ∀ a ∈ s, a ^ 2 = 1) : ElemAbelianTwo (closure s) := by
  refine ⟨fun a ha b hb => comm_of_mem_closure hc ha hb, fun a ha => ?_⟩
  have ha' := ha
  induction ha' using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (comm_of_mem_closure hc hx hy) 2), ihx hx, ihy hy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx hx, inv_one]

theorem t_part : ∀ p q : V4, q.2.2.1 = 1 → (addV (addV (0, 0, 1, 0) q) p).2.2.1 = 1 →
    p.2.2.1 = 1 := by decide

namespace A7Base

variable {X : Type} [Group X] [Finite X] (S : A7Base X)

theorem le_E_of_elem {F : Subgroup X} (hFT : F ≤ S.data.T) (hF : ElemAbelianTwo F)
    (hBF : S.B ≤ F) : F ≤ S.E S.y ∨ F ≤ S.E (S.x * S.y) := by
  by_cases h : F ≤ S.B
  · left
    exact h.trans (by rw [S.E_eq_B_sup]; exact le_sup_left)
  · obtain ⟨f, hfF, hfB⟩ := Set.not_subset.mp h
    obtain ⟨hel, -, hcard⟩ := S.elem_B.sup_zpowers (hF.sq_eq_one f hfF) hfB
      (fun a ha => hF.comm f hfF a (hBF ha))
    rw [S.card_B] at hcard
    have hle : S.B ⊔ zpowers f ≤ F := sup_le hBF (zpowers_le.mpr hfF)
    rcases S.eq_E_of_elem (hle.trans hFT) hel hcard with h16 | h16
    · left
      intro g hg
      apply S.mem_E_of_commute (Or.inl rfl) (hFT hg)
      intro e he
      rw [← h16] at he
      exact hF.comm g hg e (hle he)
    · right
      intro g hg
      apply S.mem_E_of_commute (Or.inr rfl) (hFT hg)
      intro e he
      rw [← h16] at he
      exact hF.comm g hg e (hle he)

variable {S}

theorem conjTo_of_triple (hO : S.Fus) {a b ζ : X} (hab : a * b = b * a) (haζ : a * ζ = ζ * a)
    (hbζ : b * ζ = ζ * b) (hb2 : b ^ 2 = 1) (hζ2 : ζ ^ 2 = 1)
    (ha : ConjTo S.t a) (hb : ConjTo S.t b) (habζ : ConjTo S.t (a * b * ζ)) :
    ConjTo S.t ζ := by
  obtain ⟨g, hg⟩ := ha
  have hinv : ∀ x : X, ConjTo S.t (g⁻¹ * x * g) ↔ ConjTo S.t x := fun x => by
    have := conjTo_conj_iff S.t x g⁻¹
    rwa [inv_inv] at this
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, b₁ = g⁻¹ * b * g := ⟨_, rfl⟩
  obtain ⟨ζ₁, hζ₁⟩ : ∃ ζ₁, ζ₁ = g⁻¹ * ζ * g := ⟨_, rfl⟩
  have ht : g⁻¹ * a * g = S.t := by rw [← hg]; group
  have hconj : ∀ x y : X, x * y = y * x →
      (g⁻¹ * x * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * x * g) := by
    intro x y h
    calc (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [h]
      _ = (g⁻¹ * y * g) * (g⁻¹ * x * g) := by group
  have htb : S.t * b₁ = b₁ * S.t := by rw [← ht, hb₁]; exact hconj a b hab
  have htζ : S.t * ζ₁ = ζ₁ * S.t := by rw [← ht, hζ₁]; exact hconj a ζ haζ
  have hbζ₁ : b₁ * ζ₁ = ζ₁ * b₁ := by rw [hb₁, hζ₁]; exact hconj b ζ hbζ
  have hsq : ∀ x : X, x ^ 2 = 1 → (g⁻¹ * x * g) ^ 2 = 1 := fun x h => by
    rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by rw [inv_inv], conj_pow, h]; group
  have hPel : ElemAbelianTwo (closure {S.t, b₁, ζ₁}) := by
    refine elem_closure (fun x hx y hy => ?_) (fun x hx => ?_)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first | rfl | assumption | exact htb.symm | exact htζ.symm | exact hbζ₁.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact S.t_sq
      · rw [hb₁]; exact hsq b hb2
      · rw [hζ₁]; exact hsq ζ hζ2
  have htP : S.t ∈ closure {S.t, b₁, ζ₁} := subset_closure (by simp)
  have hPC : closure {S.t, b₁, ζ₁} ≤ centralizer ({S.t} : Set X) := fun x hx => by
    rw [mem_centralizer_singleton_iff]; exact hPel.comm x hx S.t htP
  have hPp : IsPGroup 2 (closure {S.t, b₁, ζ₁}) := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (hPel.sq_eq_one x x.2)⟩
  obtain ⟨h, hh, hPT⟩ := S.data.exists_conj_le_T hPp hPC
  have hP'el : ElemAbelianTwo ((closure {S.t, b₁, ζ₁}).map (MulAut.conj h).toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hPel.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hPel.sq_eq_one x hx, map_one]
  have hF := hP'el.sup' S.elem_B (fun x hx y hy => (S.central_of_mem_B hy (hPT hx)).symm)
  have hFT := sup_le hPT S.B_le_T
  have hmem : ∀ {x : X}, x ∈ closure {S.t, b₁, ζ₁} →
      h * x * h⁻¹ ∈ (closure {S.t, b₁, ζ₁}).map (MulAut.conj h).toMonoidHom ⊔ S.B :=
    fun hx => mem_sup_left ⟨_, hx, rfl⟩
  have hht : h * S.t * h⁻¹ = S.t := by rw [mem_centralizer_singleton_iff.mp hh]; group
  have hb₂ : ConjTo S.t (h * b₁ * h⁻¹) := by rw [conjTo_conj_iff, hb₁, hinv]; exact hb
  have habζ₂ : ConjTo S.t (S.t * (h * b₁ * h⁻¹) * (h * ζ₁ * h⁻¹)) := by
    have e : S.t * (h * b₁ * h⁻¹) * (h * ζ₁ * h⁻¹) = (h * g⁻¹) * (a * b * ζ) * (h * g⁻¹)⁻¹ := by
      calc S.t * (h * b₁ * h⁻¹) * (h * ζ₁ * h⁻¹) =
          (h * S.t * h⁻¹) * (h * b₁ * h⁻¹) * (h * ζ₁ * h⁻¹) := by rw [hht]
        _ = (h * (g⁻¹ * a * g) * h⁻¹) * (h * (g⁻¹ * b * g) * h⁻¹) * (h * (g⁻¹ * ζ * g) * h⁻¹) := by
            rw [ht, hb₁, hζ₁]
        _ = (h * g⁻¹) * (a * b * ζ) * (h * g⁻¹)⁻¹ := by group
    rw [e, conjTo_conj_iff]; exact habζ
  suffices hζ₂ : ConjTo S.t (h * ζ₁ * h⁻¹) by
    rw [conjTo_conj_iff, hζ₁, hinv] at hζ₂; exact hζ₂
  have hbP : b₁ ∈ closure {S.t, b₁, ζ₁} := subset_closure (by simp)
  have hζP : ζ₁ ∈ closure {S.t, b₁, ζ₁} := subset_closure (by simp)
  have key : ∀ I : S.Inst, (closure {S.t, b₁, ζ₁}).map (MulAut.conj h).toMonoidHom ⊔ S.B ≤ I.E →
      ConjTo S.t (h * ζ₁ * h⁻¹) := by
    intro I hE
    obtain ⟨pb, hpb⟩ := I.eq_wV (hE (hmem hbP))
    obtain ⟨pζ, hpζ⟩ := I.eq_wV (hE (hmem hζP))
    have htw : S.t * (h * b₁ * h⁻¹) * (h * ζ₁ * h⁻¹) =
        I.wV (addV (addV (0, 0, 1, 0) pb) pζ) := by
      rw [hpb, hpζ, I.wV_add, I.wV_add, show I.wV (0, 0, 1, 0) = S.t by simp [Inst.wV]]
    rw [hpb, I.conjTo_wV_iff hO] at hb₂
    rw [htw, I.conjTo_wV_iff hO] at habζ₂
    rw [hpζ, I.conjTo_wV_iff hO]
    exact t_part pζ pb hb₂ habζ₂
  rcases S.le_E_of_elem hFT hF le_sup_right with hE | hE
  · exact key S.inst₂ hE
  · exact key S.inst₁ hE

theorem not_conjTo_of_comm {A : Subgroup X} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card A = 64) {q : X} (hq : q ∈ A) : ¬ ConjTo S.t q := by
  rintro ⟨g, hg⟩
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom with hA'
  have htA : S.t ∈ A' := ⟨q, hq, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; rw [← hg]; group⟩
  have hA'C : A' ≤ centralizer ({S.t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨q', hq', hq'e⟩ := htA
    rw [mem_centralizer_singleton_iff, ← hq'e]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hA a ha q' hq']
  have hcard' : Nat.card A' = 64 := by
    rw [hA', card_map_of_injective (MulAut.conj _).injective, hcard]
  have hp : IsPGroup 2 A' := IsPGroup.of_card (n := 6) (by rw [hcard']; norm_num)
  obtain ⟨h, -, hT⟩ := S.data.exists_conj_le_T hp hA'C
  have := Subgroup.card_le_of_le hT
  rw [card_map_of_injective (MulAut.conj h).injective, hcard', S.card_T] at this
  omega

end A7Base

end CFSG.ComponentClassification.HSFLit
