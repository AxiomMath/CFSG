module

public import CFSG.CGT.PushingUpLit.BHS.FourOneC

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne
open FourOneTools

namespace FourOneTools

section NormClosure

variable {Γ : Type*} [Group Γ]

@[expose] def normClosure (L X : Subgroup Γ) : Subgroup Γ :=
  sSup {Z | ∃ g ∈ L, Z = conjSub g X}

variable {L X : Subgroup Γ}

theorem le_normClosure : X ≤ normClosure L X :=
  le_sSup ⟨1, L.one_mem, (conjSub_one X).symm⟩

theorem normClosure_le (hXL : X ≤ L) : normClosure L X ≤ L := by
  refine sSup_le ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Glauberman.map_conj_le hg hXL

theorem conj_mem_normClosure {g : Γ} (hg : g ∈ L) {z : Γ} (hz : z ∈ normClosure L X) :
    g * z * g⁻¹ ∈ normClosure L X := by
  have hle : normClosure L X ≤ (normClosure L X).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le ?_
    rintro _ ⟨g', hg', rfl⟩ _ ⟨x, hx, rfl⟩
    have hmem : conjSub (g * g') X ∈ {Z | ∃ g ∈ L, Z = conjSub g X} :=
      ⟨g * g', L.mul_mem hg hg', rfl⟩
    have h1 : g * g' * x * (g * g')⁻¹ ∈ normClosure L X :=
      le_sSup hmem (mem_conjSub_of_mem hx)
    have e : g * (g' * x * g'⁻¹) * g⁻¹ = g * g' * x * (g * g')⁻¹ := by group
    show g * (g' * x * g'⁻¹) * g⁻¹ ∈ normClosure L X
    rw [e]
    exact h1
  exact hle hz

theorem le_normalizer_normClosure : L ≤ Subgroup.normalizer (normClosure L X : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => conj_mem_normClosure hg hz, fun hz => ?_⟩
  have := conj_mem_normClosure (L.inv_mem hg) hz
  simpa [mul_assoc] using this

end NormClosure

section NormClosureModule

variable {V : Type} [CommGroup V] {L X : Subgroup (MulAut V)}

theorem commV_normClosure_le (hX : commV X ≤ fixV L) : commV (normClosure L X) ≤ fixV L := by
  rw [B19.commV_le_iff]
  refine sSup_le ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [← B19.commV_le_iff]
  show commV (X.map (MulAut.conj g).toMonoidHom) ≤ fixV L
  rw [B19.commV_map_conj]
  rintro _ ⟨w, hw, rfl⟩
  have hw' : w ∈ fixV L := hX hw
  have hgw : g w = w := hw' g hg
  show g w ∈ fixV L
  rw [hgw]
  exact hw'

theorem isPGroup_normClosure (hXL : X ≤ L) (hsq : ∀ x ∈ X, x ^ 2 = 1)
    (hX : commV X ≤ fixV L) : IsPGroup 2 (normClosure L X) := by
  have hquad : IsQuadratic (normClosure L X) :=
    (commV_normClosure_le hX).trans (fixV_anti (normClosure_le hXL))
  have hcomm := comm_of_isQuadratic hquad
  refine Glauberman.isPGroup_two_of_sq_eq_one ?_
  refine sq_eq_one_of_mem_sSup (F := {Z | ∃ g ∈ L, Z = conjSub g X}) hcomm ?_
  rintro _ ⟨g, hg, rfl⟩ z hz
  have h1 := hsq _ (mem_conjSub_iff.1 hz)
  have : z ^ 2 = g * (g⁻¹ * z * g) ^ 2 * g⁻¹ := by
    simp only [pow_two]
    group
  rw [this, h1]
  group

end NormClosureModule

end FourOneTools

namespace Hyp41

variable {V : Type} [CommGroup V] [Finite V] {P : Subgroup (MulAut V)}
  {D : Set (Subgroup (MulAut V))}

theorem four_eight_fixV_sup (h : Hyp41 P D) {X Y E : Subgroup (MulAut V)} (hX : X ∈ D)
    (hY : Y ∈ D) (hE : E ∈ D) (hEX : E ≠ X) (hcomm : ∀ e ∈ E, ∀ x ∈ X, e * x = x * e)
    (hcard : Nat.card E = Nat.card Y) (hEL : E ≤ X ⊔ Y) : fixV (X ⊔ Y) = fixV (X ⊔ E) := by
  have hXE := h.card_prod X hX E hE hEX fun x hx e he => (hcomm e he x hx).symm
  have hprod := card_sup_mul_card_inf' (X := fixV X) (Y := fixV Y) fun x _ y _ => mul_comm x y
  have hsup : Nat.card ↥(fixV X ⊔ fixV Y) ≤ Nat.card V :=
    (Subgroup.card_le_of_le (le_top : fixV X ⊔ fixV Y ≤ ⊤)).trans_eq Subgroup.card_top
  have hXeq := h.card_eq X hX
  have hYeq := h.card_eq Y hY
  have hpos : 0 < Nat.card V := Nat.card_pos
  have hV : Nat.card V ≤ Nat.card X * Nat.card Y * Nat.card ↥(fixV X ⊓ fixV Y) := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc Nat.card V * Nat.card V
        = Nat.card X * Nat.card (fixV X) * (Nat.card Y * Nat.card (fixV Y)) := by
          rw [← hXeq, ← hYeq]
      _ = Nat.card X * Nat.card Y *
          (Nat.card ↥(fixV X ⊔ fixV Y) * Nat.card ↥(fixV X ⊓ fixV Y)) := by
          rw [hprod]; ring
      _ ≤ Nat.card X * Nat.card Y * (Nat.card V * Nat.card ↥(fixV X ⊓ fixV Y)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hsup)
      _ = Nat.card V * (Nat.card X * Nat.card Y * Nat.card ↥(fixV X ⊓ fixV Y)) := by ring
  have hle : fixV (X ⊔ Y) ≤ fixV (X ⊔ E) := fixV_anti (sup_le le_sup_left hEL)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hXY : 0 < Nat.card X * Nat.card Y := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.le_of_mul_le_mul_left ?_ hXY
  rw [fixV_sup X Y]
  calc Nat.card X * Nat.card Y * Nat.card ↥(fixV (X ⊔ E)) = Nat.card V := by
        rw [hXE, hcard]
    _ ≤ _ := hV

theorem four_eight_commute (h : Hyp41 P D) {X Y E : Subgroup (MulAut V)} (hX : X ∈ D)
    (hY : Y ∈ D) (hE : E ∈ D) (hEX : E ≠ X) (hcomm : ∀ e ∈ E, ∀ x ∈ X, e * x = x * e)
    (hcard : Nat.card E = Nat.card Y) (hEL : E ≤ X ⊔ Y) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := by
  have hfix := h.four_eight_fixV_sup hX hY hE hEX hcomm hcard hEL
  have hXfix : commV X ≤ fixV (X ⊔ Y) := by
    rw [hfix, fixV_sup]
    exact h.commV_le_fixV_inf hX hE hEX.symm fun x hx e he => (hcomm e he x hx).symm
  have hXL : X ≤ X ⊔ Y := le_sup_left
  have hLP : X ⊔ Y ≤ P := sup_le (h.le X hX) (h.le Y hY)
  have hNp := isPGroup_normClosure hXL (h.elemAb X hX).2 hXfix
  have hYp : IsPGroup 2 Y := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb Y hY).2
  have hQp : IsPGroup 2 (normClosure (X ⊔ Y) X ⊔ Y : Subgroup (MulAut V)) :=
    hNp.to_sup_of_normal_left' hYp (le_sup_right.trans le_normalizer_normClosure)
  obtain ⟨T, hT, hQT⟩ := Glauberman.exists_isSylowOf_ge (K := P) hQp
    (sup_le ((normClosure_le hXL).trans hLP) (h.le Y hY))
  exact h.four_seven_pairs hT X ⟨hX, le_normClosure.trans (le_sup_left.trans hQT)⟩ Y
    ⟨hY, le_sup_right.trans hQT⟩

theorem four_eight_main (h : Hyp41 P D) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hB : B ∈ D)
    (hAB : ∃ a ∈ A, ∃ b ∈ B, a * b ≠ b * a) {C : Subgroup (MulAut V)} (hC : C ∈ D)
    (hCL : C ≤ A ⊔ B) (hCA : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) :
    (∀ c ∈ C, ∀ l ∈ A ⊔ B, c * l = l * c) ∨ C = A := by
  by_cases hCA' : C = A
  · exact Or.inr hCA'
  refine Or.inl ?_
  by_contra hcon
  have hcb : ¬ ∀ c ∈ C, ∀ b ∈ B, c * b = b * c := by
    intro hcb
    apply hcon
    intro c hc l hl
    have hle : A ⊔ B ≤ Subgroup.centralizer {c} := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact hCA c hc a ha
      · rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.1 hz]
        exact hcb c hc b hb
    exact Subgroup.mem_centralizer_iff.1 (hle hl) c (Set.mem_singleton c)
  by_cases hcardCB : Nat.card C = Nat.card B
  · obtain ⟨a, ha, b, hb, hne⟩ := hAB
    exact hne (h.four_eight_commute hA hB hC hCA' hCA hcardCB hCL a ha b hb)
  · have hBp : IsPGroup 2 B := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb B hB).2
    have hCp : IsPGroup 2 C := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb C hC).2
    have hL₀P : C ⊔ B ≤ P := sup_le (h.le C hC) (h.le B hB)
    obtain ⟨S₀, hS₀, hBS₀⟩ := Glauberman.exists_isSylowOf_ge (K := C ⊔ B) hBp le_sup_right
    obtain ⟨k, hk, hkS₀⟩ := Glauberman.exists_conj_le_of_isSylowOf hS₀ hCp
      (le_sup_left : C ≤ C ⊔ B)
    obtain ⟨T, hT, hS₀T⟩ :=
      Glauberman.exists_isSylowOf_ge (K := P) hS₀.2.1 (hS₀.1.trans hL₀P)
    have hC' : conjSub k C ∈ D := h.conj_mem C hC k (hL₀P hk)
    have hcomm' := h.four_seven_pairs hT (conjSub k C) ⟨hC', hkS₀.trans hS₀T⟩ B
      ⟨hB, hBS₀.trans hS₀T⟩
    have hcardC' : Nat.card ↥(conjSub k C) = Nat.card C := Glauberman.card_map_conj k C
    have hne' : conjSub k C ≠ B := fun heq => hcardCB (by rw [← hcardC', heq])
    have hle' : conjSub k C ≤ B ⊔ C :=
      (Glauberman.map_conj_le hk (le_sup_left : C ≤ C ⊔ B)).trans (by rw [sup_comm])
    have hBC := h.four_eight_commute hB hC hC' hne' hcomm' hcardC' hle'
    exact hcb fun c hc b hb => (hBC b hb c hc).symm

theorem four_eight_conj (h : Hyp41 P D) {X Y : Subgroup (MulAut V)} (hX : X ∈ D) (hY : Y ∈ D) :
    (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) ∨
      ∃ g ∈ X ⊔ Y, Y = X.map (MulAut.conj g).toMonoidHom := by
  by_cases hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x
  · exact Or.inl hc
  refine Or.inr ?_
  push Not at hc
  obtain ⟨x₀, hx₀, y₀, hy₀, hne⟩ := hc
  have hXp : IsPGroup 2 X := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb X hX).2
  have hYp : IsPGroup 2 Y := Glauberman.isPGroup_two_of_sq_eq_one (h.elemAb Y hY).2
  have hLP : X ⊔ Y ≤ P := sup_le (h.le X hX) (h.le Y hY)
  obtain ⟨S₀, hS₀, hXS₀⟩ := Glauberman.exists_isSylowOf_ge (K := X ⊔ Y) hXp le_sup_left
  obtain ⟨k, hk, hkS₀⟩ := Glauberman.exists_conj_le_of_isSylowOf hS₀ hYp
    (le_sup_right : Y ≤ X ⊔ Y)
  obtain ⟨T, hT, hS₀T⟩ := Glauberman.exists_isSylowOf_ge (K := P) hS₀.2.1 (hS₀.1.trans hLP)
  have hY' : conjSub k Y ∈ D := h.conj_mem Y hY k (hLP hk)
  have hcomm := h.four_seven_pairs hT (conjSub k Y) ⟨hY', hkS₀.trans hS₀T⟩ X
    ⟨hX, hXS₀.trans hS₀T⟩
  have hle : conjSub k Y ≤ X ⊔ Y := Glauberman.map_conj_le hk (le_sup_right : Y ≤ X ⊔ Y)
  rcases h.four_eight_main hX hY ⟨x₀, hx₀, y₀, hy₀, hne⟩ hY' hle hcomm with hz | heq
  · exfalso
    apply hne
    have e := hz _ (mem_conjSub_of_mem (g := k) hy₀) (k * x₀ * k⁻¹)
      (by
        have h1 : k * x₀ * k⁻¹ ∈ X ⊔ Y :=
          (X ⊔ Y).mul_mem ((X ⊔ Y).mul_mem hk (Subgroup.mem_sup_left hx₀)) ((X ⊔ Y).inv_mem hk)
        exact h1)
    calc x₀ * y₀ = k⁻¹ * (k * x₀ * k⁻¹ * (k * y₀ * k⁻¹)) * k := by group
      _ = k⁻¹ * (k * y₀ * k⁻¹ * (k * x₀ * k⁻¹)) * k := by rw [e]
      _ = y₀ * x₀ := by group
  · refine ⟨k⁻¹, (X ⊔ Y).inv_mem hk, ?_⟩
    calc Y = (conjSub k Y).map (MulAut.conj k⁻¹).toMonoidHom :=
          (Glauberman.map_conj_inv_map_conj k Y).symm
      _ = X.map (MulAut.conj k⁻¹).toMonoidHom := by rw [heq]

end Hyp41

end CFSG.CGT.PushingUpLit.BHS
