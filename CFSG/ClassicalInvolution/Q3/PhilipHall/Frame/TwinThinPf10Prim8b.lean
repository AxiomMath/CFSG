module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Prim8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

theorem image_rule (q : Equiv.Perm (Fin n)) (hq : Equiv.Perm.sign q = 1) {X : Set (Finset (Fin n))}
    (rule : ∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin n), Equiv.Perm.sign p = 1 →
      x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X) :
    ∀ x ∈ (fun x : Finset (Fin n) => x.map q.toEmbedding) '' X,
      ∀ y ∈ (fun x : Finset (Fin n) => x.map q.toEmbedding) '' X, ∀ p : Equiv.Perm (Fin n),
        Equiv.Perm.sign p = 1 → x.map p.toEmbedding ∈
          (fun x : Finset (Fin n) => x.map q.toEmbedding) '' X →
        y.map p.toEmbedding ∈ (fun x : Finset (Fin n) => x.map q.toEmbedding) '' X := by
  have hinj : Function.Injective (fun x : Finset (Fin n) => x.map q.toEmbedding) :=
    fun x y h => Finset.map_injective _ h
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ p hp ⟨z, hz, hzp⟩
  have hp'' : Equiv.Perm.sign (q⁻¹ * p * q) = 1 := by
    rw [map_mul, map_mul, map_inv, hq, hp]; simp
  have h1 : (x.map (p * q).toEmbedding).map q⁻¹.toEmbedding =
      x.map (q⁻¹ * (p * q)).toEmbedding := map_map_perm _ _ _
  have h2 : x.map (p * q).toEmbedding = z.map q.toEmbedding := by
    rw [← map_map_perm x q p]; exact hzp.symm
  have h3 : (z.map q.toEmbedding).map q⁻¹.toEmbedding = z := by
    rw [map_map_perm, inv_mul_cancel, map_perm_one]
  have hxz : x.map (q⁻¹ * p * q).toEmbedding = z := by
    rw [mul_assoc, ← h1, h2, h3]
  have hw := rule x hx y hy _ hp'' (by rw [hxz]; exact hz)
  refine ⟨_, hw, ?_⟩
  show (y.map (q⁻¹ * p * q).toEmbedding).map q.toEmbedding =
    (y.map q.toEmbedding).map p.toEmbedding
  rw [map_map_perm, map_map_perm]
  congr 2
  group

theorem map_compl_perm (q : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    (sᶜ).map q.toEmbedding = (s.map q.toEmbedding)ᶜ := by
  ext x
  simp only [Finset.mem_map, Finset.mem_compl, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    exact hy (q.injective hzy ▸ hz)
  · intro hx
    refine ⟨q.symm x, fun h => hx ⟨q.symm x, h, Equiv.apply_symm_apply _ _⟩,
      Equiv.apply_symm_apply _ _⟩

theorem fourSetPrim_eight :
    ∀ (X : Set (Finset (Fin 8))), (∀ x ∈ X, x.card = 4) → ∀ α ∈ X,
      (∃ β ∈ X, β ≠ α ∧ β ≠ αᶜ) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ p : Equiv.Perm (Fin 8), Equiv.Perm.sign p = 1 →
        x.map p.toEmbedding ∈ X → y.map p.toEmbedding ∈ X) →
      ∀ γ : Finset (Fin 8), γ.card = 4 → γ ∈ X := by
  intro X hXc α hαX ⟨β, hβX, hβα, hβc⟩ rule γ hγ
  have ha0 : (sets 8)[0]? = some {4, 5, 6, 7} := by decide +kernel
  have ha0c : ({4, 5, 6, 7} : Finset (Fin 8)).card = 4 := by decide
  have hcomp : ∀ γ : Finset (Fin 8), γ.card = 4 → γ ∈ sets 8 := by decide +kernel
  have c1 : okRep 8 rep8_1 1 chain8_1 = true := by decide +kernel
  have c2 : okRep 8 rep8_2 2 chain8_2 = true := by decide +kernel
  have c3 : okRep 8 rep8_3 3 chain8_3 = true := by decide +kernel
  obtain ⟨q, hq, hqα⟩ := exists_even_perm (hXc α hαX) ha0c
  let X' : Set (Finset (Fin 8)) := (fun x => x.map q.toEmbedding) '' X
  have hinj : Function.Injective (fun x : Finset (Fin 8) => x.map q.toEmbedding) :=
    fun x y h => Finset.map_injective _ h
  have hX'c : ∀ x ∈ X', x.card = 4 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Finset.card_map]; exact hXc x hx
  have hrule' := image_rule q hq rule
  have hβ'X : β.map q.toEmbedding ∈ X' := ⟨β, hβX, rfl⟩
  have hne1 : β.map q.toEmbedding ≠ {4, 5, 6, 7} := fun h => hβα (hinj (h.trans hqα.symm))
  have hne2 : β.map q.toEmbedding ≠ ({4, 5, 6, 7} : Finset (Fin 8))ᶜ := by
    intro h
    rw [← hqα, ← map_compl_perm] at h
    exact hβc (hinj h)
  set β' := β.map q.toEmbedding with hβ'
  have hβ'c : β'.card = 4 := hX'c _ hβ'X
  have hk3 : ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card ≤ 3 := by
    by_contra hcon
    have h4 : ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card = 4 := by
      have := Finset.card_le_card
        (Finset.inter_subset_left : ({4, 5, 6, 7} : Finset (Fin 8)) ∩ β' ⊆ {4, 5, 6, 7})
      omega
    have e1 : ({4, 5, 6, 7} : Finset (Fin 8)) ∩ β' = {4, 5, 6, 7} :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h4, ha0c])
    have e2 : ({4, 5, 6, 7} : Finset (Fin 8)) ⊆ β' := by
      rw [← e1]; exact Finset.inter_subset_right
    exact hne1 (Finset.eq_of_subset_of_card_le e2 (by rw [hβ'c, ha0c])).symm
  have hk0 : 1 ≤ ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card := by
    by_contra hcon
    have h0 : ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)) = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    have hsub : β' ⊆ ({4, 5, 6, 7} : Finset (Fin 8))ᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxa
      have : x ∈ ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)) := Finset.mem_inter.mpr ⟨hxa, hx⟩
      rw [h0] at this; simp at this
    have hcc : (({4, 5, 6, 7} : Finset (Fin 8))ᶜ).card = 4 := by decide
    exact hne2 (Finset.eq_of_subset_of_card_le hsub (by rw [hβ'c, hcc]))
  have hmain : ∀ γ : Finset (Fin 8), γ.card = 4 → γ ∈ X' := by
    have hα0 : ({4, 5, 6, 7} : Finset (Fin 8)) ∈ X' := ⟨α, hαX, hqα⟩
    obtain hk | hk | hk : ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card = 1 ∨
        ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card = 2 ∨
        ({4, 5, 6, 7} ∩ β' : Finset (Fin 8)).card = 3 := by omega
    · exact prim0_rep c1 hcomp hX'c ha0 hα0 hβ'X hk hrule'
    · exact prim0_rep c2 hcomp hX'c ha0 hα0 hβ'X hk hrule'
    · exact prim0_rep c3 hcomp hX'c ha0 hα0 hβ'X hk hrule'
  obtain ⟨x, hx, hxγ⟩ := hmain (γ.map q.toEmbedding) (by rw [Finset.card_map]; exact hγ)
  have := hinj hxγ
  rw [← this]; exact hx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10
