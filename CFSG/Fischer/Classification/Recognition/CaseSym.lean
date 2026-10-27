module

public import CFSG.Fischer.Classification.Recognition.SymOBasic

public section

namespace CFSG.Fischer.Classification.Recognition

open CFSG.Open Equiv Equiv.Perm
open scoped commutatorElement

namespace SymO

variable {n : ℕ} {a b : Fin n}

def altCompl (a b : Fin n) : Subgroup (Perm (Fin n)) :=
  (alternatingGroup {x : Fin n // x ≠ a ∧ x ≠ b}).map ofSubtype

theorem card_compl (hab : a ≠ b) : Nat.card {x : Fin n // x ≠ a ∧ x ≠ b} = n - 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun x : Fin n => x ≠ a ∧ x ≠ b) = (Finset.univ.erase a).erase b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    tauto
  rw [h, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  omega

theorem altCompl_le_centralizer : altCompl a b ≤ Subgroup.centralizer {swap a b} := by
  rintro _ ⟨σ, -, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, mul_swap_eq_swap_mul,
    ofSubtype_apply_of_not_mem σ fun h => h.1 rfl, ofSubtype_apply_of_not_mem σ fun h => h.2 rfl]

theorem apply_of_mem_centralizer (hab : a ≠ b) {g : Perm (Fin n)}
    (hg : g ∈ Subgroup.centralizer {swap a b}) :
    (g a = a ∧ g b = b ∧ g⁻¹ a = a ∧ g⁻¹ b = b) ∨ (g a = b ∧ g b = a ∧ g⁻¹ a = b ∧ g⁻¹ b = a) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  have h1 : g b = swap a b (g a) := by
    simpa [Perm.mul_apply] using DFunLike.congr_fun hg a
  by_cases ha : g a = a
  · have hb : g b = b := by rw [h1, ha, swap_apply_left]
    exact Or.inl ⟨ha, hb, Perm.inv_eq_iff_eq.mpr ha.symm, Perm.inv_eq_iff_eq.mpr hb.symm⟩
  by_cases ha' : g a = b
  · have hb : g b = a := by rw [h1, ha', swap_apply_right]
    exact Or.inr ⟨ha', hb, Perm.inv_eq_iff_eq.mpr hb.symm, Perm.inv_eq_iff_eq.mpr ha'.symm⟩
  · rw [swap_apply_of_ne_of_ne ha ha'] at h1
    exact absurd (g.injective h1) hab.symm

theorem commutatorElement_mem_altCompl (hab : a ≠ b) {g₁ g₂ : Perm (Fin n)}
    (h₁ : g₁ ∈ Subgroup.centralizer {swap a b}) (h₂ : g₂ ∈ Subgroup.centralizer {swap a b}) :
    ⁅g₁, g₂⁆ ∈ altCompl a b := by
  set τ := ⁅g₁, g₂⁆ with hτ
  have hfix : τ a = a ∧ τ b = b := by
    rcases apply_of_mem_centralizer hab h₁ with ⟨p1, p2, p3, p4⟩ | ⟨p1, p2, p3, p4⟩ <;>
    rcases apply_of_mem_centralizer hab h₂ with ⟨q1, q2, q3, q4⟩ | ⟨q1, q2, q3, q4⟩ <;>
    simp [hτ, commutatorElement_def, Perm.mul_apply, p1, p2, p3, p4, q1, q2, q3, q4]
  have hsign : sign τ = 1 := by
    rw [hτ, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  have hp : ∀ x, (τ x ≠ a ∧ τ x ≠ b) ↔ (x ≠ a ∧ x ≠ b) := by
    intro x
    have ea : τ x = a ↔ x = a :=
      ⟨fun h => τ.injective (h.trans hfix.1.symm), fun h => by rw [h, hfix.1]⟩
    have eb : τ x = b ↔ x = b :=
      ⟨fun h => τ.injective (h.trans hfix.2.symm), fun h => by rw [h, hfix.2]⟩
    rw [Ne, Ne, ea, eb]
  have hmove : ∀ x, τ x ≠ x → x ≠ a ∧ x ≠ b := fun x hx =>
    ⟨fun h => hx (by rw [h, hfix.1]), fun h => hx (by rw [h, hfix.2])⟩
  refine ⟨τ.subtypePerm hp, ?_, ofSubtype_subtypePerm hp hmove⟩
  rw [SetLike.mem_coe, mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm hp hmove,
    hsign]

theorem card_quotient_center_of_isComponentOf_perm (hab : a ≠ b) (hn : 7 ≤ n)
    {K : Subgroup (Perm (Fin n))} (hK : IsComponentOf K (Subgroup.centralizer {swap a b})) :
    Nat.card (K ⧸ Subgroup.center K) = (n - 2).factorial / 2 := by
  have hΩ := card_compl hab
  have : Nontrivial {x : Fin n // x ≠ a ∧ x ≠ b} := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have e : alternatingGroup {x : Fin n // x ≠ a ∧ x ≠ b} ≃* altCompl a b :=
    Subgroup.equivMapOfInjective _ _ ofSubtype_injective
  have hA : IsSimpleGroup (altCompl a b) :=
    have := alternatingGroup.isSimpleGroup (α := {x : Fin n // x ≠ a ∧ x ≠ b}) (by omega)
    e.symm.isSimpleGroup
  have hKA : K ≤ altCompl a b :=
    (IsQuasisimple.le_commutator hK.2.2).trans ((Subgroup.commutator_mono hK.1 hK.1).trans
      (Subgroup.commutator_le.mpr fun _ h₁ _ h₂ => commutatorElement_mem_altCompl hab h₁ h₂))
  have hKeq : K = altCompl a b := by
    rcases IsSubnormal.inf_eq_bot_or_le hK.2.1 altCompl_le_centralizer hA with h | h
    · rw [inf_eq_left.mpr hKA] at h
      refine (IsQuasisimple.not_le_of_comm hK.2.2 (A := ⊥) (fun x hx z hz => ?_) h.le).elim
      rw [Subgroup.mem_bot.mp hx, Subgroup.mem_bot.mp hz]
    · exact le_antisymm hKA h
  have hKs : IsSimpleGroup K := (MulEquiv.subgroupCongr hKeq).isSimpleGroup
  have hZ : Subgroup.center K = ⊥ :=
    (hKs.eq_bot_or_eq_top_of_normal (Subgroup.center K)).resolve_right (center_ne_top hK.2.2)
  rw [hZ, ← Subgroup.index, Subgroup.index_bot,
    Nat.card_congr (MulEquiv.subgroupCongr hKeq).toEquiv, ← Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup, hΩ]

end SymO

open SymO

theorem componentOrder_case1 {G : Type} [Group G] {D : Set G}
    (hN : ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap)
    {d : G} (hd : d ∈ D) {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) :
    Nat.card (K ⧸ Subgroup.center K) ∉ fischerComponentOrders := by
  obtain ⟨m, -, φ, hφ⟩ := hN
  obtain ⟨a, b, hab, hdab⟩ := (hφ d).mp hd
  have hK' : IsComponentOf (K.map φ.toMonoidHom) (Subgroup.centralizer {swap a b}) := by
    rw [← hdab, ← map_centralizer_singleton]
    exact IsComponentOf.map_mulEquiv φ hK
  rw [← card_quotient_center_map_mulEquiv φ K]
  rcases Nat.lt_or_ge m 7 with hm | hm
  · refine notMem_of_lt (lt_of_le_of_lt (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _))
      (lt_of_le_of_lt (Subgroup.card_le_card_group _) ?_))
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    calc m.factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
      _ < 9196830720 := by decide
  · rw [card_quotient_center_of_isComponentOf_perm hab hm hK']
    exact factorial_div_two_notMem _

end CFSG.Fischer.Classification.Recognition
