module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.AGLEmbedding.LeviBlock

section Simple

variable {W T U : Type*} [Group W] [Group T] [Group U]

theorem card_dvd_ker_or_card_eq [Finite W] [IsSimpleGroup T] [IsSimpleGroup U]
    (σ : W →* T) (hσ : Function.Surjective σ) (ψ : W →* U) (hψ : Function.Surjective ψ) :
    Nat.card U ∣ Nat.card σ.ker ∨ Nat.card T = Nat.card U := by
  have : (σ.ker.map ψ).Normal := (MonoidHom.normal_ker σ).map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (σ.ker.map ψ) with h | h
  · right
    obtain ⟨φ, hφ, -⟩ := exists_factor σ hσ ψ hψ ((Subgroup.map_eq_bot_iff _).mp h)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
    · exact Nat.card_congr (Equiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hk, hφ⟩)
    · exfalso
      obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := U)).exists_pair_ne
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hx : x ∈ φ.ker := hk ▸ Subgroup.mem_top x
      have hy : y ∈ φ.ker := hk ▸ Subgroup.mem_top y
      exact hab (by rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy])
  · left
    have := Subgroup.card_map_dvd σ.ker ψ
    rwa [h, Subgroup.card_top] at this

end Simple

section Quotient

variable {X U : Type*} [Group X] [Finite X] [Group U] [Finite U] [IsSimpleGroup U]

omit [Finite U] in
theorem card_dvd_ker_of_simple {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (h3 : 3 ∣ Nat.card Q) (ρ : X →* Q) (hρ : Function.Surjective ρ) {O W : Subgroup X}
    [O.Normal] (hO3 : Nat.Coprime 3 (Nat.card O)) [(W ⊔ O).Normal] (ψ : ↥W →* U)
    (hψ : Function.Surjective ψ) : Nat.card U ∣ Nat.card ρ.ker ∨ Nat.card Q = Nat.card U := by
  have hOb : O.map ρ = ⊥ := by
    have : (O.map ρ).Normal := ‹O.Normal›.map ρ hρ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map ρ) with h | h
    · exact h
    · exfalso
      have hd := Subgroup.card_map_dvd O ρ
      rw [h, Subgroup.card_top] at hd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.Coprime.coprime_dvd_right hd hO3) h3
  have hWO : ((W ⊔ O).map ρ).Normal := ‹(W ⊔ O).Normal›.map ρ hρ
  rw [Subgroup.map_sup, hOb, sup_bot_eq] at hWO
  have hker : Nat.card (ρ.comp W.subtype).ker ∣ Nat.card ρ.ker := by
    rw [← MonoidHom.comap_ker]
    exact Subgroup.card_comap_dvd_of_injective _ _ W.subtype_injective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (W.map ρ) with h | h
  · left
    have hWk : W ≤ ρ.ker := (Subgroup.map_eq_bot_iff W).mp h
    exact (Subgroup.card_dvd_of_surjective hψ).trans (Subgroup.card_dvd_of_le hWk)
  · have hσ : Function.Surjective (ρ.comp W.subtype) := by
      intro y
      obtain ⟨w, hw, rfl⟩ := (h ▸ Subgroup.mem_top y : y ∈ W.map ρ)
      exact ⟨⟨w, hw⟩, rfl⟩
    rcases card_dvd_ker_or_card_eq _ hσ ψ hψ with h' | h'
    · exact Or.inl (h'.trans hker)
    · exact Or.inr h'

omit [Finite U] in
theorem card_dvd_ker_of_perm {n : ℕ} (hn : 5 ≤ n)
    (hnU : Nat.card (alternatingGroup (Fin n)) ≠ Nat.card U)
    (ρ : X →* Equiv.Perm (Fin n)) (hρ : Function.Surjective ρ) {O W : Subgroup X} [O.Normal]
    (hO3 : Nat.Coprime 3 (Nat.card O)) (hidx : (W ⊔ O).index ≤ 2) (hW : ⁅W, W⁆ = W)
    (ψ : ↥W →* U) (hψ : Function.Surjective ψ) : Nat.card U ∣ Nat.card ρ.ker := by
  set A := alternatingGroup (Fin n) with hA
  have h5 : 5 ≤ Nat.card (Fin n) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
  have : IsSimpleGroup A := alternatingGroup.isSimpleGroup h5
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h3A : 3 ∣ Nat.card A := by
    have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
    have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [← hAc] at h3
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)
  set N := O.map ρ with hN
  have : N.Normal := ‹O.Normal›.map ρ hρ
  have hNA : ∀ x ∈ N, x ∈ A → x = 1 := by
    have : (N.subgroupOf A).Normal := Subgroup.Normal.subgroupOf ‹N.Normal› A
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
    · intro x hxN hxA
      have : (⟨x, hxA⟩ : A) ∈ N.subgroupOf A := Subgroup.mem_subgroupOf.mpr hxN
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hAN : A ≤ N := fun a ha => by
        have : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have hd : Nat.card A ∣ Nat.card O :=
        (Subgroup.card_dvd_of_le hAN).trans (Subgroup.card_map_dvd O ρ)
      exact absurd (Nat.Coprime.coprime_dvd_right (h3A.trans hd) hO3) (by norm_num)
  have hWA : W.map ρ ≤ A := by
    have hc : ⁅W.map ρ, W.map ρ⁆ = W.map ρ := by rw [← Subgroup.map_commutator, hW]
    rw [← hc, hA, alternatingGroup_eq_sign_ker]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker Equiv.Perm.sign)
  have hAWN : A ≤ W.map ρ ⊔ N := by
    rw [← Subgroup.map_sup]
    exact Equiv.Perm.alternatingGroup_le_of_index_le_two
      ((Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
        (Subgroup.index_map_dvd _ hρ)).trans hidx)
  have hAW : A ≤ W.map ρ := by
    intro a ha
    obtain ⟨w, hw, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hAWN ha)
    have hmA : m ∈ A := by
      have := A.mul_mem (A.inv_mem (hWA hw)) ha
      rwa [inv_mul_cancel_left] at this
    rw [hNA m hm hmA, mul_one]
    exact hw
  have hWeq : W.map ρ = A := le_antisymm hWA hAW
  set σ : ↥W →* A := (ρ.comp W.subtype).codRestrict A (fun w => hWA ⟨w, w.2, rfl⟩) with hσd
  have hσ : Function.Surjective σ := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw, rfl⟩ := (hWeq ▸ ha : a ∈ W.map ρ)
    exact ⟨⟨w, hw⟩, rfl⟩
  have hker : Nat.card σ.ker ∣ Nat.card ρ.ker := by
    rw [hσd, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
    exact Subgroup.card_comap_dvd_of_injective _ _ W.subtype_injective
  rcases card_dvd_ker_or_card_eq σ hσ ψ hψ with h | h
  · exact h.trans hker
  · exact absurd h hnU

end Quotient

end CFSG.AGLEmbedding.LeviBlock
