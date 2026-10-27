module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxA

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Idx

open CFSG Subgroup Equiv Equiv.Perm
open scoped commutatorElement

theorem FixCat.of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (e : Y ≃* Z) {n : ℕ}
    (hZ : FixCat Z n) : FixCat Y n := by
  intro α τ hα2 hα1 hτα hτ2 X hXp hXd hXα hXτ
  set c := MulAut.congr e with hc
  have hfix : ∀ β : MulAut Y, (∀ x ∈ X, β x = x) →
      ∀ z ∈ X.map e.toMonoidHom, c β z = z := by
    rintro β hβ _ ⟨x, hx, rfl⟩
    rw [hc, MulAut.congr_apply]
    simp [hβ x hx]
  have h := hZ (c α) (c τ) (by rw [← map_mul, hα2, map_one])
    (fun h1 => hα1 (c.injective (by rw [h1, map_one])))
    (by rw [← map_mul, ← map_mul, hτα])
    (by obtain ⟨k, hk⟩ := hτ2; exact ⟨k, by rw [← map_pow, hk, map_one]⟩)
    (X.map e.toMonoidHom) (by rw [← map_commutator, hXp])
    (by rw [card_map_of_injective e.injective]; exact hXd) (hfix α hXα) (hfix τ hXτ)
  rcases h with h | h
  · exact Or.inl (c.injective (by rw [h, map_one]))
  · exact Or.inr (c.injective h)

variable {m : ℕ}

theorem cycleType_eq_replicate {π : Perm (Fin m)} (hπ2 : π * π = 1) :
    π.cycleType = Multiset.replicate (Multiset.card π.cycleType) 2 := by
  rw [Multiset.eq_replicate]
  refine ⟨rfl, fun n hn => ?_⟩
  have h1 : n ∣ orderOf π := dvd_of_mem_cycleType hn
  have h2 : orderOf π ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hπ2)
  have h3 := two_le_of_mem_cycleType hn
  have := Nat.le_of_dvd (by norm_num) (h1.trans h2)
  omega

theorem card_centralizer_inv {π : Perm (Fin m)} (hπ2 : π * π = 1) (hπ1 : π ≠ 1) :
    Nat.card (centralizer ({π} : Set (Perm (Fin m)))) =
      (m - 2 * Multiset.card π.cycleType).factorial * 2 ^ Multiset.card π.cycleType *
        (Multiset.card π.cycleType).factorial := by
  have hct := cycleType_eq_replicate hπ2
  set k := Multiset.card π.cycleType with hk
  have hk0 : k ≠ 0 := by
    intro h0
    apply hπ1
    rw [← cycleType_eq_zero, hct, h0, Multiset.replicate_zero]
  rw [nat_card_centralizer, hct, Multiset.sum_replicate, Multiset.prod_replicate,
    Multiset.toFinset_replicate]
  simp only [hk0, ↓reduceIte, Finset.prod_singleton, Multiset.count_replicate_self,
    Fintype.card_fin, smul_eq_mul]
  rw [mul_comm k 2]

theorem not_dvd_of_two_le {k : ℕ} (hm : m = 7 ∨ m = 8 ∨ m = 9) (hk : 2 ≤ k)
    (hkm : 2 * k ≤ m) :
    ¬ (m - 2).factorial / 2 ∣ (m - 2 * k).factorial * 2 ^ k * k.factorial := by
  have hk4 : k ≤ 4 := by omega
  rcases hm with rfl | rfl | rfl <;> interval_cases k <;> decide

theorem fix_or_swap_of_comm {i j : Fin m} (hij : i ≠ j) {x : Perm (Fin m)}
    (hx : swap i j * x = x * swap i j) : (x i = i ∧ x j = j) ∨ (x i = j ∧ x j = i) := by
  have hi : swap i j (x i) = x j := by
    have := congrArg (fun f : Perm (Fin m) => f i) hx
    simpa [Perm.mul_apply, swap_apply_left] using this
  have hj : swap i j (x j) = x i := by
    have := congrArg (fun f : Perm (Fin m) => f j) hx
    simpa [Perm.mul_apply, swap_apply_right] using this
  by_cases h1 : x i = i
  · left
    refine ⟨h1, ?_⟩
    rw [← hi, h1, swap_apply_left]
  · by_cases h2 : x i = j
    · right
      refine ⟨h2, ?_⟩
      rw [← hi, h2, swap_apply_right]
    · exfalso
      rw [swap_apply_of_ne_of_ne h1 h2] at hi
      exact hij (x.injective hi)

theorem commutator_fix {i j : Fin m} {x y : Perm (Fin m)}
    (hx : (x i = i ∧ x j = j) ∨ (x i = j ∧ x j = i))
    (hy : (y i = i ∧ y j = j) ∨ (y i = j ∧ y j = i)) : ⁅x, y⁆ i = i ∧ ⁅x, y⁆ j = j := by
  have hxi : ∀ {u v : Fin m}, x u = v → x⁻¹ v = u := fun h => Perm.inv_eq_iff_eq.mpr h.symm
  have hyi : ∀ {u v : Fin m}, y u = v → y⁻¹ v = u := fun h => Perm.inv_eq_iff_eq.mpr h.symm
  rw [commutatorElement_def]
  rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;> rcases hy with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;>
    simp [Perm.mul_apply, hx1, hx2, hy1, hy2, hxi hx1, hxi hx2, hyi hy1, hyi hy2]

abbrev altCompl (i j : Fin m) : Subgroup (Perm (Fin m)) :=
  (alternatingGroup {x : Fin m // x ≠ i ∧ x ≠ j}).map
    (ofSubtype : Perm {x : Fin m // x ≠ i ∧ x ≠ j} →* Perm (Fin m))

theorem mem_altCompl {i j : Fin m} {x : Perm (Fin m)} (hxi : x i = i) (hxj : x j = j)
    (hx : sign x = 1) : x ∈ altCompl i j := by
  have h₁ : ∀ y, (x y ≠ i ∧ x y ≠ j) ↔ (y ≠ i ∧ y ≠ j) := by
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by rw [h]; exact hxi), fun h => h2 (by rw [h]; exact hxj)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (x.injective (h.trans hxi.symm)),
        fun h => h2 (x.injective (h.trans hxj.symm))⟩
  have h₂ : ∀ y, x y ≠ y → (y ≠ i ∧ y ≠ j) := by
    intro y hy
    exact ⟨fun h => hy (by rw [h]; exact hxi), fun h => hy (by rw [h]; exact hxj)⟩
  refine ⟨x.subtypePerm h₁, ?_, ofSubtype_subtypePerm h₁ h₂⟩
  rw [SetLike.mem_coe, mem_alternatingGroup, sign_subtypePerm x h₁ h₂, hx]

theorem card_compl {i j : Fin m} (hij : i ≠ j) :
    Fintype.card {x : Fin m // x ≠ i ∧ x ≠ j} = m - 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun x : Fin m => x ≠ i ∧ x ≠ j) = Finset.univ \ {i, j} := by
    ext x
    simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, Finset.card_pair hij]

theorem card_altCompl {i j : Fin m} (hij : i ≠ j) (hm : 4 ≤ m) :
    Nat.card (altCompl i j) = (m - 2).factorial / 2 := by
  have : Nontrivial {x : Fin m // x ≠ i ∧ x ≠ j} :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [card_compl hij]; omega)
  rw [card_map_of_injective ofSubtype_injective, Nat.card_eq_fintype_card,
    card_alternatingGroup, card_compl hij]

theorem apply_mem_support_of_comm {ρ σ : Perm (Fin m)} (h : ρ * σ = σ * ρ) {a : Fin m}
    (ha : a ∈ σ.support) : ρ a ∈ σ.support := by
  have h1 : ρ * σ * ρ⁻¹ = σ := by rw [h, mul_inv_cancel_right]
  have h2 := support_conj (σ := ρ) (τ := σ)
  rw [h1] at h2
  rw [h2]
  exact Finset.mem_map_of_mem _ ha

theorem three_cycle_mem {i j a b c : Fin m} (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i)
    (hbj : b ≠ j) (hci : c ≠ i) (hcj : c ≠ j) (hab : b ≠ a) (hac : a ≠ c) :
    swap b a * swap a c ∈ altCompl i j := by
  refine mem_altCompl ?_ ?_ ?_
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hai.symm hci.symm,
      swap_apply_of_ne_of_ne hbi.symm hai.symm]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne haj.symm hcj.symm,
      swap_apply_of_ne_of_ne hbj.symm haj.symm]
  · rw [Perm.sign_mul, sign_swap hab, sign_swap hac]
    rfl

theorem eq_of_comm_altCompl {i j : Fin m} (hij : i ≠ j) (hm : 7 ≤ m) {ρ : Perm (Fin m)}
    (hρ : ∀ x ∈ altCompl i j, ρ * x = x * ρ) {a : Fin m} (hai : a ≠ i) (haj : a ≠ j) :
    ρ a = a := by
  set s : Finset (Fin m) := ((Finset.univ.erase i).erase j).erase a with hs
  have hscard : s.card = m - 3 := by
    rw [hs, Finset.card_erase_of_mem (by simp [hai, haj]),
      Finset.card_erase_of_mem (by simp [hij.symm]), Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < s.card)
  obtain ⟨c, hc⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hb]; omega : 0 < (s.erase b).card)
  obtain ⟨d, hd⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hc, Finset.card_erase_of_mem hb]; omega :
      0 < ((s.erase b).erase c).card)
  obtain ⟨e, he⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hd, Finset.card_erase_of_mem hc,
      Finset.card_erase_of_mem hb]; omega : 0 < (((s.erase b).erase c).erase d).card)
  simp only [hs, Finset.mem_erase, Finset.mem_univ, and_true] at hb hc hd he
  obtain ⟨hba, hbj, hbi⟩ := hb
  obtain ⟨hcb, hca, hcj, hci⟩ := hc
  obtain ⟨hdc, hdb, hda, hdj, hdi⟩ := hd
  obtain ⟨hed, hec, heb, hea, hej, hei⟩ := he
  have hn1 : List.Nodup [b, a, c] := by simp [hba, hca.symm, hcb.symm]
  have hn2 : List.Nodup [d, a, e] := by simp [hda, hea.symm, hed.symm]
  have h1 := apply_mem_support_of_comm
    (hρ _ (three_cycle_mem hai haj hbi hbj hci hcj hba hca.symm)) (a := a)
    (by rw [support_swap_mul_swap hn1]; simp)
  have h2 := apply_mem_support_of_comm
    (hρ _ (three_cycle_mem hai haj hdi hdj hei hej hda hea.symm)) (a := a)
    (by rw [support_swap_mul_swap hn2]; simp)
  rw [support_swap_mul_swap hn1] at h1
  rw [support_swap_mul_swap hn2] at h2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1 | h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hdb.symm
    · exact h2
    · exact absurd (h1.symm.trans h2) heb.symm
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd (h1.symm.trans h2) hdc.symm
    · exact h2
    · exact absurd (h1.symm.trans h2) hec.symm

theorem fixCat_alt (hm : m = 7 ∨ m = 8 ∨ m = 9) :
    FixCat (alternatingGroup (Fin m)) ((m - 2).factorial / 2) := by
  intro α τ hα2 hα1 hτα _ X hXp hXd hXα hXτ
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m (by omega)
    (by omega)
  obtain ⟨π, rfl⟩ := hbij.2 α
  obtain ⟨ρ, rfl⟩ := hbij.2 τ
  have hπ2 : π * π = 1 := hbij.1 (by rw [map_mul, hα2, map_one])
  have hπ1 : π ≠ 1 := fun h1 => hα1 (by rw [h1, map_one])
  have hρπ : ρ * π = π * ρ := hbij.1 (by rw [map_mul, map_mul, hτα])
  have hcomm : ∀ (σ : Perm (Fin m)) (x : alternatingGroup (Fin m)),
      MulAut.conjNormal σ x = x → σ * (x : Perm (Fin m)) = x * σ := by
    intro σ x hx
    have h1 := congrArg Subtype.val hx
    rw [MulAut.conjNormal_apply] at h1
    calc σ * (x : Perm (Fin m)) = σ * x * σ⁻¹ * σ := by group
      _ = x * σ := by rw [h1]
  set X' := X.map (alternatingGroup (Fin m)).subtype with hX'
  have hX'π : ∀ x ∈ X', π * x = x * π := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm π x (hXα x hx)
  have hX'ρ : ∀ x ∈ X', ρ * x = x * ρ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcomm ρ x (hXτ x hx)
  have hX'card : Nat.card X' = Nat.card X := card_map_of_injective (subtype_injective _)
  have hX'C : X' ≤ centralizer ({π} : Set (Perm (Fin m))) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hX'π x hx).symm
  have hdvd : (m - 2).factorial / 2 ∣ Nat.card (centralizer ({π} : Set (Perm (Fin m)))) :=
    hXd.trans (hX'card ▸ card_dvd_of_le hX'C)
  rw [card_centralizer_inv hπ2 hπ1] at hdvd
  have hct := cycleType_eq_replicate hπ2
  have hk0 : Multiset.card π.cycleType ≠ 0 := by
    intro h0
    apply hπ1
    rw [← cycleType_eq_zero, hct, h0, Multiset.replicate_zero]
  have hkm : 2 * Multiset.card π.cycleType ≤ m := by
    have h1 := sum_cycleType_le π
    rw [hct, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at h1
    omega
  have hk1 : Multiset.card π.cycleType = 1 := by
    by_contra hk
    exact not_dvd_of_two_le hm (by omega) hkm hdvd
  obtain ⟨i, j, hij, rfl⟩ : ∃ i j, i ≠ j ∧ π = swap i j := by
    have hsupp : π.support.card = 2 := by
      rw [← sum_cycleType, hct, hk1]
      simp
    exact card_support_eq_two.mp hsupp
  have hP : ∀ x ∈ X', (x i = i ∧ x j = j) ∨ (x i = j ∧ x j = i) := fun x hx =>
    fix_or_swap_of_comm hij (hX'π x hx)
  have hX'perf : ⁅X', X'⁆ = X' := by rw [hX', ← map_commutator, hXp]
  have hX'le : X' ≤ altCompl i j := by
    refine le_trans (le_of_eq hX'perf.symm) ?_
    rw [commutator_le]
    intro x hx y hy
    obtain ⟨h1, h2⟩ := commutator_fix (hP x hx) (hP y hy)
    refine mem_altCompl h1 h2 ?_
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hX'eq : X' = altCompl i j := eq_of_le_of_card_ge hX'le (by
    rw [card_altCompl hij (by omega), hX'card]
    exact Nat.le_of_dvd Nat.card_pos hXd)
  have hρfix : ∀ a, a ≠ i → a ≠ j → ρ a = a := fun a hai haj =>
    eq_of_comm_altCompl hij (by omega) (fun x hx => hX'ρ x (hX'eq ▸ hx)) hai haj
  rcases fix_or_swap_of_comm hij hρπ.symm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    have : ρ = 1 := by
      ext a
      by_cases hai : a = i
      · rw [hai, h1]; rfl
      by_cases haj : a = j
      · rw [haj, h2]; rfl
      rw [hρfix a hai haj]; rfl
    rw [this, map_one]
  · right
    congr 1
    ext a
    by_cases hai : a = i
    · rw [hai, h1, swap_apply_left]
    by_cases haj : a = j
    · rw [haj, h2, swap_apply_right]
    rw [hρfix a hai haj, swap_apply_of_ne_of_ne hai haj]

variable {H : Type} [Group H] [Finite H] (h : GSThmB.Hyp52 H)

theorem T_le_case_alt {n : ℕ} (hn : n = 5 ∨ n = 6 ∨ n = 7)
    (hJ : Nonempty (GSThmB.OddBar h.J ≃* alternatingGroup (Fin n)))
    (hKa : conjugate h.K h.a = h.K)
    (hK : Nonempty (GSThmB.OddBar h.K ≃* alternatingGroup (Fin (n + 2)))) :
    h.T ≤ zpowers h.a ⊔ h.B := by
  obtain ⟨eJ⟩ := hJ
  obtain ⟨eK⟩ := hK
  apply T_le_of_fixCat h hKa
  have hc : Nat.card (GSThmB.OddBar h.J) = (n + 2 - 2).factorial / 2 := by
    rw [Nat.card_congr eJ.toEquiv, Nat.add_sub_cancel]
    rcases hn with rfl | rfl | rfl <;>
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rw [hc]
  exact (fixCat_alt (m := n + 2) (by omega)).of_mulEquiv eK

end Idx

end CFSG.ComponentClassification.CatFactsL4U4
