module

public import CFSG.LargeExtraspecial.S12TriB

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Subgroup Equiv CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

variable {m : ℕ}

theorem exists_notMem_of_card_lt (s : Finset (Fin m)) (h : s.card < m) : ∃ k, k ∉ s := by
  by_contra hk
  push Not at hk
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ s := fun x _ => hk x
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem exists_ne_six (hm : 7 ≤ m) (a b c e g h : Fin m) :
    ∃ k, k ≠ a ∧ k ≠ b ∧ k ≠ c ∧ k ≠ e ∧ k ≠ g ∧ k ≠ h := by
  have hcard : ({a, b, c, e, g, h} : Finset (Fin m)).card < m := by
    refine lt_of_le_of_lt (Finset.card_le_six) (by omega)
  obtain ⟨k, hk⟩ := exists_notMem_of_card_lt _ hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2⟩

theorem swap_mul_swap_ne {p q s : Fin m} (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    swap p q * swap p s ≠ swap p s * swap p q := by
  intro h
  have := congrArg (fun σ : Perm (Fin m) => σ p) h
  simp only [Perm.mul_apply, swap_apply_left] at this
  rw [swap_apply_of_ne_of_ne hps.symm hqs.symm, swap_apply_of_ne_of_ne hpq.symm hqs] at this
  exact hqs this.symm

theorem swap_disjoint_of_commute {p q r s : Fin m} (hpq : p ≠ q) (hrs : r ≠ s)
    (hc : swap p q * swap r s = swap r s * swap p q) (hne : swap p q ≠ swap r s) :
    p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · subst h
    have hqs : q ≠ s := fun h' => hne (by rw [h'])
    exact swap_mul_swap_ne hpq hrs hqs hc
  · subst h
    have hqr : q ≠ r := fun h' => hne (by rw [h', swap_comm])
    rw [swap_comm r p] at hc
    exact swap_mul_swap_ne hpq hrs.symm hqr hc
  · subst h
    have hps : p ≠ s := fun h' => hne (by rw [h', swap_comm])
    rw [swap_comm p q] at hc
    exact swap_mul_swap_ne hpq.symm hrs hps hc
  · subst h
    have hpr : p ≠ r := fun h' => hne (by rw [h'])
    rw [swap_comm p q, swap_comm r q] at hc
    exact swap_mul_swap_ne hpq.symm hrs.symm hpr hc

theorem swap_mul_swap_comm {p q r s : Fin m} (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p ≠ r)
    (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) :
    swap p q * swap r s = swap r s * swap p q :=
  (Perm.Disjoint.commute (Perm.disjoint_swap_swap (by simp [hpq, hrs, hpr, hps, hqr, hqs]))).eq

theorem apply_eq_of_commute_swap {y : Perm (Fin m)} {c e k : Fin m} (hce : c ≠ e) (hck : c ≠ k)
    (hek : e ≠ k) (h1 : y * swap c e = swap c e * y) (h2 : y * swap c k = swap c k * y) :
    y c = c := by
  have e1 := congrArg (fun σ : Perm (Fin m) => σ c) h1
  have e2 := congrArg (fun σ : Perm (Fin m) => σ c) h2
  simp only [Perm.mul_apply, swap_apply_left] at e1 e2
  by_contra hyc
  by_cases hye : y c = e
  · rw [hye, swap_apply_of_ne_of_ne hce.symm hek] at e2
    exact hck (y.injective (e2.trans hye.symm)).symm
  · rw [swap_apply_of_ne_of_ne hyc hye] at e1
    exact hce (y.injective (e1.trans rfl)).symm

theorem triGood_perm (hm : 7 ≤ m) {D : Set (Perm (Fin m))} (hH : Hyp (Perm (Fin m)) D)
    (hna : ∃ a b : commutator (Perm (Fin m)), a * b ≠ b * a) (hD : ∀ σ, σ ∈ D ↔ σ.IsSwap)
    {τ : Perm (Fin m)} (hτ : τ ∈ D) (hτX : τ ∉ commutator (Perm (Fin m))) :
    TriGood (Perm (Fin m)) τ := by
  obtain ⟨a, b, hab, rfl⟩ := (hD _).1 hτ
  have hstar : ∀ {c e : Fin m}, c ≠ e → c ≠ a → c ≠ b → e ≠ a → e ≠ b →
      swap c e ∈ LocalClass D (swap a b) := by
    intro c e hce hca hcb hea heb
    refine ⟨(hD _).2 (Perm.swap_isSwap_iff.2 hce), fun h => ?_,
      swap_mul_swap_comm hce hab hca hcb hea heb⟩
    have := congrArg (fun σ : Perm (Fin m) => σ c) h
    simp only [swap_apply_left] at this
    rw [swap_apply_of_ne_of_ne hca hcb] at this
    exact hce this.symm
  have hstar' : ∀ σ ∈ LocalClass D (swap a b), ∃ c e : Fin m, c ≠ e ∧ c ≠ a ∧ c ≠ b ∧
      e ≠ a ∧ e ≠ b ∧ σ = swap c e := by
    rintro σ ⟨hσ, hne, hc⟩
    obtain ⟨c, e, hce, rfl⟩ := (hD _).1 hσ
    obtain ⟨h1, h2, h3, h4⟩ := swap_disjoint_of_commute hce hab hc hne
    exact ⟨c, e, hce, h1, h2, h3, h4, rfl⟩
  refine triGood_of_local hH hna hτ hτX ?_ ?_ ?_
  ·
    intro y hyτ hyD
    have hfix : ∀ c, c ≠ a → c ≠ b → y c = c := by
      intro c hca hcb
      obtain ⟨e, he⟩ := exists_notMem_of_card_lt ({a, b, c} : Finset (Fin m))
        (lt_of_le_of_lt Finset.card_le_three (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
      obtain ⟨k, hk⟩ := exists_notMem_of_card_lt ({a, b, c, e} : Finset (Fin m))
        (lt_of_le_of_lt Finset.card_le_four (by omega))
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      exact apply_eq_of_commute_swap (Ne.symm he.2.2) (Ne.symm hk.2.2.1) (Ne.symm hk.2.2.2)
        (hyD _ (hstar (Ne.symm he.2.2) hca hcb he.1 he.2.1))
        (hyD _ (hstar (Ne.symm hk.2.2.1) hca hcb hk.1 hk.2.1))
    have e1 := congrArg (fun σ : Perm (Fin m) => σ a) hyτ
    simp only [Perm.mul_apply, swap_apply_left] at e1
    by_cases hya : y a = a
    · left
      have hyb : y b = b := by rw [e1, hya, swap_apply_left]
      ext x
      by_cases hxa : x = a
      · rw [hxa, hya]; rfl
      by_cases hxb : x = b
      · rw [hxb, hyb]; rfl
      rw [hfix x hxa hxb]; rfl
    · by_cases hyab : y a = b
      · right
        have hyb : y b = a := by rw [e1, hyab, swap_apply_right]
        ext x
        by_cases hxa : x = a
        · rw [hxa, hyab, swap_apply_left]
        by_cases hxb : x = b
        · rw [hxb, hyb, swap_apply_right]
        rw [hfix x hxa hxb, swap_apply_of_ne_of_ne hxa hxb]
      · exfalso
        have := hfix (y a) hya hyab
        exact hya (y.injective this)
  ·
    obtain ⟨c, hc⟩ := exists_notMem_of_card_lt ({a, b} : Finset (Fin m))
      (lt_of_le_of_lt (Finset.card_le_two) (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    obtain ⟨e, he⟩ := exists_notMem_of_card_lt ({a, b, c} : Finset (Fin m))
      (lt_of_le_of_lt Finset.card_le_three (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at he
    obtain ⟨g, hg⟩ := exists_notMem_of_card_lt ({a, b, c, e} : Finset (Fin m))
      (lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg
    obtain ⟨h, hh⟩ := exists_notMem_of_card_lt ({a, b, c, e, g} : Finset (Fin m))
      (lt_of_le_of_lt Finset.card_le_five (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hh
    refine ⟨swap c e, hstar (Ne.symm he.2.2) hc.1 hc.2 he.1 he.2.1, swap g h,
      hstar (Ne.symm hh.2.2.2.2) hg.1 hg.2.1 hh.1 hh.2.1, fun hce => ?_, ?_⟩
    · have := congrArg (fun σ : Perm (Fin m) => σ c) hce
      simp only [swap_apply_left] at this
      rw [swap_apply_of_ne_of_ne (Ne.symm hg.2.2.1) (Ne.symm hh.2.2.1)] at this
      exact he.2.2 this
    · exact swap_mul_swap_comm (Ne.symm he.2.2) (Ne.symm hh.2.2.2.2) (Ne.symm hg.2.2.1)
        (Ne.symm hh.2.2.1) (Ne.symm hg.2.2.2) (Ne.symm hh.2.2.2.1)
  ·
    intro x hx y hy hxy hc
    obtain ⟨c, e, hce, hca, hcb, hea, heb, rfl⟩ := hstar' x hx
    obtain ⟨g, h, hgh, hga, hgb, hha, hhb, rfl⟩ := hstar' y hy
    obtain ⟨h1, h2, h3, h4⟩ := swap_disjoint_of_commute hce hgh hc hxy
    obtain ⟨k, hka, hkb, hkc, hke, hkg, hkh⟩ := exists_ne_six hm a b c e g h
    refine ⟨swap c k, hstar (Ne.symm hkc) hca hcb hka hkb,
      swap_mul_swap_comm (Ne.symm hkc) hgh h1 h2 hkg hkh, ?_⟩
    exact fun h' => swap_mul_swap_ne hce (Ne.symm hkc) (Ne.symm hke) h'.symm

theorem triResult_sym {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : ∃ a b : commutator G, a * b ≠ b * a) {t : G} (ht : t ∈ D) (htG : t ∉ commutator G)
    (h : ∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧ ∃ φ : G ≃* Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap) :
    TriResult G t := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have hD : ∀ σ, σ ∈ φ '' D ↔ σ.IsSwap := fun σ => by
    refine ⟨?_, fun hσ => ⟨φ.symm σ, (hφ _).2 (by rwa [MulEquiv.apply_symm_apply]),
      MulEquiv.apply_symm_apply _ _⟩⟩
    rintro ⟨g, hg, rfl⟩
    exact (hφ g).1 hg
  rcases hm with rfl | hm5
  · exfalso
    obtain ⟨a, b, hab⟩ := nonabelian_map φ hna
    have hA := alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp)
    have ha := alternatingGroup.commutator_perm_le a.2
    have hb := alternatingGroup.commutator_perm_le b.2
    have hc := hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact hab (Subtype.ext (by simpa using congrArg Subtype.val hc))
  have hcomm : commutator (Perm (Fin m)) = alternatingGroup (Fin m) :=
    alternatingGroup.commutator_perm_eq (by simpa using hm5)
  rcases (show m = 5 ∨ m = 6 ∨ 7 ≤ m by omega) with rfl | rfl | hm7
  · right; left
    rw [Nat.card_congr (commutatorEquiv φ).toEquiv, hcomm, nat_card_alternatingGroup,
      Nat.card_fin]
    rfl
  · exact Or.inr (Or.inr ⟨(commutatorEquiv φ).trans (MulEquiv.subgroupCongr hcomm)⟩)
  · left
    refine TriGood.of_mulEquiv φ (triGood_perm hm7 (hyp_map hH φ) (nonabelian_map φ hna) hD
      ⟨t, ht, rfl⟩ ?_)
    rwa [apply_mem_commutator_iff]

end CFSG.LargeExtraspecial.S12Tri
