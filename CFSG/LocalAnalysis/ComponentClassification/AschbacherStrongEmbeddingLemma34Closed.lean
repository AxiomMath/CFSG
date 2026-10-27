module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34CaseTwoFinal

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem dihedralCase_symm {T : Subgroup G} (h : DihedralCase T A₂ A₁) :
    DihedralCase T A₁ A₂ := by
  obtain ⟨⟨a, ha, g, hT, hconj⟩, hd, hcard⟩ := h
  have hA₂ : rightConjugate A₁ (g⁻¹ * a * g)⁻¹ = A₂ := by
    rw [← hconj, rightConjugate_inv_cancel]
  have hb : (g⁻¹ * a * g)⁻¹ * a⁻¹ * (g⁻¹ * a * g) ∈ A₁ := by
    rw [← hconj, mem_rightConjugate_iff]
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using A₂.inv_mem ha
  refine ⟨⟨_, hb, (g⁻¹ * a * g)⁻¹ * g, ?_, ?_⟩, ?_, ?_⟩
  · rw [show ((g⁻¹ * a * g)⁻¹ * g)⁻¹ * ((g⁻¹ * a * g)⁻¹ * a⁻¹ * (g⁻¹ * a * g)) *
      ((g⁻¹ * a * g)⁻¹ * g) = (g⁻¹ * a * g)⁻¹ by group]
    exact T.inv_mem hT
  · rw [show ((g⁻¹ * a * g)⁻¹ * g)⁻¹ * ((g⁻¹ * a * g)⁻¹ * a⁻¹ * (g⁻¹ * a * g)) *
      ((g⁻¹ * a * g)⁻¹ * g) = (g⁻¹ * a * g)⁻¹ by group]
    exact hA₂
  · exact dihedral_of_mulEquiv ((rightConjugateEquiv A₂ _).trans (MulEquiv.subgroupCongr hconj))
      hd
  · rwa [inf_comm]

theorem exists_sylow_centralizer_conj {a : G} (g : G)
    (hP : ∃ P : Sylow 2 (Subgroup.centralizer ({a} : Set G)),
      (P : Subgroup _) = (S : Subgroup G).subgroupOf (Subgroup.centralizer ({a} : Set G))) :
    ∃ P : Sylow 2 (Subgroup.centralizer ({g⁻¹ * a * g} : Set G)),
      (P : Subgroup _) = (rightConjugate (S : Subgroup G) g).subgroupOf
        (Subgroup.centralizer ({g⁻¹ * a * g} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hP
  set C := Subgroup.centralizer ({a} : Set G)
  set C' := Subgroup.centralizer ({g⁻¹ * a * g} : Set G)
  have hC' : C' = rightConjugate C g := centralizer_conj_eq a g
  have hcard_sub : ∀ (A K : Subgroup G),
      Nat.card (A.subgroupOf K) = Nat.card (A ⊓ K : Subgroup G) := fun A K => by
      rw [← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype]
  have hcard : Nat.card ((rightConjugate (S : Subgroup G) g).subgroupOf C') =
      2 ^ (Nat.card C').factorization 2 := by
    rw [hcard_sub, hC', ← rightConjugate_inf_eq, rightConjugate_card, rightConjugate_card,
      ← hcard_sub, ← hP, Sylow.card_eq_multiplicity]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem Hyp.mem_of_conj_mem_sylow_one (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {a g : G} (ha : a ∈ A₁)
    (ha2 : orderOf a = 2)
    (hCa : Subgroup.centralizer ({a} : Set G) ≤ overlapClosure A₁ A₂)
    (hSyl : ∃ P : Sylow 2 (Subgroup.centralizer ({a} : Set G)),
      (P : Subgroup _) = (S : Subgroup G).subgroupOf (Subgroup.centralizer ({a} : Set G)))
    (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : g ∈ overlapClosure A₁ A₂ := by
  by_contra hg
  by_cases hI : A₁ ⊓ A₂ = ⊥
  · exact h.false_of_inf_eq_bot h12 h21 hI ha ha2 hCa hg hS
  have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha2).2
  have hc : EscapeChoice A₁ A₂ a (g⁻¹ * a * g) g :=
    ⟨hg, rfl, by rw [centralizer_conj_eq]; exact Subgroup.map_mono hCa⟩
  have hR := hc.rechoice (exists_sylow_centralizer_conj g hSyl)
  obtain ⟨z, hzI, hz1, hzz, hzt, hfix⟩ := h.escape_center h12 h21 hc ha ha1 hS hI
  exact (CaseTwo.false ⟨h, h12, h21, ha, ha2, hS, ⟨g, hc⟩, hR, hzI, hz1, hzz, hzt, hfix⟩ hD IH
    hH)

theorem Hyp.mem_of_conj_mem_sylow_involution (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂)
    (h21 : ¬ A₂ ≤ A₁) (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂)
    (ha2 : orderOf a = 2) (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) :
    g ∈ overlapClosure A₁ A₂ := by
  by_contra hg
  have ha1 : a ≠ 1 := (orderOf_eq_prime_iff.mp ha2).2
  have hD' : ¬ DihedralCase (S : Subgroup G) A₂ A₁ := fun hd => hD (dihedralCase_symm hd)
  obtain ⟨hs₁, hs₂⟩ := h.swap_of_conj h12 h21 ha ha1 hg hS
  have hiso : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ↔
      ¬ (IsDihedralTwoGroup A₂ ∨ IsSemidihedralTwoGroup A₂) := by
    have e : A₁ ≃* A₂ := (rightConjugateEquiv A₁ _).trans (MulEquiv.subgroupCongr hs₁)
    exact ⟨fun h1 h2 => h1 (dihedral_of_mulEquiv e.symm h2),
      fun h2 h1 => h2 (dihedral_of_mulEquiv e h1)⟩
  have hex : Nat.card (A₁ ⊓ A₂ : Subgroup G) ≠ 2 ∨
      (¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) ∧
        ¬ (IsDihedralTwoGroup A₂ ∨ IsSemidihedralTwoGroup A₂)) := by
    by_cases hI2 : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2
    · right
      have hnd : ¬ (IsDihedralTwoGroup A₁ ∨ IsSemidihedralTwoGroup A₁) := by
        intro hd
        rcases ha with ha₁ | ha₂
        · exact hD ⟨⟨a, ha₁, g, hS, hs₁⟩, hd, hI2⟩
        · exact hD' ⟨⟨a, ha₂, g, hS, hs₂⟩, not_not.mp (mt hiso.mpr (not_not.mpr hd)),
            by rwa [inf_comm]⟩
      exact ⟨hnd, hiso.mp hnd⟩
    · exact Or.inl hI2
  have hSH := h.sylow_le_overlapClosure h12 h21
  obtain ⟨X, hXU, hXS, hX4⟩ : ∃ X : Subgroup G, (X : Set G) ⊆ (A₁ : Set G) ∪ A₂ ∧
      X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G) ∧ 4 ≤ Nat.card X := by
    rcases ha with ha | ha
    · exact ⟨A₁ ⊓ Subgroup.centralizer ({a} : Set G), fun x hx => Or.inl hx.1,
        inf_le_inf_right _ h.le_one,
        four_le_card_inf_centralizer (S.isPGroup'.to_le h.le_one) h.rank_one ha ha2⟩
    · exact ⟨A₂ ⊓ Subgroup.centralizer ({a} : Set G), fun x hx => Or.inr hx.1,
        inf_le_inf_right _ h.le_two,
        four_le_card_inf_centralizer (S.isPGroup'.to_le h.le_two) h.rank_two ha ha2⟩
  obtain ⟨k, hk, hSyl, hconj⟩ :=
    h.exists_conj_sylow_inf hSH hXS (h.fixesOnly_of_card h12 h21 hXU hX4)
  have hbU := hconj a ha (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hb2 : orderOf (k⁻¹ * a * k) = 2 := by
    rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]; exact ha2
  have hCb := h.centralizer_le_of_involution h12 h21 IH hH hex hbU hb2
  have hgk : (k⁻¹ * g)⁻¹ * (k⁻¹ * a * k) * (k⁻¹ * g) = g⁻¹ * a * g := by group
  have hkg : k⁻¹ * g ∈ overlapClosure A₁ A₂ → g ∈ overlapClosure A₁ A₂ := fun hmem => by
    have := (overlapClosure A₁ A₂).mul_mem hk hmem
    rwa [mul_inv_cancel_left] at this
  rcases hbU with hb₁ | hb₂
  · exact hg (hkg (h.mem_of_conj_mem_sylow_one h12 h21 IH hH hD hb₁ hb2 hCb hSyl
      (by rw [hgk]; exact hS)))
  · rw [overlapClosure_comm] at hCb hH hg hkg
    exact hg (hkg (h.symm.mem_of_conj_mem_sylow_one h21 h12 IH hH hD' hb₂ hb2 hCb hSyl
      (by rw [hgk]; exact hS)))

theorem Hyp.mem_of_conj_mem_sylow (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂)
    (ha1 : a ≠ 1) (hS : g⁻¹ * a * g ∈ (S : Subgroup G)) : g ∈ overlapClosure A₁ A₂ := by
  have haS : a ∈ (S : Subgroup G) := by
    rcases ha with ha | ha
    · exact h.le_one ha
    · exact h.le_two ha
  obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one S.isPGroup' haS
  have hdvd : orderOf a ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hm1 : 1 ≤ m := by
    by_contra hcon
    have : m = 0 := by omega
    rw [this, pow_zero, orderOf_eq_one_iff] at hm
    exact ha1 hm
  have hdvd' : 2 ^ (m - 1) ∣ orderOf a := by
    rw [hm]; exact Nat.pow_dvd_pow 2 (by omega)
  have hb2 : orderOf (a ^ (2 ^ (m - 1))) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd', hm]
    have : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel hm1]
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hbU : a ^ (2 ^ (m - 1)) ∈ (A₁ : Set G) ∪ A₂ := by
    rcases ha with ha | ha
    · exact Or.inl (A₁.pow_mem ha _)
    · exact Or.inr (A₂.pow_mem ha _)
  refine h.mem_of_conj_mem_sylow_involution h12 h21 IH hH hD hbU hb2 ?_
  rw [← MulAut.conj_inv_apply, map_pow, MulAut.conj_inv_apply]
  exact Subgroup.pow_mem _ hS _

theorem Hyp.strongly_closed (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) :
    relStronglyClosed ⊤ ((A₁ : Set G) ∪ A₂) (S : Subgroup G) := by
  intro a ha g _ hS
  by_cases ha1 : a = 1
  · subst ha1
    rw [mul_one, inv_mul_cancel]
    exact Or.inl A₁.one_mem
  exact h.conj_mem_of_mem_overlapClosure ha
    (h.mem_of_conj_mem_sylow h12 h21 IH hH hD ha ha1 hS) hS

theorem Hyp.fixesOnly_of_mem_union (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {b : G} (hb : b ∈ (A₁ : Set G) ∪ A₂)
    (hb1 : b ≠ 1) : FixesOnly (overlapClosure A₁ A₂) (Subgroup.zpowers b) := by
  rw [fixesOnly_zpowers_iff]
  intro g hg
  have hSH := h.sylow_le_overlapClosure h12 h21
  have hbS : b ∈ (S : Subgroup G) := by
    rcases hb with hb | hb
    · exact h.le_one hb
    · exact h.le_two hb
  have hp : IsPGroup 2 (Subgroup.zpowers (g⁻¹ * b * g)) := by
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one S.isPGroup' hbS
    have hord : orderOf (g⁻¹ * b * g) = orderOf b := by
      rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hord, hk])
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_sylow hSH (Subgroup.zpowers_le.mpr hg) hp
  have hmem := h.mem_of_conj_mem_sylow h12 h21 IH hH hD hb hb1 (g := g * k)
    (by simpa only [mul_inv_rev, mul_assoc] using hkS _ (Subgroup.mem_zpowers _))
  have := (overlapClosure A₁ A₂).mul_mem hmem ((overlapClosure A₁ A₂).inv_mem hk)
  rwa [mul_inv_cancel_right] at this

theorem Hyp.centralizer_le_of_mem_union (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    (IH : Statement (Nat.card G - 1)) (hH : overlapClosure A₁ A₂ ≠ ⊤)
    (hD : ¬ DihedralCase (S : Subgroup G) A₁ A₂) {b : G} (hb : b ∈ (A₁ : Set G) ∪ A₂)
    (hb1 : b ≠ 1) : Subgroup.centralizer ({b} : Set G) ≤ overlapClosure A₁ A₂ := by
  have hf := fixesOnly_zpowers_iff.mp (h.fixesOnly_of_mem_union h12 h21 IH hH hD hb hb1)
  intro g hg
  apply hf
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  rw [mul_assoc, ← hg, inv_mul_cancel_left]
  exact h.mem_overlapClosure_of_mem_union hb

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
