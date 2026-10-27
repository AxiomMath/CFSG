module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetFacts

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open Equiv Equiv.Perm

theorem nonempty_a11TwoSetStab_mulEquiv {i j : Fin 11} (hij : i ≠ j) :
    Nonempty (↥(a11TwoSetStab i j) ≃* Equiv.Perm (Fin 9)) := by
  classical
  let Ω : Finset (Fin 11) := (Finset.univ.erase i).erase j
  have hΩmem : ∀ k, k ∈ Ω ↔ k ≠ i ∧ k ≠ j := by
    intro k
    simp [Ω, Finset.mem_erase, and_assoc, and_comm, and_left_comm]
  have hΩcard : Ω.card = 9 := by
    change ((Finset.univ.erase i).erase j).card = 9
    rw [Finset.card_erase_of_mem
        (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin]
  have hcard : Fintype.card Ω = 9 := by
    rw [Fintype.card_coe, hΩcard]
  let fperm : ↥(a11TwoSetStab i j) → Equiv.Perm Ω := fun σ =>
    (σ : Equiv.Perm (Fin 11)).subtypePerm (p := fun k => k ∈ Ω) (by
      intro k
      constructor
      · intro hk
        obtain ⟨hki, hkj⟩ := (hΩmem ((σ : Equiv.Perm (Fin 11)) k)).mp hk
        refine (hΩmem k).mpr ⟨?_, ?_⟩
        · intro h
          subst h
          rcases σ.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hki h1
          · exact hkj h1
        · intro h
          subst h
          rcases σ.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact hkj h2
          · exact hki h2
      · intro hk
        obtain ⟨hki, hkj⟩ := (hΩmem k).mp hk
        refine (hΩmem ((σ : Equiv.Perm (Fin 11)) k)).mpr ⟨?_, ?_⟩
        · intro h1
          rcases σ.2 with ⟨hsi, hsj⟩ | ⟨hsi, hsj⟩
          · exact hki ((σ : Equiv.Perm (Fin 11)).injective (h1.trans hsi.symm))
          · exact hkj ((σ : Equiv.Perm (Fin 11)).injective (h1.trans hsj.symm))
        · intro h2
          rcases σ.2 with ⟨hsi, hsj⟩ | ⟨hsi, hsj⟩
          · exact hkj ((σ : Equiv.Perm (Fin 11)).injective (h2.trans hsj.symm))
          · exact hki ((σ : Equiv.Perm (Fin 11)).injective (h2.trans hsi.symm)))
  let f : ↥(a11TwoSetStab i j) →* Equiv.Perm Ω :=
    { toFun := fperm
      map_one' := by
        ext k
        rfl
      map_mul' := by
        intro σ τ
        ext k
        rfl }
  have hfcoe : ∀ (σ : ↥(a11TwoSetStab i j)) (k : Ω),
      (((f σ : Equiv.Perm Ω) k : Ω) : Fin 11) = (σ : Equiv.Perm (Fin 11)) k := by
    intro σ k
    rfl
  have hfinj : Function.Injective f := by
    intro σ τ h
    have hfix : ∀ a, a ∈ Ω →
        (((σ : Equiv.Perm (Fin 11))⁻¹ * (τ : Equiv.Perm (Fin 11))) a = a) := by
      intro a ha
      have hval : (σ : Equiv.Perm (Fin 11)) a = (τ : Equiv.Perm (Fin 11)) a := by
        have hk := congrArg (fun p : Equiv.Perm Ω => (((p ⟨a, ha⟩ : Ω) : Fin 11))) h
        rw [hfcoe σ ⟨a, ha⟩, hfcoe τ ⟨a, ha⟩] at hk
        exact hk
      rw [Equiv.Perm.mul_apply, ← hval]
      exact Equiv.symm_apply_apply (σ : Equiv.Perm (Fin 11)) a
    rcases eq_one_or_eq_swap_of_fixes_omega hij hfix with h1 | h1
    · have h2 : (σ : Equiv.Perm (Fin 11)) = (τ : Equiv.Perm (Fin 11)) :=
        inv_mul_eq_one.mp h1
      exact Subtype.ext (Subtype.ext h2)
    · exfalso
      have hsign : Equiv.Perm.sign
          ((σ : Equiv.Perm (Fin 11))⁻¹ * (τ : Equiv.Perm (Fin 11))) = 1 := by
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
        have hsσ : Equiv.Perm.sign (σ : Equiv.Perm (Fin 11)) = 1 :=
          Equiv.Perm.mem_alternatingGroup.mp σ.1.2
        have hsτ : Equiv.Perm.sign (τ : Equiv.Perm (Fin 11)) = 1 :=
          Equiv.Perm.mem_alternatingGroup.mp τ.1.2
        rw [hsσ, hsτ]
        norm_num
      rw [h1, Equiv.Perm.sign_swap hij] at hsign
      norm_num at hsign
  have hfsurj : Function.Surjective f := by
    intro τ
    let e : Equiv.Perm (Fin 11) := Equiv.Perm.ofSubtype τ
    have hei : e i = i := Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [Ω])
    have hej : e j = j := Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simp [Ω])
    by_cases heven : e ∈ alternatingGroup (Fin 11)
    · let a : alternatingGroup (Fin 11) := ⟨e, heven⟩
      have haS : a ∈ a11TwoSetStab i j := by
        change ((a : Equiv.Perm (Fin 11)) i = i ∧
            (a : Equiv.Perm (Fin 11)) j = j) ∨ _
        exact Or.inl ⟨hei, hej⟩
      refine ⟨⟨a, haS⟩, ?_⟩
      apply Equiv.ext
      intro k
      apply Subtype.ext
      rw [hfcoe]
      dsimp only [a]
      exact Equiv.Perm.ofSubtype_apply_coe τ k
    · have hodd : Equiv.Perm.sign e = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign e) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) heven
        · exact h
      have heven' : e * Equiv.swap i j ∈ alternatingGroup (Fin 11) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hodd,
          Equiv.Perm.sign_swap hij]
        norm_num
      let a : alternatingGroup (Fin 11) := ⟨e * Equiv.swap i j, heven'⟩
      have hai : (a : Equiv.Perm (Fin 11)) i = j := by
        change (e * Equiv.swap i j) i = j
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hej]
      have haj : (a : Equiv.Perm (Fin 11)) j = i := by
        change (e * Equiv.swap i j) j = i
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, hei]
      have haS : a ∈ a11TwoSetStab i j := by
        change _ ∨ ((a : Equiv.Perm (Fin 11)) i = j ∧
          (a : Equiv.Perm (Fin 11)) j = i)
        exact Or.inr ⟨hai, haj⟩
      refine ⟨⟨a, haS⟩, ?_⟩
      apply Equiv.ext
      intro k
      apply Subtype.ext
      rw [hfcoe]
      dsimp only [a]
      change (e * Equiv.swap i j) (k : Fin 11) = (τ k : Fin 11)
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        ((hΩmem k).mp k.2).1 ((hΩmem k).mp k.2).2]
      exact Equiv.Perm.ofSubtype_apply_coe τ k
  let eΩ : Ω ≃ Fin 9 := Fintype.equivFinOfCardEq hcard
  exact ⟨(MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩).trans (Equiv.permCongrHom eΩ)⟩

private lemma normalizer_apply_mem_pair {i j : Fin 11} (hij : i ≠ j)
    {S : Subgroup (Equiv.Perm (Fin 11))}
    (hSapply : ∀ y ∈ S, (y i = i ∨ y i = j) ∧ (y j = i ∨ y j = j))
    (hS : (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ S)
    (hcomm : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j)
    {σ : Equiv.Perm (Fin 11)}
    (hσ : σ ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))))
    {x : Fin 11} (hx : x = i ∨ x = j) :
    σ x = i ∨ σ x = j := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨hxi, hxj⟩ := hnot
  have h4 : ({i, j, σ i, σ j} : Finset (Fin 11)).card ≤ 4 := Finset.card_le_four
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j, σ i, σ j} : Finset (Fin 11))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      omega)
  obtain ⟨q, -, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert p ({i, j, σ i, σ j} : Finset (Fin 11))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h5 : (insert p ({i, j, σ i, σ j} : Finset (Fin 11))).card ≤ 5 := by
        calc (insert p ({i, j, σ i, σ j} : Finset (Fin 11))).card ≤
              ({i, j, σ i, σ j} : Finset (Fin 11)).card + 1 := Finset.card_insert_le _ _
          _ ≤ 4 + 1 := by omega
          _ = 5 := rfl
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp hq
  obtain ⟨hpi, hpj, hpσi, hpσj⟩ := hp
  obtain ⟨hqp, hqi, hqj, hqσi, hqσj⟩ := hq
  have hpσx : p ≠ σ x := by
    rcases hx with rfl | rfl
    · exact hpσi
    · exact hpσj
  have hqσx : q ≠ σ x := by
    rcases hx with rfl | rfl
    · exact hqσi
    · exact hqσj
  obtain ⟨t, htC, htx, htp, htq, -⟩ :=
    a11TwoSetStab_exists_threeCycle_mem_commutator hij hxi hxj
      hpi hpj hqi hqj (Ne.symm hpσx) (Ne.symm hqσx) (Ne.symm hqp)
  have htS : (t : Equiv.Perm (Fin 11)) ∈ S :=
    hS (Subgroup.mem_map_of_mem (alternatingGroup (Fin 11)).subtype (hcomm htC))
  have hconj : σ⁻¹ * (t : Equiv.Perm (Fin 11)) * σ ∈ S := by
    have hσinv : σ⁻¹ ∈ Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11))) :=
      (Subgroup.normalizer (S : Set (Equiv.Perm (Fin 11)))).inv_mem hσ
    exact (Subgroup.mem_normalizer_iff.mp hσinv (t : Equiv.Perm (Fin 11))).mp htS
  have hxS : (σ⁻¹ * (t : Equiv.Perm (Fin 11)) * σ) x = i ∨
      (σ⁻¹ * (t : Equiv.Perm (Fin 11)) * σ) x = j := by
    rcases hx with rfl | rfl
    · exact (hSapply _ hconj).1
    · exact (hSapply _ hconj).2
  have hval : (σ⁻¹ * (t : Equiv.Perm (Fin 11)) * σ) x = σ⁻¹ p := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, htx]
  rw [hval] at hxS
  have hp_mem : p = σ i ∨ p = σ j := by
    rcases hxS with h | h
    · left
      have := congrArg σ h
      simpa using this
    · right
      have := congrArg σ h
      simpa using this
  rcases hp_mem with h | h
  · exact hpσi h
  · exact hpσj h

theorem normalizer_a11TwoSetStab_le {i j : Fin 11} (hij : i ≠ j) :
    Subgroup.normalizer (((a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype :
        Subgroup (Equiv.Perm (Fin 11))) : Set (Equiv.Perm (Fin 11))) ≤
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))) := by
  intro σ hσ
  let S : Subgroup (Equiv.Perm (Fin 11)) :=
    (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype
  have hSapply : ∀ y ∈ S, (y i = i ∨ y i = j) ∧ (y j = i ∨ y j = j) := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h1, Or.inl h2⟩
  have hcomm : ⁅a11TwoSetStab i j, a11TwoSetStab i j⁆ ≤ a11TwoSetStab i j := by
    simpa using Subgroup.commutator_le_sup (a11TwoSetStab i j) (a11TwoSetStab i j)
  have hσi : σ i = i ∨ σ i = j :=
    normalizer_apply_mem_pair hij hSapply
      (show (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ S from le_rfl)
      hcomm (by simpa [S] using hσ) (Or.inl rfl)
  have hσj : σ j = i ∨ σ j = j :=
    normalizer_apply_mem_pair hij hSapply
      (show (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ S from le_rfl)
      hcomm (by simpa [S] using hσ) (Or.inr rfl)
  have hpair : (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
    rcases hσi with hi | hi
    · left
      refine ⟨hi, ?_⟩
      rcases hσj with hj | hj
      · exact absurd (σ.injective (hi.trans hj.symm)) hij
      · exact hj
    · right
      refine ⟨hi, ?_⟩
      rcases hσj with hj | hj
      · exact hj
      · exact absurd (σ.injective (hi.trans hj.symm)) hij
  have hswap : σ * Equiv.swap i j * σ⁻¹ = Equiv.swap i j := by
    rw [← Equiv.swap_apply_apply]
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Equiv.swap_comm]
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc σ * Equiv.swap i j = (σ * Equiv.swap i j * σ⁻¹) * σ := by group
    _ = Equiv.swap i j * σ := by rw [hswap]

private noncomputable def foldPerm (i j : Fin 11) (σ : Equiv.Perm (Fin 11)) :
    Equiv.Perm (Fin 11) := by
  classical
  exact if σ ∈ alternatingGroup (Fin 11) then σ else σ * Equiv.swap i j

private lemma foldPerm_one (i j : Fin 11) : foldPerm i j 1 = 1 := by
  classical
  rw [foldPerm, if_pos (one_mem (alternatingGroup (Fin 11)))]

private lemma sign_eq_neg_one_of_not_even {σ : Equiv.Perm (Fin 11)}
    (h : σ ∉ alternatingGroup (Fin 11)) : Equiv.Perm.sign σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h1) h
  · exact h1

private lemma foldPerm_mem_alternatingGroup {i j : Fin 11} (hij : i ≠ j)
    (σ : Equiv.Perm (Fin 11)) :
    foldPerm i j σ ∈ alternatingGroup (Fin 11) := by
  classical
  by_cases h : σ ∈ alternatingGroup (Fin 11)
  · rw [foldPerm, if_pos h]
    exact h
  · rw [foldPerm, if_neg h, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      sign_eq_neg_one_of_not_even h, Equiv.Perm.sign_swap hij]
    norm_num

private lemma maps_twoSet_of_mem_centralizer_swap {i j : Fin 11} (hij : i ≠ j)
    {σ : Equiv.Perm (Fin 11)}
    (hσ : σ ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11)))) :
    (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i) := by
  have hcomm : σ * Equiv.swap i j = Equiv.swap i j * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp hσ
  have hconv : σ j = Equiv.swap i j (σ i) := by
    have h := congrArg (fun p : Equiv.Perm (Fin 11) => p i) hcomm
    simpa [Equiv.Perm.mul_apply] using h
  have hmem : σ i = i ∨ σ i = j := by
    by_contra hne
    push Not at hne
    rw [Equiv.swap_apply_of_ne_of_ne hne.1 hne.2] at hconv
    exact hij (σ.injective hconv).symm
  rcases hmem with h | h
  · left
    refine ⟨h, ?_⟩
    rw [hconv, h, Equiv.swap_apply_left]
  · right
    refine ⟨h, ?_⟩
    rw [hconv, h, Equiv.swap_apply_right]

private lemma foldPerm_apply_mem_pair {i j : Fin 11} (hij : i ≠ j)
    {σ : Equiv.Perm (Fin 11)}
    (hσ : σ ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11)))) :
    (foldPerm i j σ i = i ∧ foldPerm i j σ j = j) ∨
      (foldPerm i j σ i = j ∧ foldPerm i j σ j = i) := by
  classical
  have hpair := maps_twoSet_of_mem_centralizer_swap hij hσ
  by_cases h : σ ∈ alternatingGroup (Fin 11)
  · rw [foldPerm, if_pos h]
    exact hpair
  · rw [foldPerm, if_neg h]
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right
      refine ⟨?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, h2]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, h1]
    · left
      refine ⟨?_, ?_⟩
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, h2]
      · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, h1]

private lemma foldPerm_mul {i j : Fin 11} (hij : i ≠ j)
    {σ τ : Equiv.Perm (Fin 11)}
    (hτ : τ ∈ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11)))) :
    foldPerm i j (σ * τ) = foldPerm i j σ * foldPerm i j τ := by
  classical
  by_cases hσe : σ ∈ alternatingGroup (Fin 11)
  · by_cases hτe : τ ∈ alternatingGroup (Fin 11)
    · have hστ : σ * τ ∈ alternatingGroup (Fin 11) :=
        (alternatingGroup (Fin 11)).mul_mem hσe hτe
      simp only [foldPerm]
      rw [if_pos hσe, if_pos hτe, if_pos hστ]
    · have hτo : Equiv.Perm.sign τ = -1 := sign_eq_neg_one_of_not_even hτe
      have hστ : σ * τ ∉ alternatingGroup (Fin 11) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
          Equiv.Perm.mem_alternatingGroup.mp hσe, hτo]
        norm_num
      simp only [foldPerm]
      rw [if_pos hσe, if_neg hτe, if_neg hστ]
      group
  · have hσo : Equiv.Perm.sign σ = -1 := sign_eq_neg_one_of_not_even hσe
    by_cases hτe : τ ∈ alternatingGroup (Fin 11)
    · have hστ : σ * τ ∉ alternatingGroup (Fin 11) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hσo,
          Equiv.Perm.mem_alternatingGroup.mp hτe]
        norm_num
      simp only [foldPerm]
      rw [if_neg hσe, if_pos hτe, if_neg hστ]
      have hsτ : Equiv.swap i j * τ = τ * Equiv.swap i j :=
        (Subgroup.mem_centralizer_singleton_iff.mp hτ).symm
      calc (σ * τ) * Equiv.swap i j = σ * (τ * Equiv.swap i j) := by group
        _ = σ * (Equiv.swap i j * τ) := by rw [hsτ.symm]
        _ = (σ * Equiv.swap i j) * τ := by group
    · have hτo : Equiv.Perm.sign τ = -1 := sign_eq_neg_one_of_not_even hτe
      have hστ : σ * τ ∈ alternatingGroup (Fin 11) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hσo, hτo]
        norm_num
      simp only [foldPerm]
      rw [if_neg hσe, if_neg hτe, if_pos hστ]
      have hsτ : Equiv.swap i j * τ = τ * Equiv.swap i j :=
        (Subgroup.mem_centralizer_singleton_iff.mp hτ).symm
      calc σ * τ = σ * τ * (Equiv.swap i j * Equiv.swap i j) := by
              rw [Equiv.swap_mul_self, mul_one]
        _ = σ * τ * Equiv.swap i j * Equiv.swap i j := by group
        _ = σ * (τ * Equiv.swap i j) * Equiv.swap i j := by group
        _ = σ * (Equiv.swap i j * τ) * Equiv.swap i j := by rw [hsτ.symm]
        _ = (σ * Equiv.swap i j) * (τ * Equiv.swap i j) := by group

private lemma foldPerm_eq_one_iff {i j : Fin 11} (hij : i ≠ j)
    {σ : Equiv.Perm (Fin 11)} :
    foldPerm i j σ = 1 ↔ σ = 1 ∨ σ = Equiv.swap i j := by
  classical
  have hσne : Equiv.swap i j ∉ alternatingGroup (Fin 11) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap hij]
    norm_num
  by_cases h : σ ∈ alternatingGroup (Fin 11)
  · rw [foldPerm, if_pos h]
    constructor
    · intro h1
      left
      exact h1
    · rintro (h1 | h1)
      · exact h1
      · exfalso
        rw [h1] at h
        exact hσne h
  · rw [foldPerm, if_neg h]
    constructor
    · intro h1
      right
      have h2 : σ * Equiv.swap i j * Equiv.swap i j = 1 * Equiv.swap i j := by rw [h1]
      simpa [mul_assoc, Equiv.swap_mul_self] using h2
    · rintro (h1 | h1)
      · exfalso
        rw [h1] at h
        exact h (one_mem (alternatingGroup (Fin 11)))
      · rw [h1, Equiv.swap_mul_self]

theorem exists_twoSetFold {Y : Type*} [Group Y] {i j : Fin 11} (hij : i ≠ j)
    (ψ : Y →* Equiv.Perm (Fin 11))
    (hle : ψ.range ≤ Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin 11))))
    (hge : (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype ≤ ψ.range) :
    ∃ φ : Y →* ↥(a11TwoSetStab i j), Function.Surjective φ ∧
      ∀ y, φ y = 1 ↔ (ψ y = 1 ∨ ψ y = Equiv.swap i j) := by
  classical
  let F : ↥ψ.range →* ↥(a11TwoSetStab i j) :=
    { toFun := fun g =>
        ⟨⟨foldPerm i j (g : Equiv.Perm (Fin 11)),
            foldPerm_mem_alternatingGroup hij (g : Equiv.Perm (Fin 11))⟩,
          foldPerm_apply_mem_pair hij (hle g.2)⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show foldPerm i j ((1 : ↥ψ.range) : Equiv.Perm (Fin 11)) = 1
        rw [Subgroup.coe_one, foldPerm_one]
      map_mul' := by
        intro g h
        apply Subtype.ext
        apply Subtype.ext
        show foldPerm i j ((g * h : ↥ψ.range) : Equiv.Perm (Fin 11)) =
          foldPerm i j (g : Equiv.Perm (Fin 11)) * foldPerm i j (h : Equiv.Perm (Fin 11))
        rw [Subgroup.coe_mul]
        exact foldPerm_mul hij (hle h.2) }
  let φ : Y →* ↥(a11TwoSetStab i j) := F.comp ψ.rangeRestrict
  refine ⟨φ, ?_, ?_⟩
  · intro σ
    have hσS : (σ : Equiv.Perm (Fin 11)) ∈
        (a11TwoSetStab i j).map (alternatingGroup (Fin 11)).subtype :=
      Subgroup.mem_map_of_mem (alternatingGroup (Fin 11)).subtype σ.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hge hσS)
    refine ⟨y, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show foldPerm i j (ψ y) = (σ : Equiv.Perm (Fin 11))
    rw [hy]
    rw [foldPerm, if_pos σ.1.2]
  · intro y
    have hiff : φ y = 1 ↔
        ((φ y : ↥(a11TwoSetStab i j)) : Equiv.Perm (Fin 11)) = 1 := by
      constructor
      · intro h
        exact congrArg (fun z : ↥(a11TwoSetStab i j) =>
          (z : Equiv.Perm (Fin 11))) h
      · intro h
        exact Subtype.ext (Subtype.ext h)
    rw [hiff]
    have hcoe : ((φ y : ↥(a11TwoSetStab i j)) : Equiv.Perm (Fin 11)) =
        foldPerm i j (ψ y) := rfl
    rw [hcoe]
    exact foldPerm_eq_one_iff hij

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
