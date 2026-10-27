module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Cfg
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75Lin
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Harada75F3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open CFSG.Open

section Aux

theorem normal_of_index_le_two {P : Type} [Group P] [Finite P] {C : Subgroup P}
    (hi : C.index ≤ 2) : C.Normal := by
  have hne : C.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  by_cases h1 : C.index = 1
  · rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.normal_top
  · exact Subgroup.normal_of_index_eq_two (by omega)

theorem card_centralizer_subtype {S : Type} [Group S] (P : Subgroup S) (t : S) (ht : t ∈ P) :
    Nat.card (Subgroup.centralizer ({(⟨t, ht⟩ : P)} : Set P)) =
      Nat.card (P ⊓ Subgroup.centralizer ({t} : Set S) : Subgroup S) := by
  have h : Subgroup.centralizer ({(⟨t, ht⟩ : P)} : Set P) =
      (P ⊓ Subgroup.centralizer ({t} : Set S) : Subgroup S).subgroupOf P := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · intro hy
      exact Subtype.ext hy.2
  rw [h]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

end Aux

section Cfg2Facts

variable {S : Type} [Group S] {E F : Subgroup S} {z : S}

theorem Cfg2.F_sq (h : Cfg2 S E F z) {f : S} (hf : f ∈ F) : f * f = 1 := by
  rw [← pow_two]
  exact h.hFa.2 f hf

theorem Cfg2.F_comm (h : Cfg2 S E F z) {f g : S} (hf : f ∈ F) (hg : g ∈ F) : f * g = g * f := by
  have := h.hFa.1.is_comm.comm ⟨f, hf⟩ ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem Cfg2.E_comm (h : Cfg2 S E F z) {e e' : S} (he : e ∈ E) (he' : e' ∈ E) :
    e * e' = e' * e := by
  have := h.hEa.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩
  exact congrArg Subtype.val this

theorem Cfg2.E_sq (h : Cfg2 S E F z) {e : S} (he : e ∈ E) : e * e = 1 := by
  rw [← pow_two]
  exact h.hEa.2 e he

theorem Cfg2.exists_second [Finite S] (h : Cfg2 S E F z) {f : S} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ f' ∈ F, f' ≠ 1 ∧ f' ≠ f ∧ ∀ g ∈ F, g = 1 ∨ g = f ∨ g = f' ∨ g = f * f' := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hsq : f * f = 1 := h.F_sq hf
  obtain ⟨f', hf'F, hf'1, hf'f⟩ : ∃ f' ∈ F, f' ≠ 1 ∧ f' ≠ f := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ g : F, g ∈ ({1, ⟨f, hf⟩} : Finset F) := by
      intro g
      have := hcon g.1 g.2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hg1 : g.1 = 1
      · left; exact Subtype.ext hg1
      · right; exact Subtype.ext (this hg1)
    have hcard : Nat.card F ≤ 2 := by
      have h1 : (Finset.univ : Finset F) ⊆ {1, ⟨f, hf⟩} := fun g _ => hsub g
      have h2 := Finset.card_le_card h1
      have h3 : ({1, ⟨f, hf⟩} : Finset F).card ≤ 2 := Finset.card_le_two
      rw [Nat.card_eq_fintype_card]
      simpa using h2.trans h3
    have := h.hF4
    omega
  refine ⟨f', hf'F, hf'1, hf'f, ?_⟩
  have hff'F : f * f' ∈ F := F.mul_mem hf hf'F
  have hd1 : f * f' ≠ 1 := by
    intro hh
    apply hf'f
    have : f' = f⁻¹ := eq_inv_of_mul_eq_one_right hh
    rw [this, inv_eq_of_mul_eq_one_right hsq]
  have hd2 : f ≠ f * f' := by
    intro hh
    have := mul_left_cancel (a := f) ((mul_one f).trans hh)
    exact hf'1 this.symm
  have hd3 : f' ≠ f * f' := by
    intro hh
    exact hf1 (mul_right_cancel (b := f') ((one_mul f').trans hh)).symm
  have hset : ({1, ⟨f, hf⟩, ⟨f', hf'F⟩, ⟨f * f', hff'F⟩} : Finset F).card = 4 := by
    have n1 : (1 : F) ≠ ⟨f, hf⟩ := fun hh => hf1 (congrArg Subtype.val hh).symm
    have n2 : (1 : F) ≠ ⟨f', hf'F⟩ := fun hh => hf'1 (congrArg Subtype.val hh).symm
    have n3 : (1 : F) ≠ ⟨f * f', hff'F⟩ := fun hh => hd1 (congrArg Subtype.val hh).symm
    have n4 : (⟨f, hf⟩ : F) ≠ ⟨f', hf'F⟩ := fun hh => hf'f (congrArg Subtype.val hh).symm
    have n5 : (⟨f, hf⟩ : F) ≠ ⟨f * f', hff'F⟩ := fun hh => hd2 (congrArg Subtype.val hh)
    have n6 : (⟨f', hf'F⟩ : F) ≠ ⟨f * f', hff'F⟩ := fun hh => hd3 (congrArg Subtype.val hh)
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair n6]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n4, n5⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨n1, n2, n3⟩
  have huniv : ({1, ⟨f, hf⟩, ⟨f', hf'F⟩, ⟨f * f', hff'F⟩} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hset, ← Nat.card_eq_fintype_card]
    exact h.hF4.symm
  intro g hg
  have hmem : (⟨g, hg⟩ : F) ∈ ({1, ⟨f, hf⟩, ⟨f', hf'F⟩, ⟨f * f', hff'F⟩} : Finset F) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hh | hh | hh | hh
  · exact Or.inl (congrArg Subtype.val hh)
  · exact Or.inr (Or.inl (congrArg Subtype.val hh))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val hh)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val hh)))

theorem Cfg2.card_fixE [Finite S] (h : Cfg2 S E F z) {f : S} (hf : f ∈ F) (hf1 : f ≠ 1) :
    Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) = 4 := by
  have := h.hEn
  have hsq := h.F_sq hf
  have hle := card_le_card_fix_sq E (fun x hx y hy => h.E_comm hx hy)
    (fun x hx => h.E_sq hx) f (fun y hy => h.hEn.conj_mem y hy f) (by
      intro y hy
      rw [hsq, one_mul, mul_one])
  have hdvd : Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) ∣ Nat.card E :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [h.hE8] at hle hdvd
  have hne8 : Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) ≠ 8 := by
    intro h8
    have heq : E ⊓ Subgroup.centralizer ({f} : Set S) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.hE8])
    apply hf1
    apply h.hFK f hf
    intro e he
    have : e ∈ E ⊓ Subgroup.centralizer ({f} : Set S) := by rw [heq]; exact he
    exact (Subgroup.mem_centralizer_singleton_iff.mp this.2).symm
  generalize Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) = c at hle hdvd hne8
  have hc : c ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [this] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp_all

theorem Cfg2.exists_x [Finite S] (h : Cfg2 S E F z) {f : S} (hf : f ∈ F) (hf1 : f ≠ 1) :
    ∃ x ∈ E, f * x = x * f ∧ x ≠ 1 ∧ x ≠ z := by
  by_contra hcon
  push Not at hcon
  have hsub : ((E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) : Set S) ⊆ {1, z} := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hxc : f * x = x * f := (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    by_cases hx1 : x = 1
    · left; exact hx1
    · right; exact hcon x hxE hxc hx1
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, z} : Set S).ncard ≤ 2 := by
    have := Set.ncard_insert_le (1 : S) ({z} : Set S)
    simpa [Set.ncard_singleton] using this
  have h3 := h.card_fixE hf hf1
  rw [← Nat.card_coe_set_eq] at h1
  have : Nat.card (E ⊓ Subgroup.centralizer ({f} : Set S) : Subgroup S) ≤ 2 := by
    exact (Nat.card_coe_set_eq _ ▸ h1).trans h2
  omega


theorem Cfg2.card_K_fix_le [Finite S] (hS : IsPGroup 2 S) (h : Cfg2 S E F z) {f : S} (hf : f ∈ F)
    (hf1 : f ≠ 1) :
    Nat.card (Subgroup.centralizer (E : Set S) ⊓ Subgroup.centralizer ({f} : Set S) :
      Subgroup S) ≤ 4 := by
  classical
  have := h.hEn
  obtain ⟨f', hf'F, hf'1, hf'f, hFall⟩ := h.exists_second hf hf1
  have hsq := h.F_sq hf
  have hsq' := h.F_sq hf'F
  have hff' : f * f' = f' * f := h.F_comm hf hf'F
  have hinv' : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right hsq'
  set K : Subgroup S := Subgroup.centralizer (E : Set S) with hK
  set D : Subgroup S := K ⊓ Subgroup.centralizer ({f} : Set S) with hD
  have hKmem : ∀ k : S, k ∈ K ↔ ∀ e ∈ E, e * k = k * e := by
    intro k
    rw [hK, Subgroup.mem_centralizer_iff]
    rfl
  have hDmem : ∀ k : S, k ∈ D ↔ (∀ e ∈ E, e * k = k * e) ∧ k * f = f * k := by
    intro k
    rw [hD, Subgroup.mem_inf, hKmem, Subgroup.mem_centralizer_singleton_iff]
  have hnormD : ∀ k ∈ D, f' * k * f'⁻¹ ∈ D := by
    intro k hk
    obtain ⟨hkK, hkf⟩ := (hDmem k).mp hk
    refine (hDmem _).mpr ⟨?_, ?_⟩
    · have : f' * k * f'⁻¹ ∈ K := (inferInstance : K.Normal).conj_mem k ((hKmem k).mpr hkK) f'
      exact (hKmem _).mp this
    · rw [hinv']
      calc f' * k * f' * f = f' * k * (f' * f) := by group
        _ = f' * k * (f * f') := by rw [hff']
        _ = f' * (k * f) * f' := by group
        _ = f' * (f * k) * f' := by rw [hkf]
        _ = (f' * f) * k * f' := by group
        _ = (f * f') * k * f' := by rw [hff']
        _ = f * (f' * k * f') := by group
  have hf'norm : f' ∈ Subgroup.normalizer (D : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hnormD k hk
    · intro hk
      have := hnormD _ hk
      have e : f' * (f' * k * f'⁻¹) * f'⁻¹ = k := by
        rw [hinv']
        calc f' * (f' * k * f') * f' = (f' * f') * k * (f' * f') := by group
          _ = k := by rw [hsq']; group
      rwa [e] at this
  set P : Subgroup S := D ⊔ Subgroup.zpowers f' with hP
  have hDP : D ≤ P := le_sup_left
  have hf'P : f' ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers f')
  have hPmem : ∀ p : S, p ∈ P → ∃ d ∈ D, p = d * f' ∨ p = d := by
    intro p hp
    have hLE : Subgroup.zpowers f' ≤ Subgroup.normalizer (D : Set S) :=
      (Subgroup.zpowers_le).mpr hf'norm
    have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left D (Subgroup.zpowers f') hLE
    have hp' : p ∈ (↑(D ⊔ Subgroup.zpowers f') : Set S) := hp
    rw [hcoe] at hp'
    obtain ⟨d, hd, y, hy, rfl⟩ := hp'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rcases zpow_eq_one_or_self f' hsq' n with h1 | h1
    · exact ⟨d, hd, Or.inr (by simp [h1])⟩
    · exact ⟨d, hd, Or.inl (by simp [h1])⟩
  have hcentP : Nat.card (P ⊓ Subgroup.centralizer ({f'} : Set S) : Subgroup S) ≤ 4 := by
    have hsub : ((P ⊓ Subgroup.centralizer ({f'} : Set S) : Subgroup S) : Set S) ⊆
        ((({1, z, f', z * f'} : Finset S)) : Set S) := by
      intro p hp
      obtain ⟨hpP, hpc⟩ := hp
      have hpc' : p * f' = f' * p := Subgroup.mem_centralizer_singleton_iff.mp hpc
      obtain ⟨d, hd, hpd⟩ := hPmem p hpP
      have hdc : d * f' = f' * d := by
        rcases hpd with rfl | rfl
        · have : d * f' * f' = f' * (d * f') := hpc'
          calc d * f' = d * f' * (f' * f') := by rw [hsq', mul_one]
            _ = (d * f' * f') * f' := by group
            _ = (f' * (d * f')) * f' := by rw [this]
            _ = f' * d * (f' * f') := by group
            _ = f' * d := by rw [hsq', mul_one]
        · exact hpc'
      obtain ⟨hdE, hdf⟩ := (hDmem d).mp hd
      have hdF : ∀ g ∈ F, d * g = g * d := by
        intro g hg
        rcases hFall g hg with rfl | rfl | rfl | rfl
        · rw [mul_one, one_mul]
        · exact hdf
        · exact hdc
        · calc d * (f * f') = (d * f) * f' := by group
            _ = (f * d) * f' := by rw [hdf]
            _ = f * (d * f') := by group
            _ = f * (f' * d) := by rw [hdc]
            _ = (f * f') * d := by group
      have hdz := h.hCK d (fun e he => (hdE e he).symm) hdF
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      rcases hpd with rfl | rfl <;> rcases hdz with rfl | rfl
      · right; right; left; rw [one_mul]
      · right; right; right; rfl
      · left; rfl
      · right; left; rfl
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h1
    have h2 : (({1, z, f', z * f'} : Finset S)).card ≤ 4 := Finset.card_le_four
    rw [← Nat.card_coe_set_eq] at h1
    exact (Nat.card_coe_set_eq _ ▸ h1).trans h2
  set t : P := ⟨f', hf'P⟩ with ht
  have ht2 : t ^ 2 = 1 := Subtype.ext (by
    show f' ^ 2 = 1
    rw [pow_two, hsq'])
  have ht1 : t ≠ 1 := fun hh => hf'1 (congrArg Subtype.val hh)
  have hCt : Nat.card (Subgroup.centralizer ({t} : Set P)) ≤ 4 := by
    rw [ht, card_centralizer_subtype P f' hf'P]
    exact hcentP
  obtain ⟨C, hCcyc, hCidx⟩ := exists_cyclic_index_le_two (hS.to_subgroup P) ht2 ht1 hCt
  have : C.Normal := normal_of_index_le_two hCidx
  by_cases htC : t ∈ C
  ·
    have hcen : t ∈ Subgroup.center P :=
      mem_center_of_involution_mem_cyclic_normal hCcyc htC ht2 ht1
    have hDle : D ≤ P ⊓ Subgroup.centralizer ({f'} : Set S) := by
      intro k hk
      refine ⟨hDP hk, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have := (Subgroup.mem_center_iff.mp hcen) ⟨k, hDP hk⟩
      exact congrArg Subtype.val this
    exact (Subgroup.card_le_of_le hDle).trans hcentP
  · obtain ⟨x, hxE, hxf, hx1, hxz⟩ := h.exists_x hf hf1
    have hxK : ∀ e ∈ E, e * x = x * e := fun e he => h.E_comm he hxE
    have hxD : x ∈ D := (hDmem x).mpr ⟨hxK, hxf.symm⟩
    have hxP : x ∈ P := hDP hxD
    set x' : P := ⟨x, hxP⟩ with hx'
    have hx'2 : x' ^ 2 = 1 := Subtype.ext (by
      show x ^ 2 = 1
      rw [pow_two, h.E_sq hxE])
    have hx'1 : x' ≠ 1 := fun hh => hx1 (congrArg Subtype.val hh)
    have hx'C : x' ∉ C := by
      intro hx'C
      have hcen : x' ∈ Subgroup.center P :=
        mem_center_of_involution_mem_cyclic_normal hCcyc hx'C hx'2 hx'1
      have hxf' : x * f' = f' * x := by
        have := (Subgroup.mem_center_iff.mp hcen) t
        exact (congrArg Subtype.val this).symm
      have hxF : ∀ g ∈ F, g * x = x * g := by
        intro g hg
        rcases hFall g hg with rfl | rfl | rfl | rfl
        · rw [one_mul, mul_one]
        · exact hxf
        · exact hxf'.symm
        · calc (f * f') * x = f * (f' * x) := by group
            _ = f * (x * f') := by rw [hxf']
            _ = (f * x) * f' := by group
            _ = (x * f) * f' := by rw [hxf]
            _ = x * (f * f') := by group
      rcases h.hCE x hxE hxF with hh | hh
      · exact hx1 hh
      · exact hxz hh
    have hle := card_centralizer_le_of_not_mem hCcyc hCidx htC hx'C
    have hDle : D ≤ P ⊓ Subgroup.centralizer ({x} : Set S) := by
      intro k hk
      refine ⟨hDP hk, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      obtain ⟨hkE, _⟩ := (hDmem k).mp hk
      exact (hkE x hxE).symm
    have hcard := card_centralizer_subtype P x hxP
    calc Nat.card D ≤ Nat.card (P ⊓ Subgroup.centralizer ({x} : Set S) : Subgroup S) :=
          Subgroup.card_le_of_le hDle
      _ = Nat.card (Subgroup.centralizer ({x'} : Set P)) := hcard.symm
      _ ≤ Nat.card (Subgroup.centralizer ({t} : Set P)) := hle
      _ ≤ 4 := hCt

end Cfg2Facts

end CFSG.EvenSporadicStandard.Fin76b
