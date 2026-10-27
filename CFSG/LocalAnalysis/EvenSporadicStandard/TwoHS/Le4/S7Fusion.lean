module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Sect6Abelian

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_zpowers_of_conj_mem_both {a x : G} (h1 : x * a * x⁻¹ ∈ zpowers a)
    (h2 : x⁻¹ * a * x ∈ zpowers a) : x ∈ normalizer (zpowers a : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hh
    have : x * a ^ k * x⁻¹ = (x * a * x⁻¹) ^ k := by rw [← conj_zpow]
    rw [this]
    exact zpow_mem h1 k
  · intro hh
    obtain ⟨m, hm⟩ := mem_zpowers_iff.1 hh
    have : h = (x⁻¹ * a * x) ^ m := by
      have e : (x⁻¹ * a * x) ^ m = x⁻¹ * a ^ m * x := by
        simpa using (conj_zpow (a := x⁻¹) (b := a) (i := m))
      rw [e, hm]; group
    rw [this]
    exact zpow_mem h2 m

omit [Finite G] in
theorem exists_mul_zpow_of_mem_sup {L : Subgroup G} {f : G} (hcom : ∀ l ∈ L, l * f = f * l) {x : G}
    (hx : x ∈ L ⊔ zpowers f) : ∃ l ∈ L, ∃ i : ℤ, x = l * f ^ i := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact ⟨1, L.one_mem, k, by simp⟩
  | one => exact ⟨1, L.one_mem, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl, i, rfl⟩ := hx
    obtain ⟨l', hl', j, rfl⟩ := hy
    refine ⟨l * l', L.mul_mem hl hl', i + j, ?_⟩
    have hc : Commute l' f := hcom l' hl'
    have h1 : f ^ i * l' = l' * f ^ i := (hc.zpow_right i).eq.symm
    calc l * f ^ i * (l' * f ^ j) = l * (f ^ i * l') * f ^ j := by group
      _ = l * (l' * f ^ i) * f ^ j := by rw [h1]
      _ = l * l' * (f ^ i * f ^ j) := by group
      _ = l * l' * f ^ (i + j) := by rw [zpow_add]
  | inv x _ hx =>
    obtain ⟨l, hl, i, rfl⟩ := hx
    refine ⟨l⁻¹, L.inv_mem hl, -i, ?_⟩
    have hc : Commute l⁻¹ f := hcom l⁻¹ (L.inv_mem hl)
    calc (l * f ^ i)⁻¹ = (f ^ i)⁻¹ * l⁻¹ := mul_inv_rev _ _
      _ = f ^ (-i) * l⁻¹ := by rw [zpow_neg]
      _ = l⁻¹ * f ^ (-i) := (hc.zpow_right (-i)).eq.symm


omit [Finite G] in
theorem sq_mem_of_mem_sup_zpowers {L : Subgroup G} {f : G} (hcom : ∀ l ∈ L, l * f = f * l)
    (hf2 : f ^ 2 ∈ L) {x : G} (hx : x ∈ L ⊔ zpowers f) : x ^ 2 ∈ L := by
  obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom hx
  have hc : Commute l f := hcom l hl
  have h1 : f ^ i * l = l * f ^ i := (hc.zpow_right i).eq.symm
  have hfi : f ^ (i + i) = (f ^ 2) ^ i := by
    rw [← two_mul, zpow_mul]; simp
  have : (l * f ^ i) ^ 2 = l ^ 2 * f ^ (i + i) := by
    calc (l * f ^ i) ^ 2 = (l * f ^ i) * (l * f ^ i) := sq _
      _ = l * (f ^ i * l) * f ^ i := by group
      _ = l * (l * f ^ i) * f ^ i := by rw [h1]
      _ = l * l * (f ^ i * f ^ i) := by group
      _ = l ^ 2 * f ^ (i + i) := by rw [sq, zpow_add]
  rw [this, hfi]
  exact L.mul_mem (L.pow_mem hl 2) (zpow_mem hf2 i)

theorem ne_conj_sq_of_mem_coset {L : Subgroup G} {f : G} (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f)
    (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L)
    (hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f) (hfL : f ∉ L) {l : G} (hl : l ∈ L)
    (g : G) : l * f ≠ g * f ^ 2 * g⁻¹ := by
  intro h
  set f' := g * f * g⁻¹ with hf'
  have hf'2 : f' ^ 2 = l * f := by rw [h, hf', conj_pow]
  have hconj : IsConj f f' := (isConj_iff.2 ⟨g, rfl⟩ : IsConj f f')
  have hf'4 : orderOf f' = 4 := orderOf_eq_four_of_isConj hf hconj
  have hN' : ∀ x : G, x * f' ^ 2 = f' ^ 2 * x → x * f' * x⁻¹ ∈ zpowers f' := by
    intro x hx
    have hx' : (g⁻¹ * x * g) * f ^ 2 = f ^ 2 * (g⁻¹ * x * g) := by
      have e : f' ^ 2 = g * f ^ 2 * g⁻¹ := by rw [hf', conj_pow]
      rw [e] at hx
      calc g⁻¹ * x * g * f ^ 2 = g⁻¹ * (x * (g * f ^ 2 * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * f ^ 2 * g⁻¹) * x) * g := by rw [hx]
        _ = f ^ 2 * (g⁻¹ * x * g) := by group
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hN _ hx')
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    calc f' ^ k = g * f ^ k * g⁻¹ := by rw [hf', conj_zpow]
      _ = g * ((g⁻¹ * x * g) * f * (g⁻¹ * x * g)⁻¹) * g⁻¹ := by rw [hk]
      _ = x * f' * x⁻¹ := by rw [hf']; group
  have hcomm : f * f'^2 = f'^2 * f := by
    rw [hf'2]
    calc f * (l * f) = (f * l) * f := by group
      _ = (l * f) * f := by rw [hcom l hl]
  have h1 : f * f' * f⁻¹ ∈ zpowers f' := hN' f hcomm
  have hc : Commute f (f' ^ 2) := hcomm
  have h2 : f⁻¹ * f' * f ∈ zpowers f' := by
    have := hN' f⁻¹ hc.inv_left.eq
    simpa using this
  have hfn : f ∈ normalizer (zpowers f' : Set G) := mem_normalizer_zpowers_of_conj_mem_both h1 h2
  have h2grp : ∀ a : G, orderOf a = 4 → IsPGroup 2 (zpowers a) := fun a ha =>
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, ha]; norm_num)
  have hP : IsPGroup 2 (zpowers f' ⊔ zpowers f : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (h2grp f' hf'4) (h2grp f hf) (zpowers_le.2 hfn)
  have hcc : f * f' = f' * f :=
    commute_of_isConj_of_centralizer_le hf hN hP (IsConj.refl f) hconj
      (Subgroup.mem_sup_right (mem_zpowers f)) (Subgroup.mem_sup_left (mem_zpowers f'))
  have hf'C : f' ∈ L ⊔ zpowers f := hC f' hcc.symm
  have hsq := sq_mem_of_mem_sup_zpowers hcom hf2 hf'C
  rw [hf'2] at hsq
  apply hfL
  have : f = l⁻¹ * (l * f) := by group
  rw [this]
  exact L.mul_mem (L.inv_mem hl) hsq

omit [Finite G] in
theorem mem_or_exists_of_mem_sup_zpowers {A : Subgroup G} {y : G} (hy : y * y = 1)
    (hA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) {x : G} (hx : x ∈ A ⊔ zpowers y) :
    x ∈ A ∨ ∃ a ∈ A, x = a * y := by
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h2 : y ^ 2 = 1 := by rw [sq]; exact hy
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left
        have : y ^ (m + m) = 1 := by rw [← two_mul, zpow_mul]; simp [h2]
        rw [this]; exact A.one_mem
      · right
        refine ⟨1, A.one_mem, ?_⟩
        have : y ^ (2 * m + 1) = y := by rw [zpow_add, zpow_mul]; simp [h2]
        rw [this]; group
  | one => exact Or.inl A.one_mem
  | mul x z _ _ hx hz =>
    rcases hx with hx | ⟨a, ha, rfl⟩
    · rcases hz with hz | ⟨b, hb, rfl⟩
      · exact Or.inl (A.mul_mem hx hz)
      · exact Or.inr ⟨x * b, A.mul_mem hx hb, by group⟩
    · rcases hz with hz | ⟨b, hb, rfl⟩
      · refine Or.inr ⟨a * (y * z * y⁻¹), A.mul_mem ha (hA z hz), ?_⟩
        group
      · left
        have : a * y * (b * y) = a * (y * b * y⁻¹) * (y * y) := by group
        rw [this, hy, mul_one]
        exact A.mul_mem ha (hA b hb)
  | inv x _ hx =>
    rcases hx with hx | ⟨a, ha, rfl⟩
    · exact Or.inl (A.inv_mem hx)
    · refine Or.inr ⟨y * a⁻¹ * y⁻¹, hA _ (A.inv_mem ha), ?_⟩
      calc (a * y)⁻¹ = y⁻¹ * a⁻¹ := mul_inv_rev _ _
        _ = y * a⁻¹ := by rw [hyinv]
        _ = (y * a⁻¹ * y⁻¹) * y := by group

omit [Finite G] in
theorem mem_sup_zpowers_of_commute_of_centralizer_eq {L : Subgroup G} {f y : G} (hf : orderOf f = 4)
    (hcom : ∀ l ∈ L, l * f = f * l) (hyy : y * y = 1) (hyf : y * f * y⁻¹ = f⁻¹)
    (hyL : y ∈ normalizer (L : Set G))
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) {x : G}
    (hx : x * f = f * x) : x ∈ L ⊔ zpowers f := by
  have hA : ∀ a ∈ L ⊔ zpowers f, y * a * y⁻¹ ∈ L ⊔ zpowers f := by
    intro a ha
    obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom ha
    have e : y * (l * f ^ i) * y⁻¹ = (y * l * y⁻¹) * (y * f * y⁻¹) ^ i := by
      rw [conj_zpow]; group
    rw [e, hyf]
    exact Subgroup.mul_mem_sup ((mem_normalizer_iff.1 hyL l).1 hl)
      (zpow_mem (inv_mem (mem_zpowers f)) i)
  have hxC : x ∈ centralizer ({f ^ 2} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have : Commute x f := hx
    exact (this.pow_right 2).eq.symm
  rw [hN] at hxC
  rcases mem_or_exists_of_mem_sup_zpowers hyy hA hxC with h | ⟨a, ha, rfl⟩
  · exact h
  · exfalso
    obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom ha
    have hc : Commute (l * f ^ i) f := by
      have : Commute l f := hcom l hl
      exact this.mul_left (Commute.zpow_left (Commute.refl f) i)
    have hyc : y * f = f * y := by
      have h1 : l * f ^ i * y * f = l * f ^ i * f * y := by
        calc l * f ^ i * y * f = f * (l * f ^ i * y) := hx
          _ = (f * (l * f ^ i)) * y := by group
          _ = ((l * f ^ i) * f) * y := by rw [hc.symm.eq]
          _ = l * f ^ i * f * y := by group
      have := mul_left_cancel (a := l * f ^ i) (by simpa [mul_assoc] using h1)
      exact this
    have : f = f⁻¹ := by
      calc f = y * f * y⁻¹ := by rw [hyc]; group
        _ = f⁻¹ := hyf
    have h2 : f ^ 2 = 1 := by
      calc f ^ 2 = f * f := sq f
        _ = f * f⁻¹ := by rw [← this]
        _ = 1 := by group
    have : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rw [hf] at this
    omega

theorem no_fusion_of_fy {L : Subgroup G} {f : G} {T U : Subgroup G} (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f)
    (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hfL : f ∉ L)
    (hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f) {y : G}
    (hfy : ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers y → w ∉ L ⊔ zpowers f →
      ∀ g : G, w ≠ g⁻¹ * f ^ 2 * g)
    (hU : ∀ w ∈ T, w * f ^ 2 = f ^ 2 * w → w ∉ U → w ∉ L ⊔ zpowers y) :
    ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∈ T → w ∉ U → ∀ g : G, w ≠ g⁻¹ * f ^ 2 * g := by
  intro w hw hwT hwU g
  have hwy := hU w hwT hw hwU
  by_cases hwA : w ∈ L ⊔ zpowers f
  · obtain ⟨l, hl, i, rfl⟩ := exists_mul_zpow_of_mem_sup hcom hwA
    rcases Int.even_or_odd i with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exfalso
      apply hwy
      have hfi : f ^ (m + m) = (f ^ 2) ^ m := by rw [← two_mul, zpow_mul]; simp
      rw [hfi]
      exact Subgroup.mem_sup_left (L.mul_mem hl (zpow_mem hf2 m))
    · have hfi : f ^ (2 * m + 1) = (f ^ 2) ^ m * f := by
        rw [zpow_add, zpow_mul]; simp
      have e : l * f ^ (2 * m + 1) = (l * (f ^ 2) ^ m) * f := by rw [hfi]; group
      rw [e]
      have := ne_conj_sq_of_mem_coset hf hN hcom hf2 hC hfL
        (l := l * (f ^ 2) ^ m) (L.mul_mem hl (zpow_mem hf2 m)) g⁻¹
      simpa using this
  · exact hfy w hw hwy hwA g

omit [Finite G] in
theorem sq_fusion_of_phase1 {F E : Subgroup G} {f s : G} (hf : orderOf f = 4)
    (hE_inv : ∀ x ∈ E, x * x = 1 → x ∈ F ∨ ∃ u ∈ F, x = f ^ 2 * u)
    (hF_conj : ∀ u ∈ F, u ≠ 1 → ∃ h : G, u = h * (s ^ 2 * f ^ 2) * h⁻¹)
    (hn : ¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) :
    ∀ g : G, g⁻¹ * f ^ 2 * g ∈ E → g⁻¹ * f ^ 2 * g ∈ {x : G | ∃ u ∈ F, x = f ^ 2 * u} := by
  intro g hgE
  have hf4 : f ^ 4 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hxx : (g⁻¹ * f ^ 2 * g) * (g⁻¹ * f ^ 2 * g) = 1 := by
    have : (g⁻¹ * f ^ 2 * g) * (g⁻¹ * f ^ 2 * g) = g⁻¹ * f ^ 4 * g := by
      rw [show f ^ 4 = f ^ 2 * f ^ 2 by rw [← pow_add]]; group
    rw [this, hf4]; group
  rcases hE_inv _ hgE hxx with hF | ⟨u, hu, hu'⟩
  · exfalso
    have hne : g⁻¹ * f ^ 2 * g ≠ 1 := by
      intro h1
      have h2 : f ^ 2 = 1 := by
        have : f ^ 2 = g * (g⁻¹ * f ^ 2 * g) * g⁻¹ := by group
        rw [this, h1]; group
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hf] at this
      omega
    obtain ⟨h, hh⟩ := hF_conj _ hF hne
    apply hn
    refine ⟨(g * h)⁻¹, ?_⟩
    calc s ^ 2 * f ^ 2 = h⁻¹ * (h * (s ^ 2 * f ^ 2) * h⁻¹) * h := by group
      _ = h⁻¹ * (g⁻¹ * f ^ 2 * g) * h := by rw [← hh]
      _ = (g * h)⁻¹ * f ^ 2 * (g * h)⁻¹⁻¹ := by group
  · exact ⟨u, hu, hu'⟩

end CFSG.EvenSporadicStandard.TwoHS
