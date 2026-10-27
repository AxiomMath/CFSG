module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

namespace BlockData

variable {X : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem apply_mem_commV_of_conjAut_eq (hI : BlockData X I) {g : MulAut W} (hgX : g ∈ X)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) (hgL : B1.conjAut g L = L) :
    ∀ v ∈ commV L, g v ∈ commV L := by
  intro v hv
  have h := (hI.perm g hgX L hL).2
  rw [hgL] at h
  rw [← h]
  exact Subgroup.mem_map_of_mem _ hv

private theorem mem_stabSub_commV (hI : BlockData X I) {g : MulAut W} (hgX : g ∈ X)
    {L : Subgroup (MulAut W)} (hL : L ∈ I) (hgL : B1.conjAut g L = L) :
    g ∈ stabSub (commV L) := by
  have hgL' : B1.conjAut g⁻¹ L = L := by
    have := B1.conjAut_inv_conjAut g L
    rwa [hgL] at this
  exact S1417.mem_stabSub_of_forall (hI.apply_mem_commV_of_conjAut_eq hgX hL hgL)
    (hI.apply_mem_commV_of_conjAut_eq (X.inv_mem hgX) hL hgL')

private theorem sl2_center : ∀ a : S1417.SL2, (∀ b : S1417.SL2, a * b = b * a) → a = 1 := by
  decide

private theorem eq_one_of_central {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) {l : MulAut W} (hl : l ∈ L) (h : ∀ l' ∈ L, l * l' = l' * l) :
    l = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : e ⟨l, hl⟩ = 1 := by
    refine sl2_center _ fun b => ?_
    obtain ⟨x, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (h x x.2))
  have h2 : (⟨l, hl⟩ : L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

private theorem conjAut_eq_of_commute {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ l ∈ L, g * l = l * g) : B1.conjAut g L = L := by
  have key : ∀ y ∈ L, g⁻¹ * y * g = y := fun y hy => by
    rw [mul_assoc, ← hg y hy, inv_mul_cancel_left]
  ext x
  rw [B1.mem_conjAut]
  refine ⟨fun h => ?_, fun h => by rwa [key x h]⟩
  have h2 := key _ h
  have h3 : g⁻¹ * x * g = x :=
    calc g⁻¹ * x * g = g * (g⁻¹ * (g⁻¹ * x * g) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by rw [h2]
      _ = x := by group
  rwa [h3] at h

theorem apply_eq_of_commute (hI : BlockData X I) {L : Subgroup (MulAut W)} (hL : L ∈ I)
    {g : MulAut W} (hgX : g ∈ X) (hg : ∀ l ∈ L, g * l = l * g) : ∀ v ∈ commV L, g v = v := by
  have hnat := hI.natural L hL
  have hst : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => commV_stable L hl hu
  obtain ⟨l, hlL, hl⟩ := S1417.exists_apply_eq_of_stab hnat hst
    (hI.mem_stabSub_commV hgX hL (conjAut_eq_of_commute hg))
  have hl1 : l = 1 := by
    refine eq_one_of_central hnat hlL fun l' hl' => ?_
    have hmem : (l' * l)⁻¹ * (l * l') ∈ L :=
      L.mul_mem (L.inv_mem (L.mul_mem hl' hlL)) (L.mul_mem hlL hl')
    have h1 := S1417.eq_one_of_forall_apply_eq hnat hst hmem (fun u hu => ?_)
    · exact (inv_mul_eq_one.mp h1).symm
    · have h2 : (l * l') u = (l' * l) u := by
        rw [MulAut.mul_apply, MulAut.mul_apply, hl _ (hst l' hl' u hu), hl u hu]
        have := congrArg (fun f : MulAut W => f u) (hg l' hl')
        simpa using this
      rw [MulAut.mul_apply, h2]
      simp
  intro v hv
  rw [← hl v hv, hl1]
  rfl

private theorem mul_eq_inv_mul {L : Subgroup (MulAut W)} {U : Subgroup W}
    (hN : ActsAsNaturalL2 L U) {t g : MulAut W} (ht : t ∈ L) (hg : g ∈ L) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) : t * g = g⁻¹ * t :=
  mul_inv_eq_iff_eq_mul.mp (S1417.conj_inv hN ht ht2 ht1 hg hg3 hg1)

theorem exists_delta (hI : BlockData X I) (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL : L ∈ I) {t g : MulAut W} (ht : t ∈ L) (hg : g ∈ L) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ c : W, ∀ a : W, t a = a → (g a = a ∨ g a * a⁻¹ = c) := by
  have hnat := hI.natural L hL
  have hst : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => commV_stable L hl hu
  have htg : t * g = g⁻¹ * t := mul_eq_inv_mul hnat ht hg ht2 ht1 hg3 hg1
  have hs2 : (g * t) ^ 2 = 1 :=
    calc (g * t) ^ 2 = g * (t * g) * t := by rw [pow_two]; simp only [mul_assoc]
      _ = t ^ 2 := by rw [htg, pow_two]; group
      _ = 1 := ht2
  have hs1 : g * t ≠ 1 := by
    intro h
    apply hg1
    have h2 : g ^ 2 = 1 := by
      have : t = g⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this, inv_pow, inv_eq_one] at ht2
      exact ht2
    calc g = g ^ 3 * (g ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg3, h2]; simp
  obtain ⟨c, -, -, hc⟩ := S1417.exists_fixed_vector hnat hst (L.mul_mem hg ht) hs2 hs1
  refine ⟨c, fun a hta => ?_⟩
  by_cases hga : g a = a
  · exact Or.inl hga
  right
  have hd : g a * a⁻¹ ∈ commV L := Subgroup.subset_closure ⟨g, hg, a, rfl⟩
  have hinv : ∀ w : W, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hW w)
  have hfix : (g * t) (g a * a⁻¹) = g a * a⁻¹ := by
    have h1 : t (g a) = g⁻¹ a := by
      have := congrArg (fun f : MulAut W => f a) htg
      simpa [hta] using this
    rw [MulAut.mul_apply, map_mul, map_inv, h1, hta, map_mul, map_inv, MulAut.apply_inv_self,
      hinv (g a), hinv a, mul_comm]
  rcases (hc _ hd).mp hfix with h | h
  · exact absurd (mul_inv_eq_one.mp h) hga
  · exact h

theorem exists_fixed_vector (hI : BlockData X I) {L : Subgroup (MulAut W)} (hL : L ∈ I)
    {t g : MulAut W} (ht : t ∈ L) (hg : g ∈ L) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    ∃ e ∈ commV L, e ≠ 1 ∧ t e = e ∧ g e ≠ e := by
  have hnat := hI.natural L hL
  have hst : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => commV_stable L hl hu
  obtain ⟨a, haU, ha1, ha⟩ := S1417.exists_fixed_vector hnat hst ht ht2 ht1
  refine ⟨a, haU, ha1, (ha a haU).mpr (Or.inr rfl), fun hga => hg1 ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact S1417.eq_one_of_odd_of_fixed hnat hst hg (by rw [orderOf_eq_prime hg3 hg1]; decide) haU
    ha1 hga

private theorem sl2_gen : ∀ s x y : S1417.SL2, s ^ 2 = 1 → s ≠ 1 → x ^ 3 = 1 → x ≠ 1 →
    ∃ i : Fin 3, ∃ j : Fin 2, y = x ^ (i : ℕ) * s ^ (j : ℕ) := by
  decide +kernel

private theorem pow_apply_eq_of_apply_eq {h : MulAut W} {a : W} (ha : h a = a) (n : ℕ) :
    (h ^ n) a = a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, ha, ih]

theorem apply_eq_of_apply_eq_gen (hI : BlockData X I) {L : Subgroup (MulAut W)} (hL : L ∈ I)
    {t g : MulAut W} (ht : t ∈ L) (hg : g ∈ L) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {a : W} (hta : t a = a) (hga : g a = a) :
    ∀ l ∈ L, l a = a := by
  obtain ⟨e, -, -⟩ := hI.natural L hL
  have hs2 : (e ⟨t, ht⟩) ^ 2 = 1 := by
    rw [← map_pow, show (⟨t, ht⟩ : L) ^ 2 = 1 from Subtype.ext ht2, map_one]
  have hs1 : e ⟨t, ht⟩ ≠ 1 := fun h =>
    ht1 (congrArg Subtype.val (e.injective (by rw [h, map_one]) : (⟨t, ht⟩ : L) = 1))
  have hx3 : (e ⟨g, hg⟩) ^ 3 = 1 := by
    rw [← map_pow, show (⟨g, hg⟩ : L) ^ 3 = 1 from Subtype.ext hg3, map_one]
  have hx1 : e ⟨g, hg⟩ ≠ 1 := fun h =>
    hg1 (congrArg Subtype.val (e.injective (by rw [h, map_one]) : (⟨g, hg⟩ : L) = 1))
  intro l hl
  obtain ⟨i, j, hij⟩ := sl2_gen _ _ (e ⟨l, hl⟩) hs2 hs1 hx3 hx1
  have hl' : (⟨l, hl⟩ : L) = ⟨g, hg⟩ ^ (i : ℕ) * ⟨t, ht⟩ ^ (j : ℕ) :=
    e.injective (by rw [hij, map_mul, map_pow, map_pow])
  have hl'' : l = g ^ (i : ℕ) * t ^ (j : ℕ) := congrArg Subtype.val hl'
  rw [hl'', MulAut.mul_apply, pow_apply_eq_of_apply_eq hta, pow_apply_eq_of_apply_eq hga]

private theorem conjAut_cube {g : MulAut W} (hg3 : g ^ 3 = 1) (L : Subgroup (MulAut W)) :
    B1.conjAut g (B1.conjAut g (B1.conjAut g L)) = L := by
  have h : g * g * g = 1 := by rw [← pow_three']; exact hg3
  ext x
  simp only [B1.mem_conjAut]
  have e : g⁻¹ * (g⁻¹ * (g⁻¹ * x * g) * g) * g = (g * g * g)⁻¹ * x * (g * g * g) := by group
  rw [e, h, inv_one, one_mul, mul_one]

theorem conjAut_eq_of_card_le_two (hI : BlockData X I) (hcard : I.card ≤ 2) {g : MulAut W}
    (hgX : g ∈ X) (hg3 : g ^ 3 = 1) : ∀ L ∈ I, B1.conjAut g L = L := by
  classical
  intro L hL
  by_contra hne
  have hL' : B1.conjAut g L ∈ I := (hI.perm g hgX L hL).1
  have hI2 : ({L, B1.conjAut g L} : Finset (Subgroup (MulAut W))) = I := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hL
      · rw [Finset.mem_singleton.mp hx]
        exact hL'
    · rw [Finset.card_pair (Ne.symm hne)]
      exact hcard
  have hL'' : B1.conjAut g (B1.conjAut g L) ∈ I := (hI.perm g hgX _ hL').1
  rw [← hI2, Finset.mem_insert, Finset.mem_singleton] at hL''
  have h3 := conjAut_cube hg3 L
  rcases hL'' with h | h
  · rw [h] at h3
    exact hne h3
  · rw [h, h] at h3
    exact hne h3

end BlockData

end CFSG.LocalAnalysis.RankThreeUC
