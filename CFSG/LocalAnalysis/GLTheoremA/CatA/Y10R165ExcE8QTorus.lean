module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonE6Holds

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

open scoped Pointwise

variable {τ : Tag} {K L : Type} [Field K] [Field L]

theorem exists_elemAbelian_three_of_commute {G : Type} [Group G] {q : ℕ}
    [Fact q.Prime] {a b c : G} (ha : orderOf a = q) (hb : orderOf b = q) (hc : orderOf c = q)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (hind : ∀ m n k : ℕ, a ^ m * b ^ n * c ^ k = 1 → q ∣ m ∧ q ∣ n ∧ q ∣ k)
    {H : Subgroup G} (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H) :
    ∃ F : Subgroup G, F ≤ H ∧ IsElemAbelian q F ∧ Nat.card F = q ^ 3 := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact (1 < q) := ⟨hq.one_lt⟩
  have hqa : a ^ q = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hqb : b ^ q = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hqc : c ^ q = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  let φa : Multiplicative (ZMod q) →* G := orderPHom a hqa
  let φb : Multiplicative (ZMod q) →* G := orderPHom b hqb
  let φc : Multiplicative (ZMod q) →* G := orderPHom c hqc
  have hab' : ∀ x y : Multiplicative (ZMod q), Commute (φa x) (φb y) := fun x y =>
    (hab.pow_left _).pow_right _
  have hac' : ∀ x y : Multiplicative (ZMod q), Commute (φa x) (φc y) := fun x y =>
    (hac.pow_left _).pow_right _
  have hbc' : ∀ x y : Multiplicative (ZMod q), Commute (φb x) (φc y) := fun x y =>
    (hbc.pow_left _).pow_right _
  let φbc : Multiplicative (ZMod q) × Multiplicative (ZMod q) →* G :=
    MonoidHom.noncommCoprod φb φc hbc'
  let φ : Multiplicative (ZMod q) × Multiplicative (ZMod q) × Multiplicative (ZMod q) →* G :=
    MonoidHom.noncommCoprod φa φbc fun x y => (hab' x y.1).mul_right (hac' x y.2)
  have hφval : ∀ (m n k : Multiplicative (ZMod q)),
      φ (m, (n, k)) = a ^ (Multiplicative.toAdd m).val *
        (b ^ (Multiplicative.toAdd n).val * c ^ (Multiplicative.toAdd k).val) := by
    intro m n k
    change φa m * φbc (n, k) = _
    rw [show φbc (n, k) = φb n * φc k from MonoidHom.noncommCoprod_apply φb φc hbc' (n, k)]
    rfl
  have hφ : ∀ x, φ x = 1 → x = 1 := by
    rintro ⟨m, n, k⟩ h
    rw [hφval] at h
    have h' : a ^ (Multiplicative.toAdd m).val * b ^ (Multiplicative.toAdd n).val *
        c ^ (Multiplicative.toAdd k).val = 1 := by
      rw [mul_assoc]
      exact h
    obtain ⟨hm, hn, hk⟩ := hind _ _ _ h'
    have hm0 : (Multiplicative.toAdd m).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hm (ZMod.val_lt _)
    have hn0 : (Multiplicative.toAdd n).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hn (ZMod.val_lt _)
    have hk0 : (Multiplicative.toAdd k).val = 0 :=
      Nat.eq_zero_of_dvd_of_lt hk (ZMod.val_lt _)
    have hm' : Multiplicative.toAdd m = 0 := (ZMod.val_eq_zero _).1 hm0
    have hn' : Multiplicative.toAdd n = 0 := (ZMod.val_eq_zero _).1 hn0
    have hk' : Multiplicative.toAdd k = 0 := (ZMod.val_eq_zero _).1 hk0
    rw [show m = 1 from Multiplicative.toAdd.injective hm',
      show n = 1 from Multiplicative.toAdd.injective hn',
      show k = 1 from Multiplicative.toAdd.injective hk']
    rfl
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hφ _ h1
    rwa [mul_inv_eq_one] at h2
  let F : Subgroup G := Subgroup.closure ({a, b, c} : Set G)
  have hFle : F ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      refine ⟨(Multiplicative.ofAdd (1 : ZMod q), (1, 1)), ?_⟩
      rw [hφval]
      simp [ZMod.val_one q]
    · rw [hx]
      refine ⟨(1, (Multiplicative.ofAdd (1 : ZMod q), 1)), ?_⟩
      rw [hφval]
      simp [ZMod.val_one q]
    · rw [hx]
      refine ⟨(1, (1, Multiplicative.ofAdd (1 : ZMod q))), ?_⟩
      rw [hφval]
      simp [ZMod.val_one q]
  have hrangele : φ.range ≤ F := by
    rintro x ⟨⟨m, n, k⟩, rfl⟩
    rw [hφval]
    refine mul_mem ?_ (mul_mem ?_ ?_)
    · exact Subgroup.pow_mem F (Subgroup.subset_closure (by simp)) _
    · exact Subgroup.pow_mem F (Subgroup.subset_closure (by simp)) _
    · exact Subgroup.pow_mem F (Subgroup.subset_closure (by simp)) _
  have hFeq : F = φ.range := le_antisymm hFle hrangele
  have hFel : IsElemAbelian q F := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
      · rw [hx, hy]
      · rw [hx, hy]; exact hab.eq
      · rw [hx, hy]; exact hac.eq
      · rw [hx, hy]; exact hab.symm.eq
      · rw [hx, hy]
      · rw [hx, hy]; exact hbc.eq
      · rw [hx, hy]; exact hac.symm.eq
      · rw [hx, hy]; exact hbc.symm.eq
      · rw [hx, hy]
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · rw [hx]; exact hqa
      · rw [hx]; exact hqb
      · rw [hx]; exact hqc
  have hFcard : Nat.card F = q ^ 3 := by
    rw [hFeq, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    simp [Nat.card_prod, CFSG.LocalAnalysis.GLTheoremA.card_multiplicative_zmod]
    ring
  have hFH : F ≤ H := by
    rw [show F = Subgroup.closure ({a, b, c} : Set G) from rfl, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]; exact haH
    · rw [hx]; exact hbH
    · rw [hx]; exact hcH
  exact ⟨F, hFH, hFel, hFcard⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE8Three
