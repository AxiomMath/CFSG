module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three
public import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Invol

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

theorem index_ker_le_of_not_sq_dvd {p : ℕ} (hp : p.Prime) {H A : Type*} [Group H] [Group A]
    [Finite A] (hH : IsPGroup p H) (f : H →* A) (hA : ¬ p ^ 2 ∣ Nat.card A) :
    f.ker.index ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (G := f.range)).1
    (hH.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hk' : p ^ k ∣ Nat.card A := hk ▸ Subgroup.card_subgroup_dvd_card f.range
  have hk1 : k ≤ 1 := by
    by_contra h
    exact hA ((pow_dvd_pow p (by omega : 2 ≤ k)).trans hk')
  rw [Subgroup.index_ker, hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem alt6_exists_conj_of_pow
    (α : MulAut (alternatingGroup (Fin 6))) {k : ℕ} (hα : α ^ 3 ^ k = 1) :
    ∃ g : alternatingGroup (Fin 6), α = MulAut.conj g := by
  set R : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range with hR
  have : R.Normal := ⟨by
    rintro _ ⟨g, rfl⟩ φ
    refine ⟨φ g, ?_⟩
    ext x
    simp [MulAut.conj_apply, map_mul]⟩
  obtain ⟨e'⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6
    (K := alternatingGroup (Fin 6)) ⟨MulEquiv.refl _⟩
  have hcard : Nat.card (MulAut (alternatingGroup (Fin 6))) = 1440 :=
    CFSG.GH74.KGroups.A6.card_mulAut e'
  have hRcard : Nat.card R = 360 := by
    have h1 : Nat.card R = Nat.card (alternatingGroup (Fin 6)) :=
      Nat.card_congr (MonoidHom.ofInjective
        CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective).symm.toEquiv
    rw [h1, Nat.card_eq_fintype_card]
    decide +kernel
  have hidx : R.index = 4 := by
    have := Subgroup.card_mul_index R
    rw [hcard, hRcard] at this
    omega
  have h4 : α ^ 4 ∈ R := hidx ▸ Subgroup.pow_index_mem R α
  have hcop : IsCoprime ((4 : ℕ) : ℤ) ((3 ^ k : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : ((4 : ℕ) : ℤ) * a + ((3 ^ k : ℕ) : ℤ) * b = 1 := by linarith [hab]
  have hαR : α ∈ R := by
    have : α = (α ^ 4) ^ a := by
      calc α = α ^ (1 : ℤ) := (zpow_one α).symm
        _ = α ^ (((4 : ℕ) : ℤ) * a + ((3 ^ k : ℕ) : ℤ) * b) := by rw [hab']
        _ = (α ^ 4) ^ a := by
          rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hα]
          simp
    rw [this]
    exact zpow_mem h4 a
  obtain ⟨g, hg⟩ := hαR
  exact ⟨g, hg.symm⟩

theorem alt6_orderOf_eq_three (g : alternatingGroup (Fin 6)) (hg : g ≠ 1) {k : ℕ}
    (hk : g ^ 3 ^ k = 1) : orderOf g = 3 := by
  obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hg (orderOf_eq_one_iff.1 (by simpa using hjo))
  by_contra hne
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · exact absurd (by rw [hjo]; have : j = 1 := by omega
                       subst this; norm_num) hne
    · exact h
  set x : alternatingGroup (Fin 6) := g ^ 3 ^ (j - 1) with hx
  have h3dvd : 3 ^ (j - 1) ∣ orderOf g := hjo ▸ pow_dvd_pow 3 (Nat.sub_le j 1)
  have hxo : orderOf x = 3 := by
    rw [hx, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) h3dvd, hjo]
    have : 3 ^ j = 3 ^ (j - 1) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [this, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hgc : g ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh, hx]
    exact (Commute.pow_left (Commute.refl g) _).eq
  have h3 : g ^ 3 = 1 := pow_three_of_mem_centralizer hxo g hgc
  have : 3 ^ j ∣ 3 := hjo ▸ orderOf_dvd_of_pow_eq_one h3
  have := Nat.le_of_dvd (by norm_num) this
  have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
  omega

theorem card_mulAut_eq_of_equiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (MulAut H) = Nat.card (MulAut K) :=
  Nat.card_congr
    { toFun := fun σ => (e.symm.trans σ).trans e
      invFun := fun τ => (e.trans τ).trans e.symm
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp }

end CFSG.HardMathSupport.RichardWeiss.Coordinator
