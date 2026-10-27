module

public import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGAlt

open CFSG.Open CFSG.GH74.Uniqueness.SU Subgroup Equiv

theorem exists_elemAbelian_alt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 2 * p ≤ n) :
    ∃ E : Subgroup (alternatingGroup (Fin n)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Perm (Fin p)) p (by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.dvd_factorial hp.pos le_rfl)
  let e₁ : Fin p ↪ Fin n := ⟨fun i => ⟨i, by omega⟩, fun i j h => Fin.ext (by
    simpa using congrArg Fin.val h)⟩
  let e₂ : Fin p ↪ Fin n := ⟨fun i => ⟨p + i, by omega⟩, fun i j h => Fin.ext (by
    have := congrArg Fin.val h
    simp only at this
    omega)⟩
  have hcp : c ^ p = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc] at this
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    exact hp.one_lt.ne hc
  obtain ⟨i₀, hi₀⟩ : ∃ i, c i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hc1 (Equiv.ext hcon)
  set c₁ : Perm (Fin n) := c.viaFintypeEmbedding e₁ with hc₁
  set c₂ : Perm (Fin n) := c.viaFintypeEmbedding e₂ with hc₂
  have hhom₁ : ∀ g : Perm (Fin p),
      g.viaFintypeEmbedding e₁ = Perm.extendDomainHom e₁.toEquivRange g := fun g => rfl
  have hhom₂ : ∀ g : Perm (Fin p),
      g.viaFintypeEmbedding e₂ = Perm.extendDomainHom e₂.toEquivRange g := fun g => rfl
  have hc₁p : c₁ ^ p = 1 := by
    rw [hc₁, hhom₁, ← map_pow, hcp, map_one]
  have hc₂p : c₂ ^ p = 1 := by
    rw [hc₂, hhom₂, ← map_pow, hcp, map_one]
  have hsign : ∀ g : Perm (Fin p), g ^ p = 1 → Perm.sign g = 1 := by
    intro g hg
    have h1 : Perm.sign g ^ p = 1 := by rw [← map_pow, hg, map_one]
    have h2 : Perm.sign g ^ p = Perm.sign g ^ (p % 2) :=
      Int.units_pow_eq_pow_mod_two (Perm.sign g) p
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rw [h2, hodd, pow_one] at h1
    exact h1
  have hs₁ : Perm.sign c₁ = 1 := by rw [hc₁, Perm.viaFintypeEmbedding_sign]; exact hsign c hcp
  have hs₂ : Perm.sign c₂ = 1 := by rw [hc₂, Perm.viaFintypeEmbedding_sign]; exact hsign c hcp
  let a₁ : alternatingGroup (Fin n) := ⟨c₁, Perm.mem_alternatingGroup.mpr hs₁⟩
  let a₂ : alternatingGroup (Fin n) := ⟨c₂, Perm.mem_alternatingGroup.mpr hs₂⟩
  have ha₁p : a₁ ^ p = 1 := Subtype.ext (by simpa [a₁] using hc₁p)
  have ha₂p : a₂ ^ p = 1 := Subtype.ext (by simpa [a₂] using hc₂p)
  have hfix₁ : ∀ x : Fin n, x ∉ Set.range e₁ → c₁ x = x := fun x hx =>
    Perm.viaFintypeEmbedding_apply_notMem_range c e₁ hx
  have hfix₂ : ∀ x : Fin n, x ∉ Set.range e₂ → c₂ x = x := fun x hx =>
    Perm.viaFintypeEmbedding_apply_notMem_range c e₂ hx
  have hdisj : ∀ x, x ∉ Set.range e₁ ∨ x ∉ Set.range e₂ := by
    intro x
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
    have h : (i : ℕ) = p + (j : ℕ) := congrArg Fin.val (hi.trans hj.symm)
    have := i.isLt
    omega
  have hcomm : Commute c₁ c₂ := by
    have hd : Perm.Disjoint c₁ c₂ := by
      intro x
      rcases hdisj x with h | h
      · exact Or.inl (hfix₁ x h)
      · exact Or.inr (hfix₂ x h)
    exact hd.commute
  have hcomm' : ∀ a ∈ zpowers a₁, ∀ b ∈ zpowers a₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul]
    have := (hcomm.zpow_zpow i j).eq
    simpa [a₁, a₂] using this
  have hnot : a₂ ∉ zpowers a₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    have hk' : (c₁ ^ k) = c₂ := by simpa [a₁, a₂] using congrArg Subtype.val hk
    have hx : e₂ i₀ ∉ Set.range e₁ := by
      rintro ⟨j, hj⟩
      have h : (j : ℕ) = p + (i₀ : ℕ) := congrArg Fin.val hj
      have := j.isLt
      omega
    have h1 : (c₁ ^ k) (e₂ i₀) = e₂ i₀ := by
      have : c₁ (e₂ i₀) = e₂ i₀ := hfix₁ _ hx
      exact (Perm.zpow_apply_eq_self_of_apply_eq_self this k)
    have h2 : c₂ (e₂ i₀) = e₂ (c i₀) := Perm.viaFintypeEmbedding_apply_image c e₂ i₀
    rw [hk'] at h1
    rw [h1] at h2
    exact hi₀ (e₂.injective h2.symm)
  refine ⟨zpowers a₁ ⊔ zpowers a₂, SU1.IsElemAbelian.sup (SU1.isElemAbelian_zpowers ha₁p)
    (SU1.isElemAbelian_zpowers ha₂p) hcomm', ?_⟩
  have ha₁o : orderOf a₁ = p := by
    refine orderOf_eq_prime ha₁p fun h => ?_
    have : c₁ = 1 := by simpa [a₁] using congrArg Subtype.val h
    have h3 : c = 1 := by
      have : (Perm.extendDomainHom e₁.toEquivRange) c = 1 := this
      exact (injective_iff_map_eq_one _).mp (Perm.extendDomainHom_injective _) c this
    exact hc1 h3
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers a₁) ha₂p hnot
    (fun e he => hcomm' e he a₂ (mem_zpowers a₂)), Nat.card_zpowers, ha₁o, pow_two]

theorem lt_two_mul_of_pRank_le_one {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A : Type}
    [Group A] [Finite A] {K : Subgroup A} (e : ↥K ≃* alternatingGroup (Fin n))
    (h : Open.pRank p K ≤ 1) : n < 2 * p := by
  by_contra hn
  push Not at hn
  obtain ⟨E, hE, hcard⟩ := exists_elemAbelian_alt hp hp2 hn
  have hEm : IsElemAbelian p (E.map e.symm.toMonoidHom) := CFSG.Open.IsElemAbelian.map hE _
  have hcard' : Nat.card (E.map e.symm.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hcard]
  have hle := SU1.le_pRank hp.one_lt (le_top : E.map e.symm.toMonoidHom ≤ ⊤) hEm hcard'
  have h2 : (E.map e.symm.toMonoidHom).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hEm2 : IsElemAbelian p ((E.map e.symm.toMonoidHom).map K.subtype) :=
    CFSG.Open.IsElemAbelian.map hEm _
  have hcard2 : Nat.card ((E.map e.symm.toMonoidHom).map K.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcard']
  have := SU1.le_pRank hp.one_lt h2 hEm2 hcard2
  omega

theorem le_of_dvd_card_alt {p n : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (alternatingGroup (Fin n))) : p ≤ n := by
  have h2 : Nat.card (alternatingGroup (Fin n)) ∣ Nat.factorial n := by
    have := Subgroup.card_subgroup_dvd_card (alternatingGroup (Fin n))
    rwa [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at this
  exact (hp.dvd_factorial).mp (h.trans h2)

theorem not_sq_dvd_two_mul_factorial {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ≤ n)
    (hn : n < 2 * p) : ¬ p ^ 2 ∣ 2 * n.factorial := by
  intro h
  have hcop : Nat.Coprime (p ^ 2) 2 := by
    refine Nat.Coprime.pow_left 2 ?_
    exact (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have h1 : p ^ 2 ∣ n.factorial := hcop.dvd_of_dvd_mul_left h
  have hlog : Nat.log p n < 2 := by
    refine Nat.log_lt_of_lt_pow (by omega) ?_
    nlinarith
  have := (hp.pow_dvd_factorial_iff hlog).mp h1
  have h2 : ∑ i ∈ Finset.Ico 1 2, n / p ^ i = n / p := by simp
  rw [h2] at this
  have : n / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGAlt
