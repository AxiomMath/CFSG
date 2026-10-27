module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.AbelianTransitive77
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

open Equiv MulAction CFSG.RankThree.LocalRank CFSG.AGLEmbeddingD2.Wilson.Proving

variable {n : ℕ}

theorem fixedPoints_ne_univ_of_ne_bot {G : Subgroup (Equiv.Perm (Fin n))}
    {D : Subgroup G} (hD : D ≠ ⊥) : MulAction.fixedPoints D (Fin n) ≠ Set.univ := by
  intro hfix
  apply hD
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  apply Equiv.ext
  intro i
  have hi : i ∈ MulAction.fixedPoints D (Fin n) := by
    rw [hfix]
    exact Set.mem_univ i
  have h := MulAction.mem_fixedPoints.mp hi ⟨x, hx⟩
  simp only [Subgroup.coe_one, Equiv.Perm.one_apply]
  exact h

theorem exists_abelian_normal_transitive (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive G (Fin n)] (S : Subgroup G) [S.Normal] [Group.IsSolvable S]
    (hS : S ≠ ⊥) :
    ∃ A : Subgroup (Equiv.Perm (Fin n)), A ≤ G ∧ (A.subgroupOf G).Normal ∧ A ≠ ⊥ ∧
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ i j : Fin n, ∃ a ∈ A, a i = j) := by
  classical
  have hex : ∃ n, derivedSeries S n = ⊥ := Group.IsSolvable.solvable
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hS
    have hbot : derivedSeries S 0 = ⊥ := by
      have := Nat.find_spec hex
      rwa [h0] at this
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ derivedSeries S 0 := Subgroup.mem_top _
    rw [hbot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hm0
  have hkne : derivedSeries S k ≠ ⊥ := fun h =>
    Nat.find_min hex (show k < Nat.find hex by omega) h
  have hkbot : derivedSeries S (k + 1) = ⊥ := by
    rw [← hk]
    exact Nat.find_spec hex
  have hcommS : ∀ x ∈ derivedSeries S k, ∀ y ∈ derivedSeries S k, x * y = y * x := by
    intro x hx y hy
    have hmem := Subgroup.commutator_mem_commutator hx hy
    rw [← derivedSeries_succ, hkbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup G, D = (derivedSeries S k).map S.subtype := ⟨_, rfl⟩
  have hDnormal : D.Normal := by
    rw [hDdef]
    infer_instance
  have hDne : D ≠ ⊥ := by
    intro h
    apply hkne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxD : S.subtype x ∈ D := by
      rw [hDdef]
      exact Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at hxD
    exact Subtype.ext hxD
  have hfix : MulAction.fixedPoints D (Fin n) ≠ Set.univ := fixedPoints_ne_univ_of_ne_bot hDne
  have hpt : MulAction.IsPretransitive D (Fin n) :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := D) hfix
  obtain ⟨φ, hφ⟩ : ∃ φ : S →* Equiv.Perm (Fin n), φ = G.subtype.comp S.subtype := ⟨_, rfl⟩
  have hφx : ∀ x : S, φ x = ((S.subtype x : G) : Equiv.Perm (Fin n)) := by
    intro x
    rw [hφ]
    rfl
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (Equiv.Perm (Fin n)),
      A = (derivedSeries S k).map φ := ⟨_, rfl⟩
  have hAle : A ≤ G := by
    intro a ha
    rw [hAdef] at ha
    obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.mp ha
    rw [hφx]
    exact (S.subtype x).2
  have hAD : A.subgroupOf G = D := by
    ext g
    rw [Subgroup.mem_subgroupOf, hAdef]
    constructor
    · intro hg
      obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hg
      rw [hDdef]
      refine Subgroup.mem_map.mpr ⟨x, hx, Subtype.ext ?_⟩
      rw [hφx] at hxeq
      exact hxeq
    · intro hg
      rw [hDdef] at hg
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
      rw [hφx, hxg]
  refine ⟨A, hAle, by rw [hAD]; exact hDnormal, ?_, ?_, ?_⟩
  · intro h
    apply hDne
    rw [← hAD, h, Subgroup.bot_subgroupOf]
  · intro a ha b hb
    rw [hAdef] at ha hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hcommS x hx y hy]
  · intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D i j
    have hgD : (g : G) ∈ (derivedSeries S k).map S.subtype := by
      rw [← hDdef]
      exact g.2
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgD
    refine ⟨φ x, ?_, ?_⟩
    · rw [hAdef]
      exact Subgroup.mem_map_of_mem φ hx
    · rw [hφx, hxg, ← hg]
      rfl

@[expose] def expSub (A : Subgroup (Equiv.Perm (Fin n)))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (m : ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {x | x ∈ A ∧ x ^ m = 1}
  mul_mem' := by
    rintro a b ⟨ha, ham⟩ ⟨hb, hbm⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    rw [(show Commute a b from hcomm a ha b hb).mul_pow, ham, hbm, mul_one]
  one_mem' := ⟨A.one_mem, one_pow m⟩
  inv_mem' := by
    rintro a ⟨ha, ham⟩
    exact ⟨A.inv_mem ha, by rw [inv_pow, ham, inv_one]⟩

theorem pow_eq_one_of_abelian_normal_transitive (G A : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive G (Fin n)] (hA : A ≤ G) (hAn : (A.subgroupOf G).Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (htrans : ∀ i j : Fin n, ∃ a ∈ A, a i = j)
    {m p : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hpn : p ∣ n) : ∀ x ∈ A, x ^ m = 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    intro x _
    have : x = 1 := Equiv.ext fun i => isEmptyElim i
    rw [this, one_pow]
  have hcard : Nat.card A = n :=
    CFSG.AGLEmbeddingD2.Wilson.Proving.card_eq_of_abelian_transitive A hcomm htrans ⟨0, hpos⟩
  set T := expSub A hcomm m with hT
  have hTA : T ≤ A := fun x hx => hx.1
  have hTG : T ≤ G := hTA.trans hA
  have hTn : (T.subgroupOf G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxA : (x : Equiv.Perm (Fin n)) ∈ A := hx.1
    have hconj : (g * x * g⁻¹ : G) ∈ A.subgroupOf G := hAn.conj_mem x hxA g
    refine ⟨hconj, ?_⟩
    have h1 : ((g * x * g⁻¹ : G) : Equiv.Perm (Fin n)) =
        (g : Equiv.Perm (Fin n)) * x * (g : Equiv.Perm (Fin n))⁻¹ := rfl
    show ((g * x * g⁻¹ : G) : Equiv.Perm (Fin n)) ^ m = 1
    rw [h1, conj_pow, hx.2]
    simp
  have : Fact p.Prime := ⟨hp⟩
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
  have hTne : T ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p (by rw [hcard]; exact hpn : p ∣ Nat.card A)
    have hx1 : (x : Equiv.Perm (Fin n)) ≠ 1 := by
      intro h
      have : x = 1 := Subtype.ext h
      rw [this, orderOf_one] at hx
      exact hp.one_lt.ne hx
    have hxm : (x : Equiv.Perm (Fin n)) ^ m = 1 := by
      have : (x : Equiv.Perm (Fin n)) ^ p = 1 := by
        have h := pow_orderOf_eq_one x
        rw [hx] at h
        exact congrArg Subtype.val h
      obtain ⟨c, rfl⟩ := hpm
      rw [pow_mul, this, one_pow]
    have hmem : (x : Equiv.Perm (Fin n)) ∈ T := ⟨x.2, hxm⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hTsub : T.subgroupOf G ≠ ⊥ := by
    intro h
    apply hTne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (⟨x, hTG hx⟩ : G) ∈ T.subgroupOf G := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hfix := fixedPoints_ne_univ_of_ne_bot (G := G) hTsub
  have hpt : MulAction.IsPretransitive (T.subgroupOf G) (Fin n) :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal (N := T.subgroupOf G) hfix
  have hTtrans : ∀ i j : Fin n, ∃ a ∈ T, a i = j := by
    intro i j
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (T.subgroupOf G) i j
    exact ⟨g, Subgroup.mem_subgroupOf.mp g.2, hg⟩
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => hcomm a ha.1 b hb.1
  have hTcard : Nat.card T = n :=
    CFSG.AGLEmbeddingD2.Wilson.Proving.card_eq_of_abelian_transitive T hTcomm hTtrans ⟨0, hpos⟩
  have hTAeq : T = A := by
    refine Subgroup.eq_of_le_of_card_ge hTA ?_
    rw [hcard, hTcard]
  intro x hx
  have : x ∈ T := by rw [hTAeq]; exact hx
  exact this.2

theorem eq_bot_of_normal_solvable_of_not_isPrimePow (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive G (Fin n)] (hn : ¬ IsPrimePow n)
    (S : Subgroup G) [S.Normal] [Group.IsSolvable S] : S = ⊥ := by
  classical
  by_contra hS
  obtain ⟨A, hAG, hAn, hAne, hcomm, htrans⟩ := exists_abelian_normal_transitive G S hS
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    apply hAne
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Equiv.ext fun i => isEmptyElim i
  have hcard : Nat.card A = n :=
    card_eq_of_abelian_transitive A hcomm htrans ⟨0, hpos⟩
  have hn1 : n ≠ 1 := by
    intro h1
    apply hAne
    exact Subgroup.card_eq_one.1 (hcard.trans h1)
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hpos.ne' hpn
  have hpm : p ∣ p ^ (n.factorization p) := dvd_pow_self p hk.ne'
  have hall : ∀ x ∈ A, x ^ (p ^ (n.factorization p)) = 1 :=
    pow_eq_one_of_abelian_normal_transitive G A hAG hAn hcomm htrans hp hpm hpn
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hpos.ne')
  apply hn
  rw [isPrimePow_iff_unique_prime_dvd]
  refine ⟨p, ⟨hp, hpn⟩, ?_⟩
  rintro q ⟨hq, hqn⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q (by rw [hcard]; exact hqn : q ∣ Nat.card A)
  have h1 : orderOf (x : Equiv.Perm (Fin n)) ∣ p ^ (n.factorization p) :=
    orderOf_dvd_of_pow_eq_one (hall x x.2)
  rw [Subgroup.orderOf_coe, hx] at h1
  exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h1)

theorem eq_bot_of_normal_solvable_of_order_four (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPreprimitive G (Fin n)] (hn2 : 2 ∣ n) {u : ℕ} (hu : Odd u)
    (hcardG : Nat.card G = n * u) (g : G) (hg4 : g ^ 4 = 1) (hg2 : g ^ 2 ≠ 1)
    (S : Subgroup G) [S.Normal] [Group.IsSolvable S] : S = ⊥ := by
  classical
  by_contra hS
  obtain ⟨A, hAG, hAn, hAne, hcomm, htrans⟩ := exists_abelian_normal_transitive G S hS
  have hpos : 0 < n := Nat.pos_of_ne_zero (by
    rintro rfl
    apply hAne
    rw [Subgroup.eq_bot_iff_forall]
    intro x _
    exact Equiv.ext fun i => isEmptyElim i)
  have hcard : Nat.card A = n :=
    card_eq_of_abelian_transitive A hcomm htrans ⟨0, hpos⟩
  have hall : ∀ x ∈ A, x ^ 2 = 1 :=
    pow_eq_one_of_abelian_normal_transitive G A hAG hAn hcomm htrans Nat.prime_two
      (dvd_refl 2) hn2
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by
    rw [hcardG]; exact Nat.mul_ne_zero hpos.ne' (by rintro rfl; exact absurd hu (by decide)))
  set D := A.subgroupOf G with hD
  have hDcard : Nat.card D = n :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAG).toEquiv).trans hcard
  have hq : Nat.card (G ⧸ D) = u := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup D
    rw [hcardG, hDcard] at h
    have : n * u = n * Nat.card (G ⧸ D) := by rw [h, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have hgbar : (g : G ⧸ D) = 1 := by
    have h1 : orderOf (g : G ⧸ D) ∣ u := hq ▸ orderOf_dvd_natCard _
    have h2 : orderOf (g : G ⧸ D) ∣ 4 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← QuotientGroup.mk_pow, hg4, QuotientGroup.mk_one]
    have hcop : Nat.Coprime u 4 := by
      have h2 : Nat.Coprime u 2 := hu.coprime_two_right
      simpa using Nat.Coprime.pow_right 2 h2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  have hgD : g ∈ D := (QuotientGroup.eq_one_iff g).1 hgbar
  have hgA : (g : Equiv.Perm (Fin n)) ∈ A := hgD
  apply hg2
  exact Subtype.ext (by simpa using hall _ hgA)

theorem aschbacherSolvableCore_eq_bot_of_hom {H Y : Type*} [Group H] [Finite H] [Group Y]
    (ψ : H →* Y) (hker : IsPGroup 3 ψ.ker)
    (hrad : ∀ K : Subgroup ψ.range, K.Normal → Group.IsSolvable K → K = ⊥) :
    aschbacherSolvableCore 3 H = ⊥ := by
  obtain ⟨hsolv, hchar, hcard, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  set θ := aschbacherSolvableCore 3 H with hθ
  have : θ.Characteristic := hchar
  have : θ.Normal := inferInstance
  set f : H →* ψ.range := ψ.rangeRestrict with hf
  have hfs : Function.Surjective f := ψ.rangeRestrict_surjective
  have hKn : (θ.map f).Normal := Subgroup.Normal.map ‹θ.Normal› f hfs
  have hKs : Group.IsSolvable (θ.map f) :=
    Group.isSolvable_of_surjective (f := f.subgroupMap θ) (MonoidHom.subgroupMap_surjective f θ)
  have hK : θ.map f = ⊥ := hrad _ hKn hKs
  have hle : θ ≤ ψ.ker := by
    intro x hx
    have : f x ∈ θ.map f := Subgroup.mem_map_of_mem f hx
    rw [hK, Subgroup.mem_bot] at this
    rw [MonoidHom.mem_ker]
    have h2 := congrArg Subtype.val this
    simpa [hf] using h2
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hdvd : Nat.card θ ∣ 3 ^ k := hk ▸ Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime (Nat.card θ) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (fun h => hcard h)).symm
  have h1 : Nat.card θ = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  exact Subgroup.card_eq_one.1 h1

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

end
