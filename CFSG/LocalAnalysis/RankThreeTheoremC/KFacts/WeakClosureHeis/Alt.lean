module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocksOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.Open Equiv Equiv.Perm

private theorem exists_injective_pi_alt {k m n : ℕ} (h : k * m ≤ n) :
    ∃ φ : (Fin k → alternatingGroup (Fin m)) →* alternatingGroup (Fin n),
      Function.Injective φ := by
  classical
  let ψ : (Fin k → Perm (Fin m)) →* Perm (Fin k × Fin m) :=
    { toFun := fun σ => Equiv.prodCongrRight σ
      map_one' := Equiv.ext fun _ => rfl
      map_mul' := fun _ _ => Equiv.ext fun _ => rfl }
  have hψ : Function.Injective ψ := fun σ τ hστ => funext fun a => Equiv.ext fun b => by
    have := congrArg (fun f : Perm (Fin k × Fin m) => (f (a, b)).2) hστ
    simpa [ψ] using this
  obtain ⟨ι⟩ : Nonempty (Fin k × Fin m ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  let χ : (Fin k → alternatingGroup (Fin m)) →* Perm (Fin n) :=
    (viaEmbeddingHom ι).comp (ψ.comp ((alternatingGroup (Fin m)).subtype.compLeft (Fin k)))
  have hχ : ∀ x, χ x ∈ alternatingGroup (Fin n) := fun x => by
    rw [mem_alternatingGroup]
    simp only [χ, MonoidHom.comp_apply, viaEmbeddingHom_apply, viaEmbedding, sign_extendDomain]
    change sign (Equiv.prodCongrRight _) = 1
    rw [sign_prodCongrRight]
    exact Finset.prod_eq_one fun i _ => (x i).2
  refine ⟨χ.codRestrict _ hχ, (MonoidHom.injective_codRestrict _ _ _).mpr ?_⟩
  refine (viaEmbeddingHom_injective ι).comp (hψ.comp fun x y hxy => funext fun i => ?_)
  exact Subtype.ext (congrFun hxy i)

private theorem prime_dvd_card_alt {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ Nat.card (alternatingGroup (Fin p)) := by
  have hsq : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  have hfac := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks.factorization_card_alternatingGroup_fin
    hp hp2 hp.two_le hsq
  have hpos : Nat.card (alternatingGroup (Fin p)) ≠ 0 := Nat.card_pos.ne'
  exact (hp.dvd_iff_one_le_factorization hpos).2 (by rw [hfac, Nat.div_self hp.pos])

private theorem isElemAbelian_range_of_comm' {V X : Type*} [Group V] [Group X] {q : ℕ}
    (φ : V →* X) (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ a : V, a ^ q = 1) :
    IsElemAbelian q φ.range := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp, map_one]

theorem sdAlt_holds : SDAlt := by
  intro n hn p hp hp5
  have hp2 : p ≠ 2 := by omega
  by_cases h4 : n < 4 * p
  ·
    have hsq : 4 * p ≤ p ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul_right p (by omega)
    refine SylowDichotomyAt.of_factorization_le ?_
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AltBlocks.factorization_card_alternatingGroup_fin
      hp hp2 (by omega) (lt_of_lt_of_le h4 hsq)]
    have hdiv : n / p < 4 := (Nat.div_lt_iff_lt_mul hp.pos).2 (by omega)
    omega
  ·
    push Not at h4
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨φ, hφ⟩ := exists_injective_pi_alt (k := 4) (m := p) (n := n) h4
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p (prime_dvd_card_alt hp hp2)
    set C : Subgroup (alternatingGroup (Fin p)) := Subgroup.zpowers c
    have hCcard : Nat.card C = p := by rw [Nat.card_zpowers, hc]
    have hCcomm : ∀ x y : C, x * y = y * x := (Subgroup.zpowers_isMulCommutative c).is_comm.comm
    have hCexp : ∀ x : C, x ^ p = 1 := fun x => by
      have h := pow_card_eq_one' (x := x)
      rwa [hCcard] at h
    set j : (Fin 4 → C) →* (Fin 4 → alternatingGroup (Fin p)) := C.subtype.compLeft (Fin 4)
      with hjdef
    have hj : Function.Injective j := fun x y hxy =>
      funext fun i => Subtype.ext (congrFun hxy i)
    have hcard4 : Nat.card (Fin 4 → C) = p ^ 4 := by
      rw [Nat.card_fun, hCcard, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hjcomm : ∀ x y : Fin 4 → C, x * y = y * x := fun x y =>
      funext fun i => hCcomm (x i) (y i)
    have hjexp : ∀ x : Fin 4 → C, x ^ p = 1 := fun x => funext fun i => hCexp (x i)
    set ψ := φ.comp j with hψdef
    have hψ : Function.Injective ψ := hφ.comp hj
    have hEel : IsElemAbelian p ψ.range := isElemAbelian_range_of_comm' ψ hjcomm hjexp
    have hEcard : Nat.card ψ.range = p ^ 4 :=
      (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm.trans hcard4
    exact SylowDichotomyAt.of_elemAbelian hp hEel hEcard le_rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
