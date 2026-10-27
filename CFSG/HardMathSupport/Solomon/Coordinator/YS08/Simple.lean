module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Chev

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.HardMathSupport.Solomon.Coordinator

private theorem ys08s_isQuasisimple_native {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨hQ.1⟩, hQ.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q hQ⟩

theorem component_to_simple {Y : Type} [Group Y] [Finite Y] {α : MulAut Y} (hα : α ^ 3 = 1)
    {J : Subgroup Y} (hJ : GLAPComponent 3 (Lemma510Ns.fixSub α) J) :
    ∃ (β : MulAut (Y ⧸ Subgroup.center Y)) (J' : Subgroup (Y ⧸ Subgroup.center Y)),
      β ^ 3 = 1 ∧ GLAPComponent 3 (Lemma510Ns.fixSub β) J' ∧
        ∃ ψ : barOf 3 J →* barOf 3 J', Function.Surjective ψ ∧
          ψ.ker ≤ Subgroup.center (barOf 3 J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ Subgroup.center Y := (QuotientGroup.ker_mk' _).le
  let β : MulAut (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) α (map_center_mulEquiv α)
  have hαβ : ∀ y, π (α y) = β (π y) := fun y => rfl
  have hβk : ∀ (k : ℕ) (y : Y), (β ^ k) (π y) = π ((α ^ k) y) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ k ih => intro y; rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ← hαβ, ih]
  have hβ3 : β ^ 3 = 1 := by
    ext z
    obtain ⟨y, rfl⟩ := hπ z
    rw [hβk, hα]
    rfl
  have hJ' : GLAPComponent 3 (fixSubgroup β) (J.map π) :=
    glaPComponent_map_fixSubgroup π hker α β hαβ hπ Nat.prime_three hJ
  refine ⟨β, J.map π, hβ3, hJ', ?_⟩
  let φ0 : ↥J →* barOf 3 (J.map π) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(J.map π))).comp (π.subgroupMap J)
  have hφ0 : Function.Surjective φ0 :=
    (QuotientGroup.mk'_surjective _).comp (MonoidHom.subgroupMap_surjective π J)
  have hker0 : GLAPPrimeCore 3 ↥J ≤ φ0.ker := by
    intro x hx
    have := CFSG.map_pPrimeCore_le (π.subgroupMap J) (MonoidHom.subgroupMap_surjective π J)
      ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 this
  let ψ : barOf 3 J →* barOf 3 (J.map π) := QuotientGroup.lift (GLAPPrimeCore 3 ↥J) φ0 hker0
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ0 y
    exact ⟨QuotientGroup.mk x, rfl⟩
  refine ⟨ψ, hψ, ?_⟩
  have hKq : CFSG.Open.IsQuasisimple (barOf 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  have hKq' : CFSG.Open.IsQuasisimple (barOf 3 (J.map π)) :=
    isQuasisimple_quotient_of_glaPComponent hJ'
  rcases CFSG.LocalCores.quasisimple_normal_subgroups (ys08s_isQuasisimple_native hKq)
    (inferInstance : ψ.ker.Normal) with h | h
  · exfalso
    have hsub : Subsingleton (barOf 3 (J.map π)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : x ∈ ψ.ker := h ▸ Subgroup.mem_top x
      have hy : y ∈ ψ.ker := h ▸ Subgroup.mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      rw [hx, hy]
    have := hKq'.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (barOf 3 (J.map π) ⧸ Subgroup.center (barOf 3 (J.map π)))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subsingleton.elim a b))
  · exact h

@[expose] def IsL3Kind (p : ℕ) (X : Type) [Group X] : Prop :=
  SL3EpsOfChar p X ∨
    ∃ (W : Type) (_ : Group W), SL3EpsOfChar p W ∧ Nonempty (X ≃* W ⧸ Subgroup.center W)

theorem SL3EpsOfChar.of_mulEquiv' {p : ℕ} {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    (h : SL3EpsOfChar p X) : SL3EpsOfChar p X' := by
  rcases h with ⟨F, hF, hfin, hchar, hmod, ⟨f⟩⟩ | ⟨F, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨f⟩⟩
  · exact Or.inl ⟨F, hF, hfin, hchar, hmod, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨F, hF, hfin, q, hchar, hcard, hq3, hq2, ⟨e.symm.trans f⟩⟩

theorem isL3Kind_of_isLThreeFour {X : Type} [Group X] (h : IsLThreeFour X) : IsL3Kind 2 X := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hchar : CharP F 2 := by
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
  refine Or.inr ⟨Matrix.SpecialLinearGroup (Fin 3) F, inferInstance,
    Or.inl ⟨F, hF, hfin, hchar, by rw [hcard], ⟨CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F⟩⟩,
    ⟨?_⟩⟩
  exact (e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 F).symm).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 F))

theorem isL3Kind_of_central_quotient {p : ℕ} {X X' : Type} [Group X] [Finite X] [Group X']
    (hX : SL3EpsOfChar p X) (ψ : X →* X') (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center X) : IsL3Kind p X' := by
  obtain ⟨hZ3, -⟩ := sl3Eps_facts hX
  have hdvd : Nat.card ψ.ker ∣ 3 := by
    rw [← hZ3]
    exact Subgroup.card_dvd_of_le hk
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
  · have hbot : ψ.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hbot
    exact Or.inl (SL3EpsOfChar.of_mulEquiv' (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩) hX)
  · have heq : ψ.ker = Subgroup.center X :=
      Subgroup.eq_of_le_of_card_ge hk (by rw [hZ3]; exact h3.ge)
    refine Or.inr ⟨X, inferInstance, hX, ⟨?_⟩⟩
    exact (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq heq)

theorem isLThreeFour_of_central_quotient {X X' : Type} [Group X] [Group X'] (hX : IsLThreeFour X)
    (ψ : X →* X') (hψ : Function.Surjective ψ) (hk : ψ.ker ≤ Subgroup.center X) :
    IsLThreeFour X' := by
  obtain ⟨hs, hna⟩ := isSimpleGroup_of_isLThreeFour hX
  haveI := hs
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have hbot : ψ.ker = ⊥ := le_bot_iff.1 (hZ ▸ hk)
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hbot
  exact IsLThreeFour.of_mulEquiv (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩) hX

end CFSG.HardMathSupport.Solomon.Coordinator.YS08
