module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeSporAlt
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Equiv Equiv.Perm

theorem exists_injective_pi_alternatingGroup {k m n : ℕ} (h : k * m ≤ n) :
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

theorem alternatingGroup_three_comm (a b : alternatingGroup (Fin 3)) : a * b = b * a :=
  (alternatingGroup.isMulCommutative_of_card_le_three (by simp)).is_comm.comm a b

theorem natCard_alternatingGroup_three : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem alternatingGroup_three_pow (a : alternatingGroup (Fin 3)) : a ^ 3 = 1 := by
  have h := pow_card_eq_one' (x := a)
  rwa [natCard_alternatingGroup_three] at h

theorem isPGroup_range_rank {V X : Type*} [Group V] [Finite V] [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) {φ : V →* X} (hφ : Function.Injective φ) (hcomm : ∀ a b : V, a * b = b * a)
    (hexp : ∀ a : V, a ^ q = 1) {k : ℕ} (hcard : Nat.card V = q ^ k) :
    IsPGroup q φ.range ∧ Group.rank φ.range = k := by
  have hcard' : Nat.card φ.range = q ^ k := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  refine ⟨IsPGroup.of_card hcard', ?_⟩
  rw [← Group.rank_congr (MonoidHom.ofInjective hφ)]
  exact rank_eq_of_elementary hq hcomm hexp hcard

theorem isElemAbelian_range_of_comm {V X : Type*} [Group V] [Group X] {q : ℕ} (φ : V →* X)
    (hcomm : ∀ a b : V, a * b = b * a) (hexp : ∀ a : V, a ^ q = 1) :
    IsElemAbelian q φ.range := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, hcomm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp, map_one]

theorem exists_injective_of_center_eq_bot {X : Type*} [Group X] {K : Subgroup X} {n : ℕ}
    (hZ : Subgroup.center K = ⊥)
    (he : Nonempty (K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n))) :
    ∃ ι : alternatingGroup (Fin n) →* X, Function.Injective ι := by
  obtain ⟨e⟩ := he
  let e' : alternatingGroup (Fin n) ≃* K :=
    e.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  exact ⟨K.subtype.comp e'.toMonoidHom, K.subtype_injective.comp e'.injective⟩

theorem exists_rank_seven {X : Type*} [Group X] [Finite X] {p : ℕ} (hp7 : 7 ≤ p)
    {ι : alternatingGroup (Fin (3 * p)) →* X} (hι : Function.Injective ι) :
    ∃ Y : Subgroup X, IsPGroup 3 Y ∧ Group.rank Y = 7 := by
  obtain ⟨φ, hφ⟩ := exists_injective_pi_alternatingGroup (k := 7) (m := 3) (n := 3 * p)
    (by omega)
  exact ⟨_, isPGroup_range_rank Nat.prime_three (φ := ι.comp φ) (hι.comp hφ)
    (fun a b => funext fun i => alternatingGroup_three_comm (a i) (b i))
    (fun a => funext fun i => alternatingGroup_three_pow (a i))
    (by rw [Nat.card_fun, natCard_alternatingGroup_three, Nat.card_eq_fintype_card,
      Fintype.card_fin])⟩

theorem prime_dvd_natCard_alternatingGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ Nat.card (alternatingGroup (Fin p)) := by
  have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr hp.two_le
  have h3 : 2 ≤ p - 1 := by have := hp.two_le; omega
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  apply Nat.dvd_div_of_mul_dvd
  rw [← Nat.mul_factorial_pred hp.ne_zero, mul_comm 2 p]
  exact Nat.mul_dvd_mul_left p (Nat.dvd_factorial two_pos h3)

theorem exists_rank_six_le {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) {ι : alternatingGroup (Fin (3 * p)) →* X} (hι : Function.Injective ι)
    (R : Sylow p X) {X₀ : Subgroup X}
    (hX₀ : ∀ E : Subgroup X, IsElemAbelian p E → Nat.card E = p ^ 3 → E ≤ R →
      ∀ F : Subgroup X, F ≤ E → F.relIndex E = p → Subgroup.centralizer (F : Set X) ≤ X₀) :
    ∃ Y : Subgroup X, Y ≤ X₀ ∧ IsPGroup 3 Y ∧ Group.rank Y = 6 := by
  have hp : p.Prime := Fact.out
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_injective_pi_alternatingGroup (k := 3) (m := p) (n := 3 * p) le_rfl
  obtain ⟨c, hc⟩ :=
    exists_prime_orderOf_dvd_card' p (prime_dvd_natCard_alternatingGroup hp (by omega))
  set C : Subgroup (alternatingGroup (Fin p)) := Subgroup.zpowers c
  have hCcard : Nat.card C = p := by rw [Nat.card_zpowers, hc]
  have hCcomm : ∀ x y : C, x * y = y * x := (Subgroup.zpowers_isMulCommutative c).is_comm.comm
  have hCexp : ∀ x : C, x ^ p = 1 := fun x => by
    have h := pow_card_eq_one' (x := x)
    rwa [hCcard] at h
  set j : (Fin 3 → C) →* (Fin 3 → alternatingGroup (Fin p)) := C.subtype.compLeft (Fin 3)
    with hjdef
  have hj : Function.Injective j := fun x y hxy => funext fun i => Subtype.ext (congrFun hxy i)
  have hcard3 : Nat.card (Fin 3 → C) = p ^ 3 := by
    rw [Nat.card_fun, hCcard, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hjcomm : ∀ x y : Fin 3 → C, x * y = y * x := fun x y => funext fun i => hCcomm (x i) (y i)
  have hjexp : ∀ x : Fin 3 → C, x ^ p = 1 := fun x => funext fun i => hCexp (x i)
  have hΨ₀ : Function.Injective (ι.comp Ψ₁) := hι.comp hΨ₁
  obtain ⟨S, hS⟩ := (isPGroup_range_rank hp (φ := (ι.comp Ψ₁).comp j) (hΨ₀.comp hj) hjcomm
    hjexp hcard3).1.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S R
  set Ψ := (MulAut.conj g).toMonoidHom.comp (ι.comp Ψ₁)
  have hΨ : Function.Injective Ψ := (MulAut.conj g).injective.comp hΨ₀
  set ψ := Ψ.comp j
  have hψ : Function.Injective ψ := hΨ.comp hj
  have hψR : ψ.range ≤ R := by
    rintro _ ⟨x, rfl⟩
    have hx : (ι.comp Ψ₁).comp j x ∈ (S : Subgroup X) := hS ⟨x, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hx
  have hEel : IsElemAbelian p ψ.range := isElemAbelian_range_of_comm ψ hjcomm hjexp
  have hEcard : Nat.card ψ.range = p ^ 3 :=
    (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm.trans hcard3
  let F : Fin 3 → Subgroup X := fun k => (Pi.evalMonoidHom (fun _ : Fin 3 => C) k).ker.map ψ
  have hFE : ∀ k, F k ≤ ψ.range := fun k => Subgroup.map_le_range ψ _
  have hFidx : ∀ k, (F k).relIndex ψ.range = p := fun k => by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hψ,
      Subgroup.relIndex_top_right, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr fun x => ⟨Pi.mulSingle k x, by simp⟩, Subgroup.card_top, hCcard]
  have hcent : ∀ k, Subgroup.centralizer (F k : Set X) ≤ X₀ := fun k =>
    hX₀ _ hEel hEcard hψR (F k) (hFE k) (hFidx k)
  have hblock : ∀ k (u : alternatingGroup (Fin p)), Ψ (Pi.mulSingle k u) ∈ X₀ := by
    intro k u
    apply hcent k
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨f, hf, rfl⟩
    have hf' : f k = 1 := hf
    have hcomm : j f * Pi.mulSingle k u = Pi.mulSingle k u * j f := by
      funext i
      by_cases hi : i = k
      · subst hi
        simp [hjdef, hf']
      · simp [hjdef, Pi.mulSingle_eq_of_ne hi]
    change Ψ (j f) * Ψ (Pi.mulSingle k u) = Ψ (Pi.mulSingle k u) * Ψ (j f)
    rw [← map_mul, ← map_mul, hcomm]
  obtain ⟨ιU, hιU⟩ := exists_injective_pi_alternatingGroup (k := 2) (m := 3) (n := p) (by omega)
  set χ := Ψ.comp (ιU.compLeft (Fin 3))
  have hχ : Function.Injective χ :=
    hΨ.comp fun x y hxy => funext fun i => hιU (congrFun hxy i)
  refine ⟨χ.range, ?_, isPGroup_range_rank Nat.prime_three hχ
    (fun a b => funext fun i => funext fun l => alternatingGroup_three_comm (a i l) (b i l))
    (fun a => funext fun i => funext fun l => alternatingGroup_three_pow (a i l)) ?_⟩
  · rintro _ ⟨v, rfl⟩
    have hv : ιU.compLeft (Fin 3) v = Pi.mulSingle 0 (ιU (v 0)) * Pi.mulSingle 1 (ιU (v 1)) *
        Pi.mulSingle 2 (ιU (v 2)) := by
      funext i
      fin_cases i <;> simp
    change Ψ (ιU.compLeft (Fin 3) v) ∈ X₀
    rw [hv, map_mul, map_mul]
    exact X₀.mul_mem (X₀.mul_mem (hblock 0 _) (hblock 1 _)) (hblock 2 _)
  · rw [Nat.card_fun, Nat.card_fun, natCard_alternatingGroup_three]
    simp

theorem a3pGuestLift_of (hT : ThompsonNormalAbelianGen) : A3pGuestLift := by
  intro G _ _ p _ P M H R Rbar hcfg K _ _ hZ he hp7
  set N := primeComplementCore (G := H) p with hNdef
  obtain ⟨ι, hι⟩ := exists_injective_of_center_eq_bot hZ he
  obtain ⟨Y₇, hY₇, hr₇⟩ := exists_rank_seven hp7 hι
  have h4 : 3 < Open.pRank 3 H :=
    lt_pRank_of_quotient hT (by norm_num) N hY₇ (Subgroup.map_subtype_le _) (by rw [hr₇]; norm_num)
  have hβ : 3 ∈ GLBBetaFour G := by
    refine ⟨Nat.prime_three, by norm_num,
      PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank 3 Nat.prime_three H
        (by omega), ?_⟩
    have h4' : 4 ≤ Open.pRank 3 H := h4
    exact h4'.trans (le_csSup (PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3
      Nat.prime_three) ⟨H, hcfg.ext.maxTwoLocal_H.1, rfl⟩)
  obtain ⟨Y₆, hY₆X₀, hY₆, hr₆⟩ := exists_rank_six_le hp7 hι Rbar hcfg.red.hyperplane_le
  have hOM : N ≤ (H ⊓ M).subgroupOf H := by
    rw [hNdef, ← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hcfg.ext.primeCore_le
  have hle : (Y₆.comap (QuotientGroup.mk' N)).map H.subtype ≤ H ⊓ M := by
    calc _ ≤ ((((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N)).map H.subtype := Subgroup.map_mono (Subgroup.comap_mono hY₆X₀)
      _ = H ⊓ M := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOM,
          Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  exact ⟨hβ, lt_pRank_of_quotient hT (by norm_num) N hY₆ hle (by rw [hr₆]; norm_num)⟩

end CFSG.AGLEmbedding
