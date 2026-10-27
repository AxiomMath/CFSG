module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Reducible
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.CentralNormal
public import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists

section Helpers

variable {K : Type} [Field K] [Finite K] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem isPerfect_of_not_isSolvable {G : Type*} [Group G] (hns : ¬ Group.IsSolvable G)
    (hmin : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) : Group.IsPerfect G := by
  refine ⟨by_contra fun h => hns ?_⟩
  have := hmin _ h
  exact Group.isSolvable_of_ker_le_range (commutator G).subtype (Abelianization.of (G := G))
    (by rw [Abelianization.ker_of, Subgroup.range_subtype])

private def fixedSubmodule {Y : Subgroup (GL ι K)} (N : Subgroup Y) : Submodule K (ι → K) where
  carrier := {v | ∀ n ∈ N, ((n : GL ι K) : Matrix ι ι K) *ᵥ v = v}
  add_mem' ha hb n hn := by rw [mulVec_add, ha n hn, hb n hn]
  zero_mem' n _ := mulVec_zero _
  smul_mem' c v hv n hn := by rw [mulVec_smul, hv n hn]

omit [Finite K] in
private theorem fixedSubmodule_invariant {Y : Subgroup (GL ι K)} {N : Subgroup Y} (hN : N.Normal) :
    ∀ g ∈ Y, ∀ w ∈ fixedSubmodule N, (g : Matrix ι ι K) *ᵥ w ∈ fixedSubmodule N := by
  intro g hg w hw n hn
  have hc := hw _ (hN.conj_mem n hn (⟨g, hg⟩ : Y)⁻¹)
  have hmul : ((n : GL ι K) : Matrix ι ι K) * g =
      g * (((⟨g, hg⟩ : Y)⁻¹ * n * (⟨g, hg⟩ : Y)⁻¹⁻¹ : Y) : GL ι K) := by
    simp only [inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, ← mul_assoc,
      Units.mul_inv, one_mul]
  rw [mulVec_mulVec, hmul, ← mulVec_mulVec, hc]

private theorem fixedSubmodule_ne_bot [Nonempty ι] {Y : Subgroup (GL ι K)} {N : Subgroup Y}
    (hp : IsPGroup (ringChar K) N) : fixedSubmodule N ≠ ⊥ := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  have := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ Nat.card (ι → K) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card, hk, ← pow_mul]
    exact dvd_pow_self _ (Nat.mul_ne_zero k.ne_zero Nat.card_pos.ne')
  obtain ⟨v, hv, hv0⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (ι → K) hdvd
    (a := 0) (fun n => smul_zero _)
  rw [Submodule.ne_bot_iff]
  exact ⟨v, fun n hn => hv ⟨n, hn⟩, Ne.symm hv0⟩

theorem eq_bot_of_normal_isPGroup_ringChar [Nonempty ι] {Y : Subgroup (GL ι K)}
    (hirr : IsIrreducibleOn Y) {N : Subgroup Y} (hN : N.Normal)
    (hp : IsPGroup (ringChar K) N) : N = ⊥ := by
  have htop := (hirr _ (fixedSubmodule_invariant hN)).resolve_left (fixedSubmodule_ne_bot hp)
  refine (Subgroup.eq_bot_iff_forall N).mpr fun n hn => ?_
  have h1 : ((n : GL ι K) : Matrix ι ι K) = 1 := by
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
    exact (htop ▸ Submodule.mem_top (x := v) : v ∈ fixedSubmodule N) n hn
  exact Subtype.ext (Units.ext h1)

private theorem fittingSubgroup_le_center [Nonempty ι] (hι : Fintype.card ι ≤ 4)
    {Y : Subgroup (GL ι K)} (hY : Group.IsPerfect Y) (hirr : IsIrreducibleOn Y)
    (h3 : Nat.Coprime 3 (Nat.card Y)) : CFSG.fittingSubgroup Y ≤ Subgroup.center Y := by
  rw [CFSG.fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  by_cases hp : p.1.1 = ringChar K
  · rw [eq_bot_of_normal_isPGroup_ringChar hirr CFSG.pCore_normal (hp ▸ CFSG.pCore_isPGroup)]
    exact bot_le
  · exact le_center_of_normal_of_isPGroup hι hY hirr h3 (Nat.prime_of_mem_primeFactors p.1.2) hp
      CFSG.pCore_normal CFSG.pCore_isPGroup

theorem isSolvable_of_fittingSubgroup_le_center_of_layer_eq_bot {G : Type*} [Group G] [Finite G]
    (hF : CFSG.fittingSubgroup G ≤ Subgroup.center G) (hL : CFSG.layer G = ⊥) :
    Group.IsSolvable G := by
  have hc : Subgroup.centralizer (CFSG.generalizedFitting G : Set G) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset, CFSG.generalizedFitting.eq_sup, hL, sup_bot_eq]
    exact hF
  have hB := CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup (G := G)
  rw [hc] at hB
  exact Group.isSolvable_of_comm fun a b =>
    (Subgroup.mem_center_iff.mp (hF (hB (Subgroup.mem_top a))) b).symm

private theorem isQuasisimple_of_layer_ne_bot {G : Type*} [Group G]
    (hmin : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hL : CFSG.layer G ≠ ⊥) :
    CFSG.IsQuasisimple G := by
  rw [CFSG.layer.eq_sSup] at hL
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup G, CFSG.IsComponent Q := by
    by_contra h
    exact hL (sSup_eq_bot.mpr fun Q hQ => (h ⟨Q, hQ⟩).elim)
  have hQq := hQ.1
  have hQt : Q = ⊤ := by
    by_contra hne
    have := hmin Q hne
    have := CFSG.LocalCores.isQuasisimple_nontrivial hQq
    have := hQq.1
    exact Group.IsPerfect.not_isSolvable Q ‹_›
  subst hQt
  exact hQq.of_mulEquiv Subgroup.topEquiv.symm

private theorem isSolvable_of_forall_ne_top_isSolvable (hι : Fintype.card ι ≤ 4)
    (hlow : ∀ d < Fintype.card ι, ∀ Y : Subgroup (GL (Fin d) K),
      Nat.Coprime 3 (Nat.card Y) → Group.IsSolvable Y)
    {Y : Subgroup (GL ι K)} (h3 : Nat.Coprime 3 (Nat.card Y))
    (hq : CFSG.IsQuasisimple Y → IsIrreducibleOn Y → 3 ∣ Nat.card Y)
    (hmin : ∀ H : Subgroup Y, H ≠ ⊤ → Group.IsSolvable H) : Group.IsSolvable Y := by
  by_contra hns
  have hirr : IsIrreducibleOn Y :=
    by_contra fun h => hns (isSolvable_of_not_isIrreducibleOn hlow h3 h)
  cases isEmpty_or_nonempty ι with
  | inl _ => exact hns inferInstance
  | inr _ =>
    have hY := isPerfect_of_not_isSolvable hns hmin
    by_cases hL : CFSG.layer Y = ⊥
    · exact hns (isSolvable_of_fittingSubgroup_le_center_of_layer_eq_bot
        (fittingSubgroup_le_center hι hY hirr h3) hL)
    · exact absurd (h3.eq_one_of_dvd (hq (isQuasisimple_of_layer_ne_bot hmin hL) hirr))
        (by norm_num)

end Helpers

theorem isSolvable_of_coprime_three_of_quasisimple {K : Type} [Field K] [Finite K]
    {ι : Type} [Fintype ι] [DecidableEq ι] (hι : Fintype.card ι ≤ 4)
    (hlow : ∀ d < Fintype.card ι, ∀ Y : Subgroup (GL (Fin d) K),
      Nat.Coprime 3 (Nat.card Y) → Group.IsSolvable Y)
    (X : Subgroup (GL ι K)) (h3 : Nat.Coprime 3 (Nat.card X))
    (hq : ∀ Y : Subgroup (GL ι K), Y ≤ X → CFSG.IsQuasisimple Y → IsIrreducibleOn Y →
      3 ∣ Nat.card Y) :
    Group.IsSolvable X := by
  suffices h : ∀ n, ∀ Y : Subgroup (GL ι K), Y ≤ X → Nat.card Y = n → Group.IsSolvable Y from
    h _ X le_rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rintro Y hYX rfl
  refine isSolvable_of_forall_ne_top_isSolvable hι hlow
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hYX) h3) (hq Y hYX) fun H hH => ?_
  have hc : Nat.card (H.map Y.subtype) < Nat.card Y := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective, ← Subgroup.card_top (G := Y)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hH)
  have := ih _ hc _ ((Subgroup.map_subtype_le H).trans hYX) rfl
  exact Group.isSolvable_of_isSolvable_injective
    (f := (H.equivMapOfInjective _ Y.subtype_injective).toMonoidHom) (MulEquiv.injective _)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
