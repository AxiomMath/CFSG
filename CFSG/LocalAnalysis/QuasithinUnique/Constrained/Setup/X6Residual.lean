module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.ABGLocalTools
open scoped commutatorElement

section DInf

variable {G : Type*} [Group G]

@[expose] def dInf (M : Subgroup G) : Subgroup G := (CFSG.perfectResidual ↥M).map M.subtype

theorem dInf_le (M : Subgroup G) : dInf M ≤ M := Subgroup.map_subtype_le _

theorem dInf_isPerfect [Finite G] (M : Subgroup G) : Group.IsPerfect (dInf M) :=
  CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect M

theorem le_dInf_of_perfect {R Q : Subgroup G} (hR : Group.IsPerfect R) (hRQ : R ≤ Q) :
    R ≤ dInf Q :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf R Q hR hRQ

theorem dInf_eq_of_commutator_le [Finite G] {M Q : Subgroup G} (hMQ : M ≤ Q)
    (hc : ⁅Q, Q⁆ ≤ M) : dInf M = dInf Q := by
  apply le_antisymm
  · exact le_dInf_of_perfect (dInf_isPerfect M) ((dInf_le M).trans hMQ)
  · have hperf := dInf_isPerfect Q
    have hle : dInf Q ≤ M := by
      calc dInf Q = ⁅dInf Q, dInf Q⁆ := (Subgroup.isPerfect_iff.mp hperf).symm
        _ ≤ ⁅Q, Q⁆ := Subgroup.commutator_mono (dInf_le Q) (dInf_le Q)
        _ ≤ M := hc
    exact le_dInf_of_perfect hperf hle

theorem map_isPerfect {G' : Type*} [Group G'] {R : Subgroup G} (hR : Group.IsPerfect R)
    (f : G →* G') : Group.IsPerfect (R.map f) := by
  rw [Subgroup.isPerfect_iff] at hR ⊢
  rw [← Subgroup.map_commutator, hR]

theorem dInf_map_le {G' : Type*} [Group G'] [Finite G] (e : G ≃* G') (M : Subgroup G) :
    (dInf M).map e.toMonoidHom ≤ dInf (M.map e.toMonoidHom) :=
  le_dInf_of_perfect (map_isPerfect (dInf_isPerfect M) _) (Subgroup.map_mono (dInf_le M))

theorem dInf_map_equiv {G' : Type*} [Group G'] [Finite G] [Finite G'] (e : G ≃* G')
    (M : Subgroup G) : dInf (M.map e.toMonoidHom) = (dInf M).map e.toMonoidHom := by
  apply le_antisymm
  · have h := dInf_map_le e.symm (M.map e.toMonoidHom)
    rw [map_symm_map] at h
    have h2 := Subgroup.map_mono (f := e.toMonoidHom) h
    rw [Subgroup.map_map] at h2
    have e1 : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by ext x; simp
    rw [e1, Subgroup.map_id] at h2
    exact h2
  · exact dInf_map_le e M

end DInf

theorem map_isSolvable_equiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (M : Subgroup S)
    (hs : Group.IsSolvable ↥M) : Group.IsSolvable ↥(M.map e.toMonoidHom) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective).symm.toMonoidHom)
    (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective).symm.injective

theorem isSolvable_of_map_equiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (M : Subgroup S) (hs : Group.IsSolvable ↥(M.map e.toMonoidHom)) : Group.IsSolvable ↥M :=
  Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective).injective

section Residual

variable {G : Type*} [Group G]

theorem no_swap_of_odd_order {A B : Subgroup G} (hAB : A ≠ B) (α : MulAut G)
    (hodd : Odd (orderOf α)) (hB : B.map α.toMonoidHom = A ∨ B.map α.toMonoidHom = B)
    (h : A.map α.toMonoidHom = B) : False := by
  have hBA : B.map α.toMonoidHom = A := by
    rcases hB with hB | hB
    · exact hB
    · exact absurd (Subgroup.map_injective α.injective (h.trans hB.symm)) hAB
  have h2 : A.map (α * α).toMonoidHom = A := by
    rw [CFSG.LieType.Chevalley.map_mulAut_mul, h, hBA]
  have h2n : ∀ n : ℕ, A.map ((α * α) ^ n).toMonoidHom = A := by
    intro n
    induction n with
    | zero => rw [pow_zero]; exact CFSG.LieType.Chevalley.map_mulAut_one A
    | succ n ih => rw [pow_succ', CFSG.LieType.Chevalley.map_mulAut_mul, ih, h2]
  obtain ⟨k, hk⟩ := hodd
  have hpow : α ^ (orderOf α) = 1 := pow_orderOf_eq_one α
  have hm : α ^ orderOf α = α * (α * α) ^ k := by rw [hk, pow_succ', pow_mul, sq]
  have : A.map (α ^ orderOf α).toMonoidHom = A := by
    rw [hpow]; exact CFSG.LieType.Chevalley.map_mulAut_one A
  rw [hm, CFSG.LieType.Chevalley.map_mulAut_mul, h2n, h] at this
  exact hAB this.symm

variable [Finite G]

theorem residual_abstract {U : Subgroup G} {P N : Fin 2 → Subgroup G}
    (hne : P 0 ≠ P 1) (hUP : ∀ j, U ≤ P j)
    (hmax : ∀ M : Subgroup G, U ≤ M → (M ⋖ ⊤ ↔ ∃ j, M = P j))
    (hsolv : Group.IsSolvable ↥(P 0 ⊓ P 1))
    (hc : ∀ j, ⁅P j, P j⁆ ≤ N j)
    (hns : ∀ j, ∀ M : Subgroup G, U ≤ M → M ≤ P j → ¬ Group.IsSolvable ↥M → N j ≤ M) :
    (∀ M : Subgroup G, U ≤ M → M ≠ ⊤ → ¬ Group.IsSolvable ↥M →
      ∃ j, (∀ k, M ≤ P k ↔ k = j) ∧ dInf M = dInf (P j)) ∧
    ∀ α : MulAut G, Odd (orderOf α) → U.map α.toMonoidHom = U →
      ∀ M : Subgroup G, U ≤ M → M ≠ ⊤ → ¬ Group.IsSolvable ↥M →
        (dInf M).map α.toMonoidHom = dInf M := by
  have hC2 : ∀ M : Subgroup G, U ≤ M → M ≠ ⊤ → ¬ Group.IsSolvable ↥M →
      ∃ j, (∀ k, M ≤ P k ↔ k = j) ∧ dInf M = dInf (P j) := by
    intro M hUM hMt hMns
    obtain ⟨M', hMM', hM'⟩ := exists_le_covBy_of_lt (lt_top_iff_ne_top.2 hMt)
    obtain ⟨j, hj⟩ := (hmax M' (hUM.trans hMM')).1 hM'
    have hMj : M ≤ P j := hj ▸ hMM'
    refine ⟨j, fun k => ⟨fun hk => ?_, fun hk => hk ▸ hMj⟩, ?_⟩
    · by_contra hkj
      apply hMns
      have hinf : M ≤ P 0 ⊓ P 1 := by
        fin_cases j <;> fin_cases k
        · exact absurd rfl hkj
        · exact le_inf hMj hk
        · exact le_inf hk hMj
        · exact absurd rfl hkj
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hinf)
        (Subgroup.inclusion_injective hinf)
    · exact dInf_eq_of_commutator_le hMj ((hc j).trans (hns j M hUM hMj hMns))
  refine ⟨hC2, fun α hodd hα M hUM hMt hMns => ?_⟩
  have hperm : ∀ j, ∃ k, (P j).map α.toMonoidHom = P k := by
    intro j
    have hcov : (P j).map α.toMonoidHom ⋖ ⊤ := by
      have h := (apply_covBy_apply_iff (MulEquiv.mapSubgroup α)).2
        ((hmax (P j) (hUP j)).2 ⟨j, rfl⟩)
      rwa [show (MulEquiv.mapSubgroup α) (⊤ : Subgroup G) = ⊤ from
        Subgroup.map_top_of_surjective _ α.surjective] at h
    have hU' : U ≤ (P j).map α.toMonoidHom := by
      rw [← hα]
      exact Subgroup.map_mono (hUP j)
    obtain ⟨k, hk⟩ := (hmax _ hU').1 hcov
    exact ⟨k, hk⟩
  have hfix : ∀ j, (P j).map α.toMonoidHom = P j := by
    intro j
    obtain ⟨k, hk⟩ := hperm j
    by_cases hjk : j = k
    · subst hjk; exact hk
    · exfalso
      fin_cases j <;> fin_cases k
      · exact hjk rfl
      · obtain ⟨k', hk'⟩ := hperm 1
        have hB : (P 1).map α.toMonoidHom = P 0 ∨ (P 1).map α.toMonoidHom = P 1 := by
          fin_cases k'
          · exact Or.inl hk'
          · exact Or.inr hk'
        exact no_swap_of_odd_order hne α hodd hB hk
      · obtain ⟨k', hk'⟩ := hperm 0
        have hB : (P 0).map α.toMonoidHom = P 1 ∨ (P 0).map α.toMonoidHom = P 0 := by
          fin_cases k'
          · exact Or.inr hk'
          · exact Or.inl hk'
        exact no_swap_of_odd_order hne.symm α hodd hB hk
      · exact hjk rfl
  obtain ⟨j, hjk, hdM⟩ := hC2 M hUM hMt hMns
  have hMα : M.map α.toMonoidHom ≤ P j := by
    rw [← hfix j]
    exact Subgroup.map_mono ((hjk j).2 rfl)
  have hUα : U ≤ M.map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono hUM
  have hMαt : M.map α.toMonoidHom ≠ ⊤ := by
    intro h
    apply hMt
    have h2 := congrArg (Subgroup.map α.symm.toMonoidHom) h
    rw [map_symm_map α M, Subgroup.map_top_of_surjective _ α.symm.surjective] at h2
    exact h2
  have hMαns : ¬ Group.IsSolvable ↥(M.map α.toMonoidHom) := fun hs =>
    hMns (isSolvable_of_map_equiv α M hs)
  obtain ⟨j', hjk', hdMα⟩ := hC2 _ hUα hMαt hMαns
  have hjj : j' = j := ((hjk' j).1 hMα).symm
  rw [← dInf_map_equiv α, hdMα, hjj, ← hdM]

end Residual

@[expose] def ResidualOvergroupsAt (S : Type*) [Group S] (U : Subgroup S) (P : Fin 2 → Subgroup S) :
    Prop :=
  P 0 ≠ P 1 ∧ (∀ j, U ≤ P j) ∧
    (∀ M : Subgroup S, U ≤ M → (M ⋖ ⊤ ↔ ∃ j, M = P j)) ∧ Group.IsSolvable ↥(P 0 ⊓ P 1) ∧
    (∀ M : Subgroup S, U ≤ M → M ≠ ⊤ → ¬ Group.IsSolvable ↥M →
      ∃ j, (∀ k, M ≤ P k ↔ k = j) ∧ dInf M = dInf (P j)) ∧
    ∀ α : MulAut S, Odd (orderOf α) → U.map α.toMonoidHom = U →
      ∀ M : Subgroup S, U ≤ M → M ≠ ⊤ → ¬ Group.IsSolvable ↥M →
        (dInf M).map α.toMonoidHom = dInf M

@[expose] def ResidualOvergroups (S : Type*) [Group S] (U : Subgroup S) : Prop :=
  ∃ P : Fin 2 → Subgroup S, ResidualOvergroupsAt S U P

theorem ResidualOvergroupsAt.map {S S' : Type*} [Group S] [Group S'] [Finite S] [Finite S']
    {U : Subgroup S} {P : Fin 2 → Subgroup S} (h : ResidualOvergroupsAt S U P) (e : S ≃* S') :
    ResidualOvergroupsAt S' (U.map e.toMonoidHom) (fun j => (P j).map e.toMonoidHom) := by
  obtain ⟨hne, hUP, hmax, hsolv, hC2, hC3⟩ := h
  have key : ∀ x y : Subgroup S, x.map e.toMonoidHom ⋖ y.map e.toMonoidHom ↔ x ⋖ y :=
    fun x y => apply_covBy_apply_iff (MulEquiv.mapSubgroup e)
  have hback : ∀ M' : Subgroup S', ∃ M : Subgroup S, M' = M.map e.toMonoidHom := fun M' =>
    ⟨M'.map e.symm.toMonoidHom, by
      have := map_symm_map e.symm M'
      simpa using this.symm⟩
  have hmapTop : ∀ M : Subgroup S, M.map e.toMonoidHom = ⊤ ↔ M = ⊤ := fun M => by
    constructor
    · intro h
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [h, Subgroup.map_top_of_surjective _ e.surjective]
    · rintro rfl
      exact Subgroup.map_top_of_surjective _ e.surjective
  refine ⟨?_, fun j => Subgroup.map_mono (hUP j), ?_, ?_, ?_, ?_⟩
  · intro hEq
    exact hne (Subgroup.map_injective (f := e.toMonoidHom) e.injective hEq)
  · intro M' hUM'
    obtain ⟨M, rfl⟩ := hback M'
    have hUM : U ≤ M := (Subgroup.map_le_map_iff_of_injective e.injective).1 hUM'
    rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective, key, hmax M hUM]
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, Subgroup.map_injective (f := e.toMonoidHom) e.injective hj⟩
  · rw [← Subgroup.map_inf_eq _ _ _ e.injective]
    exact map_isSolvable_equiv e _ hsolv
  · intro M' hUM' hMt hMns
    obtain ⟨M, rfl⟩ := hback M'
    have hUM : U ≤ M := (Subgroup.map_le_map_iff_of_injective e.injective).1 hUM'
    obtain ⟨j, hj, hd⟩ := hC2 M hUM (fun h => hMt ((hmapTop M).2 h))
      (fun hs => hMns (map_isSolvable_equiv e M hs))
    refine ⟨j, fun k => ?_, ?_⟩
    · rw [Subgroup.map_le_map_iff_of_injective e.injective]
      exact hj k
    · rw [dInf_map_equiv, hd, dInf_map_equiv]
  · intro α' hodd hα' M' hUM' hMt hMns
    obtain ⟨M, rfl⟩ := hback M'
    set α : MulAut S := e.trans (α'.trans e.symm) with hα
    have hαo : orderOf α = orderOf α' := by
      have : α = (MulAut.congr e.symm) α' := rfl
      rw [this]
      exact MulEquiv.orderOf_eq _ _
    have hαU : U.map α.toMonoidHom = U := by
      have h := hα'
      rw [map_comm_equiv] at h
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h
    have hUM : U ≤ M := (Subgroup.map_le_map_iff_of_injective e.injective).1 hUM'
    have h1 := hC3 α (hαo ▸ hodd) hαU M hUM (fun h => hMt ((hmapTop M).2 h))
      (fun hs => hMns (map_isSolvable_equiv e M hs))
    rw [dInf_map_equiv, map_comm_equiv, ← hα, h1]

theorem ResidualOvergroups.map {S S' : Type*} [Group S] [Group S'] [Finite S] [Finite S']
    {U : Subgroup S} (h : ResidualOvergroups S U) (e : S ≃* S') :
    ResidualOvergroups S' (U.map e.toMonoidHom) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨_, hP.map e⟩

theorem ResidualOvergroupsAt.exists_iso_of_isSylow {S S' : Type*} [Group S] [Group S']
    [Finite S] [Finite S'] (e : S ≃* S') {U₀ : Subgroup S'} {P₀ : Fin 2 → Subgroup S'}
    (h₀ : ResidualOvergroupsAt S' U₀ P₀) (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    {U : Subgroup S} (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ φ : S ≃* S', U.map φ.toMonoidHom = U₀ ∧
      ResidualOvergroupsAt S U (fun j => (P₀ j).map φ.symm.toMonoidHom) := by
  have hU' : IsSylowOf 2 (U.map e.toMonoidHom) ⊤ := by
    have := isSylowOf_map_injective (p := 2) e.toMonoidHom e.injective
      (isSylowTwoOf_iff_isSylowOf.1 hU)
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj hU'
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U.map e.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  set φ : S ≃* S' := e.trans (MulAut.conj k).symm with hφ
  have hφU : U.map φ.toMonoidHom = U₀ := by
    have : U.map φ.toMonoidHom = (U.map e.toMonoidHom).map (MulAut.conj k).symm.toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [this, ← hconj]
    exact map_symm_map (MulAut.conj k) U₀
  refine ⟨φ, hφU, ?_⟩
  have h1 := h₀.map φ.symm
  have hUU : U₀.map φ.symm.toMonoidHom = U := by
    rw [← hφU]
    exact map_symm_map φ U
  rwa [hUU] at h1

theorem ResidualOvergroups.of_isSylow {S S' : Type*} [Group S] [Group S'] [Finite S] [Finite S']
    (e : S ≃* S') {U₀ : Subgroup S'} (h₀ : ResidualOvergroups S' U₀)
    (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤) {U : Subgroup S}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : ResidualOvergroups S U := by
  obtain ⟨P₀, hP₀⟩ := h₀
  obtain ⟨φ, -, h⟩ := hP₀.exists_iso_of_isSylow e hU₀ hU
  exact ⟨_, h⟩

theorem commutator_le_of_sup_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    ⁅H ⊔ N, H ⊔ N⁆ ≤ N := by
  have hconj : ∀ a ∈ H, ∀ m ∈ N, a * m * a⁻¹ ∈ N := fun a ha m hm =>
    (Subgroup.mem_normalizer_iff.1 (hHN ha) m).1 hm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H N hHN] at hx hy
  obtain ⟨h, hh, n, hn, rfl⟩ := hx
  obtain ⟨h', hh', n', hn', rfl⟩ := hy
  have hc : h'⁻¹ * h⁻¹ * h' = h⁻¹ := by
    calc h'⁻¹ * h⁻¹ * h' = (h * h')⁻¹ * h' := by group
      _ = (h' * h)⁻¹ * h' := by rw [hcomm h hh h' hh']
      _ = h⁻¹ := by group
  have e : ⁅h * n, h' * n'⁆ = (h * n * h⁻¹) * ((h * h') * n' * (h * h')⁻¹) *
      ((h * h') * n⁻¹ * (h * h')⁻¹) * (h' * n'⁻¹ * h'⁻¹) := by
    rw [commutatorElement_def]
    calc h * n * (h' * n') * (h * n)⁻¹ * (h' * n')⁻¹
        = h * n * h' * n' * n⁻¹ * (h⁻¹ * n'⁻¹ * h'⁻¹) := by group
      _ = h * n * h' * n' * n⁻¹ * ((h'⁻¹ * h⁻¹ * h') * n'⁻¹ * h'⁻¹) := by rw [hc]
      _ = _ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem (hconj h hh n hn) (hconj _ (mul_mem hh hh') n' hn'))
    (hconj _ (mul_mem hh hh') _ (inv_mem hn))) (hconj h' hh' _ (inv_mem hn'))

section Ambient

variable {M : Type} [Group M]

theorem covBy_top_iff_map_subtype {C : Subgroup M} (M' : Subgroup C) :
    M' ⋖ ⊤ ↔ M'.map C.subtype ⋖ C := by
  have hAC : M'.map C.subtype ≤ C := Subgroup.map_subtype_le M'
  have hAeq : M' = (M'.map C.subtype).subgroupOf C :=
    (Subgroup.comap_map_eq_self_of_injective C.subtype_injective M').symm
  conv_lhs => rw [hAeq, ← Subgroup.subgroupOf_self C]
  exact subgroupOf_covBy_iff hAC le_rfl

theorem residualOvergroupsAt_of_ambient [Finite M] {C U : Subgroup M} {P N : Fin 2 → Subgroup M}
    (hUC : U ≤ C) (hPC : ∀ j, P j ≤ C) (hUP : ∀ j, U ≤ P j) (hne : P 0 ≠ P 1)
    (hmax : ∀ A : Subgroup M, U ≤ A → A ≤ C → (A ⋖ C ↔ ∃ j, A = P j))
    (hsolv : Group.IsSolvable ↥(P 0 ⊓ P 1))
    (hc : ∀ j, ⁅P j, P j⁆ ≤ N j)
    (hns : ∀ j, ∀ A : Subgroup M, U ≤ A → A ≤ P j → ¬ Group.IsSolvable ↥A → N j ≤ A) :
    ResidualOvergroupsAt C (U.subgroupOf C) (fun j => (P j).subgroupOf C) := by
  have hne' : (P 0).subgroupOf C ≠ (P 1).subgroupOf C := fun h => hne (by
    have := congrArg (Subgroup.map C.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le (hPC 0), Subgroup.map_subgroupOf_eq_of_le (hPC 1)]
      at this)
  have hUP' : ∀ j, U.subgroupOf C ≤ (P j).subgroupOf C := fun j x hx => hUP j hx
  have hmax' : ∀ M' : Subgroup C, U.subgroupOf C ≤ M' →
      (M' ⋖ ⊤ ↔ ∃ j, M' = (P j).subgroupOf C) := by
    intro M' hUM'
    have hAC : M'.map C.subtype ≤ C := Subgroup.map_subtype_le M'
    have hAeq : M' = (M'.map C.subtype).subgroupOf C :=
      (Subgroup.comap_map_eq_self_of_injective C.subtype_injective M').symm
    have hUA : U ≤ M'.map C.subtype := by
      have := Subgroup.map_mono (f := C.subtype) hUM'
      rwa [Subgroup.map_subgroupOf_eq_of_le hUC] at this
    rw [covBy_top_iff_map_subtype, hmax _ hUA hAC]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨j, hAeq.trans (by rw [hj])⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, by rw [hj, Subgroup.map_subgroupOf_eq_of_le (hPC j)]⟩
  have hsolv' : Group.IsSolvable ↥((P 0).subgroupOf C ⊓ (P 1).subgroupOf C) := by
    have hle : P 0 ⊓ P 1 ≤ C := inf_le_left.trans (hPC 0)
    have : (P 0).subgroupOf C ⊓ (P 1).subgroupOf C = (P 0 ⊓ P 1).subgroupOf C :=
      (Subgroup.comap_inf _ _ _).symm
    rw [this]
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom) (MulEquiv.injective _)
  have hc' : ∀ j, ⁅(P j).subgroupOf C, (P j).subgroupOf C⁆ ≤ (N j).subgroupOf C := by
    intro j
    refine Subgroup.map_le_iff_le_comap.1 ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hPC j)]
    exact hc j
  have hns' : ∀ j, ∀ M' : Subgroup C, U.subgroupOf C ≤ M' → M' ≤ (P j).subgroupOf C →
      ¬ Group.IsSolvable ↥M' → (N j).subgroupOf C ≤ M' := by
    intro j M' hUM' hMP hMns
    have hAeq : M' = (M'.map C.subtype).subgroupOf C :=
      (Subgroup.comap_map_eq_self_of_injective C.subtype_injective M').symm
    have hUA : U ≤ M'.map C.subtype := by
      have := Subgroup.map_mono (f := C.subtype) hUM'
      rwa [Subgroup.map_subgroupOf_eq_of_le hUC] at this
    have hAP : M'.map C.subtype ≤ P j := by
      have := Subgroup.map_mono (f := C.subtype) hMP
      rwa [Subgroup.map_subgroupOf_eq_of_le (hPC j)] at this
    have hAns : ¬ Group.IsSolvable ↥(M'.map C.subtype) := fun hs => hMns
      (Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective M' C.subtype C.subtype_injective).toMonoidHom)
        (MulEquiv.injective _))
    have hN := hns j _ hUA hAP hAns
    rw [hAeq]
    exact fun x hx => hN hx
  obtain ⟨h2, h3⟩ := residual_abstract (G := C) (U := U.subgroupOf C)
    (P := fun j => (P j).subgroupOf C) (N := fun j => (N j).subgroupOf C) hne' hUP' hmax' hsolv'
    hc' hns'
  exact ⟨hne', hUP', hmax', hsolv', h2, h3⟩

theorem inf_eq_of_covBy {α : Type*} [Lattice α] {B P₁ P₂ : α} (h₁ : B ⋖ P₁) (h₂ : B ⋖ P₂)
    (hne : P₁ ≠ P₂) : P₁ ⊓ P₂ = B := by
  have h1 : P₁ ⊓ P₂ ≤ P₁ := inf_le_left
  have hB : B ≤ P₁ ⊓ P₂ := le_inf h₁.le h₂.le
  rcases h₁.eq_or_eq hB h1 with h | h
  · exact h
  · exfalso
    have hP₁₂ : P₁ ≤ P₂ := h.symm.le.trans inf_le_right
    rcases h₂.eq_or_eq h₁.le hP₁₂ with h' | h'
    · exact h₁.ne h'.symm
    · exact hne h'

theorem maximal_overgroups_of_covers {C U B P₁ P₂ : Subgroup M} (hB₁ : B ⋖ P₁) (hB₂ : B ⋖ P₂)
    (hP₁ : P₁ ≤ C) (hP₂ : P₂ ≤ C) (h₁ : P₁ ≠ C) (h₂ : P₂ ≠ C)
    (hcont : ∀ A : Subgroup M, U ≤ A → A ≤ C → A ≠ C → A ≤ P₁ ∨ A ≤ P₂) :
    ∀ A : Subgroup M, U ≤ A → A ≤ C → (A ⋖ C ↔ A = P₁ ∨ A = P₂) := by
  have hlt₁ : P₁ < C := lt_of_le_of_ne hP₁ h₁
  have hlt₂ : P₂ < C := lt_of_le_of_ne hP₂ h₂
  intro A hUA hAC
  constructor
  · intro hA
    rcases hcont A hUA hAC hA.ne with h | h
    · left
      exact (h.eq_or_lt.resolve_right fun hlt => hA.2 hlt hlt₁)
    · right
      exact (h.eq_or_lt.resolve_right fun hlt => hA.2 hlt hlt₂)
  · rintro (rfl | rfl)
    · refine ⟨hlt₁, fun c hc hcC => ?_⟩
      rcases hcont c (hUA.trans hc.le) hcC.le hcC.ne with h | h
      · exact lt_irrefl _ (hc.trans_le h)
      · exact hB₂.2 hB₁.lt (hc.trans_le h)
    · refine ⟨hlt₂, fun c hc hcC => ?_⟩
      rcases hcont c (hUA.trans hc.le) hcC.le hcC.ne with h | h
      · exact hB₁.2 hB₂.lt (hc.trans_le h)
      · exact lt_irrefl _ (hc.trans_le h)

theorem residualOvergroupsAt_of_two_covers [Finite M] {C U B : Subgroup M}
    {P N : Fin 2 → Subgroup M} (hUC : U ≤ C) (hPC : ∀ j, P j ≤ C) (hUP : ∀ j, U ≤ P j)
    (hne : P 0 ≠ P 1) (hcov : ∀ j, B ⋖ P j)
    (hcont : ∀ A : Subgroup M, U ≤ A → A ≤ C → A ≠ C → A ≤ P 0 ∨ A ≤ P 1)
    (hB : Group.IsSolvable ↥B) (hc : ∀ j, ⁅P j, P j⁆ ≤ N j)
    (hns : ∀ j, ∀ A : Subgroup M, U ≤ A → A ≤ P j → ¬ Group.IsSolvable ↥A → N j ≤ A) :
    ResidualOvergroupsAt C (U.subgroupOf C) (fun j => (P j).subgroupOf C) := by
  have hne' : ∀ j : Fin 2, P (j + 1) ≠ P j := by
    intro j
    fin_cases j
    · exact fun h => hne h.symm
    · exact fun h => hne h
  have hPne : ∀ j, P j ≠ C := by
    intro j h
    have hlt : P (j + 1) < P j := lt_of_le_of_ne ((hPC (j + 1)).trans_eq h.symm) (hne' j)
    exact (hcov j).2 (hcov (j + 1)).lt hlt
  have hmax : ∀ A : Subgroup M, U ≤ A → A ≤ C → (A ⋖ C ↔ ∃ j, A = P j) := by
    intro A hUA hAC
    rw [maximal_overgroups_of_covers (hcov 0) (hcov 1) (hPC 0) (hPC 1) (hPne 0) (hPne 1) hcont
      A hUA hAC]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨j, hj⟩
      fin_cases j
      · exact Or.inl hj
      · exact Or.inr hj
  have hsolv : Group.IsSolvable ↥(P 0 ⊓ P 1) := by
    rw [inf_eq_of_covBy (hcov 0) (hcov 1) hne]
    exact hB
  exact residualOvergroupsAt_of_ambient hUC hPC hUP hne hmax hsolv hc hns

end Ambient

end CFSG.QuasithinUnique.Setup.X6
