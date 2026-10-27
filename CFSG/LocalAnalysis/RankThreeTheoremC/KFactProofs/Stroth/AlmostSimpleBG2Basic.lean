module

public import CFSG.RankThree.PartOne.S11c.Sec66G2Sub

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.Sec66T
open scoped Pointwise

section Group

theorem exists_sylow_normalized_of_isPGroup {C : Type*} [Group C] [Finite C] {p ℓ : ℕ}
    [Fact p.Prime] [Fact ℓ.Prime] (N : Subgroup C) [N.Normal] (P : Subgroup C)
    (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card N)) :
    ∃ S : Sylow ℓ N, P ≤ Subgroup.normalizer ((S : Subgroup N).map N.subtype : Set C) := by
  classical
  letI : MulAction P (Sylow ℓ N) :=
    MulAction.compHom (Sylow ℓ N) ((MulAut.conjNormal (H := N)).comp P.subtype)
  have hnd : ¬ p ∣ Nat.card (Sylow ℓ N) := by
    intro h
    have h1 : Nat.card (Sylow ℓ N) ∣ Nat.card N := by
      rw [Sylow.card_eq_index_normalizer (default : Sylow ℓ N)]
      exact Subgroup.index_dvd_card _
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (h.trans h1))
  obtain ⟨S, hS⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow ℓ N) hnd
  refine ⟨S, fun g hg => ?_⟩
  have hfix : (⟨g, hg⟩ : P) • S = S := MulAction.mem_fixedPoints.1 hS ⟨g, hg⟩
  have hSub : ∀ s ∈ (S : Subgroup N), (MulAut.conjNormal (H := N) g) s ∈ (S : Subgroup N) := by
    intro s hs
    have h1 : (S : Subgroup N) = (MulAut.conjNormal (H := N) g) • (S : Subgroup N) := by
      have := congrArg (fun T : Sylow ℓ N => (T : Subgroup N)) hfix
      exact this.symm
    have := Subgroup.smul_mem_pointwise_smul s (MulAut.conjNormal (H := N) g) (S : Subgroup N) hs
    rwa [← h1] at this
  refine g2Sub_mem_normalizer fun r hr => ?_
  obtain ⟨s, hs, rfl⟩ := hr
  refine ⟨MulAut.conjNormal (H := N) g s, hSub s hs, ?_⟩
  simp [MulAut.conjNormal_val]

end Group

section BT


theorem card_dvd_of_le_normalizer_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (R : Subgroup (adjointGroup Tag.G2 K)) (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (M : Subgroup (adjointGroup Tag.G2 K)) (hM : M ≤ Subgroup.normalizer (R : Set _)) :
    ∃ n : ℕ, Nat.card M ∣
      Nat.card (torusGroup Tag.G2 K) * Nat.card K ^ n * (1 + Nat.card K) := by
  have hfin : Finite (ModGL Tag.G2 K) := finite_modGL
  have hBC : borelGroup Tag.G2 K ≤ adjointGroup Tag.G2 K := g2Sub_borel_le_adjointGroup
  have hUC : posUnipotent Tag.G2 K ≤ adjointGroup Tag.G2 K := le_sup_right.trans hBC
  obtain ⟨S, P, hPtop, hNR, -, -, hNS⟩ := holds_adjointGroup_tag Tag.G2 K 2 R hR hR2
  obtain ⟨hUp, hUi⟩ := isPGroup_and_not_dvd_index 2 hUC card_posUnipotent
  have hUc := IsPGroup.toSylow_coe hUp hUi
  obtain ⟨g, hg⟩ := g2Sub_exists_conj_le (hUp.toSylow hUi) S
    ((borelGroup Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) P
    (by rw [hUc]; exact g2Sub_borel_le_normalizer) hNS
  have hP₁top : P.comap (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro y _
    have hy : (MulAut.conj g).toMonoidHom ((MulAut.conj g).symm y) ∈ P :=
      Subgroup.mem_comap.1 (h ▸ Subgroup.mem_top _)
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using hy
  obtain ⟨J, hJ, hJP⟩ := g2Sub_exists_parabolic _ hg hP₁top
  obtain ⟨j, hj⟩ := g2Sub_exists_subset_singleton hJ
  obtain ⟨-, -, -, hle, -, -, hcell⟩ := standard_parabolic_cells Tag.G2 K
  let φ : adjointGroup Tag.G2 K →* ModGL Tag.G2 K :=
    (adjointGroup Tag.G2 K).subtype.comp (MulAut.conj g⁻¹).toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp (MulAut.conj g⁻¹).injective
  have hMJ : M.map φ ≤ parabolicSubgroup Tag.G2 K J := by
    rintro _ ⟨y, hy, rfl⟩
    refine hJP (g⁻¹ * y * g⁻¹⁻¹) ?_
    rw [Subgroup.mem_comap]
    have : (MulAut.conj g).toMonoidHom (g⁻¹ * y * g⁻¹⁻¹) = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hNR (hM hy)
  have hMj : M.map φ ≤ parabolicSubgroup Tag.G2 K {j} := hMJ.trans ((hle J {j}).2 hj)
  have hdvd1 : Nat.card M ∣ Nat.card (parabolicSubgroup Tag.G2 K {j}) := by
    rw [← Subgroup.card_map_of_injective hφ]
    exact Subgroup.card_dvd_of_le hMj
  refine ⟨{α : Fin Tag.G2.rank → ℤ | IsRoot Tag.G2 α ∧ 0 < height α}.ncard, ?_⟩
  refine hdvd1.trans ?_
  rw [hcell {j}]
  rcases g2Sub_finsum_parabolicWeyl (Set.Subset.refl ({j} : Set (Fin Tag.G2.rank)))
    (Nat.card K) with hs | hs
  · rw [hs, mul_one]
    exact Dvd.intro (1 + Nat.card K) rfl
  · rw [hs, add_comm]

theorem odd_card_of_normal_of_big_p_part {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (C : Subgroup (adjointGroup Tag.G2 K))
    (hbig : (Nat.card (torusGroup Tag.G2 K) * (1 + Nat.card K)).factorization p <
      (Nat.card C).factorization p)
    (N : Subgroup C) [N.Normal] (hcop : Nat.Coprime p (Nat.card N)) : Odd (Nat.card N) := by
  classical
  by_contra hodd
  have h2 : 2 ∣ Nat.card N := (Nat.not_odd_iff_even.1 hodd).two_dvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow p C) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_normalized_of_isPGroup (ℓ := 2) N (P : Subgroup C)
    P.isPGroup' hcop
  have hSne : (S : Subgroup N) ≠ ⊥ := by
    intro h
    have h1 : Nat.card (S : Subgroup N) = 1 := by rw [h]; simp
    rw [Sylow.card_eq_multiplicity] at h1
    have hf : 1 ≤ (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
    have := Nat.one_lt_pow (by omega : (Nat.card N).factorization 2 ≠ 0) (by norm_num : 1 < 2)
    omega
  set A : Subgroup C := (S : Subgroup N).map N.subtype with hA
  set R : Subgroup (adjointGroup Tag.G2 K) := A.map C.subtype with hR
  have hR2 : IsPGroup 2 R := by
    intro x
    obtain ⟨_, ⟨s, hs, rfl⟩, hx⟩ := x.2
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hx, ← map_pow, ← map_pow, hk', map_one, map_one]
  have hRne : R ≠ ⊥ := by
    intro h
    apply hSne
    have h1 : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective A C.subtype_injective).1 h
    exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).1 h1
  have hMR : (P : Subgroup C).map C.subtype ≤ Subgroup.normalizer (R : Set _) :=
    (Subgroup.map_mono hS).trans (Subgroup.le_normalizer_map C.subtype)
  obtain ⟨n, hn⟩ := card_dvd_of_le_normalizer_two R hRne hR2 _ hMR
  rw [Subgroup.card_map_of_injective C.subtype_injective, Sylow.card_eq_multiplicity] at hn
  have hcopq : Nat.Coprime (p ^ (Nat.card C).factorization p) (Nat.card K ^ n) :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpK).pow _ _
  have hn' : p ^ (Nat.card C).factorization p ∣
      Nat.card (torusGroup Tag.G2 K) * (1 + Nat.card K) := by
    refine hcopq.dvd_of_dvd_mul_right ?_
    have : Nat.card (torusGroup Tag.G2 K) * Nat.card K ^ n * (1 + Nat.card K) =
        Nat.card (torusGroup Tag.G2 K) * (1 + Nat.card K) * Nat.card K ^ n := by ring
    rwa [this] at hn
  have hne : Nat.card (torusGroup Tag.G2 K) * (1 + Nat.card K) ≠ 0 := by
    have : 0 < Nat.card (torusGroup Tag.G2 K) := Nat.card_pos
    positivity
  have := (hp.pow_dvd_iff_le_factorization hne).1 hn'
  omega

end BT


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
