module

public import CFSG.Assembly.DichotomyDefs
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOneAutomorphisms
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.Assembly.Dichotomy

private theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {E X : Subgroup G}
    (hE : IsElemAbelian p E) (hXE : X ≤ E) : IsElemAbelian p X :=
  CFSG.Open.IsElemAbelian.mono hE hXE

private theorem card_frattini_quotient_le_four (Q : Type*) [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (hrank : CFSG.pRank 2 Q ≤ 1) :
    Nat.card (Q ⧸ frattini Q) ≤ 4 := by
  rcases (CFSG.LocalAnalysis.ComponentInitial.pgroup_rank_one_classification Nat.prime_two
    hQ).mp hrank with hcyc | ⟨-, n, -, ⟨e⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (IsPGroup 2 Q) := ⟨hQ⟩
    have : IsCyclic (Q ⧸ frattini Q) :=
      isCyclic_of_surjective (QuotientGroup.mk' (frattini Q)) (QuotientGroup.mk'_surjective _)
    have hexp : Monoid.exponent (Q ⧸ frattini Q) ∣ 2 := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      intro x
      induction x using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact CFSG.pth_power_mem_frattini_of_isPGroup y
    rw [← IsCyclic.exponent_eq_card]
    exact (Nat.le_of_dvd (by decide) hexp).trans (by decide)
  · let φ : QuaternionGroup (2 ^ (n - 2)) →* Q := e.symm.toMonoidHom
    have hφ : Function.Surjective φ := e.symm.surjective
    let ψ := (QuotientGroup.mk' (frattini Q)).comp φ
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
    have hker : frattini (QuaternionGroup (2 ^ (n - 2))) ≤ ψ.ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact frattini_le_comap_frattini_of_surjective hφ
    exact (Nat.card_le_card_of_surjective _
      (QuotientGroup.lift_surjective_of_surjective _ ψ hψ hker)).trans
      (CFSG.ProperTwoGeneratedCore.quaternion_frattini_quotient_card_le_four (n - 2))

private def nonidentityPerm (V : Type*) [Group V] :
    MulAut V →* Equiv.Perm {v : V // v ≠ 1} where
  toFun σ := Equiv.Perm.subtypePerm σ.toEquiv fun _ => σ.map_ne_one_iff
  map_one' := Equiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := Equiv.ext fun _ => Subtype.ext rfl

private theorem nonidentityPerm_apply (V : Type*) [Group V] (σ : MulAut V)
    (v : {v : V // v ≠ 1}) : ((nonidentityPerm V σ v : {v : V // v ≠ 1}) : V) = σ v :=
  rfl

private theorem nonidentityPerm_injective (V : Type*) [Group V] :
    Function.Injective (nonidentityPerm V) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [Subgroup.mem_bot]
  apply MulEquiv.ext
  intro v
  by_cases hv : v = 1
  · rw [hv, map_one, map_one]
  · have h := congrArg Subtype.val (Equiv.ext_iff.mp hσ ⟨v, hv⟩)
    rw [nonidentityPerm_apply] at h
    exact h

private theorem card_le_two_of_isPGroup_mulAut {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V ≤ 4) (A : Subgroup (MulAut V)) (hA : IsPGroup 2 A) :
    Nat.card A ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hA.exists_card_eq
  have hsub : Nat.card {v : V // v ≠ 1} ≤ 3 := by
    have := Finite.card_subtype_lt (p := fun v : V => v ≠ 1) (x := 1) (by simp)
    omega
  have hdvd : Nat.card A ∣ 6 := by
    have h1 : Nat.card A ∣ Nat.card (Equiv.Perm {v : V // v ≠ 1}) :=
      Subgroup.card_dvd_of_injective ((nonidentityPerm V).comp A.subtype)
        ((nonidentityPerm_injective V).comp Subtype.val_injective)
    rw [Nat.card_perm] at h1
    exact h1.trans ((Nat.factorial_dvd_factorial hsub).trans (by decide))
  rw [hk] at hdvd ⊢
  rcases k with _ | _ | k
  · decide
  · decide
  · have h4 : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 (by omega)).trans hdvd
    exact absurd h4 (by decide)

theorem twoRank_le_two_of_charP_two_core_rank_le_one (H : Type*) [Group H] [Finite H]
    (hchar : dichotomyCharP 2 H) (hcore : pRank 2 (pCore 2 H) ≤ 1) : twoRank H ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup H := pCore 2 H with hQdef
  have : Q.Normal := by rw [hQdef]; infer_instance
  have hQp : IsPGroup 2 Q := by rw [hQdef]; exact CFSG.pCore_isPGroup
  have hmax : ∀ N : Subgroup H, N.Normal → IsPGroup 2 N → N ≤ Q := fun N hN hp =>
    le_sSup ⟨hN, hp⟩
  have hQrank : CFSG.pRank 2 Q ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hcore
  have hV : Nat.card (Q ⧸ frattini Q) ≤ 4 := card_frattini_quotient_le_four Q hQp hQrank
  have hconj : (MulAut.conjNormal : H →* MulAut Q).ker ≤ Q := by
    intro h hh
    refine hchar (Subgroup.mem_centralizer_iff.mpr fun q hq => ?_)
    have hfix := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : H)) (MonoidHom.mem_ker.mp hh)
    change h * q * h⁻¹ = q at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hKp : IsPGroup 2
      ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).comp
        (MulAut.conjNormal : H →* MulAut Q)).ker := by
    rw [← MonoidHom.comap_ker]
    exact IsPGroup.comap_of_ker_isPGroup
      (CFSG.LargeEvenClassification.Helpers.frattiniAutAction_isPGroup_ker Q Nat.prime_two hQp)
      _ (hQp.to_le hconj)
  have hKQ := hmax _ inferInstance hKp
  have hbound : ∀ E : Subgroup H, E ≤ ⊤ → CFSG.Open.IsElemAbelian 2 E →
      Nat.card E ≤ 2 ^ 2 := by
    intro E _ hE
    let f : E →* MulAut (Q ⧸ frattini Q) :=
      ((CFSG.LargeEvenClassification.Helpers.frattiniAutAction Q).comp
        (MulAut.conjNormal : H →* MulAut Q)).comp E.subtype
    have hker : Nat.card f.ker ≤ 2 := by
      have hXQ : f.ker.map E.subtype ≤ Q := by
        rintro _ ⟨x, hx, rfl⟩
        exact hKQ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
      have hX : IsElemAbelian 2 (f.ker.map E.subtype) :=
        isElemAbelian_of_le hE (Subgroup.map_subtype_le _)
      have hXp : IsPGroup 2 (f.ker.map E.subtype) := fun x =>
        ⟨1, Subtype.ext (by simpa using hX.2 x x.2)⟩
      obtain ⟨k, hk⟩ := hXp.exists_card_eq
      have hk1 : k ≤ 1 := (CFSG.SectionRank.le_pRank one_lt_two hXQ hX hk).trans hcore
      rw [← Subgroup.card_map_of_injective (K := f.ker) E.subtype_injective, hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 2 := by norm_num
    have hrange : Nat.card f.range ≤ 2 := by
      refine card_le_two_of_isPGroup_mulAut hV f.range fun y => ?_
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
      have hx2 : x ^ 2 = 1 := Subtype.ext (hE.2 x x.2)
      refine ⟨1, Subtype.ext ?_⟩
      rw [pow_one, Subgroup.coe_pow, ← hx, ← map_pow, hx2, map_one]
      rfl
    calc Nat.card E = Nat.card f.ker * Nat.card f.range :=
          (Subgroup.card_ker_mul_card_range f).symm
      _ ≤ 2 * 2 := Nat.mul_le_mul hker hrange
      _ = 2 ^ 2 := by norm_num
  exact CFSG.SectionRank.pRank_le one_lt_two hbound

theorem two_le_pRank_pCore_of_charP_two (H : Type*) [Group H] [Finite H]
    (hchar : dichotomyCharP 2 H) (hrank : 3 ≤ twoRank H) : 2 ≤ pRank 2 (pCore 2 H) := by
  by_contra h
  have := twoRank_le_two_of_charP_two_core_rank_le_one H hchar (by omega)
  omega

end CFSG.Assembly.Dichotomy
