module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

section Trace

variable {W : Type*} [CommGroup W] (P : Subgroup (MulAut W)) [Fintype P]

private def traceOf : W →* W where
  toFun w := ∏ x : P, (x : MulAut W) w
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

private theorem traceOf_apply (w : W) : traceOf P w = ∏ x : P, (x : MulAut W) w := rfl

private theorem traceOf_smul {σ : MulAut W} (hσ : σ ∈ P) (w : W) :
    traceOf P (σ w) = traceOf P w := by
  rw [traceOf_apply, traceOf_apply]
  refine (Fintype.prod_equiv (Equiv.mulRight (⟨σ, hσ⟩ : P)) _ _ fun x => ?_)
  rfl

private theorem traceOf_fixed (hW : ∀ w : W, w ^ 2 = 1) (hP : Odd (Fintype.card P)) {w : W}
    (hw : ∀ x ∈ P, x w = w) : traceOf P w = w := by
  rw [traceOf_apply]
  have : ∀ x : P, (x : MulAut W) w = w := fun x => hw x x.2
  simp only [this, Finset.prod_const, Finset.card_univ]
  obtain ⟨k, hk⟩ := hP
  rw [hk, pow_succ, pow_mul, hW, one_pow, one_mul]

private theorem traceOf_conj {t : MulAut W} (ht : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (ht' : ∀ x ∈ P, t⁻¹ * x * t ∈ P) (w : W) : traceOf P (t w) = t (traceOf P w) := by
  rw [traceOf_apply, traceOf_apply, map_prod]
  let e : P ≃ P :=
    { toFun := fun x => ⟨t⁻¹ * x * t, ht' x x.2⟩
      invFun := fun x => ⟨t * x * t⁻¹, ht x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  refine Fintype.prod_equiv e _ _ fun x => ?_
  show (x : MulAut W) (t w) = t ((t⁻¹ * x * t : MulAut W) w)
  simp [mul_assoc]

end Trace

theorem eq_one_of_odd_normalized_fixed {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {P T' : Subgroup (MulAut W)} (hP : Odd (Nat.card P))
    (hT : IsPGroup 2 T') (hn : ∀ t ∈ T', ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hfix : ∀ w : W, (∀ t ∈ T', t w = w) → ∀ x ∈ P, x w = w) :
    ∀ x ∈ P, ∀ w : W, x w = w := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype W := Fintype.ofFinite W
  have hPc : Odd (Fintype.card P) := by rwa [← Nat.card_eq_fintype_card]
  set D : Subgroup W := (traceOf P).ker with hD
  have hDmem : ∀ w, w ∈ D ↔ traceOf P w = 1 := fun w => MonoidHom.mem_ker
  have hinv : ∀ t ∈ T', ∀ w ∈ D, t w ∈ D := by
    intro t ht w hw
    rw [hDmem] at hw ⊢
    have h1 : traceOf P (t w) = t (traceOf P w) :=
      traceOf_conj P (hn t ht) (fun x hx => by
        have := hn t⁻¹ (T'.inv_mem ht) x hx
        simpa using this) w
    rw [h1, hw, map_one]
  have hDbot : D = ⊥ := by
    by_contra hne
    obtain ⟨d₀, hd₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    let s : Set W := {w | w ∈ D ∧ w ≠ 1}
    have hs : ∀ t ∈ T', ∀ w ∈ s, t w ∈ s := by
      intro t ht w hw
      refine ⟨hinv t ht w hw.1, fun h => hw.2 ?_⟩
      have : (t : MulAut W) w = (t : MulAut W) 1 := by rw [h, map_one]
      exact (t : MulAut W).injective this
    have hD2 : IsPGroup 2 D := fun g => ⟨1, by
      apply Subtype.ext
      simpa using hW (g : W)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hD2
    have hn0 : n ≠ 0 := by
      rintro rfl
      have : Nat.card D = 1 := by simpa using hn
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 this
      exact hd₀1 (hsub.elim d₀ 1)
    have hs_eq : s = (D : Set W) \ {1} := by
      ext w
      simp [s, Set.mem_diff, SetLike.mem_coe]
    have hncard : Nat.card s = 2 ^ n - 1 := by
      have h1 : Nat.card s = s.ncard := (Nat.card_coe_set_eq s)
      have h2 : Nat.card D = (D : Set W).ncard := (Nat.card_coe_set_eq (D : Set W))
      rw [h1, hs_eq, Set.ncard_diff_singleton_of_mem D.one_mem, ← h2, hn]
    have hnd : ¬ 2 ∣ Nat.card s := by
      rw [hncard]
      obtain ⟨m, hm⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 hn0
      have hpos : 0 < 2 ^ n := by positivity
      omega
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let _ : MulAction T' s :=
      { smul := fun t v => ⟨(t : MulAut W) v, hs t t.2 v v.2⟩
        one_smul := fun v => Subtype.ext rfl
        mul_smul := fun p q v => Subtype.ext rfl }
    obtain ⟨⟨v, hv⟩, hfixv⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hT s hnd
    have hvfix : ∀ t ∈ T', (t : MulAut W) v = v := fun t ht =>
      congrArg Subtype.val (MulAction.mem_fixedPoints.mp hfixv ⟨t, ht⟩)
    have h1 := traceOf_fixed P hW hPc (hfix v hvfix)
    rw [(hDmem v).1 hv.1] at h1
    exact hv.2 h1.symm
  intro x hx w
  have h1 : x w * w⁻¹ ∈ D := by
    rw [hDmem, map_mul, map_inv, traceOf_smul P hx]
    exact mul_inv_cancel _
  rw [hDbot, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem exists_odd_pCoreOf_ne_bot {G : Type} [Group G] [Finite G] {Y : Subgroup G} (hY : Y ≠ ⊥)
    (hsub : Y.IsSubnormal) (hC : Y ≤ Subgroup.centralizer ((CFSG.layer G : Subgroup G) : Set G))
    (hO2 : CFSG.Open.pCoreOf 2 Y = ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Open.pCoreOf p Y ≠ ⊥ := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hpc : ∀ p : ℕ, p.Prime → CFSG.pCore p ↥Y = ⊥ := by
    intro p hp
    have h : CFSG.Open.pCoreOf p Y = ⊥ := by
      by_cases h2 : p = 2
      · rw [h2]; exact hO2
      · exact hcon p hp h2
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).1 h
  have hF : CFSG.fittingSubgroup ↥Y = ⊥ := by
    rw [CFSG.fitting_eq_sup_pCore]
    exact le_bot_iff.mp (iSup_le fun p => (hpc p.1.1 (Nat.prime_of_mem_primeFactors p.1.2)).le)
  have hlayer : CFSG.layer ↥Y = ⊥ := by
    refine CFSG.LocalCores.layer_eq_bot_of_forall fun K hK => ?_
    have hK' : CFSG.IsComponent (K.map Y.subtype) :=
      ⟨CFSG.IsQuasisimple.of_mulEquiv (Subgroup.equivMapOfInjective K Y.subtype
        Y.subtype_injective).symm hK.1, CFSG.GroupTheory.isSubnormal_map_subtype hK.2 hsub⟩
    have hKl := CFSG.LocalCores.component_le_layer hK'
    obtain ⟨a, b, hab⟩ := hK.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have ha : ((a' : ↥Y) : G) ∈ Subgroup.centralizer ((CFSG.layer G : Subgroup G) : Set G) :=
      hC a'.1.2
    exact (Subgroup.mem_centralizer_iff.1 ha ((b' : ↥Y) : G) (hKl ⟨b', b'.2, rfl⟩)).symm
  have hFs : CFSG.generalizedFitting ↥Y = ⊥ := by
    rw [CFSG.generalizedFitting.eq_sup, hF, hlayer]; simp
  have htop : (⊤ : Subgroup ↥Y) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc (⊤ : Subgroup ↥Y) ≤ Subgroup.centralizer ((CFSG.generalizedFitting ↥Y : Subgroup ↥Y) : Set ↥Y) := by
          rw [hFs]; intro x _; simp [Subgroup.mem_centralizer_iff]
      _ ≤ CFSG.generalizedFitting ↥Y := CFSG.centralizer_generalizedFitting_le ↥Y
      _ = ⊥ := hFs
  apply hY
  rw [eq_bot_iff]
  intro y hy
  have : (⟨y, hy⟩ : ↥Y) ∈ (⊥ : Subgroup ↥Y) := htop ▸ Subgroup.mem_top _
  have h1 : (⟨y, hy⟩ : ↥Y) = 1 := (Subgroup.mem_bot).1 this
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
