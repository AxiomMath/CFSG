module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabStated
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabInvol
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOne
public import CFSG.LieType.Steinberg.CentralExt.UnitaryRootGroups
import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.Universal.Unitary.Extras

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.Steinberg CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

section Equiv

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

theorem borelQuotient_of_stated_equiv [Finite F] [CharP F 2] {H : Subgroup (GL ι F)}
    {K Y : Type} [Group K] [Group Y] (ψ : K ≃* ↥H) (e : Y ≃* StatedProj H)
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {T : Fin D.rank → Subgroup K}
    (ct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n T)
    (extras : SteinbergExtras D n T) (pGroup : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    (torus_pow : ∀ i, ∀ g ∈ T i, g ^ (Nat.card F - 1) = 1) :
    BorelQuotient D n T
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp ψ.toMonoidHom)) (Nat.card F - 1) where
  ct := ct
  extras := extras
  pGroup := pGroup
  surj := e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp ψ.surjective)
  odd := odd_card_sub_one F
  torus_pow := torus_pow
  ker_central := fun z hz => by
    have h1 : (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) (ψ z) = 1 :=
      e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
    have h2 := Subgroup.mem_center_iff.1 (mk_eq_one_mem_center H h1)
    rw [Subgroup.mem_center_iff]
    intro g
    apply ψ.injective
    rw [map_mul, map_mul]
    exact h2 (ψ g)
  ker_pow := fun z hz => by
    have h1 : (QuotientGroup.mk' ((StatedScalars ι F).subgroupOf H)) (ψ z) = 1 :=
      e.symm.injective (by rw [map_one]; exact MonoidHom.mem_ker.1 hz)
    exact ψ.injective (by rw [map_pow, map_one]; exact mk_eq_one_pow H h1)

end Equiv

section Torus

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n : ℕ}

theorem diag_pow_eq_one {g : SU σ n} (hg : g ∈ diagSubgroup σ n) : g ^ (Nat.card F - 1) = 1 := by
  obtain ⟨t, ht⟩ := hg
  have := Fintype.ofFinite F
  have hu : IsUnit ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det :=
    Matrix.isUnits_det_units _
  rw [ht, Matrix.det_diagonal] at hu
  have ht0 : ∀ i, t i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.1 hu.ne_zero) i (Finset.mem_univ i)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ht, Matrix.diagonal_pow,
    Nat.card_eq_fintype_card]
  change _ = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rw [Units.val_one, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact FiniteField.pow_card_sub_one_eq_one _ (ht0 i)

end Torus

section Last

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
  {k : Fin (n / 2)}

omit [CharP F 2] in
theorem longRootHom_mem_heisenberg {i m : Fin n} (hi : i ≠ Fin.rev i) (him : i ≠ m)
    (hm : Fin.rev m = m) (c : Multiplicative (traceZero σ)) :
    longRootHom σ hi c ∈ heisenbergSubgroup σ hσ hi him hm := by
  refine ⟨0, (c.toAdd : F), ?_, ?_⟩
  · rw [map_zero, zero_mul, add_zero]
    exact c.toAdd.2
  · rw [coe_longRootHom, longRootMatrix, heisenbergMatrix]
    simp

omit [CharP F 2] in
theorem longRootHom_mem_last (hk : ¬k.val + 1 < n / 2) (c : Multiplicative (traceZero σ)) :
    longRootHom σ (lowIdx_ne_rev k k) c ∈ rootGroup σ hσ n (Pi.single k 1) ∧
      longRootHom σ (rev_ne_rev_rev (lowIdx_ne_rev k k)) c ∈
        rootGroup σ hσ n (-Pi.single k 1) := by
  by_cases he : Even n
  · exact ⟨longRootHom_mem hσ _ (toStd_last_even hk he).symm c,
      longRootHom_mem hσ _ (toStd_neg_last_even hk he).symm c⟩
  · have hm := rev_midIdx he
    have hk' := k.isLt
    have h1 : lowIdx k ≠ midIdx n he := Fin.ne_of_val_ne (by simp only [lowIdx, midIdx]; omega)
    have h2 : Fin.rev (lowIdx k) ≠ midIdx n he := Fin.ne_of_val_ne (by
      simp only [Fin.val_rev, lowIdx, midIdx]
      rw [Nat.not_even_iff_odd] at he
      obtain ⟨r, hr⟩ := he
      omega)
    exact ⟨heisenberg_le hσ _ h1 hm (toStd_last_odd hk he).symm
        (longRootHom_mem_heisenberg hσ _ h1 hm c),
      heisenberg_le hσ _ h2 hm (toStd_neg_last_odd hk he).symm
        (longRootHom_mem_heisenberg hσ _ h2 hm c)⟩

theorem hasOrderThree_su_last (hk : ¬k.val + 1 < n / 2) :
    ∃ x ∈ rootGroup σ hσ n (Pi.single k 1), ∃ y ∈ rootGroup σ hσ n (-Pi.single k 1),
      (x * y) ^ 3 = 1 ∧ ∃ c : SU σ n, x * y * c ≠ c * (x * y) := by
  have h11 : (1 : F) ∈ traceZero σ := by
    rw [mem_traceZero, map_one]
    exact CharTwo.add_self_eq_zero 1
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hp : lowIdx k ≠ Fin.rev (lowIdx k) := lowIdx_ne_rev k k
  have hp' := rev_ne_rev_rev hp
  obtain ⟨hxm, hym⟩ := longRootHom_mem_last hσ hk (Multiplicative.ofAdd ⟨1, h11⟩)
  set p : Fin n := lowIdx k with hpdef
  set x : SU σ n := longRootHom σ hp (Multiplicative.ofAdd ⟨1, h11⟩) with hx
  set y : SU σ n := longRootHom σ hp' (Multiplicative.ofAdd ⟨1, h11⟩) with hy
  set a : Matrix (Fin n) (Fin n) F := Matrix.single p (Fin.rev p) 1 with ha
  set b : Matrix (Fin n) (Fin n) F := Matrix.single (Fin.rev p) p 1 with hb
  have hxmat : ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + a := rfl
  have hymat : ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + b := by
    change 1 + Matrix.single (Fin.rev p) (Fin.rev (Fin.rev p)) 1 = _
    rw [Fin.rev_rev]
  have hrp : Fin.rev p ≠ p := hp.symm
  have ha2 : a + a = 0 := by
    rw [ha, ← Matrix.single_add, h2, Matrix.single_zero]
  have hb2 : b + b = 0 := by
    rw [hb, ← Matrix.single_add, h2, Matrix.single_zero]
  have haa : a * a = 0 := by
    rw [ha]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hrp _
  have hbb : b * b = 0 := by
    rw [hb]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hp _
  have hab : a * b = Matrix.single p p 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have hba : b * a = Matrix.single (Fin.rev p) (Fin.rev p) 1 := by
    rw [ha, hb, Matrix.single_mul_single_same, mul_one]
  have haba : a * b * a = a := by
    rw [hab, ha, Matrix.single_mul_single_same, mul_one]
  have hbab : b * a * b = b := by
    rw [hba, hb, Matrix.single_mul_single_same, mul_one]
  obtain ⟨hx2, hy2, hbraid, hxyx⟩ := braid_of_rels ha2 hb2 haa hbb haba hbab
  have hx2' : x * x = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hxmat]; exact hx2))
  have hy2' : y * y = 1 :=
    Subtype.ext (Units.ext (by rw [Subgroup.coe_mul, Units.val_mul, hymat]; exact hy2))
  have hbraid' : x * y * x = y * x * y :=
    Subtype.ext (Units.ext (by
      simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat]
      exact hbraid))
  refine ⟨x, hxm, y, hym, cube_eq_one_of_braid hx2' hy2' hbraid', x, fun h => ?_⟩
  have h' := congrArg (fun g : SU σ n => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, hxmat, hymat] at h'
  rw [hxyx, ← mul_assoc, hx2, one_mul] at h'
  have h'' := congrFun (congrFun h' p) p
  simp [ha, hb, hrp, h2] at h''

end Last

section Short

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {k : Fin (n / 2)}
  (hk : k.val + 1 < n / 2)

include hk in
theorem exists_sl2_short :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* SU σ n, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) ∈ rootGroup σ hσ n (Pi.single k 1)) ∧
      ∀ c, φ (sl2Lower c) ∈ rootGroup σ hσ n (-Pi.single k 1) := by
  set e := rankOneShortEquiv (hσ := hσ) hk with he
  set p : Fin n := lowIdx k with hpdef
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩ with hqdef
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hp : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hq : q ≠ Fin.rev q := lowIdx_ne_rev _ _
  have hqp : q ≠ Fin.rev p := lowIdx_ne_rev _ _
  have hpq' : p ≠ Fin.rev q := lowIdx_ne_rev _ _
  refine ⟨(Subgroup.subtype _).comp e.symm.toMonoidHom,
    Subtype.val_injective.comp e.symm.injective, fun c => ?_, fun c => ?_⟩
  · have hx := rootHom_mem hσ hpq hp hq hqp (toStd_short hk).symm (Multiplicative.ofAdd c)
    have key : e ⟨_, Subgroup.mem_sup_left hx⟩ = sl2Upper c := by
      apply Subtype.ext
      change ((rankOneShortHom hk ⟨_, Subgroup.mem_sup_left hx⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [coe_rankOneShortHom, toBlock_of_mem_pos hk hx, mat_apply, coe_rootHom, toAdd_ofAdd,
        rootMatrix_apply_pq hpq hqp, coe_sl2Upper]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_eq.2 key.symm,
      Subgroup.coe_subtype]
    exact hx
  · have hy := rootHom_mem hσ hpq.symm hq hp hpq' (toStd_short_neg hk).symm
      (Multiplicative.ofAdd c)
    have key : e ⟨_, Subgroup.mem_sup_right hy⟩ = sl2Lower c := by
      apply Subtype.ext
      change ((rankOneShortHom hk ⟨_, Subgroup.mem_sup_right hy⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
      rw [coe_rankOneShortHom, toBlock_of_mem_neg hk hy, mat_apply, coe_rootHom, toAdd_ofAdd,
        rootMatrix_apply_pq hpq.symm hpq', coe_sl2Lower]
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_eq.2 key.symm,
      Subgroup.coe_subtype]
    exact hy

end Short

section Unitary

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem hasSL2Node_su_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    HasSL2Node (rootDatum hF n) k F := by
  obtain ⟨φ, hφ, hx, hy⟩ := exists_sl2_short (unitaryInvolution_involutive hF) hk
  exact ⟨φ, hφ, hx, hy⟩

theorem hasOrderThree_su (i : Fin (n / 2)) : HasOrderThree (rootDatum hF n) i := by
  by_cases hk : i.val + 1 < n / 2
  · exact (hasSL2Node_su_short hF hk).hasOrderThree
  · obtain ⟨x, hx, y, hy, h3, c, hc⟩ :=
      hasOrderThree_su_last (unitaryInvolution_involutive hF) hk
    exact ⟨x, hx, y, hy, h3, c, hc⟩

theorem borelQuotient_su (hn : 2 ≤ n) (ζ : traceZero (unitaryInvolution F 2 f))
    (hζ : (ζ : F) ≠ 0) {Y : Type} [Group Y] (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) :
    BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F 2 f))
      (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (equivStatedSU hF n).toMonoidHom))
      (Nat.card F - 1) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  exact borelQuotient_of_stated_equiv (equivStatedSU hF n) e (isCTGroupDatum hF n hn ζ hζ)
    (steinbergExtras hF n hn ζ hζ)
    (fun _ hγ => isPGroup_rootGroup (unitaryInvolution_involutive hF)
      (toStd_ne_zero_of_mem_roots hγ))
    (fun k _ hg => diag_pow_eq_one (levelTorus_le_diagSubgroup k hg))

include hF in
theorem threeDvd_su (hn : 2 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  exact (borelQuotient_su hF hn ζ hζ e).three_dvd_card (fun i => hasOrderThree_su hF i) T J hNJ hJ

end Unitary

theorem threeDvd_of_model_psu {Y : Type} [Group Y] [Finite Y] {n f : ℕ}
    (h : StatedClassicalModel Y .PSU n 2 f) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) : 3 ∣ Nat.card J := by
  obtain ⟨⟨-, -, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  exact threeDvd_su hcard (by omega) e T J hNJ hJ

end CFSG.AGLEmbedding.ParabHub
