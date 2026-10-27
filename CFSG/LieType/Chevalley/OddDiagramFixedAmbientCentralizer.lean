module

public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley Polynomial

theorem list_prod_ofFn_sum {A : Type*} [Semiring A] {β : Type*} [Fintype β] :
    ∀ {d : ℕ} (u : Fin d → β → A),
      (List.ofFn fun j => ∑ n, u j n).prod = ∑ e : Fin d → β, (List.ofFn fun j => u j (e j)).prod
  | 0, _ => by simp
  | d + 1, u => by
    rw [List.ofFn_succ, List.prod_cons, list_prod_ofFn_sum fun j => u j.succ, Finset.sum_mul_sum,
      ← (Fin.consEquiv fun _ => β).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
    rw [List.ofFn_succ, List.prod_cons]
    simp [Fin.consEquiv]

theorem list_prod_ofFn_pow_smul {L A : Type*} [CommSemiring L] [Semiring A] [Algebra L A]
    (q : ℕ) : ∀ {d : ℕ} (x : L) (e : Fin d → ℕ) (B : Fin d → A),
      (List.ofFn fun j => (x ^ q ^ (j : ℕ)) ^ e j • B j).prod =
        x ^ Nat.ofDigits q (List.ofFn e) • (List.ofFn B).prod
  | 0, _, _, _ => by simp
  | d + 1, x, e, B => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.ofFn_succ, List.prod_cons,
      Nat.ofDigits_cons]
    have h : ∀ j : Fin d, x ^ q ^ ((j.succ : Fin (d + 1)) : ℕ) = (x ^ q) ^ q ^ (j : ℕ) :=
      fun j => by rw [Fin.val_succ, pow_succ', pow_mul]
    simp only [h]
    rw [list_prod_ofFn_pow_smul q (x ^ q) (fun j => e j.succ) (fun j => B j.succ),
      smul_mul_smul_comm, Fin.val_zero, pow_zero, pow_one, ← pow_mul, ← pow_add]

theorem list_prod_ofFn_eq_of_ne_one {M : Type*} [Monoid M] :
    ∀ {d : ℕ} (g : Fin d → M) (j : Fin d), (∀ j', j' ≠ j → g j' = 1) → (List.ofFn g).prod = g j
  | 0, _, j, _ => j.elim0
  | d + 1, g, j, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases j using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨j', rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero j')
    | succ j =>
      rw [h 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact list_prod_ofFn_eq_of_ne_one (fun j' => g j'.succ) j fun j' hj' =>
        h _ fun e => hj' (Fin.succ_injective _ e)

theorem eq_zero_of_forall_sum_pow_smul_eq_zero {L E κ ι' : Type*} [Field L] [AddCommGroup E]
    [Module L E] [Fintype κ] [Fintype ι'] {N : κ → ℕ} (hN : Function.Injective N)
    (hlt : ∀ e, N e < Fintype.card ι') {f : ι' → L} (hf : Function.Injective f) {D : κ → E}
    (h : ∀ i, ∑ e, f i ^ N e • D e = 0) (e : κ) : D e = 0 := by
  classical
  refine (Module.forall_dual_apply_eq_zero_iff L (D e)).1 fun φ => ?_
  set P : L[X] := ∑ e', C (φ (D e')) * X ^ N e' with hP
  have hdeg : P.natDegree < Fintype.card ι' := by
    have hpos : 0 < Fintype.card ι' := lt_of_le_of_lt (Nat.zero_le _) (hlt e)
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ fun e' _ => ?_)
      (Nat.sub_lt hpos one_pos)
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_sub_one_of_lt (hlt e'))
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hf (fun i => ?_) hdeg
    have := congrArg φ (h i)
    rw [map_sum, map_zero] at this
    rw [hP, eval_finsetSum, ← this]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X, map_smul, smul_eq_mul, mul_comm]
  have hc := congrArg (fun p : L[X] => p.coeff (N e)) hP0
  simp only [hP, finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at hc
  rwa [Finset.sum_eq_single e (fun e' _ he' => ite_eq_right fun h => he' (hN h).symm)
    (fun h => absurd (Finset.mem_univ e) h), ite_eq_left rfl] at hc

theorem commute_coeff_of_commute_twisted_prod {L E : Type*} [Field L] [Ring E] [Algebra L E]
    {q d : ℕ} (hq : 3 ≤ q) (X : Fin d → Fin 3 → E) (hX : ∀ j, X j 0 = 1) {ι' : Type*}
    [Fintype ι'] {f : ι' → L} (hf : Function.Injective f) (hcard : q ^ d ≤ Fintype.card ι')
    {z : E} (hz : ∀ i, Commute z
      (List.ofFn fun j => ∑ n : Fin 3, (f i ^ q ^ (j : ℕ)) ^ (n : ℕ) • X j n).prod)
    (j : Fin d) (n : Fin 3) : Commute z (X j n) := by
  classical
  set N : (Fin d → Fin 3) → ℕ := fun e => Nat.ofDigits q (List.ofFn fun j => (e j : ℕ))
  set C : (Fin d → Fin 3) → E := fun e => (List.ofFn fun j => X j (e j)).prod
  have hexp : ∀ x : L,
      (List.ofFn fun j => ∑ n : Fin 3, (x ^ q ^ (j : ℕ)) ^ (n : ℕ) • X j n).prod =
        ∑ e, x ^ N e • C e := fun x => by
    rw [list_prod_ofFn_sum]
    exact Finset.sum_congr rfl fun e _ =>
      list_prod_ofFn_pow_smul q x (fun j => (e j : ℕ)) (fun j => X j (e j))
  have hdig : ∀ e : Fin d → Fin 3, ∀ l ∈ List.ofFn fun j => (e j : ℕ), l < q := fun e l hl => by
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hl
    exact lt_of_lt_of_le (e j).isLt hq
  have hN : Function.Injective N := fun e e' h => by
    have := Nat.ofDigits_inj_of_len_eq (by omega) (by simp) (hdig e) (hdig e') h
    funext j
    exact Fin.ext (congrFun (List.ofFn_injective this) j)
  have hlt : ∀ e, N e < Fintype.card ι' := fun e =>
    lt_of_lt_of_le (by simpa using Nat.ofDigits_lt_base_pow_length (by omega) (hdig e)) hcard
  have hD := eq_zero_of_forall_sum_pow_smul_eq_zero hN hlt hf (D := fun e => z * C e - C e * z)
    (fun i => by
      have h := (hz i).eq
      rw [hexp, Finset.mul_sum, Finset.sum_mul, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h
      rw [← h]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [smul_sub, mul_smul_comm, smul_mul_assoc])
    (Pi.single j n)
  have hC : C (Pi.single j n) = X j n := by
    refine (list_prod_ofFn_eq_of_ne_one _ j fun j' hj' => ?_).trans (by simp)
    rw [Pi.single_eq_of_ne hj', hX]
  rw [← hC]
  exact sub_eq_zero.1 hD

section Orbit

variable {t : TwistTag} {L : Type} [Field L]

theorem entryDegreeBound_twistTag (t : TwistTag) : entryDegreeBound t.tag = 2 := by
  cases t <;> rfl

theorem xOp_eq_sum_fin_three
    (i : Fin t.tag.rank) (s : L) :
    xOp t.tag L i s = ∑ n : Fin 3, s ^ (n : ℕ) • xCoeff t.tag L i n := by
  rw [xOp_eq_sum_xCoeff_entryDegreeBound, entryDegreeBound_twistTag, Finset.sum_range]

theorem yOp_eq_sum_fin_three
    (i : Fin t.tag.rank) (s : L) :
    yOp t.tag L i s = ∑ n : Fin 3, s ^ (n : ℕ) • yCoeff t.tag L i n := by
  rw [yOp_eq_sum_yCoeff_entryDegreeBound, entryDegreeBound_twistTag, Finset.sum_range]

theorem commute_coeff_of_commute_orbit_prod {q : ℕ} (hq : 3 ≤ q) (a : Fin t.foldedTag.rank)
    (Y : Fin t.tag.rank → Fin 3 → Module.End L (RootModule t.tag L)) (hY : ∀ i, Y i 0 = 1)
    {ι' : Type*} [Fintype ι'] {f : ι' → L} (hf : Function.Injective f)
    (hcard : q ^ (t.orbit a).card ≤ Fintype.card ι') {z : Module.End L (RootModule t.tag L)}
    (hz : ∀ c, Commute z ((List.range (t.orbit a).card).map fun k =>
      ∑ n : Fin 3, (f c ^ q ^ k) ^ (n : ℕ) • Y ((t.perm ^ k) (t.orbitMin a)) n).prod)
    {i : Fin t.tag.rank} (hi : i ∈ t.orbit a) (n : Fin 3) : Commute z (Y i n) := by
  obtain ⟨k, hk, rfl⟩ := t.exists_eq_perm_pow_orbitMin hi
  refine commute_coeff_of_commute_twisted_prod hq
    (fun j n => Y ((t.perm ^ (j : ℕ)) (t.orbitMin a)) n) (fun j => hY _) hf hcard
    (fun c => ?_) ⟨k, hk⟩ n
  have e : ((List.range (t.orbit a).card).map fun k =>
      ∑ n : Fin 3, (f c ^ q ^ k) ^ (n : ℕ) • Y ((t.perm ^ k) (t.orbitMin a)) n) =
        List.ofFn fun j : Fin (t.orbit a).card => ∑ n : Fin 3,
          (f c ^ q ^ (j : ℕ)) ^ (n : ℕ) • Y ((t.perm ^ (j : ℕ)) (t.orbitMin a)) n := by
    apply List.ext_getElem <;> simp
  rw [← e]
  exact hz c

variable {K : Type} [Field K] (σ : K →+* K) (ι : K →+* L)

theorem coe_baseChangeGL_orbitX
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    ((baseChangeGL ι (orbitX t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
        Module.End L (RootModule t.tag L)) =
      ((List.range (t.orbit a).card).map fun k =>
        xOp t.tag L ((t.perm ^ k) (t.orbitMin a)) (ι ((σ ^ k) (c : K)))).prod := by
  rw [coe_orbitX, map_list_prod, List.map_map, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, Units.coeHom_apply, baseChangeGL_xUnit, coe_xUnit]

theorem coe_baseChangeGL_orbitY
    (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    ((baseChangeGL ι (orbitY t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
        Module.End L (RootModule t.tag L)) =
      ((List.range (t.orbit a).card).map fun k =>
        yOp t.tag L ((t.perm ^ k) (t.orbitMin a)) (ι ((σ ^ k) (c : K)))).prod := by
  rw [coe_orbitY, map_list_prod, List.map_map, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, Units.coeHom_apply, baseChangeGL_yUnit, coe_yUnit]

end Orbit

theorem odd_diagram_fixed_ambient_centralizer_trivial
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (L : Type) [Field L] (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := t.tag) ι) ∧
    (graphFixedRootGroup t K σ).map (baseChangeGL ι) ≤ adjointGroup t.tag L ∧
    (∀ z ∈ adjointGroup t.tag L, (∀ h ∈ (graphFixedRootGroup t K σ).map (baseChangeGL ι),
      z * h = h * z) → z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup t.tag L)
      ((graphFixedRootGroup t K σ).map (baseChangeGL ι))) := by
  classical
  set q := p ^ f with hqdef
  set H := (graphFixedRootGroup t K σ).map (baseChangeGL ι) with hHdef
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (pow_pos hp.pos f) _).ne')
  have hq3 : 3 ≤ q := by
    have hq2 : 2 ≤ q := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    obtain ⟨m, hm⟩ := hodd
    omega
  have hHle : H ≤ adjointGroup t.tag L := by
    rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι
      (twistedFixedGroup_le_adjointGroup t K σ (graphFixedRootGroup_le t K σ hg))
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have hσσ' : σ'.toRingHom = σ := RingHom.ext fun c => by
    change σ' c = σ c
    rw [hσ', hσ]
  have hcardL : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card := fun a => by
    rw [← hσσ']
    exact hcard a
  have hgen : ∀ z : Module.End L (RootModule t.tag L),
      (∀ a (c : orbitField t K σ a),
        Commute z ((baseChangeGL ι (orbitX t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
          Module.End L (RootModule t.tag L)) ∧
        Commute z ((baseChangeGL ι (orbitY t K σ a c : ModGL t.tag K) : ModGL t.tag L) :
          Module.End L (RootModule t.tag L))) →
      ∀ (i : Fin t.tag.rank) (s : L), Commute z (xOp t.tag L i s) ∧
        Commute z (yOp t.tag L i s) := by
    intro z hz i s
    set a := t.orbitIndex i
    have : Fintype (orbitField t K σ a) := Fintype.ofFinite _
    have hf' : Function.Injective fun c : orbitField t K σ a => ι c :=
      ι.injective.comp Subtype.val_injective
    have hcard' : q ^ (t.orbit a).card ≤ Fintype.card (orbitField t K σ a) := by
      rw [← Nat.card_eq_fintype_card, hcardL]
    have hpow : ∀ (c : orbitField t K σ a) (k : ℕ), ι ((σ ^ k) (c : K)) = ι c ^ q ^ k :=
      fun c k => by rw [pow_apply_eq_pow hσ, map_pow]
    refine ⟨?_, ?_⟩
    · have hX : ∀ n : Fin 3, Commute z (xCoeff t.tag L i n) :=
        commute_coeff_of_commute_orbit_prod hq3 a (fun i (n : Fin 3) => xCoeff t.tag L i n)
          (fun _ => xCoeff_zero _) hf'
          hcard' (fun c => by
            have h := (hz a c).1
            rw [coe_baseChangeGL_orbitX] at h
            simpa only [hpow, xOp_eq_sum_fin_three] using h)
          (t.mem_orbit_orbitIndex i)
      rw [xOp_eq_sum_fin_three]
      exact Commute.sum_right _ _ _ fun n _ => (hX n).smul_right _
    · have hY : ∀ n : Fin 3, Commute z (yCoeff t.tag L i n) :=
        commute_coeff_of_commute_orbit_prod hq3 a (fun i (n : Fin 3) => yCoeff t.tag L i n)
          (fun _ => yCoeff_zero _) hf'
          hcard' (fun c => by
            have h := (hz a c).2
            rw [coe_baseChangeGL_orbitY] at h
            simpa only [hpow, yOp_eq_sum_fin_three] using h)
          (t.mem_orbit_orbitIndex i)
      rw [yOp_eq_sum_fin_three]
      exact Commute.sum_right _ _ _ fun n _ => (hY n).smul_right _
  have hcentral : ∀ z ∈ adjointGroup t.tag L,
      (∀ (i : Fin t.tag.rank) (s : L), Commute (z : Module.End L (RootModule t.tag L))
        (xOp t.tag L i s) ∧ Commute (z : Module.End L (RootModule t.tag L)) (yOp t.tag L i s)) →
      z = 1 := by
    intro z hzC hzg
    have hcent : ⟨z, hzC⟩ ∈ Subgroup.center (adjointGroup t.tag L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hle : adjointGroup t.tag L ≤ Subgroup.centralizer {z} := by
        rw [adjointGroup, Subgroup.closure_le]
        rintro g ⟨i, c, hg | hg⟩ <;>
          refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
          rw [Units.val_mul, Units.val_mul, hg]
        · exact (hzg i c).1.eq.symm
        · exact (hzg i c).2.eq.symm
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hcentralizer : ∀ z ∈ adjointGroup t.tag L, (∀ h ∈ H, z * h = h * z) → z = 1 := by
    intro z hzC hz
    refine hcentral z hzC (hgen z fun a c => ⟨?_, ?_⟩)
    · have h1 := hz _ (Subgroup.mem_map_of_mem _ (graphFixedPosUnipotent_le_graphFixedRootGroup
        t K σ (orbitX_mem_graphFixedPosUnipotent t σ a c)))
      exact congrArg Units.val h1
    · have h1 := hz _ (Subgroup.mem_map_of_mem _ (graphFixedNegUnipotent_le_graphFixedRootGroup
        t K σ (orbitY_mem_graphFixedNegUnipotent t σ a c)))
      exact congrArg Units.val h1
  refine ⟨baseChangeGL_injective ι, hHle, hcentralizer, ?_⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  apply Subtype.ext
  refine hcentralizer g (Subgroup.mem_inf.1 g.2).1 fun h hh => ?_
  have h1 := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : ModGL t.tag L)) hg
  simp only [conjNormalizerHom_apply, MulAut.one_apply] at h1
  calc (g : ModGL t.tag L) * h = (g * h * (g : ModGL t.tag L)⁻¹) * g := by group
    _ = h * g := by rw [h1]

end CFSG.LieType.Chevalley
