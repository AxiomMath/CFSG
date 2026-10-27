module

public import CFSG.LieType.Chevalley.GraphFixedCommonBaseField
public import CFSG.LieType.Chevalley.GraphFixedE6CubesOdd
public import CFSG.LieType.Chevalley.GraphFixedF4Intertwiner

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LocalAnalysis.ComponentInitial (ringAut_mul_comm)
open Matrix

theorem ringEquiv_comm_of_finite {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K) (c : K) :
    δ (σ c) = σ (δ c) :=
  congrArg (fun e : RingAut K => e c) (ringAut_mul_comm K δ σ)

theorem ringHom_pow_comm {K : Type} [Field K] {σ : K →+* K} {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) (n : ℕ) (c : K) : δ ((σ ^ n) c) = (σ ^ n) (δ c) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, RingHom.coe_mul, Function.comp_apply, Function.comp_apply, ih, hδ]

variable {t : TwistTag} {K : Type} [Field K]

theorem mem_orbitField_iff_ringEquiv {σ : K →+* K} {δ : K ≃+* K}
    (hδ : ∀ c, δ (σ c) = σ (δ c)) (a : Fin t.foldedTag.rank) (x : K) :
    x ∈ orbitField t K σ a ↔ δ x ∈ orbitField t K σ a := by
  rw [mem_orbitField, mem_orbitField, ← ringHom_pow_comm hδ]
  exact ⟨fun h => by rw [h], fun h => δ.injective h⟩

variable (t) in
@[expose] def orbitFieldRestrict [Finite K] (σ δ : K ≃+* K) (a : Fin t.foldedTag.rank) :
    orbitField t K σ.toRingHom a ≃+* orbitField t K σ.toRingHom a :=
  δ.restrict _ _ (mem_orbitField_iff_ringEquiv (ringEquiv_comm_of_finite σ δ) a)

theorem coe_orbitFieldRestrict [Finite K] (σ δ : K ≃+* K) (a : Fin t.foldedTag.rank)
    (c : orbitField t K σ.toRingHom a) : (orbitFieldRestrict t σ δ a c : K) = δ c :=
  rfl

theorem commute_orbitX_of_rootForm
    {σ : K →+* K} {a b : Fin t.foldedTag.rank}
    (h : ∀ i ∈ t.orbit a, ∀ j ∈ t.orbit b, (Pi.single i 1 : Fin t.tag.rank → ℤ) ⬝ᵥ
      (t.tag.symmetrizedCartan *ᵥ (Pi.single j 1 : Fin t.tag.rank → ℤ)) = 0)
    (c : orbitField t K σ a) (d : orbitField t K σ b) :
    Commute (orbitX t K σ a c : ModGL t.tag K) (orbitX t K σ b d : ModGL t.tag K) := by
  rw [coe_orbitX, coe_orbitX]
  refine Commute.list_prod_left _ _ fun x hx => Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hy
  rw [← pinnedX_single, ← pinnedX_single]
  exact commute_pinnedX_of_rootForm_eq_zero K (isRoot_single _ _) (isRoot_single _ _)
    (h _ (t.perm_pow_mem_orbit (t.orbitMin_mem a) k) _
      (t.perm_pow_mem_orbit (t.orbitMin_mem b) l)) _ _

theorem single_dotProduct_mulVec_single {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (Pi.single i 1 : Fin n → ℤ) ⬝ᵥ (B *ᵥ (Pi.single j 1 : Fin n → ℤ)) = B i j := by
  simp [Matrix.mulVec_single]

theorem commute_orbitX_E6
    {σ : K →+* K} {a b : Fin TwistTag.E6.foldedTag.rank}
    (h : ∀ i ∈ TwistTag.E6.orbit a, ∀ j ∈ TwistTag.E6.orbit b,
      TwistTag.E6.tag.symmetrizedCartan i j = 0)
    (c : orbitField TwistTag.E6 K σ a) (d : orbitField TwistTag.E6 K σ b) :
    Commute (orbitX TwistTag.E6 K σ a c : ModGL TwistTag.E6.tag K)
      (orbitX TwistTag.E6 K σ b d : ModGL TwistTag.E6.tag K) :=
  commute_orbitX_of_rootForm (fun i hi j hj => by
    rw [single_dotProduct_mulVec_single]
    exact h i hi j hj) c d

theorem xOp_one_vecOf
    (R : Type) [CommRing R] (i : Fin Tag.E6.rank) {v : List (ℕ × ℤ)}
    (hv : ValidVec .E6 v) :
    xOp .E6 R i 1 (vecOf .E6 R v) =
      vecOf .E6 R ((List.range 4).flatMap fun k => coeffVec .E6 false i k v) ∧
    ValidVec .E6 ((List.range 4).flatMap fun k => coeffVec .E6 false i k v) := by
  refine ⟨?_, ?_⟩
  · rw [xOp_eq_sum_xCoeff, LinearMap.sum_apply, vecOf_flatMap_range]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [one_pow, one_smul]
    exact (coeffOp_vecOf simpleRow_E6 e6_allValid R false i (Finset.mem_range.1 hk) hv).1
  · intro x hx
    obtain ⟨k, hk, hx⟩ := List.mem_flatMap.1 hx
    exact (coeffOp_vecOf simpleRow_E6 e6_allValid R false i (List.mem_range.1 hk) hv).2 x hx

theorem vecOf_apply_posLabel
    {τ : Tag} {R : Type*} [CommRing R] {L : List (ℕ × ℤ)}
    (hL : ValidVec τ L) {q : ℕ} (hq : q < dim τ) :
    vecOf τ R L (posLabel q hq) = (((L.filter fun x => x.1 == q).map Prod.snd).sum : ℤ) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx : x.1 < dim τ := hL x List.mem_cons_self
    rw [vecOf_cons, Finsupp.add_apply, Finsupp.smul_apply, posVec_eq_single hx,
      ih fun y hy => hL y (List.mem_cons_of_mem _ hy), List.filter_cons]
    by_cases hxq : x.1 = q
    · subst hxq
      simp
    · have hne : posLabel x.1 hx ≠ posLabel q hq := fun h => hxq (posLabel_injective hx hq h)
      simp [hne, hxq]

theorem not_commute_xUnit_E6
    (R : Type) [CommRing R] [Nontrivial R] :
    ¬Commute (xUnit Tag.E6 R ⟨2, by decide⟩ 1 * xUnit Tag.E6 R ⟨4, by decide⟩ 1)
      (xUnit Tag.E6 R ⟨3, by decide⟩ 1) := by
  intro h
  have e := congrArg (fun g : (Module.End R (RootModule Tag.E6 R))ˣ =>
    (g : Module.End R (RootModule Tag.E6 R)) (posVec Tag.E6 R 0)) h.eq
  simp only [Units.val_mul, Module.End.mul_apply] at e
  simp only [coe_xUnit] at e
  rw [posVec_eq_vecOf_single] at e
  have hv0 : ValidVec .E6 [(0, 1)] := validVec_single (by decide)
  obtain ⟨e3, v3⟩ := xOp_one_vecOf R ⟨3, by decide⟩ hv0
  obtain ⟨e43, v43⟩ := xOp_one_vecOf R ⟨4, by decide⟩ v3
  obtain ⟨e243, v243⟩ := xOp_one_vecOf R ⟨2, by decide⟩ v43
  obtain ⟨e4, v4⟩ := xOp_one_vecOf R ⟨4, by decide⟩ hv0
  obtain ⟨e24, v24⟩ := xOp_one_vecOf R ⟨2, by decide⟩ v4
  obtain ⟨e324, v324⟩ := xOp_one_vecOf R ⟨3, by decide⟩ v24
  rw [e3, e43, e243, e4, e24, e324] at e
  have e17 := congrArg (fun v : RootModule Tag.E6 R => v (posLabel 17 (by decide))) e
  rw [vecOf_apply_posLabel v243, vecOf_apply_posLabel v324] at e17
  have hA : ((((List.range 4).flatMap fun k => coeffVec .E6 false ⟨2, by decide⟩ k
      ((List.range 4).flatMap fun k => coeffVec .E6 false ⟨4, by decide⟩ k
        ((List.range 4).flatMap fun k => coeffVec .E6 false ⟨3, by decide⟩ k [(0, 1)]))).filter
          fun x => x.1 == 17).map Prod.snd).sum = 0 := by decide +kernel
  have hB : ((((List.range 4).flatMap fun k => coeffVec .E6 false ⟨3, by decide⟩ k
      ((List.range 4).flatMap fun k => coeffVec .E6 false ⟨2, by decide⟩ k
        ((List.range 4).flatMap fun k => coeffVec .E6 false ⟨4, by decide⟩ k [(0, 1)]))).filter
          fun x => x.1 == 17).map Prod.snd).sum = 1 := by decide +kernel
  rw [hA, hB, Int.cast_zero, Int.cast_one] at e17
  exact zero_ne_one e17

variable (t K) in
@[expose] def OrbitXCommute
    (σ : K →+* K) (a b : Fin t.foldedTag.rank) : Prop :=
  ∀ c d, Commute (fixedOrbitX t K σ a c) (fixedOrbitX t K σ b d)

theorem fixedOrbitX_mem
    (σ : K →+* K) (a : Fin t.foldedTag.rank) (c : orbitField t K σ a) :
    fixedOrbitX t K σ a c ∈ (orbitXSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ) :=
  orbitX_mem_orbitXSubgroup a c

theorem exists_eq_fixedOrbitX
    {σ : K →+* K} {a : Fin t.foldedTag.rank}
    {x : graphFixedRootGroup t K σ}
    (hx : x ∈ (orbitXSubgroup t K σ a).subgroupOf (graphFixedRootGroup t K σ)) :
    ∃ c, fixedOrbitX t K σ a c = x := by
  have h : (x : ModGL t.tag K) ∈ (orbitXSubgroup t K σ a : Set (ModGL t.tag K)) := hx
  rw [coe_orbitXSubgroup] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c, Subtype.ext hc⟩

theorem orbitXCommute_iff
    {σ : K →+* K} {β : MulAut (graphFixedRootGroup t K σ)}
    {π : Equiv.Perm (Fin t.foldedTag.rank)} (hπ : PermutesSimpleOrbitGroups t K σ β π)
    (a b : Fin t.foldedTag.rank) :
    OrbitXCommute t K σ a b ↔ OrbitXCommute t K σ (π a) (π b) := by
  have himg : ∀ (a : Fin t.foldedTag.rank) (c : orbitField t K σ a),
      ∃ c', β (fixedOrbitX t K σ a c) = fixedOrbitX t K σ (π a) c' := fun a c => by
    have h := Subgroup.mem_map_of_mem β.toMonoidHom (fixedOrbitX_mem σ a c)
    rw [(hπ a).1] at h
    obtain ⟨c', hc'⟩ := exists_eq_fixedOrbitX h
    exact ⟨c', hc'.symm⟩
  have hpre : ∀ (a : Fin t.foldedTag.rank) (c' : orbitField t K σ (π a)),
      ∃ c, β (fixedOrbitX t K σ a c) = fixedOrbitX t K σ (π a) c' := fun a c' => by
    have h := fixedOrbitX_mem σ (π a) c'
    rw [← (hπ a).1] at h
    obtain ⟨x, hx, hxe⟩ := h
    obtain ⟨c, rfl⟩ := exists_eq_fixedOrbitX hx
    exact ⟨c, hxe⟩
  constructor
  · intro h c' d'
    obtain ⟨c, hc⟩ := hpre a c'
    obtain ⟨d, hd⟩ := hpre b d'
    rw [← hc, ← hd]
    exact (h c d).map β
  · intro h c d
    obtain ⟨c', hc⟩ := himg a c
    obtain ⟨d', hd⟩ := himg b d
    have h' := h c' d'
    rw [← hc, ← hd] at h'
    have h'' := h'.map β.symm.toMonoidHom
    simpa using h''

theorem coe_orbitX_E6_one
    (σ : K →+* K) :
    (orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨2, by decide⟩ 1 * xUnit Tag.E6 K ⟨4, by decide⟩ 1 := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide
  have hm : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hp : (TwistTag.E6.perm ^ 1) ⟨2, by decide⟩ = ⟨4, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, OneMemClass.coe_one, map_one, pow_zero, hm, hp]
  rfl

theorem coe_orbitX_E6_two
    (σ : K →+* K) :
    (orbitX TwistTag.E6 K σ ⟨2, by decide⟩ 1 : ModGL TwistTag.E6.tag K) =
      xUnit Tag.E6 K ⟨3, by decide⟩ 1 := by
  rw [coe_orbitX]
  have hc : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := by decide
  have hm : TwistTag.E6.orbitMin ⟨2, by decide⟩ = ⟨3, by decide⟩ := by decide
  rw [hc, List.range_succ, List.range_zero]
  simp only [List.nil_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, OneMemClass.coe_one, map_one, pow_zero, hm]
  rfl

theorem orbitXCommute_E6
    (σ : K →+* K) :
    OrbitXCommute TwistTag.E6 K σ ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    OrbitXCommute TwistTag.E6 K σ ⟨0, by decide⟩ ⟨3, by decide⟩ ∧
    OrbitXCommute TwistTag.E6 K σ ⟨1, by decide⟩ ⟨3, by decide⟩ ∧
    ¬OrbitXCommute TwistTag.E6 K σ ⟨1, by decide⟩ ⟨2, by decide⟩ := by
  refine ⟨fun c d => ?_, fun c d => ?_, fun c d => ?_, fun h => ?_⟩
  all_goals try exact Subtype.ext (commute_orbitX_E6 (fun i hi j hj => by
    revert hi hj
    fin_cases i <;> fin_cases j <;> decide) c d)
  · have h1 := congrArg Subtype.val (h 1 1).eq
    change (orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 : ModGL TwistTag.E6.tag K) *
      orbitX TwistTag.E6 K σ ⟨2, by decide⟩ 1 =
        (orbitX TwistTag.E6 K σ ⟨2, by decide⟩ 1 : ModGL TwistTag.E6.tag K) *
          orbitX TwistTag.E6 K σ ⟨1, by decide⟩ 1 at h1
    rw [coe_orbitX_E6_one, coe_orbitX_E6_two] at h1
    exact not_commute_xUnit_E6 K h1

theorem permutesSimpleOrbitGroups_one_E6
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) [Finite K]
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hβ : β ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom) :
    PermutesSimpleOrbitGroups TwistTag.E6 K σ.toRingHom β 1 := by
  obtain ⟨π, hπ, -⟩ := existsUnique_permutesSimpleOrbitGroups σ hβ
  have hcard := fun a => (diagram_fixed_intrinsic_simple_pairs TwistTag.E6 K σ).2.2.1 β hβ π hπ a
  obtain ⟨σ', hσ', -, hcardL, -, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 hp hf K hK
  have hσσ' : σ = σ' := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ'
  have hq : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hd : ∀ a, (TwistTag.E6.orbit (π a)).card = (TwistTag.E6.orbit a).card := fun a => by
    have h := hcard a
    rw [hcardL, hcardL] at h
    exact (Nat.pow_right_injective hq h).symm
  obtain ⟨h02, h03, h13, hn12⟩ := orbitXCommute_E6 (K := K) σ.toRingHom
  have htr := orbitXCommute_iff hπ
  have hone : ∀ x : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit x).card = 1 →
      x = ⟨2, by decide⟩ ∨ x = ⟨3, by decide⟩ := by
    intro x
    fin_cases x <;> decide
  have htwo : ∀ x : Fin TwistTag.E6.foldedTag.rank, (TwistTag.E6.orbit x).card = 2 →
      x = ⟨0, by decide⟩ ∨ x = ⟨1, by decide⟩ := by
    intro x
    fin_cases x <;> decide
  have hc0 : (TwistTag.E6.orbit ⟨0, by decide⟩).card = 2 := by decide
  have hc1 : (TwistTag.E6.orbit ⟨1, by decide⟩).card = 2 := by decide
  have hc2 : (TwistTag.E6.orbit ⟨2, by decide⟩).card = 1 := by decide
  have hc3 : (TwistTag.E6.orbit ⟨3, by decide⟩).card = 1 := by decide
  have hn := (htr ⟨1, by decide⟩ ⟨2, by decide⟩).not.1 hn12
  have hπ2 : π ⟨2, by decide⟩ = ⟨2, by decide⟩ := by
    rcases hone _ ((hd _).trans hc2) with h | h
    · exact h
    · exfalso
      rw [h] at hn
      rcases htwo _ ((hd _).trans hc1) with h' | h'
      · rw [h'] at hn
        exact hn h03
      · rw [h'] at hn
        exact hn h13
  have hπ1 : π ⟨1, by decide⟩ = ⟨1, by decide⟩ := by
    rcases htwo _ ((hd _).trans hc1) with h | h
    · exfalso
      rw [h, hπ2] at hn
      exact hn h02
    · exact h
  have hπ3 : π ⟨3, by decide⟩ = ⟨3, by decide⟩ := by
    rcases hone _ ((hd _).trans hc3) with h | h
    · exact absurd (π.injective (h.trans hπ2.symm)) (by decide)
    · exact h
  have hπ0 : π ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
    rcases htwo _ ((hd _).trans hc0) with h | h
    · exact h
    · exact absurd (π.injective (h.trans hπ1.symm)) (by decide)
  have hπ1' : π = 1 := Equiv.ext fun x => by
    fin_cases x
    exacts [hπ0, hπ1, hπ2, hπ3]
  rw [hπ1'] at hπ
  exact hπ

theorem compatDiag_mulSingle_of_ne {σ : K →+* K} {a : Fin t.foldedTag.rank}
    (u : (orbitField t K σ a)ˣ) {j : Fin t.tag.rank} (hj : t.orbitIndex j ≠ a) :
    compatDiag t σ (Pi.mulSingle (M := fun c => (orbitField t K σ c)ˣ) a u) j = 1 := by
  obtain ⟨k, hk, hi⟩ := t.exists_eq_perm_pow_orbitMin (t.mem_orbit_orbitIndex j)
  rw [← hi, compatDiag_pow _ _ hk, Pi.mulSingle_eq_of_ne hj]
  ext
  simp [orbitFieldUnit]

theorem fixedOrbitH_conj_fixedOrbitX_E6
    {σ : K →+* K}
    (u : (orbitField TwistTag.E6 K σ ⟨0, by decide⟩)ˣ) :
    ∃ w : (orbitField TwistTag.E6 K σ ⟨1, by decide⟩)ˣ,
      ((w : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) : K) =
        ((u : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) : K)⁻¹ ∧
      ∀ c, fixedOrbitH TwistTag.E6 K σ ⟨0, by decide⟩ u *
          fixedOrbitX TwistTag.E6 K σ ⟨1, by decide⟩ c *
          (fixedOrbitH TwistTag.E6 K σ ⟨0, by decide⟩ u)⁻¹ =
        fixedOrbitX TwistTag.E6 K σ ⟨1, by decide⟩ (w * c) := by
  obtain ⟨v, -, hv, hX, -⟩ := exists_list_prod_orbitH_conj (Pi.mulSingle ⟨0, by decide⟩ u)
  rw [list_prod_orbitH_mulSingle] at hX
  refine ⟨v ⟨1, by decide⟩, ?_, fun c => Subtype.ext (hX _ c)⟩
  have h := hv ⟨1, by decide⟩
  have hm1 : TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have hm0 : TwistTag.E6.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  rw [hm1, cartanChar, Finset.prod_eq_single (⟨0, by decide⟩ : Fin TwistTag.E6.tag.rank)] at h
  · rw [← hm0, compatDiag_orbitMin, Pi.mulSingle_eq_same, hm0,
      show TwistTag.E6.tag.cartan ⟨0, by decide⟩ ⟨2, by decide⟩ = -1 by decide, _root_.zpow_neg,
      zpow_one] at h
    have h' := congrArg Units.val h
    rw [Units.val_inv_eq_inv_val, coe_orbitFieldUnit, coe_orbitFieldUnit] at h'
    exact h'
  · intro j _ hj
    by_cases hjo : TwistTag.E6.orbitIndex j = ⟨0, by decide⟩
    · have hj5 : j = ⟨5, by decide⟩ := by
        revert hj hjo
        fin_cases j <;> decide
      rw [hj5, show TwistTag.E6.tag.cartan ⟨5, by decide⟩ ⟨2, by decide⟩ = 0 by decide,
        zpow_zero]
    · rw [compatDiag_mulSingle_of_ne u hjo, _root_.one_zpow]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

theorem orbitParams_right_zero_eq_one
    [Finite K] {σ : K →+* K}
    (α : graphFixedPairAut TwistTag.E6 K σ) {c : K}
    (h0 : c ∈ orbitField TwistTag.E6 K σ ⟨0, by decide⟩)
    (h1 : c ∈ orbitField TwistTag.E6 K σ ⟨1, by decide⟩) :
    ((orbitParams TwistTag.E6 K σ ⟨0, by decide⟩ α).right ⟨c, h0⟩ : K) =
      ((orbitParams TwistTag.E6 K σ ⟨1, by decide⟩ α).right ⟨c, h1⟩ : K) := by
  by_cases hc0 : c = 0
  · subst hc0
    have ha0 : (⟨0, h0⟩ : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) = 0 := rfl
    have hb0 : (⟨0, h1⟩ : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) = 0 := rfl
    rw [ha0, hb0, map_zero, map_zero, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]
  have hca : (⟨c, h0⟩ : orbitField TwistTag.E6 K σ ⟨0, by decide⟩) ≠ 0 :=
    fun h => hc0 (congrArg Subtype.val h)
  have hcb : (⟨c, h1⟩ : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) ≠ 0 :=
    fun h => hc0 (congrArg Subtype.val h)
  obtain ⟨hxb, -, -⟩ := orbitParams_spec ⟨1, by decide⟩ α
  obtain ⟨-, -, hha⟩ := orbitParams_spec ⟨0, by decide⟩ α
  obtain ⟨w, hw, hconj⟩ := fixedOrbitH_conj_fixedOrbitX_E6 (σ := σ) (Units.mk0 _ hca)
  obtain ⟨w', hw', hconj'⟩ := fixedOrbitH_conj_fixedOrbitX_E6 (σ := σ)
    (Units.map (orbitParams TwistTag.E6 K σ ⟨0, by decide⟩ α).right.toMonoidHom (Units.mk0 _ hca))
  have e := congrArg (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)) (hconj 1)
  rw [map_mul, map_mul, map_inv, hha, hxb, hxb, map_one, mul_one, hconj', mul_one] at e
  have e' := fixedOrbitX_injective _ e
  have e'' : (w' : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) =
      (orbitParams TwistTag.E6 K σ ⟨1, by decide⟩ α).right w :=
    mul_left_cancel₀ (orbitParams TwistTag.E6 K σ _ α).left.ne_zero ((mul_comm _ _).trans e')
  have hwc : (w : orbitField TwistTag.E6 K σ ⟨1, by decide⟩) =
      (⟨c, h1⟩ : orbitField TwistTag.E6 K σ ⟨1, by decide⟩)⁻¹ :=
    Subtype.ext (by rw [hw, Units.val_mk0]; rfl)
  rw [hwc, map_inv₀] at e''
  have e3 := congrArg (fun x : orbitField TwistTag.E6 K σ ⟨1, by decide⟩ => (x : K)) e''
  rw [hw', Units.coe_map, Units.val_mk0] at e3
  exact inv_injective (e3.trans (by rfl))

theorem twisted_E6_all_characteristic_common_full_field_parameters
    {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    ∀ β ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom,
      β ∈ graphFixedPairAut TwistTag.E6 K σ.toRingHom ∧
      ∃! P : (K ≃+* K) × ((a : Fin TwistTag.E6.foldedTag.rank) →
          (orbitField TwistTag.E6 K σ.toRingHom a)ˣ), ∀ a,
        (∀ c, β (fixedOrbitX TwistTag.E6 K σ.toRingHom a c) = fixedOrbitX TwistTag.E6 K
          σ.toRingHom a (P.2 a * orbitFieldRestrict TwistTag.E6 σ P.1 a c)) ∧
        (∀ c, β (fixedOrbitY TwistTag.E6 K σ.toRingHom a c) = fixedOrbitY TwistTag.E6 K
          σ.toRingHom a (((P.2 a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) *
            orbitFieldRestrict TwistTag.E6 σ P.1 a c)) ∧
        ∀ u, β (fixedOrbitH TwistTag.E6 K σ.toRingHom a u) = fixedOrbitH TwistTag.E6 K
          σ.toRingHom a (Units.map (orbitFieldRestrict TwistTag.E6 σ P.1 a).toMonoidHom u) := by
  have h0top : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ :=
    orbitField_E6_eq_top_of_card hK hσ (by decide)
  have h1top : orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ :=
    orbitField_E6_eq_top_of_card hK hσ (by decide)
  have hσq : ∀ c, σ.toRingHom c = c ^ (p ^ f) := hσ
  refine ⟨h0top, h1top, fun c => mem_orbitField_iff_of_card_eq_one (by decide),
    fun c => mem_orbitField_iff_of_card_eq_one (by decide), fun β hβ => ?_⟩
  have hpair := permutesSimpleOrbitGroups_one_E6 hp hf hK σ hσ hβ
  have hmem : β ∈ graphFixedPairAut TwistTag.E6 K σ.toRingHom :=
    Subgroup.mem_iInf.2 fun a => hpair a
  refine ⟨hmem, ?_⟩
  set α : graphFixedPairAut TwistTag.E6 K σ.toRingHom := ⟨β, hmem⟩ with hα
  have hmem0 : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ := fun c => by
    rw [h0top]
    trivial
  let e0 : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ≃+* K :=
    (RingEquiv.subfieldCongr h0top).trans Subfield.topEquiv
  let δ : K ≃+* K :=
    (e0.symm.trans (orbitParams TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ α).right).trans e0
  have hδ : ∀ c : K, δ c =
      ((orbitParams TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ α).right ⟨c, hmem0 c⟩ : K) :=
    fun c => rfl
  have hres : ∀ a, orbitFieldRestrict TwistTag.E6 σ δ a =
      (orbitParams TwistTag.E6 K σ.toRingHom a α).right := by
    intro a
    refine RingEquiv.ext fun c => Subtype.ext ?_
    rw [coe_orbitFieldRestrict, hδ]
    have hfix : ∀ (a' : Fin TwistTag.E6.foldedTag.rank), (TwistTag.E6.orbit a').card = 1 →
        c.1 ∈ orbitField TwistTag.E6 K σ.toRingHom a' → c.1 ∈ orbitField TwistTag.E6 K
          σ.toRingHom (baseOrbit TwistTag.E6) := fun a' ha' hc => by
      rw [mem_orbitField_iff_of_card_eq_one ha'] at hc
      exact (mem_orbitField_iff_of_card_eq_one (card_orbit_baseOrbit _)).2 hc
    fin_cases a
    · rfl
    · exact orbitParams_right_zero_eq_one α _ c.2
    · exact orbitParams_right_eq_base hσq α _ _ (hfix _ (by decide) c.2)
    · exact (orbitParams_right_eq_base hσq α _ _ (hfix _ (by decide) c.2)).trans
        (orbitParams_right_eq_base hσq α _ _ (hfix _ (by decide) c.2)).symm
  refine ⟨(δ, fun a => (orbitParams TwistTag.E6 K σ.toRingHom a α).left), fun a => ?_,
    fun P hP => ?_⟩
  · simp only [hres]
    exact orbitParams_spec a α
  · have hu : ∀ a, P.2 a = (orbitParams TwistTag.E6 K σ.toRingHom a α).left ∧
        orbitFieldRestrict TwistTag.E6 σ P.1 a =
          (orbitParams TwistTag.E6 K σ.toRingHom a α).right :=
      fun a => orbit_params_unique (hP a).1 (orbitParams_spec a α).1
    refine Prod.ext (RingEquiv.ext fun c => ?_) (funext fun a => (hu a).1)
    have h := congrArg (fun e : orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ ≃+*
      orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ => (e ⟨c, hmem0 c⟩ : K)) (hu _).2
    exact h

theorem twisted_E6_odd_common_full_field_parameters
    {p f : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    orbitField TwistTag.E6 K σ.toRingHom ⟨0, by decide⟩ = ⊤ ∧
    orbitField TwistTag.E6 K σ.toRingHom ⟨1, by decide⟩ = ⊤ ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨2, by decide⟩ ↔ σ c = c) ∧
    (∀ c, c ∈ orbitField TwistTag.E6 K σ.toRingHom ⟨3, by decide⟩ ↔ σ c = c) ∧
    ∀ β ∈ graphFixedUnipotentStabilizer TwistTag.E6 K σ.toRingHom,
      β ∈ graphFixedPairAut TwistTag.E6 K σ.toRingHom ∧
      ∃! P : (K ≃+* K) × ((a : Fin TwistTag.E6.foldedTag.rank) →
          (orbitField TwistTag.E6 K σ.toRingHom a)ˣ), ∀ a,
        (∀ c, β (fixedOrbitX TwistTag.E6 K σ.toRingHom a c) = fixedOrbitX TwistTag.E6 K
          σ.toRingHom a (P.2 a * orbitFieldRestrict TwistTag.E6 σ P.1 a c)) ∧
        (∀ c, β (fixedOrbitY TwistTag.E6 K σ.toRingHom a c) = fixedOrbitY TwistTag.E6 K
          σ.toRingHom a (((P.2 a)⁻¹ : (orbitField TwistTag.E6 K σ.toRingHom a)ˣ) *
            orbitFieldRestrict TwistTag.E6 σ P.1 a c)) ∧
        ∀ u, β (fixedOrbitH TwistTag.E6 K σ.toRingHom a u) = fixedOrbitH TwistTag.E6 K
          σ.toRingHom a (Units.map (orbitFieldRestrict TwistTag.E6 σ P.1 a).toMonoidHom u) :=
  twisted_E6_all_characteristic_common_full_field_parameters hp hf K hK σ hσ

end CFSG.LieType.Chevalley
