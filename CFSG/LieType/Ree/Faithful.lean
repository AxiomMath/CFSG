module

public import CFSG.LieType.Ree.FaithfulTriangular
public import CFSG.LieType.Ree.Intertwiner
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.RootSystem

theorem wordProd_smul {τ : Tag} (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    (coxeterSystem τ).wordProd l • v = l.foldr (reflect τ) v := by
  induction l with
  | nil => rw [CoxeterSystem.wordProd_nil, one_smul, List.foldr_nil]
  | cons i l ih => rw [CoxeterSystem.wordProd_cons, mul_smul, ih, simple_smul, List.foldr_cons]

namespace ReeTag

variable {t : ReeTag} {K : Type} [Field K]

theorem mem_shortModule_of_mem (hp : (t.prime : K) = 0) {g : ModGL t.tag K}
    (hg : g ∈ adjointGroup t.tag K) {v : RootModule t.tag K} (hv : v ∈ t.shortModule K) :
    (g : Module.End K (RootModule t.tag K)) v ∈ t.shortModule K := by
  induction hg using Subgroup.closure_induction'' generalizing v with
  | mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · rw [h]
      exact xOp_mem_shortModule K hp i c hv
    · rw [h]
      exact yOp_mem_shortModule K hp i c hv
  | inv_mem g hg =>
    obtain ⟨i, c, h | h⟩ := hg
    · rw [show g = xUnit t.tag K i c from Units.ext h, coe_xUnit_inv]
      exact xOp_mem_shortModule K hp i (-c) hv
    · rw [show g = yUnit t.tag K i c from Units.ext h, coe_yUnit_inv]
      exact yOp_mem_shortModule K hp i (-c) hv
  | one => simpa using hv
  | mul g g' _ _ ihg ihg' =>
    rw [Units.val_mul, Module.End.mul_apply]
    exact ihg (ihg' hv)

theorem rootVec_mem_shortModule {β : Fin t.tag.rank → ℤ} (hβ : β ∈ t.shortRoots) :
    rootVec t.tag K β ∈ t.shortModule K :=
  Submodule.subset_span (Or.inr ⟨β, hβ, rfl⟩)

theorem quadForm_neg (α : Fin t.tag.rank → ℤ) : t.quadForm (-α) = t.quadForm α := by
  simp [quadForm, Matrix.mulVec_neg]

theorem neg_mem_shortRoots {β : Fin t.tag.rank → ℤ} (hβ : β ∈ t.shortRoots) :
    -β ∈ t.shortRoots :=
  ⟨IsRoot.neg hβ.1, by rw [lengthParam, quadForm_neg]; exact hβ.2⟩

theorem isRoot_of_memDec {v : Fin t.tag.rank → ℤ}
    (h : t.tag.stringData.memDec t.tag.rootCertificate v = true) : IsRoot t.tag v :=
  (StringData.memDec_iff t.tag.rootCertificate_check t.tag.stringData_check).1 h

theorem not_isRoot_of_memDec {v : Fin t.tag.rank → ℤ}
    (h : t.tag.stringData.memDec t.tag.rootCertificate v = false) : ¬IsRoot t.tag v := fun hv => by
  rw [← StringData.memDec_iff t.tag.rootCertificate_check t.tag.stringData_check, h] at hv
  exact Bool.false_ne_true hv

theorem mem_shortRoots_of_memDec {v : Fin t.tag.rank → ℤ}
    (h : t.tag.stringData.memDec t.tag.rootCertificate v = true) (hq : t.quadForm v = 2) :
    v ∈ t.shortRoots :=
  ⟨isRoot_of_memDec h, lengthParam_eq_one_iff.2 hq⟩

variable (t K) in
@[expose] def shortKernel : Subgroup (adjointGroup t.tag K) where
  carrier := {g | ∀ v ∈ t.shortModule K, glRep _ g v = v}
  mul_mem' {g h} hg hh v hv := by rw [map_mul, Module.End.mul_apply, hh v hv, hg v hv]
  one_mem' v _ := by rw [map_one, Module.End.one_apply]
  inv_mem' {g} hg v hv := by
    conv_lhs => rw [← hg v hv]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem mem_shortKernel {g : adjointGroup t.tag K} :
    g ∈ t.shortKernel K ↔ ∀ v ∈ t.shortModule K, glRep _ g v = v :=
  Iff.rfl

theorem shortKernel_normal (hp : (t.prime : K) = 0) : (t.shortKernel K).Normal := by
  refine ⟨fun g hg x v hv => ?_⟩
  have hv' : glRep _ x⁻¹ v ∈ t.shortModule K := mem_shortModule_of_mem hp (x⁻¹).2 hv
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg _ hv',
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[expose] def negOneWord : (t : ReeTag) → List (Fin t.tag.rank)
  | G2 => ([0, 1, 0, 1, 0, 1] : List (Fin 2))
  | F4 => ([0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3] :
      List (Fin 4))

variable (t) in
@[expose] def negOne : WeylGroup t.tag :=
  (coxeterSystem t.tag).wordProd t.negOneWord

theorem negOne_smul_single (t : ReeTag) (i : Fin t.tag.rank) :
    t.negOne • (Pi.single i 1 : Fin t.tag.rank → ℤ) = -Pi.single i 1 := by
  rw [negOne, wordProd_smul]
  revert i
  cases t <;> decide +kernel

theorem negOne_smul (t : ReeTag) (v : Fin t.tag.rank → ℤ) : t.negOne • v = -v := by
  have h : weylAction (isFiniteType_cartan t.tag) t.negOne = -LinearMap.id := by
    refine LinearMap.pi_ext fun i x => ?_
    rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul, ← smul_def,
      negOne_smul_single]
    simp
  rw [smul_def, h]
  rfl

@[expose] def shortPair : (t : ReeTag) → Fin t.tag.rank →
    (Fin t.tag.rank → ℤ) × (Fin t.tag.rank → ℤ)
  | G2 => (![(![1, 1], ![0, 1]), (![0, 1], 0)] : Fin 2 → (Fin 2 → ℤ) × (Fin 2 → ℤ))
  | F4 => (![(![1, 1, 1, 0], ![0, 1, 1, 0]), (![0, 1, 1, 0], ![0, 0, 1, 0]),
      (![0, 0, 1, 0], 0), (![0, 0, 0, 1], 0)] : Fin 4 → (Fin 4 → ℤ) × (Fin 4 → ℤ))

theorem shortPair_spec (t : ReeTag) : ∀ i : Fin t.tag.rank,
    (t.tag.stringData.memDec t.tag.rootCertificate (t.shortPair i).1 = true ∧
      t.quadForm (t.shortPair i).1 = 2) ∧
    ((t.shortPair i).2 = 0 ∨
      (t.tag.stringData.memDec t.tag.rootCertificate (t.shortPair i).2 = true ∧
        t.quadForm (t.shortPair i).2 = 2)) ∧
    (Pi.single i 1 : Fin t.tag.rank → ℤ) = (t.shortPair i).1 - (t.shortPair i).2 := by
  cases t <;> decide +kernel

theorem eq_one_of_forall_shortRoots {w : WeylGroup t.tag} (hw : ∀ β ∈ t.shortRoots, w • β = β) :
    w = 1 := by
  refine ext_single fun i => ?_
  obtain ⟨⟨h1, h1'⟩, h2, he⟩ := t.shortPair_spec i
  rw [one_smul, he, smul_sub, hw _ (mem_shortRoots_of_memDec h1 h1')]
  rcases h2 with h2 | ⟨h2, h2'⟩
  · rw [h2, smul_zero]
  · rw [hw _ (mem_shortRoots_of_memDec h2 h2')]

theorem shortKernel_le_B [Finite K] (hp : (t.prime : K) = 0) :
    t.shortKernel K ≤ (nativeData t.tag K).B := by
  intro g hg
  obtain ⟨m, b₁, hb₁, b₂, hb₂, rfl⟩ := RootGroupData.exists_mem_doubleCoset
    (D := nativeData t.tag K) (nativeRootSubgroups t.tag K).simple_le_normalizer_Ui
    (nativeRootSubgroups t.tag K).rankOne (nativeRootSubgroups t.tag K).closure_B_union_n g
  have hQ : ((m : monomialGroup t.tag K) : adjointGroup t.tag K) * (b₂ * b₁) ∈
      t.shortKernel K := by
    have := (shortKernel_normal hp).conj_mem _ hg b₁⁻¹
    convert this using 1
    group
  have hb : b₂ * b₁ ∈ (nativeData t.tag K).B := mul_mem hb₂ hb₁
  have hw : (weylHom t.tag K m)⁻¹ = 1 := eq_one_of_forall_shortRoots fun β hβ =>
    inv_smul_eq_of_fixes m hb hβ.1 (hQ _ (rootVec_mem_shortModule hβ))
      (hQ _ (rootVec_mem_shortModule (neg_mem_shortRoots hβ)))
  have hmH : (m : adjointGroup t.tag K) ∈ (nativeData t.tag K).H :=
    RootGroupData.mem_H_iff.2 ⟨m, inv_eq_one.1 hw, rfl⟩
  exact mul_mem (mul_mem hb₁ ((nativeData t.tag K).H_le_B hmH)) hb₂

theorem preservesWeights_of_mem_shortKernel [Finite K] (hp : (t.prime : K) = 0)
    {g : adjointGroup t.tag K} (hg : g ∈ t.shortKernel K) : PreservesWeights (glRep _ g) := by
  obtain ⟨n, hn⟩ := weylHom_surjective (τ := t.tag) (K := K) t.negOne
  have hn' : ∀ v : Fin t.tag.rank → ℤ, weylHom t.tag K n • v = -v := fun v => by
    rw [hn]
    exact t.negOne_smul v
  have hc : (n : adjointGroup t.tag K)⁻¹ * g * (n : adjointGroup t.tag K) ∈ t.shortKernel K := by
    have := (shortKernel_normal hp).conj_mem _ hg (n : adjointGroup t.tag K)⁻¹
    rwa [inv_inv] at this
  exact preservesWeights_of_isUpper n hn' (isUpper_of_mem_B (shortKernel_le_B hp hg))
    (isUpper_of_mem_B (shortKernel_le_B hp hc))

theorem commute_of_mem_shortKernel [Finite K] (hp : (t.prime : K) = 0)
    {g : adjointGroup t.tag K} (hg : g ∈ t.shortKernel K) {α : Root t.tag} {s : ℤ}
    (hs : 0 < s * height α.1) {x : adjointGroup t.tag K}
    (hx : x ∈ (nativeRootSubgroups t.tag K).X α) : g * x = x * g := by
  have hz : g * x * g⁻¹ * x⁻¹ ∈ t.shortKernel K := by
    have := mul_mem hg ((shortKernel_normal hp).conj_mem _ (inv_mem hg) x)
    rwa [← mul_assoc, ← mul_assoc] at this
  exact commute_of_preservesWeights (preservesWeights_of_mem_shortKernel hp hg)
    (preservesWeights_of_mem_shortKernel hp (inv_mem hg))
    (preservesWeights_of_mem_shortKernel hp hz) (raisesHeight_of_mem_X hs hx)

@[expose] def longWitness : (t : ReeTag) → Fin t.tag.rank → List (Fin t.tag.rank) × Fin t.tag.rank
  | G2 => (![([], 1), ([], 0)] : Fin 2 → List (Fin 2) × Fin 2)
  | F4 => (![([1], 2), ([], 2), ([], 0), ([], 0)] : Fin 4 → List (Fin 4) × Fin 4)

variable (t) in
@[expose] def witnessRoot (j : Fin t.tag.rank) : Fin t.tag.rank → ℤ :=
  (t.longWitness j).1.foldr (reflect t.tag) (Pi.single j 1)

variable (t) in
@[expose] def witnessSingle (j : Fin t.tag.rank) : Fin t.tag.rank → ℤ :=
  Pi.single (t.longWitness j).2 1

theorem longWitness_spec (t : ReeTag) : ∀ j : Fin t.tag.rank,
    (t.tag.stringData.memDec t.tag.rootCertificate (Pi.single j 1) = true ∧
      t.quadForm (Pi.single j 1) = 2) ∨
    (t.witnessRoot j ≠ t.witnessSingle j ∧ t.witnessRoot j ≠ -t.witnessSingle j ∧
      t.tag.stringData.memDec t.tag.rootCertificate (t.witnessRoot j + t.witnessSingle j) =
        true ∧
      t.quadForm (t.witnessRoot j + t.witnessSingle j) = 2 ∧
      t.tag.stringData.memDec t.tag.rootCertificate (t.witnessRoot j - t.witnessSingle j) =
        false) := by
  cases t <;> decide +kernel

theorem rootVec_single_fixed {h : Module.End K (RootModule t.tag K)} (hh : PreservesWeights h)
    (hx : ∀ i, h * xOp t.tag K i 1 = xOp t.tag K i 1 * h)
    (hn : ∀ i, h * (weylElt t.tag K i 1 : Module.End K (RootModule t.tag K)) =
      (weylElt t.tag K i 1 : Module.End K (RootModule t.tag K)) * h)
    (hI : ∀ β ∈ t.shortRoots, h (rootVec t.tag K β) = rootVec t.tag K β) (j : Fin t.tag.rank) :
    h (rootVec t.tag K (Pi.single j 1)) = rootVec t.tag K (Pi.single j 1) := by
  rcases t.longWitness_spec j with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5⟩
  · exact hI _ (mem_shortRoots_of_memDec h1 h2)
  · have hα : IsRoot t.tag (t.witnessRoot j) := by
      unfold witnessRoot
      induction (t.longWitness j).1 with
      | nil => exact .basis j
      | cons i u ih => exact .reflect i ih
    exact rootVec_fixed_of_foldr hn (.basis j) _ (rootVec_fixed_of_witness hh (hx _) hα h1 h2
      (isRoot_of_memDec h3) (not_isRoot_of_memDec h5) (hI _ (mem_shortRoots_of_memDec h3 h4)))

theorem shortKernel_eq_bot [Finite K] (hp : (t.prime : K) = 0) : t.shortKernel K = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_
  have hx : ∀ i, glRep _ g * xOp t.tag K i 1 = xOp t.tag K i 1 * glRep _ g := fun i => by
    have := congrArg (glRep _) (commute_of_mem_shortKernel hp hg (α := simpleRoot t.tag i)
      (s := 1) (by simp [simpleRoot])
      (((nativeRootSubgroups t.tag K).mem_simple i (xElement i 1)).2 ⟨1, rfl⟩))
    rwa [map_mul, map_mul] at this
  have hy : ∀ i, glRep _ g * yOp t.tag K i (-1) = yOp t.tag K i (-1) * glRep _ g := fun i => by
    have := congrArg (glRep _) (commute_of_mem_shortKernel hp hg (α := -simpleRoot t.tag i)
      (s := -1) (by simp [simpleRoot])
      (((nativeRootSubgroups t.tag K).mem_neg_simple i (yElement i (-1))).2 ⟨-1, rfl⟩))
    rwa [map_mul, map_mul] at this
  have h1 : glRep _ g = 1 := eq_one_of_fixes_simple hx hy
    (rootVec_single_fixed (preservesWeights_of_mem_shortKernel hp hg) hx
      (fun i => commute_weylElt (hx i) (hy i))
      (fun β hβ => hg _ (rootVec_mem_shortModule hβ)))
  exact glRep_injective _ (by rw [h1, map_one])

variable (t K) in
@[expose] def ShortFaithful : Prop :=
  ∀ g ∈ adjointGroup t.tag K,
    (∀ v ∈ t.shortModule K, (g : Module.End K (RootModule t.tag K)) v = v) → g = 1

theorem shortFaithful [Finite K] (hp : (t.prime : K) = 0) : t.ShortFaithful K := by
  intro g hg h
  have : (⟨g, hg⟩ : adjointGroup t.tag K) ∈ t.shortKernel K := h
  rw [shortKernel_eq_bot hp, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem ShortFaithful.eq_of_eqOn (hf : t.ShortFaithful K) {g g' : ModGL t.tag K}
    (hg : g ∈ adjointGroup t.tag K) (hg' : g' ∈ adjointGroup t.tag K)
    (h : ∀ v ∈ t.shortModule K,
      (g : Module.End K (RootModule t.tag K)) v = (g' : Module.End K (RootModule t.tag K)) v) :
    g = g' := by
  have h1 := hf (g'⁻¹ * g) (mul_mem (inv_mem hg') hg) fun v hv => by
    rw [Units.val_mul, Module.End.mul_apply, h v hv, ← Module.End.mul_apply, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rwa [inv_mul_eq_one, eq_comm] at h1

end ReeTag

open ReeTag

theorem exceptional_short_faithful (t : ReeTag) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] {g : ModGL t.tag K} (hg : g ∈ adjointGroup t.tag K)
    (h : ∀ v ∈ t.shortModule K, (g : Module.End K (RootModule t.tag K)) v = v) : g = 1 :=
  shortFaithful (CharP.cast_eq_zero K t.prime) g hg h

end CFSG.LieType.Ree
