module

public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.LieType.Chevalley.IntrinsicSimplePairs
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.GraphFixedF4GroupRestriction
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.RootCharacterConjugation

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  Polynomial

variable {τ : Tag}

theorem center_adjointGroup_eq_bot_field
    (τ : Tag) (L : Type) [Field L] :
    Subgroup.center (adjointGroup τ L) = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzc : ∀ g ∈ adjointGroup τ L, (z : ModGL τ L) * g = g * z := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩).symm
  have hnorm : ∀ S : Subgroup (ModGL τ L), S ≤ adjointGroup τ L →
      (z : ModGL τ L) ∈ Subgroup.normalizer (S : Set (ModGL τ L)) := by
    intro S hS
    refine Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩
    · rw [hzc g (hS hg), mul_inv_cancel_right]
      exact hg
    · have hgC : g ∈ adjointGroup τ L := by
        have := mul_mem (mul_mem (inv_mem z.2) (hS hg)) z.2
        simpa [mul_assoc] using this
      rw [hzc g hgC, mul_inv_cancel_right] at hg
      exact hg
  have hB : (z : ModGL τ L) ∈ borelGroup τ L := by
    rw [← (borel_self_normalizers τ L).1]
    exact ⟨z.2, hnorm _ posUnipotent_le_adjointGroup⟩
  have hB' : (z : ModGL τ L) ∈ oppositeBorel τ L := by
    rw [← oppositeBorel_normalizer τ L]
    exact ⟨z.2, hnorm _ negUnipotent_le_adjointGroup⟩
  obtain ⟨w₀, hmax, -⟩ := weyl_longest_element τ
  have hH : (z : ModGL τ L) ∈ torusGroup τ L := by
    rw [← (opposite_Borel_intersection τ L w₀ hmax).2.2.1]
    exact ⟨hB, hB'⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hH
  have ha1 : a = 1 := by
    funext i
    have h1 := (root_diagonal_conjugation τ L a).1 i 1
    rw [← ha, hzc _ (xUnit_mem_adjointGroup i 1), mul_inv_cancel_right, mul_one,
      ← pinnedX_single, ← pinnedX_single] at h1
    exact Units.ext ((pinnedX_injective τ L _ h1).symm)
  apply Subtype.ext
  rw [ha, ha1, rootDiagUnit_one]
  rfl

theorem end_mul_single_apply
    {L : Type} [Field L] (A B : Module.End L (RootModule τ L))
    (a b : Label τ) :
    (A * B) (Finsupp.single b 1) a =
      ∑ d, (B (Finsupp.single b 1)) d * (A (Finsupp.single d 1)) a := by
  classical
  rw [Module.End.mul_apply]
  conv_lhs => rw [← Finsupp.univ_sum_single (B (Finsupp.single b 1))]
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show Finsupp.single d (B (Finsupp.single b 1) d) =
      (B (Finsupp.single b 1) d) • Finsupp.single d (1 : L) by simp, map_smul,
    Finsupp.smul_apply, smul_eq_mul]

theorem commute_of_polynomial_entries
    {L : Type} [Field L] {ι' : Type*} [Fintype ι']
    {F : L → Module.End L (RootModule τ L)} {D : ℕ}
    (hF : ∀ a b : Label τ, ∃ p : L[X], p.natDegree ≤ D ∧
      ∀ c, F c (Finsupp.single b 1) a = p.eval c)
    (z : Module.End L (RootModule τ L)) (f : ι' → L) (hf : Function.Injective f)
    (hcard : D < Fintype.card ι') (hz : ∀ j, z * F (f j) = F (f j) * z) (t : L) :
    z * F t = F t * z := by
  classical
  choose p hpdeg hpval using hF
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  set P : L[X] := ∑ d, C (z (Finsupp.single d 1) a) * p d b -
    ∑ d, p a d * C (z (Finsupp.single b 1) d) with hP
  have hev : ∀ c, P.eval c = (z * F c) (Finsupp.single b 1) a -
      (F c * z) (Finsupp.single b 1) a := by
    intro c
    rw [end_mul_single_apply, end_mul_single_apply, hP, eval_sub, eval_finsetSum,
      eval_finsetSum]
    congr 1
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [eval_mul, eval_C, ← hpval, mul_comm]
    · refine Finset.sum_congr rfl fun d _ => ?_
      rw [eval_mul, eval_C, ← hpval, mul_comm]
  have hdeg : P.natDegree ≤ D := by
    rw [hP]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · refine (natDegree_sum_le_of_forall_le _ _ fun d _ => ?_)
      exact (natDegree_C_mul_le _ _).trans (hpdeg d b)
    · refine (natDegree_sum_le_of_forall_le _ _ fun d _ => ?_)
      exact (natDegree_mul_C_le _ _).trans (hpdeg a d)
  have hP0 : P = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hf (fun j => ?_)
      (lt_of_le_of_lt hdeg hcard)
    rw [hev, hz j, sub_self]
  have := hev t
  rw [hP0, eval_zero, eq_comm, sub_eq_zero] at this
  exact this

@[expose] def conjNormalizerHom {G : Type*} [Group G] (C H : Subgroup G) :
    ↥(C ⊓ Subgroup.normalizer (H : Set G)) →* MulAut H where
  toFun g :=
    { toFun := fun h => ⟨(g : G) * h * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 g.2).2 h).1 h.2⟩
      invFun := fun h => ⟨(g : G)⁻¹ * h * g, by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem (Subgroup.mem_inf.1 g.2).2) h).1 h.2
        simpa using this⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h h' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := MulEquiv.ext fun h => Subtype.ext (by simp)
  map_mul' g g' := MulEquiv.ext fun h => Subtype.ext (by
    simp only [Subgroup.coe_mul, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply]
    group)

theorem conjNormalizerHom_apply {G : Type*} [Group G] (C H : Subgroup G)
    (g : ↥(C ⊓ Subgroup.normalizer (H : Set G))) (h : H) :
    ((conjNormalizerHom C H g h : H) : G) = (g : G) * h * (g : G)⁻¹ :=
  rfl

theorem exceptional_Lang_finite_root_centralizer_faithfulness
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (hK : Odd (Nat.card K)) (L : Type) [Field L] (ι : K →+* L) :
    Function.Injective (baseChangeGL (τ := τ) ι) ∧
    (adjointGroup τ K).map (baseChangeGL ι) ≤ adjointGroup τ L ∧
    (∀ z ∈ adjointGroup τ L, (∀ h ∈ (adjointGroup τ K).map (baseChangeGL ι), z * h = h * z) →
      z = 1) ∧
    Function.Injective (conjNormalizerHom (adjointGroup τ L)
      ((adjointGroup τ K).map (baseChangeGL ι))) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set H := (adjointGroup τ K).map (baseChangeGL ι) with hHdef
  have hHle : H ≤ adjointGroup τ L := by
    rintro _ ⟨g, hg, rfl⟩
    exact baseChangeGL_mem_adjointGroup ι hg
  have hgen : ∀ z ∈ adjointGroup τ L,
      (∀ (i : Fin τ.rank) (t : L), (z : Module.End L (RootModule τ L)) * xOp τ L i t =
        xOp τ L i t * z ∧ (z : Module.End L (RootModule τ L)) * yOp τ L i t =
          yOp τ L i t * z) → z = 1 := by
    intro z hzC hzg
    have hcent : ⟨z, hzC⟩ ∈ Subgroup.center (adjointGroup τ L) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hle : adjointGroup τ L ≤ Subgroup.centralizer {z} := by
        rw [adjointGroup, Subgroup.closure_le]
        rintro g ⟨i, c, hg | hg⟩ <;>
          refine Subgroup.mem_centralizer_singleton_iff.2 (Units.ext ?_) <;>
          rw [Units.val_mul, Units.val_mul, hg]
        · exact (hzg i c).1.symm
        · exact (hzg i c).2.symm
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hle g.2))
    rw [center_adjointGroup_eq_bot_field, Subgroup.mem_bot] at hcent
    exact congrArg Subtype.val hcent
  have hcentralizer : ∀ z ∈ adjointGroup τ L, (∀ h ∈ H, z * h = h * z) → z = 1 := by
    intro z hzC hz
    have hx : ∀ (i : Fin τ.rank) (c : K), (z : Module.End L (RootModule τ L)) *
        xOp τ L i (ι c) = xOp τ L i (ι c) * z := fun i c => by
      have h1 := hz _ ⟨xUnit τ K i c, xUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_xUnit] at h1
      exact congrArg Units.val h1
    have hy : ∀ (i : Fin τ.rank) (c : K), (z : Module.End L (RootModule τ L)) *
        yOp τ L i (ι c) = yOp τ L i (ι c) * z := fun i c => by
      have h1 := hz _ ⟨yUnit τ K i c, yUnit_mem_adjointGroup i c, rfl⟩
      rw [baseChangeGL_yUnit] at h1
      exact congrArg Units.val h1
    have hcard2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
    have hcard3 : 3 ≤ Fintype.card K := by
      rw [← Nat.card_eq_fintype_card] at hcard2 ⊢
      obtain ⟨m, hm⟩ := hK
      omega
    by_cases hD : entryDegreeBound τ < Fintype.card K
    · refine hgen z hzC fun i t => ⟨?_, ?_⟩
      · refine commute_of_polynomial_entries (F := xOp τ L i) (fun a b => ?_) _ ι ι.injective hD
          (fun c => hx i c) t
        obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
        exact ⟨p, hp, fun c => (hpq c).1⟩
      · refine commute_of_polynomial_entries (F := yOp τ L i) (fun a b => ?_) _ ι ι.injective hD
          (fun c => hy i c) t
        obtain ⟨p, q, hp, hq, hpq⟩ := exists_entry_polynomial (R := L) τ i a b
        exact ⟨q, hq, fun c => (hpq c).2⟩
    ·
      have hG2 : τ = .G2 := by
        by_contra hne
        apply hD
        simp only [entryDegreeBound, hne, ↓reduceIte]
        omega
      subst hG2
      have hK3 : Fintype.card K = 3 := by
        simp only [entryDegreeBound, ↓reduceIte] at hD
        omega
      have h3K : ((3 : ℕ) : K) = 0 := by
        rw [← hK3]
        exact FiniteField.cast_card_eq_zero K
      have h3L : ((3 : ℕ) : L) = 0 := by
        rw [← map_natCast ι, h3K, map_zero]
      have : CharP L 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).2 h3L
      have hx1 : ∀ i, Commute (z : Module.End L (RootModule Tag.G2 L)) (xOp Tag.G2 L i 1) :=
        fun i => by
          have h := hx i 1
          rw [map_one] at h
          exact h
      have hy1 : ∀ i, Commute (z : Module.End L (RootModule Tag.G2 L)) (yOp Tag.G2 L i 1) :=
        fun i => by
          have h := hy i 1
          rw [map_one] at h
          exact h
      obtain ⟨a, ha⟩ := (G2_char_three_commutant L (ringChar.eq L 3)
        (z : Module.End L (RootModule Tag.G2 L))).1 ⟨hx1 _, hy1 _, hx1 _, hy1 _⟩
      refine hgen z hzC fun i t => ⟨?_, ?_⟩ <;> rw [ha, smul_mul_assoc, one_mul, mul_smul_comm,
        mul_one]
  refine ⟨baseChangeGL_injective ι, hHle, hcentralizer, ?_⟩
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  apply Subtype.ext
  refine hcentralizer g (Subgroup.mem_inf.1 g.2).1 fun h hh => ?_
  have h1 := congrArg (fun φ : MulAut H => ((φ ⟨h, hh⟩ : H) : ModGL τ L)) hg
  simp only [conjNormalizerHom_apply, MulAut.one_apply] at h1
  calc (g : ModGL τ L) * h = (g * h * (g : ModGL τ L)⁻¹) * g := by group
    _ = h * g := by rw [h1]

end CFSG.LieType.Chevalley
