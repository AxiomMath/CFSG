module

public import CFSG.LieType.AlgebraicGroups.E6RationalGraphCoset
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorOddBasic

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Normal

variable {C : Type} [Group C]

theorem eq_of_isComponentOf_of_normal_quasisimple {K J F : Subgroup C}
    (hJq : CFSG.IsQuasisimple J) (hJF : J ≤ F) (hJn : (J.subgroupOf F).Normal)
    (hsolv : Group.IsSolvable (F ⧸ J.subgroupOf F)) (hK : Assembly.IsComponentOf K F) :
    K = J := by
  have hKq' : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).1 hK.2.2
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := OddToralOrdinary.exists_mul_ne_mul_of_isQuasisimple hKq'
  have hKJ : K ≤ J := by
    intro y hy
    have hf := MonoidHom.range_eq_bot_iff.1
      (LieType.Chevalley.OddToralOrdinary.range_eq_bot_of_commutator_eq_top hK.2.2.1
        ((QuotientGroup.mk' (J.subgroupOf F)).comp (Subgroup.inclusion hK.1)))
    have hy' : (QuotientGroup.mk (Subgroup.inclusion hK.1 ⟨y, hy⟩) : F ⧸ J.subgroupOf F) = 1 :=
      DFunLike.congr_fun hf ⟨y, hy⟩
    exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hK.1 ⟨y, hy⟩)).1 hy'
  have hKc : Assembly.IsComponentOf K J :=
    LieType.Chevalley.OddToralOrdinary.isComponentOf_of_le_of_le hK hKJ hJF
  have hsub := LieType.Chevalley.OddToralOrdinary.isSubnormal_subgroupOf_of_assembly hKc.2.1
  rcases quasisimple_subnormal_subgroups hJq hsub with h | h
  · exact le_antisymm hKJ (Subgroup.subgroupOf_eq_top.1 h)
  · exfalso
    apply hxy₀
    have := Subgroup.mem_center_iff.1
      (h (show (⟨y₀, hKJ hy₀⟩ : J) ∈ K.subgroupOf J from hy₀)) ⟨x₀, hKJ hx₀⟩
    exact congrArg Subtype.val this

theorem assembly_isSubnormal_trans_normal {L Y B : Subgroup C} (h : Assembly.IsSubnormal L Y)
    (hYB : Y ≤ B) (hYn : (Y.subgroupOf B).Normal) : Assembly.IsSubnormal L B :=
  h.trans (.step hYB hYn (.refl B))

end Normal

section Signed

open CFSG.LieType.Chevalley.E6SignedGraph

variable {K : Type} [Field K]

theorem signed_rootGenerated_not_smallType [Finite K] (hK : ringChar K ≠ 2) :
    ¬ SmallType (rootGenerated K) := by
  obtain ⟨w₁, hw₁, a₁, he₁⟩ := exists_orbitImage_eq (simpleOrbit_spec 0).1
  obtain ⟨w₂, hw₂, a₂, he₂⟩ := exists_orbitImage_eq (simpleOrbit_spec 1).1
  have hO₁ : orbitImage w₁ a₁ ∈ orbits := he₁ ▸ (simpleOrbit_spec 0).1
  have hO₂ : orbitImage w₂ a₂ ∈ orbits := he₂ ▸ (simpleOrbit_spec 1).1
  have hE : iform (∑ α ∈ orbitImage w₂ a₂, α)
      (w₁ • (Pi.single (TwistTag.E6.orbitMin a₁) 1 : E6Vec)) = -1 := by
    have hmul := iform_orbitVec_mul hw₂ hw₁ a₂ a₁
    have hv₁ : orbitVec (orbitImage w₁ a₁) = simpleVec 0 := by
      rw [he₁]
      exact (simpleOrbit_spec 0).2
    have hv₂ : orbitVec (orbitImage w₂ a₂) = simpleVec 1 := by
      rw [he₂]
      exact (simpleOrbit_spec 1).2
    rw [hv₁, hv₂, show iform (simpleVec 1) (simpleVec 1) = 4 by decide +kernel,
      show iform (simpleVec 1) (simpleVec 0) = -2 by decide +kernel] at hmul
    omega
  set q : K → ModGL TwistTag.E6.tag K := fun c => orbitSL2 K w₁ a₁ (uSL c) with hqdef
  have hconj : ∀ c, orbitSL2 K w₂ a₂ (HSL (-1)) * q c * (orbitSL2 K w₂ a₂ (HSL (-1)))⁻¹ =
      q (-c) := fun c => by
    have e := orbitTorus_conj_orbitSL2_uSL (K := K) hw₂ hw₁ a₂ a₁ (-1) c
    rw [hE] at e
    have h1 : (((-1 : Kˣ) ^ (-1 : ℤ) : Kˣ) : K) = -1 := by simp
    rw [h1, neg_one_mul] at e
    exact e
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hq1 : q 1 ≠ q (-1) := by
    intro h
    have hk : uSL (2 : K) ∈ (orbitSL2 K w₁ a₁).ker := by
      rw [MonoidHom.mem_ker]
      have e : uSL (2 : K) = uSL 1 * (uSL (-1))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, ← uSL_add]
        norm_num
      rw [e, map_mul, map_inv]
      exact mul_inv_eq_one.2 h
    have hc := ker_orbitSL2_le_center hK w₁ a₁ hk
    exact h2 (eq_zero_of_uSL_eq_one_or_neg_one (sl2_eq_one_or_neg_one_of_mem_center hc))
  set φ : SL2 K →* rootGenerated K := (orbitSL2 K w₂ a₂).codRestrict _
    fun A => range_orbitSL2_le_rootGenerated hw₂ hO₂ ⟨A, rfl⟩ with hφ
  have hφ1 : (φ (-1) : ModGL TwistTag.E6.tag K) = orbitSL2 K w₂ a₂ (HSL (-1)) := by
    rw [hφ, MonoidHom.codRestrict_apply, HSL_neg_one_eq]
  have hz : φ (-1) ∉ center (rootGenerated K) := fun hz => hq1 (by
    have hc := congrArg Subtype.val ((mem_center_iff.1 hz)
      ⟨q 1, range_orbitSL2_le_rootGenerated hw₁ hO₁ ⟨_, rfl⟩⟩)
    change q 1 * (φ (-1) : ModGL TwistTag.E6.tag K) = (φ (-1) : ModGL TwistTag.E6.tag K) * q 1
      at hc
    rw [hφ1] at hc
    have := hconj 1
    rw [← hc, mul_inv_cancel_right] at this
    exact this)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro A hA
    have hA' : orbitSL2 K w₂ a₂ A = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hA)
    rcases sl2_eq_one_or_neg_one_of_mem_center (ker_orbitSL2_le_center hK w₂ a₂ hA') with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · exfalso
      apply hz
      have h1 : φ (-1) = 1 := Subtype.ext (by
        change orbitSL2 K w₂ a₂ (-1) = 1
        rw [← h]
        exact hA')
      rw [h1]
      exact Subgroup.one_mem _
  exact not_smallType_of_sl2 hK φ hinj hz

end Signed

section Rational

open CFSG.LieType.Chevalley.E6SignedGraph

theorem rationalRootGroup_not_smallType {K : Type} [Field K] (σ : K ≃+* K)
    [Finite (fixSubfield σ)] (hK : ringChar (fixSubfield σ) ≠ 2)
    {AK : ModGL TwistTag.E6.tag (fixSubfield σ)}
    (hAK : AK = diagramMap TwistTag.E6 _ ∨
      AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) :
    ¬ SmallType (rationalRootGroup σ AK) := by
  rw [rationalRootGroup, ← smallType_congr (Subgroup.equivMapOfInjective _ _
    (baseChangeGL_injective (fixSubfield σ).subtype))]
  rcases hAK with rfl | rfl
  · have hinner : (posUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
        graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) ⊔
          (negUnipotent TwistTag.E6.tag (fixSubfield σ) ⊓
            graphCentralizer TwistTag.E6.tag (fixSubfield σ) (diagramMap TwistTag.E6 _)) =
        graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
      rw [graphFixedRootGroup, graphFixedPosUnipotent, graphFixedNegUnipotent,
        twistedFixedGroup_id_eq]
    rw [hinner]
    exact graphFixedRootGroup_E6_odd_not_smallType hK _ Function.surjective_id
  · exact signed_rootGenerated_not_smallType hK

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem finite_fixSubfield_frobenius {e : ℕ} (he : 1 ≤ e) :
    Finite (fixSubfield (iterateFrobeniusEquiv k p e)) := by
  have hq1 : 1 < p ^ e := Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt
  have hP0 : (Polynomial.X ^ (p ^ e) - Polynomial.X : Polynomial k) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero k hq1
  refine Set.Finite.to_subtype ((Polynomial.finite_setOfPred_isRoot hP0).subset fun c hc => ?_)
  rw [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, sub_eq_zero]
  exact hc

theorem e6_rational_graph_coset_not_smallType (hp : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {ε : ℕ}
    (hε : ε = 0 ∨ ε = 1) {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)))
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) {L : Subgroup (ModGL TwistTag.E6.tag k)}
    (hL : Assembly.IsComponentOf L
      (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε)),
        fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k ^ ε))⁆ ⊓
        Subgroup.centralizer {x * diagramMap TwistTag.E6 k})) : ¬ SmallType L := by
  classical
  obtain ⟨-, -, -, hrep⟩ := E6_rational_graph_coset_fixed_components p hp he k halg ε hε
  obtain ⟨⟨y, hyR, hyA'⟩, -⟩ := hrep x hx hx2
  obtain ⟨A, hAdef⟩ : ∃ A, y * (x * diagramMap TwistTag.E6 k) * y⁻¹ = A := ⟨_, rfl⟩
  obtain ⟨AK, hAK⟩ : ∃ AK : ModGL TwistTag.E6.tag (fixSubfield (iterateFrobeniusEquiv k p e)),
      (A = diagramMap TwistTag.E6 k ∧ AK = diagramMap TwistTag.E6 _) ∨
      (A = rootDiagUnit TwistTag.E6.tag (signTuple k) * diagramMap TwistTag.E6 k ∧
        AK = rootDiagUnit TwistTag.E6.tag (signTuple _) * diagramMap TwistTag.E6 _) := by
    rw [hAdef] at hyA'
    rcases hyA' with h | h
    · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨h, rfl⟩⟩
  obtain ⟨-, -, hSJ, hSn, hcomm, hSq, hP1, hD1⟩ :=
    E6_canonical_graph_centralizer_rational_fixed_components p hp he k A AK hAK
  set P := diagramMap TwistTag.E6 k with hPdef
  set F := frobTwistGL TwistTag.E6.tag k p e (P ^ ε) with hFdef
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hRdef
  obtain ⟨hyG, hFy⟩ := Subgroup.mem_inf.1 hyR
  have hFy' : F y = y := hFy
  set B := R ⊓ Subgroup.centralizer {x * P} with hBdef
  have hHR : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_self R
  have hBR : B ≤ R := inf_le_left
  have hHB : ⁅R, R⁆ ⊓ B = ⁅R, R⁆ ⊓ Subgroup.centralizer {x * P} := by
    rw [hBdef, ← inf_assoc, inf_eq_left.2 hHR]
  have : (⁅R, R⁆.subgroupOf R).Normal := commutator_subgroupOf_normal R
  have hLB : Assembly.IsComponentOf L B := by
    rw [← hHB] at hL
    exact ⟨hL.1.trans inf_le_right, assembly_isSubnormal_trans_normal hL.2.1 inf_le_right
      (normal_inf_subgroupOf hBR), hL.2.2⟩
  have hBJ : B.map (MulAut.conj y).toMonoidHom =
      frobFixedCentralizer TwistTag.E6.tag p e A (P ^ ε) := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨hbR, hbc⟩ := Subgroup.mem_inf.1 hb
      obtain ⟨hbG, hbF⟩ := Subgroup.mem_inf.1 hbR
      have hbF' : F b = b := hbF
      rw [Subgroup.mem_centralizer_singleton_iff] at hbc
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hyG hbG) (inv_mem hyG), ?_⟩,
        ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff, ← hAdef]
        calc y * b * y⁻¹ * (y * (x * P) * y⁻¹) = y * (b * (x * P)) * y⁻¹ := by group
          _ = y * ((x * P) * b) * y⁻¹ := by rw [hbc]
          _ = y * (x * P) * y⁻¹ * (y * b * y⁻¹) := by group
      · change F (y * b * y⁻¹) = y * b * y⁻¹
        rw [map_mul, map_mul, map_inv, hFy', hbF']
    · intro hw
      obtain ⟨hwZ, hwF⟩ := Subgroup.mem_inf.1 hw
      obtain ⟨hwG, hwc⟩ := Subgroup.mem_inf.1 hwZ
      have hwF' : F w = w := hwF
      rw [Subgroup.mem_centralizer_singleton_iff] at hwc
      refine ⟨y⁻¹ * w * y, Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2
        ⟨mul_mem (mul_mem (inv_mem hyG) hwG) hyG, ?_⟩, ?_⟩, ?_⟩
      · change F (y⁻¹ * w * y) = y⁻¹ * w * y
        rw [map_mul, map_mul, map_inv, hFy', hwF']
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hxP : x * P = y⁻¹ * A * y := by rw [← hAdef]; group
        rw [hxP]
        calc y⁻¹ * w * y * (y⁻¹ * A * y) = y⁻¹ * (w * A) * y := by group
          _ = y⁻¹ * (A * w) * y := by rw [hwc]
          _ = y⁻¹ * A * y * (y⁻¹ * w * y) := by group
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hLJ := isComponentOf_map_of_injective (MulAut.conj y).toMonoidHom
    (MulAut.conj y).injective hLB
  rw [hBJ] at hLJ
  obtain ⟨M, hM, ⟨eM⟩⟩ : ∃ M : Subgroup (ModGL TwistTag.E6.tag k), Assembly.IsComponentOf M
      (frobFixedCentralizer TwistTag.E6.tag p e A (P ^ 0)) ∧ Nonempty (L ≃* M) := by
    have e₁ : L ≃* L.map (MulAut.conj y).toMonoidHom :=
      L.equivMapOfInjective _ (MulAut.conj y).injective
    rcases hε with rfl | rfl
    · exact ⟨_, hLJ, ⟨e₁⟩⟩
    · rcases hAK with ⟨hA, -⟩ | ⟨hA, -⟩
      · rw [hP1 hA] at hLJ
        exact ⟨_, hLJ, ⟨e₁⟩⟩
      · obtain ⟨v, -, hv⟩ := hD1 hA
        have hLJ' := isComponentOf_map_of_injective (MulAut.conj v).toMonoidHom
          (MulAut.conj v).injective hLJ
        rw [hv] at hLJ'
        exact ⟨_, hLJ', ⟨e₁.trans (Subgroup.equivMapOfInjective _ _ (MulAut.conj v).injective)⟩⟩
  have hsolv : Group.IsSolvable (frobFixedCentralizer TwistTag.E6.tag p e A (P ^ 0) ⧸
      (rationalRootGroup (iterateFrobeniusEquiv k p e) AK).subgroupOf
        (frobFixedCentralizer TwistTag.E6.tag p e A (P ^ 0))) :=
    Group.isSolvable_of_comm (@hcomm hSn)
  have : Finite (fixSubfield (iterateFrobeniusEquiv k p e)) := finite_fixSubfield_frobenius p he
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  rw [smallType_congr eM, eq_of_isComponentOf_of_normal_quasisimple hSq hSJ hSn hsolv hM]
  exact rationalRootGroup_not_smallType _ (ringChar_fixSubfield_ne_two hk _)
    (hAK.imp (fun h => h.2) (fun h => h.2))

end Rational

end CFSG.ComponentClassification.ExcSelector
