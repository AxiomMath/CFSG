module

public import CFSG.LieType.HighestRoot.CentG2
public import CFSG.ClassicalInvolution.ModelFacts.Families
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLang

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Universal

section Characters

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_smul_eq_of_single
    {a b : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ i, rootChar a (w • (Pi.single i 1 : Fin τ.rank → ℤ)) = b i)
    (v : Fin τ.rank → ℤ) : rootChar a (w • v) = rootChar b v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, CFSG.LieType.Chevalley.rootChar_sum]
  conv_rhs => rw [hv, CFSG.LieType.Chevalley.rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [CFSG.LieType.Chevalley.rootChar_zsmul, CFSG.LieType.Chevalley.rootChar_zsmul, h i]
  congr 1
  simpa using (rootChar_nsmul_single b i 1).symm

theorem rootDiagUnit_eq_conj_of_single
    {a b : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ i, rootChar a (w • (Pi.single i 1 : Fin τ.rank → ℤ)) = b i) :
    rootDiagUnit τ a = canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ :=
  (rootDiagUnit_eq_conj_canonicalRep_iff a b w).2 (rootChar_smul_eq_of_single h)

end Characters

section Sums

theorem sum_g2 {M : Type*} [AddCommMonoid M] (f : Fin (Tag.rank .G2) → M) :
    ∑ j, f j = f g2l + f g2s :=
  Fintype.sum_eq_add g2l g2s (by decide) fun x hx => by
    fin_cases x
    · exact absurd rfl hx.1
    · exact absurd rfl hx.2

end Sums

section Involutions

variable {K : Type} [Field K]

theorem g2_rootChar_l (v : Fin (Tag.rank .G2) → ℤ) :
    rootChar (signTuple .G2 K g2l) v = (-1 : Kˣ) ^ (2 * v g2l - v g2s) := by
  rw [rootChar_signTuple, sum_g2]
  congr 1
  rw [show Tag.cartan .G2 g2l g2l = 2 by decide, show Tag.cartan .G2 g2l g2s = -1 by decide]
  ring

theorem neg_one_zpow_one : (-1 : Kˣ) ^ (1 : ℤ) = -1 := zpow_one _

theorem neg_one_zpow_neg_one : (-1 : Kˣ) ^ (-1 : ℤ) = -1 := by
  rw [zpow_neg_one, inv_neg_one]

theorem neg_one_zpow_zero : (-1 : Kˣ) ^ (0 : ℤ) = 1 := zpow_zero _

@[expose] noncomputable def g2z
    : adjointGroup .G2 K :=
  ⟨rootDiagUnit .G2 (signTuple .G2 K g2l), by
    rw [← torusElt_neg_one_eq]
    exact torusElt_mem_adjointGroup g2l _⟩

variable [Finite K]

theorem g2_isConj_g2z
    (hK : ringChar K ≠ 2) {x : adjointGroup .G2 K} (hx : orderOf x = 2) :
    IsConj x g2z := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hodd : Odd (Nat.card K) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK)
  have hxx : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
  obtain ⟨g, b, hb, hgx⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_conj_eq_rootDiagUnit_of_involution (Or.inl rfl)
      hodd x hxx
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by decide)
  obtain ⟨w, hw⟩ : ∃ w : WeylGroup .G2, ∀ i,
      rootChar (signTuple .G2 K g2l) (w • (Pi.single i 1 : Fin (Tag.rank .G2) → ℤ)) = b i := by
    rcases hb g2l with hb0 | hb0 <;> rcases hb g2s with hb1 | hb1
    · exfalso
      apply hx1
      have hb1' : b = 1 := funext fun i => by fin_cases i <;> assumption
      rw [hb1', rootDiagUnit_one] at hgx
      have hgx' : g * x * g⁻¹ = 1 := Subtype.ext hgx
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [hgx']; group
    ·
      refine ⟨1, fun i => ?_⟩
      rw [one_smul, g2_rootChar_l]
      fin_cases i
      · rw [hb0, show 2 * (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ) g2l -
          (Pi.single g2l 1 : Fin (Tag.rank .G2) → ℤ) g2s = 2 by decide]
        exact (show Even (2 : ℤ) by decide).neg_one_zpow
      · rw [hb1, show 2 * (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ) g2l -
          (Pi.single g2s 1 : Fin (Tag.rank .G2) → ℤ) g2s = -1 by decide]
        exact neg_one_zpow_neg_one
    ·
      refine ⟨simple .G2 g2s * simple .G2 g2l, fun i => ?_⟩
      fin_cases i
      · rw [g2_w_smul_e0, g2_rootChar_l, hb0, show 2 * g2w0 g2l - g2w0 g2s = 1 by decide]
        exact neg_one_zpow_one
      · rw [g2_w_smul, g2_rootChar_l, hb1, show 2 * g2δ g2l - g2δ g2s = 0 by decide]
        exact neg_one_zpow_zero
    ·
      refine ⟨simple .G2 g2s, fun i => ?_⟩
      rw [simple_smul, g2_rootChar_l]
      fin_cases i
      · rw [hb0, show 2 * reflect .G2 g2s (Pi.single g2l 1) g2l -
          reflect .G2 g2s (Pi.single g2l 1) g2s = -1 by decide]
        exact neg_one_zpow_neg_one
      · rw [hb1, show 2 * reflect .G2 g2s (Pi.single g2s 1) g2l -
          reflect .G2 g2s (Pi.single g2s 1) g2s = 1 by decide]
        exact neg_one_zpow_one
  have hconj := rootDiagUnit_eq_conj_of_single (K := K) hw
  set n : adjointGroup .G2 K := ⟨canonicalRep (coxeterSystem .G2) K w,
    canonicalRep_mem_adjointGroup _ K w⟩
  rw [isConj_iff]
  refine ⟨n * g, Subtype.ext ?_⟩
  have e : n * g * x * (n * g)⁻¹ = n * (g * x * g⁻¹) * n⁻¹ := by group
  rw [e]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgx]
  exact hconj.symm

theorem g2_involutions_isConj
    (hK : ringChar K ≠ 2) (x y : adjointGroup .G2 K)
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (g2_isConj_g2z hK hx).trans (g2_isConj_g2z hK hy).symm

end Involutions

section Datum

open CFSG.ClassicalInvolution.ModelFacts in
theorem g2_e0_isLongest
    (K : Type) [Field K] :
    g2e0 ∈ (g2Datum K).roots ∧ ∀ δ ∈ (g2Datum K).roots,
      rootForm (g2Datum K) δ δ ≤ rootForm (g2Datum K) g2e0 g2e0 :=
  isLongest_single_G2 rfl _ (k := g2l) rfl

variable {K : Type} [Field K]

theorem g2_coe_eq_of_mem
    (hK : ringChar K ≠ 2) {z : adjointGroup .G2 K}
    (hz : z ∈ rankOneGroup (g2Datum K) g2e0) (h2 : orderOf z = 2) :
    (z : ModGL .G2 K) = rootDiagUnit .G2 (signTuple .G2 K g2l) := by
  rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)] at hz
  rw [← torusElt_neg_one_eq]
  exact eq_torusElt_neg_one hK g2l (Subgroup.mem_subgroupOf.1 hz) (by rwa [Subgroup.orderOf_coe])

theorem g2_centralizer_le_normalizer
    (hK : ringChar K ≠ 2) {z : adjointGroup .G2 K}
    (hz : z ∈ rankOneGroup (g2Datum K) g2e0) (h2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ≤
      Subgroup.normalizer (rankOneGroup (g2Datum K) g2e0 : Set (adjointGroup .G2 K)) := by
  have hzC := g2_coe_eq_of_mem hK hz h2
  rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)]
  exact centralizer_le_normalizer_subgroupOf hzC (g2_toralCentralizer_le_normalizer hK (Or.inl rfl))

@[expose] noncomputable def g2L₀
    (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) :=
  (rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)).subgroupOf (adjointGroup .G2 K)

theorem g2L₀_le
    : rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ) ≤ adjointGroup .G2 K :=
  sup_le (rootSubgroup_le_adjointGroup _) (rootSubgroup_le_adjointGroup _)

theorem g2L₀_equiv
    (hK : ringChar K ≠ 2) :
    Nonempty (g2L₀ K ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨e⟩ := (odd_arbitrary_root_pair_SL2_p_components .G2 K hK isRoot_g2δ).2.1
  exact ⟨(Subgroup.subgroupOfEquivOfLe g2L₀_le).trans e.symm⟩

theorem g2_mem_toralCentralizer_iff
    {z : adjointGroup .G2 K}
    (hzC : (z : ModGL .G2 K) = rootDiagUnit .G2 (signTuple .G2 K g2l)) (y : adjointGroup .G2 K) :
    (y : ModGL .G2 K) ∈ toralCentralizer .G2 K (signTuple .G2 K g2l) ↔
      y ∈ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := by
  rw [mem_toralCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨-, h⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hzC]
    calc (y : ModGL .G2 K) * rootDiagUnit .G2 (signTuple .G2 K g2l) =
        (rootDiagUnit .G2 (signTuple .G2 K g2l) * y * (rootDiagUnit .G2 (signTuple .G2 K g2l))⁻¹) *
          rootDiagUnit .G2 (signTuple .G2 K g2l) := by rw [h]
      _ = rootDiagUnit .G2 (signTuple .G2 K g2l) * y := by group
  · intro h
    refine ⟨y.2, ?_⟩
    have h' := congrArg (fun x : adjointGroup .G2 K => (x : ModGL .G2 K)) h
    simp only [Subgroup.coe_mul, hzC] at h'
    calc rootDiagUnit .G2 (signTuple .G2 K g2l) * y * (rootDiagUnit .G2 (signTuple .G2 K g2l))⁻¹ =
        (y : ModGL .G2 K) * rootDiagUnit .G2 (signTuple .G2 K g2l) *
          (rootDiagUnit .G2 (signTuple .G2 K g2l))⁻¹ := by rw [h']
      _ = y := by group

theorem g2_eq_or_eq_datum
    [Finite K] (hK : ringChar K ≠ 2) {z : adjointGroup .G2 K}
    (hzC : (z : ModGL .G2 K) = rootDiagUnit .G2 (signTuple .G2 K g2l))
    {L : Subgroup (adjointGroup .G2 K)}
    (hLC : L ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)))
    (hCL : Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ≤
      Subgroup.normalizer (L : Set (adjointGroup .G2 K)))
    (eL : L ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    L = rankOneGroup (g2Datum K) g2e0 ∨ L = g2L₀ K := by
  have hL'X : L.map (adjointGroup .G2 K).subtype ≤
      toralCentralizer .G2 K (signTuple .G2 K g2l) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (g2_mem_toralCentralizer_iff hzC x).2 (hLC hx)
  have hL'N : rootSpan .G2 K (rootCharKernel (signTuple .G2 K g2l)) ≤
      Subgroup.normalizer ((L.map (adjointGroup .G2 K).subtype : Subgroup (ModGL .G2 K)) :
        Set (ModGL .G2 K)) := by
    intro y hy
    have hyH : y ∈ adjointGroup .G2 K := rootSpan_le_adjointGroup K _ hy
    have hyC : (⟨y, hyH⟩ : adjointGroup .G2 K) ∈
        Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) :=
      (g2_mem_toralCentralizer_iff hzC ⟨y, hyH⟩).1
        (rootSpan_rootCharKernel_le_toralCentralizer _ hy)
    exact Subgroup.le_normalizer_map (adjointGroup .G2 K).subtype ⟨⟨y, hyH⟩, hCL hyC, rfl⟩
  have eL' : L.map (adjointGroup .G2 K).subtype ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Subgroup.equivMapOfInjective L (adjointGroup .G2 K).subtype Subtype.val_injective).symm.trans
      eL
  have hback : ∀ {Q : Subgroup (ModGL .G2 K)}, L.map (adjointGroup .G2 K).subtype = Q →
      L = Q.subgroupOf (adjointGroup .G2 K) := by
    intro Q hQ
    rw [← hQ]
    exact (Subgroup.comap_map_eq_self_of_injective Subtype.val_injective L).symm
  rcases g2_eq_or_eq hK hL'X hL'N eL' with h | h
  · left
    rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)]
    exact hback h
  · exact Or.inr (hback h)

theorem highestRootCZ_G2
    (hK : ringChar K ≠ 2) (h3 : Nat.card K ≠ 3) :
    HighestRootCZ (g2Datum K) K :=
  ⟨g2e0, (g2_e0_isLongest K).1, (g2_e0_isLongest K).2, fun _ hz h2 =>
    ⟨g2_centralizer_le_normalizer hK hz h2, fun h => absurd h h3⟩⟩

theorem map_conj_subgroupOf {G : Type*} [Group G] {H X : Subgroup G} (n : H) :
    (X.subgroupOf H).map (MulAut.conj n).toMonoidHom =
      (X.map (MulAut.conj (n : G)).toMonoidHom).subgroupOf H := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem g2_exists_smul_eq
    {γ : Fin (Tag.rank .G2) → ℤ} (hγ : γ ∈ (g2Datum K).roots)
    (hlong : ∀ δ ∈ (g2Datum K).roots, rootForm (g2Datum K) δ δ ≤ rootForm (g2Datum K) γ γ) :
    ∃ w : WeylGroup .G2, w • g2e0 = γ := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · refine ⟨w, ?_⟩
    have h := hlong g2e0 (g2_e0_isLongest K).1
    change CFSG.ClassicalInvolution.ModelFacts.lenSq (isFiniteType_cartan .G2)
        (Pi.single g2l 1) ≤ CFSG.ClassicalInvolution.ModelFacts.lenSq (isFiniteType_cartan .G2)
        (CFSG.LieType.RootSystem.weylAction (isFiniteType_cartan .G2) w (Pi.single i 1)) at h
    rw [CFSG.ClassicalInvolution.ModelFacts.lenSq_weylAction,
      CFSG.ClassicalInvolution.ModelFacts.lenSq_single,
      CFSG.ClassicalInvolution.ModelFacts.lenSq_single] at h
    fin_cases i
    · rfl
    · exfalso
      have hs := CFSG.ClassicalInvolution.ModelFacts.symmetrizer_mul_apply
        (isFiniteType_cartan .G2) g2l g2s
      rw [show Tag.cartan .G2 g2l g2s = -1 by decide,
        show Tag.cartan .G2 g2s g2l = -3 by decide] at hs
      have hpos := CFSG.LieType.RootSystem.symmetrizer_pos (isFiniteType_cartan .G2) g2s
      push_cast at hs
      change 2 * CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan .G2) g2l ≤
        2 * CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan .G2) g2s at h
      linarith
  · exact absurd hi (Set.notMem_empty i)

theorem not_highestRootCZ_G2_three
    (hK : ringChar K ≠ 2) (h3 : Nat.card K = 3) :
    ¬ HighestRootCZ (g2Datum K) K := by
  rintro ⟨γ, hγ, hlong, hCZ⟩
  obtain ⟨w, rfl⟩ := g2_exists_smul_eq hγ hlong
  set n : adjointGroup .G2 K :=
    ⟨canonicalRep (coxeterSystem .G2) K w, canonicalRep_mem_adjointGroup _ K w⟩
  set φ : MulAut (adjointGroup .G2 K) := MulAut.conj n
  have hJ : rankOneGroup (g2Datum K) (w • g2e0) =
      (rankOneGroup (g2Datum K) g2e0).map φ.toMonoidHom := by
    rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l), map_conj_subgroupOf,
      rankOneGroup_adjDatum _ (IsRoot.smul (isRoot_single .G2 g2l) w), Subgroup.map_sup,
      (canonical_weyl_root_transport .G2 K).2.1 w _ (isRoot_single .G2 g2l),
      (canonical_weyl_root_transport .G2 K).2.1 w _ (IsRoot.neg (isRoot_single .G2 g2l)),
      smul_neg]
  set z : adjointGroup .G2 K := g2z
  have hzJ : z ∈ rankOneGroup (g2Datum K) g2e0 := by
    rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)]
    exact Subgroup.mem_subgroupOf.2 (g2_rootDiagUnit_mem_long hK).1
  have hz2 : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact (g2_rootDiagUnit_mem_long hK).2
  have hL₀C : g2L₀ K ≤ Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (g2_commute hK (g2_rootDiagUnit_mem_long hK).1 (Subgroup.mem_subgroupOf.1 hl)).eq.symm))
  have hCL₀ : Subgroup.centralizer ({z} : Set (adjointGroup .G2 K)) ≤
      Subgroup.normalizer (g2L₀ K : Set (adjointGroup .G2 K)) :=
    centralizer_le_normalizer_subgroupOf rfl (g2_toralCentralizer_le_normalizer hK (Or.inr rfl))
  obtain ⟨eL₀⟩ := g2L₀_equiv hK
  have hzL₀ : z ∈ g2L₀ K := Subgroup.mem_subgroupOf.2 (g2_rootDiagUnit_mem_short hK)
  have hφz : φ z ∈ rankOneGroup (g2Datum K) (w • g2e0) :=
    hJ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hzJ
  have hφz2 : orderOf (φ z) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hz2
  have hL := (hCZ (φ z) hφz hφz2).2 h3 ((g2L₀ K).map φ.toMonoidHom) ?_ ?_
    ⟨(Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).symm.trans eL₀⟩
    (Subgroup.mem_map_of_mem φ.toMonoidHom hzL₀)
  ·
    rw [hJ] at hL
    have hL' := Subgroup.map_injective φ.injective hL
    obtain ⟨x, y, hxy⟩ := exists_not_commute_sl2 (K := K)
    apply hxy
    have ha : ((eL₀.symm x : g2L₀ K) : adjointGroup .G2 K) ∈ rankOneGroup (g2Datum K) g2e0 :=
      hL' ▸ (eL₀.symm x).2
    rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)] at ha
    have hc := g2_commute hK (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 (eL₀.symm y).2)
    have e : eL₀.symm x * eL₀.symm y = eL₀.symm y * eL₀.symm x := Subtype.ext (Subtype.ext hc.eq)
    simpa using congrArg eL₀ e
  · rintro _ ⟨l, hl, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hL₀C hl)
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h]
  · rw [← Subgroup.map_equiv_normalizer_eq]
    intro g hg
    rw [Subgroup.mem_map_equiv]
    apply hCL₀
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hg]

theorem g2InvolutionData
    [Finite K] (hK : ringChar K ≠ 2) : G2InvolutionData (g2Datum K) K := by
  refine ⟨fun x y hx hy => g2_involutions_isConj hK x y hx hy, g2e0, (g2_e0_isLongest K).1,
    (g2_e0_isLongest K).2, fun z hz h2 => ⟨g2_centralizer_le_normalizer hK hz h2, g2L₀ K,
      g2L₀_equiv hK, ?_, ?_, ?_, ?_⟩⟩
  · have hzC := g2_coe_eq_of_mem hK hz h2
    exact Subgroup.mem_subgroupOf.2 (hzC ▸ g2_rootDiagUnit_mem_short hK)
  · exact centralizer_le_normalizer_subgroupOf (g2_coe_eq_of_mem hK hz h2)
      (g2_toralCentralizer_le_normalizer hK (Or.inr rfl))
  · intro x hx y hy
    rw [rankOneGroup_adjDatum _ (isRoot_single .G2 g2l)] at hx
    exact Subtype.ext (g2_commute hK (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy)).eq
  · rintro L hLC hCL ⟨eL⟩ -
    exact g2_eq_or_eq_datum hK (g2_coe_eq_of_mem hK hz h2) hLC hCL eL

end Datum

end CFSG.LieType.HighestRoot
