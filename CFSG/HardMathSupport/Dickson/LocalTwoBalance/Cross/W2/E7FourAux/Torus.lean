module

public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
public import CFSG.RankThree.PartOne.KE.E7FourPerX

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
  CFSG.RankThree.E6
open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false


section Coroot

theorem e7Four_rootSpan_mono {L : Type} [Field L] {τ : Tag} {A B : Set (Fin τ.rank → ℤ)} (h : A ⊆ B) :
    rootSpan τ L A ≤ rootSpan τ L B :=
  iSup₂_le fun γ hγ => le_iSup₂_of_le γ (h hγ) le_rfl

variable {L : Type} [Field L]

@[expose] def corootE7 (γ : Fin Tag.E7.rank → ℤ) (i : Fin Tag.E7.rank) : ℤ :=
  ∑ j, γ j * Tag.E7.cartan j i

theorem hm_corootE7 {γ : Fin Tag.E7.rank → ℤ} (hγ : IsRoot Tag.E7 γ)
    (δ : Fin Tag.E7.rank → ℤ) :
    2 * iform γ δ / iform γ γ = ∑ i, δ i * corootE7 γ i := by
  have h2 : iform γ γ = 2 :=
    CFSG.HardMathSupport.Timmesfeld.LangTorus.iform_self_eq_two_of_simplyLaced
      (Or.inr (Or.inr (Or.inl rfl))) hγ
  rw [h2]
  have hB : Tag.E7.symmetrizedCartan = Tag.E7.cartan := by
    simp [Tag.symmetrizedCartan, Tag.symmetrizer]
  have e : iform γ δ = ∑ i, δ i * corootE7 γ i := by
    simp only [iform, hB, corootE7, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  omega


theorem e7Four_pow_val_add_five {ζ : Lˣ} (h5 : ζ ^ 5 = 1) (a b : ZMod 5) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  have key : ∀ m : ℕ, ζ ^ m = ζ ^ (m % 5) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m 5]
    rw [pow_add, pow_mul, h5, one_pow, mul_one]
  rw [← pow_add, ZMod.val_add, ← key]

theorem e7Four_pow_val_zpow {ζ : Lˣ} (a : ZMod 5) (m : ℤ) :
    (ζ ^ a.val) ^ m = ζ ^ ((a.val : ℤ) * m) := by
  rw [← zpow_natCast, ← zpow_mul]

theorem rootDiagUnit_pow_val_mem_rootSpan {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {S : Set (Fin Tag.E7.rank → ℤ)} (γ : Fin 4 → Fin Tag.E7.rank → ℤ)
    (hγ : ∀ k, IsRoot Tag.E7 (γ k)) (hS : ∀ k, γ k ∈ S ∧ -γ k ∈ S)
    (c : Fin Tag.E7.rank → ZMod 5) (u : Fin 4 → ZMod 5)
    (hdec : ∀ i, c i = ∑ k, u k * ((corootE7 (γ k) i : ℤ) : ZMod 5)) :
    rootDiagUnit .E7 (fun i => ζ ^ (c i).val) ∈ rootSpan .E7 L S := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  set x : Fin 4 → ModGL .E7 L := fun k => rootSL2 .E7 L (γ k) (HSL (ζ ^ (u k).val)) with hx
  have hxk : ∀ k, x k = rootDiagUnit .E7 (fun i => (ζ ^ (u k).val) ^ corootE7 (γ k) i) :=
    fun k => rootSL2_HSL_eq_rootDiagUnit (hγ k) (corootE7 (γ k))
      (fun δ _ => hm_corootE7 (hγ k) δ) _
  have hmem : ∀ k, x k ∈ rootSpan .E7 L S := fun k => by
    have h1 := CFSG.HardMathSupport.Timmesfeld.CrossChar.rootSL2_mem_rootSpan_pair
      (L := L) (hγ k) (HSL (ζ ^ (u k).val))
    refine (e7Four_rootSpan_mono ?_) h1
    intro y hy
    rcases hy with rfl | hy
    · exact (hS k).1
    · rw [Set.mem_singleton_iff.1 hy]
      exact (hS k).2
  have hprod : rootDiagUnit .E7 (fun i => ζ ^ (c i).val) = x 0 * x 1 * x 2 * x 3 := by
    rw [hxk 0, hxk 1, hxk 2, hxk 3, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
    congr 1
    funext i
    have hc := hdec i
    rw [Fin.sum_univ_four] at hc
    have hexp : ζ ^ (c i).val = ζ ^ (((u 0).val : ℤ) * corootE7 (γ 0) i +
        ((u 1).val : ℤ) * corootE7 (γ 1) i + ((u 2).val : ℤ) * corootE7 (γ 2) i +
        ((u 3).val : ℤ) * corootE7 (γ 3) i) := by
      apply pow_val_eq_zpow_of_pow_eq_one h5
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val]
      exact hc.symm
    simp only [Pi.mul_apply]
    rw [hexp, zpow_add, zpow_add, zpow_add, e7Four_pow_val_zpow, e7Four_pow_val_zpow, e7Four_pow_val_zpow,
      e7Four_pow_val_zpow]
  rw [hprod]
  exact mul_mem (mul_mem (mul_mem (hmem 0) (hmem 1)) (hmem 2)) (hmem 3)

theorem rootDiagUnit_pow_val_mem_twistedTorus {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {n : ModGL .E7 L} {Fr : L →+* L} (hFr : ∀ x, Fr x = x ^ 2)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7F4W Fr).map (rootDiagUnitHom .E7 L))
    (c : Fin Tag.E7.rank → ZMod 5)
    (hW : ∀ j, ∑ i, c i * ((e7F4W i j : ℤ) : ZMod 5) = 2 * c j) :
    rootDiagUnit .E7 (fun i => ζ ^ (c i).val) ∈
      twistedTorusOf n (Units.map (entrywiseHom Fr)) := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  rw [hT]
  refine ⟨fun i => ζ ^ (c i).val, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_fixedCharTuples_iff]
  intro v
  rw [rootChar_pow_val_eq hζ c (e7F4W *ᵥ v), CTTorus.map_units_eq_pow hFr,
    rootChar_pow_val_eq hζ c v]
  have e1 : charVal c (e7F4W *ᵥ v) = 2 * charVal c v := by
    have h1 : charVal ((e7F4W.map (Int.cast : ℤ → ZMod 5)).transpose.mulVec c) v =
        charVal c (e7F4W *ᵥ v) := charVal_mulVec c e7F4W v
    have h2 : (e7F4W.map (Int.cast : ℤ → ZMod 5)).transpose.mulVec c = fun j => 2 * c j := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
      rw [← hW j]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← h1, h2]
    simp only [charVal, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, two_mul, e7Four_pow_val_add_five h5, sq]

theorem orderOf_rootDiagUnit_pow_val {ζ : Lˣ} (hζ : orderOf ζ = 5)
    (c : Fin Tag.E7.rank → ZMod 5) (hc : ∃ i, c i ≠ 0) :
    orderOf (rootDiagUnit .E7 (fun i => ζ ^ (c i).val) : ModGL .E7 L) = 5 := by
  have h5 : ζ ^ 5 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine orderOf_eq_prime ?_ ?_
  · have : (rootDiagUnitHom .E7 L (fun i => ζ ^ (c i).val)) ^ 5 =
        rootDiagUnitHom .E7 L 1 := by
      rw [← map_pow (rootDiagUnitHom .E7 L)]
      congr 1
      funext i
      change (ζ ^ (c i).val) ^ 5 = 1
      rw [← pow_mul, mul_comm, pow_mul, h5, one_pow]
    rw [map_one] at this
    exact this
  · intro h1
    obtain ⟨i, hi⟩ := hc
    have h2 : (fun i => ζ ^ (c i).val : Fin Tag.E7.rank → Lˣ) = 1 := by
      apply rootDiagUnit_injective
      rw [h1, rootDiagUnit_one]
    have h3 : ζ ^ (c i).val = 1 := congrFun h2 i
    exact hi (eq_of_pow_val_eq_pow_val hζ (by rw [h3]; simp))

@[expose] def e7D4Gamma (w : List (Fin Tag.E7.rank)) (k : Fin 4) : Fin Tag.E7.rank → ℤ :=
  fun j => lget (e7wl w) j.val (k.val + 1)

@[expose] def e7D4Node (k : Fin 4) : Fin Tag.E7.rank :=
  ⟨k.val + 1, by have := k.2; change k.val + 1 < 7; omega⟩

theorem wordProd_smul_node (w : List (Fin Tag.E7.rank)) (k : Fin 4) :
    (coxeterSystem Tag.E7).wordProd w • (Pi.single (e7D4Node k) 1 : Fin Tag.E7.rank → ℤ) =
      e7D4Gamma w k := by
  rw [wordProd_smul_eq_wordMat_mulVec, wordMat_e7wl]
  funext j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, toMat, e7D4Gamma, e7D4Node]

theorem e7D4Node_mem (k : Fin 4) : e7D4Node k ∈ d4Nodes Tag.E7 := by
  have := k.2
  show 1 ≤ k.val + 1 ∧ k.val + 1 ≤ 4
  omega

theorem e7Four_single_mem_D4 (k : Fin 4) :
    (Pi.single (e7D4Node k) 1 : Fin Tag.E7.rank → ℤ) ∈
      parabolicRoots Tag.E7 (d4Nodes Tag.E7) :=
  ⟨isRoot_single Tag.E7 _, fun j hj =>
    Pi.single_eq_of_ne (fun e => hj (by rw [e]; exact e7D4Node_mem k)) 1⟩

theorem e7Four_neg_single_mem_D4 (k : Fin 4) :
    (-Pi.single (e7D4Node k) 1 : Fin Tag.E7.rank → ℤ) ∈
      parabolicRoots Tag.E7 (d4Nodes Tag.E7) :=
  ⟨isRoot_neg_single Tag.E7 _, fun j hj => by
    have hne : j ≠ e7D4Node k := fun e => hj (by rw [e]; exact e7D4Node_mem k)
    have h : (Pi.single (e7D4Node k) 1 : Fin Tag.E7.rank → ℤ) j = 0 := Pi.single_eq_of_ne hne 1
    simp [h]⟩

theorem e7D4Gamma_mem (cert : D4A1Cert) (k : Fin 4) :
    e7D4Gamma cert.w k ∈ e7D4Set cert ∧ -e7D4Gamma cert.w k ∈ e7D4Set cert := by
  refine ⟨⟨_, e7Four_single_mem_D4 k, wordProd_smul_node cert.w k⟩, ⟨_, e7Four_neg_single_mem_D4 k, ?_⟩⟩
  show (coxeterSystem Tag.E7).wordProd cert.w • (-Pi.single (e7D4Node k) 1 : Fin 7 → ℤ) =
    -e7D4Gamma cert.w k
  rw [smul_neg, wordProd_smul_node]

theorem isRoot_e7D4Gamma (w : List (Fin Tag.E7.rank)) (k : Fin 4) :
    IsRoot Tag.E7 (e7D4Gamma w k) := by
  rw [← wordProd_smul_node]
  exact IsRoot.smul (isRoot_single Tag.E7 _) _

@[expose] def e7F4OrdFive : List (ℕ × (Fin 7 → ZMod 5) × (Fin 4 → ZMod 5)) :=
  [(0, ![3, 2, 0, 1, 2, 0, 4], ![1, 1, 4, 0]), (1, ![4, 0, 3, 0, 1, 2, 4], ![1, 3, 4, 0]),
   (2, ![0, 4, 3, 2, 0, 2, 2], ![1, 1, 3, 0]), (3, ![2, 4, 2, 2, 3, 3, 4], ![1, 3, 4, 0]),
   (4, ![1, 1, 4, 3, 4, 1, 4], ![1, 1, 4, 0]), (5, ![2, 1, 1, 3, 3, 4, 0], ![1, 3, 4, 0])]

theorem e7F4_ordFive_check : ∀ cert ∈ e7F4Certs, ∃ cu ∈ e7F4OrdFive, cu.1 = cert.cls ∧
    (∃ i : Fin 7, cu.2.1 i ≠ 0) ∧
    (∀ j : Fin 7, ∑ i : Fin 7, cu.2.1 i * ((lget e7F4WList i j : ℤ) : ZMod 5) = 2 * cu.2.1 j) ∧
    ∀ i : Fin 7, cu.2.1 i = ∑ k : Fin 4, cu.2.2 k *
      ((∑ j : Fin 7, lget (e7wl cert.w) j (k.val + 1) * Tag.E7.cartan j i : ℤ) : ZMod 5) := by
  decide +kernel

theorem exists_order_five_mem_D4 {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {n : ModGL .E7 L} {Fr : L →+* L} (hFr : ∀ x, Fr x = x ^ 2)
    (hT : twistedTorusOf n (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples e7F4W Fr).map (rootDiagUnitHom .E7 L))
    {cert : D4A1Cert} (hcert : cert ∈ e7F4Certs) :
    ∃ d ∈ rootSpan .E7 L (e7D4Set cert) ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)),
      orderOf d = 5 := by
  obtain ⟨⟨_, c, u⟩, -, -, hnz, hW, hdec⟩ := e7F4_ordFive_check cert hcert
  simp only at hnz hW hdec
  have hW' : ∀ j, ∑ i, c i * ((e7F4W i j : ℤ) : ZMod 5) = 2 * c j := fun j => by
    rw [← hW j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e7F4W_eq]
    rfl
  refine ⟨rootDiagUnit .E7 (fun i => ζ ^ (c i).val), ⟨?_, ?_⟩, ?_⟩
  · exact rootDiagUnit_pow_val_mem_rootSpan hζ (e7D4Gamma cert.w) (isRoot_e7D4Gamma cert.w)
      (e7D4Gamma_mem cert) c u hdec
  · exact mem_twistedFixedPoints.2
      (mem_twistedTorusOf.1 (rootDiagUnit_pow_val_mem_twistedTorus hζ hFr hT c hW')).2
  · exact orderOf_rootDiagUnit_pow_val hζ c hnz

end Coroot

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
