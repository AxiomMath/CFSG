module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27DiagData
public import CFSG.RankThree.E6.LargePrimeStabilizers

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Lattice CFSG.RankThree.E6 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace DiagWeyl

@[expose] def vecOf (u : List ℤ) : Fin Tag.E6.rank → ZMod 3 := fun i => (vget u i : ZMod 3)

theorem vecOf_injOn : ∀ u ∈ vecs3, ∀ u' ∈ vecs3, vecOf u = vecOf u' → u = u' := by
  intro u hu u' hu' h
  unfold vecs3 at hu hu'
  simp only [List.mem_map, List.mem_range] at hu hu'
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb, rfl⟩ := hu'
  have key : ∀ x y : ℕ, (((x : ℕ) : ℤ) : ZMod 3) = (((y : ℕ) : ℤ) : ZMod 3) → x % 3 = y % 3 := by
    intro x y hxy
    rw [Int.cast_natCast, Int.cast_natCast] at hxy
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 hxy
  have h0 := key _ _ (congrFun h ⟨0, by decide⟩)
  have h1 := key _ _ (congrFun h ⟨1, by decide⟩)
  have h2 := key _ _ (congrFun h ⟨2, by decide⟩)
  have h3 := key _ _ (congrFun h ⟨3, by decide⟩)
  have h4 := key _ _ (congrFun h ⟨4, by decide⟩)
  have h5 := key _ _ (congrFun h ⟨5, by decide⟩)
  have : a = b := by omega
  rw [this]

theorem vget_map_mod (l : List ℤ) (i : ℕ) : vget (l.map fun x => x % 3) i = vget l i % 3 := by
  unfold vget
  rcases h : l[i]? with _ | a
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

theorem toVec_lmulVecT6 (M : List (List ℤ)) (u : List ℤ) :
    toVec Tag.E6.rank (lmulVecT 6 M u) =
      (toMat Tag.E6.rank M).transpose.mulVec (toVec Tag.E6.rank u) :=
  toVec_lmulVecT 6 M u

theorem mulVec_vecOf_of_mem (M : List (List ℤ)) (u : List ℤ)
    (hu : (lmulVecT 6 M u).map (fun x => x % 3) = u) :
    ((toMat Tag.E6.rank M).map (Int.cast : ℤ → ZMod 3)).transpose.mulVec (vecOf u) = vecOf u := by
  funext i
  have h1 : vget ((lmulVecT 6 M u).map (fun x => x % 3)) i = vget u i := by rw [hu]
  rw [vget_map_mod] at h1
  have h2 := congrFun (toVec_lmulVecT6 M u) i
  have h3 : ((vget (lmulVecT 6 M u) i : ℤ) : ZMod 3) = (vget u i : ZMod 3) := by
    rw [← h1]
    exact (ZMod.intCast_mod (vget (lmulVecT 6 M u) i) 3).symm
  have h5 : (((toMat Tag.E6.rank M).map (Int.cast : ℤ → ZMod 3)).transpose.mulVec (vecOf u)) i
      = ((Int.castRingHom (ZMod 3)) (((toMat Tag.E6.rank M).transpose.mulVec (toVec Tag.E6.rank u)) i)) := by
    rw [RingHom.map_mulVec, Matrix.transpose_map]
    rfl
  rw [h5, ← h2]
  exact h3

theorem fixCount_le_card (M : List (List ℤ)) :
    fixCount M ≤ Nat.card {u : Fin Tag.E6.rank → ZMod 3 //
      ((toMat Tag.E6.rank M).map (Int.cast : ℤ → ZMod 3)).transpose.mulVec u = u} := by
  classical
  have hnd : (vecs3.filter fun u => (lmulVecT 6 M u).map (fun x => x % 3) = u).Nodup :=
    vecs3_nodup.filter _
  have hlen : fixCount M =
      (vecs3.filter fun u => (lmulVecT 6 M u).map (fun x => x % 3) = u).length := rfl
  rw [hlen, ← List.toFinset_card_of_nodup hnd, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_image_of_injOn (f := vecOf)]
  · refine Finset.card_le_card ?_
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
    rw [List.mem_toFinset, List.mem_filter] at hu
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, mulVec_vecOf_of_mem M u (of_decide_eq_true hu.2)⟩
  · intro u hu u' hu' h
    have hu1 := List.mem_filter.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hu))
    have hu2 := List.mem_filter.1 (List.mem_toFinset.1 (Finset.mem_coe.1 hu'))
    exact vecOf_injOn u hu1.1 u' hu2.1 h

section Weyl


@[expose] def gA : WeylGroup Tag.E6 :=
  (coxeterSystem Tag.E6).wordProd (e6Word [3, 0, 2, 1, 3, 4, 5, 0, 2, 1, 3, 4, 1, 3, 2, 0])

@[expose] def gB : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word [4, 5, 4, 3])

theorem weylMatrix_gA : weylMatrix gA = toMat Tag.E6.rank genA :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem weylMatrix_gB : weylMatrix gB = toMat Tag.E6.rank genB :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem toMat_lmul6 (A B : List (List ℤ)) :
    toMat Tag.E6.rank (lmul 6 A B) = toMat Tag.E6.rank A * toMat Tag.E6.rank B :=
  toMat_lmul 6 A B

theorem toMat_lid6 : toMat Tag.E6.rank (lid 6) = 1 := toMat_lid 6

theorem toMat_genAinv_mul : toMat Tag.E6.rank genAinv * toMat Tag.E6.rank genA = 1 := by
  rw [← toMat_lmul6, ← toMat_lid6]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem toMat_genBinv_mul : toMat Tag.E6.rank genBinv * toMat Tag.E6.rank genB = 1 := by
  rw [← toMat_lmul6, ← toMat_lid6]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem eq_of_mul_eq_one {n : ℕ} {X Y g : Matrix (Fin n) (Fin n) ℤ} (hX : X * g = 1)
    (hY : Y * g = 1) : X = Y := by
  have h : g * Y = 1 := mul_eq_one_comm.1 hY
  calc X = X * (g * Y) := by rw [h, Matrix.mul_one]
    _ = Y := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

theorem weylMatrix_gA_inv : weylMatrix gA⁻¹ = toMat Tag.E6.rank genAinv :=
  eq_of_mul_eq_one (by rw [← weylMatrix_mul, inv_mul_cancel, weylMatrix_one])
    (by rw [weylMatrix_gA]; exact toMat_genAinv_mul)

theorem weylMatrix_gB_inv : weylMatrix gB⁻¹ = toMat Tag.E6.rank genBinv :=
  eq_of_mul_eq_one (by rw [← weylMatrix_mul, inv_mul_cancel, weylMatrix_one])
    (by rw [weylMatrix_gB]; exact toMat_genBinv_mul)

@[expose] def Pw : Subgroup (WeylGroup Tag.E6) := Subgroup.closure {gA, gB}

@[expose] def gSel (b : Bool) : WeylGroup Tag.E6 := if b then gB else gA

@[expose] def gProd (ω : List Bool) : WeylGroup Tag.E6 := ω.foldl (fun g b => g * gSel b) 1

theorem gSel_mem (b : Bool) : gSel b ∈ Pw := by
  cases b
  · exact Subgroup.subset_closure (Or.inl rfl)
  · exact Subgroup.subset_closure (Or.inr rfl)

theorem foldl_gSel_mem (ω : List Bool) : ∀ g0 ∈ Pw, ω.foldl (fun g b => g * gSel b) g0 ∈ Pw := by
  induction ω with
  | nil => exact fun g0 h => h
  | cons b ω ih => exact fun g0 h => ih _ (mul_mem h (gSel_mem b))

theorem gProd_mem (ω : List Bool) : gProd ω ∈ Pw := foldl_gSel_mem ω 1 (one_mem _)

theorem weylMatrix_foldl (ω : List Bool) : ∀ (g0 : WeylGroup Tag.E6) (L0 : List (List ℤ)),
    weylMatrix g0 = toMat Tag.E6.rank L0 →
    weylMatrix (ω.foldl (fun g b => g * gSel b) g0) =
      toMat Tag.E6.rank (ω.foldl (fun M b => lmul 6 M (if b then genB else genA)) L0) := by
  induction ω with
  | nil => exact fun _ _ h => h
  | cons b ω ih =>
    intro g0 L0 h
    refine ih _ _ ?_
    rw [weylMatrix_mul, h]
    show _ = toMat Tag.E6.rank (lmul 6 L0 (if b then genB else genA))
    rw [toMat_lmul6]
    congr 1
    cases b
    · exact weylMatrix_gA
    · exact weylMatrix_gB

theorem weylMatrix_gProd (ω : List Bool) : weylMatrix (gProd ω) = toMat Tag.E6.rank (dEval ω) :=
  weylMatrix_foldl ω 1 (lid 6) (by rw [weylMatrix_one, toMat_lid6])

theorem exists_mem_dMats_of_mem_Pw {w : WeylGroup Tag.E6} (hw : w ∈ Pw) :
    ∃ M ∈ dMats, weylMatrix w = toMat Tag.E6.rank M := by
  induction hw using Subgroup.closure_induction_right with
  | one => exact ⟨lid 6, lid_mem_dMats, by rw [weylMatrix_one, toMat_lid6]⟩
  | mul_right x hx y hy ih =>
    obtain ⟨M, hM, hxM⟩ := ih
    obtain ⟨h1, -, h3, -⟩ := dMats_closed M hM
    rcases hy with rfl | hy
    · exact ⟨_, h1, by rw [weylMatrix_mul, hxM, weylMatrix_gA, toMat_lmul6]⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨_, h3, by rw [weylMatrix_mul, hxM, weylMatrix_gB, toMat_lmul6]⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨M, hM, hxM⟩ := ih
    obtain ⟨-, h2, -, h4⟩ := dMats_closed M hM
    rcases hy with rfl | hy
    · exact ⟨_, h2, by rw [weylMatrix_mul, hxM, weylMatrix_gA_inv, toMat_lmul6]⟩
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨_, h4, by rw [weylMatrix_mul, hxM, weylMatrix_gB_inv, toMat_lmul6]⟩

theorem mem_Pw_iff {w : WeylGroup Tag.E6} : w ∈ Pw ↔ ∃ ω ∈ dWords, w = gProd ω := by
  constructor
  · intro hw
    obtain ⟨M, hM, hwM⟩ := exists_mem_dMats_of_mem_Pw hw
    obtain ⟨ω, hω, rfl⟩ := List.mem_map.1 (show M ∈ dWords.map dEval from hM)
    exact ⟨ω, hω, weylMatrix_injective (by rw [hwM, weylMatrix_gProd])⟩
  · rintro ⟨ω, -, rfl⟩
    exact gProd_mem ω

theorem gProd_nodup : (dWords.map gProd).Nodup := by
  classical
  refine List.Nodup.of_map weylMatrix ?_
  have : (dWords.map gProd).map weylMatrix = dMats.map (toMat Tag.E6.rank) := by
    rw [List.map_map, dMats, List.map_map]
    exact List.map_congr_left fun ω _ => weylMatrix_gProd ω
  rw [this]
  refine List.Nodup.map_on ?_ dMats_nodup
  intro M hM M' hM' h
  exact dMats_inj M hM M' hM' fun i j => congrFun (congrFun h i) j

theorem card_Pw : Nat.card Pw = 81 := by
  classical
  have h1 : Nat.card Pw = (dWords.map gProd).toFinset.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [List.mem_toFinset, List.mem_map, mem_Pw_iff]
      exact ⟨fun ⟨ω, h1, h2⟩ => ⟨ω, h1, h2.symm⟩, fun ⟨ω, h1, h2⟩ => ⟨ω, h1, h2.symm⟩⟩)
  rw [h1, List.toFinset_card_of_nodup gProd_nodup, List.length_map]
  have := dMats_length
  rwa [dMats, List.length_map] at this

theorem exists_conj_mem_Pw {w : WeylGroup Tag.E6} (hw : w ^ 3 = 1) :
    ∃ v : WeylGroup Tag.E6, v⁻¹ * w * v ∈ Pw := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 Pw := IsPGroup.of_card (n := 4) (by rw [card_Pw]; norm_num)
  have hidx : ¬ 3 ∣ Pw.index := by
    have h := Subgroup.card_mul_index Pw
    rw [card_Pw, card_weylGroup_E6] at h
    have : Pw.index = 640 := by omega
    rw [this]
    norm_num
  let P0 : Sylow 3 (WeylGroup Tag.E6) := hP.toSylow hidx
  have hz : IsPGroup 3 (Subgroup.zpowers w) := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change ((w ^ k) ^ 3 ^ 1 : WeylGroup Tag.E6) = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (WeylGroup Tag.E6) P0 Q
  refine ⟨g, ?_⟩
  have hwQ : w ∈ (Q : Subgroup (WeylGroup Tag.E6)) := hQ (Subgroup.mem_zpowers w)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hwQ
  have : (MulAut.conj g)⁻¹ • w = g⁻¹ * w * g := by
    rw [MulAut.smul_def]
    simp
  rw [this] at hwQ
  exact hwQ

theorem card_fixed_ge {v : WeylGroup Tag.E6} (hv : v ∈ Pw) (hv3 : v ^ 3 = 1) :
    27 ≤ Nat.card {u : Fin Tag.E6.rank → ZMod 3 //
      ((weylMatrix v).map (Int.cast : ℤ → ZMod 3)).transpose.mulVec u = u} ∧
    (v = 1 → 81 ≤ Nat.card {u : Fin Tag.E6.rank → ZMod 3 //
      ((weylMatrix v).map (Int.cast : ℤ → ZMod 3)).transpose.mulVec u = u}) := by
  obtain ⟨M, hM, hvM⟩ := exists_mem_dMats_of_mem_Pw hv
  have h3 : ∀ i j : Fin 6, lget (lmul 6 M (lmul 6 M M)) i j = lget (lid 6) i j := by
    intro i j
    have h := congrArg weylMatrix hv3
    rw [weylMatrix_pow, weylMatrix_one, hvM] at h
    have h' : toMat Tag.E6.rank (lmul 6 M (lmul 6 M M)) = toMat Tag.E6.rank (lid 6) := by
      rw [toMat_lid6, toMat_lmul6, toMat_lmul6, ← pow_three]
      exact h
    exact congrFun (congrFun h' i) j
  obtain ⟨hA, hB⟩ := dMats_fix M hM h3
  rw [hvM]
  refine ⟨hA.trans (fixCount_le_card M), fun hv1 => (hB fun i j => ?_).trans (fixCount_le_card M)⟩
  have h : toMat Tag.E6.rank M = toMat Tag.E6.rank (lid 6) := by
    rw [toMat_lid6, ← hvM, hv1, weylMatrix_one]
  exact congrFun (congrFun h i) j

@[expose] noncomputable def cm (g : WeylGroup Tag.E6) :
    Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) (ZMod 3) :=
  (weylMatrix g).map (Int.castRingHom (ZMod 3))

theorem cm_mul (a b : WeylGroup Tag.E6) : cm (a * b) = cm a * cm b := by
  unfold cm
  rw [weylMatrix_mul, Matrix.map_mul]

theorem cm_one : cm (1 : WeylGroup Tag.E6) = 1 := by
  unfold cm
  rw [weylMatrix_one, Matrix.map_one _ (map_zero _) (map_one _)]

abbrev FixSet (g : WeylGroup Tag.E6) : Type :=
  {u : Fin Tag.E6.rank → ZMod 3 // (cm g).transpose.mulVec u = u}

theorem card_fixed_ge' {w : WeylGroup Tag.E6} (hw : w ^ 3 = 1) :
    27 ≤ Nat.card (FixSet w) ∧ (w = 1 → 81 ≤ Nat.card (FixSet w)) := by
  obtain ⟨v, hv⟩ := exists_conj_mem_Pw hw
  set w0 := v⁻¹ * w * v with hw0def
  have hw0 : w0 ^ 3 = 1 := by
    have := conj_pow (a := v⁻¹) (b := w) (i := 3)
    rw [inv_inv] at this
    rw [hw0def, this, hw]
    simp
  obtain ⟨h27, h81⟩ := card_fixed_ge hv hw0
  have hvv : (cm v).transpose * (cm v⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul, ← cm_mul, inv_mul_cancel, cm_one, Matrix.transpose_one]
  have hwdecomp : cm w = cm v * cm w0 * cm v⁻¹ := by
    rw [← cm_mul, ← cm_mul, hw0def]
    congr 1
    group
  have hid : (cm w).transpose * (cm v⁻¹).transpose = (cm v⁻¹).transpose * (cm w0).transpose := by
    rw [hwdecomp, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
      hvv, Matrix.mul_one]
  have key : Nat.card (FixSet w0) ≤ Nat.card (FixSet w) := by
    refine Nat.card_le_card_of_injective
      (fun z : FixSet w0 => (⟨(cm v⁻¹).transpose.mulVec z.1, ?_⟩ : FixSet w)) ?_
    · rw [Matrix.mulVec_mulVec, hid, ← Matrix.mulVec_mulVec, z.2]
    · intro z z' h
      apply Subtype.ext
      have h' := congrArg (fun u : FixSet w => (cm v).transpose.mulVec u.1) h
      simp only [Matrix.mulVec_mulVec, hvv, Matrix.one_mulVec] at h'
      exact h'
  refine ⟨h27.trans key, fun hw1 => ?_⟩
  refine (h81 ?_).trans key
  rw [hw0def, hw1, mul_one, inv_mul_cancel]

end Weyl

end DiagWeyl

end CFSG.HardMathSupport.Lang.E6Descent
