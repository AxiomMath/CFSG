module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCard
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

theorem exists_symplectic_of_normal {X : Type} [Group X] [Finite X]
    {W : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3))}
    (e : ↥(oPPrimeHull 3 (⊤ : Subgroup X)) ≃* ↥W ⧸ CFSG.pCore 3 ↥W)
    {N : Subgroup X} [N.Normal] (hNO : N ≤ oPPrimeHull 3 ⊤) (hNgen : oPPrimeHull 3 N = N) :
    ∃ W' : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)), oPPrimeHull 3 W' = W' ∧
      Nonempty (↥N ≃* ↥W' ⧸ CFSG.pCore 3 ↥W') := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let O : Subgroup X := oPPrimeHull 3 (⊤ : Subgroup X)
  let P : Subgroup ↥W := CFSG.pCore 3 ↥W
  have hOdef : O = oPPrimeHull 3 (⊤ : Subgroup X) := rfl
  have hPdef : P = CFSG.pCore 3 ↥W := rfl
  let φ : ↥W →* ↥O := e.symm.toMonoidHom.comp (QuotientGroup.mk' P)
  have hφ_surj : Function.Surjective φ := by
    intro y
    obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective P (e y)
    refine ⟨z, ?_⟩
    change e.symm (QuotientGroup.mk' P z) = y
    rw [hz, MulEquiv.symm_apply_apply]
  have hφ_ker : φ.ker = P := by
    ext x
    rw [MonoidHom.mem_ker]
    show e.symm (QuotientGroup.mk' P x) = 1 ↔ x ∈ P
    rw [← map_one e.symm, e.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  let N' : Subgroup ↥O := N.subgroupOf O
  have hN'def : N' = N.subgroupOf O := rfl
  haveI hN'normal : N'.Normal := by
    rw [hN'def]
    infer_instance
  let Ŵ : Subgroup ↥W := N'.comap φ
  have hŴdef : Ŵ = N'.comap φ := rfl
  haveI hŴnormal : Ŵ.Normal := by
    rw [hŴdef]
    infer_instance
  have hPŴ : P ≤ Ŵ := by
    rw [hŴdef, ← hφ_ker]
    exact MonoidHom.ker_le_comap φ N'
  have h1 : ↥Ŵ ⧸ (P.subgroupOf Ŵ) ≃* ↥N' := by
    have hker : (φ.subgroupComap N').ker = P.subgroupOf Ŵ := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        rw [← hφ_ker, MonoidHom.mem_ker]
        exact congrArg Subtype.val h
      · intro h
        rw [← hφ_ker, MonoidHom.mem_ker] at h
        exact Subtype.ext h
    exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ := φ.subgroupComap N')
        (φ.subgroupComap_surjective N' hφ_surj))
  have h2 : CFSG.pCore 3 ↥Ŵ = P.subgroupOf Ŵ := by
    have := pCore_eq_subgroupOf_pCore (p := 3) (X := ↥W) Ŵ
    rw [← hPdef] at this
    exact this
  let W' : Subgroup (Matrix.symplecticGroup (Fin 2) (ZMod 3)) := Ŵ.map W.subtype
  have hW'def : W' = Ŵ.map W.subtype := rfl
  let f : ↥Ŵ ≃* ↥W' := Subgroup.equivMapOfInjective Ŵ W.subtype W.subtype_injective
  have hf : (CFSG.pCore 3 ↥Ŵ).map f.toMonoidHom = CFSG.pCore 3 ↥W' :=
    CFSG.pCore_map_iso 3 f
  have eQ : ↥Ŵ ⧸ CFSG.pCore 3 ↥Ŵ ≃* ↥W' ⧸ CFSG.pCore 3 ↥W' :=
    QuotientGroup.congr (CFSG.pCore 3 ↥Ŵ) (CFSG.pCore 3 ↥W') f hf
  have h3 : ↥N ≃* ↥W' ⧸ CFSG.pCore 3 ↥W' :=
    (Subgroup.subgroupOfEquivOfLe hNO).symm.trans
      (h1.symm.trans ((QuotientGroup.quotientMulEquivOfEq h2.symm).trans eQ))
  let s : Set ↥W := {u : ↥W | u ∈ Ŵ ∧ ∃ k : ℕ, orderOf u = 3 ^ k}
  let T : Subgroup ↥W := Subgroup.closure s
  have hTdef : T = Subgroup.closure s := rfl
  have hP3 : IsPGroup 3 P := CFSG.pCore_isPGroup (p := 3) (G := ↥W)
  have hPleT : P ≤ T := by
    intro x hx
    change x ∈ Subgroup.closure s
    refine Subgroup.subset_closure ⟨hPŴ hx, ?_⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 3) (G := P)).mp hP3 ⟨x, hx⟩
    exact ⟨k, by simpa using hk⟩
  have hN'le : N' ≤ T.map φ := by
    refine (Subgroup.map_le_map_iff_of_injective (f := O.subtype) O.subtype_injective).mp ?_
    have hN'map : N'.map O.subtype = N := by
      change (N.subgroupOf O).map O.subtype = N
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hNO
    rw [hN'map, Subgroup.map_map, ← hNgen]
    change Subgroup.closure {x : X | x ∈ N ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ≤
      T.map (O.subtype.comp φ)
    rw [Subgroup.closure_le]
    rintro x ⟨hxN, k, hk⟩
    have hxO : x ∈ O := hNO hxN
    obtain ⟨w, hw⟩ := hφ_surj ⟨x, hxO⟩
    have hwŴ : w ∈ Ŵ := by
      rw [hŴdef, Subgroup.mem_comap, hw, hN'def, Subgroup.mem_subgroupOf]
      exact hxN
    have hwT : w ∈ T := by
      change w ∈ Subgroup.closure s
      refine Subgroup.subset_closure ⟨hwŴ, ?_⟩
      have h3k : orderOf (⟨x, hxO⟩ : ↥O) = 3 ^ k := by
        rw [Subgroup.orderOf_mk, hk]
      have hwpow : w ^ (3 ^ k) ∈ P := by
        rw [← hφ_ker, MonoidHom.mem_ker, map_pow, hw, ← h3k, pow_orderOf_eq_one]
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf (p := 3) (G := P)).mp hP3
        ⟨w ^ (3 ^ k), hwpow⟩
      have hj' : orderOf (w ^ (3 ^ k)) = 3 ^ j := by
        simpa using hj
      have hw_order : orderOf w ∣ 3 ^ (k + j) := by
        apply orderOf_dvd_of_pow_eq_one
        rw [pow_add, pow_mul, ← hj', pow_orderOf_eq_one]
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hw_order
      exact ⟨m, hm⟩
    refine Subgroup.mem_map.mpr ⟨w, hwT, ?_⟩
    simp [MonoidHom.comp_apply, hw]
  have hŴT : Ŵ ≤ T := by
    intro w hw
    have hφw : φ w ∈ N' := by
      rw [hŴdef, Subgroup.mem_comap] at hw
      exact hw
    obtain ⟨t, htT, ht_eq⟩ := Subgroup.mem_map.mp (hN'le hφw)
    have hmem : t⁻¹ * w ∈ P := by
      rw [← hφ_ker, MonoidHom.mem_ker, map_mul, map_inv, ht_eq, inv_mul_cancel]
    have hw_eq : w = t * (t⁻¹ * w) := by rw [mul_inv_cancel_left]
    rw [hw_eq]
    exact T.mul_mem htT (hPleT hmem)
  have hW'ge : W' ≤ oPPrimeHull 3 W' := by
    have hTle : T.map W.subtype ≤ oPPrimeHull 3 W' := by
      have hgen : W.subtype '' s ⊆
          {x : Matrix.symplecticGroup (Fin 2) (ZMod 3) |
            x ∈ W' ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
        rintro _ ⟨u, ⟨huŴ, k, hk⟩, rfl⟩
        exact ⟨Subgroup.mem_map_of_mem W.subtype huŴ, k,
          by rw [orderOf_injective W.subtype W.subtype_injective u, hk]⟩
      calc T.map W.subtype = (Subgroup.closure s).map W.subtype := by rw [hTdef]
        _ = Subgroup.closure (W.subtype '' s) := MonoidHom.map_closure W.subtype s
        _ ≤ Subgroup.closure {x : Matrix.symplecticGroup (Fin 2) (ZMod 3) |
              x ∈ W' ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := Subgroup.closure_mono hgen
        _ = oPPrimeHull 3 W' := rfl
    calc W' = Ŵ.map W.subtype := hW'def
      _ ≤ T.map W.subtype := Subgroup.map_mono hŴT
      _ ≤ oPPrimeHull 3 W' := hTle
  have hW'le : oPPrimeHull 3 W' ≤ W' := by
    change Subgroup.closure {x : Matrix.symplecticGroup (Fin 2) (ZMod 3) |
        x ∈ W' ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ≤ W'
    rw [Subgroup.closure_le]
    rintro x ⟨hxW', -, -⟩
    exact hxW'
  exact ⟨W', le_antisymm hW'le hW'ge, ⟨h3⟩⟩

theorem sixThreeOneList_of_normal {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hO : SixThreeOneList p ↥(oPPrimeHull p (⊤ : Subgroup X)))
    {N : Subgroup X} [N.Normal] (hNgen : oPPrimeHull p N = N) (hx : ∃ x ∈ N, orderOf x = p) :
    SixThreeOneList p ↥N ∧ Nat.card ↥N ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup X := oPPrimeHull p (⊤ : Subgroup X)
  have hOdef : O = oPPrimeHull p (⊤ : Subgroup X) := rfl
  have hNO : N ≤ O := by
    rw [hOdef, ← hNgen]
    change Subgroup.closure {x : X | x ∈ N ∧ ∃ k, orderOf x = p ^ k} ≤
      Subgroup.closure {x : X | x ∈ ⊤ ∧ ∃ k, orderOf x = p ^ k}
    exact Subgroup.closure_mono (fun x hx => ⟨trivial, hx.2⟩)
  have hcard : Nat.card ↥N ≠ 1 := by
    obtain ⟨x, hxN, hxord⟩ := hx
    intro h1
    have hsub : Subsingleton ↥N := (Nat.card_eq_one_iff_unique.mp h1).1
    have hx1 : x = 1 := by
      have : (⟨x, hxN⟩ : ↥N) = ⟨1, N.one_mem⟩ := Subsingleton.elim _ _
      exact Subtype.ext_iff.mp this
    exact hp.ne_one (by rw [← hxord, hx1, orderOf_one])
  refine ⟨?_, hcard⟩
  have hO' : SixThreeOneList p ↥O := hO
  have key : N = O → SixThreeOneList p ↥N := fun hEq =>
    SixThreeOneList.of_mulEquiv (MulEquiv.subgroupCongr hEq.symm) hO'
  rcases hO with h | h | h | h
  · rcases h with h | h | h | h
    · exact key (eq_oPPrimeHull_of_not_sq_dvd hNO hx (not_sq_dvd_card_of_isSLType_two h))
    · obtain ⟨esl⟩ := h
      have hq : CFSG.IsQuasisimple ↥O :=
        CFSG.IsQuasisimple.of_mulEquiv esl
          (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple
            3 (ZMod p) (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))
      obtain ⟨x, hxN, hxord⟩ := hx
      have hy : orderOf (esl ⟨x, hNO hxN⟩) = p := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxord]
      have hnc := not_mem_center_SL3_of_orderOf hy
      rw [Subgroup.mem_center_iff] at hnc
      push Not at hnc
      obtain ⟨z, hz⟩ := hnc
      refine key (eq_of_normal_of_isQuasisimple hNO hq
        ⟨x, hxN, (esl.symm z : ↥O), (esl.symm z).2, ?_⟩)
      intro hcomm
      have hOcomm : (⟨x, hNO hxN⟩ : ↥O) * esl.symm z =
          esl.symm z * ⟨x, hNO hxN⟩ := by
        apply Subtype.ext
        simpa using hcomm
      have hzy : esl ⟨x, hNO hxN⟩ * z = z * esl ⟨x, hNO hxN⟩ := by
        simpa using congrArg esl hOcomm
      exact hz hzy.symm
    · exact key (eq_oPPrimeHull_of_not_sq_dvd hNO hx (not_sq_dvd_card_of_isPSLType_two hp2 h))
    · exfalso
      obtain ⟨x, hxN, hxord⟩ := hx
      have hsub : Subsingleton ↥O := (Nat.card_eq_one_iff_unique.mp h).1
      have hx1 : x = 1 := Subtype.ext_iff.mp (Subsingleton.elim (⟨x, hNO hxN⟩ : ↥O) 1)
      exact hp.ne_one (by rw [← hxord, hx1, orderOf_one])
  · obtain ⟨hp7, hExt⟩ := h
    subst p
    refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
      (not_sq_dvd_card_of_isExtNotation (p := 7) ?_ ?_ hExt))
    · rintro V _ _ ⟨e7⟩
      rw [Nat.card_congr e7.toEquiv, natCard_alternatingGroup_fin 7 (by norm_num)]
      norm_num
    · rintro V _ _ hV
      rw [hV]
      norm_num
  · obtain ⟨hp5, h5⟩ := h
    subst p
    rcases h5 with h5 | h5 | h5
    · refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
        (not_sq_dvd_card_of_isExtNotation (p := 5) ?_ ?_ h5))
      · rintro V _ _ ⟨e6⟩
        rw [Nat.card_congr e6.toEquiv, natCard_alternatingGroup_fin 6 (by norm_num)]
        norm_num
      · rintro V _ _ hV
        rw [hV]
        norm_num
    · refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
        (not_sq_dvd_card_of_isExtNotation (p := 5) ?_ ?_ h5))
      · rintro V _ _ ⟨e5⟩
        rw [Nat.card_congr e5.toEquiv, natCard_alternatingGroup_fin 5 (by norm_num)]
        norm_num
      · rintro V _ _ hV
        exact not_dvd_card_of_isQ8D8Type (p := 5) (by norm_num) hV
    · refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
        (not_sq_dvd_card_of_isExtNotation (p := 5) ?_ ?_ h5))
      · rintro V _ _ hV
        rw [hV]
        norm_num
      · rintro V _ _ hV
        exact not_dvd_card_of_isQ8D8Type (p := 5) (by norm_num) hV
  · obtain ⟨hp3, h3⟩ := h
    subst p
    rcases h3 with h3 | h3 | h3 | h3
    · exact key (eq_oPPrimeHull_of_not_sq_dvd hNO hx (not_sq_dvd_card_of_isSLType_two_five h3))
    · refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
        (not_sq_dvd_card_of_isExtNotation (p := 3) ?_ ?_ h3))
      · rintro V _ _ ⟨e5⟩
        rw [Nat.card_congr e5.toEquiv, natCard_alternatingGroup_fin 5 (by norm_num)]
        norm_num
      · rintro V _ _ hV
        exact not_dvd_card_of_isQ8D8Type (p := 3) (by norm_num) hV
    · refine key (eq_oPPrimeHull_of_not_sq_dvd hNO hx
        (not_sq_dvd_card_of_isExtNotation (p := 3) ?_ ?_ h3))
      · rintro V _ _ hV
        rw [hV]
        norm_num
      · rintro V _ _ hV
        rw [hV]
        norm_num
    · obtain ⟨W, hWgen, ⟨eW⟩⟩ := h3
      exact Or.inr (Or.inr (Or.inr
        ⟨rfl, Or.inr (Or.inr (Or.inr (exists_symplectic_of_normal eW hNO hNgen)))⟩))

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
