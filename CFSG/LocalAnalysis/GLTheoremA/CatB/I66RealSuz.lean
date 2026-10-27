module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealFix
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzFuse
public import Certificates.Certificate10134
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66RealJ3B
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I66At

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.HardMathSupport.Dickson.I271.TabSuzFuse CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Sporadic.SuzOddCore (suzM suzB0 suzB1)

@[expose] noncomputable def suzGen (l : ℕ) : Equiv.Perm (Fin 1782) := if l = 0 then suzB0 else suzB1

theorem rep_suzWordArr :
    ∀ w : List ℕ, Rep 1782 (suzWordArr w) (w.map suzGen).prod
  | [] => by
    simp only [suzWordArr, List.foldr_nil, List.map_nil, List.prod_nil]
    exact rep_idA
  | l :: w => by
    have ih := rep_suzWordArr w
    simp only [suzWordArr, List.foldr_cons, List.map_cons, List.prod_cons] at ih ⊢
    refine rep_compA ?_ ih
    unfold suzGen
    split_ifs
    · exact CFSG.Sporadic.SuzOddCore.rep_b0
    · exact CFSG.Sporadic.SuzOddCore.rep_b1

theorem prod_suzGen_mem : ∀ w : List ℕ, (w.map suzGen).prod ∈ suzM
  | [] => by simp only [List.map_nil, List.prod_nil]; exact Subgroup.one_mem _
  | l :: w => by
    simp only [List.map_cons, List.prod_cons]
    refine Subgroup.mul_mem _ ?_ (prod_suzGen_mem w)
    unfold suzGen CFSG.Sporadic.SuzOddCore.suzM
    split_ifs
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem inverted_of_invertsOK {w : List ℕ} {x : Array ℕ}
    {X : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X) (hX : X ^ 3 = 1) (h : invertsOK w x = true) :
    ∃ g ∈ suzM, g * X * g⁻¹ = X⁻¹ := by
  unfold invertsOK at h
  simp only [Bool.and_eq_true] at h
  have hRG := rep_suzWordArr w
  have e1 : (w.map suzGen).prod * X = (X * X) * (w.map suzGen).prod :=
    (eqA_iff (rep_compA hRG hx) (rep_compA (rep_compA hx hx) hRG)).1 h.2
  refine ⟨(w.map suzGen).prod, prod_suzGen_mem w, ?_⟩
  calc (w.map suzGen).prod * X * ((w.map suzGen).prod)⁻¹
      = (X * X) * (w.map suzGen).prod * ((w.map suzGen).prod)⁻¹ := by rw [e1]
    _ = X⁻¹ := by
        rw [mul_inv_cancel_right]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_two, ← pow_succ]; exact hX)


theorem suz_rep_inverted
    {c : Equiv.Perm (Fin 1782)}
    (hc : c = CFSG.HardMathSupport.Dickson.I271.fuseXA ∨ c = CFSG.HardMathSupport.Dickson.I271.fuseXB ∨
      c = yPerm) : ∃ g ∈ suzM, g * c * g⁻¹ = c⁻¹ := by
  have h := Certificates.certificate10134
  unfold suzRealOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, hY⟩ := h
  rcases hc with rfl | rfl | rfl
  · exact inverted_of_invertsOK CFSG.HardMathSupport.Dickson.I271.rep_fuseXA
      CFSG.HardMathSupport.Dickson.I271.fuseXA_pow hA
  · exact inverted_of_invertsOK CFSG.HardMathSupport.Dickson.I271.rep_fuseXB
      CFSG.HardMathSupport.Dickson.I271.fuseXB_pow hB
  · exact inverted_of_invertsOK rep_y yPerm_pow hY

theorem suzM_inverted
    {s : Equiv.Perm (Fin 1782)} (hs : s ∈ suzM)
    (hs3 : orderOf s = 3) : ∃ h ∈ suzM, h * s * h⁻¹ = s⁻¹ := by
  obtain ⟨k, hk, c, hc, e, -, rfl⟩ :=
    CFSG.HardMathSupport.Dickson.I271.suz_exists_conj_classes hs hs3
  obtain ⟨g, hgM, hgc⟩ := suz_rep_inverted hc
  refine ⟨k * g * k⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hgM) (Subgroup.inv_mem _ hk), ?_⟩
  have hpow : g * c ^ e * g⁻¹ = (c ^ e)⁻¹ := by rw [← conj_pow, hgc, inv_pow]
  calc k * g * k⁻¹ * (k * c ^ e * k⁻¹) * (k * g * k⁻¹)⁻¹
      = k * (g * c ^ e * g⁻¹) * k⁻¹ := by group
    _ = k * (c ^ e)⁻¹ * k⁻¹ := by rw [hpow]
    _ = (k * c ^ e * k⁻¹)⁻¹ := by group

theorem i66_real_Suz :
    ∀ t : TauCeti.SporadicName.Suz.Group, orderOf t = 3 → IsConj t t⁻¹ := by
  intro t ht
  obtain ⟨ψ⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv
  let φ : TauCeti.SporadicName.Suz.Group ≃* ↥suzM := ψ.symm.trans CFSG.Sporadic.SuzOddCore.suzEquivM
  have hφ : orderOf ((φ t : ↥suzM) : Equiv.Perm (Fin 1782)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact ht
  obtain ⟨h, hh, hconj⟩ := suzM_inverted (φ t).2 hφ
  have hc : IsConj (φ t) (φ t)⁻¹ := isConj_iff.mpr ⟨⟨h, hh⟩, Subtype.ext (by simpa using hconj)⟩
  obtain ⟨c, hc'⟩ := isConj_iff.mp hc
  refine isConj_iff.mpr ⟨φ.symm c, ?_⟩
  have h2 := congrArg φ.symm hc'
  simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using h2

end CFSG.LocalAnalysis.GLTheoremA.CatB

namespace CFSG.LocalAnalysis.GLTheoremA

theorem i66RealS_holds :
    I66RealS :=
  ⟨CatB.i66_real_Suz, CatB.i66_real_Fi22, CatB.i66_real_Fi24, CatB.i66_j3_real_XB⟩

end CFSG.LocalAnalysis.GLTheoremA
