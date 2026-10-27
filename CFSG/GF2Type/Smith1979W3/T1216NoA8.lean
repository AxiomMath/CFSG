module

public import CFSG.GF2Type.Smith1979W3.T1216Census
public import CFSG.GF2Type.Smith1979W3.T1216Lift
public import CFSG.GF2Type.Smith1979W3.T1216A8Swap
public import CFSG.GF2Type.Smith1979W3.T1216SquareData

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690

theorem exists_ρ_apply_eq_of_mbarModel_eq_omega {G : Type} [Group G] [Finite G] (S : Setting G)
    {L : S.Qt ≃ₗ[ZMod 2] V₀} (hL : ∀ v, qPlus (L v) = S.q v)
    (hΩ : mbarModel S L = Ω₀ false) :
    ∀ v w : S.Qt, v ≠ 0 → w ≠ 0 → S.q v = 0 → S.q w = 0 →
      ∃ m : S.M, (S.ρ m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w := by
  intro v w hv hw hqv hqw
  have hLv : L v ≠ 0 := fun h => hv (L.injective (by rw [h, map_zero]))
  have hLw : L w ≠ 0 := fun h => hw (L.injective (by rw [h, map_zero]))
  have hqLv : qPlus (L v) = 0 := (hL v).trans hqv
  have hqLw : qPlus (L w) = 0 := (hL w).trans hqw
  have h5 : 5 ≤ Module.finrank (ZMod 2) V₀ := by
    rw [Module.finrank_fin_fun]
    norm_num
  obtain ⟨g, hgΩ, hgvw⟩ := exists_mem_omegaGroup_apply_eq qPlus_nondegenerate h5 hLv hLw
    (by rw [hqLv, hqLw])
  have hg : g ∈ mbarModel S L := by
    rw [hΩ]
    exact hgΩ
  obtain ⟨m, hm⟩ := (mem_mbarModel_iff S L).mp hg
  refine ⟨m, ?_⟩
  have h := congrArg (fun e : V₀ ≃ₗ[ZMod 2] V₀ => e (L v)) hm
  simp only [conjL_apply, LinearEquiv.symm_apply_apply] at h
  exact L.injective (h.trans hgvw)

private theorem card_sq_subtype_eq {G : Type} [Group G] (S : Setting G) (a' c : S.Q) :
    Nat.card {x : G // x ∈ S.M ∧ x * ((a' : S.M) : G) = ((a' : S.M) : G) * x ∧
        x * x = ((c : S.M) : G)} =
      Nat.card {x : S.M // x * a' = a' * x ∧ x * x = c} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_, ?_⟩
      invFun := fun y => ⟨(y.1 : G), y.1.2, ?_, ?_⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl }
  · apply Subtype.ext
    simpa using x.2.2.1
  · apply Subtype.ext
    simpa using x.2.2.2
  · simpa using congrArg (fun z : S.M => (z : G)) y.2.1
  · simpa using congrArg (fun z : S.M => (z : G)) y.2.2

theorem t1216W3NoA8_of (hP : CensusPlusProp) (hF : PGLFactsProp) (hA8 : A8SquareProp) :
    T1216W3NoA8 := by
  intro G _ _ _ S hw hirr hb hcard
  have hplus : QtPlusType S := qtPlusType_of_card S hw (Or.inr hcard)
  obtain ⟨L, hL⟩ := exists_isometry_qPlus S hw hplus
  have hΩ : mbarModel S L = Ω₀ false :=
    mbarModel_eq_omega hP hF S hw hirr hb hcard L hL
  have htrans := exists_ρ_apply_eq_of_mbarModel_eq_omega S hL hΩ
  have hb' : ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
    obtain ⟨g, hgQ, hgne, -⟩ := hb
    exact ⟨g, hgQ, hgne⟩
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Q0 S hL
  let a' : S.Q := φ.symm a0
  let a : G := ((a' : S.M) : G)
  have hpa : φ a' = a0 := MulEquiv.apply_symm_apply φ a0
  have ha0sq : a0 * a0 = 1 := by
    apply Q0.ext
    · rw [mul_a, one_a]
      simp only [a0, zero_add]
      rw [beta0_self, qPlus_apply]
      decide
    · rw [mul_v, one_v]
      simpa [a0] using CharTwo.add_self_eq_zero (Code.vec 1)
  have ha0ne1 : a0 ≠ 1 := by
    intro h
    have h' := congrFun (congrArg Q0.v h) 0
    simp [a0, Code.vec, Code.bitZ] at h'
  have ha0nez : a0 ≠ z0 := by
    intro h
    have h' := congrArg Q0.a h
    simp [a0, z0] at h'
  have ha'2 : a' * a' = 1 := by
    simpa using congrArg φ.symm ha0sq
  have hpz : φ S.zQ = z0 := phi_zQ S φ
  have ha'1 : a' ≠ 1 := by
    intro h
    apply ha0ne1
    have h' : φ a' = φ 1 := congrArg φ h
    rw [hpa, map_one] at h'
    exact h'
  have ha'z : a' ≠ S.zQ := by
    intro h
    apply ha0nez
    have h' : φ a' = φ S.zQ := congrArg φ h
    rw [hpa, hpz] at h'
    exact h'
  have ha : a ∈ S.QG := Subgroup.mem_map.mpr ⟨(a' : S.M), a'.2, rfl⟩
  have ha2 : a * a = 1 := by
    simpa using congrArg (fun q : S.Q => ((q : S.M) : G)) ha'2
  have ha1 : a ≠ 1 := by
    intro h
    exact ha'1 (Subtype.ext (Subtype.ext h))
  have haz : a ≠ S.z := by
    intro h
    exact ha'z (Subtype.ext (Subtype.ext h))
  have hswap := card_sq_eq_z_eq_card_sq_eq S htrans hb' ha ha2 ha1 haz
  have hMz : Nat.card {x : S.M // x * a' = a' * x ∧ x * x = S.zQ} =
      Nat.card {x : S.M // x * a' = a' * x ∧ x * x = a'} := by
    rw [← card_sq_subtype_eq S a' S.zQ, ← card_sq_subtype_eq S a' a']
    exact hswap
  have hcount_z := card_sq_eq S φ hφ a' S.zQ
  have hcount_a := card_sq_eq S φ hφ a' a'
  have h2 : 2 * Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (mbarModel S L) ∧ θ (φ a') = φ a' ∧
          sqData S φ θ = φ S.zQ} =
      2 * Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (mbarModel S L) ∧ θ (φ a') = φ a' ∧
          sqData S φ θ = φ a'} := by
    rw [← hcount_z, ← hcount_a]
    exact hMz
  have hKeq : Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (mbarModel S L) ∧ θ (φ a') = φ a' ∧
          sqData S φ θ = φ S.zQ} =
      Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (mbarModel S L) ∧ θ (φ a') = φ a' ∧
          sqData S φ θ = φ a'} :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2
  have hSD : IsSquareData (Ω₀ false) (sqData S φ) := by
    simpa only [hΩ] using isSquareData S φ hφ
  obtain ⟨h120, hZmem⟩ := hA8 (sqData S φ) hSD
  have hZeq : Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ sqData S φ θ = z0} =
      Set.ncard {θ : Q0 ≃* Q0 |
        θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ sqData S φ θ = a0} := by
    simpa only [hΩ, hpa, hpz] using hKeq
  have hZeq120 : Set.ncard {θ : Q0 ≃* Q0 |
      θ ∈ ThetaOver (Ω₀ false) ∧ θ a0 = a0 ∧ sqData S φ θ = z0} = 120 := by
    rw [hZeq, h120]
  rw [hZeq120] at hZmem
  exact absurd hZmem (by decide)

end CFSG.GF2Type.Smith1979W3

end
