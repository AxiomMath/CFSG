module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSp

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance CFSG.ComponentClassification CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.ClassicalInvolution.Models (two_ne_zero_of_odd_natCard)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

section Sp

variable {F : Type} [Field F] {n : ℕ}

theorem componentOddCore_statedSp_eq_bot [Finite F] (hF : Nat.card F = 3) (a : ℕ) :
    componentClassificationOddCore (StatedSp a F) = ⊥ := by
  rcases Nat.lt_or_ge a 2 with h | h
  · interval_cases a
    · have := subsingleton_statedSp_zero (F := F)
      exact Subsingleton.elim _ _
    · have h1 := OddCore.equiv_invariant (longBlockEquivOne (K := F))
      rw [componentOddCore_sl2_eq_bot hF, Subgroup.map_bot] at h1
      exact h1.symm
  · exact componentOddCore_eq_bot_of_isQuasisimple
      (open_isQuasisimple (CFSG.LieType.Universal.Symplectic.isQuasisimple a F (by omega)
        (Or.inr (Or.inl ⟨hF, h⟩))))
      (centerExp_statedSp a 1 F (by rw [hF]; norm_num)).isPGroup

theorem mulVec_mem_minusSpace {i c : StatedSp n F} (hc : c * i = i * c)
    {v : Fin n ⊕ Fin n → F} (hv : v ∈ minusSpace i) : mat n F c *ᵥ v ∈ minusSpace i := by
  rw [mem_minusSpace, Matrix.mulVec_mulVec, ← map_mul, ← hc, map_mul, ← Matrix.mulVec_mulVec,
    mem_minusSpace.1 hv, Matrix.mulVec_neg]

theorem conj_mem_complGroup {i c x : StatedSp n F} (hc : c * i = i * c)
    (hx : x ∈ complGroup i) : c * x * c⁻¹ ∈ complGroup i := by
  have hc' : c⁻¹ * i = i * c⁻¹ := (Commute.inv_left (show Commute c i from hc)).eq
  intro v hv
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    mem_complGroup.1 hx _ (mulVec_mem_minusSpace hc' hv), Matrix.mulVec_mulVec, ← map_mul,
    mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem exists_smul_of_mem_center {x : StatedSp n F} (hx : x ∈ Subgroup.center (StatedSp n F)) :
    ∃ c : F, mat n F x = c • 1 := by
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hx
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp hx
  refine ⟨u, ?_⟩
  have h := congrArg (fun y : GL (Fin n ⊕ Fin n) F =>
    (y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) hu
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal] at h
  exact h.symm

theorem mem_center_of_mat_eq_neg_one {z : StatedSp n F}
    (h : mat n F z = (-1 : F) • 1) : z ∈ Subgroup.center (StatedSp n F) := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply mat_injective
  rw [map_mul, map_mul, h]
  simp

theorem eq_one_of_mat_eq_one {z : StatedSp n F} (h : mat n F z = 1) : z = 1 :=
  mat_injective (by rw [h, map_one])

theorem eq_one_of_mem_center_of_mem_longRootGroup (h2 : (2 : F) ≠ 0) {z : StatedSp n F}
    (hz : z * z = 1) (hzc : z ∉ Subgroup.center (StatedSp n F)) {x : StatedSp n F}
    (hx : x ∈ Subgroup.center (StatedSp n F)) (hxL : x ∈ longRootGroup z) : x = 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_mem_center hx
  have h1 := (mem_longRootGroup_iff_mat h2 hz).mp hxL
  rw [hc, Matrix.smul_mul, Matrix.one_mul] at h1
  by_cases hc1 : c = 1
  · exact eq_one_of_mat_eq_one (by rw [hc, hc1, one_smul])
  · exfalso
    apply hzc
    have h3 : ePlus (mat n F z) = 0 := by
      have : (c - 1) • ePlus (mat n F z) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
    have h4 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) + mat n F z = 0 := by
      rw [one_add_eq_smul_ePlus h2, h3, smul_zero]
    exact mem_center_of_mat_eq_neg_one (by rw [neg_one_smul]; exact eq_neg_of_add_eq_zero_right h4)

theorem eq_one_of_mem_center_of_mem_complGroup (h2 : (2 : F) ≠ 0) {z : StatedSp n F}
    (hz : z * z = 1) (hzc : z ∉ Subgroup.center (StatedSp n F)) {x : StatedSp n F}
    (hx : x ∈ Subgroup.center (StatedSp n F)) (hxL : x ∈ complGroup z) : x = 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_mem_center hx
  have h1 := (mem_complGroup_iff_mat h2 hz).mp hxL
  rw [hc, Matrix.smul_mul, Matrix.one_mul] at h1
  by_cases hc1 : c = 1
  · exact eq_one_of_mat_eq_one (by rw [hc, hc1, one_smul])
  · exfalso
    apply hzc
    have h3 : eMinus (mat n F z) = 0 := by
      have : (c - 1) • eMinus (mat n F z) = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hc1)
    have h4 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - mat n F z = 0 := by
      rw [one_sub_eq_smul_eMinus h2, h3, smul_zero]
    have h5 : mat n F z = 1 := (sub_eq_zero.mp h4).symm
    exact Subgroup.mem_center_iff.mpr fun y => by
      rw [eq_one_of_mat_eq_one h5, one_mul, mul_one]

theorem oddCoreIn_centralizer_eq_bot_of_sp_sq_eq_one [Finite F] (hF : Nat.card F = 3)
    {z : StatedSp n F} (hz : z * z = 1) (hzc : z ∉ Subgroup.center (StatedSp n F)) :
    oddCoreIn (Subgroup.centralizer
      ({(QuotientGroup.mk z : StatedSp n F ⧸ Subgroup.center (StatedSp n F))} :
        Set (StatedSp n F ⧸ Subgroup.center (StatedSp n F)))) = ⊥ := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_natCard (by rw [hF]; decide)
  obtain ⟨S, g, hSg⟩ := exists_mul_eq_stdInv h2 hz
  have hzg : z = g * stdInv F S * g⁻¹ := eq_mul_inv_of_mul_eq hSg
  obtain ⟨eL⟩ := nonempty_mulEquiv_longRootGroup_sp h2 hzg
  obtain ⟨eC⟩ := nonempty_mulEquiv_complGroup_sp h2 hzg
  have hk : Nat.card F = 2 ^ 1 + 1 := by rw [hF]; norm_num
  have hZ : IsPGroup 2 (Subgroup.center (StatedSp n F)) :=
    (centerExp_statedSp n 1 F hk).isPGroup
  set π := QuotientGroup.mk' (Subgroup.center (StatedSp n F)) with hπ
  refine oddCoreIn_centralizer_eq_bot_of_blocks hZ z (ι := Bool)
    (fun b => cond b (complGroup z) (longRootGroup z)) ?_ ?_ ?_ ?_
  · intro b x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    cases b
    · exact comm_of_mem_longRootGroup h2 hz hx
    · exact comm_of_mem_complGroup h2 hz hx
  · intro b c hc x hx
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
    cases b
    · exact conj_mem_longRootGroup hc' hx
    · exact conj_mem_complGroup hc' hx
  · intro b
    cases b
    · show oddCoreIn ((longRootGroup z).map π) = ⊥
      set Θ : StatedSp S.card F →* StatedSp n F := (longRootGroup z).subtype.comp eL.toMonoidHom
      have hrange : Θ.range = longRootGroup z := by
        ext y
        constructor
        · rintro ⟨a, rfl⟩
          exact (eL a).2
        · intro hy
          obtain ⟨a, ha⟩ := eL.surjective ⟨y, hy⟩
          exact ⟨a, congrArg Subtype.val ha⟩
      rw [← hrange, ← MonoidHom.range_comp]
      refine oddCoreIn_range_eq_bot_of_injective _ ?_ (componentOddCore_statedSp_eq_bot hF _)
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : Θ a ∈ Subgroup.center (StatedSp n F) := (QuotientGroup.eq_one_iff _).mp ha
      have h3 := eq_one_of_mem_center_of_mem_longRootGroup h2 hz hzc h1 (eL a).2
      exact eL.map_eq_one_iff.mp (Subtype.ext h3)
    · show oddCoreIn ((complGroup z).map π) = ⊥
      set Θ : StatedSp (Sᶜ).card F →* StatedSp n F := (complGroup z).subtype.comp eC.toMonoidHom
      have hrange : Θ.range = complGroup z := by
        ext y
        constructor
        · rintro ⟨a, rfl⟩
          exact (eC a).2
        · intro hy
          obtain ⟨a, ha⟩ := eC.surjective ⟨y, hy⟩
          exact ⟨a, congrArg Subtype.val ha⟩
      rw [← hrange, ← MonoidHom.range_comp]
      refine oddCoreIn_range_eq_bot_of_injective _ ?_ (componentOddCore_statedSp_eq_bot hF _)
      rw [injective_iff_map_eq_one]
      intro a ha
      have h1 : Θ a ∈ Subgroup.center (StatedSp n F) := (QuotientGroup.eq_one_iff _).mp ha
      have h3 := eq_one_of_mem_center_of_mem_complGroup h2 hz hzc h1 (eC a).2
      exact eC.map_eq_one_iff.mp (Subtype.ext h3)
  · intro ν hν hL
    have hνz : ν * z = z * ν := Subgroup.mem_centralizer_singleton_iff.mp hν
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_commute h2 hz hνz
    have hxy : x * y = y * x := commute_of_mem_longRootGroup_of_mem_complGroup h2 hz hx hy
    refine ⟨1, ?_⟩
    have hxc : (⟨x, hx⟩ : longRootGroup z) ∈ Subgroup.center (longRootGroup z) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hw : x * y * (w : StatedSp n F) = (w : StatedSp n F) * (x * y) := hL false w w.2
      have hyw : (w : StatedSp n F) * y = y * w :=
        commute_of_mem_longRootGroup_of_mem_complGroup h2 hz w.2 hy
      show (w : StatedSp n F) * x = x * w
      apply mul_right_cancel (b := y)
      calc (w : StatedSp n F) * x * y = w * (x * y) := by group
        _ = x * y * w := hw.symm
        _ = x * (y * w) := by group
        _ = x * (w * y) := by rw [hyw]
        _ = x * w * y := by group
    have hyc : (⟨y, hy⟩ : complGroup z) ∈ Subgroup.center (complGroup z) := by
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      have hw : x * y * (w : StatedSp n F) = (w : StatedSp n F) * (x * y) := hL true w w.2
      have hxw : x * (w : StatedSp n F) = w * x :=
        commute_of_mem_longRootGroup_of_mem_complGroup h2 hz hx w.2
      show (w : StatedSp n F) * y = y * w
      apply mul_left_cancel (a := x)
      calc x * (w * y) = (x * w) * y := by group
        _ = (w * x) * y := by rw [hxw]
        _ = w * (x * y) := by group
        _ = x * y * w := hw.symm
        _ = x * (y * w) := by group
    have hx2 : x ^ 2 = 1 := by
      have := CenterExp.of_mulEquiv eL.symm (centerExp_statedSp S.card 1 F hk) _ hxc
      exact congrArg Subtype.val this
    have hy2 : y ^ 2 = 1 := by
      have := CenterExp.of_mulEquiv eC.symm (centerExp_statedSp (Sᶜ).card 1 F hk) _ hyc
      exact congrArg Subtype.val this
    rw [pow_one, Commute.mul_pow hxy, hx2, hy2, mul_one]

end Sp

end CFSG.ClassicalInvolution.Q3
