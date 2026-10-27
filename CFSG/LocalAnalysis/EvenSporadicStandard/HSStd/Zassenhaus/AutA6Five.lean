module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6FiveK

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  AutA6Three AutA6Types

namespace AutA6Five

@[expose] def ord5P : List (List ℕ) :=
  Core.pslLit.filter fun c => Core.cpow c 5 == Core.cid && c != Core.cid

@[expose] def isInv (c : List ℕ) : Bool := Core.cmul c c == Core.cid && c != Core.cid

theorem psl_centralizer_check5 : ord5P.all (fun a => (Core.cpslList a).length == 5) = true := by
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨Y, hY, rfl, h5⟩ := AutA6FiveK.ord5_of_mem ha
  unfold Core.cpslList
  rw [AutA6K.length_filter_pslL (fun y => Core.cmul y (code Y) == Core.cmul (code Y) y)
    (fun d => CFSG.Permutation.FinPack.commLaneK 10 d (CFSG.Permutation.FinPack.enc Y))
    (fun Z _ => AutA6K.comm_eqP Z Y), AutA6FiveK.beq_natBeq]
  exact AutA6FiveK.of_ord5 AutA6FiveK.c5psl hY h5

theorem aut_centralizer_check5 : ord5P.all (fun a =>
    ((Core.autL.filter fun c => Core.cmul a c == Core.cmul c a).dedup.length == 10)) = true := by
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨Y, hY, rfl, h5⟩ := AutA6FiveK.ord5_of_mem ha
  rw [AutA6FiveK.cnt_autL_eqP (psl29_le_autA6 hY), AutA6FiveK.beq_natBeq]
  exact AutA6FiveK.of_ord5 AutA6FiveK.c5aut hY h5

theorem involution_centralizer_check : ord5P.all (fun a => Core.autL.all fun y =>
    !isInv y || (Core.cmul y a != Core.cmul a y) ||
      ((Core.autL.filter fun c => Core.cmul y c == Core.cmul c y).dedup.length == 40)) = true := by
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨Y, hY, rfl, h5⟩ := AutA6FiveK.ord5_of_mem ha
  rw [List.all_eq_true]
  intro y hy
  obtain ⟨w, rfl⟩ := exists_of_mem_autL hy
  have hi : isInv (cd w) = AutA6K.invTK (CFSG.Permutation.FinPack.enc (w : P10)) :=
    (AutA6K.invTK_eq w).symm
  have hc : (Core.cmul (cd w) (code Y) == Core.cmul (code Y) (cd w)) =
      CFSG.Permutation.FinPack.commLaneK 10 (CFSG.Permutation.FinPack.enc (w : P10))
        (CFSG.Permutation.FinPack.enc Y) := AutA6K.comm_eqP (w : P10) Y
  rw [bne, hi, hc, AutA6FiveK.cnt_autL_eq, AutA6FiveK.beq_natBeq]
  cases hI : AutA6K.invTK (CFSG.Permutation.FinPack.enc (w : P10)) <;>
    cases hC : CFSG.Permutation.FinPack.commLaneK 10 (CFSG.Permutation.FinPack.enc (w : P10))
      (CFSG.Permutation.FinPack.enc Y) <;>
    simp only [Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or]
  exact CFSG.Permutation.FinPack.allK_iff.1 AutA6FiveK.inv5B _
    (CFSG.Permutation.FinPack.memK_iff.1 (AutA6FiveK.mem_y5K hY h5 hI hC))

theorem outer_involution_check : ord5P.all (fun a => Core.autL.any fun y =>
    isInv y && (Core.cmul y a == Core.cmul a y) && !Core.pslLit.contains y && !fixes3 y) = true := by
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨Y, hY, rfl, h5⟩ := AutA6FiveK.ord5_of_mem ha
  have h := AutA6FiveK.of_ord5 AutA6FiveK.outer5 hY h5
  rw [AutA6FiveK.anyK_eq_any] at h
  obtain ⟨d, hd, hdf⟩ := List.any_eq_true.1 h
  obtain ⟨w, rfl⟩ := AutA6FiveK.exists_of_mem_autK (CFSG.Permutation.FinPack.memK_iff.1
    (CFSG.Permutation.FinPack.allK_iff.1 AutA6FiveK.y5K_sub d hd))
  rw [List.any_eq_true]
  refine ⟨cd w, cd_mem_autL w, ?_⟩
  have hi : isInv (cd w) = AutA6K.invTK (CFSG.Permutation.FinPack.enc (w : P10)) :=
    (AutA6K.invTK_eq w).symm
  have hc : (Core.cmul (cd w) (code Y) == Core.cmul (code Y) (cd w)) =
      CFSG.Permutation.FinPack.commLaneK 10 (CFSG.Permutation.FinPack.enc (w : P10))
        (CFSG.Permutation.FinPack.enc Y) := AutA6K.comm_eqP (w : P10) Y
  rw [hi, hc, AutA6K.contains_psl_eq, AutA6FiveK.fixes3_eq]
  simp only [Bool.and_eq_true] at hdf ⊢
  exact ⟨⟨⟨hdf.1.1.2, hdf.1.1.1⟩, hdf.1.2⟩, hdf.2⟩

theorem code_mem_ord5P_of_orderOf {x : alternatingGroup (Fin 6)} (hx : orderOf x = 5) :
    code ((psiEquiv.symm x : ↥A6Models.psl29) : P10) ∈ ord5P := by
  have h5 : x ^ 5 = 1 := hx ▸ pow_orderOf_eq_one x
  have h1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  unfold ord5P
  rw [List.mem_filter]
  refine ⟨(mem_psl29_iff _).1 (psiEquiv.symm x).2, ?_⟩
  have hp5 : ((psiEquiv.symm x : ↥A6Models.psl29) : P10) ^ 5 = 1 := by
    have : (psiEquiv.symm x) ^ 5 = 1 := by rw [← map_pow, h5, map_one]
    simpa using congrArg Subtype.val this
  rw [← code_pow, hp5, code_one]
  simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
  rw [← code_one]
  intro h
  apply h1
  have h2 : (psiEquiv.symm x : ↥A6Models.psl29) = 1 := Subtype.ext (code_injective h)
  simpa using h2

theorem exists_aut_conj (x : alternatingGroup (Fin 6)) :
    ∃ u : AutA6, thetaEquiv u = MulAut.conj x ∧
      cd u = code ((psiEquiv.symm x : ↥A6Models.psl29) : P10) := by
  refine ⟨⟨((psiEquiv.symm x : ↥A6Models.psl29) : P10), psl29_le_autA6 (psiEquiv.symm x).2⟩, ?_, rfl⟩
  rw [thetaEquiv_mk, MulEquiv.apply_symm_apply]

theorem thetaEquiv_fix_iff {y u : AutA6} {x : alternatingGroup (Fin 6)}
    (hu : thetaEquiv u = MulAut.conj x) : thetaEquiv y x = x ↔ y * u = u * y := by
  have key : thetaEquiv (y * u * y⁻¹) = MulAut.conj (thetaEquiv y x) := by
    rw [map_mul, map_mul, map_inv, hu, conj_thetaEquiv_apply]
  constructor
  · intro h
    have h2 : thetaEquiv (y * u * y⁻¹) = thetaEquiv u := by rw [key, hu, h]
    have h3 := thetaEquiv.injective h2
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  · intro h
    have h2 : y * u * y⁻¹ = u := by rw [h, mul_inv_cancel_right]
    rw [h2, hu] at key
    exact (CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
      key).symm

theorem card_centralizer_aut_eq (α : MulAut (alternatingGroup (Fin 6))) (y : AutA6)
    (hy : thetaEquiv y = α) :
    Nat.card (Subgroup.centralizer ({α} : Set (MulAut (alternatingGroup (Fin 6))))) =
      (Core.autL.filter fun c => Core.cmul (cd y) c == Core.cmul c (cd y)).dedup.length := by
  set L := Core.autL.filter fun c => Core.cmul (cd y) c == Core.cmul c (cd y) with hL
  let f : ↥(Subgroup.centralizer ({α} : Set (MulAut (alternatingGroup (Fin 6))))) →
      ↥L.toFinset :=
    fun g => ⟨cd (thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6)))), by
    have hg := (Subgroup.mem_centralizer_iff.mp g.2) α (Set.mem_singleton _)
    have hc : y * thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) =
        thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) * y := by
      apply thetaEquiv.injective
      rw [map_mul, map_mul, hy, MulEquiv.apply_symm_apply, hg]
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨cd_mem_autL _, ?_⟩
    rw [← cd_mul, ← cd_mul, hc]
    simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      have h1 := cd_injective (congrArg Subtype.val h)
      exact Subtype.ext (thetaEquiv.symm.injective h1)
    · rintro ⟨c, hc⟩
      rw [List.mem_toFinset, hL, List.mem_filter] at hc
      obtain ⟨z, rfl⟩ := exists_of_mem_autL hc.1
      have hc2 : y * z = z * y := by
        apply cd_injective
        rw [cd_mul, cd_mul]
        simpa using hc.2
      refine ⟨⟨thetaEquiv z, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh, ← hy, ← map_mul, ← map_mul, hc2]
      · apply Subtype.ext
        simp [f]
  calc Nat.card (Subgroup.centralizer ({α} : Set (MulAut (alternatingGroup (Fin 6)))))
      = Nat.card ↥L.toFinset := Nat.card_eq_of_bijective f hf
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = L.dedup.length := List.card_toFinset L

end AutA6Five

open AutA6Five

theorem card_centralizer_of_orderOf_eq_five (a : alternatingGroup (Fin 6)) (ha : orderOf a = 5) :
    Nat.card (Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6)))) = 5 := by
  set w : ↥A6Models.psl29 := psiEquiv.symm a with hw
  have hmem := code_mem_ord5P_of_orderOf ha
  have hcheck := List.all_eq_true.mp psl_centralizer_check5 _ hmem
  rw [beq_iff_eq] at hcheck
  let f : ↥(Subgroup.centralizer ({a} : Set (alternatingGroup (Fin 6)))) →
      ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({(w : P10)} : Set P10)) :=
    fun g => ⟨((psiEquiv.symm (g : alternatingGroup (Fin 6)) : ↥A6Models.psl29) : P10),
      (psiEquiv.symm (g : alternatingGroup (Fin 6))).2, by
        have hg := (Subgroup.mem_centralizer_iff.mp g.2) a (Set.mem_singleton _)
        have : w * psiEquiv.symm (g : alternatingGroup (Fin 6)) =
            psiEquiv.symm (g : alternatingGroup (Fin 6)) * w := by
          rw [hw, ← map_mul, ← map_mul, hg]
        exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this).symm⟩
  have hf : Function.Bijective f := by
    constructor
    · intro g g' h
      have h1 := Subtype.ext_iff.mp h
      exact Subtype.ext (psiEquiv.symm.injective (Subtype.ext h1))
    · rintro ⟨p, hp1, hp2⟩
      refine ⟨⟨psiEquiv ⟨p, hp1⟩, ?_⟩, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        apply psiEquiv.symm.injective
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_singleton_iff.1 hp2).symm
      · apply Subtype.ext
        simp [f]
  rw [Nat.card_eq_of_bijective f hf, card_psl29_centralizer, hcheck]

theorem card_centralizer_conj_of_orderOf_eq_five (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 5) :
    Nat.card (Subgroup.centralizer ({MulAut.conj a} :
      Set (MulAut (alternatingGroup (Fin 6))))) = 10 := by
  obtain ⟨u, hu, hcu⟩ := exists_aut_conj a
  rw [card_centralizer_aut_eq _ u hu]
  have hmem : cd u ∈ ord5P := by rw [hcu]; exact code_mem_ord5P_of_orderOf ha
  have := List.all_eq_true.mp aut_centralizer_check5 _ hmem
  rw [beq_iff_eq] at this
  exact this

theorem card_centralizer_of_involution_of_mem_centralizer_five (a : alternatingGroup (Fin 6))
    (ha : orderOf a = 5) (c' : MulAut (alternatingGroup (Fin 6)))
    (hc' : c' ∈ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (alternatingGroup (Fin 6)))))
    (h2 : c' * c' = 1) (h1 : c' ≠ 1) :
    Nat.card (Subgroup.centralizer ({c'} : Set (MulAut (alternatingGroup (Fin 6))))) = 40 := by
  obtain ⟨u, hu, hcu⟩ := exists_aut_conj a
  set y : AutA6 := thetaEquiv.symm c' with hy
  have hyc : thetaEquiv y = c' := MulEquiv.apply_symm_apply _ _
  rw [card_centralizer_aut_eq _ y hyc]
  have hyy : y * y = 1 := aut_mul_self h2
  have hy1 : y ≠ 1 := by
    intro h
    apply h1
    rw [← hyc, h, map_one]
  have hcomm : u * y = y * u := by
    apply thetaEquiv.injective
    have := (Subgroup.mem_centralizer_iff.mp hc') (MulAut.conj a) (Set.mem_singleton _)
    rw [map_mul, map_mul, hu, hyc]
    exact this
  have hmem : cd u ∈ ord5P := by rw [hcu]; exact code_mem_ord5P_of_orderOf ha
  have h := List.all_eq_true.mp involution_centralizer_check _ hmem
  have h' := List.all_eq_true.mp h (cd y) (cd_mem_autL y)
  have hinv : isInv (cd y) = true := by
    unfold isInv
    rw [← cd_mul, hyy, cd_one]
    simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq]
    rw [← cd_one]
    exact fun h => hy1 (cd_injective h)
  have hc : (Core.cmul (cd y) (cd u) != Core.cmul (cd u) (cd y)) = false := by
    rw [← cd_mul, ← cd_mul, ← hcomm]
    simp
  rw [hinv, hc] at h'
  simpa using h'

theorem exists_outer_involution_fix_five (a : alternatingGroup (Fin 6)) (ha : orderOf a = 5) :
    ∃ γ : MulAut (alternatingGroup (Fin 6)), γ * γ = 1 ∧ γ a = a ∧
      γ ∉ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ∧
      ∀ b : alternatingGroup (Fin 6), orderOf b = 3 → γ b ≠ b := by
  obtain ⟨u, hu, hcu⟩ := exists_aut_conj a
  have hmem : cd u ∈ ord5P := by rw [hcu]; exact code_mem_ord5P_of_orderOf ha
  have h := List.all_eq_true.mp outer_involution_check _ hmem
  obtain ⟨c, hcmem, hc⟩ := List.any_eq_true.mp h
  obtain ⟨y, rfl⟩ := exists_of_mem_autL hcmem
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
  obtain ⟨⟨⟨hinv, hcomm⟩, hnp⟩, hnf⟩ := hc
  unfold isInv at hinv
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hinv
  have hyy : y * y = 1 := by
    apply cd_injective
    rw [cd_mul, cd_one, hinv.1]
  have hyu : y * u = u * y := by
    apply cd_injective
    rw [cd_mul, cd_mul]
    exact hcomm
  have hyP : y ∉ PslSub := by
    rw [mem_PslSub_iff_contains, hnp]
    simp
  refine ⟨thetaEquiv y, ?_, (thetaEquiv_fix_iff hu).2 hyu, ?_, ?_⟩
  · rw [← map_mul, hyy, map_one]
  · intro hmem'
    rw [mem_inner_iff, MulEquiv.symm_apply_apply] at hmem'
    exact hyP hmem'
  · intro b hb hfix
    have := (fixes3_iff y).1 ⟨b, hb, hfix⟩
    rw [hnf] at this
    exact absurd this (by simp)

theorem autA6Five_prop : ∀ a : alternatingGroup (Fin 6), orderOf a = 5 →
    Nat.card (Subgroup.centralizer ({MulAut.conj a} :
      Set (MulAut (alternatingGroup (Fin 6))))) = 10 ∧
    ∀ c' ∈ Subgroup.centralizer ({MulAut.conj a} : Set (MulAut (alternatingGroup (Fin 6)))),
      c' * c' = 1 → c' ≠ 1 →
        Nat.card (Subgroup.centralizer ({c'} : Set (MulAut (alternatingGroup (Fin 6))))) = 40 :=
  fun a ha => ⟨card_centralizer_conj_of_orderOf_eq_five a ha,
    fun c' hc' h2 h1 => card_centralizer_of_involution_of_mem_centralizer_five a ha c' hc' h2 h1⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
