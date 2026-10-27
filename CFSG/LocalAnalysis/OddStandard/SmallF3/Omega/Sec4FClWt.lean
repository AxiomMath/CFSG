module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FClXt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDBlock
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma piOrth_mul_t_eq_blockHom {t : OGroup Q} (htt : t * t = 1) :
    (piOrth Q * t : OGroup Q) =
      blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
  have h1 := blockHom_piOrth_piOrth htt
  have h2 := blockHom_one_piOrth htt
  calc piOrth Q * t
      = blockHom htt (piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          blockHom htt (1, piOrth (Q.restrict (commSp t))) := by rw [h1, h2]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), piOrth (Q.restrict (commSp t))) *
          (1, piOrth (Q.restrict (commSp t)))) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) := by
          rw [Prod.mk_mul_mk, mul_one, piOrth_mul_self]

private lemma piOrth_mul_t_mul_blockInr {t : OGroup Q} (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) :
    (piOrth Q * t) * blockInr htt b =
      blockHom htt (piOrth (Q.restrict (fixSp t)), b) := by
  calc (piOrth Q * t) * blockInr htt b
      = blockHom htt (piOrth (Q.restrict (fixSp t)), 1) * blockHom htt (1, b) := by
          rw [piOrth_mul_t_eq_blockHom htt, blockInr_apply]
    _ = blockHom htt ((piOrth (Q.restrict (fixSp t)), 1) * (1, b)) := (map_mul _ _ _).symm
    _ = blockHom htt (piOrth (Q.restrict (fixSp t)), b) := by
          rw [Prod.mk_mul_mk, mul_one, one_mul]

private lemma piOrth_mul_t_mul_blockInr_commute (hQ : Q.Nondegenerate) {t : OGroup Q}
    (htt : t * t = 1) (b : OGroup (Q.restrict (commSp t))) :
    ((piOrth Q * t) * blockInr htt b) * t = t * ((piOrth Q * t) * blockInr htt b) := by
  have hpit : Commute (piOrth Q) t :=
    (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t).symm
  have hbt : Commute (blockInr htt b) t :=
    Subgroup.mem_centralizer_singleton_iff.mp (blockInr_mem_centralizer hQ htt b)
  exact ((hpit.mul_left (Commute.refl t)).mul_left hbt).eq

private lemma piOrth_mul_t_mul_blockInr_apply_fixSp {t : OGroup Q} (htt : t * t = 1)
    (b : OGroup (Q.restrict (commSp t))) (v : fixSp t) :
    ((((piOrth Q * t) * blockInr htt b : OGroup Q) : V ≃ₗ[ZMod 3] V) (v : V)) =
      -(v : V) := by
  rw [piOrth_mul_t_mul_blockInr htt b]
  have h := blockHom_apply htt (piOrth (Q.restrict (fixSp t)), b) v (0 : commSp t)
  rw [Submodule.coe_zero, add_zero] at h
  rw [h]
  simp [coe_piOrth_apply]

theorem sec4FClDt_card_le (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    Nat.card (Sec4FDDt hQ t) ≤ 12130560 := by
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  let C : Subgroup (OGroup Q) := Subgroup.centralizer ({t} : Set (OGroup Q))
  let D : Subgroup (OGroup Q) := Sec4FDDt hQ t
  have hDC : D ≤ C := by
    change Sec4FDDt hQ t ≤ Subgroup.centralizer ({t} : Set (OGroup Q))
    rw [Sec4FDDt]
    exact inf_le_right
  have hdimU : Module.finrank (ZMod 3) (commSp t) = 6 := by
    have := congrArg Prod.fst ht6
    simpa only [invType, invDim] using this
  have hsgnU : quadSign (Q.restrict (commSp t)) = 1 := by
    have := congrArg Prod.snd ht6
    simpa only [invType, invSign] using this
  have hfix1 : Module.finrank (ZMod 3) (fixSp t) = 1 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have hU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  have hcardC : Nat.card C = 48522240 := by
    change Nat.card (Subgroup.centralizer ({t} : Set (OGroup Q))) = 48522240
    rw [natCard_centralizer_involution hQ htt]
    have h1 : Nat.card (OGroup (Q.restrict (fixSp t))) = 2 :=
      natCard_oGroup_one (nondegenerate_restrict_fixSp hQ htt) hfix1
    have h2 : Nat.card (OGroup (Q.restrict (commSp t))) = 4 * 6065280 := by
      have hcard := Subgroup.card_mul_index (H := omegaGroup hU)
      rw [index_omegaGroup hU (by omega : 2 ≤ Module.finrank (ZMod 3) (commSp t)),
        natCard_omegaGroup_six_plus hU hdimU hsgnU] at hcard
      omega
    rw [h1, h2]
  have hπt_center : t * piOrth Q = piOrth Q * t :=
    Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t
  have hC1 : (1 : OGroup Q) ∈ C := by
    change (1 : OGroup Q) ∈ Subgroup.centralizer ({t} : Set (OGroup Q))
    exact Subgroup.one_mem _
  have hCt : t ∈ C := by
    change t ∈ Subgroup.centralizer ({t} : Set (OGroup Q))
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hCpi : piOrth Q ∈ C := by
    change piOrth Q ∈ Subgroup.centralizer ({t} : Set (OGroup Q))
    exact Subgroup.mem_centralizer_singleton_iff.mpr hπt_center.symm
  have hCpit : piOrth Q * t ∈ C := by
    change piOrth Q * t ∈ Subgroup.centralizer ({t} : Set (OGroup Q))
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (piOrth Q * t) * t = piOrth Q := by rw [mul_assoc, htt, mul_one]
      _ = t * (piOrth Q * t) := by
            rw [← mul_assoc, hπt_center, mul_assoc, htt, mul_one]
  have ht_not : t ∉ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ htt]
    rintro ⟨-, hsign⟩
    have h1 : invDim t = 6 := by simpa [invType] using congrArg Prod.fst ht6
    have h2 : invSign t = 1 := by simpa [invType] using congrArg Prod.snd ht6
    rw [h1, h2] at hsign
    have hcalc : ((-1 : ℤˣ) ^ (6 / 2)) = -1 := by ext; norm_num
    rw [hcalc] at hsign
    have hone : (1 : ℤˣ) ≠ -1 := by
      intro hcon
      have h' : ((1 : ℤˣ) : ℤ) = ((-1 : ℤˣ) : ℤ) :=
        congrArg (fun u : ℤˣ => (u : ℤ)) hcon
      norm_num at h'
    exact hone hsign
  have hπ_not : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ]
    rintro ⟨heven, -⟩
    rw [hdim] at heven
    exact (by decide : ¬ Even 7) heven
  have hπt_type : invType (piOrth Q * t) = (1, 1) := by
    have hn : Odd (Module.finrank (ZMod 3) V) := by rw [hdim]; decide
    rw [invType_piOrth_mul_of_odd hQ htt hn hσ]
    have h1 : invDim t = 6 := by simpa [invType] using congrArg Prod.fst ht6
    have h2 : invSign t = 1 := by simpa [invType] using congrArg Prod.snd ht6
    rw [h1, h2, hdim]
  have hπt_not : piOrth Q * t ∉ omegaGroup hQ := by
    rw [involution_mem_omegaGroup_iff hQ (piOrth_mul_mul_self htt)]
    rintro ⟨heven, -⟩
    have h1 : invDim (piOrth Q * t) = 1 := by
      simpa [invType] using congrArg Prod.fst hπt_type
    rw [h1] at heven
    exact (by decide : ¬ Even 1) heven
  let φC : C →* OGroup Q ⧸ omegaGroup hQ :=
    (QuotientGroup.mk' (omegaGroup hQ)).comp C.subtype
  have hker' : φC.ker = (omegaGroup hQ).subgroupOf C := by
    change ((QuotientGroup.mk' (omegaGroup hQ)).comp C.subtype).ker =
      (omegaGroup hQ).comap C.subtype
    rw [← MonoidHom.comap_ker (g := QuotientGroup.mk' (omegaGroup hQ)) (f := C.subtype),
      QuotientGroup.ker_mk']
  have hDsub : D.subgroupOf C = (omegaGroup hQ).subgroupOf C := by
    change (omegaGroup hQ ⊓ C).subgroupOf C = (omegaGroup hQ).subgroupOf C
    rw [Subgroup.inf_subgroupOf_right]
  have hker : φC.ker = D.subgroupOf C := by rw [hker', hDsub]
  have hkerCard : Nat.card φC.ker = Nat.card D := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv
  have h01 : φC ⟨1, hC1⟩ ≠ φC ⟨t, hCt⟩ := by
    intro h
    have hv : ((1 : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (1 : OGroup Q) / t ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [one_div, inv_eq_of_mul_eq_one_right htt] at hmem
    exact ht_not hmem
  have h02 : φC ⟨1, hC1⟩ ≠ φC ⟨piOrth Q, hCpi⟩ := by
    intro h
    have hv : ((1 : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((piOrth Q : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (1 : OGroup Q) / piOrth Q ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [one_div, inv_eq_of_mul_eq_one_right (piOrth_mul_self (Q := Q))] at hmem
    exact hπ_not hmem
  have h03 : φC ⟨1, hC1⟩ ≠ φC ⟨piOrth Q * t, hCpit⟩ := by
    intro h
    have hv : ((1 : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((piOrth Q * t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (1 : OGroup Q) / (piOrth Q * t) ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [one_div, inv_eq_of_mul_eq_one_right (piOrth_mul_mul_self htt)] at hmem
    exact hπt_not hmem
  have h12 : φC ⟨t, hCt⟩ ≠ φC ⟨piOrth Q, hCpi⟩ := by
    intro h
    have hv : ((t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((piOrth Q : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (t : OGroup Q) / piOrth Q ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (piOrth_mul_self (Q := Q)),
      hπt_center] at hmem
    exact hπt_not hmem
  have h13 : φC ⟨t, hCt⟩ ≠ φC ⟨piOrth Q * t, hCpit⟩ := by
    intro h
    have hv : ((t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((piOrth Q * t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (t : OGroup Q) / (piOrth Q * t) ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (piOrth_mul_mul_self htt)] at hmem
    have htpt : t * (piOrth Q * t) = piOrth Q := by
      rw [← mul_assoc, hπt_center, mul_assoc, htt, mul_one]
    rw [htpt] at hmem
    exact hπ_not hmem
  have h23 : φC ⟨piOrth Q, hCpi⟩ ≠ φC ⟨piOrth Q * t, hCpit⟩ := by
    intro h
    have hv : ((piOrth Q : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) =
        ((piOrth Q * t : OGroup Q) : OGroup Q ⧸ omegaGroup hQ) := by simpa [φC] using h
    have hmem : (piOrth Q : OGroup Q) / (piOrth Q * t) ∈ omegaGroup hQ :=
      (QuotientGroup.eq_iff_div_mem (N := omegaGroup hQ)).mp hv
    rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right (piOrth_mul_mul_self htt)] at hmem
    have hππt : piOrth Q * (piOrth Q * t) = t := by
      rw [← mul_assoc, piOrth_mul_self, one_mul]
    rw [hππt] at hmem
    exact ht_not hmem
  have hcard_range : 4 ≤ Nat.card φC.range := by
    haveI : Finite φC.range := inferInstance
    let a0 : φC.range := ⟨φC ⟨1, hC1⟩, ⟨⟨1, hC1⟩, rfl⟩⟩
    let a1 : φC.range := ⟨φC ⟨t, hCt⟩, ⟨⟨t, hCt⟩, rfl⟩⟩
    let a2 : φC.range := ⟨φC ⟨piOrth Q, hCpi⟩, ⟨⟨piOrth Q, hCpi⟩, rfl⟩⟩
    let a3 : φC.range := ⟨φC ⟨piOrth Q * t, hCpit⟩, ⟨⟨piOrth Q * t, hCpit⟩, rfl⟩⟩
    let g : Fin 4 → φC.range :=
      Fin.cases a0 (Fin.cases a1 (Fin.cases a2 (Fin.cases a3 Fin.elim0)))
    have ha01 : a0 ≠ a1 := fun h => h01 (congrArg Subtype.val h)
    have ha02 : a0 ≠ a2 := fun h => h02 (congrArg Subtype.val h)
    have ha03 : a0 ≠ a3 := fun h => h03 (congrArg Subtype.val h)
    have ha12 : a1 ≠ a2 := fun h => h12 (congrArg Subtype.val h)
    have ha13 : a1 ≠ a3 := fun h => h13 (congrArg Subtype.val h)
    have ha23 : a2 ≠ a3 := fun h => h23 (congrArg Subtype.val h)
    have hg : Function.Injective g := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact absurd hij ha01
      · exact absurd hij ha02
      · exact absurd hij ha03
      · exact absurd hij.symm ha01
      · rfl
      · exact absurd hij ha12
      · exact absurd hij ha13
      · exact absurd hij.symm ha02
      · exact absurd hij.symm ha12
      · rfl
      · exact absurd hij ha23
      · exact absurd hij.symm ha03
      · exact absurd hij.symm ha13
      · exact absurd hij.symm ha23
      · rfl
    have hle := Nat.card_le_card_of_injective g hg
    simpa using hle
  have hmain := Subgroup.card_ker_mul_card_range φC
  rw [hkerCard, hcardC] at hmain
  have hle : Nat.card D * 4 ≤ 48522240 :=
    (Nat.mul_le_mul_left (Nat.card D) hcard_range).trans_eq hmain
  show Nat.card D ≤ 12130560
  omega

theorem sec4FCl_exists_wt (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 7)
    (hσ : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) (ht6 : invType t = (6, 1)) :
    ∃ w : OGroup Q, w ∈ Sec4FDDt hQ t ∧ w * w = 1 ∧ invType w = (4, 1) ∧
      w ∉ sec4FClXt hQ htt := by
  have hdimU : Module.finrank (ZMod 3) (commSp t) = 6 := by
    have := congrArg Prod.fst ht6
    simpa only [invType, invDim] using this
  have hfix1 : Module.finrank (ZMod 3) (fixSp t) = 1 := by
    have h := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have hU : (Q.restrict (commSp t)).Nondegenerate := nondegenerate_restrict_commSp hQ htt
  obtain ⟨b, hbb, hbtype⟩ :=
    (exists_involution_of_type hU 3 (-1)).mpr
      ⟨by rw [hdimU]; norm_num, fun h => by omega, fun h => by omega⟩
  have hb1 : invDim b = 3 := by simpa [invType] using congrArg Prod.fst hbtype
  have hb2 : invSign b = -1 := by simpa [invType] using congrArg Prod.snd hbtype
  let w : OGroup Q := (piOrth Q * t) * blockInr htt b
  have hww : w * w = 1 := by
    change ((piOrth Q * t) * blockInr htt b) * ((piOrth Q * t) * blockInr htt b) = 1
    exact sec4FD_block_neg_sq hQ htt hbb
  have hwDim : invDim ((piOrth Q * t) * blockInr htt b) = 4 := by
    have hraw : invDim ((piOrth Q * t) * blockInr htt b) = 1 + invDim b :=
      (by simpa [invType] using
        congrArg Prod.fst (sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb))
    rw [hb1] at hraw
    omega
  have hwSign : invSign ((piOrth Q * t) * blockInr htt b) = 1 := by
    have hraw : invSign ((piOrth Q * t) * blockInr htt b) = invSign b * (-1) ^ invDim b :=
      (by simpa [invType] using
        congrArg Prod.snd (sec4FD_invType_mul_block hQ hdim hσ htt ht6 hbb))
    have hcalc : ((-1 : ℤˣ) * (-1) ^ 3) = 1 := by ext; norm_num
    rw [hb1, hb2, hcalc] at hraw
    exact hraw
  have hwtype : invType w = (4, 1) := by
    change invType ((piOrth Q * t) * blockInr htt b) = (4, 1)
    exact Prod.ext hwDim hwSign
  have hwmem : w ∈ Sec4FDDt hQ t := by
    rw [mem_sec4FDDt_iff]
    refine ⟨?_, ?_⟩
    · change w ∈ omegaGroup hQ
      rw [involution_mem_omegaGroup_iff hQ hww]
      change Even (invDim ((piOrth Q * t) * blockInr htt b)) ∧
        invSign ((piOrth Q * t) * blockInr htt b) =
          (-1 : ℤˣ) ^ (invDim ((piOrth Q * t) * blockInr htt b) / 2)
      refine ⟨?_, ?_⟩
      · rw [hwDim]; decide
      · rw [hwDim, hwSign]
        have hcalc2 : ((-1 : ℤˣ) ^ (4 / 2)) = 1 := by ext; norm_num
        exact hcalc2.symm
    · change ((piOrth Q * t) * blockInr htt b) * t =
        t * ((piOrth Q * t) * blockInr htt b)
      exact piOrth_mul_t_mul_blockInr_commute hQ htt b
  have hwnot : w ∉ sec4FClXt hQ htt := by
    intro hw
    obtain ⟨v, hv0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ZMod 3)
      (M := fixSp t)).mp (by rw [hfix1]; norm_num)
    have h1 : ((w : V ≃ₗ[ZMod 3] V) (v : V)) = (v : V) :=
      sec4FClXt_fix hQ htt hw (v : V) v.2
    have h2 : ((w : V ≃ₗ[ZMod 3] V) (v : V)) = -(v : V) := by
      change ((((piOrth Q * t) * blockInr htt b : OGroup Q) : V ≃ₗ[ZMod 3] V) (v : V)) =
        -(v : V)
      exact piOrth_mul_t_mul_blockInr_apply_fixSp htt b v
    have hnegv : -(v : V) = (v : V) := h2.symm.trans h1
    have h2v : (2 : ZMod 3) • (v : V) = 0 := by
      rw [two_smul]
      exact neg_eq_iff_add_eq_zero.mp hnegv
    have hvV : (v : V) = 0 :=
      (isUnit_of_invertible (2 : ZMod 3)).smul_eq_zero.mp h2v
    exact hv0 (Subtype.ext hvV)
  exact ⟨w, hwmem, hww, hwtype, hwnot⟩

end CFSG.OddStandard.SmallF3.Omega
